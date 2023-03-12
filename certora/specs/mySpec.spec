using DummyERC20A as ERC20a 
using DummyERC20B as ERC20b 

methods {
    name() returns string envfree;
    symbol() returns string envfree;
    decimals() returns uint8 envfree;
    asset() returns address envfree;

    totalSupply() returns uint256 envfree;
    balanceOf(address) returns uint256 envfree => DISPATCHER(true);
    nonces(address) returns uint256 envfree;

    approve(address,uint256) returns bool;
    transfer(address,uint256) returns bool => DISPATCHER(true);
    transferFrom(address,address,uint256) returns bool => DISPATCHER(true);
    deposit(uint256,address);
    mint(uint256,address);
    withdraw(uint256,address,address);
    redeem(uint256,address,address);

    totalAssets() returns uint256 envfree;
    userAssets(address) returns uint256 envfree;
    convertToShares(uint256) returns uint256 envfree;
    convertToAssets(uint256) returns uint256 envfree;
    previewDeposit(uint256) returns uint256 envfree;
    previewMint(uint256) returns uint256 envfree;
    previewWithdraw(uint256) returns uint256 envfree;
    previewRedeem(uint256) returns uint256 envfree;

    maxDeposit(address) returns uint256 envfree;
    maxMint(address) returns uint256 envfree;
    maxWithdraw(address) returns uint256 envfree;
    maxRedeem(address) returns uint256 envfree;
    allowance(address, address) returns uint256 envfree;

    permit(address,address,uint256,uint256,uint8,bytes32,bytes32);
    DOMAIN_SEPARATOR() returns bytes32;

    ERC20a.balanceOf(address) returns uint256 envfree;

    // * Mine

    getValues(address, address) returns (uint256, uint256, uint256, uint256) envfree;
}

// https://docs.google.com/document/d/1rzB01jJVjYyBxzL1MIgHs-ucPzYIPIt_z1KefP3jfTw/edit


function setup(env e) {
  require e.msg.sender != currentContract;
  require asset() != currentContract;
  require asset() == ERC20a;
}

// ** Hooks

ghost mathint ghostSumOfBalances {
	init_state axiom ghostSumOfBalances == 0 ;
}

hook Sstore balanceOf [KEY address account] uint256 newValue (uint256 oldValue) STORAGE {
  ghostSumOfBalances = ghostSumOfBalances + newValue - oldValue;
}

// This ensures that the account balances aren't initialized to be greater than the total supply, this would be an invalid initial state
hook Sload uint256 val balanceOf[KEY address account] STORAGE {
    require ghostSumOfBalances >= val;
}

invariant totalSupplyIsSumOfBalances()
  totalSupply() == ghostSumOfBalances

invariant totalSupplyLessThanMax()
  totalSupply() <= 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
  {
    preserved {
      requireInvariant totalSupplyIsSumOfBalances();
    }
  }

invariant totalSupplyNonZeroAssetsNonZero(env e)
  totalSupply() > 0 => totalAssets() > 0
  {
    preserved {
      setup(e);
      requireInvariant totalSupplyIsSumOfBalances();
    }
  }


// ! This fails for withdraws and redeems
// The pre-state is fine, but the post-state fails, assuming because of precision loss

// Rounding favours the contract, there is left-over dust in the contract after withdraws and 
// invariant totalAssetsIsSolvent(env e)
//     convertToAssets(totalSupply()) <= totalAssets()
//   {
//     preserved {
//       setup(e); // new
//       requireInvariant totalSupplyNonZeroAssetsNonZero(e);
//     }
//   }

rule depositingAssetsReturnsShares(env e, uint256 amount, address receiver) {
  require asset() != currentContract;

  uint256 beforeShareBalance = balanceOf(receiver);

  deposit(e, amount, receiver);

  uint256 afterShareBalance = balanceOf(receiver);

  assert afterShareBalance > beforeShareBalance, "User's share balance didn't increase";
}

// ### UNIT TESTS

// TODO: Could do same test for withdraw and redeem
rule unitDepositMintShouldUpdateState(method f, uint256 amount, address receiver)
  filtered { f -> 
                f.selector == deposit(uint256, address).selector 
                || f.selector == mint(uint256, address).selector 
    }
{
  env e;

  setup(e);
  require amount > 0;
  requireInvariant totalSupplyNonZeroAssetsNonZero(e);

  uint256 totalSupplyBefore = totalSupply();
  uint256 balanceReceiverBefore = balanceOf(receiver);
  uint256 tokenBalanceBefore = ERC20a.balanceOf(e.msg.sender);
  uint256 contractBalanceBefore = ERC20a.balanceOf(currentContract);

  if (f.selector == deposit(uint256, address).selector) {
    deposit(e, amount, receiver);
  } else {
    mint(e, amount, receiver);
  }

  assert totalSupply() > totalSupplyBefore, "Total supply should've increased";
  assert balanceOf(receiver) > balanceReceiverBefore, "Receiver balance should've increased";
  assert ERC20a.balanceOf(e.msg.sender) < tokenBalanceBefore, "Sender's token balance should've decreased";
  assert ERC20a.balanceOf(currentContract) > contractBalanceBefore, "Contract balance should've increased";
}


// ! Can't seem to verify this, it does revert in some instances
rule convertToAssetsNoRevertAfterDeposit(uint256 amount, address receiver) {
  env e;

  setup(e);
  requireInvariant totalSupplyIsSumOfBalances();
  requireInvariant totalSupplyNonZeroAssetsNonZero(e);

  // TODO: Need a nice way to target deposit and mint at the same time
  uint256 shares = deposit(e, amount, receiver);

  convertToAssets@withrevert(shares);

  // It is reverting
  assert !lastReverted, "Shouldn't revert when converting returned shares back to assets";
}

// **** Variable transition

// Users can only reduce the balance of others up to the allowance they are given
rule allowedUserCanOnlyReduceUpToAllowance(address owner) {
  env e; method f; calldataarg args;

  setup(e);
  requireInvariant totalSupplyIsSumOfBalances();

  uint256 beforeBalance = balanceOf(owner);
  uint256 beforeAllowance = allowance(owner, e.msg.sender);
  f(e, args);
  uint256 afterBalance = balanceOf(owner);

  mathint balanceReduction = beforeBalance - afterBalance;

  assert balanceReduction > 0 => (owner == e.msg.sender
    || beforeAllowance >= balanceReduction);
}

// If balanceOf increased, deposit, mint or transfer was called
rule balanceOfIncreasedOnSelectMethods() {
  env e; method f; calldataarg args;

  uint256 beforeBalance = balanceOf(e.msg.sender);
  f(e, args);
  uint256 afterBalance = balanceOf(e.msg.sender);

  assert afterBalance > beforeBalance <=> (f.selector == deposit(uint256, address).selector || f.selector == mint(uint256, address).selector);
}

// If balanceOf decreased, withdraw, redeem or transfer was called

// Anti-monotinicity
// If asset.balanceOf(address(this)) went up <=> asset.balanceOf(user) went down
// ^ same rule but inverted, if contract balance went down user balance went up

// **** State transition

// Total supply of vault == 0 only if balance of contract == 0 (no deposits == no shares)

// **** Helpers

function callDepositMint(env e, method f, uint256 amount, address receiver) returns bool {
  if (f.selector == deposit(uint256, address).selector) {
    deposit@withrevert(e, amount, receiver);

    return !lastReverted;
  } else {
    mint@withrevert(e, amount, receiver);

    return !lastReverted;
  }
}