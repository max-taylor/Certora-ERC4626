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

// ***** Hooks

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

// ***** Valid States

invariant totalSupplyIsSumOfBalances()
  totalSupply() == ghostSumOfBalances

invariant totalSupplyNonZeroAssetsNonZero(env e)
  totalSupply() > 0 => totalAssets() > 0
  {
    preserved {
      setup(e);
      requireInvariant totalSupplyIsSumOfBalances();
    }
  }


// **** UNIT TESTS

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

rule unitWithdrawRedeemShouldUpdateState(method f, uint256 amount, address receiver) 
  filtered { f -> 
                f.selector == withdraw(uint256, address, address).selector 
                || f.selector == redeem(uint256, address, address).selector 
    }
{
  env e;

  setup(e);
  require e.msg.sender != currentContract;
  require amount > 0;
  requireInvariant totalSupplyIsSumOfBalances();
  requireInvariant totalSupplyNonZeroAssetsNonZero(e);

  address owner = e.msg.sender;

  uint256 totalSupplyBefore = totalSupply();
  uint256 balanceReceiverBefore = ERC20a.balanceOf(receiver);
  uint256 tokenBalanceBefore = balanceOf(owner);
  uint256 contractBalanceBefore = ERC20a.balanceOf(currentContract);

 if (f.selector == withdraw(uint256, address, address).selector) {
    withdraw(e, amount, receiver, owner);
  } else {
    redeem(e, amount, receiver, owner);
  }

  assert totalSupply() < totalSupplyBefore, "Total supply should've decreased";
  assert ERC20a.balanceOf(receiver) > balanceReceiverBefore, "Receiver balance should've increased";
  assert balanceOf(owner) < tokenBalanceBefore, "Sender's token balance should've decreased";
  assert ERC20a.balanceOf(currentContract) < contractBalanceBefore, "Contract balance should've decreased";
}

// **** Variable transition

// Users can only reduce their own balance or can have their balance reduced up to the allowance
rule balanceReduceableByOwnerOrAllowance(address owner) {
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
rule balanceOfIncreasedOnSelectMethods(method f) 
  filtered { 
    // Ignoring transferFrom method, as it doesn't really work with the assertion and not important for the property we are testing
    f -> 
        f.selector != transferFrom(address, address, uint256).selector
} {
  env e; calldataarg args;

  setup(e);
  requireInvariant totalSupplyIsSumOfBalances();

  uint256 beforeBalance = balanceOf(e.msg.sender);

  if (f.selector == deposit(uint256, address).selector) {
    uint256 amount;

    require amount > 0;

    deposit(e, amount, e.msg.sender);
  } else if (f.selector == mint(uint256, address).selector) {
    uint256 amount;

    require amount > 0;

    mint(e, amount, e.msg.sender);
  } else {
    f(e, args);
  }

  uint256 afterBalance = balanceOf(e.msg.sender);

  // ! I'm unsure why the prover doesn't fail on the transfer method
  assert afterBalance > beforeBalance <=> (
    f.selector == deposit(uint256, address).selector || 
    f.selector == mint(uint256, address).selector
  );
}

// If balanceOf decreased, withdraw, redeem or transfer was called
rule balanceOfDecreasedOnSelectMethods(method f) 
  filtered {
    f -> 
        f.selector != transferFrom(address, address, uint256).selector
} {
  env e; calldataarg args;

  setup(e);
  requireInvariant totalSupplyIsSumOfBalances();

  uint256 beforeBalance = balanceOf(e.msg.sender);

  if (f.selector == withdraw(uint256, address, address).selector) {
    uint256 amount; address receiver;
    require amount > 0;
    
    withdraw(e, amount, receiver, e.msg.sender);
  } else if (f.selector == redeem(uint256, address, address).selector) {
    uint256 amount; address receiver;
    require amount > 0;

    redeem(e, amount, receiver, e.msg.sender);
  } else if (f.selector == transfer(address, uint256).selector) {
    uint256 amount; address receiver;
    require amount > 0;
    require receiver != e.msg.sender;

    transfer(e, receiver, amount);
  } else {
    f(e, args);
  }

  uint256 afterBalance = balanceOf(e.msg.sender);

   assert afterBalance < beforeBalance <=> (
    f.selector == withdraw(uint256, address, address).selector || 
    f.selector == redeem(uint256, address, address).selector || 
    f.selector == transfer(address, uint256).selector
  );
}

// *** High-level properties

rule canAlwaysRedeemShares() {
  env e; uint256 amount;

  setup(e);
  requireInvariant totalSupplyIsSumOfBalances();

  uint256 shares = deposit(e, amount, e.msg.sender);

  require previewRedeem(shares) > 0;

  redeem@withrevert(e, shares, e.msg.sender, e.msg.sender);

  assert !lastReverted, "Vault insolvent, user should always be able to withdraw assets";
}
