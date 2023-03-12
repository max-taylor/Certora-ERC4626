# Valid states
- totalAssets() >= asset.balanceOf(currentContract)
- totalSupply == sumOf(balanceOf(user))


# Unit tests
- balanceOf(user) should increase on transfer



# State transition
- Balance of sender should decrease on transfer, balance of receiver should increase



# Variable transition
- If the user's share balance decreases they must've called withdraw or redeem
- If the user's token balance decreases they must've called deposit or mint



# High level
- Depositing more than 0 assets should always return shares
- Calling the mint method should take assets at the conversion rate and return shares
- Solvency; 



# Unit test

