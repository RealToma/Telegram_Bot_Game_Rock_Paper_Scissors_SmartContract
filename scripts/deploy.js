async function main() {

    const [deployer] = await ethers.getSigners();

    console.log(
        "Deploying contracts with the account:",
        deployer.address
    );

    const Scissors = await ethers.getContractFactory("Scissors");
    // const gasPrice = await MyOcadaTestToken.signer.getGasPrice();
    // console.log(`Current gas price: ${gasPrice}`);

    // const estimatedGas = await MyOcadaTestToken.signer.estimateGas(
    //     MyOcadaTestToken.getDeployTransaction()
    // );
    // console.log(`Estimated gas: ${estimatedGas}`);
    
    // const deploymentPrice = gasPrice.mul(estimatedGas);
    // const deployerBalance = await MyOcadaTestToken.signer.getBalance();
    // console.log(`Deployer balance:  ${ethers.utils.formatEther(deployerBalance)}`);
    // console.log( `Deployment price:  ${ethers.utils.formatEther(deploymentPrice)}`);

    // if (Number(deployerBalance) < Number(deploymentPrice)) {
    // throw new Error("You dont have enough balance to deploy.");
    // }
    // const checksumAddress = ethers.utils.getAddress("0xf8785de6Bb2e211616bF205974f973F311669C9A");
    const Token = await Scissors.deploy("Scissors", "SCT", 18);
    const token = await Token.deployed();
    console.log("Contract deployed at:", token.address);
}

main()
  .then(() => process.exit(0))
  .catch(error => {
    console.error(error);
    process.exit(1);
  });

