mod biguint;
use biguint::BigUint32;
use rsa::{RsaPrivateKey, RsaPublicKey};
use rsa::pkcs1v15::{SigningKey, VerifyingKey, Signature};
use rsa::signature::{Keypair, RandomizedSigner, SignatureEncoding, Verifier};
use rsa::sha2::{Digest, Sha256};
use rsa::traits::PublicKeyParts;

fn sign_with_rsa(msg: &str) -> (RsaPublicKey, Signature) {
    let mut rng = rand::thread_rng();

    let bits = 2048;
    let private_key: RsaPrivateKey = RsaPrivateKey::new(&mut rng, bits).expect("failed to generate a key");
    let public_key = private_key.to_public_key();
    let signing_key = SigningKey::<Sha256>::new(private_key);
    let verifying_key: VerifyingKey<Sha256> = signing_key.verifying_key();
    
    // Sign
    let data = msg.as_bytes();
    let signature = signing_key.sign_with_rng(&mut rng, data);
    assert_ne!(signature.to_bytes().as_ref(), data);
    
    // Verify
    verifying_key.verify(data, &signature).expect("failed to verify");

    (public_key, signature)
}

fn main() {
    let msg_str = "About ready south environment second finally. Work agency determine chance mean serve.";

    let (public_key, signature) = sign_with_rsa(msg_str);
    println!("public_key exp: {:?}", public_key.e().to_str_radix(16));
    println!("public_key modulus: {:?}", public_key.n().to_str_radix(16));
    println!("signature: {:?}", signature.to_string());

    let mut hasher = Sha256::new();

    hasher.update(msg_str.as_bytes());

    let mut hash = hasher.finalize();

    hash.reverse();
    println!("msg: {:?}", &hash);
    
    let mut sig_le = signature.to_bytes();
    sig_le.reverse();
    println!("sig: {:?}", sig_le);

    let sig = BigUint32::from_bytes(&sig_le);

    let mut pubkey_e_le = public_key.e().to_bytes_be();
    // Could use to_bytes_le() instead of to_bytes_be() and skip the reverse() below
    // but just to be explicit as most examples use Big Endian ordered byte arrays
    // while the BigUint32 uses Little Endian ordered byte arrays
    pubkey_e_le.reverse();
    println!("pubkey_e: {:?}", pubkey_e_le);

    let pubkey_e = BigUint32::from_bytes(&pubkey_e_le);

    let mut pubkey_n_le = public_key.n().to_bytes_be();
    pubkey_n_le.reverse();
    println!("pubkey_n: {:?}", pubkey_n_le);

    let pubkey_n = BigUint32::from_bytes(&pubkey_n_le);

    let (quotients, remainders) = sig.powmod(pubkey_e, pubkey_n);

    println!("quotients: {:?}", quotients);
    println!("remainders: {:?}", remainders);
}
