#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 05
#
# Selective Disclosure (Anonymous) Credentials
#
# Run the tests through:
# $ py.test -v test_file_name.py

###########################
# Group Members: TODO
###########################

from petlib.ec import EcGroup
from petlib.bn import Bn

from hashlib import sha256
from binascii import hexlify

#####################################################
# Background, setup, key derivation and utility 
# functions.
# 

def credential_setup():
    """ Generates the parameters of the algebraic MAC scheme"""
    G = EcGroup()
    g = G.hash_to_point(b"g")
    h = G.hash_to_point(b"h")
    o = G.order()

    params = (G, g, h, o)
    return params

def credential_KeyGenIssuer(params):
    """ Generates keys and parameters for the credential issuer for 1 attribute"""
    _, g, h, o = params

    # Generate x0, x1 as the keys to the algebraic MAC scheme
    x0, x1 = o.random(), o.random()
    sk = [x0, x1]
    iparams = x1 * h 

    # Generate a pedersen commitment Cx0 to x0 with opening x0_bar
    x0_bar = o.random()
    Cx0 = x0 * g + x0_bar * h

    return (Cx0, iparams), (sk, x0_bar)

def credential_KeyGenUser(params):
    """ Generates keys and parameters for credential user """
    G, g, h, o = params
    priv = o.random()
    pub = priv * g # This is just an EC El-Gamal key
    return (priv, pub)

## This is our old friend "to_challenge" from Lab04 on Zero Knowledge

def to_challenge(elements):
    """ Generates a Bn challenge by hashing a number of EC points """
    Cstring = b",".join([hexlify(x.export()) for x in elements])
    Chash =  sha256(Cstring).digest()
    return Bn.from_binary(Chash)

#####################################################
# TASK 1 -- User Encrypts a secret value v and sends
#           and sends it to the issuer. This v will 
#           become the single attribute of the user.
#           Prove in ZK that the user knows v and the
#           private key of pub.

## IMPORTANT NOTE: The reference scheme for all the 
# techniques in this exercise are in section 
# "4.2 Keyed-verification credentials from MAC_GGM"
# pages 8-9 of https://eprint.iacr.org/2013/516.pdf

def credential_EncryptUserSecret(params, pub, priv):
    """ Encrypt a user defined random secret v under the public key of the user. 
        Prove knowledge of the secret v, the private key "priv" and correctness of 
        the encryption """
    G, g, h, o = params
    v = o.random()
    
    ## Encrypt v using Benaloh with randomness k
    k = o.random()
    ciphertext = k * g, k * pub + v * g
    a, b = ciphertext

    ## Prove knowledge of the encrypted v and priv in ZK
    #  NIZK{(v, k, priv): a = k * g and 
    #                     b = k * pub + v * g and 
    #                     pub = priv * g}

    wk,wv,wpriv = o.random(),o.random(),o.random()

    Wa,Wb,Wpriv = wk*g, wk*pub + wv*g, wpriv*g

    c = to_challenge([g,pub,a,b,Wa,Wb,Wpriv])

    rk,rv,rpriv = wk - c*k, wv - c*v, wpriv - c*priv
    

    # Return the fresh v, the encryption of v and the proof.
    proof = (c, rk, rv, rpriv)
    return v, ciphertext, proof


def credential_VerifyUserSecret(params, pub, ciphertext, proof):
    """ Verify the ciphertext is a correct encryption and the 
        proof of knowledge of the secret key "priv" """
    G, g, h, o = params

    ## The cipher text and its proof of correctness
    a, b = ciphertext
    (c, rk, rv, rpriv) = proof

    # Verify knowledge of the encrypted k, v and priv
    Wap = c * a + rk * g
    Wbp = c * b + rk * pub + rv * g
    Wpubp = c * pub + rpriv * g

    cp = to_challenge([g, pub, a, b, Wap, Wbp, Wpubp])
    return cp == c


#####################################################
# TASK 2 -- The issuer issues an
#           algebraic MAC on v, along with a ZK proof
#           that the MAC is correctly formed. The user
#           decrypts and verifies the MAC.

## IMPRTANT NOTE: Study the section "Issuance" p.8 
#  of https://eprint.iacr.org/2013/516.pdf


def credential_Issuing(params, pub, ciphertext, issuer_params):
    """ A function used by the credential issuer to provide a MAC
        on a secret (encrypted) attribute v """

    G, g, h, o = params
    
    ## The public and private parameters of the issuer 
    (Cx0, iparams), (sk, x0_bar) = issuer_params
    X1 = iparams
    x0, x1 = sk

    # The ciphertext of the encrypted attribute v
    a, b = ciphertext

    # 1) Create a "u" as u = b*g 
    # 2) Create a X1b as X1b == b * X1 == (b * x1) * h
    #     and x1b = (b * x1) mod o 
    
    randb = o.random()
    u = randb*g

    X1b = (randb*x1)*h
    x1b = (randb*x1) % o

    # 3) The encrypted MAC is u, and an encrypted u_prime defined as 
    #    E( (b*x0) * g + (x1 * b * v) * g ) + E(0; r_prime)
     # ciphertext b = k * g*x1 + v * g
    
    #u_prime =  (randb*x0)*g+(x1*randb*v)*g
    #k = o.random()
    r_prime = o.random()

    new_a = r_prime * g + x1b * a
    new_b = r_prime * pub + x1b * b + x0 * u 

    ciphertext = new_a, new_b

    ## A large ZK proof that:
    #  NIZK{(x1, beta, x1b, r_prime, x0, x0_bar)
    #       X1  = x1 * h
    #       X1b = beta * X1
    #       X1b = x1b * h
    #       u   = beta * g
    #       new_a = r_prime * g + x1b * a
    #       new_b = r_prime * pub + x1b * b + x0 * u 
    #       Cx0 = x0 * g + x0_bar * h }

    wx1,wrandb,wx1b,wrprime,wx0,wx0_bar = o.random(),o.random(),o.random(),o.random(),o.random(),o.random() 						#randoms
  
    c = to_challenge([g,h,pub,a,b,X1,X1b,new_a,new_b,Cx0, 
	wx1*h, wrandb*X1,
	wx1b*h, wrandb*g, 
	wrprime*g + wx1b*a,
	wrprime*pub + wx1b*b + wx0*u,
	wx0*g + wx0_bar*h])

    rs = [					#respsonses
	wx1 - c*x1,
	wrandb - c*randb,
	wx1b - c*x1b,
	wrprime - c*r_prime,
	wx0 - c*x0,
	wx0_bar - c*x0_bar
	]
   
    proof = (c, rs, X1b)

    return u, ciphertext, proof

def credential_Verify_Issuing(params, issuer_pub_params, pub, u, Enc_v, Enc_u_prime, proof):
    """ User verifies that the proof associated with the issuance 
        of the credential is valid. """

    G, g, h, o = params

    ## The public parameters of the issuer.
    (Cx0, iparams) = issuer_pub_params
    X1 = iparams

    ## The ciphertext of the encrypted attribute v and the encrypted u_prime
    a, b = Enc_v
    new_a, new_b = Enc_u_prime
    
    ## The proof of correctness
    (c, rs, X1b) = proof

    c_prime = to_challenge([g, h, pub, a, b, X1, X1b, new_a, new_b, Cx0,
                    c * X1 + rs[0] * h,
                    c * X1b + rs[1] * X1,
                    c * X1b + rs[2] * h,
                    c * u + rs[1] * g,
                    c * new_a + rs[3] * g + rs[2] * a,
                    c * new_b + rs[3] * pub + rs[2] * b + rs[4] * u,
                    c * Cx0 + rs[4] * g + rs[5] * h
                    ])

    return c_prime == c

def credential_Decrypt(params, priv, u, Enc_u_prime):
    """ Decrypt the second part of the credential u_prime """

    G, g, h, o = params
    new_a, new_b = Enc_u_prime
    u_prime = new_b - priv * new_a
    return (u, u_prime)

#####################################################
# TASK 3 -- The user re-blinds the MAC and proves
#           its possession without revealing the secret
#           attribute.

## IMPORTANT NOTE: Study the section "Credential presentation"
#  p.9 of https://eprint.iacr.org/2013/516.pdf

def credential_show(params, issuer_pub_params, u, u_prime, v):
    """ The user blinds the credential (u, u_prime) and then
        proves its correct possession."""

    G, g, h, o = params
    
    ## The public parameters of the credential issuer
    (Cx0, iparams) = issuer_pub_params
    X1 = iparams

    # 1) First blind the credential (u, u_prime)
    #    using (alpha * u, alpha * u_prime) for a
    #    random alpha.
    
    alpha = o.random()
    u_blind, u_prime_blind = alpha*u, alpha*u_prime

    # 2) Implement the "Show" protocol (p.9) for a single attribute v.
    #    Cv is a commitment to v and Cup is C_{u'} in the paper. 

    z1, r = o.random(), o.random()
    Cv = v*u_blind + z1*h
    Cup = u_prime_blind + r*g

    
    tag = (u_blind, Cv, Cup)

    # Proof or knowledge of the statement

    wr, wz1, wv = o.random(), o.random(), o.random()	#randoms

    c = to_challenge([g, h, X1, Cx0,
   	wv*u_blind + wz1*h,
 	wr*(-g) + wz1*X1]) 

    rr, rz1, rv = wr - c*r, wz1 - c*z1, wv - c*v	#responses

    proof = (c, rr, rz1, rv)
    return tag, proof

def credential_show_verify(params, issuer_params, tag, proof):
    """ Take a blinded tag and a proof of correct credential showing and verify it """

    G, g, h, o = params

    ## Public and private issuer parameters
    (Cx0, iparams), (sk, x0_bar) = issuer_params
    x0, x1 = sk
    X1 = iparams

    # Verify proof of correct credential showing
    (c, rr, rz1, rv) = proof
    (u, Cv, Cup) = tag

    c_prime = to_challenge([g, h, X1, Cx0,
   	rv*u + rz1*h + c*Cv,
 	rr*(-g) + rz1*X1 + c*((x0*u + x1*Cv) - Cup)]) 

    return c == c_prime

#####################################################
# TASK 4 -- Modify the standard Show / ShowVerify process
#           to link the credential show to a long term 
#           pseudonym for a service. The pseudonyms should 
#           be unlikable between services.

def credential_show_pseudonym(params, issuer_pub_params, u, u_prime, v, service_name):
    """ From a credential (u, u_prime) generate a pseudonym H(service_name)^v 
        and prove you hold a valid credential with attribute v """

    G, g, h, o = params

    ## Public issuer parameters    
    (Cx0, iparams) = issuer_pub_params
    X1 = iparams

    ## A stable pseudonym associated with the service 
    N = G.hash_to_point(service_name)
    pseudonym = v * N

    # blind u,u'
    alpha = o.random()
    u_blind, u_prime_blind = alpha*u, alpha*u_prime

    # Show()
    z1, r = o.random(), o.random()
    Cv = v*u_blind + z1*h
    Cup = u_prime_blind + r*g

    
    tag = (u_blind, Cv, Cup)

    # Proof or knowledge of the statement

    wr, wz1, wv = o.random(), o.random(), o.random()	#randoms

    c = to_challenge([g, h, X1, Cx0,
   	wv*N,
   	wv*u_blind + wz1*h,
 	wr*(-g) + wz1*X1]) 

    rr, rz1, rv = wr - c*r, wz1 - c*z1, wv - c*v	#responses

    proof = (c, rr, rz1, rv)    

    return pseudonym, tag, proof

def credential_show_verify_pseudonym(params, issuer_params, pseudonym, tag, proof, service_name):
    """ Verify a pseudonym H(service_name)^v is generated by the holder of the 
        a valid credential with attribute v """

    G, g, h, o = params

    ## The public and private issuer parameters
    (Cx0, iparams), (sk, x0_bar) = issuer_params
    x0, x1 = sk
    X1 = iparams

    ## The EC point corresponding to the service
    N = G.hash_to_point(service_name)

    # Verify proof of correct credential showing
    (c, rr, rz1, rv) = proof
    (u, Cv, Cup) = tag

    c_prime = to_challenge([g, h, X1, Cx0,
        rv*N + c*pseudonym,
   	rv*u + rz1*h + c*Cv,
 	rr*(-g) + rz1*X1 + c*((x0*u + x1*Cv) - Cup)]) 

    return c == c_prime

#####################################################
# TASK Q1 -- Answer the following question:
#
# How could you use a credential scheme, such as the one you
# implemented above to implement an electronic cash scheme
# ensuring both integrity (no-double spending) and privacy. 
# What would the credential represent, and what statements
# would need to be shown to a verifier.

"""

	Using the unspent transaction input (UTXO) model found in E-cash schemes such as Bitcoin, money can be sent to and from addresses (pseudonyms) which can be proven to be owned by users with knowledge of their secret value v. 

	A central authority is required to maintain a UTXO set, issue credentials to users, process transactions and optionally could store a ledger of transactions to save the history of the system.  

	A new transaction would include:
		- For each input a proof of knowledge of v corresponding to some address in the UTXO set
		- output addresses and encrypted amounts being sent to each
		- range proofs proving the amounts being sent are positive
		- any scirpting or extra data fields
	
	Each transaction would be verified and processed by the central authority ensuring:
		- The proof of knowledge of v for the input UTXO addresses is valid
		- The UTXO havent already been spent (perhaps by simply removing them from the UTXO set once claimed)
		- sum of inputs = sum of ouptpus (via homomorphic property of Benaloh encryption)
		- Range proofs are valid
		- The ledger of transaction history is updated
		- outputs are added to the UTXO set

	 
	Integrity is acheived by either removing UTXOs from the UTXO set once spent and/or checking the ledger each time for past spends of the UTXO being claimed. 

	Since pseudonyms are unlinkable and verification of credentials is done in zero-knowledge, privacy is achieved because users can use many different addresses for each transaction and within each transaction. For example each time the CEO of a large social media platform wishes to be paid by a British analytics firm in secret they can generate a new pseudonym for each payment, and when spending can generate new pseudonyms for their change addresses.  
"""



