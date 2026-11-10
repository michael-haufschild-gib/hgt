# Summable residue errors cannot rescue a constituent

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Γ215; B153, arithmetic constituents of ξ.
- **Statement:** A nonzero absolutely convergent real-scale expansion on a strip about `Re s = 1/2`, with a zero and all its strip zeros on that line, has nonsummable residues `mρ ζ(ρ)/ρ` over its zeros.

## Mathematical connection

CTZ excludes finitely many exceptional zeros. Its jump law already tolerates countably many poles with summable residues. The missing bridge is the holomorphic remainder of `−ζF'/(sF)` after subtracting all principal parts. Local zero factorization, normal convergence away from the discrete divisor, and the existing good-height bounds should supply it.

## Required proof

1. Construct and audit the countable principal-part remainder, with the actual logarithmic-derivative residues.
2. Bound that remainder between good heights and on both boundary lines.
3. Apply the summable-pole jump law to identify the two logarithmic-derivative expansions; the resulting holomorphic logarithmic derivative excludes every zero.

No claim about bounded constituents in the Bohr strip. No contribution counted until the exact capstone passes Lean and transitive axiom audit.
