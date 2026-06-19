# Family cross-resonance modulus split

- **ID:** family-cross-resonance-modulus-split
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/family-dss-gsh.md` section R1
- **Statement:** A finite family cross-resonance product splits into a family-dependent twist product and a
  shared-prime modulus product whose exponent at each prime is the family sum `sum_chi m_chi,p`; if the
  modulus prime product is trivial, unique factorization forces `sum_chi m_chi,p = 0` for every prime.

## Goal
This banks the finite algebraic core of the family-DSS/GSH resolution: shared-prime cross-resonance is
killed in its modulus part by ordinary unique factorization, leaving only a finite twist/cyclotomic
relation. It does not formalize Dirichlet characters, cyclotomic Galois theory, GSH, zero statistics, or
the value-lift/F1 apex.

## Paper Proof
Let `m_chi` be a finitely supported integer exponent vector on the prime base for each member `chi` of a
finite family. For any family-dependent twist `u_chi,p` and shared scale `a_p`, commutativity gives

`product_chi product_p (u_chi,p a_p)^(m_chi,p)`

`= (product_chi product_p u_chi,p^(m_chi,p)) * product_p a_p^(sum_chi m_chi,p)`.

Thus the shared-prime contribution depends only on the balance vector

`b_p = sum_chi m_chi,p`.

For the Dirichlet-family application, the shared scale is `a_p=p^-1`, while the twists `u_chi,p=chi(p)`
are roots of unity. If the positive modulus part is trivial, the positive and negative prime products
attached to `b` agree. Unique factorization then gives `b=0`, hence

`sum_chi m_chi,p = 0`

for every prime `p`. The remaining relation is only the twist/root-of-unity part.

## Gates
- [x] 0 -> 1  in-progress: finite family product split extracted from the family-DSS/GSH resolution.
- [x] 1 -> 2  fully-proven: paper proof above by finite support, commutativity, and unique factorization.
- [x] 2 -> 3  formalized: Lean definitions/theorems `familyExponentSum`, `familyTwistedProduct`,
  `familyTwistedProduct_split`, `familyPrimeBalance`,
  `familyPrimeBalance_apply_eq_zero_of_primeProduct_eq`, and
  `familyPrimeBalance_apply_eq_zero_of_primeLogFrequency_eq_zero` in
  `formal/GaloisForLFunctions/FamilyCrossResonance.lean`; scratch `#check` / `#print axioms`,
  `lake build`, and `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the formal certificate for the modulus/root-of-unity split in the
  family-DSS/GSH resolution.

## Log
- 2026-06-19 - Leaner split this exact finite algebraic core from `family-dss-gsh` section R1. The parent
  card remains in `2-fully-proven` because Dirichlet characters, finite cyclotomic Galois structure, GSH,
  zero statistics, and the A2/F1 value-lift layer are not fully Lean-formalized.
