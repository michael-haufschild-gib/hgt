# OWU: blind odd window closed at pole weight 1 (2026-10-16, Lean) — MUST-1560

Card: docs/drafts/pipeline/3-formalized/owu-odd-window-closed-at-one-2026-10-16.md.
Lean: formal/GaloisForLFunctions/RHTower/WeilOddWindowClosedAtOne.lean (namespace RHTower), wired into RHTower.lean,
axioms [propext, Classical.choice, Quot.sound].

- `sum_poleWeightArchRe_eq`: Σ c_f poleWeightArchRe β f = Σ c_f poleWeightArchRe 1 f + (β−1) Σ c_f Re P(k_f).
- `primeBlindPositiveOddAt_one_of_forall_lt`: (∀ β < 1, PrimeBlindPositiveOddAt β) → PrimeBlindPositiveOddAt 1.
- `primeBlindPositiveOddAt_one_iff_forall_lt`; `exists_weilPositiveOdd_iff_forall_lt_one`:
  (∃ lam, WeilPositiveOdd lam) ↔ ∀ β < 1, ∃ lam, WeilPositiveOddAt β lam.

Reading: the OWU source problem (critical pole weight) = family of sub-critical source problems (pole cancelled to
density β < 1). With MUST-1554: RH ⟺ a weight odd-positive at every β < 1 and positive on dilates of one bump.
The source itself is Λ (uniqueness theorems); finding it = proving WeilPositiveOdd Λ = RH.

Loop ledger (not formalised): pole-weight dichotomy conjecture — sources at β ≤ 0 RH-free (tempered λ(p) = c log p/√p,
odd lane row 1244, needs the line inequality c Re P₁(1+iτ) ≤ w(τ), tight near τ ≈ 0 and 6.3, w(0) = −2.69,
w(1) ≈ −1.0, w(2) ≈ −0.57, w(4) ≈ −0.23, crossing ≈ 6.3); density-positive sources must be Λ-like because the
Kronecker resonances of n^{−iτ} make any density-β Dirichlet series exceed ½ log τ on the line unless cancelled by
critical zeros (the explicit-formula structure). Under RH, (1−ε)Λ + ε λ_temp ∈ cone at β = 1−ε. Adding (1−β)·𝟙 to
raise the pole weight fails on the line (1 − Re ζ(½+iτ) changes sign). Re ξ'/ξ on the critical line is exactly the
on-line atoms (off-line quadruples cancel there); off-line zeros enter only as poles inside the slit domain.
