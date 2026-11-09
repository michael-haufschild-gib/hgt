# Finite-energy functional-equation rigidity

- **ID:** euler-fe-finite-energy-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Programme:** Euler–FE transport theory; Exact-event theory of Euler products.
- **Target:** Replace integrability of the uncompleted FE defect by square integrability
  in the established Hamburger-strip Beurling classification.

## Exact scope

Retain the countable positive Beurling system, inverse-3/2 moment, strip regularity and
decay of `E`, and actual Hamburger boundary identities from
`../3-formalized/exact-event-decaying-fourier-defect-rigidity.md`.
For measurable polynomially bounded `g ∈ L²(ℝ)`, the proved conclusion is
`β=½`, ordinary integer counting measure, unique norm factorization, and a
norm-preserving bijection of prime labels with rational primes.

## Mechanism

The actual defect is the Laplace transform of its Mellin source. The proved strong
boundary identification gives `‖Bg‖²=π⁻¹‖g‖²` and permits every `L²` test pairing
(`../3-formalized/euler-fe-hardy-laplace-transport.md`).
For the height-space tent `T_(h,a)(y)=max(1-|y-a|/h,0)`,

    |∫ T_(h,a)(y) Re(Bg(y))dy| ≤ √(2h) ‖Bg‖₂.

Thus errors tend to zero uniformly as the width tends to zero. At fixed width they
tend to zero as `a→∞`, by the `L²` tail of `Bg`. Atomic recurrence therefore
retains the unit-gap mechanism of the integrable-defect proof.

The Laplace representation gives the height-uniform bound

    |εJ_g(ε+iy)| ≤ ‖ψ_g‖₂ √(2ε)/2.

Consequently `εJ_g(ε+iy)→0`, the residue scale needed for pole reality and extraction
of atomic coefficients. No pointwise boundary representative is needed.

For the origin pairing, conjugation symmetry of the actual interior defect passes
through an almost-everywhere subsequence of the strong boundary limit. This makes
`Re Bg` even almost everywhere. Positive unit-gap vanishing therefore removes the
entire origin tent. Its strong boundary limit is enough for the Fejér extraction;
the integrable-defect proof's pointwise majorant is unnecessary.

## Formalized proof

1. **Proved in Lean:** the actual theta/tent identity with the canonical `L²` boundary
   (`tent_boundary_identity_of_finite_energy_defect`).
2. **Proved in Lean:** the small-width and translated-tent estimates above
   (`abs_finiteEnergyTentError_le`, `tendsto_finiteEnergyTentError_atTop`,
   `tendsto_finiteEnergyTentError_smallWidth`).
3. **Recurrence proved in Lean:** `P_h(y)<¼ ⇒ P_(h/2)(y)=0`, and sufficiently small
   unit-gap tents have zero boundary pairing. **Gap proved in Lean:**
   `beurling_finiteEnergyBoundary_re_eq_zero_on_unit_gap` gives almost-everywhere
   vanishing of the real canonical boundary on `(0,1)`.
4. **Integer support proved in Lean:** almost-everywhere reflection and the origin
   Fejér identity force every generalized-integer norm to be natural
   (`beurling_intNorm_nat_of_finiteEnergy_theta_defect`). The vanishing radial
   residue, real pole coefficient, unit multiplicities and full lattice filling
   are also proved in Lean (`integer_spectrum_of_integer_support_finiteEnergy_defect`).
5. **Prime classification proved in Lean:**
   `beurlingSystem_rigidity_of_finiteEnergy_theta_defect` and
   `beurlingSystem_rigidity_of_finiteEnergy_defect` identify the ordinary counting
   measure and rational-prime labels. Every nonclassical system has infinite
   defect energy (`nonclassical_beurling_defect_energy_eq_top`). The paper proof
   and module list are in `euler-fe-finite-energy-integer-support.md`.

All terminal theorems pass direct Lean checks and use only `propext`,
`Classical.choice`, and `Quot.sound` transitively.
`euler-fe-finite-energy-defect-annihilation.md` completes the classification of
the defect itself: zero almost everywhere for the theta formulation, and zero
pointwise for the original strip formulation.

This is an extension of the defect-classification branch. It does not exclude a finite
exceptional layer of ζ or prove height replication.
