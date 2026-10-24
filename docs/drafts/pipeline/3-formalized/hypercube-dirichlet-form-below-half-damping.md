# The hypercube Dirichlet form below half damping, and the natural form as the receiver

- **ID:** hdf-below-half
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2410/fable.md §2.3 B · BVI README §7.2, §7.5 · THIM §7.8.4
- **Statement:** For every `r > 1` and `0 ≤ ε < 1/2` the hypercube dilation Dirichlet form
  `D_{r,ε}(P) = Σ_{d₁,d₂ | P} μ(d₁)μ(d₂)(d₁d₂)^{-1/2-ε} Φ_r(d₁/d₂)` is unbounded over squarefree `P`
  coprime to `r` (growth `≥ c_r (2y)^{1-2ε}/log²(2y)` on prime blocks), for `μ` and for `|μ|`
  alike. The size-ordered (natural-cutoff) form with prime core `p` is bounded below its horizon
  iff the receiver is admitted.

## Goal
Opening B gives as its concrete finite problem and first rung a uniform-in-`P` bound for
`D_{r,ε}(P)` at one fixed `ε < 1/2` ("quasi-RH strength"). Decide it, and identify the finite form
the receiver actually needs.

## Paper proof
1. *Physical form.* `Φ_r(d₁/d₂) = √(d₁d₂)·stepGram(C_r(⌊·/d₁⌋), C_r(⌊·/d₂⌋))`, so for weights `w`
   and scales `D`, `Σ_{d₁,d₂∈D} w(d₁)w(d₂)(d₁d₂)^{-1/2-ε}Φ_r(d₁/d₂) = Σ_{n≥1} Ψ(n)²/(n(n+1))` with
   `Ψ(n) = Σ_{d∈D} w(d)d^{-ε}C_r(⌊n/d⌋)`.
2. *Depth-one plateau.* `y ≥ r`, `h = ⌊y/2r⌋`, `S` = primes in `(y, y+h]`, `P = ∏_S p`. For
   `(r-1)(y+h) ≤ n ≤ ry`: `⌊n/p⌋ = r-1` for `p ∈ S`; any divisor with two prime factors exceeds
   `y² ≥ n`. With `C_r(r-1) = -φ(r)`: `Ψ(n) = w(1)C_r(n) - φ(r)Σ_{p∈S} w(p)p^{-ε}`.
3. *Mass.* The plateau has pronic mass `≥ 1/(4r²y)`, so
   `D ≥ (φ(r)|Σ_S w(p)p^{-ε}| - B_r)²/(4r²y)` once `φ(r)|Σ| ≥ B_r`.
4. *Count.* PNT (`θ ~ x`): `Σ_{p∈S} p^{-ε} ≥ (2y)^{1-ε}/(16 r log 2y)` for large `y`, giving
   `D ≥ φ(r)²/(2048 r⁴)·(2y)^{1-2ε}/log²(2y) → ∞` for `ε < 1/2` when `w(p) = ±1` on primes.
5. *Natural form.* For `n ≤ N`, `Σ_{d≤N} μ(d)d^{-ε}C_r(⌊n/d⌋) = Σ_{ab=r} aμ(b)(α_ε⌊n/a⌋ + A_ε(⌊n/a⌋))`
   (floor expansion of `C_r` and `Σ_{d≤m} μ(d)d^{-ε}⌊m/d⌋ = α_ε m + A_ε(m)`). Admission bounds the
   head by the pronic dilation contraction. For a prime core it is `pA(⌊n/p⌋) - A(n) + O(p)`;
   exact block dilation gives `√p‖A‖_M ≤ K + ‖A‖_{pM+p-1}`, and `E_T = O(1+T^{1-2ε})` lets the
   backward iteration close: `‖A‖_M ≤ K₁/(√p-1)`.

## Lean
- `BezoutValuationIncidence/TheHypercubeDirichletFormDivergesBelowHalfDamping.lean`:
  `hasSum_signedDilationPrimitive_sq`, `signedDilationPrimitive_primeBlockProd_eq`,
  `plateau_le_signedDilationDirichletForm`, `eventually_primeBlock_rpow_mass_ge`,
  `eventually_signedDilationDirichletForm_ge`, `tendsto_hypercubeDilationDirichletForm_primeBlockProd`,
  `tendsto_hypercubeTwinDilationDirichletForm_primeBlockProd`,
  `not_bddAbove_hypercubeDilationDirichletForm`, `hypercubeDilationDirichletForm_threshold`.
- `BezoutValuationIncidence/TheNaturalCutoffDilationFormIsTheReceiver.lean`:
  `naturalDilationPrimitive_eq`, `naturalDilationPrimitive_prime_eq`, `sum_pronic_dilate_block_eq`,
  `bounded_naturalDilationHeadEnergy_of_mem_receiverDampings`,
  `mem_receiverDampings_of_bounded_naturalDilationHeadEnergy`,
  `bounded_naturalDilationHeadEnergy_iff_mem_receiverDampings`,
  `mem_receiverDampings_of_bounded_naturalDilationDirichletForm`,
  `re_le_of_bounded_naturalDilationDirichletForm_on_Ioo`.
- Both files checked with `lake --old env lean`; `#print axioms` on the main theorems:
  `propext, Classical.choice, Quot.sound`. Wired into `BezoutValuationIncidence.lean`.

## Consequences for opening B
- The first rung as stated is false: no bound at any fixed `0 ≤ ε < 1/2` exists for the hypercube
  form, unconditionally. It is not the finite form of `ζ(1+ε)ζ(1+ε)^{-1} = 1` the receiver needs.
- Its threshold `1/2` is the same for `μ` and `|μ|`: the hypercube form is sign-blind (Class II).
- The size-ordered form is the receiver itself: its head is bounded exactly at `receiverDampings`,
  and a cutoff-uniform bound on a band of dampings is a zero-free strip. The corrected first rung
  is exactly the receiver; opening B has no finite proxy below it in this family.
- Open endpoint: `ε = 1/2` for the hypercube form (not needed by the receiver).
- Independent Mellin-side proof of the divergence for `-1/2 ≤ ε < 1/2`:
  `SignedSuccessorArithmetic/TheHypercubeDirichletFormIsUnbounded.lean`
  (`hypercubeDilationDirichletForm_unbounded`). The physical-space proof here adds the explicit
  rate, the parity twin and the natural-form equivalence.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** depth-one plateau of a prime block
  (`signedDilationPrimitive_primeBlockProd_eq`, `tendsto_hypercubeDilationDirichletForm_primeBlockProd`).
- **Strongest positive survivor:** sign-blind threshold law (`hypercubeDilationDirichletForm_threshold`)
  and the exact replacement: natural head ⟺ admission
  (`bounded_naturalDilationHeadEnergy_iff_mem_receiverDampings`).
- **New insight:** cross-depth cancellation must be organised by size, and organised by size it is
  the receiver.
- **Status:** dependency-closed in Lean.

## Log
- 2026-10-24 — created in 1-in-progress; paper proof complete
- 2026-10-24 — formalized; moved to 3-formalized
