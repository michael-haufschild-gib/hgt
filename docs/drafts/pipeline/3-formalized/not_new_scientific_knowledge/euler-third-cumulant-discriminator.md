# The third-cumulant resonance discriminator of multiplicativity

- **ID:** euler-q3-discriminator
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** T1 of `../../rh-monodromy-weight-mismatch/123-constraint-reframe-catalog.md`;
  parent `docs/rh/berry_higher_cumulant_sign_structure_20260618.md`,
  `berry_discriminator_scoping_and_genuine_RH_test_20260618.md`,
  `opus_euler_product_is_the_RH_ingredient_20260615.md`.
- **Statement:** The third moment (bispectrum) of a finite trigonometric field is the sum over
  additive frequency resonances `k+l+m=0` of its Fourier coefficients; the minimal resonance is the
  fundamental–second-harmonic `1+1=2`, and multiplicativity (the Euler local factor
  `log((1-w)⁻¹)=∑wᵏ/k`, `x²`-coefficient `1/2`) forces the second harmonic `b=a²/2`, hence a strictly
  positive third moment `(3/8)a⁴`; a tower-free / non-multiplicative field has zero third moment.

## Goal

Make theorem-grade the parent's *measured* discriminator `Q_3` (`|Q_3|/|Q_1|` ≈ 0.20→0.25 for ζ,
≈0.07 for DH), by isolating its structural cause without any hard analytic number theory. The cause:
the third cumulant of the critical-line log-field `log|ζ(½+it)| = ∑_p ∑_k (1/k)p^{-k/2}cos(k·t log p)`
is carried by the intra-prime resonance `k=1,1,2` — the fundamental (`p`) with its second harmonic
(`p²`) — which multiplicativity forces and a non-multiplicative field lacks. This is the "codim-2
Hermitian non-crossing" of `opus_euler_product_is_the_RH_ingredient` read at the level of the third
cumulant: the second harmonic is the codim-2 (prime-square) direction, and the third cumulant is the
lowest one that sees it (the 2-point / variance is RH-blind, the divergent Selberg `½loglog`).

## Gates

- [x] 0 → 1 — well-posed; source-pure (structural cause, no ζ-analytics); Door passport: Door-1 object
  (native invariant of the log-field), Door-3 native invariant (a cumulant), Door-5 restricts to the
  known Selberg diagonal.
- [x] 1 → 2 — complete paper proof (below), no open dependency at the mechanism level.
- [x] 2 → 3 — Lean module `GaloisForLFunctions/RHTower/ThirdMomentResonance.lean`, `lake build`
  green, `#print axioms` = `[propext, Classical.choice, Quot.sound]` on every theorem, formal lint
  passes.
- [ ] 3 → 4 — **BLOCKED by the novelty grade (see Verdict): not publication-track as new knowledge.**

## The Lean certificate (axiom-clean)

`GaloisForLFunctions/RHTower/ThirdMomentResonance.lean`:

- `integral_cexp_int` — character orthogonality `∫₀^{2π} exp(i·j·θ) = 2π·[j=0]`.
- `thirdMoment_eq_resonance` — **the bispectrum**: `M₃(c,S) = ∑_{k+l+m=0} c_k c_l c_m`.
- `thirdMoment_pureTone` — spectrum `{±1}` ⟹ `M₃ = 0` (no odd 3-resonance `±1±1±1≠0`).
- `thirdMoment_two_harmonic` — `a·cosθ + b·cos2θ` ⟹ `M₃ = (3/4)a²b`.
- `thirdMoment_multiplicative` — `b = a²/2` ⟹ `M₃ = (3/8)a⁴`.
- `thirdMoment_discriminator` — tower-free `b=0` ⟹ `0`; multiplicative `b=a²/2` ⟹ `≠0` (`a≠0`).
- `thirdMoment_multiplicative_pos` — real `a≠0` ⟹ `M₃ = (3/8)a⁴ > 0` (ζ prime `p`: `a=p^{-1/2}`,
  gives `(3/8)p^{-2}`).
- `thirdMomentR_pos_of_tower` — **general tower, no truncation**: any real nonnegative-coefficient
  field whose spectrum carries the fundamental and second harmonic positively has strictly positive
  third moment (every resonance term `≥0`, the `1+1=2` term `>0`). This is the full ζ tower.

## Approach (paper proof of the mechanism)

Model the per-prime log-field on the line as `f(θ)=∑_k c_k cos(kθ)` with `θ = t·log p`. Character
orthogonality on the circle kills every triple of frequencies except those with `k+l+m=0`, so the
third moment is the bispectrum `∑_{k+l+m=0} c_k c_l c_m`. A pure tone (`{±1}`) has no such triple
(`±1±1±1` is odd). The lowest resonance is `1+1=2`, needing a second harmonic. For an Euler factor
`(1-w)⁻¹`, `-log(1-w)=∑wᵏ/k` gives the `p²` amplitude `= ½·(p^{-1})`, i.e. `b=a²/2` with `a=p^{-1/2}`;
so `M₃ = (3/4)a²b = (3/8)a⁴ = (3/8)p^{-2} > 0`, convergent over `p` (`∑p^{-2}<∞`, the parent's proven
"higher cumulants bounded"). A non-multiplicative field with no forced second harmonic (`b=0`) has
`M₃=0`. Cross-prime resonances `k log p + l log q + m log r = 0` are excluded by ℚ-independence of
`{log p}` (Baker; the tree's `LogIndependence.lean`), so the third moment localizes to the
single-prime diagonal — this is unique factorization read as the absence of cross-prime additive
resonance. (The multi-variable diagonal localization is the known Baker input, not re-formalized.)

## Verdict — dual gate

**DELIVERED (formalized):** the theorem "multiplicativity forces the third-cumulant signature" is
proven and machine-checked, axiom-clean, with the general tower (no truncation). T1's own success
criterion is met.

**KILLED as new knowledge (reduce-to-known × RH-blind):**
- *Novelty:* the mechanism is the **bispectrum** (third moment = additive-resonance sum, standard
  harmonic analysis / signal processing) composed with the **Selberg cumulant** structure of `log ζ`
  (the higher cumulants live on the convergent prime-power diagonal). A competent literature search
  produces both. The cross-prime localization is Baker's `{log p}`-independence. So the invariant is
  real and native-*flavoured* but **reduces to known** — it does not clear the NOVEL gate.
- *Significance:* the invariant tracks **multiplicativity, not RH** — it is blind to zero location
  (parent scoping: ζ and the Dirichlet L Λχ are both multiplicative with large `Q_3`; only the
  non-multiplicative DH is separated). It does not even single out the FE-class; it is a plain
  Euler-product detector. RH would enter only through the **sign** of the second-harmonic amplitude
  `b` across the tower — the definiteness of that sign is Weil positivity, RH-equivalent, and
  correctly *outside* this invariant (T1 "stops short of ⟹RH" — confirmed structurally here).

**Banked value:** a clean, axiom-clean formal anchor for the parent's surviving structural insight
"the Euler product is the RH ingredient — it supplies the codim-2 non-crossing": the codim-2
direction is the second harmonic, and the third cumulant is the lowest one that detects it. This is
branch infrastructure (a formal handle on the Euler/FE separation), not a peak.

**Where it points (not a terminus):** the invariant sees magnitude, not sign; the *sign* of the
tower's second-harmonic amplitude is the untouched RH-bearing datum. The live constraint-side object
remains the sign/polarization (the weld `ω` / T2, the HP-index of `123-constraint-reframe-catalog`),
where the third-cumulant magnitude is now a proven-free backdrop and the sign is the open content.

## Log
- 2026-07-07 — created directly in 3-formalized: mechanism proven + formalized axiom-clean
  (`ThirdMomentResonance.lean`, 10 theorems); dual-gate verdict recorded (delivered × reduce-to-known
  + RH-blind). T1 closed at the mechanism level.
