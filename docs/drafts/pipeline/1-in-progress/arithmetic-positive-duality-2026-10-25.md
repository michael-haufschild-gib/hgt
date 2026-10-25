# Arithmetic Positive Duality (APD)

- **ID:** arithmetic-positive-duality-2026-10-25
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) — research programme
- **Source:** `docs/reports/review-2510/fable.md` §4 (the proposed field), §1, §2.3, §3 Focus 1
- **Statement:** Develop the rigidity theory of positive arithmetic Poisson pairs under
  self-duality and integer quantization: answer the seven central questions of §4.2 and build
  the tools listed there.

## Goal
Lean programme `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`, umbrella
`ArithmeticPositiveDuality.lean`, foundational README, unconditional theorems.

## Plan (topics → modules)
- **A. Theta rigidity (existing).** `PositiveMeasureHamburgerRigidity`,
  `BeurlingRiemannFunctionalEquationRigidity`: audit, compile, wire.
- **B. Herglotz–Bochner on `ℤ^r` (tool).** PD functions on `ℤ^r`; Fourier coefficients of positive
  measures on `T^r` are PD; finitely supported PD ⇔ nonnegative trig polynomial; full Herglotz.
- **C. Integer PD classification (Q1).** On every abelian group: integer-valued even PD with
  `φ 0 = 1` ⇔ `±1` character on a subgroup; isolation ⇒ `δ₀` iff no 2-torsion; rank-`r` realization.
- **D. Exact multi-frequency barrier (Q2).** Bohr projection onto rational fibres preserves
  nonnegativity; exact barrier of a finite-spectrum certificate = Fejér barrier of the rational
  fibre; Kronecker line: a second prime never raises the purchase ratio of the first.
- **E. Poisson rigidity (Q5).** Positive self-dual measure with gap `(−1,1)∖{0}` is a Dirac comb;
  wider gap forces zero.
- **F. Two-prime Bochner (Q3).** Restriction of PD functions to `ℤ log p + ℤ log q` and the
  push-forward of spectral measures; RH ⇔ the spline two-prime correlation is the coefficient
  sequence of a positive measure on `T²`.
- **G. Weil-pair gap identity (Q5).** Tent identity at prime-free aperture; same-side gap.
- **H. `𝔽_q` calibration.** Weil's theorem as PD on `ℤ` of the normalized trace sequence, budget `2g`.
- **I. Non-commutative carrier (Q6).** Positive extensions over the finite affine quotient.
- **J. Topology (Q7).** Jet topology on the Meyer source.
- **K. Quantized budget (Q4).**

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized: modules compiled with `lake --old env lean`, wired, axioms audited
- [ ] 3 → 4  README final

## Status
- README first draft written.

## No-go closure
(per topic, when a route closes)
