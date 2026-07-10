# Thue--Morse finite products discharge the entire Mellin interface

- **ID:** thue-morse-mellin-flatness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[PROVED HERE]`
- **Date:** 2026-07-10
- **Source:** `../../2-fully-proven/new/thue-morse-entire-dirichlet-order-two.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/ThueMorseMellinFlatness.lean`
- **Statement:** Every finite binary product obeys the exact all-order bound
  `exp(-x) prod_{k<m}(1-exp(-2^k x)) <= 2^(m(m-1)/2)x^m`. Any complex kernel dominated by all
  those finite products, locally integrable on `(0,infinity)`, and exponentially decaying at
  infinity has a Mellin transform analytic on the whole complex plane.

## Delivered theorem chain

- `HasAllOrderZeroBound`: concrete natural-power bounds `||f(x)|| <= C_m x^m` on `(0,1]`.
- `HasAllOrderZeroBound.superpolynomialDecayAtZero`: discharges every real zero-side big-O
  exponent by choosing a natural `m >= -b`.
- `IsMellinFlatKernel`: local integrability, one exponential tail, and all-real zero-side decay.
- `IsMellinFlatKernel.mellinConvergent`: Mellin convergence for every `s : C`.
- `IsMellinFlatKernel.mellin_differentiable`: whole-plane complex differentiability.
- `IsMellinFlatKernel.mellin_analyticOnNhd`: whole-plane analyticity.
- `thueMorseFiniteKernel_flat_bound`: the exact finite product inequality with coefficient
  `2^(m(m-1)/2)`.
- `IsThueMorseKernelBound.hasAllOrderZeroBound`: finite-product domination supplies every natural
  order.
- `IsThueMorseKernelBound.superpolynomialDecayAtZero`: the full real-exponent interface is derived.
- `IsThueMorseKernelBound.isMellinFlatKernel`: the all-order hypothesis is removed from the caller.
- `mellin_analyticOnNhd_of_thueMorseKernelBound`: capstone; finite binary-product domination plus
  local integrability and one exponential tail imply an entire Mellin transform.

## Proof content

The finite estimate uses only

`0 <= 1-exp(-u) <= u` for `u>=0`

and

`prod_{k<m}(2^k x) = 2^(m(m-1)/2)x^m`.

For an arbitrary Mellin parameter `s`, the quantifier-changing theorem chooses the zero exponent
`b=Re(s)-1`. The bound family supplies `O(x^{-b})` at zero, and mathlib's exponential-tail Mellin
theorem supplies differentiability at `s`. Since `s` was arbitrary, the transform is analytic on
`C`.

## Scope

- `[PROVED]` The caller no longer supplies a separate zero-side Mellin hypothesis for each `s`.
- `[PROVED]` The result is vector-valued over every complete complex normed space.
- `[PROVED]` The exact binary coefficient `2^(m(m-1)/2)` is formalized, not hidden in an existential
  constant.
- `[OPEN CORE]` The actual infinite Thue--Morse product has not yet been constructed in Lean or
  connected to the shifted coefficient series.
- `[OPEN CORE]` The matching lower product bound and exact Hadamard type `(log 2)/2` remain paper-only.
- `[BRIDGE]` Mellin strip holomorphy is mathlib infrastructure. The new formal payload is the
  all-order quantifier discharge and its exact binary-product instantiation.

## Verification

- Target module compile: PASS.
- Target module build: PASS (`8475` jobs).
- Scratch `#check`: PASS for the five principal theorems.
- Scratch `#print axioms`: each principal theorem uses only
  `{propext, Classical.choice, Quot.sound}`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.

## Gates

- [x] 0 -> 1: exact interface and finite source bound isolated.
- [x] 1 -> 2: proof complete.
- [x] 2 -> 3: formalized, target build and axiom audit pass.
- [ ] 3 -> 4: requires formal construction of the infinite product and the exact order/type layer.

## Next generative move

Construct the positive infinite binary product as the monotone limit of the finite kernels and prove
that its omitted tail lies in `[0,1]`. The capstone then yields the entire Mellin transform with no
new analytic hypotheses; the remaining scientific layer is the matching lower flatness estimate,
which determines the exact type.

## Concrete infinite-product update

- 2026-07-10 — `thueMorseFactor` and `thueMorseKernel` now construct the actual positive infinite
  binary product in Lean. Summability of the exponential defects proves `Multipliable`; monotonicity
  of the finite prefix products proves that the infinite product is nonnegative, at most one, and
  bounded above by every finite prefix.
- `[PROVED]` `thueMorseMellinKernel_bound` instantiates `IsThueMorseKernelBound` for the concrete
  infinite product.
- `[PROVED]` measurability, a global norm bound by one, local integrability on `(0,infinity)`, and
  big-O of `exp(-x)` at infinity are discharged in Lean.
- `[PROVED]` `thueMorseMellinKernel_mellin_analyticOnNhd` proves that the Mellin transform of the
  concrete infinite product is analytic on the whole complex plane.
- `[OPEN CORE]` The formal series identity connecting this product to the shifted signed
  Thue--Morse Dirichlet series is not yet present.
- `[OPEN CORE]` The matching lower flatness estimate and exact Hadamard order-two type remain
  paper-only.

The earlier scope item saying that the infinite product had not been constructed is superseded by
this update. The targeted module build still passes at `8475/8475`, and the four added principal
claims have axiom set `{propext, Classical.choice, Quot.sound}`.
