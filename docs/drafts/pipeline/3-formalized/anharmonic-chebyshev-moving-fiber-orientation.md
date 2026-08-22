# Anharmonic Chebyshev moving-fiber orientation sector

- **ID:** anharmonic-chebyshev-moving-fiber-orientation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Rouyea--Bourgeois (2026), Proposition 6.9 and Remark 6.10; new invariant-coordinate orientation analysis
- **Statement:** Möbius recentering loses fixed exceptional-point locality but retains an exact finite moving anharmonic fiber; its coordinate-correct Xi standard sector has a nonnegative full-`S₃` Hermitian energy, while every cyclic-invariant scalar holomorphic quadratic is isotropic.

## Goal

Identify information discarded by the scalar `q²` Chebyshev descent and determine whether the
scale-dependent Möbius scan really requires infinite source data, or only changes source anchors.
Result must expose a concrete positive survivor and connect it to actual completed Xi, not merely
restate a representation-theoretic obstruction.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, explicit hostile tests, literature baseline identified
- [x] 1 → 2 fully-proven: exact algebraic proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean modules named below; direct compile and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone novelty audit and arithmetic consequences remain open

## Literature baseline

- Zhang, [A Hausdorff moment problem and the Riemann hypothesis](https://arxiv.org/abs/2303.09396),
  proves an RH-equivalent Hausdorff finite-difference criterion. Corpus theorem
  `scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis` already gives an
  endpoint-calibrated form, so no duplicate alias was added.
- Rouyea--Bourgeois,
  [A Chebyshev Trace Criterion for the Riemann Hypothesis](https://www.alphaxiv.org/abs/2608.chebyshev-trace-riemann-hypothesis),
  gives the order-three quotient, `q²` descent, Koebe trace, bounded-trace RH criterion, and the
  scale-dependent Möbius scan. Their Remark 6.10 correctly says recentered coefficients generally
  depend on infinitely many *original trace coefficients* and therefore leave their fixed
  three-point information class.
- The moving-fiber reinterpretation and `q`-normalized Xi orientation energy below are not claimed
  in that paper. They are new to this corpus. External novelty beyond this targeted current-source
  audit remains to be established before publication.

## Conjecture loop

### C1 — scalar holomorphic orientation energy

**Conjecture.** An odd or standard `S₃` sector supplies a scalar holomorphic positive orientation
detector lost by `q²` descent.

**Hostile test.** Classify every cyclic-invariant quadratic on difference coordinates
`p = a-b`, `q = b-c`.

**Failure.** Every such quadratic is a scalar multiple of

`p² + p q + q²`.

Over `ℂ` this Casimir is isotropic on the nonzero vector
`(p,q) = ((-1+i√3)/2,1)`. Scalar holomorphic quadratic positivity is impossible.

### C2 — doubled Hermitian survivor

**Conjecture.** Conjugate doubling repairs isotropy.

**Result `[PROVED HERE]`.** The energy

`‖a-b‖² + ‖b-c‖² + ‖c-a‖²`

is cyclic- and reflection-invariant, nonnegative, and zero exactly when `a=b=c`. Positivity forces
a Hermitian/doubled sector; trivial-sector scalar compression cannot retain orientation.

### C3 — moving locality under Möbius scanning

**Conjecture.** Recentring destroys fixed locality but retains finite moving-orbit locality.

**Hostile test.** A generic statement that order-`n` coefficients depend on an order-`n` jet at the
new center is only chain-rule infrastructure. Require exact source anchors, fiber cardinality,
real-sheet geometry, Koebe center, and actual Xi current.

**Result `[PROVED HERE]`.** For `s,z ∉ {0,1}`,

`q(z)² = q(s)²`

iff `z` belongs to the cyclic orbit of `s` or the cyclic orbit of `1-s`. For real `s>2`, one cyclic
orbit has points in `(2,∞)`, `(1/2,1)`, and `(-1,0)`. An explicit real center `a(q)∈(0,1)` satisfies

`27 a(q)/(1-a(q))² = q²`.

Thus Möbius scanning leaves fixed exceptional-point locality but retains finite moving six-point
locality, folded by Xi's functional equation to a moving three-point orbit.

## Invariant-coordinate split

Define

`D_q log xi(s) = (xi'/xi)(s) / q'(s)`

with

`q'(s) = 1 + 1/s² + 1/(s-1)²`.

The Jacobian satisfies the exact cyclic covariance laws

`q'(w(s)) w'(s) = q'(s)`,

`q'(w²(s)) (w²)'(s) = q'(s)`.

For every real `s>2`, the descended product current splits exactly as

`D_q log (xi(s) xi(w(s)) xi(w²(s)))`

`= D_q log xi(s) + D_q log xi(w(s)) + D_q log xi(w²(s))`.

This sum is the trivial sector. The standard-sector energy

`E_q(s) = Σ_cyclic ‖D_q log xi(s) - D_q log xi(w(s))‖²`

is nonnegative, invariant under the cyclic generator and reflection, and vanishes exactly when all
three `q`-coordinate Xi logarithmic derivatives coincide.

## Higher-principle interpretation

Repeated scalar-positivity failures are shadows of one quotient principle: invariant scalar descent
retains the trivial representation and erases the standard representation. Over `ℂ`, the unique
holomorphic quadratic Casimir on that standard sector is isotropic. Positive orientation data
therefore cannot live in one scalar holomorphic channel; it requires conjugate doubling. The correct
derivatives are taken in invariant quotient coordinate `q`, not source coordinate `s`.

## Formal certificate

- `formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevOrientationCasimir.lean`
  - literature quotient/Koebe algebra
  - invariant quadratic classification and explicit isotropic witness
  - Hermitian positive survivor
- `formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevMovingFiber.lean`
  - exact three-/six-point fiber classification
  - real moving-orbit chambers and explicit Koebe scan center
  - actual Xi moving-three-point logarithmic current
  - `q`-normalized trivial/standard split and full-`S₃` Hermitian energy
- Both modules compile with this toolchain.
- Audited representative theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in either module.

## Open core and falsifiers

1. **Arithmetic producer:** derive a completed prime--Gamma formula for the three
   `D_q log xi` components or for `E_q(s)`. Algebra alone supplies no sign or bound.
2. **Non-theatre falsifier:** if the completed source formula is only an identity with an uncontrolled
   cross term, this lane does not advance RH and must pivot.
3. **Useful target:** a source-pure bound or monotonicity law for `E_q(s)` coupled to the Chebyshev
   trace current. Any claimed RH consequence must pass the existing exact-tail audit.
4. **Publication gate:** search current literature specifically for invariant-coordinate orbit
   variance of logarithmic derivatives before claiming external novelty.

## Log

- 2026-08-22 — literature baseline checked; C1 falsified with exact classification and isotropic witness.
- 2026-08-22 — C2 Hermitian survivor proved on paper and in Lean.
- 2026-08-22 — C3 strengthened from generic finite jets to exact moving fibers, explicit scan center,
  and actual Xi invariant-coordinate split; formalized and axiom-audited.
