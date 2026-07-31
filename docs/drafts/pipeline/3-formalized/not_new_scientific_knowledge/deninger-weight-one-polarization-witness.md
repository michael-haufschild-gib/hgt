# The corpus's RH-bearing structure had no instance. Now it has one.

- **ID:** `deninger-weight-one-polarization-witness`
- **Stage:** 1-in-progress
- **Type:** NON-VACUITY WITNESS (formalized)
- **Scientific status:** `[LEAN-PROVED, AXIOM-CLEAN]` `[NOT NEW MATHEMATICS]` `[NOT AN RH PROOF]`
- **Module:** `formal/GaloisForLFunctions/RHTower/DeningerWeightOnePolarizationWitness.lean`

## 1. What the corpus proves, and what it rests on

`RHTower/DeningerWeightOnePolarization.lean` proves

```text
eigenvalue_re_eq_half
    (P : DeningerWeightOnePolarization H) {rho : C} {v : H}
    (hv0 : v ≠ 0) (hv : P.theta v = rho • v) :
    rho.re = 1 / 2
```

— *every eigenvalue of a polarized weight-one Frobenius-flow generator lies on the critical line.*
The proof is four lines: `theta_inner_sum` (`⟪θx,y⟫ + ⟪x,θy⟫ = ⟪x,y⟫`, itself three rewrites from the
axioms) plus positivity of `⟪v,v⟫`. **This is the RH conclusion of the whole Deninger lane**, and it
is correct.

Everything therefore sits in the hypothesis. `DeningerWeightOnePolarization` bundles: a generator
`theta`, a nondegenerate bilinear `cupTrace`, an odd `KRealStructure` (anti-linear `sigma` with
`sigma^2 = -1`), the derivation law `theta_cup`, commutation `star_theta`, and the Hodge realisation
`inner_eq_cup_star`.

**It is consumed in two modules and constructed in none.** `grep` over the whole tree finds the
structure declaration, the umbrella import, and `DeningerClosedOperatorPolarization` — no `def`, no
instance, no witness. That is blind spot (b) of `prop-interface-discharge-audit.md` (bundled data
consumed as a hypothesis, constructed nowhere), and this particular structure is not in that audit's
table of 28.

An implication whose hypothesis has no instance proves nothing about anything.

## 2. The witness

On `H = EuclideanSpace C (Fin 2)`:

```text
sigma (z0, z1) = (-conj z1, conj z0)          anti-linear, sigma^2 = -1
omega (x, y)   = x0 * y1 - x1 * y0            nondegenerate, and SKEW
theta_t        = (1/2 + i t) on e0,  (1/2 - i t) on e1
```

`polarization (t : R) : DeningerWeightOnePolarization Carrier` verifies every axiom, for every real
`t`, and is axiom-clean `[propext, Classical.choice, Quot.sound]`. Feeding it to
`eigenvalue_re_eq_half` type-checks, so the RH-bearing implication is now instantiated on a concrete
package.

Two structural facts fell out of building it, and both constrain any arithmetic realisation:

- **`sigma^2 = -1` is impossible in complex dimension one.** For anti-linear `sigma z = c * conj z`
  one gets `sigma^2 = |c|^2 > 0`. So the carrier must have even complex dimension — the odd K-real
  structure is a quaternionic structure.
- **A scalar `theta` forces its eigenvalue to be real.** `star_theta` with `theta = rho • id` gives
  `conj rho = rho`. So a witness with `t ≠ 0` must have non-scalar `theta`; the witnesses above
  realise an entire real line of eigenvalue pairs `1/2 ± i t`.

The second point is what makes the witness worth having rather than a formality: it shows the axioms
do **not** collapse to the trivial case, and that `eigenvalue_re_eq_half` has genuine content on the
instances that exist.

## 3. The skewness, and what it means for the reduction

`omega` is skew, matching what the arithmetic assembly actually uses: in
`RHTower/DeningerArithmeticPoissonZetaAssembly.lean` the middle cup pairing is built with
`hpsiSkew : ∀ h k, psi h k = - psi k h`, so `psi h h = 0` identically. **No positivity is free.** The
positive form is the twist `Q(h,k) = psi(h, C k)` by the complex structure — in the weight-one
package, `inner_eq_cup_star` is exactly that twist, with `C = sigma` the Hodge star.

So the correct reading of the lane's open clause is neither "connectivity" (my earlier reframing,
retracted in `deninger-lane-reduces-to-one-hypothesis.md` §11) nor "construct a positive energy". It
is: **exhibit the K-real structure and the cup trace whose twist is positive definite** — the second
Riemann bilinear relation of the would-be arithmetic Hodge structure.

## 4. Honest grade

- **This does not advance RH by one inch.** A finite-dimensional witness with a hand-chosen `theta`
  is not the arithmetic cohomology; the arithmetic case is infinite-dimensional with `theta`'s
  spectrum required to be the zeta zeros.
- **What it does establish** is that the corpus's RH-bearing implication is not vacuous, that its
  axioms are mutually consistent, and that they are not secretly forcing the degenerate case. Before
  this file, none of that was known — the structure had never been instantiated.
- The mathematics is elementary linear algebra over `C^2`. Its only claim on attention is that
  nobody had checked whether the hypothesis of the corpus's headline purity theorem can be satisfied
  at all.

## Gates

- [x] witness constructed and axiom-clean
- [x] witness feeds `eigenvalue_re_eq_half` (type-checked)
- [x] non-scalar `theta` with eigenvalues `1/2 ± i t` for arbitrary real `t`
- [x] even-dimensionality of the carrier forced by `sigma^2 = -1`
- [ ] an infinite-dimensional witness with unbounded spectrum
- [ ] the arithmetic realisation — this is RH
- [ ] independent audit (Codex; the structure is in his lane)

## Log

- 2026-07-27 (Claude): found while chasing the polarization question raised by the skewness of the
  arithmetic cup pairing. Checked whether `DeningerWeightOnePolarization` is ever constructed; it is
  not. Built a witness rather than report the gap, because a gap in an unwitnessed interface is not
  a finding until you know the interface can be satisfied.

## Gate closure (2026-07-31)

Repo-state verification (per the standing rule: verify modules, not card text): the gate
"an infinite-dimensional witness with unbounded spectrum" was completed in
`RHTower/DeningerPreHilbertUnboundedWitness.lean` (umbrella-registered, axiom-clean):
the pre-Hilbert carrier `⨁_n ℂ²` with `exists_polarization_with_prescribed_spectrum`
(a polarization package for **every** real spectrum sequence) and `not_completeSpace_carrier`
(incompleteness derived from the unbounded-spectrum no-go). See
`deninger-complete-carrier-forbids-zeta-spectrum.md` §6–§7, which also proves the sharper
statement this card's gate asked for: the axioms constrain the spectrum to exactly
"critical line, conjugation-closed" and nothing else.

Updated gates:

- [x] witness constructed and axiom-clean
- [x] witness feeds `eigenvalue_re_eq_half` (type-checked)
- [x] non-scalar `theta` with eigenvalues `1/2 ± i t` for arbitrary real `t`
- [x] even-dimensionality of the carrier forced by `sigma^2 = -1`
- [x] an infinite-dimensional witness with unbounded spectrum — DONE
      (`DeningerPreHilbertUnboundedWitness`, prescribed-spectrum form)
- [ ] the arithmetic realisation — this is RH (programme-wide wall, tracked by
      `deninger-two-halves-do-not-compose`)
- [ ] independent audit (Codex; external)

The card's own topic — non-vacuity of the corpus's RH-bearing polarization interface — is
complete and fully formalized. Moving to `3-formalized/not_new_scientific_knowledge` per its
own `[NOT NEW MATHEMATICS]` self-grade.
