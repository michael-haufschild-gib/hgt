# Shifted polygamma jets as infinite positive spectral clocks

- **ID:** `shifted-polygamma-positive-spectral-clock`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`, quantum spectral moment value relation
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.GammaBoseSpectralHankel`
- **Statement:** For every real shift `a > 0`, the alternating-factorial-normalized positive-order
  digamma jet at `a` is the infinite positive moment sequence of the reciprocal ladder
  `E_j = j+a`; hence every finite Hankel block is positive definite and no uniformly bounded
  finite spectral, state-space, or linear-recurrence model can reproduce the all-order jet.

## Exact value relation

Fix `a > 0` and define

```text
E_j(a) = j+a,
x_j(a) = E_j(a)^(-1),
w_j(a) = E_j(a)^(-2),
M_m(a) = sum_(j>=0) w_j(a) x_j(a)^m.                       (1)
```

Lean proves

```text
M_m(a) = zeta(m+2,a),                                      (2)
psi^(m+1)(a) = (-1)^(m+2) (m+1)! M_m(a).                  (3)
```

Here `zeta(s,a)` is the project Hurwitz-zeta series.  Equation `(3)` is an exact observable-value
relation: the derivative-order label is the clock readout index, not time evolution.

At `a=1`, equation `(2)` specializes to `M_m(1)=zeta(m+2)`.  The generic theorem also applies
without modification at the quarter and half shifts occurring in archimedean Gamma factors and at
the half-integer shifts of oscillator spectra.

## Positive statement

Every weight `w_j(a)` is strictly positive, the reciprocal nodes `x_j(a)` are distinct, and all
absolute moments are summable.  Therefore Lean proves, for every finite size `N`,

```text
H_N(a) = [M_(i+j)(a)]_(0<=i,j<N) is positive definite,
det H_N(a) > 0.                                             (4)
```

The same conclusions hold after replacing `M_m(a)` by the actual signed normalized digamma jet

```text
J_m(a) = Re(((-1)^(m+2) psi^(m+1)(a))/(m+1)!).             (5)
```

Thus the no-go consequences rest on a nontrivial positive representation rather than on a bare
rank obstruction.

## Finite-model boundaries

Strict positivity in `(4)` directly discharges the nonzero-determinant hypotheses of the existing
HTGeometry finite-model boundaries.  Lean consequently proves, for every fixed `d`,

```text
not FixedSpectralWidthLocalClosure d J(a),
not FixedStateSpaceDimensionLocalClosure d J(a),
not E.IsSolution J(a)                                      (6)
```

for every positive-order real linear recurrence `E`.  Even if a different finite model is selected
for each longer observation window, its spectral width or state dimension cannot remain uniformly
bounded.

This contrasts with the already formalized inverse-Gamma local principal-part tower, whose
factorial-normalized Hankel matrices have rank one.  The local pole principal part is one geometric
ray; the equilibrium observable jet reports the full infinite shifted ladder.  The difference is
observability structure, not temporal propagation.

## Physics provenance

M. Tierz and E. Elizalde, *Heat kernel-zeta function relationship coming from the classical moment
problem*, arXiv:math-ph/0112050, identifies discrete spectral-zeta values with moment data for the
density of states and partition function in quantum mechanics and explains the dependence on the
zeta singularity structure.

The present Lean theorem is the elementary positive shifted-ladder instance of that general
spectral-zeta/moment interface.  It uses no claim that Gamma values generate a physical time flow.

## Lean surface

- `gammaBoseNode`
- `gammaBoseWeight`
- `gammaBoseMoment`
- `gammaBoseMoment_ofReal_eq_hzeta`
- `gammaBoseMoment_one_ofReal_eq_riemannZeta`
- `iteratedDeriv_digamma_eq_gammaBoseMoment`
- `signedNormalizedDigammaJet`
- `signedNormalizedDigammaJet_eq_gammaBoseMoment`
- `gammaBoseHankel_posDef`
- `det_gammaBoseHankel_pos`
- `signedNormalizedDigammaJet_hankel_posDef`
- `det_signedNormalizedDigammaJet_hankel_pos`
- `signedNormalizedDigammaJet_not_fixedSpectralWidthLocalClosure`
- `signedNormalizedDigammaJet_not_fixedStateSpaceDimensionLocalClosure`
- `signedNormalizedDigammaJet_not_linearRecurrence`

## RH impact and exact boundary

The theorem supplies an unconditional positive infinite-support spectral representation for the
Gamma/polygamma component at every positive shift.  It can therefore be inserted directly into
mixed scalar or matrix spectral constructions and discharges all positivity, summability,
infinite-support, and finite-rank-boundary obligations for that component.

It does not identify the complete `normalizedPrimeArchMoment` sequence with `M(a)`.  The canonical
prime--Gamma moment germ also contains the continued prime source and its coupling to the Gamma
connection.  Positivity of the Gamma summand cannot be subtracted from, or promoted to positivity
of, that full source.  Consequently this theorem does not discharge
`PrimeArchMomentRepresentation` or prove RH.  The remaining producer problem is an exact
source-faithful decomposition in which the prime residual is itself represented by a positive
measure, or a direct positive measure for the coupled total.

## Anti-theatre verdict

The polygamma--Hurwitz value formula and the classical moment consequences are known mathematics.
The formal result is valuable because it strengthens the general HTGeometry corpus and turns a
physics spectral-zeta relation into reusable, hypothesis-discharging Lean theorems.  It is not
advertised as new scientific knowledge.

## Verification

- [x] exact module cache build passed in one foreground process
- [x] direct touched-file Lean check passed
- [x] no numerical computation used
- [x] selected capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`
- [x] module imported by the HTGeometry umbrella
- [x] no full or self-concurrent Lean build used
