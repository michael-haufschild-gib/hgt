# Mass-shifted hard-edge root-division spectral classification

- **ID:** `mass-shifted-hard-edge-root-division-spectral-classification`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / route classification
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 and
  `mass-shifted-hard-edge-hyperbolic-weil-boundary`
- **Statement:** Hard-edge root divisions are pairwise orthogonal spectral descendants of one
  null state; they detect multiplicity but cannot exclude a simple ground state. The remaining
  nonredundant datum is cross-aperture/current-admission transport.

## Goal

Determine whether the simultaneous Cauchy equations at all real roots of the hard-edge
Laguerre--Polya state can annihilate that state without reintroducing RH-equivalent global Weil
positivity.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure algebra and hostile alternatives isolated
- [ ] 1 -> 2 fully-proven: finish source-specific bounded-scale transport theorem and audit all
  analytic dependencies
- [ ] 2 -> 3 formalized: root-division spectral theorem is Lean-proved; source-specific bounded
  transport still awaits the hard-edge degree theorem's literal analytic formalization
- [ ] 3 -> 4 publication-ready

## Exact algebraic survivor `[PROVED HERE]`

Let `B` be a bilinear form and let `T` be `B`-self-adjoint. Let `f` lie in the left radical of
`B`. Suppose distinct scalars `r != s` and vectors `q_r,q_s` satisfy

```text
(T-r) q_r = f,        (T-s) q_s = f.
```

Then

```text
B(q_r,q_s)=0.
```

Indeed, radicality and self-adjointness give

```text
0 = B((T-r)q_r,q_s) = B(q_r,(T-r)q_s),
0 = B(q_r,(T-s)q_s),
```

and subtraction gives `(s-r) B(q_r,q_s)=0`.

If instead `(T-r)q=h` and `(T-r)h=f`, then

```text
B(h,h)=B((T-r)h,q)=B(f,q)=0.
```

For hard-edge multiplication `T:u |-> u`, `f=F`, and `q_r=F/(u-r)`, this proves:

1. deletions at distinct real zeros are pairwise orthogonal for the restricted Weil form;
2. a multiple zero produces another null vector after one deletion;
3. for a positive-semidefinite form with one-dimensional kernel, every zero is simple and every
   root-deletion energy is strictly positive.

Thus the Cauchy equations are not independent arithmetic constraints. They are forced spectral
descendants of the complete null row. They classify kernel multiplicity but do not kill a simple
isolated ground state.

## Conjecture / proof-or-fail loop

1. **Cauchy zeros accumulating at infinity force the transform to vanish. FAIL.** The roots lie
   on the support of the positive tail. The Cauchy transform has no analytic continuation across
   that support, and the boundary state has only logarithmic weighted `L2`, not all finite
   moments. Neither the identity theorem at infinity nor a moment expansion applies.
2. **Laguerre--Polya hyperbolicity is exceptional enough to exclude a restricted-Weil ground
   state. FAIL.** Real-zero Fourier transforms occur for simple isolated even ground states of a
   broad class of finite-interval convolution forms. Hyperbolicity is compatible with, rather
   than contradictory to, ground-edge geometry.
3. **One root barycenter plus the positive Gamma tail orients the state. FAIL.** The compact
   finite-prime well remains signed and balances any selected barycenter. Simultaneous root
   divisions add orthogonal descendants, not a new source sign.
4. **Differentiate the static equation under dilation to retain Gamma confinement. FAIL.** The
   virial derivative turns each nonzero prime mode `c cos(lambda x)` into a term containing
   `c lambda x sin(lambda x)`, unbounded in both signs. Static dilation destroys the
   compact-negative/positive-tail geometry.
5. **Survivor: root divisions are a spectral basis diagnostic. PROVED.** Any successful closure
   must use motion of the source or aperture, not another static division.

## Bounded-scale terminal-transport survivor `[PAPER DERIVATION]`

Assume the already paper-proved parabolic degree lower bound

```text
D(y) > c * sqrt(y)
```

for all large `y`, where `D(y)` is the least non-positive shifted-Xi Hankel size. For every degree
`N`, every mass

```text
y > (N/c)^2
```

has `D(y)>N`, hence every leading block through size `N` is positive definite. Therefore a
first-contact schedule `N_j/a_j -> tau` reaches a complete terminal positive chamber by a mass
whose square-root ratio to `a_j` is bounded by `tau/c+o(1)`. The frozen/current obstruction does
not require transport to an unbounded relative mass. It lives on one compact dilation interval.

This is the first bridge between hard-edge compactification and the current-admission Riccati
law. It removes unbounded horizontal transport from the open core. What remains is adjacent-current
compatibility on a bounded scale interval; no static root equation sees it.

## No-go closure

- **Exact killing theorem/mechanism:** root-division equations follow from radicality and
  self-adjoint multiplication; distinct deletions are orthogonal, and multiple roots enlarge the
  kernel.
- **Strongest positive survivor:** bounded-scale terminal transport plus root-deletion spectral
  classification.
- **New insight:** hard-edge boundary is a legitimate ground-edge spectral state. Arithmetic must
  act through aperture/current history before reflection aggregation.
- **Status:** algebraic survivor dependency-closed and Lean-proved; bounded-scale bridge depends
  on the paper-proved hard-edge degree theorem whose literal analytic Lean formalization remains
  open.

## Literature collision audit

- Connes--van Suijlekom (2025), *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*,
  proves real zeros for Fourier transforms of simple isolated even convolution ground states. It
  confirms the hostile ground-state model but does not state the root-deletion orthogonality or
  the shifted-Xi bounded-scale transport bridge.
- Suzuki (2026), *Weil's quadratic form via the screw function*, supplies the restricted Weil
  operator setting but no hard-edge reciprocal-Hankel compactification or root-deletion
  classification.
- Kulikov (2025), *Bounded symbols of Toeplitz operators on Paley-Wiener spaces and a weak
  factorization theorem*, shows the ambient product space is large; it does not make the principal
  ideal generated by one null state cyclic.

## Log

- 2026-08-11 — static Cauchy annihilation and virial routes failed under hostile audit.
- 2026-08-11 — root-deletion orthogonality/multiplicity law proved; bounded-scale terminal bridge
  isolated.
- 2026-08-11 — algebraic and literal polynomial-moment specializations formalized and audited in
  `HTGeometry.NullRootDivisionSpectralLaw`.
