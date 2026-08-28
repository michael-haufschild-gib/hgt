# Physical endpoint valuation-completion cofinal invariance

- **ID:** `physical-endpoint-valuation-completion-cofinal-invariance`
- **Stage:** 3 — formalized in Lean 4
- **Source route:** CCM-FU / PPM / completed physical endpoint response
- **Theorem status:** Lean-proved

## Claim

The valuation-resolved correction from unit--double refinement to the ordinary-prime physical
endpoint is not a cofinal growth obstruction. It enters the completed prime-ratio kernel and its
physical aperture Dirichlet energy by an exact additive decomposition. On every translated support
packet with fixed aperture `A` and fixed logarithmic width `c`, its full signed energy has one
explicit bound independent of translation scale `m`.

Consequently existence of either a cofinal upper bound or a cofinal lower floor for the completed
physical endpoint Dirichlet energy is equivalent to the same property for the uncorrected,
refinement-oriented completed seam energy.

## Gates

- [x] Exact paper statement and proof
- [x] Corpus conjecture search before construction
- [x] Targeted literature novelty audit
- [x] Direct Lean check
- [x] Umbrella wiring
- [x] Targeted module build and built-module axiom audit
- [ ] Publication-ready exposition

## Exact theorem

Write `U(p,q)` for the real-symmetric unit--double completed seam kernel and

```text
C(t)=sum_(r,e) log(r) correction(r,e) exp(-i(e+1)log(r)t),
C_sym(p,q)=Re[(C(log p-log q)+C(log q-log p))/2].
```

If `K_end(p,q)` is the valuation-completed physical endpoint kernel, Lean proves coefficientwise

```text
K_end(p,q)=-U(p,q)+C_sym(p,q).                              (1)
```

Let `d_A,m,k(p,q)` be the true centered physical-aperture Hilbert distance, `w(p)=log(p)/p`, and

```text
D_corr(P)=sum_(p,q in P) w(p)w(q) C_sym(p,q)d(p,q)^2.
```

Then

```text
D_end(P)=D_ref(P)+D_corr(P).                                (2)
```

If

```text
M_corr=sum_(r,e)|log(r) correction(r,e)|,
W(P)=sum_(p in P)log(p)/p,
```

absolute convergence of the valuation correction and aperture geometry give

```text
|C_sym(p,q)| <= M_corr,
d_A,m,k(p,q)^2 <= 4A,
|D_corr(P)| <= 4 A M_corr W(P)^2.                            (3)
```

For the exact support packet

```text
P_m={p : m-A < log p <= m+c},
```

Mertens' first theorem gives, whenever `2<=exp(m-A)`,

```text
W(P_m) <= A+c+C_M,                                          (4)
```

where `C_M=primeLogWindowConst`. Combining `(2)--(4)` gives the scale-free law

```text
|D_end(P_m)-D_ref(P_m)|
  <= 4 A M_corr (A+c+C_M)^2.                                (5)
```

For every `A>0` and `c>=0`, Lean therefore proves both

```text
exists B, forall late m, D_end(P_m)<=B
  <-> exists B, forall late m, D_ref(P_m)<=B,

exists B, forall late m, B<=D_end(P_m)
  <-> exists B, forall late m, B<=D_ref(P_m).                (6)
```

## Proof

The physical endpoint completed kernel is the negative unit--double completed response plus the
phase-preserving valuation correction. Hermitian symmetry of the unit--double response turns its
two-sided real symmetrization into exactly `U(p,q)`, proving `(1)`. Diagonal completion disappears
from every Dirichlet energy because `d(p,p)=0`; summing `(1)` proves `(2)`.

The correction series is absolutely summable over prime-by-valuation clocks. Triangle inequality
therefore bounds its Fourier kernel uniformly by `M_corr`, and real symmetrization preserves that
bound. Every centered clipped carrier has squared norm at most its clipped length, at most `A`;
the Hilbert triangle inequality gives `d^2<=4A`. Termwise absolute values and factorization of the
double endpoint-weight sum prove `(3)`.

The support-packet endpoint mass is exactly the Mertens prime-weight increment between
`floor(exp(m-A))` and `floor(exp(m+c))`. Applying the corpus uniform Mertens error at both endpoints
proves `(4)`. Equation `(5)` follows. Adding or subtracting its constant right side transfers any
uniform upper bound or lower floor in both directions, proving `(6)`.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalEndpointValuationCompletionCofinalInvariance.lean`
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: PASS
- Targeted build: PASS
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Capstones:
  `xiPhysicalEndpointCompletedPrimeRatioRealKernel_eq_refinement_add_correction`,
  `xiPhysicalEndpointCompletedBalancedApertureDirichletEnergy_eq_refinement_add_correction`,
  `abs_physicalEndpointCompleted_sub_refinement_supportPacket_le`,
  `physicalEndpointCompleted_lowerFloor_iff_refinement_lowerFloor`,
  `physicalEndpointCompleted_upperBound_iff_refinement_upperBound`

## No-go closure

Prime powers do not supply the missing cofinal sign or growth estimate. Their unique
phase-preserving correction is trace class globally and, more strongly, changes the exact
fixed-width physical aperture Dirichlet energy by only a translation-uniform constant. Faster
valuation truncation, deeper prime-power cancellation, or a separate positivity argument for the
correction cannot close the route.

The surviving open core is strictly smaller: prove the cofinal upper bound, lower floor, or exact
source comparison for the refinement-oriented completed seam response itself. This card proves
invariance of that burden; it does not prove the burden or RH.

## Novelty audit

Primary literature treats compactly supported Weil tests, finite-place/prime-power contributions,
trace-class positivity, truncated Weil forms, and spectral limits. Searches through 2026-08-27
found no coefficientwise ordinary-prime endpoint/refinement decomposition `(1)--(2)`, no
translation-uniform valuation-completion estimate `(5)`, and no cofinal upper/lower boundedness
equivalence `(6)` for this physical prime-log aperture energy. Candidate-new content is restricted
to this route-specific synthesis.

Primary comparison points:

- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368):
  semilocal Weil trace formulas, finite prime-power support, and the obstruction in Li's proposed
  trace-class positivity argument.
- A. Connes and W. van Suijlekom,
  [*Quadratic Forms, Real Zeros and Echoes of the Spectral Action*](https://arxiv.org/abs/2511.23257):
  lower-bounded finite-interval convolution forms and real-zero conclusions.
- A. Connes, C. Consani, and H. Moscovici,
  [*Zeta Spectral Triples*](https://arxiv.org/abs/2511.22755): finite-prime rank-one perturbations
  and the still-conjectural scaling limit.
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096):
  unconditional finite-interval Weil-form operators and the conjectural large-aperture limit.

## Verification log

- 2026-08-27: mandatory Lean-corpus research completed before conjecturing.
- 2026-08-27: coefficientwise kernel and exact energy decompositions closed in scratch.
- 2026-08-27: uniform finite-packet correction budget and fixed-width Mertens mass bound closed.
- 2026-08-27: cofinal upper-bound and lower-floor invariance closed in Lean.
- 2026-08-27: targeted primary-literature novelty audit completed.
- 2026-08-27: direct check, umbrella wiring, targeted build, and axiom audit passed. Global lint
  reached this module but was blocked by two unrelated, concurrently edited unwired Sieve modules.
