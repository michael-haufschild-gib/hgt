# Positive compact Fredholm realization of the actual theta renewal denominator

- **ID:** theta-renewal-positive-fredholm-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-verified)
- **Count:** Contribution 13, counted once. Verified goal count: 13/100.
- **Source:** Local Lean corpus only; no external novelty claim.

## Exact target

Write nu(t)=thetaRenewalIncrement(t), c=Theta(1),
N(z)=integral_0^infinity exp(-zt) nu(t) dt, D(z)=c-N(z), d=D(0)>0,
and beta=thetaRenewalDrift=integral_0^infinity t nu(t) dt / d.
On H=L2((0,infinity),dt), put g(t)=sqrt(nu(t)) and define the literal kernel

    V(t,a) = 1_(0<a<t) g(t)/g(a),
    K = V + d^(-1) |g><V* g|.

Construct these operators and prove, with all theta source admission discharged:

1. V and K are Hilbert--Schmidt, hence compact. Both preserve the cone of
   almost-everywhere real nonnegative functions.
2. For every complex z and any Hilbert basis b of H,

       det2Op b (z K) = exp(-beta z) D(z)/d.

   This is the existing global entire Hilbert--Carleman determinant.
3. Consequently D(z)=0 iff -1 is an eigenvalue of z K; equivalently, for
   z nonzero, -1/z is an eigenvalue of K. Transfer zero orders to algebraic
   multiplicities using the existing global determinant theorem.
4. Substitute this exact identity into the existing two-ended identity:

       XiC(2z) = d [(1/4-iz) exp(-i beta z) det2Op b (-iz K)
                    +(1/4+iz) exp(i beta z) det2Op b (iz K)].

Count this full actual-source realization once, including its generic
determinant and kernel helpers. Positive means cone preserving; K is not
claimed self-adjoint or positive as a quadratic form. No RH claim, positive
Xi determinant, trace-class claim, or C0 evolution is part of this target.

## Structural purpose

The renewal route has an entire scalar denominator and resonance divisor but
no operator admission in the inspected source family. The target supplies an
explicit compact positive operator directly from the actual theta increment,
without inserting zeros, assuming a spectral realization, or postulating an
unproved source/core condition. It places the full renewal resonance problem
and its two-ended Xi coupling inside the corpus's global Fredholm machinery.
A generic rank-one identity alone, a bound, or a scalar reformulation does not
qualify; the actual kernel admission and entire identity must both be proved.
Final significance review remains mandatory before counting.

## Dependency-closed paper proof [PROVED HERE]

Existing Lean theorems give nu>0, its derivative, all exponential moments,
d>0, beta>0, and the exact two-ended identity. The derivative is

    nu' = 2 pi exp(5t/4) [(5/4) M1(exp t) - pi exp(t) M2(exp t)].

For t>=0, M2>=M1>0, exp(t)>=1, and pi>3 imply nu'+exp(t)nu<=0.
Thus nu(t) exp(exp t) decreases on [0,infinity), giving, for 0<=a<=t,

    nu(t)/nu(a) <= exp(-(exp t-exp a))
                   <= exp(-exp(a)(t-a)).

The second inequality follows from exp(t-a)>=1+t-a. In particular the
square kernel has column integral at most exp(-a), so its double integral
is at most 1. Its unsquared kernel is at most exp(-(t-a)/2) on a<t;
both Schur integrals are at most 2. This constructs the bounded literal
Volterra operator and proves its Hilbert--Schmidt admission. All factors
in its kernel are real nonnegative. All exponential moments put
g_z(t)=g(t)exp(-zt) in H, including g=g_0.

Composition of two strictly causal square-integrable Schur kernels remains
strictly causal. Its square integrability follows from the square-integrable
kernel composition construction. The trace of a product of two such
operators is the double integral of k1(t,a)k2(a,t), which vanishes pointwise.
Induction gives tr(V^n)=0 for every n>=2. The existing local determinant
trace series therefore equals 1 near zero; uniqueness of its entire
continuation gives det2(I+zV)=1 for all z. No local exponential is substituted
for the global determinant.

Direct integration on [0,t] gives

    (I+zV)g_z=g,   <g,g_z>=N(z),   Vg=tg,
    z <V*g,g_z>=N(0)-N(z),   <V*g,g>=integral t nu(t) dt.

These identities hold also at z=0, without division by z. The rank-one
perturbation is Hilbert--Schmidt. Since V* also preserves nonnegativity,
K preserves it. Set A=zV and B=(z/d)|g_z><V*g|. Then

    (I+A)(I+B)=I+zK,
    1+tr(B)=D(z)/d,
    tr(B)+tr(AB)=beta z.

For Hilbert--Schmidt A,B, the regularized determinant multiplication law is

    det2(I+A+B+AB)=det2(I+A)det2(I+B) exp(-tr(AB)).

Here is a dependency-closed proof of the law: compress A and B by the net of
finite-coordinate projections P_s, ordered by inclusion. The finite-dimensional identity
follows from determinant multiplicativity and
tr(A_s+B_s+A_s B_s)=tr(A_s)+tr(B_s)+tr(A_s B_s).
The compressions converge in Hilbert--Schmidt norm. Their products converge
in trace norm, since
||A_s B_s-AB||_1 <= ||A_s-A||_2 ||B_s||_2 + ||A||_2 ||B_s-B||_2.
They therefore also converge in Hilbert--Schmidt norm, and their traces
converge. The existing entire determinant continuity passes the finite
identity to the limit. The same finite-dimensional argument, or the
rank-one power traces and entire uniqueness, gives
det2(I+B)=(1+tr(B))exp(-tr(B)). These two laws give the stated formula.

The exponential and d are nonzero, so the existing global determinant
zero/eigenvector theorem and algebraic-multiplicity theorem give the
spectral assertions. Substitution into the existing two-ended identity
gives the displayed Xi formula, including its signs and normalization.

## Corpus audit

- Three whole-corpus deep searches covered renewal comparison, positive
  boundary feedback, and compact Volterra resolvents. Each returned
  partial=false against an inventory of 73,222 files and 1,083,647 declarations.
  Semantic coverage was unmeasured and compiled snapshots were mostly stale
  or pending; direct source inspection governs applicability. Generated
  oscillatory-Liouville--Green/Laplacian ingredient sets were inapplicable.
- The actual theta renewal family already contains phase factorization,
  positive exit density, the full resonance divisor and reflection-preserving
  positive zero surgery. Those are not recounted here.
- Exhaustive text search of modules using thetaRenewalDenominator found no
  occurrence of Fredholm/det2/operator-admission APIs in that family.
- SquareIntegrableKernelOperator, SchurKernelComposition,
  FredholmDeterminantTracePowers, MertensClockRelativeDeterminant,
  RegularizedDeterminantAlgebraicMultiplicity and
  EntireDet2HilbertSchmidtContinuity supply the generic machinery used above.
- CCMArchimedeanHankelTraceClass has a different weighted interval observer
  and a Hankel factorization, not this theta renewal realization.
- A coefficient-based companion operator was considered but not selected:
  the present literal theta kernel preserves the physical source and has a
  direct closed formula. No companion construction is claimed.

## Formalization plan and checkpoint

1. Prove the intrinsic theta increment ratio estimate and construct the
   square-root mode family and actual causal kernel.
2. Establish strict-causal trace vanishing and global determinant value 1.
3. Prove the generic Hilbert--Schmidt determinant multiplication law and
   rank-one formula using finite compressions and continuity.
4. Prove the actual mode identities, positive perturbation, entire identity,
   multiplicities and two-ended Xi formula.
5. Audit every public theorem's axioms and primary signatures, wire imports,
   run targeted single-process Lean checks, index and authoritative lint;
   reassess significance and only then count once.

2026-10-17: Paper mechanism and exact target recorded before new Lean code.
At this initial checkpoint, no formal result for candidate 13 existed. Count remains 12/100. Frontier map is
read-only and untouched by this agent.

### Formalization checkpoint

The following targeted leaves compile with empty logs, one Lean process at
a time. They are helpers inside candidate 13, not separate counted results:

- `RHTower/ThetaRenewalCausalDecay.lean`: actual derivative loss, increment and
  half-density ratio estimates, all source premises discharged.
- `HTGeometry/CausalExponentialIntegrals.lean`: the two half-line exponential
  masses used by the kernel admission.
- `RHTower/ThetaRenewalCausalKernel.lean`: literal measurable kernel, both
  Schur bounds, squared kernel integral at most 1, actual Hilbert--Schmidt
  and compact operator.
- `HTGeometry/StrictlyCausalFredholm.lean`: strict-causal composition and
  square-integrable powers, zero trace powers, global entire determinant 1.
- `RHTower/ThetaRenewalCausalModes.lean`: every complex tilted mode lies in
  L2; its inner product with the base mode is the actual renewal Laplace
  transform. Base mode is nonnegative.

- `HTGeometry/PositiveSchurKernel.lean`: a nonnegative Schur kernel and its
  adjoint preserve the complex L2 positive cone; nonnegative L2 vectors have
  a nonnegative inner product.
- `RHTower/ThetaRenewalCausalResponse.lean`: every tilted mode solves the exact
  Volterra response equation, including z=0; the adjoint pairings are the
  actual Laplace difference and first moment; the causal determinant is 1.

Written but not yet fully checked: `HTGeometry/HilbertSchmidtProductLimits.lean`,
`HTGeometry/RegularizedDeterminantMultiplication.lean`,
`HTGeometry/RegularizedDeterminantRankOne.lean`, and
`RHTower/ThetaRenewalPositiveFredholm.lean`. The first extends the existing
sequential entire determinant continuity to arbitrary filters via the
Hilbert--Schmidt matrix L2 space, avoiding a countable-basis restriction in
the multiplication law. Trace convergence uses continuity of the Hilbert--Schmidt
inner product, so no trace-norm API is needed. Multiplication, the rank-one
formula and actual K realization remain unverified; spectral multiplicities
remain to be written. No imports wired,
final axiom audit, lint or counting yet. Count remains 12/100.

### Determinant and multiplicity checkpoint

`HilbertSchmidtProductLimits`, `RegularizedDeterminantMultiplication`,
`RegularizedDeterminantRankOne`, and `CoordinateDeterminantMultiplicity` now
compile with empty logs. The multiplication law uses the net over all finite
coordinate sets. The rank-one update requires an exact response vector, not
an inverse at a potentially singular spectral parameter. Coordinate transport
preserves both generalized-eigenspace dimension and finite-dimensionality.

`ThetaRenewalPositiveFredholm` has compiled successfully: actual K is positive,
Hilbert--Schmidt and compact, its entire determinant equals exp(-beta z)D(z)/d
for every z, and its two signed evaluations give the exact Xi identity.
A proof-log cleanup is being checked. `ThetaRenewalFredholmSpectrum` is written
but has not yet been checked. Full axiom/signature audit and integration gates
remain pending. Candidate 13 remains uncounted.

### Full-target check and audit

All thirteen leaves compile with the existing heartbeat limit and one owned
Lean process at a time. `ThetaRenewalFredholmSpectrum` proves the scaled and
unscaled eigenvector equivalences and exact finite-dimensional generalized
eigenspace multiplicity on the original L2 space. No coordinate-space
multiplicity is substituted for the physical operator's multiplicity.

All 103 named public declarations have been axiom-audited from `/tmp`:
only `propext`, `Classical.choice`, and `Quot.sound` occur. Every owned object
is newer than its source; all thirteen imports occur exactly once in their
theorem-area umbrellas. Index regeneration exits 0. Both authoritative lint
and lint with `--check-generated` exit 1 solely for the concurrent foreign
unwired module `GaloisForLFunctions.RHTower.CHMDNativeJordanSamples`, plus
381 existing large-file warnings. No own-module, forbidden-declaration, or
generated-index error is reported. `ThetaRenewalPositiveFredholm` emits one
nonfatal tactic suggestion while exiting 0; other leaf logs are empty.
The final printed-signature audit exits 0: all sixteen primary signatures
and ten definitions were inspected. They assert the actual L2 operator and
global entire determinant, with no hidden RH or source/core premise. All
thirteen source hashes remained unchanged through the integration checks.

### Significance review

The full result removes the source-admission obstacle between the actual
theta renewal route and the compact positive Fredholm class: the kernel,
all complex response vectors, positivity, compactness, global determinant,
Xi coupling, and algebraic multiplicities are proved from the theta source.
The operator is defined before and independently of its resonance zeros.
No RH, zero placement, spectral realization, or unresolved core premise is
assumed. This opens the full compact-operator spectral framework for the
renewal resonances with the actual Xi coupling retained. It is not a bound,
conditional receiver, or scalar RH equivalence.

The generic kernel, continuity, determinant, rank-one, and coordinate
transport lemmas are implementation ingredients of this one result and
receive no separate counts. Internal overlap checks found no prior actual
theta operator realization; no claim of external publication novelty is made.

Final disposition: counted once as contribution 13. Goal remains active at
13/100. `docs/reports/rh-current-frontier-map.md` remained read-only for this
agent throughout.


## Audited source hashes

| Source | SHA-256 |
|---|---|
| `GaloisForLFunctions/HTGeometry/CausalExponentialIntegrals.lean` | `c126810a266ba7f6512b60321f0b9494d46568d2b5a8f78361de3fae5234c923` |
| `GaloisForLFunctions/HTGeometry/CoordinateDeterminantMultiplicity.lean` | `8fe0877358a44b5ac2889aa03de0bb596ead162f518f29edd764b50dbfac6376` |
| `GaloisForLFunctions/HTGeometry/HilbertSchmidtProductLimits.lean` | `8a5beaff09d4162c318df6bf8155fae63e309a524b084bcc225d5c11ba397c9c` |
| `GaloisForLFunctions/HTGeometry/PositiveSchurKernel.lean` | `ce08fc044c6279c7d80196fcc624ecfdae30ece0f2a76fb5f8aad791e9d603f1` |
| `GaloisForLFunctions/HTGeometry/RegularizedDeterminantMultiplication.lean` | `7d68c7d8c8f7f944f8966a8238a9f0ed77f366b7f3387e26e5ba1f4fbbecb25a` |
| `GaloisForLFunctions/HTGeometry/RegularizedDeterminantRankOne.lean` | `f8161c05a21f27126dc3a22fe8de699be99318605b804098a56acc3ad4abf651` |
| `GaloisForLFunctions/HTGeometry/StrictlyCausalFredholm.lean` | `00649325faf78493e5b1dbb92f63523cc47b3b5176964a93f40bd34e64c8e9ad` |
| `GaloisForLFunctions/RHTower/ThetaRenewalCausalDecay.lean` | `c5eccaabd906bb12268a3c979e5c2381eec2e68ddc0d4ab587220748dc09d7df` |
| `GaloisForLFunctions/RHTower/ThetaRenewalCausalKernel.lean` | `73aa77cdfa5842689c9c9df411a69a63d493c60ae74676ba8757c82151ddbb3e` |
| `GaloisForLFunctions/RHTower/ThetaRenewalCausalModes.lean` | `81ab365edc16ba637c89d8d6ee0065908a929b1e227acaaa787dde00baf50a7d` |
| `GaloisForLFunctions/RHTower/ThetaRenewalCausalResponse.lean` | `ea289551830715fac618dd52827b98233d627d9c7ae30517e4498731a191346e` |
| `GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean` | `020cfe5a61bc50234716dbdb41b248cd32eb15bb0c5c4938128e7b11ac338f23` |
| `GaloisForLFunctions/RHTower/ThetaRenewalPositiveFredholm.lean` | `0543a4dc97f1a1a8804e432c817e2811bd8d613ebf2924d80b313a8720d238eb` |

All 52 reviewed contribution-13 temporary files were removed after verification.
