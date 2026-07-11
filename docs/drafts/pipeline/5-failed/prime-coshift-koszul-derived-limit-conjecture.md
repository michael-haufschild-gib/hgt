# Prime co-shift Koszul derived-limit proposal — terminal record

- **ID:** `prime-coshift-koszul-derived-limit-conjecture`
- **Stage:** 5-failed
- **Type:** TERMINAL ROUTE RECORD
- **Scientific status:** `[CLOSED IN THIS FORM]`; replaced by the concrete closed-row coercivity route
- **Source:** `prime-coshift-eigenline-regularized-boundary-complex.md`, the additive heat-aperture
  theorem, and the completed theta/Poisson reflection
- **Statement:** The common prime co-shift eigenline and its additive regularized boundary are valid,
  but an unspecified derived limit of finite Koszul complexes does not define the required defect.
  The route is replaced by a concrete densely defined closed all-prime row operator and an explicit
  off-line coercivity target.

## Terminal correction

The theorem
`acyclic-finite-fibers-derived-limit-zero.md` rules out the earlier raw mechanism whenever the
specialized finite fibers are acyclic: they are zero objects, so their ordinary derived inverse
limit is zero.  The finite co-shift Koszul fibers below are not all acyclic, but merely writing
`R lim` still leaves the transition maps, topology, closed ranges, determinant, and specialization
undefined.  It supplies no canonical completion defect.

The correct analytic replacement is the closed row

```text
R_s x=((V_p^*-p^(-s))x)_p,
```

whose domain, closedness, and kernel are proved in
`prime-coshift-eigenline-regularized-boundary-complex.md`.  The live question is whether a
source-defined additive trace can be closed on its graph domain and satisfy an off-line coercive
estimate.  That replacement is recorded in
[`prime-coshift-additive-trace-coercivity-conjecture.md`](../0-backlog/prime-coshift-additive-trace-coercivity-conjecture.md).

## Why this is a pivot

The retired screen route tried to turn a scalar heat echo into a bounded normal map between two
prime representations.  That implication is exactly RH, and the canonical tangent fails the
required covariance off the line.

This route asks for no sector intertwiner.  Its basic object is instead the constraint complex of
the same arithmetic state.  On `H=l2(N_(>=1))`, let

```text
V_p e_n=e_(pn),
T_(p,s)=V_p^*-p^(-s)I.
```

The operators `T_(p,s)` commute.  Their simultaneous Hilbert kernel is already proved to be

```text
intersection_p ker T_(p,s)=C Psi_s
```

for `Re(s)>1/2`, and to vanish on and left of the critical wall.  The arithmetic vector is therefore
fixed by the complete multiplicative constraint rather than propagated by a flow.

The regularized additive boundary map of this eigenline is source-defined by subtracting the
universal polylogarithm singular branch.  Its value is `zeta(s)`, and its positive quadratic shadow
is the missing heat echo.  Thus the finite reduction

```text
C Psi_s --RegEv_s--> C
```

is acyclic exactly away from the zeta divisor.

## Why the reduced complex is insufficient

`[PROVED]` At a zero the reduced differential is the zero map between two one-dimensional spaces.
It creates one-dimensional kernel and one-dimensional cokernel simultaneously, so its Fredholm
index remains zero.  Finite-dimensional duality also supplies no selector:

- a positive norm makes no nonzero isotropic class possible;
- an indefinite form pairs an off-line zero with its functional-equation mate and permits the
  resulting hyperbolic plane; and
- determinant or Fitting support records the divisor but not the critical line.

The location information, if it exists, must therefore be a closure defect of the unreduced
all-prime complex, not an invariant of its one-dimensional cohomology after the infinite prime
constraints have already been solved.

## Proposed full object

For a finite prime set `P`, form the commuting Koszul complex

```text
K_P(s)=Koszul((T_(p,s))_(p in P); H).
```

Prime inclusion gives a directed system.  The target is a specified closed derived limit

```text
K_infinity(s)=R lim_P K_P(s)
```

together with a closed additive boundary relation `B_s` constructed from the Gaussian aperture,
not from point evaluation and not by declaring its determinant to be zeta.  Its reduction on the
joint eigenline must agree with `RegEv_s`.

The completed theta/Poisson constraint should give a chain-level reflected duality

```text
J_s : K_infinity(s) -> dual(K_infinity(1-conj(s))).     (1)
```

The critical line is the fixed locus of this duality.  The conjectural selector is not the mere
existence of (1), since an indefinite duality accepts off-line pairs.  It is the stronger claim that
a heat-boundary cohomology class produced by the actual source has a positive self-dual defect
pairing.  Such a class cannot be paired with a distinct reflected class and would therefore have to
lie at the fixed locus.

## Exact open core

Construct `K_infinity(s)`, `B_s`, and `J_s` from the pre-divisor Euler--Gamma/theta source and prove:

```text
RegEv_rho(Psi_rho)=0
  =>
there is a nonzero class c_rho in H*(K_infinity(rho),B_rho)
carrying a positive J_rho-self-dual defect pairing.      (2)
```

Then prove the source-independent selector

```text
nonzero positive J_s-self-dual defect class
  =>
s=1-conj(s).                                            (3)
```

Equation (3) is plausible linear algebra once the precise positive defect space exists.  Equation
(2) is the hard construction.  It must be a theorem about the closure/domain anomaly of the full
prime complex; asserting self-duality only after reading `rho` is the retired descent in different
notation.

## Kill tests

The route is false or circular if any of the following occurs:

1. **Finite-prime stabilization:** a fixed finite `P` already carries the claimed selector.  Finite
   prime constraints have excessive kernels and cannot see the Hilbert wall.
2. **Reduced-index substitution:** the construction factors through the two-term eigenline complex.
   Its Fredholm index is identically zero.
3. **Indefinite-only pairing:** the reflected duality merely forms a hyperbolic pair.  This accepts
   every hypothetical off-line zero quartet.
4. **Arbitrary extension:** the domain of the closed boundary relation is chosen to include line
   defects and exclude bulk defects.  The domain must be forced by the Gaussian aperture and prime
   exhaustion.
5. **Divisor insertion:** `zeta`, `xi`, their zeros, or an RH-equivalent square-summability premise
   appears in the definition of the complex or polarization.
6. **Normal-sector fallback:** (2) is proved by manufacturing a bounded normal reflected-sector
   intertwiner.  That is the retired RH-equivalent route.
7. **Exhaustion dependence:** different cofinal prime orders or admissible heat regularizations
   produce inequivalent defect classes.

## Immediate paper program

1. Define the finite Koszul differentials explicitly and classify their homology and transition
   maps before taking a limit.
2. Identify the minimal graph norm in which the regularized additive boundary is closable on the
   algebraic union of finite-prime constraint domains.
3. Derive the reflected chain map from Poisson summation on that graph domain.
4. Compute the signed Green form on the closure defect and test whether its radical quotient is
   positive or merely Krein-hyperbolic.
5. Retire the route immediately if the quotient is hyperbolic at a formal off-line pair or if its
   positivity is equivalent to RH without an independent source estimate.

## Lean surface

The existing tree already supplies multiplicative isometries, Mellin/Fourier transport, the
completed theta seam, signed Green-form algebra, and the no-go for a naive positive reciprocity
quotient.  The first useful formal target is the common prime co-shift eigenline after the paper
interface is fixed.  No full build and no conjectural wrapper are warranted now.

## Gates

- [x] finite reduction and zero-index obstruction proved on paper
- [x] route separated from normal sector intertwiners and ordinary Fredholm index
- [x] exact infinite closure object and falsifiers stated
- [ ] finite Koszul homology and transition maps classified
- [ ] canonical closable additive boundary constructed
- [ ] theta reflection lifted to the closed complex
- [ ] positive self-dual closure defect proved at every zero
- [ ] self-dual defect selector proved and composed to RH
- [ ] unconditional Lean formalization
