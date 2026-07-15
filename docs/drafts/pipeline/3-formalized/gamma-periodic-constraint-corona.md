# The Gamma shift source realizes a nonzero infinite conormal with arbitrary finite jets

- **ID:** `gamma-periodic-constraint-corona`
- **Stage:** 3-formalized
- **Type:** CONCRETE HT SOURCE REALIZATION / ANALYTIC CORONA MODEL
- **Scientific status:** `[CORE THEOREM LEAN-FORMALIZED] [RANK-ONE CLOCK CURVATURE LEAN-FORMALIZED] [FORMAL-GLOBAL UNIT DEFECT LEAN-FORMALIZED] [SELF-DUAL SYMBOL PROVED] [LAGRANGIAN EXTENSION OPEN] [NOVELTY PROVISIONAL]`
- **Parents:**
  - `../2-fully-proven/needs-audit/finite-observable-conormal-corona.md`
  - `../2-fully-proven/needs-audit/hypertranscendental-kaehler-tate-clock-linearization.md`
- **Statement:** The affine digamma shift equation has a homogeneous periodic source tangent which
  realizes every finite jet packet but is annihilated by one nonzero infinite-support Taylor
  conormal. It is therefore a concrete HT source realization of the finite-observable conormal
  corona.

## Source equation

The digamma function satisfies, away from its pole orbit,

```text
psi(z+1)-psi(z)=1/z.                                       (1)
```

The solution set of `(1)` is affine: the difference of any two solutions is `1`-periodic, and
adding any `1`-periodic meromorphic function to a solution gives another solution. The actual
digamma source is selected only after imposing normalization/asymptotic data. Digamma is
hypertranscendental, so this is an actual constrained HT source rather than a formal toy carrier.

## Periodic finite-jet controllability `[PROVED]`

Put

```text
beta_m=2 pi i m,
e_m(z)=exp(beta_m z),       m=0,1,2,... .                  (2)
```

Every `e_m` is entire and `1`-periodic. For each `k>=1`, the first `k` jets at zero satisfy

```text
e_m^(n)(0)=beta_m^n,       0<=m,n<k.                      (3)
```

The matrix `(beta_m^n)_(n,m<k)` is Vandermonde on distinct frequencies. Hence for every target
packet `(c_0,...,c_(k-1))` there is a unique Fourier polynomial

```text
h(z)=sum_(m<k) a_m e_m(z)                                 (4)
```

with `h^(n)(0)=c_n` for every `n<k`. Therefore the homogeneous periodic tangent of `(1)` is
surjective onto every finite jet window.

## Infinite Taylor conormal `[PROVED]`

For every entire `1`-periodic `h`, Taylor expansion from `0` to `1` gives

```text
0=h(1)-h(0)=sum_(n>=1) h^(n)(0)/n!.                       (5)
```

Thus the coefficient sequence

```text
nu=(1,1/2!,1/3!,...)                                      (6)
```

is a nonzero infinite-support conormal to the periodic jet tangent, while the Vandermonde theorem
shows that no finite truncation of `nu` is a conormal. Equations `(3)`--`(6)` give the exact
combination required by the abstract corona theorem:

```text
arbitrary finite clock capacity + one genuine constraint at infinity.  (7)
```

For each Fourier mode, `(5)` reduces to

```text
sum_(n>=1) beta_m^n/n! = exp(beta_m)-1 = 0,                (8)
```

so the conormal is source-derived from translation by one and not chosen from a degeneracy set.

## Source rigging

Let `Phi` be a locally convex space of entire functions containing the Fourier polynomials, with
compact-open topology, and map `h` to its Taylor jet at zero. Evaluation difference

```text
h |-> h(1)-h(0)                                            (9)
```

is continuous on `Phi` and pulls back to `(6)`. Relative to the product topology on raw jet
sequences, `(6)` is not a finite-support covector. Relative to the analytic test-space topology,
it is continuous. The Gamma/digamma shift source therefore constructs the topology enlargement
and the nonzero corona class demanded by the abstract theory.

The affine solution space of `(1)` supplies the calibration torsor. The periodic homogeneous
space supplies its tangent. Asymptotic normalization selects the actual digamma section. This is
the first concrete realization of all three pieces from one HT source.

## Formal/global unit defect `[PROVED AND LEAN-FORMALIZED]`

The shift operator factors as

```text
exp(D)-1=D U(D),
U_hat(D)=1+D/2!+D^2/3!+... .                              (10)
```

The formal series `U_hat` is a unit because its constant coefficient is one. It has a canonical
two-sided formal inverse, so every finite nilpotent clock truncation erases this factor.

The global analytic symbol

```text
U(lambda)=(exp(lambda)-1)/lambda                          (11)
```

is not a unit in the periodic source realization:

```text
U(2 pi i m)=0,             m != 0.                        (12)
```

Thus the same factor is formally invertible but globally singular. Its source inverse is
meromorphic with poles on the periodic-frequency lattice. Reflection is exact:

```text
U(-lambda)=exp(-lambda)U(lambda).                          (13)
```

The multiplier is nowhere zero, so the global nonunit divisor is self-dual. This is the concrete
mechanism joining the five proposed obstruction languages: kernel/cokernel, inverse continuation,
phase/positivity, winding, and closed inverse extensions are properties of one failed source unit.

## Clock-descent and topology consequence

Let `S h=h(.+1)-h` and let `q_k` record the first `k` derivatives at zero. The Fourier
interpolation theorem makes `q_k|ker(S)` surjective. Therefore the general descent-anomaly theorem
implies:

```text
q_k S=T_k q_k  implies  T_k=0                            (14)
```

for every proposed finite shadow `T_k`. More exactly, the full range of `T_k` is the anomaly range
of `T_k q_k-q_k S` on actual periodic solutions.

The compatible infinite jet set of periodic Fourier polynomials is dense in the raw product jet
topology because it realizes every finite initial packet. Hence the nonzero conormal `(6)` cannot
be continuous for that product topology, while it is continuous in the analytic source topology
through `h |-> h(1)-h(0)`. Gamma therefore exhibits all three forced layers:

```text
finite algebraic freedom
  -> dense product-clock tangent and no Hausdorff product constraint
  -> source topology separates one infinite conormal and global unit defect.  (15)
```

The abstract anomaly, product-density, and Hausdorff no-go theorems are Lean-formalized in
`ClockDescentAnomaly.lean`. The explicit Gamma Fourier and conormal inputs are Lean-formalized in
this module. Packaging their function-space composition as one specialized Lean declaration is
still open; equation `(14)` is a paper-level composition of the two verified interfaces.

## Scientific boundary

The following ingredients are classical and are `[BRIDGE]`:

- the Gamma and digamma shift equations;
- periodic ambiguity of solutions to a first-order additive difference equation;
- Fourier exponentials and Vandermonde jet interpolation;
- Taylor expansion and the compact-open topology on entire functions.

The candidate-new result is the identification of this package as a realization of the forced HT
conormal corona: finite differential-algebraic freedom and a nonzero analytic constraint coexist
because the constraint covector has infinite clock support and is continuous only in the
source-selected analytic rigging.

Targeted searches found work on periodic entire-function interpolation and on jet/Borel maps, but
no exact Gamma/digamma interpretation through a finite-observable conormal corona. This is a
provisional absence claim, not a priority claim.

## Relation to the unified-obstruction conjecture `[CONJECTURE]`

The shift equation constructs an affine corona object but not yet a self-dual one. The Gamma
reflection formula should supply the opposite translation direction and an involutive pairing of
the shift conormal with its reflected conormal. The next exact target is to determine whether that
pair is Lagrangian in the affine rigged Tate clock and whether its determinant section is the
source normalization rather than a restatement of Gamma.

This is a general HT prototype. It is not an RH argument.

## Lean formalization

`GammaPeriodicConstraintCorona.lean` formalizes:

1. `gammaPeriodicFrequency`, `gammaPeriodicMode`, and `gammaPeriodicMode_periodic`;
2. `iteratedDeriv_gammaPeriodicMode_zero`, the exact Fourier-mode jet law;
3. `existsUnique_gammaPeriodicFourierJet`, the Vandermonde finite-window isomorphism;
4. `existsUnique_gammaPeriodicFourierPolynomial_jet`, realization by actual entire period-one
   functions;
5. `gammaPeriodicMode_taylorConormal_hasSum`, the infinite factorial-tail identity `(8)`;
6. `gammaPeriodicFourier_taylorConormal_hasSum`, the common conormal for every finite Fourier
   packet;
7. `gammaClockCurvature_apply` and `gammaClockCurvature_eq_outerProduct`, the exact factorial-tail
   boundary formula;
8. `range_gammaClockCurvature` and `finrank_range_gammaClockCurvature`, the exact boundary line and
   rank-one theorem at every positive resolution;
9. `gammaClockTranslation_extendZero`, exact compatibility with forward Ind-clock assembly;
10. `gammaShiftCofactorFormal_mul_inverse` and
   `gammaShiftCofactorFormal_inverse_mul`, formal invertibility in `(10)`;
11. `gammaShiftCofactorSymbol_periodicFrequency`, the global nonunit lattice `(12)`;
12. `gammaShiftCofactorSymbol_neg`, the self-dual reflection law `(13)`.

The general formal consequences `(14)`--`(15)` are supplied by
`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` as described above.

The module reuses the cached `HurwitzExp.iteratedDeriv_expLin` and
`RHTower.existsUnique_weightedFiniteMoments`. Since its `.olean` was missing, verification used
exactly one targeted build followed by one direct source check:

```text
lake build +GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona
lake env lean GaloisForLFunctions/HTGeometry/GammaPeriodicConstraintCorona.lean
```

No full build or concurrent Lean invocation was run by this task.

## Gates

- [x] actual HT source equation identified
- [x] affine periodic homogeneous tangent identified
- [x] arbitrary finite-jet controllability proved on paper
- [x] infinite-support Taylor conormal proved on paper
- [x] source topology making the conormal continuous identified
- [x] core theorem formalized in Lean
- [x] finite unit-translation shadows and exact rank-one curvature formalized in Lean
- [x] forward Ind-clock compatibility of the same shadows formalized in Lean
- [x] general clock-descent and product-topology no-gos formalized in Lean
- [ ] explicit Gamma function-space anomaly specialization packaged in Lean
- [ ] Gamma reflection paired with the shift conormal
- [ ] self-dual Lagrangian relation constructed
- [ ] independent novelty/significance audit
