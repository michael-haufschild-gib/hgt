# Theta-cusp Ward--Laplace half-density observation budget

- **ID:** `theta-cusp-ward-laplace-half-density-observation-budget`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); exact source-value law and existing-moment discharge
- **Register:** `[BRIDGE] [CORPUS-USEFUL] [NOT A NOVELTY CLAIM]`
- **Formal files:**
  `formal/GaloisForLFunctions/HTGeometry/ObservationFidelity.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ObservationMomentBudget.lean`, and
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaWardLaplaceHalfDensity.lean`
- **Statement:** The two half-density exponential observations of every positive theta-cusp atom
  have an exact closed sum and difference.  A general HTGeometry fidelity theorem identifies the
  unweighted observation as their geometric mean and turns the nonzero difference into a strict
  square deficit.  The completed source has total half-density budget `1/2`, so removing the first
  atom leaves an exact closed higher-tail budget.  These values produce direct existing-moment
  bounds.

## Exact value relations

For the positive half-density

```text
b_n(x) = exp(x/2) (n exp x)^2 exp(-pi (n exp x)^2)
```

and source atom `f_n(x) = thetaCuspSourceTerm x n`, define

```text
B_n(z) = integral_(0,infinity) exp(z x) b_n(x) dx,
A_n(z) = integral_(0,infinity) exp(z x) f_n(x) dx.
```

The source Ward identity and the Gibbs score are

```text
f_n = -2 pi (b_n' + b_n/2),
b_n' = (5/2 - 2 pi n^2 exp(2x)) b_n.
```

Lean proves integrability for every real `z < 1`, the boundary integration-by-parts law

```text
integral exp(zx) b_n'(x) dx = -b_n(0) - z B_n(z),
```

and the Ward--Laplace relations

```text
A_n(z) = 2 pi (b_n(0) + (z - 1/2) B_n(z)),
2 pi n^2 B_n(z+2) = b_n(0) + (z + 5/2) B_n(z).
```

At the half-density values the shift coefficient vanishes:

```text
B_n(-1/2) = exp(-pi n^2)/(2 pi),
A_n( 1/2) = 2 pi n^2 exp(-pi n^2),
A_n(-1/2) = (2 pi n^2 - 1) exp(-pi n^2).
```

Therefore

```text
A_n(1/2) + A_n(-1/2)
  = 2 integral_(0,infinity) cosh(x/2) f_n(x) dx
  = (4 pi n^2 - 1) exp(-pi n^2).                     (1)
```

The antisymmetric channel is equally exact:

```text
A_n(1/2) - A_n(-1/2)
  = 2 integral_(0,infinity) sinh(x/2) f_n(x) dx
  = exp(-pi n^2).                                     (1a)
```

HTGeometry now proves the reusable opposite-channel fidelity law for every measurable
nonnegative density `rho` and observation coordinate `phi`:

```text
(integral rho)^2
  <= (integral exp(phi) rho) (integral exp(-phi) rho). (1b)
```

Taking `rho=f_n` and `phi=x/2`, and polarizing the exact sum and difference, gives

```text
thetaCuspAtomRawEvenMoment(0,n)^2 + exp(-pi n^2)^2
  <= ((4 pi n^2 - 1) exp(-pi n^2))^2.                 (1c)
```

No numerical enclosure occurs.

## Direct corpus application

The existing zeroth raw atom moment is

```text
thetaCuspAtomRawEvenMoment 0 n = 2 integral_(0,infinity) f_n(x) dx.
```

On the positive half-line, `f_n >= 0` and `cosh(x/2) >= 1`.  Equation `(1)` first closes the
previously free moment by the weak bound

```text
thetaCuspAtomRawEvenMoment 0 n
  <= (4 pi n^2 - 1) exp(-pi n^2).                     (2)
```

The positive orientation term in `(1c)` strengthens `(2)` to the strict theorem

```text
thetaCuspAtomRawEvenMoment 0 n
  < (4 pi n^2 - 1) exp(-pi n^2).                      (2a)
```

The first-atom specialization is

```text
thetaCuspAtomRawEvenMoment 0 1 < (4 pi - 1) exp(-pi).
```

Using the existing Liouville--Ward identity for this same raw moment, Lean consumes `(2a)` as the
strict symbolic lower bound

```text
exp(-pi n^2) < 2 pi thetaCuspLiouvilleGibbsMoment(0,n). (2b)
```

The stronger two-moment consumer uses the positive Taylor truncation

```text
1 + x^2/8 <= cosh(x/2)
```

and proves exactly

```text
thetaCuspAtomRawEvenMoment 0 1
  + thetaCuspAtomRawEvenMoment 1 1 / 8
  <= (4 pi - 1) exp(-pi).                              (3)
```

The left side of `(3)` is the `W = a_0 + a_1/8` denominator in the existing reflected
likelihood-budget transfer.  This is a direct consumer theorem, not a restatement of the integral
identity.

## Antisymmetric odd-moment closure

The orientation channel gives more than the exact difference `(1a)`.  For any nonnegative
observation coordinate `X` and density `rho`, HTGeometry proves the adjacent moment inequality

```text
M_2^2 <= M_1 M_3,
M_k = integral X^k rho.                                  (3a)
```

It also proves the closed algebraic implication

```text
M_1 + M_3/24 <= S  ->  M_2^2 <= 6 S^2.                  (3b)
```

On the positive half-line,

```text
x + x^3/24 <= 2 sinh(x/2).
```

Combining this pointwise inequality with `(1a)` yields the source-specific budget

```text
integral x f_n(x) dx + (integral x^3 f_n(x) dx)/24
  <= exp(-pi n^2).
```

Equations `(3a)`--`(3b)` then give

```text
thetaCuspAtomRawEvenMoment(1,n)^2
  <= 24 exp(-pi n^2)^2,

thetaCuspAtomRawEvenMoment(1,n)
  <= 5 exp(-pi n^2).                                    (3c)
```

For the first atom this reaches the existing Ward/Liouville coordinate directly:

```text
(2 pi thetaCuspFirstAtomWardMoment(1))^2 <= 24 exp(-pi)^2,
2 pi thetaCuspFirstAtomWardMoment(1) <= 5 exp(-pi).      (3d)
```

The live relaxed fourth-moment certificate needs a lower bound involving this coordinate, so
`(3d)` does not prove it.  The positive no-go residue is the exact necessary feasibility cap:

```text
16 ((3005/2997) a_0) ((3005/2997) a_2) <= 45 a_1^2
  ->
16 ((3005/2997) a_0) ((3005/2997) a_2) <= 1080 exp(-pi)^2.
```

Thus the external fluctuation relation now constrains a theorem hypothesis already present in the
RH corpus; it is not an unused probabilistic analogy.

## Fourth-order half-density remainder and live hypothesis discharge

Keeping one more positive term in the same symmetric clock observation gives the reusable
HTGeometry inequality

```text
1 + x^2/8 + x^4/384 <= cosh(x/2).                         (3e)
```

For the first theta atom, write `a_j = thetaCuspAtomRawEvenMoment(j,1)`.  Combining `(3e)` with
the exact endpoint value `(1)` proves

```text
a_0 + a_1/8 + a_2/384 <= (4 pi - 1) exp(-pi),             (3f)

a_2 <= 384 ((4 pi - 1) exp(-pi) - a_0 - a_1/8).           (3g)
```

Equation `(3g)` eliminates the unknown fourth raw moment from a sufficient condition for the
live relaxed fourth-moment concentration box.  In exact Lean form, if

```text
6144 (3005/2997)^2 a_0
  ((4 pi - 1) exp(-pi) - a_0 - a_1/8) <= 45 a_1^2,         (3h)
```

then

```text
16 m_0 m_2 <= 45 m_1^2,                                   (3i)
```

where `m_j = thetaCuspRawEvenMoment j` is the completed source moment.  The proof uses the
already-formalized first-atom domination factor `m_j <= (3005/2997) a_j` and the lower inclusion
`a_1 <= m_1`.

The direct prime-source consumer now takes only the existing upper adjacent-ratio condition and
the endpoint remainder `(3h)` and concludes nonnegativity of every linear
`primeArchSourceTraceHankel` test.  Thus the former `hrelaxed` argument is discharged at the
consumer interface.  Condition `(3h)` remains open and is stronger than the original condition;
the gain is that it contains no fourth moment and is tied to an exact source value rather than a
free moment box.

## Completed source and higher-tail subtraction

The formal Fourier--Laplace strip identity and the endpoint theorem give

```text
integral_R exp(x/2) thetaCuspFullSource(x) dx = XiC(I/2) = 1/2.
```

The full source is even.  Splitting the real line at zero therefore proves the exact observation
budget

```text
2 integral_(0,infinity) cosh(x/2) thetaCuspFullSource(x) dx = 1/2.   (4)
```

Define the closed higher-tail constant

```text
H = 1/2 - (4 pi - 1) exp(-pi).                              (5)
```

Subtracting the exact first-atom identity `(1)` from `(4)` gives, with
`h(x)=thetaCuspFullSource(x)-thetaCuspSourceTerm(x,1)`,

```text
2 integral_(0,infinity) cosh(x/2) h(x) dx = H.               (6)
```

Lean proves `h>=0` on the positive half-line and hence proves `0<=H` without evaluating the
constant.  If `r_j` denotes the existing higher-atom raw even moment, the same positive Taylor
truncation gives

```text
r_0 + r_1/8 <= H.                                            (7)
```

Combining `(3)` and `(7)` with the existing first/higher moment decomposition gives the direct
completed-source consumers

```text
m_0 + m_1/8 <= 1/2,
m_0 <= a_0 + H.                                              (8)
```

Thus the full and higher observation budgets are no longer paper-only constants or free tail
hypotheses.

## Clock interpretation

The source is globally static.  Its clock structure is read by the observation family
`x |-> exp(zx)` rather than propagated by a Hamiltonian flow.  The endpoint value `b_n(0)` is an
anomalous boundary charge.  Reading the constraint at the two half-density characters produces
the closed nonlocal budget `(1)`.

This is the useful content of the motif “hypertranscendence is about the observability structure
of a clock, not temporal evolution”: a distinguished observation family can close values even
when no finite generative flow is available.

## Physics provenance

- D. Berenstein and G. Hulsey, *Anomalous Bootstrap on the Half Line*, arXiv:2206.01765.  Correct
  half-line moment recursions acquire endpoint/contact anomalies; the algebraic bootstrap does not
  require explicit dynamics.
- C. V. Sukumar, *Generalised Virial Theorems in Classical and Quantum Physics*,
  arXiv:1410.5592.  Static generalized virial identities give exact relations among quantum
  matrix elements.
- D. N. Page and W. K. Wootters, *Evolution without evolution: dynamics described by stationary
  observables*, Phys. Rev. D 27 (1983), 2885--2892.  Observable clock dependence is encoded by
  correlations in a stationary constrained state.
- K. M. R. Audenaert et al., *Discriminating States: The Quantum Chernoff Bound*,
  arXiv:quant-ph/0610027.  The overlap/fidelity of two observation channels controls their
  distinguishability.
- M. P. L. Salazar, *Improving the Cramér--Rao bound with the detailed fluctuation theorem*,
  arXiv:2308.08570, and M. Rao--M. Esposito, *Detailed Fluctuation Theorems: A Unifying
  Perspective*, arXiv:1807.09242.  Forward/reversed observations are paired by an exponential
  likelihood ratio.  Here that pairing is static and source-exact rather than stochastic-time
  evolution.

The literature supplies the boundary-Ward, stationary-observable, and fidelity interfaces.  The
exact theta-cusp orientation deficit and the raw/Liouville-moment consumers are source-specific
Lean theorems.

## Genomics, genetics, ML, and AI transfer boundary

Epigenetic clocks make the same conceptual separation between an observed clock coordinate and a
mechanism that generates biological time: Horvath's DNA-methylation clock reads age from a finite
panel of CpG observations, while methylation-dynamics models separately posit a continuous-time
Markov evolution.  Tilted empirical-risk minimization and the quantum Esscher transform likewise
use exponential tilts as observation/reweighting channels.  These sources support the general
HTGeometry abstraction `(1b)`.  Thermodynamic analyses of biochemical clocks additionally bound
the number of coherent cycles by entropy dissipated per cycle.  That is a dynamical parent result,
whereas `(3a)`--`(3d)` are static source-observation consequences and require no entropy-production
object.

Primary comparison sources are S. Horvath, *DNA methylation age of human tissues and cell types*,
Genome Biology 14:R115 (2013); J. A. Capra--D. Kostka, *Modeling DNA methylation dynamics with
approaches from phylogenetics*, arXiv:1404.3223; T. Li et al., *Tilted Empirical Risk
Minimization*, arXiv:2007.01162; and Y. Qiu--K. Koor--P. Rebentrost, *The Quantum Esscher
Transform*, arXiv:2401.07561.
For biochemical clock precision, R. Marsland III--W. Cui--J. M. Horowitz, *The Thermodynamic
Uncertainty Relation in Biochemical Oscillations*, arXiv:1901.00548, proves the universal parent
bound `N <= DeltaS/2` for the number of coherent oscillations.

They do not supply the source-specific endpoint values in `(1)` or `(1a)`.  Therefore no genomic,
genetic, ML, or AI paper directly discharges another theta-cusp certificate field.  The significant
positive residue is `HTGeometry.sq_integral_le_exponential_tilt_product`: any future nonnegative
genomic likelihood, genetic population density, or ML loss distribution already represented in
the corpus can use the theorem without rebuilding the square-root/Cauchy argument.  The present
corpus has no such domain-specific object, so adding a vocabulary-only wrapper would have no
mathematical value.

The enlarged search also includes algebraic identifiability of molecular clocks and gauge
redundancy in neural ODEs.  Coons--Hollering, *Identifiability of the Rooted Tree Parameter under
the Cavender--Farris--Neyman Model with a Molecular Clock* (arXiv:2303.12058), show that adding the
molecular-clock invariant can make the rooted tree generically identifiable even though the
underlying time-reversible model alone sees only an unrooted tree.  Hashimoto--Hirono--Sannai,
*Unification of Symmetries Inside Neural Networks: Transformer, Feedforward and Neural ODE*
(arXiv:2402.02362), formulate parameter redundancies as gauge symmetries while treating model
functions as observables.  These support the constraint/observable-quotient search criterion, but
neither supplies a theta-source value or sign.  Their positive corpus consequence is already
captured by the finite-circuit source-extraction and observable-gauge theorems; duplicating those
results under genomic or AI names would be wrapper bloat.

## RH impact

Equation `(2a)` removes the equality boundary from one independent first-atom moment box, and
`(2b)` reaches the existing zeroth Liouville--Gibbs certificate variable,
while `(3)` directly controls the two-moment partial budget used by the reflected likelihood
transfer.  Equations `(7)`--`(8)` additionally discharge the previously free higher-tail
zeroth-moment allowance and cap the full two-moment block by the exact source value `1/2`.
Equations `(3c)`--`(3d)` now cap the first nonconstant raw/Ward moment and turn the live relaxed
fourth-moment assumption into an explicit necessary half-density inequality.  Equations
`(3f)`--`(3h)` additionally replace that fourth-moment hypothesis in the direct linear-Hankel
consumer by a lower-order endpoint remainder involving only `a_0`, `a_1`, and the exact
half-density value.
It does not prove the remaining quadratic Stein--Robertson energy inequality and does not orient
an off-line zero.  Its positive effect is to replace a generic tail or free-moment allowance by an
exact source-defined reflected observation budget.

The strict symbolic lower bound `(2b)` does not by itself prove the decimal rational enclosure for
that moment: converting it into the current rational field still needs independent exact bounds on
`pi` and `exp(-pi)` strong enough for the stated decimal.  The next valid consumer is a certificate
that is monotone in the zeroth raw/Liouville moment or in the two half-density tilts.  Another
generic finite-channel or curvature wrapper would not use the new information.

## Formalized declarations

- `HTGeometry.sq_integral_le_exponential_tilt_product`
- `HTGeometry.sq_second_observation_le_first_mul_third`
- `HTGeometry.sq_second_observation_le_six_budget_sq`
- `HTGeometry.self_add_cube_div_six_le_sinh`
- `HTGeometry.self_add_cube_div_twenty_four_le_two_sinh_half`
- `HTGeometry.one_add_sq_div_two_add_fourth_div_twenty_four_le_cosh`
- `HTGeometry.one_add_sq_div_eight_add_fourth_div_384_le_cosh_half`
- `integrableOn_exp_mul_thetaCuspPolynomialAtom_of_lt_one`
- `exp_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_lt_one`
- `integral_exp_mul_deriv_thetaCuspWardGibbsAtom_eq`
- `thetaCuspSourceExponentialTilt_eq_wardBoundary`
- `thetaCuspWardGibbsExponentialTilt_shift`
- `thetaCuspWardGibbsExponentialTilt_neg_half`
- `thetaCuspSourceExponentialTilt_half`
- `thetaCuspSourceExponentialTilt_neg_half`
- `thetaCuspSourceExponentialTilt_half_budget`
- `thetaCuspSourceExponentialTilt_half_sub_neg_half`
- `two_mul_integral_sinh_half_mul_thetaCuspSourceTerm_eq_orientation`
- `integrableOn_first_mul_thetaCuspSourceTerm`
- `integrableOn_third_mul_thetaCuspSourceTerm`
- `integrableOn_sinh_half_mul_thetaCuspSourceTerm`
- `thetaCuspSourceOddMomentPair_le_orientation`
- `thetaCuspSourceSecondMoment_sq_le_first_mul_third`
- `thetaCuspSourceSecondMoment_sq_le_six_orientation_sq`
- `thetaCuspAtomRawEvenMoment_one_sq_le_twenty_four_orientation_sq`
- `thetaCuspAtomRawEvenMoment_one_le_five_mul_orientation`
- `two_pi_mul_thetaCuspFirstAtomWardMoment_one_sq_le_orientation_sq`
- `two_pi_mul_thetaCuspFirstAtomWardMoment_one_le_five_exp_neg_pi`
- `relaxedFourthMoment_firstAtom_hypothesis_implies_halfDensity_cap`
- `thetaCuspAtomRawEvenMoment_zero_eq_two_mul_tilt_zero`
- `thetaCuspSourceExponentialTilt_zero_sq_le_half_mul_neg_half`
- `thetaCuspAtomRawEvenMoment_zero_sq_add_orientation_sq_le_budget_sq`
- `thetaCuspAtomRawEvenMoment_zero_lt_halfDensityBudget`
- `thetaCuspFirstAtomRawEvenMoment_zero_lt_halfDensityBudget`
- `exp_orientation_lt_two_pi_mul_thetaCuspLiouvilleGibbsMoment_zero`
- `exp_neg_pi_lt_two_pi_mul_firstLiouvilleGibbsMoment_zero`
- `two_mul_integral_cosh_half_mul_thetaCuspSourceTerm_eq_budget`
- `thetaCuspAtomRawEvenMoment_zero_le_halfDensityBudget`
- `thetaCuspFirstAtomRawEvenMoment_zero_le_halfDensityBudget`
- `one_add_sq_div_two_le_cosh`
- `one_add_sq_div_eight_le_cosh_half`
- `thetaCuspFirstAtomMomentPair_le_halfDensityBudget`
- `integral_exp_half_mul_thetaCuspFullSource_eq_half`
- `two_mul_integral_cosh_half_mul_thetaCuspFullSource_eq_half`
- `thetaCuspHigherHalfDensityBudget`
- `two_mul_integral_cosh_half_mul_thetaCuspHigherSource_eq_budget`
- `thetaCuspHigherAtomRawEvenMoment_eq_integral_tail`
- `thetaCuspHigherAtomMomentPair_le_halfDensityBudget`
- `thetaCuspHigherAtomRawEvenMoment_zero_le_halfDensityBudget`
- `thetaCuspHigherHalfDensityBudget_nonneg`
- `thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget`
- `thetaCuspRawEvenMoment_zero_le_first_add_higherHalfDensityBudget`
- `thetaCuspFirstAtomMomentTriple_le_halfDensityBudget`
- `thetaCuspFirstAtomRawEvenMoment_two_le_halfDensityRemainder`
- `thetaCuspRelaxedFourthMomentConcentration_of_firstAtomHalfDensityRemainder`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_firstAtomHalfDensityRemainder`

## Verification

- isolated scratch proof passed before source insertion;
- both touched Lean files pass direct `lake env lean` checks;
- missing cache objects were produced only by serialized exact-module builds, including
  `lake build +GaloisForLFunctions.HTGeometry.ObservationMomentBudget`; no full or self-parallel
  build was run;
- six new generic/orientation/fidelity capstones use only `propext`, `Classical.choice`, and
  `Quot.sound`;
- five completed/higher-tail capstone declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`;
- the repository formal lint gate passes;
- no numerical computation, full build, or self-concurrent build was run;
- the fourth-order module was cached by the serialized exact target
  `+GaloisForLFunctions.RHTower.PrimeArchThetaHalfDensityMomentRemainder` and then passed its
  direct source-file check;
- its six new fourth-order/remainder capstones use only `propext`, `Classical.choice`, and
  `Quot.sound`;
- a single serialized targeted attempt to cache `PrimeArchThetaAtomLikelihoodRatio` stopped in
  independently failing shared dependencies (`HTGeometry.MonotoneLikelihoodRatio` and
  `HTGeometry.VacuumFeshbachValue`); no theorem in this card depends on that failed target.

## Gates

- [x] exact half-line endpoint/Ward relation
- [x] exponential-tilt integrability and vanishing top boundary
- [x] shifted Laplace identity
- [x] exact two-sided half-density budget
- [x] exact antisymmetric half-density orientation value
- [x] odd first/third moment budget from the exact orientation
- [x] second-moment log-convexity and closed first raw-moment square bound
- [x] direct first Ward/Liouville moment cap
- [x] necessary half-density cap for the live relaxed fourth-moment hypothesis
- [x] fourth-order half-density remainder eliminates the first atom's unknown fourth moment
- [x] direct linear-Hankel consumer replaces the relaxed fourth-moment hypothesis by the exact
  lower-order endpoint remainder
- [x] generic HTGeometry opposite-channel fidelity theorem
- [x] strict square-deficit and raw-moment bound
- [x] direct existing Liouville--Gibbs zeroth-moment consumer
- [x] direct existing raw-moment upper bound
- [x] exact completed-source and higher-tail budget subtraction
- [x] direct full/higher two-moment and zeroth-moment consumers
- [ ] formalize the normalized likelihood-ratio transfer (shared dependency currently fails)
- [ ] consume the remaining finite first-atom inequalities in a sign/energy certificate
- [ ] prove the lower-order endpoint remainder condition `(3h)` from a source-specific identity
- [ ] RH
