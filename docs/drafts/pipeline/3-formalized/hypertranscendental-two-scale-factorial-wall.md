# The two-scale factorial wall and noncommuting limits of hypertranscendental filtrations

- **ID:** `hypertranscendental-two-scale-factorial-wall`
- **Stage:** 3-formalized
- **Type:** GENERAL HT MULTIFILTRATION / ALL-ORDER ANALYTIC UNIFORMIZATION THEOREM
- **Scientific status:** `[CORE THEOREMS LEAN-FORMALIZED] [SOURCE INSTANCE LEAN-FORMALIZED] [EXTERNAL NOVELTY PROVISIONAL] [NOT AN RH RESULT]`
- **Parents:**
  `hypertranscendental-controlled-cohomology-and-bornological-shape.md`,
  `gamma-factorial-asymptotic-connection.md`
- **Statement:** Finite analytic resolution and infinite jet resolution do not commute.  A
  comparison germ can converge uniformly to the identity in a source parameter while retaining an
  unbounded raw derivative tail at every parameter value.  For tangent Möbius comparisons the
  obstruction is exactly factorial, and Taylor normalization converts it exactly to a geometric
  positive-capacity profile.  Therefore the universal HT obstruction object requires at least two
  scale directions: source depth and observable order.

## 1. Exact Möbius jet law

For `a in C`, define the tangent-to-identity Möbius germ

```text
M_a(z)=z/(1-az).                                                  (1)
```

Its Taylor expansion at zero is

```text
M_a(z)=sum_(j>=0) a^j z^(j+1).                                   (2)
```

### Theorem A: raw and normalized all-order jets

For every `k>=1`,

```text
M_a^(k)(0)=k! a^(k-1),                                           (3)
M_a^(k)(0)/k!=a^(k-1).                                           (4)
```

The raw derivative norms satisfy the exact recurrence

```text
|M_a^(k+1)(0)|=(k+1)|a| |M_a^k(0)|.                              (5)
```

Equations `(3)`--`(5)` are Lean-formalized.

## 2. The all-order no-go

Assume `a!=0`.  The multiplier in `(5)` tends to infinity.  Choose `K` so that
`(k+1)|a|>=2` for `k>=K`.  Then

```text
|M_a^(K+j)(0)| >= 2^j |M_a^K(0)| -> infinity.                    (6)
```

### Theorem B: no nontrivial raw all-order Möbius uniformization

For every `a!=0`, the raw derivative profile of `M_a` is unbounded.  Consequently no normed
all-order jet carrier in which the coordinate functionals have uniform unweighted derivative cost
can implement a nontrivial tangent Möbius comparison by a bounded transformation.

This no-go remains true however small `|a|` is.  Analytic closeness of germs and agreement at every
fixed finite jet order do not imply bounded equivalence of their complete raw jet towers.

The strong positive successor is exact rather than qualitative: the obstruction is precisely the
factorial removed in `(4)`.

## 3. Taylor/Gevrey normalization is forced

The Taylor-normalized profile in `(4)` is geometric.  For `|a|<1`, its squared Hardy capacity is

```text
Cap_Tay(a)=sum_(j>=0) |a|^(2j)=1/(1-|a|^2).                      (7)
```

The inverse germ is `M_a^(-1)=M_(-a)`, so it has the same capacity.  Thus Taylor normalization
makes the comparison uniformly two-sided bounded on every region `|a|<=q<1`.

The boundary is exact:

```text
|a|<1:  finite all-order normalized capacity,
|a|=1:  cutoff capacity is exactly N+1,
|a|>1:  exponential capacity escape.                             (8)
```

### Theorem C: factorial-wall uniformization

Raw derivative grading rejects every nonidentity Möbius comparison, while factorial/Taylor
grading admits exactly the open unit parameter disk and places its thin capacity wall at the unit
circle.

This identifies the missing analytic structure in the capacity field.  Hypertranscendence supplies
an infinite algebraic jet tower, but analytic comparison forces a Gevrey/Taylor weight scale on
that tower.  The weight is not optional decoration: without it, even arbitrarily small coordinate
changes are unbounded at sufficiently high order.

### Theorem D: Gevrey order one is the unique critical completion

For a real Gevrey exponent `sigma`, normalize the `k`th derivative by `(k!)^sigma`.  The exact
profile is

```text
G_(sigma,k)(a)=(k!)^(1-sigma)|a|^(k-1),
G_(sigma,k+1)(a)/G_(sigma,k)(a)=(k+1)^(1-sigma)|a|.              (G)
```

For every `a!=0`, the ratio in `(G)` gives the complete trichotomy:

```text
sigma<1:  G_(sigma,k)(a) is unbounded; only the identity chart is admissible,
sigma=1:  G_(sigma,k)(a)=|a|^(k-1); a proper finite wall survives,
sigma>1:  G_(sigma,k)(a)->0 and is square-summable for every finite a.               (H)
```

For `sigma>1`, the ratio tends to zero, so the tail is dominated by a geometric sequence.  For
`sigma<1`, the ratio tends to infinity and is eventually at least two.  At `sigma=1`, boundedness
holds exactly for `|a|<=1`, while square summability holds exactly for `|a|<1`.

Thus Taylor order is selected by a structural requirement: the chart category must be nontrivial
but must not collapse all finite Möbius scales into one bounded class.  Subcritical weights make
the completion discrete; supercritical weights erase the finite boundary; order one is the unique
critical exponent.  Multiplying the weights by an exponential scale `R^k` moves the wall radius
but does not change the selected Gevrey exponent.

Lean verifies all three representative regimes: raw order zero, critical Taylor order one, and
supercritical order two.  In the last case

```text
||M_a^((k+1))(0)|| / (((k+1)!)^2) <= exp(|a|)                   (I)
```

for every `a` and `k`.  The continuous real-exponent trichotomy is proved above from `(G)` but has
not yet been encoded with real powers in Lean.

The critical profile is also faithful, not merely bounded: its `k=1` coordinate recovers `a`.
Thus `a |-> (a^k)_k` is injective.  This first local completeness theorem is Lean-formalized as
`mobiusCriticalJetProfile_injective`.

## 4. Noncommuting source and jet limits

Let `a_n!=0` and `a_n->0`.  For every fixed `k>=2`, equation `(3)` gives

```text
M_(a_n)^(k)(0) -> 0.                                             (9)
```

But Theorem B gives, for every fixed `n`,

```text
sup_k |M_(a_n)^(k)(0)|=infinity.                                 (10)
```

In extended-real notation,

```text
sup_k lim_(n->infinity) |M_(a_n)^(k)(0)| = 1,
lim_(n->infinity) sup_k |M_(a_n)^(k)(0)| = infinity.             (11)
```

The value `1` on the first line is the persistent first derivative.  If only nonlinear orders
`k>=2` are retained, the first quantity is `0`; the second remains infinity.

### Theorem E: source depth and observable order do not commute

Pointwise convergence at every finite observable order cannot be upgraded to uniform convergence
on the raw infinite jet tower.  Taylor normalization repairs the interchange: for `|a_n|<=q<1`,
the normalized profiles are dominated by the summable geometric majorant `q^(k-1)`, and their
nonlinear capacity tends to zero by dominated convergence.

This is an exact model of an obstruction concentrated on a moving thin boundary.  At source depth
`n`, the comparison looks trivial below every fixed order, yet factorial amplification reappears
beyond an `n`-dependent order horizon.

## 5. Gamma source theorem

For the reciprocal-Gamma pole filtration,

```text
a_n=s_n/n,
s_n=(-1)^(n+1)/n!.                                               (12)
```

The normalized inverse branch `B_n` and intrinsic moving-base transition are related by

```text
D_n=M_(a_n) composed with B_n.                                  (13)
```

The source theorems prove

```text
a_n -> 0,
sup_t |D_n(t)-B_n(t)| <= 2|a_n| -> 0,
B_n -> id uniformly,
D_n -> id uniformly                                             (14)
```

on one common closed analytic collar.

Combining `(3)`--`(14)` gives the first actual two-scale HT source instance:

```text
fixed finite order: B_n and D_n become identical as n->infinity,
raw all-order tower: their Möbius chart change is unbounded for every n,
Taylor-normalized tower: the chart-change capacity is <=4/3 once |a_n|<=1/2.           (15)
```

This closes the analytic comparison and identifies the exact normalization needed for a bounded
all-order chart.  Transport of the full positive capacity form and relative algebraic
multiplicities through composition remains open.

## 6. The higher object forced by the wall

A path over one grading ray is insufficient.  The minimal index geometry is at least the directed
product

```text
source/realization depth  x  observable/jet order.               (16)
```

Different cofinal paths through `(16)` can see different limits because of `(11)`.  Therefore a
conservative comparison must control a cofinal region in the product bornology, not merely each
row, each column, or one diagonal separately.

This failure has an exact universal scalar model:

```text
h(n,k)=max(k-n,0).                                                (17)
```

For every fixed `k`, `h(n,k)=0` eventually in `n`, and the diagonal path has `h(n,n)=0` exactly.
Nevertheless every row `h(n,-)` is unbounded, so the full product profile is unbounded.  The
diagonal is cofinal in the product order but not bornologically cofinal in the transport image.

### Theorem F: cofinal-region criterion

For arbitrary index types `I,J`, a profile `h:I->R`, and comparison `phi:J->I`, suppose the sampled
transport image is uniformly dense:

```text
there is C such that for every i in I there is j in J with
|h(i)-h(phi(j))|<=C.                                             (18)
```

Then `h` is uniformly bounded if and only if `h composed with phi` is uniformly bounded.  This
theorem and the strict diagonal counterexample `(17)` are Lean-formalized.  Thus the required
notion is not order-theoretic cofinality but bornological cofinality of the realized diagram.

Define the provisional **multifiltered polarized HT shape** as the localization of source-natural
signed Hermitian capacity diagrams, with positivity as their distinguished chamber, over their
full directed scale cones at comparisons that are bornologically
cofinal on cofinal regions and uniformly tame in the required Gevrey weights.

The algebraic body under these diagrams is universal: every pair of one-generator HT sources has
canonically equivalent marked finite-jet fields at every order.  Hence the source-sensitive object
is not a new algebraic jet variety but a completion structure on the universal free jet tower.
This sharpening is proved and gated in
`hypertranscendental-algebraic-bulk-completion-boundary.md`.

**[CONJECTURE: MULTISCALE COMPLETENESS.]**  The derived self-dual multifiltered polarized HT shape is the
initial conservative recipient of every persistent source-natural HT reconstruction obstruction.
Spectral, continuation, positivity, monodromy, and boundary-condition failures are restrictions to
different cofinal directions or boundary functors of this one shape.

**[CONJECTURE: DIRECTIONAL DEGENERACY.]**  The common degeneracy object is not generally a set of
points on one spectrum.  It is a conic support in the boundary of the scale diagram.  Different
proof chains report different shadows because they approach that support along different cofinal
directions.  A common self-dual degeneracy spectrum exists only after proving those directional
restrictions conservative with multiplicity.

These conjectures are general HT statements.  A future zeta realization may test them, but no RH
claim follows.

## 7. External novelty gate

Established parent theories include:

- groups of analytic and formal diffeomorphism germs,
  https://arxiv.org/abs/2206.09652 and https://arxiv.org/abs/math/0207297;
- weighted composition operators on Hardy, Bergman, and other analytic-function spaces,
  https://arxiv.org/abs/1706.09001 and https://arxiv.org/abs/2110.05247;
- weighted diffeomorphism groups, https://arxiv.org/abs/1006.5580;
- Gevrey normalization of formal series, https://arxiv.org/abs/math/0609618;
- invariant jet differentials, https://doi.org/10.1007/s00222-023-01219-z;
- coarse cohomology and coarse compactification,
  https://arxiv.org/abs/1711.08599 and https://arxiv.org/abs/2009.08147.

The Möbius Taylor series, factorial derivative growth, geometric-series capacity, Gevrey weights,
and composition operators are not new separately.  Targeted searches located no external theorem
that derives the noncommuting scale law `(11)` from an actual hypertranscendental source
filtration, combines it with the capacity-realization and bounded-gauge theorems, and proves that
the universal obstruction object must be localized over a bornological product of source and
observable scales.  This is provisional absence, not a priority proof.

## 8. Significance and anti-theatre gate

- `[PASS]` The theorem kills the one-ray version of the proposed unified object with an exact
  all-order counterexample.
- `[PASS]` The positive successor is forced and complete for the model: factorial/Taylor
  normalization converts the obstruction exactly into geometric capacity with a sharp wall.
- `[PASS]` Gamma supplies an actual source family with noncommuting source and jet limits.
- `[PASS]` The theorem gives a concrete mechanism for apparently incompatible obstruction chains:
  restriction along inequivalent cofinal directions of one multi-scale diagram.
- `[ANTI-THEATRE]` Equations `(1)`--`(8)` alone are classical complex analysis.  The candidate new
  science is their source-forced role in the HT capacity field and the minimal multifiltration
  theorem they force.
- `[FAIL until proved]` Multiscale Completeness, nonabelian/Gevrey descent, and conservative
  comparison of at least three obstruction functors remain open.
- `[PAPER VERDICT]` Together with capacity freedom, single-carrier rigidity, controlled
  cohomology, and the Gamma source comparison, this is a credible foundational-paper package.  It
  is not a standalone-paper claim about the elementary Möbius calculation.
- `[MEDAL-SCALE VERDICT]` Proving Multiscale Completeness and constructing two distinct analytic or
  arithmetic sources whose obstruction functors are multiplicity-conservative would establish the
  requested field.  The current theorem identifies the correct scale geometry but does not yet
  prove its universality.

## 9. Lean certificate

`GaloisForLFunctions/HTGeometry/GammaCommonInverseCollar.lean` verifies:

- `mobiusTangentGerm`;
- `iteratedDeriv_mobiusTangentGerm_zero`;
- `normalizedIteratedDeriv_mobiusTangentGerm_zero`;
- `mobiusCriticalJetProfile_injective`;
- `norm_iteratedDeriv_mobiusTangentGerm_zero_succ`;
- `gevreyTwoNorm_mobiusTangentGerm_zero`;
- `gevreyTwoNorm_mobiusTangentGerm_zero_le_exp`;
- `gammaMovingBaseShell`;
- `gammaMovingBaseTransition`;
- `gammaMovingBaseTransition_dist_branch_le`;
- `tendsto_gammaMovingBaseShell_zero`;
- `tendsto_gammaMovingBaseTransition_branch_uniformlyOn`;
- `tendsto_gammaCommonInverseCollar_branch_uniformlyOn`;
- `tendsto_gammaMovingBaseTransition_uniformlyOn`.

`GaloisForLFunctions/HTGeometry/HypertranscendentalClockBoundary.lean` verifies the product-scale
cofinality layer:

- the arbitrary-index `IsUniformlyBoundedProfile` and `IsBornologicallyCofinal`;
- `uniformlyBoundedProfile_of_bornologicallyCofinal`;
- `uniformlyBoundedProfile_iff_subsample_of_bornologicallyCofinal`;
- arbitrary-pseudometric `IsUniformlyBoundedAround` and `IsMetricBornologicallyCofinal`;
- `uniformlyBoundedAround_iff_subsample_of_metricBornologicallyCofinal`;
- `movingBoundaryProfile_fixedOrder_eventually_zero`;
- `movingBoundaryProfile_diagonal_bounded`;
- `movingBoundaryProfile_not_uniformlyBounded`;
- `diagonal_not_bornologicallyCofinal_for_movingBoundary`.

The cached source passed a direct Lean check after these declarations were added.  No build was
run.

## Gates

- [x] prove the exact raw Möbius all-order jet law
- [x] prove the exact Taylor-normalized jet law
- [x] prove the exact raw norm recurrence
- [x] prove raw all-order unboundedness for every nonzero parameter
- [x] identify the sharp normalized capacity wall
- [x] prove the Gevrey criticality trichotomy on paper
- [x] formalize the raw, Taylor-critical, and supercritical order-two regimes
- [x] prove and formalize the actual Gamma two-filtration analytic comparison
- [x] prove and formalize arbitrary-index bornological cofinality
- [x] prove and formalize the moving-boundary product-scale diagonal no-go
- [x] run targeted external parent and novelty searches
- [ ] formalize summability and the sharp Taylor-capacity formula
- [ ] construct the nonabelian Gevrey-weighted capacity category
- [x] lift boundedness preservation to arbitrary pseudometric, hence nonabelian, transport targets
- [ ] construct the source-natural invariant metric and Gevrey completion on positive capacity
      diagrams
- [ ] prove or falsify Multiscale Completeness
