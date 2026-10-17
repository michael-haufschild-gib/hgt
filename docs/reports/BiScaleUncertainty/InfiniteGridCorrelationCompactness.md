# Global correlation compactness and preservation of singular energy

Fix K>=0. Let S_K consist of actual real compactly supported C² sources f with positive
mass R_f=h_f(0), normalized Lévy energy E_f<=K, and h_f(log n)=0 for every integer n>=2.
Write H_f=h_f/R_f. These are the domain conditions, not assumed analytic interfaces.

## Compact closure [PROVED HERE]

The set {H_f:f in S_K} has compact closure in the supremum norm on bounded continuous
functions on the whole real line. In particular, every sequence in S_K has a subsequence
whose normalized correlations converge uniformly on all of R to a continuous real H.

Proof. The correlation envelope gives |H_f(x)|<=1. The certified theorem
`exists_uniform_autocorr_continuity_radius` supplies one continuity radius for all f in
S_K, at every location. The certified `exists_uniform_infinite_grid_tail_radius` supplies
one two-sided tail radius for the same class. For a prescribed epsilon, restrict to a
compact interval outside which every H_f is small. Cover that interval by finitely many
common continuity neighborhoods, and discretize the bounded range on their centers.
Functions with the same finite data differ by less than epsilon on the interval; their
uniformly small tails give the same control outside. Thus the family is totally bounded.
The complete space of bounded continuous functions gives compact closure and sequential
compactness. The already proved `HTGeometry.totallyBounded_bcf_of_uniform_tails` implements
this exact argument for complex functions. Complexify H_f isometrically and apply it;
taking real parts preserves uniform convergence and yields the real limit claimed here.

## Geometry of every limit [PROVED HERE]

Any such uniform limit satisfies:

- H is continuous, H(0)=1, |H(x)|<=1, H(-x)=H(x), and H(log n)=0 for all n>=2.
- For every epsilon>0 there is A>0 with |H(x)|<epsilon whenever |x|>=A.
- For every finite real coefficient family c_i and real locations t_i,
  sum_i sum_j c_i c_j H(t_i-t_j)>=0.

Proof. Uniform convergence implies pointwise convergence, preserving normalization,
evenness, the pointwise envelope, and each grid zero. To retain strict tail smallness,
choose the common source tail radius at epsilon/2 and pass to the pointwise limit there;
the limit magnitude is at most epsilon/2. For the Gram assertion, the exact identity

    sum_i sum_j c_i c_j H_f(t_i-t_j)
      = (1/R_f) integral (sum_i c_i f(u+t_i))² du

is nonnegative. Finite sums commute with pointwise limits, so their limits remain
nonnegative. No spectral representation theorem or source realization of H is used.

## Singular-energy closure [PROVED HERE]

For any real kernel H, define its extended normalized energy

    J_ext(H) = integral_(0,infinity) [(1-H(x)) w(x)]_+ dx,
    w(x)=exp(x/2)/sinh x,

as a nonnegative extended-real Lebesgue integral. For each H_f this equals E_f exactly:
the integrand is nonnegative, since H_f<=1 and w>0, and source regularity ensures its
ordinary integrability. Dividing the original integrand by R_f gives (1-H_f)w.

For any sequence H_n converging pointwise to H,

    J_ext(H) <= liminf J_ext(H_n)

whenever the H_n are measurable. This follows directly from Fatou: the positive-part
integrands converge pointwise, since multiplication by the fixed finite w(x) and the
nonnegative-part embedding into extended reals are continuous. In the source application,
each H_n is continuous and J_ext(H_n)=E_n<=K. Hence J_ext(H)<=K<infinity.

For the actual limit H above, H<=1 and w>=0 on (0,infinity), so the positive part is the
integrand itself. Continuity of H and measurability of w give measurability. Finiteness
of J_ext(H) therefore proves ordinary integrability of (1-H)w, and

    integral_(0,infinity) (1-H(x))w(x) dx <= K.

Thus no mass in the nonnegative singular energy can appear in a uniform limit beyond the
original energy budget. Energy may decrease; equality is not asserted.

## Significance and boundary

The bounded-energy infinite-grid class has a compact correlation relaxation with its
positivity and energy constraints intact. This supplies the missing limit-extraction step
for variational questions posed in correlation space. It does not prove that each relaxed
kernel has a compact or square-integrable source, and it does not establish closedness of
the exponentially weighted polar condition. Those remain distinct questions.

The general compactness and Fatou principles are reused, not claimed as new. The new
connected result derives their hypotheses from this field's actual source class and
retains its complete grid, Gram positivity, and singular energy in the resulting limits.

## Formal certificate

Both leaves passed direct `lake --old env lean` checks without diagnostics:
`InfiniteGridCorrelationCompactness.lean` (nine public theorems) and
`InfiniteGridLimitEnergy.lean` (eight public theorems, one private normalization identity).
The leaf checks emitted artifacts for a separate scratch import audit.

The complete endpoint is `exists_infiniteGrid_finite_energy_limit`. Its source domain is
`InfiniteGridEnergySource K`, containing an actual compact source, C² regularity, positive
mass, the energy ceiling, and every logarithmic-grid zero. All compactness, integrability,
and positivity estimates are derived. The principal reusable endpoints are:

- `isCompact_closure_infiniteGrid_correlations`
- `exists_uniform_limit_infiniteGrid_correlations`
- `infiniteGrid_uniform_limit_geometry`
- `correlationLevyEnergy_le_liminf`
- `infiniteGrid_pointwise_limit_energy_le`
- `infiniteGrid_uniform_limit_integrable_energy`
- `infiniteGrid_uniform_limit_gram_nonneg`

All seventeen dependency audits passed with only `propext`, `Classical.choice`, and
`Quot.sound`. The private normalization identity is included transitively. Both imports
and every generated API entry were verified. This connected package counts once: 8/100.

Logs: `/tmp/infinite-grid-{compactness,limit-energy}-leaf.log` and
`/tmp/infinite-grid-compactness-{axioms,index,lint}.log`.
Global lint failed only on three concurrent foreign modules missing umbrella reachability:
`RHTower.FermiNymanDyadicFoldGeometry`, `BiScaleUncertainty.DyadicMultiplierFrameBound`,
and `BiScaleUncertainty.SignedPrimePolarCoupling`. Neither new leaf has a lint error.
No full or umbrella build was run.
