# CCM singular-Loewner central-slab order law

- **ID:** `ccm-singular-loewner-central-slab-order-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL THEOREM / CCM COFINAL FALSIFIER
- **Scientific status:** `[PROVED] [LEAN-PROVED] [CANDIDATE NEW] [NOVELTY AUDIT OPEN]`
- **Parent:** `ccm-source-pencil-radical-evans-coefficient-law.md`
- **Formal modules:**
  - `GaloisForLFunctions.HTGeometry.PositiveResiduePoleForcing`
  - `GaloisForLFunctions.HTGeometry.HermitianLoewnerPoleForcing`
  - `GaloisForLFunctions.RHTower.CCM.CCMPositiveResidueCentralSlab`
  - `GaloisForLFunctions.RHTower.CCM.CCMPublishedSourceSineCoefficient`
  - `GaloisForLFunctions.RHTower.CCM.CCMSingularLoewnerPoleForcing`

## Main law

Let `T` be an arbitrary finite positive-semidefinite CCM divided-difference matrix on distinct
real clock nodes:

```text
T_ij=(b_i-b_j)/(x_i-x_j), i!=j.
```

Let `e` be any normalized active-even radical vector, let

```text
A=diag(x)-|diag(x)e><1|,
```

and let `T=B^T B`, `BR=I`, `C=BAR` be the full-radical quotient. No restriction is imposed on
`dim ker T`. Then

```text
x_i<x_j and b_j<b_i
  -> exists lambda in spec(C) intersect [x_i,x_j].          (1)
```

Equivalently, every negative source divided difference forces a real zero of the actual
complexified quotient characteristic polynomial in the same clock interval.

For a cofinal family of such quotients, suppose arbitrary scalar-normalized quotient
characteristic functions converge locally uniformly to centered Xi. Then for every pair of moving
nodes contained in `[-4,4]`,

```text
b_i<=b_j eventually whenever x_i<x_j.                      (2)
```

Dimensions, radical dimensions, normalization functions, and selected node pairs may all vary.

## Proof

Put `v_i=B delta_i` and `u=B diag(x)e`. The active-even column identity and full-radical quotient
intertwining give

```text
C v_i=x_i v_i-u.                                           (3)
```

The Gram identity gives

```text
<v_i,v_j>=T_ij=(b_i-b_j)/(x_i-x_j).                        (4)
```

Assume `[x_i,x_j]` contains no eigenvalue of the real symmetric matrix `C`. Expand `u,v_i,v_j` in
an orthonormal eigenbasis `q_r` of `C`. From `(3)`,

```text
<q_r,u>=(x_i-lambda_r)<q_r,v_i>
       =(x_j-lambda_r)<q_r,v_j>.                           (5)
```

Because `lambda_r` lies strictly to one side of the whole interval,

```text
(x_i-lambda_r)(x_j-lambda_r)>0.
```

Multiplying the two identities in `(5)` shows

```text
<q_r,v_i><q_r,v_j>>=0.
```

Parseval gives `<v_i,v_j>>=0`, contradicting `(4)` when `x_i<x_j` and `b_j<b_i`. This proves
`(1)`. The spectral theorem makes the forced eigenvalue a characteristic-polynomial zero.

Centered Xi is unconditionally nonzero on the closed complex disk of radius four. Local-uniform
convergence is uniform there, so all normalized approximants are zero-free on that disk eventually.
A descent between nodes in `[-4,4]` would produce a quotient zero in the disk by `(1)`, while the
scalar normalization cannot remove a characteristic-polynomial zero. Contradiction proves `(2)`.

## Why this is not the discarded rational-Pick argument

The earlier candidate claimed the common source `u` in `(3)` was automatically cyclic and that
every clock node was a regular interpolation point. Both claims fail when a radical coordinate
vanishes or a clock node is already a quotient eigenvalue. The proof above uses neither claim. It
works at singular nodes, permits pole cancellation in scalar response entries, and sees the full
quotient spectrum directly through the cross Gram sign.

## Scientific significance and exact frontier

This is a source-only, non-asymptotic necessary law for the sole cofinal branch left by the corpus:
graded index balance already excludes persistent response completion and selects active-even
completion. It converts divisor-faithful CCM convergence into an explicit order constraint on the
published von-Mangoldt--Gamma source coefficients.

The source side is now connected without an unnamed distributional step. Put `L=2a`,
`t_n=pi*n/a`,

```text
E_crit(h)=4*sinh(h/2)-sum_(2<=m<=exp(h)) Lambda(m)m^(-1/2),
rho_infinity(h)=exp(h/2)/(exp(h)-exp(-h)).
```

Stieltjes integration by parts has zero endpoint at every physical frequency and Lean proves

```text
b_n
 = (1/pi) integral_(0,L] sin(t_n h) rho_infinity(h) dh
   +(1/pi) integral_(0,L] E_crit(h) t_n cos(t_n h) dh.      (3)
```

The second integral is unchanged if `E_crit` is replaced by its formalized normalized Chebyshev
Volterra potential. Thus the central-node specialization of `(2)` is

```text
active-even CCM quotient determinants -> Xi locally uniformly
  -> b_n>=0 eventually for every moving physical 0<t_n<=4. (4)
```

Conversely, one negative coefficient in this slab forces an actual quotient characteristic zero
in `[0,t_n]` at that finite stage.

It does **not** prove RH and does **not** yet kill CCM. Exact unresolved decision problem is:

```text
For physical nodes t_n=2*pi*n/L inside [-4,4], does the explicit Gamma-sine plus
Chebyshev-cosine functional (3) become negative along every proposed cofinal CCM schedule? (5)
```

- A proven persistent descent makes `(2)` impossible and kills divisor-faithful active-even CCM
  determinant convergence.
- Proven eventual order is a new arithmetic regularity theorem that the determinant route must
  then combine with divisor-tight convergence.

No estimate, simple-evenness argument, finite-rank surrogate, or selected-ground-vector
approximation can replace this decision.

## Novelty boundary

Spectral decomposition, rational Herglotz monotonicity, and Loewner divided differences are
classical parent ingredients. Candidate-new content is the singular inverse-free operator law
`(1)` assembled with the actual CCM active-even full-radical quotient, followed by the arbitrary-
dimension cofinal Xi order law `(2)`. External priority remains open; no publication claim should
state novelty as settled before expert and bibliographic review.

## Lean surface

```text
positiveResidueResponse_le_of_poles_avoid
exists_pole_between_of_positiveResidueResponse_descent
exists_eigenvalue_mem_Icc_of_symmetric_resolvent_cross_neg
eventually_forall_ne_zero_closedBall_four_of_tendstoLocallyUniformly_XiC
eventually_positiveResidueResponse_mono_on_centralSlab_of_XiC_convergence
realMetricAdjoint_splitRadical
ccmActiveEven_singleColumn
quotientFrameColumn_dotProduct
ccmActiveEven_sourceDescent_forces_quotientCharpoly_zero
eventually_ccmActiveEven_source_order_on_centralSlab_of_XiC_convergence
ccmPublishedPolarPrimeSineCoefficient_physical_eq_completedErrorCosineMoment
ccmPublishedSourceSineCoefficient_physical_eq_arch_add_completedErrorCosineMoment
ccmCompletedErrorCosineMoment_eq_chebyshevVolterra
ccmActiveEven_negativePublishedSourceCoefficient_forces_quotientCharpoly_zero
eventually_ccmPublishedSourceSineCoefficient_nonneg_of_XiC_convergence
```

All declarations are theorem/definition based; no `axiom`, `sorry`, `admit`, `opaque`, `unsafe`,
or RH premise occurs.

## Gates

- [x] paper proof complete
- [x] singular-node/cyclicity hostile test passed
- [x] arbitrary radical dimension
- [x] actual active-even CCM quotient connector
- [x] actual published von-Mangoldt--Gamma coefficient connector
- [x] exact normalized-Chebyshev cosine-moment reduction
- [x] cofinal local-uniform Xi connector
- [x] Lean formalization
- [x] direct Lean checks, targeted build, and axiom audit
- [x] lint attributable audit; global lint has unrelated shared-tree umbrella omissions
- [ ] actual von-Mangoldt--Gamma persistent-descent or eventual-order theorem
- [ ] external novelty audit

## Log

- 2026-07-23 — proved scalar positive-residue descent forces an intervening pole.
- 2026-07-23 — replaced invalid cyclic rational realization by inverse-free simultaneous spectral
  expansion; proved negative cross Gram forces an intervening Hermitian eigenvalue.
- 2026-07-23 — instantiated exact CCM active-even completion, arbitrary full radical quotient, and
  complexified characteristic polynomial.
- 2026-07-23 — combined with Xi's unconditional radius-four zero-free disk to prove the moving-node
  cofinal source-order law.
- 2026-07-23 — identified the physical source coefficient with its finite Gamma sine term plus the
  completed-error/normalized-Chebyshev cosine moment; proved negative one-mode forcing and
  eventual nonnegativity under Xi convergence in Lean.
- 2026-07-23 — all five new modules pass direct Lean; targeted cached build
  `GaloisForLFunctions.RHTower.CCM.CCMSingularLoewnerPoleForcing` passes `8971/8971`; capstone axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Global lint reaches the new
  modules and reports only unrelated shared-tree modules missing from their umbrellas.
