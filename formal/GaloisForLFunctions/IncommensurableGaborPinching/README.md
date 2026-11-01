# Incommensurable Gabor Pinching (IGP)

Namespace `GaloisForLFunctions.IncommensurableGaborPinching`; umbrella `IncommensurableGaborPinching.lean`.
The flagship theorems for `ζ` are unconditional. They are built on the `Zeta23` library (Alpöge–Furman Theorem D:
zero-side Gram, seams, `paperInputs_zeta`, `zetaZeroConfig`); the abstract lemmas take Zeta23's parameter packages
(`PhiHatConj`, `PoissonSq`, `TailInputs`, `P.Valid`) as hypotheses, discharged for `ζ` in the flagship statements.

## 1. Motivation

Alpöge–Furman prove that at least `HD(1) = 3/2 − cot(1/√2)/√2 ≈ 0.6725007` of the zeros of `ζ` are simple and on the
critical line, using a rank–trace inequality on the Gram of zero evaluation vectors. Their bound on the simple on-line
summand `P₁ = Σ_{S₁} w_zw_zᵀ` uses only trace dominance `‖P₁‖_F² ≤ tr P₁`, which is sharp only when the evaluation vectors are
pairwise orthogonal. IGP asks whether the Montgomery–Taylor cosine window allows that orthogonality. It does not: the
correlation kernel of the cosine window has non-lattice zeros, so dense on-line zeros must have off-diagonal Gram energy.
That energy is a structural (Gram-geometric) gain and lifts the proportion strictly above `HD(1)`.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Rotation scalars | `exists_unit_rot_scalars`, `rot_outer_eq` | real `2 × 2` rotation diagonalizing a symmetric block; preserves `uu* + ww*` |
| Vector norms | `vecSq`, `realInnerVec` | `Σ‖u_a‖²`, `Re⟨u, w⟩` |
| MT kernel | `mtKernelNum`, `mtKernel` | `∫_{−1/2}^{1/2} cos(√2λv)cos(2πΔv)dv`, normalized by `aStar` |
| Exclusion intervals | `mtExcl₁`, `mtExcl₂` | `(26/25, 43/40)`, `(503/250, 256/125)`: where the kernel can vanish on `[0, 3]` |
| Grid overlap | `pairGridOverlap` | `(aL²)⁻¹Σ_k φ̂_R(γ_x − τ_k)φ̂_R(γ_y − τ_k)`: finite-grid Gram entry of two zeros |
| Bulk simple zeros | `S₁Bulk` | simple critical zeros with ordinate in `(T + √T, 2T − √T]` |

External (Zeta23): `kc` `k_c(t) = c² − ((c − t)₊)²`, `Pmat`, `xsq`, `rank_trace_mult_k` (Lemma R), `ZeroBlockData`, `HD`,
`GD`, `cStar`, `vStar`, `aStar`, `AdmWindow`, `Params`.

## 3. Language

- **Pinching slack**: the gap between `tr P` and `‖P‖_F²` (Schur–Jensen) discarded by trace dominance.
- **Kink**: `t = c` in `k_c`; below it `k_c(t) = 2ct − t²` is quadratic, so rotations act exactly.
- **Non-lattice zeros**: the kernel zeros on `[0, 3]` sit in two short intervals whose sumsets miss both intervals; contrast
  the boxcar sinc kernel with zeros on `ℤ ∖ {0}`.
- **Short triple**: three consecutive bulk ordinates with scaled span `(L/2π)(γ₃ − γ₁) ≤ 3`.

## 4. Mechanisms

1. **Disjoint-pair rotation.** For `c ≥ 2` and two unit-multiplicity vectors of norm `≤ 1`, the rotation diagonalizing their real
   Gram block keeps `P = WWᴴ`, keeps both norms below the kink, and extracts `2Re⟨v_x, v_y⟩²` from `Σk_c`
   (`exists_unit_rot_kc`). Inducting over a disjoint family gives Lemma R with slack (`rank_trace_mult_k_disjointPairs`),
   then block bounds (`mult_two_disjointPairs`, `mult_three_disjointPairs`) and Seam A bounds.
2. **Non-lattice floor.** Closed form `((πΔ)² − θ²)·num = πΔ cos θ sin(πΔ) − θ sin θ cos(πΔ)` (`θ = λ/√2`), trig enclosures for
   `λ ∈ [0.999, 1]`, and an 11-subinterval case split give `|K_λ| ≥ 1/250` off `I₁ ∪ I₂` (`one_div_250_le_abs_mtKernel`).
3. **Sumset disjointness.** `2·(26/25) > 256/125` and `26/25 + 503/250 > 3`: in any short triple, the two gaps and their sum
   cannot all lie in `I₁ ∪ I₂` (`exists_pair_mtKernel_ge_of_triple`).
4. **Grid transfer.** Parseval for `φ'` bounds the far grid tail by `4L²(c/w)²/T`; taper-vs-sharp-window comparison costs
   `≤ 6w/(aL)`; uniformly on bulk pairs the grid overlap is within `1/500` of `K_λ` (`eventually_pairGridOverlap_atD_close`).
5. **Mod-3 packing.** Two-step spans telescope to `≤ 2α(b − a)`; the best residue class mod 3 gives `9|R| ≥ 3(m − 2) − 2α(b − a)`
   disjoint short triples (`exists_disjoint_short_triples`). With `|S₁Bulk| ≥ 0.6716N` and `αT ≤ N` this is `≥ N/625` triples,
   each worth `≥ (1/500)²`, total `2Σoverlap² ≥ 10⁻⁸N` (`eventually_exists_disjointPairs_slack`).
6. **λ → 1.** `HD(1) − HD(λ) ≤ 56π²(1 − λ)` (`HD_one_sub_HD_le`) lets the gain survive the limit `λ ↑ 1`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Lemma R with disjoint-pair Schur–Jensen slack | `rank_trace_mult_k_disjointPairs`, `seamA_mult2_disjointPairs`, `seamA_mult3_disjointPairs` | proved |
| Non-lattice floor of the MT kernel | `one_div_250_le_abs_mtKernel`, `exists_pair_mtKernel_ge_of_triple` | proved |
| Bulk grid overlap ≈ kernel | `eventually_pairGridOverlap_atD_close` | proved |
| Arbitrary-bandwidth cosine sampling | `pairGridOverlap_cosineParams_error`, `eventually_pairGridOverlap_cosineParams_close` | proved |
| Wide local estimates and complex-strip Fourier decay for independent cosine shape and bandwidth | `cosineParams_eventually_localHypsCoreW`, `cosineParams_phiHat_decay` | proved |
| Explicit actual credit `1/[200(10+720π²λ²)²]` at every fixed positive bandwidth | `zetaCosine_explicit_disjointPairs`, `zetaCosine_explicit_rankTrace` | proved, unconditional |
| Exact kernel degeneracy classification | `mtKernel_additive_zero_triple_iff` | proved |
| Explicit all-frequency weighted triple floor | `cotangentLineResidual_triple_floor`, `mtKernel_explicit_triple_floor` | proved |
| Shape-one diagonal coefficient above the box rate for `λ ≥ 1` | `shapeOneCosineRate_ge_box`, `cosineWindowRate_fourThirds_eventually` | proved; prime surplus remains separate |
| Macroscopic slack `≥ 10⁻⁸N(T,2T)` | `eventually_exists_disjointPairs_slack` | proved |
| Simple critical proportion `≥ HD(1) + 10⁻⁸` | `beyond_HD_one_simple_critical_cumulative`, `simple_critical_proportion_ge_67250071` | proved, unconditional |
| Distinct zeros `≥ GD(1) + ½·10⁻⁸` | `beyond_GD_one_distinct_cumulative` | proved, unconditional |
| Transport to the `ξ` census; liminf form | `beyond_montgomeryTaylor_xiSimpleCritical_epsilon`, `HD_one_add_pos_le_liminf_xiSimpleCriticalRatio` | proved |

## 6. Tools

**Developed**
- Kink-safe pair rotation `exists_unit_rot_kc` and simultaneous version `exists_disjointPairs_rot`.
- Exact closed form and rational floor for the cosine Gabor kernel; `HD_one_ge_67250070` (degree-20 Taylor enclosure).
- Grid-tail Parseval bound for admissible windows; taper comparison `VPhiR_phiD_close`.
- Abstract `c = 3` seam consumer `thmD_mult3_count_of_seam`; abstract improvement `thmD_beyond_lam_abstract`.
- Boundary-strip and scale bounds from Riemann–von Mangoldt (`isLittleO_boundary_N`, `eventually_L_mul_T_div_two_pi_le_N`).

**To build**
- Slack from pairs at all spans (not only short triples), with the true macroscopic constant.
- A window optimized jointly for the diagonal bound and the non-lattice floor.
- Slack for multiple zeros and for the full distinct-zero count.

## 7. Open questions

1. What is the true macroscopic off-diagonal energy of simple critical zeros under the MT window?
2. Positive zero-side pair slack now holds for every fixed `λ > 0`. Can its matching signed prime-side source be bounded past `λ = 1`?
3. Which windows maximize `diagonal gain + pinching slack`?
4. Does the same Gram geometry give gains in other rank–trace zero-density arguments?

## 8. Traps

| Trap | Fact |
|---|---|
| Trace dominance is sharp for the rank–trace method | It discards the pinching slack; the cosine kernel forces some |
| Any window gives slack | Boxcar windows allow orthogonality on a shifted lattice |
| The gain is arithmetic | It is Gram geometry; it says nothing about off-line zeros |
| Rotations can move norms past the kink | Two vectors of norm `≤ 1` sum to `≤ 2 ≤ c`; no crossing |
| `10⁻⁸` is the true gain | It is what short triples certify |

## 9. Context

**Uses**

| Programme | Imports | For |
|---|---|---|
| Zeta23 (library) | 2 | Theorem D, Lemma R, seams, parameter packages, `ζ` zero configuration |
| RHTower | 3 | sampling Parseval, horizontally isolated simple zeros, MT off-line moment, `ξ` census transport |

**Used by**

| Programme | Modules | For |
|---|---|---|
| `MainTheorems.lean` | 1 | flagship zero-proportion theorems |

| Neighbour | Relation |
|---|---|
| ArithmeticCastelnuovoSeveri | rank–trace inertia and `HD(1)` bounds in the scaling-surface setting |
| TransThresholdPairCorrelation | pair correlation beyond `λ = 1`; IGP supplies positive pair credit at every fixed bandwidth |
| ArithmeticLorentzianGeometry | Gram slack as a signature cost |

## 10. Big picture

IGP is a zero-proportion result, not an RH route. Its lesson is methodological: the best unconditional counting
arguments throw away Gram geometry, and keeping it pays. The Montgomery–Taylor window cannot make dense on-line zeros
orthogonal because its kernel zeros are not on a lattice, so the trace bound is never attained and a definite fraction of
energy is recovered.

For the RH programme this marks what structural information alone can and cannot do. It improves constants in counting
arguments that are blind to arithmetic, and the improvement is tiny (`10⁻⁸`) and certified only for the shortest
configurations. It does not touch off-line zeros. Arithmetic positivity has to come from elsewhere; IGP shows that
existing zero-density machinery is not saturated and that its slack is Gram geometry.
