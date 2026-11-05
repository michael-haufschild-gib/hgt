# FFP — the finite free route to the Jensen polynomials of Ξ

- **ID:** FFP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme); items below THEOREM (Lean) where marked
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.4
- **Statement:** realize the Jensen polynomials of `Ξ` as finite free convolutions of real-rooted
  pieces built from Gamma and Euler data; locate exactly where this fails.
- **Lean folder:** `formal/GaloisForLFunctions/FiniteFreeProbability/` (umbrella
  `FiniteFreeProbability.lean`, wired into `MainTheorems.lean`).

## Goal
Real-rootedness by an algebraic preservation law (Walsh / Hermite–Biehler) instead of a quadratic-form
sign, a square-root count or a collision exclusion.

## Dictionary and bridges
| Item | Statement | Lean |
|---|---|---|
| D1 | `p ⊞_d q = (1/d!) Σ_j q^{(d-j)}(0) p^{(j)} = S_q(D) p`, `S_q(D)X^d = q`; commutative, unit `X^d`; `(p ⊞_d q)(z)` is the apolarity pairing of `p(z+·)` with `q` | `AdditiveConvolution`, `JensenDictionary`: `ffConv`, `eval_ffConv`, `ffConv_comm`, `ffConv_X_pow_right` |
| D2 | Walsh, half-plane form: roots of `p` in `Im ≤ a`, of `q` in `Im ≤ b` ⇒ roots of `p ⊞_d q` in `Im ≤ a+b` (strict form too); real ⊞ real is real. Proof: polar derivatives + Laguerre's averaging lemma | `WalshHalfPlaneTheorem`: `ffConv_root_im_le`, `splits_ffConv`; `EulerFactorStability.ffConv_root_im_lt` |
| D3 | `R_d(f) = f(D)X^d` is a ring map: `R_d(fg) = R_d(f) ⊞_d R_d(g)` | `jensenRev_mul` |
| D4 | `R_d(e^{cz}) = (X+c)^d`; `⊞_d` against `R_d(g)` is `g(D)`; heat `e^{sD²} = ⊞_d He_{d,s}` | `jensenRev_exp`, `ffConv_jensenRev_right`, `heatOp_eq_ffConv` |
| D5 | Jensen ladder `(R_{d+1}f)' = (d+1) R_d f`; real-rootedness descends; Turán `2f₀f₂ ≤ f₁²` | `derivative_jensenRev`, `turan_of_splits_jensenRev` |

## Results
| # | Statement | Lean |
|---|---|---|
| R1 | **Finite free de Bruijn–Newman law.** For every `t > 0`, `J_d ⊞_d He_{d,t/d²} = e^{(t/d²)D²}J_d` is not real-rooted for all large `d`: no Gaussian component at scale `d^{-2}` (formal version of obstacle (i)). Mechanism: kernel representation, Tannery + dominated convergence, Vitali, Laguerre–Pólya limit, Rodgers–Tao | `FiniteFreeDeBruijnNewman.eventually_not_splits_heatOp_jensenPoly_XiC` |
| R2 | RH ⇔ infinitely many Jensen polynomials of `Ξ` are real-rooted | `riemannHypothesis_iff_frequently_splits_jensenPoly_XiC` |
| R3 | **Dirichlet pieces are never real-rooted** (real direction): a positive exponential mixture `Σ w_i e^{−λ_i w}` with two distinct frequencies violates Turán by the variance, so no `R_d`, `d ≥ 2`, is real-rooted | `not_splits_jensenRev_expMixture` |
| R4 | **Normalized Euler factors are Hermite–Biehler stable** (critical direction): roots of `R_d(e^{iℓw/2} − q e^{−iℓw/2})` lie on an Apollonius circle in `Im < 0`, every `d`, every `0 ≤ q < 1` | `im_neg_of_isRoot_jensenRev_eulerFactor` |
| R5 | Finite normalized Euler products stay in `Im < 0` (Walsh); their FE symmetrization `R_d(G_S) + R_d(G_S)^#` is real-rooted at every degree, for every `σ > 0` and finite set of primes | `im_eq_zero_of_isRoot_symmetrized_primeEulerProduct` |
| R6 | For every `t > 0`: `e^{(t/d²)D²}J_d` has `≥ M` distinct non-real roots for large `d` (every `M`), and in the scale `z = dx` its roots leave every horizontal strip (Hurwitz + Newman zeros of `H_{−t}`) | `BackwardHeatJensenNonRealRootCount` |
| R7 | Heat group `e^{sD²}e^{s'D²} = e^{(s+s')D²}`; forward heat preserves real-rootedness (Walsh against Hermite); Gaussian capacity `{s : e^{sD²}p real-rooted}` is an interval. **Shift regime:** for fixed `d` and `s < 1/2`, `e^{sD²}J̃^{d,n}` is real-rooted for large `n` (normalized and actual `J^{d,n}`): the shifted Jensen polynomials carry a Gaussian component of any fraction `< 1` of the Hermite variance | `ShiftRegimeGaussianCapacity` |

| R8 | **Szegő's composition theorem**: `p ⊠_d q = Σ C(d,k)a_k b_k X^k` is real-rooted for real-rooted `p` (degree `d`) and `q` (degree `d`) with roots in `(−∞,0]`; proof = half-plane apolarity applied to `y^d q(z/y)` | `SzegoComposition.splits_ffMul` |
| R9 | **Source-faithful ⊠ factorization** `J^{d,n} = (γ(n)/m(n)) Γ_{n,d} ⊠_d Θ_{n,d}` (Gamma Pochhammer piece ⊠ theta-moment piece); the theta piece is **never real-rooted** for `d ≥ 2` (Jensen ladder + strict log-convexity `m(k+1)² < m(k)m(k+2)`), so Szegő never certifies `J^{d,n}` through it | `GammaThetaSzegoFactorization` |

| R10 | **Capacity table**: heat commutes with `D`, so real-rootedness of `e^{sD²}J^{d+1,n}` implies that of `e^{sD²}J^{d,n+1}`; the degree row bounds the whole `(d,n)` table from below | `CapacityTable.splits_heatOp_jensenPoly_shift` |
| R11 | **Bernoulli robustness**: Bernoulli (cosine) shifts preserve real-rootedness (Hermite–Biehler), and for all `a, t > 0` the Bernoulli shift by `a/d` of `e^{(t/d²)D²}J_d` is still not real-rooted for large `d` (limit: cosine shift of `H_{−t}`, cosine de Bruijn–Newman theorem). Strengthens R1 | `BernoulliRobustness` |

| R12 | **Sharpness of the half-log normalization**: for `c < ℓ/2` the translated Euler factor `e^{icw}(1 − q e^{−iℓw})` has a reversed Jensen root `i(r(ℓ−c) − c)/(1+r)`, `r = q^{1/d}`, in the open upper half-plane for all large even `d`; each prime forces the drift `(log p)/2` | `EulerNormalizationSharpness` |
| R14 | **Sharp Hermite–Biehler threshold of finite Euler products**: for every nonempty finite `S`, `σ > 0`, `c < θ_S/2 = ½Σ_{p∈S} log p`, the translated product `e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` has reversed Jensen roots `iy`, `y > 0`, at all large degrees with `d + |S|` odd (signed-mixture domination on the imaginary axis); with R5 the threshold is exactly `θ_S/2`. **No bounded translation stabilizes all finite Euler products**, for any `σ > 0` (also `σ > 1`): the obstruction is the phase, not convergence | `EulerProductDriftIsForced` |
| R15 | **Real-zero horizon of symmetrized Euler products**: for `|S|` odd and `σ > 0`, the even real trigonometric sum `C(z) = Σ_{T⊆S} (−1)^{|T|}Π_T p^{−σ} · 2cos((c − λ_T)z)` (the symmetrization of `e^{icz}Π_S(1 − p^{−σ}e^{−iz log p})`) has only real zeros **iff** `c ≥ θ_S/2`. Above: translation `e^{aD}` = shift, Walsh + Hermite–Biehler make every Jensen polynomial real-rooted, so `C ∈ LP`. Below: `C(iy) = 2Σ w_T cosh((c−λ_T)y)` is `> 0` at `0` and dominated by the `T = S` term (weight `−Π_S p^{−σ}`) at large `y`, giving a zero `iy`, `y > 0` | `SymmetrizedEulerHorizon.symEuler_realZeros_iff` |
| R16 | **Pole pieces admit no stabilizing translation**: for a nonnegative mixture `Σ_k a_k e^{i(c−λ_k)w}` (coefficientwise), `R_d(ix) = i^d Σ a_k (x + c − λ_k)^d`; if `λ_k ≥ m` and some `λ_K > 2c − m` with `a_K > 0`, then for all large odd `d` there is a root `iy`, `y > 0` (far frequency dominates at `x = 0`, leading coefficient `Σ a_k > 0`). The pole piece `e^{icw}(1 − q e^{−iℓw})^{−1} = Σ q^k e^{i(c−kℓ)w}` (certified as `e^{icw}·(1 − q e^{−iℓw})^{−1}` in `ℂ⟦w⟧`) is unstable for **every** `c` | `PoleSideInstability.eventually_exists_upper_root_polePiece`, `polePiece_eq` |
| R17 | **The zeta side admits no stabilizing phase**: for `σ > 1` the Taylor series of `ζ(σ + iw)` (coefficients `i^kζ^{(k)}(σ)/k!`) equals the mixture `Σ_n n^{−σ}e^{−iw log n}`; for every `c` the reversed Jensen polynomials of `e^{icw}ζ(σ + iw)` have upper-half-plane roots at all large odd degrees | `ZetaSideInstability.eventually_exists_upper_root_zetaTaylor` |
| R18 | **The Gamma piece admits no stabilizing phase**: `e^{icw}Γ(1/4 + iw/2)` (certified: Taylor coefficients `i^k∫e^{u/4−e^u}(c + u/2)^k du/k!`, via `Γ^{(k)}(1/4) = ∫ e^{u/4−e^u}u^k du`) has reversed Jensen roots in the open upper half-plane at all large odd degrees, for every `c`. Mechanism: fold the log-variable weight about `u = −2c`; the bracket `e^{v/2−Ae^{2v}} − e^{−v/2−Ae^{−2v}}` is negative beyond `1/(2A)`, and a window at twice that distance beats the bounded positive part (the pole of `Γ` at `0` is the heavy tail) | `GammaSideInstability.eventually_exists_upper_root_gammaMixture`, `gammaMixture_eq` |
| R19 | **The Gamma piece is a Laguerre polynomial with negative real roots**: `Γ_{n,d}(X) = P_{d,c}(−X/4)`, `c = n + 1/2`, `P_{d,c} = Σ(−1)^jC(d,j)x^j/(c)_j`; against the Gamma moments `(c)_m` one has `⟪P_{d,c}, X^k⟫ = Σ_j(−1)^jC(d,j)(c+j)_k = 0` (`k < d`), so `P_{d,c}` is a multiple of the monic orthogonal polynomial of a positive definite form and is real-rooted; positive coefficients put all roots of `Γ_{n,d}` in `(−∞, 0)`. So `Γ_{n,d}` is Szegő-admissible and the ⊠ obstruction of R9 is entirely the theta piece | `GammaPieceIsLaguerre.splits_gammaPiece`, `eval_gammaPiece_pos` |
| R20 | **Degree horizon of a curved phase**: with `σ = √a(1 − i)`, `R_d(e^{iaw²})(y) = σ^d He_d(y/σ)`, so the roots of `R_d(e^{iδw + iaw²})` are `σh − iδ` (`He_d(h) = 0`), imaginary parts `−√a h − δ`. Exactly: stable at degree `n+1` **iff** `√a·h_max(n+1) < δ`; stable whenever `2√(a(n+1)) ≤ δ`; unstable for all large `n` (`h_max²/(n+1) → 4`). With an Euler product (strict Walsh): `√a·h_max ≤ c − θ_S/2` ⇒ `R_{n+1}(e^{icw+iaw²}Π_S(1 − p^{−σ−iw}))` stable. Local Gamma-phase reading: drift `θ'(t)`, curvature `θ''(t)/2`, stable range `≈ (θ'(t) − θ_S/2)²/(2θ''(t))` | `QuadraticPhaseHorizon.quadraticPhase_stable_iff`, `eventually_not_stable_quadraticPhase`, `im_neg_of_isRoot_jensenRev_gaussC_mul_translatedMobiusProduct` |
| R13 | **The degree-three test is vacuous**: on centered cubics `⊞₃` adds `(s,t)`, and every real-rooted centered cubic (`|t| ≤ s^{3/2}`) is a `⊞₃`-product of two double-root (capacity-zero, semicircle-free) cubics | `CubicFirstTest.exists_doubleRoot_factorization` |

## No-go closure for the naive route (source-faithful real-rooted pieces)
- **Killing theorems:** R1 (no Gaussian component at scale `d^{-2}`), R3 (Dirichlet pieces fail
  Turán by the variance), R9 (the theta piece of the canonical ⊠ split fails Turán by the strict
  dispersion), R16–R18 (every positive-mixture factor of `Ξ` — pole pieces, `ζ(σ + iw)` for
  `σ > 1`, `Γ(1/4 + iw/2)` — is Hermite–Biehler unstable for every phase, all in the same
  orientation: their frequency laws have a heavy tail on one side).
- **Positive survivors:** R4/R5 (normalized Euler factors are Hermite–Biehler stable at every
  degree; their symmetrizations are real-rooted), R7 (the shifted Jensen polynomials are
  asymptotically purely semicircular), R8 (Szegő), R15 (exact real-zero horizon `θ_S/2` of
  symmetrized Euler products), R19 (the Gamma piece of the ⊠ split has negative real roots).
- **Insight:** real-rootedness of `J^{d,n}` cannot be inherited from Euler/theta pieces; it must come
  from the Gamma weights overpowering a strictly positive theta dispersion (⊠ picture) or from a
  functional-equation phase pairing (critical-direction ⊞ picture). Both are the sign wall in
  finite free form.

## Capacity landscape
- Degree regime (`d → ∞`, `n = 0`): Gaussian capacity `o(d^{-2})` in the native scale (R1), with
  unboundedly many non-real roots after any backward heat at that scale (R6).
- Shift regime (`n → ∞`, `d` fixed): capacity tends to the full Hermite capacity (R7).
- RH ⇔ capacity `≥ 0` at every `(d, n)` ⇔ infinitely many real-rooted `J_d` (R2).

## Where the route meets the walls
- (i) Criticality is a theorem (R1): any finite free factorization of `J_d` has Hermite capacity
  `o(d^{-2})`.
- Real direction: Euler/Dirichlet data give Appell pieces with positive variance; Turán fails (R3).
- Critical direction: the entire (Möbius-side) Euler factors are stable only after the per-prime
  translation `X ↦ X + iℓ_p/2`; the translations add to `θ(N)/2 → ∞`, and without them Walsh's bound
  drifts to `Im < Σ log p /2`. The ζ-side factors `(1 − q e^{−iℓw})^{-1}` carry poles in the upper
  half-plane. Ξ's own symmetrization phase is the Gamma phase, not a ⊞-product of the prime
  translations.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven (route as a whole: open)
- [ ] 2 → 3  formalized (route as a whole: open)

## Open conjectures (next)
- Local Gamma phase beyond the quadratic model (R20): the full Taylor phase `θ(t + w) − θ(t)`
  (Stirling) and the matching instability of `e^{icw+iaw²}·E_S` beyond the Walsh range.

## Log
- 2026-11-04 — created
- 2026-11-05 — D1–D5, R1–R20 formalized
