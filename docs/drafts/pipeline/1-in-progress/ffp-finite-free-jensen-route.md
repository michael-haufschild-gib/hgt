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
| R21 | **Möbius-mollified finite free RH criterion**: for nonempty finite `S`, `σ > 0`, `c ≥ θ_S/2`: RH ⇔ the reversed Jensen polynomials of `Ξ(w)·e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` have all roots in `Im < 0` for infinitely many `d` (and then for every `d`). Forward: `R_d(Ξ)` real-rooted (LP) ⊞ stable Möbius piece, strict Walsh. Converse: `R_d(F)(d/u) = (d/u)^dΦ_d(u)`, `Φ_d → F` locally uniformly (Tannery), stability puts zeros of `Φ_d` in `Im > 0`, Hurwitz + conjugation symmetry of `Ξ`'s zeros. Generalizes R2; the Möbius side can be attached to `Ξ`, the pole side cannot (R16–R18) | `MollifiedJensenCriterion.riemannHypothesis_iff_frequently_stable_mollified` |
| R22 | **Finite free Hardy theorem** (unconditional): for every `M`, `R_d(Ξ)` has at least `M` distinct real roots for all large `d`. Hardy's tail argument excludes a nonnegative or nonpositive tail of `Ξ`, giving `p_0 < p_1 < ⋯` with `(−1)^jΞ(p_j) > 0`; `Φ_d → Ξ` carries the signs, and each zero `u_j ∈ (p_j, p_{j+1})` of `Φ_d` gives the real root `d/u_j`. Complements R6 (unboundedly many non-real roots after backward heat) | `FiniteFreeHardyTheorem.eventually_le_card_roots_jensenReverse_XiC` |
| R23 | **Bounded imaginary parts decide RH**: for every finite `S` (possibly empty), `σ > 0` and **every** phase `c`: RH ⇔ ∃`K`, for infinitely many `d` all roots of `R_d(Ξ·e^{icw}Π_{p∈S}(1 − p^{−σ−iw}))` have `Im ≤ K`; under RH `K = θ_S/2 − c` works at every degree (Walsh). Converse: Hurwitz with the degree-dependent region `Im u ≥ −K|u|²/d`, via the closed sets `{Im ≥ −ε} ∪ {|u| ≥ R}`. Robust form of R2/R21: real-rootedness and normalization are not needed | `BoundedImaginaryPartsCriterion.riemannHypothesis_iff_frequently_im_le_mollified`, `riemannHypothesis_iff_frequently_im_le` |
| R24 | **Bounded-or-linear dichotomy**: for `F = Ξ·e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` (any finite `S`, any `c`), either RH and every root of `R_d(F)` has `Im ≤ θ_S/2 − c`, or ¬RH and there is `κ > 0` with a root of `Im ≥ κd` for all large `d` (Hurwitz existence: a zero `ρ` of `F` in `Im < 0` attracts zeros `u_d` of `Φ_d`, `Im(d/u_d) ≥ κd`). Hence RH ⇔ for every `ε > 0` the imaginary parts are `≤ εd` along infinitely many `d`: no intermediate growth | `ImaginaryPartDichotomy.exists_linear_im_of_not_riemannHypothesis`, `riemannHypothesis_iff_forall_frequently_im_le_mul` |
| R25 | **Finite free detection of zero-free half-planes**: with `G_σ(w) = ξ(σ + iw)` (zeros `w_ρ = (ρ − σ)/i`, `Im w_ρ = σ − Re ρ`), bounded-above (or `≤ εd` for every `ε`) root imaginary parts of `R_d(G_σ)` along infinitely many `d` imply `ξ ≠ 0` on `Re s > σ`; a zero with `Re ρ > σ` forces roots with `Im ≥ κd` for all large `d`. At `σ = 1/2` this is R23/R24; for `σ ∈ (1/2, 1)` it reads quasi-RH | `ZeroFreeHalfPlaneCriterion.re_le_of_frequently_im_le`, `exists_linear_im_of_xi_zero`, `zeroFree_of_forall_frequently_im_le_mul` |
| R26 | **Finite free zero-free half-plane theorem**: for every `σ`, `ξ ≠ 0` on `Re s > σ` ⇔ every root of every reversed Jensen polynomial of `ξ(σ + i·)` has `Im ≤ 0` ⇔ for some `K` and infinitely many `d` the roots have `Im ≤ K`. **Unconditional at `σ ≥ 1`.** Proof of ⇒: genus-one Hadamard product `Ξ = Ξ(0)ΠE₁(z/a_q)` (corpus), partial products `Π_F E₁((w − iδ)/a_q) = c_F Π_F(1 − w/(a_q+iδ))·e^{wΣ_F 1/a_q}`; Walsh puts the linear part in `Im ≤ 0` (`Im a_q ≥ −δ`), the exponential drifts by `τ_F = −Im Σ_F 1/a_q → 0` (conjugation involution of the zeros); Taylor coefficients converge (iterated derivatives of locally uniform limits) and a closed-set Hurwitz for polynomials of bounded degree gives the limit. ⇐ is R25 | `ZeroFreeHalfPlaneStability.zeroFree_iff_forall_im_le_zero`, `zeroFree_iff_exists_frequently_im_le`, `im_le_zero_of_one_le` |
| R27 | **Strict stability from closed zero-free half-planes; finite free non-vanishing on `Re s = 1`**: if `ξ ≠ 0` on `Re s ≥ σ`, every root of every `R_d(ξ(σ + i·))`, `d ≥ 1`, has `Im < 0`; **unconditional for `σ ≥ 1`**. Mechanism: multiplication by `1 − βw` acts as `q ↦ q − βq'`; with `Im β < 0` and roots of `q` in `Im ≤ 0`, a new root in `Im ≥ 0` must be a multiple root of `q` (Gauss–Lucas via `q'/q = Σ 1/(x − r)`), so `d` reserved zeros strip the root `0` of `X^d` one multiplicity at a time; the resulting strictly stable factor keeps a fixed margin through Walsh, the Hadamard partial products and the polynomial Hurwitz limit | `ZeroFreeStrictStability.im_neg_of_one_le`, `im_neg_of_closed_zeroFree` |
| R28 | **Strict half-plane theorem right of the critical line**: for `σ > 1/2`, `ξ ≠ 0` on the **open** half-plane `Re s > σ` ⇔ every root of every `R_d(ξ(σ + i·))`, `d ≥ 1`, has `Im < 0`. A zero on the line `Re s = σ` does not break strictness: its reflection `1 − ρ̄` lies strictly left, so (line conjugation is injective) infinitely many zeros are strictly placed and serve as the reserved factors of R27. At `σ = 1/2` strictness fails under RH (roots real) | `ZeroFreeStrictStability.zeroFree_iff_forall_im_neg`, `im_neg_of_zeroFree`, `infinite_strict_of_weak` |
| R29 | **Hurwitz stability of the real Jensen polynomials of `ξ`**: `J_d(ξ; σ)(t) = Σ_{k≤d} C(d,k) ξ^{(k)}(σ) t^k` satisfies `R_d(ξ(σ + i·))(i/t) = i^d t^{−d} J_d(ξ; σ)(t)` with `Im(i/t) = Re t/|t|²`. Hence: **for every `σ ≥ 1` and `d ≥ 1` all roots of `J_d(ξ; σ)` have `Re t < 0` (unconditional)**; for `σ > 1/2`, `ξ ≠ 0` on `Re s > σ` ⇔ every `J_d(ξ; σ)` is Hurwitz stable; for every `σ`, weak Hurwitz stability (`Re t ≤ 0`) of all `J_d(ξ; σ)` forces the zero-free half-plane | `RealJensenHurwitzStability.re_neg_of_isRoot_xiRealJensen_of_one_le`, `zeroFree_iff_xiRealJensen_hurwitz`, `zeroFree_of_forall_re_nonpos` |
| R30 | **Finite free Hermite–Biehler theorem for genus-one products**: for any family `z_i ≠ 0` with `Σ 1/|z_i|² < ∞`, `Im z_i ≥ 0`, summable `Im(1/z_i)` and drift `Im a + Σ Im(1/z_i) ≥ 0`, every reversed Jensen polynomial of `e^{aw}Π E₁(w/z_i)` has roots in `Im ≤ 0` (countability of the index follows from square-summability). Corollary for every entire `f` of order ≤ 1 via the corpus Hadamard factorization `f = e^{az+b}Π E₁(z/z_q)`. Finite free form of the Pólya–Levin class; R26 is the shifted case of `Ξ` | `FiniteFreePolyaClass.im_le_zero_of_isRoot_jensenRev_polya`, `im_le_zero_of_isRoot_jensenRev_genusOne` |
| R31 | **Canonical zero-piece realization (the route in zero form)**: unconditionally, along an exhaustion `G_n` of the zeros closed under `a ↦ −a` (the reflection makes `Σ_G 1/a_q = 0`, so no translation survives), `R_d(Ξ)/Ξ(0) = lim_n ⊞_{q∈G_n} R_d(1 − w/a_q)` coefficientwise, with rank-one pieces `R_d(1 − w/a) = X^{d−1}(X − d/a)`. All these pieces are real-rooted **iff RH** | `ZeroPieceRealization.exists_zeroPiece_realization`, `riemannHypothesis_iff_zeroPieces_realRooted` |
| R32 | **Hurwitz with multiplicity by deflation; concentration**: writing `Φ_d(u) = Π_x(1 − (x/d)u)` over the roots of `R_d`, a factorization `g = Π_T(1 − u/z_i)·G` splits the rescaled roots as `A_d + B_d` with `Σ_{A_d} v → Σ_T 1/z_i` (uniform convergence on a large circle, then the maximum principle). The first moment `Σ_x x/d = −f_1` then gives: if all roots have `Im ≤ 0`, at most `|T| + (Im f_1 + Σ_T Im(1/z_i) + ε)d/μ` roots have `Im x ≤ −μ` | `HurwitzDeflation.exists_multiset_deflation`, `eventually_card_filter_le`, `tendsto_card_filter_div` |
| R33 | **Classification of the finite free class of genus one**: all `R_d(e^{aw}Π E₁(w/z_i))` have roots in `Im ≤ 0` **iff** all `Im z_i ≥ 0` and the drift `D = Im a + Σ Im(1/z_i) ≥ 0` (converse of R30). For zeros in `Im ≥ 0`: every root has `Im x ≤ −D`, sharply (a root with `Im x > −D − μ` for all large `d`); at `D = 0` almost all roots converge to the real axis | `GenusOneStabilityClassification.jensenRev_polya_stable_iff`, `im_le_neg_drift`, `eventually_exists_root_im_gt_neg_drift`, `tendsto_card_filter_div_polya` |
| R34 | **`ξ` sits on the boundary of finite free stability**: the functional equation gives drift exactly `0` on every line (`Re ξ'/ξ(σ) = Σ_ρ Re 1/(σ−ρ)`). **No margin**: for every `σ`, `μ > 0` and large `d`, `R_d(ξ(σ+i·))` has a root with `Im x > −μ`. At `σ ≥ 1` (unconditional) the roots lie in `Im x < 0` and the proportion with `Im x ≤ −μ` tends to `0`. **Critical phase**: `e^{c(s−σ)}ξ(s)` is stable on `Re s = σ` iff `ξ ≠ 0` on `Re s > σ` and `c ≥ 0` | `StabilityBoundaryOfXi.eventually_exists_root_im_gt_xi`, `tendsto_card_filter_div_xi_of_one_le`, `jensenRev_phase_xi_stable_iff` |
| R35 | **First-order law of the moments**: for `σ ≥ 1/2`, `c_k = ξ^{(k)}(σ) = ∫Φ(x)x^k e^{(σ−1/2)x}dx ≥ 0`, and `m_d(t) = Σ C(d,k)t^{d−k}c_k = E(t+V)^d` satisfies `(1/d) log m_d(θℓ_d) − log ℓ_d → log(1+θ)`, `ℓ_d = ½ log d` (Cauchy estimate at the saddle `r = d/((1+θ)ℓ_d)` with the Gamma cap, restriction of the integral to `[ℓ−log ℓ, ℓ−log ℓ+1]` with the first cusp term of `Φ`). Log-convexity of `m_d` in `log t` upgrades this to `ℓ_{d+1} m_d(θℓ_{d+1})/m_{d+1}(θℓ_{d+1}) → 1/(1+θ)` | `JensenMassConvexity.tendsto_ratio_of_tendsto_log`, `XiMomentsOnALine.tendsto_log_jensenMass`, `tendsto_cauchy_ratio` |
| R36 | **The Cauchy limit law of the Jensen roots**: with `G_d(z) = (1/d)Σ_x 1/(z − x/ℓ_d)`, unconditionally for `σ ≥ 1/2`, `θ > 0`: `G_d(iθ) → 1/(iθ+i)`. If all roots lie in `Im x ≤ 0` (always for `σ ≥ 1`, RH at `σ = 1/2`), `G_d(z) → 1/(z+i)` on the upper half-plane: the Cauchy transform of the standard Cauchy law. The bulk at scale `½ log d` is universal, comes from the Gamma factor alone, does not depend on `σ`, and cannot see the zeros | `CauchyLimitLaw.tendsto_jensenCauchy_imag`, `tendsto_jensenCauchy_of_one_le`, `tendsto_jensenCauchy_of_zeroFree` |
| R37 | **Bulk hyperbolicity, unconditional**: for every `ε > 0` the proportion of roots of `R_d(Ξ)` with `|Im x| ≥ ε ½ log d` tends to `0`; for `σ ≥ 1/2` the proportion of roots of `R_d(ξ(σ+i·))` with `Im x ≥ ε ½ log d` tends to `0`. Mechanism: the complex moment formula `R_d(w) = E(w+iV)^d` gives `|R_d(ℓz)| ≤ ℓ^d|z+i|^d e^{o(d)}` uniformly on circles in `Im z > 0` (`|ℓz+iv| ≤ ℓ(|z+i|−1) + max(|v|,ℓ)`), sharp at `z = iθ` by R35; `log|z+i|` is harmonic, so a Blaschke–maximum-principle Jensen inequality on discs around `iθ` gives `o(d)` roots in them. The discs exhaust `Im z > 0`; the same inequality bounds the far roots; `R_d(−x) = (−1)^d R_d(x)` gives the lower half-plane | `MultisetJensenInequality.multiset_prod_max_le`, `BulkHyperbolicity.tendsto_card_im_ge_div`, `tendsto_card_abs_im_ge_div_xiSeries` |
| R38 | **Almost all Jensen roots of `Ξ` are real and simple, unconditionally**: for every `η > 0` and large `d`, `R_d(Ξ)` has at least `(1−η)d` distinct real roots; the proportion of non-real roots with multiplicity tends to `0`. Mechanism: on the real axis `R_d = 2 Re E_d` with `E_d(w) = ∫₀^∞Φ(v)(w+iv)^d dv`. For the one-sided transform the bound `|E_d(ℓζ)| ≤ ℓ^d|ζ+i|^d e^{o(d)}` persists on `Im ζ ≥ −1/2`, so the Jensen discs of R37 may cross the real axis, and `E_d` has only `o(d)` roots in `Im ≥ 0`. The winding count `Z₋ − Z₊ ≤ #{real zeros of Re E}` (counting form of Hermite–Biehler) gives the real roots | `HermiteBiehlerCounting.exists_finset_re_eval_eq_zero`, `KernelJensenRoots.HyperbolicKernel.eventually_card_im_nonneg_halfJensen_le`, `AlmostAllJensenRootsAreReal.eventually_exists_real_roots_xiSeries`, `tendsto_card_nonreal_roots_div` |
| R39 | **The non-real count is monotone**: `N_d = #{non-real roots of R_d(Ξ)}` is nondecreasing in `d` (Rolle on `R_{d+1}' = (d+1)R_d`). With R38, `N_d` is nondecreasing and `o(d)` | `NonRealRootCount.card_nonreal_roots_le_succ` |
| R40 | **The real roots of `R_d(Ξ)` follow the Cauchy law, unconditionally**: for `Im w > 0`, `(1/d)Σ_{y real} 1/(w − y) → 1/(w + i)`, over the real rescaled roots `y = x/ℓ_d`. For `σ ≥ 1/2` the same limit holds for the rescaled roots outside a disc around `iθ` containing `w`. Mechanism: reflect the roots inside the disc and divide by `(z+i)^d`; the quotient has no zero, `|Q_d| ≤ e^{o(d)}` by the maximum principle and `|Q_d(iθ)| ≥ e^{−o(d)}` by R35, so Borel–Carathéodory and Cauchy's estimate make `(1/d)Q_d'/Q_d → 0` | `RealRootsCauchyLaw.tendsto_exterior_transform`, `tendsto_real_jensenCauchy` |
| R41 | **R38 for every hyperbolic kernel, and the bulk is blind**: R38 holds for every continuous even `g` with `0 ≤ g ≤ Φ` and `g(v) ≥ exp(−Ae^{2v})` for large `v`, in particular for `g = Φe^{−τv²}`. So for every `τ > 0`, `H_{−τ}` has non-real zeros (Newman), yet the number `N_d` of non-real roots of `R_d(H_{−τ})` satisfies `N_d/d → 0` and `N_d → ∞`. Hence "almost all Jensen roots are real" cannot imply RH, and no argument using only the size and positivity of the kernel can | `KernelJensenRoots.HyperbolicKernel.eventually_exists_real_roots`, `tendsto_card_nonreal_roots_div`, `BulkBlindness.bulk_blind_riemannHeat_neg` |
| R42 | **The half transform is not a Hermite–Biehler half**: `K(w) = ∫₀^∞Φ e^{wu}du`, with `Ξ(u) = K(iu) + K(−iu)`, has infinitely many zeros, all in `Re w > 0`. So for every `M` and large `d`, `E_d` has at least `M` roots in `Im > 0`: the splitting `R_d(Ξ) = 2 Re E_d` is not Hermite–Biehler. Mechanism: finitely many zeros would make `K` of exponential type on the real axis by the order-one Hadamard factorization, while `K(σ) + K(−σ) = ξ(1/2 + σ)` is superexponential | `HalfTransformInstability.thetaHalfLaplace_zeros_infinite`, `re_pos_of_thetaHalfLaplace_eq_zero`, `eventually_le_card_upper_roots_halfJensen` |
| R43 | **The Cauchy law for every hyperbolic kernel**: for `Im w > 0`, `(1/d)Σ_{y real} 1/(w − y) → 1/(w + i)` over the real rescaled roots of `R_d(x) = ∫g(v)(x+iv)^d dv`. In particular `R_d(H_{−τ})`, `τ > 0`, has exactly the bulk of `R_d(Ξ)`, although `H_{−τ}` has non-real zeros: the limit law is blind too. Abstract core: a bound on circles around `iθ₀` and at the centre, with error `o(d)`, determine both the number of roots in the disc and the Cauchy transform outside it | `KernelCauchyLaw.tendsto_card_near_of_data`, `tendsto_exterior_of_data`, `HyperbolicKernel.tendsto_real_cauchy`, `tendsto_real_cauchy_riemannHeat_neg` |
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
  symmetrized Euler products), R19 (the Gamma piece of the ⊠ split has negative real roots),
  R20 (exact degree window of a curved phase), R21 (Möbius mollification preserves the finite free
  RH criterion), R22 (unboundedly many real roots of `R_d(Ξ)`, unconditionally).
- **Insight:** real-rootedness of `J^{d,n}` cannot be inherited from Euler/theta pieces; it must come
  from the Gamma weights overpowering a strictly positive theta dispersion (⊠ picture) or from a
  functional-equation phase pairing (critical-direction ⊞ picture). Both are the sign wall in
  finite free form.
- **Insight (completion stabilizes):** `ζ(σ + iw)` (`σ > 1`) and `Γ(1/4 + iw/2)` are each
  Hermite–Biehler unstable for every phase (R17, R18), yet the completed `ξ(σ + iw)` is strictly
  stable for every `σ ≥ 1` at every degree (R27). Stability is a property of the completed function
  (its Hadamard product), not of the Euler/Gamma factorization; on `Re s = σ` it is exactly the
  zero-free half-plane (R25–R27), and at `σ = 1/2` exactly RH.
- **Positive survivors of the bulk analysis:** R33 (classification of the genus-one class by the drift), R34
  (`ξ` has drift exactly `0`: critical phase `c = 0`, no margin), R36 and R40 (Cauchy law at scale `½ log d`),
  R37 and R38 (almost all roots real and simple, unconditionally), R39 (monotone `N_d`).
- **Insight (the bulk is blind):** R41. The bulk theorems use only the evenness, positivity and size of the
  kernel, and hold for `H_{−τ}`, which has non-real zeros (R41, R43). RH is `N_d = 0`, a statement about the `o(d)` outliers
  `x ≈ d/a_q`, which are the zeros themselves: real-rootedness of `J_d` cannot be read off any bulk statistic.

## Capacity landscape
- Degree regime (`d → ∞`, `n = 0`): Gaussian capacity `o(d^{-2})` in the native scale (R1), with
  unboundedly many non-real roots after any backward heat at that scale (R6).
- Shift regime (`n → ∞`, `d` fixed): capacity tends to the full Hermite capacity (R7).
- RH ⇔ capacity `≥ 0` at every `(d, n)` ⇔ infinitely many real-rooted `J_d` (R2) ⇔ bounded
  imaginary parts of the roots of `R_d(Ξ·M)` along infinitely many `d`, any Möbius mollifier `M`
  (R21, R23); imaginary parts are either `O(1)` or `≍ d`, never in between (R24).
- Vertical lines `Re s = σ`: `R_d(ξ(σ + i·))` weakly Hermite–Biehler stable at every degree ⇔ no
  zero right of the line (R25, R26); for `σ > 1/2` weak ⇔ strict (R27, R28); unconditional for
  `σ ≥ 1`, RH at `σ = 1/2`. Equivalently: the real Jensen polynomials `Σ C(d,k)ξ^{(k)}(σ)t^k` are
  Hurwitz stable exactly right of all zeros (R29).

- Stability is critical and the bulk is blind: on every line the drift of `ξ` is exactly `0`, so there
  is no margin (R34); the roots at scale `½ log d` follow a universal Cauchy law from Stirling alone (R36),
  and almost all of them are real and simple, unconditionally (R37, R38). RH is decided by the `o(d)`
  outliers `x ≈ d/a_q`, not by any bulk statistic of the Jensen polynomials.

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
- **Size of the non-real count.** `N_d = #{non-real roots of R_d(Ξ)}` is nondecreasing and `o(d)` (R38, R39).
  Heuristics. The winding of `E_d` cannot do better than `d/log d`: on the real axis the endpoint `v = 0` of
  `E_d` overtakes the saddle at `|x| ≈ ℓ_d²`, and the bulk zeros of `E_d` cross into `Im > 0` there. The
  full-line contour `R_d(x) = i^d d!/(2πi) ∮ e^{−ixw} ξ(1/2 + w) w^{−d−1} dw` has no endpoint and should give
  two conjugate saddles for `|x| ≪ √d log d`, with phase rate `Re w*(x) ≈ dℓ/(x² + ℓ²)`, hence
  `N_d ≲ d^{1/2+ε}`, sharp for `H_{−τ}`. Past that height the roots are the zeros of `Ξ` up to `√d/log d`, so
  real-rootedness of `R_d(Ξ)` should be RH up to about that height.
- Other completed L-functions: R30 gives the forward direction for any genus-one entire function;
  the converse (Hurwitz, R25) is general too — instantiate for completed Dirichlet L-functions once
  their order-one bounds are in the corpus.
- (Superseded) local Gamma-phase models (R20): stability is a property of the completed function
  (R27); the instabilities of the factors (R16–R18) are exactly their poles.


## Log
- 2026-11-04 — created
- 2026-11-05 — D1–D5, R1–R43 formalized
