# Moving-cusp reflection turns Euler deletion into a signed-totient source — Lean certificate

- **Paper card:** `theta-prime-deletion-moving-cusp-dual-source.md`
- **Lean modules (umbrella `GaloisForLFunctions.RHTower`):**
  - `ThetaFiniteEulerMovingCuspDuality` (existing): abstract finite-list reflection.
  - `ThetaMovingCuspSignedTotientInverse` (existing): `A ⋆ φ = δ`, `φ = μ ⋆ id`.
  - `ThetaMovingCuspDualSource`: log-shift series calculus (Gaussian-tailed sources, termwise differentiation, Tannery), `R_S`, (1), (2), `R_∞`, (3) with every derivative, (5), `R_∞/k → 1`, one-sign obstruction.
  - `ThetaMovingCuspTotientReconstruction`: composition of log-shift series by Dirichlet convolution, seed atom `h`, (4), (4a), (4b) and its limit, second sign proof.
  - `ThetaMovingCuspSpectralShear`: Gaussian bound on the positive ray, entire head transform, Landau sign changes at the negative cusp, spectral shear orders, multiplier, wall, product = seed transform.
  - `ThetaMovingCuspWeightedEscape`: (6), positive-tail integrability iff `c < 2`, `R_∞ ∉ L²((−∞,0))`, divergence of the normalized terminal energies (7).
- **Verification (2026-10-04):** targeted `lake build --old` of each new module; final `lake env lean` audit of each source with empty output; `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for all 144 declarations of the six modules; no `sorry`, no axiom, no heartbeat options.
- **Hypotheses:** only the card's quantifiers (finite prime sets, prime exhaustions, compact windows, Mellin parameters in the stated half-planes, `0 < c < 2`, points of the critical strip).

Dictionary: `k = thetaCuspFullSource`; `k_S = thetaPrimeDeletion S k`; `R_S = movingCuspSource S k`; `R_∞ = movingCuspDualLimit`; `h = thetaSeedAtom`; `A = signedTotientAF`; `φ = eulerTotientAF`; `A_S = finiteSignedTotient S`; `T_φ f = logShiftSeries totientAtomWeight f`; `F(w)/ζ(w−1/2) = movingCuspDualTransform`; `ζ(w−1/2)/ζ(w+1/2) = totientReconstructionMultiplier`; `G = thetaAtomMellinFactor`.

| Card item | Lean theorem |
|-|-|
| **(1)** `R_S(u) = μ(P)√P k_S(−log P−u)` | `movingCuspSource_eq_moebius_mul_deletion`, `movingCuspSource_eq_neg_one_pow_mul_deletion` |
| **(1)** `= Σ_{e|P} μ(e)√e k(u+log e) = ∏(1−√p T_{log p})k` | `movingCuspSource_eq_sum_divisors`, `movingCuspSource_insert` |
| **(2)** `∫e^{wu}R_S = F(w)∏(1−p^{1/2−w})`, all `w` | `integral_cexp_mul_movingCuspSource_theta`, `integrable_cexp_mul_movingCuspSource_theta`, `integral_cexp_mul_movingCuspSource` |
| **(2)** reflected form `μ(P)P^{1/2−w}F(−w)∏(1−p^{−1/2+w})` | `XiC_mul_prod_one_sub_eq_reflected` |
| **(3)** `R_∞` absolutely convergent, Gaussian majorant | `summable_movingCuspDualLimit`, `GaussianLogTail.exists_majorant` |
| **(3)** `R_S → R_∞` locally uniformly with every derivative; `R_∞` smooth | `PrimeExhaustion.tendstoUniformlyOn_iteratedDeriv_movingCuspSource`, `iteratedDeriv_movingCuspDualLimit`, `contDiff_movingCuspDualLimit` |
| **(3)** `√P k_S(−log P−u) − μ(P)R_∞(u) → 0` locally uniformly | `PrimeExhaustion.tendstoUniformlyOn_sqrt_mul_deletion_sub` |
| **(4)** `R_∞ = Σ A(m) m^{−1/2} h(u+log m)`, `A(m) = Σ_{e|m}μ(e)e = ∏_{p|m}(1−p)` | `movingCuspDualLimit_eq_signedTotientAtoms`, `movingCuspDualLimit_eq_tsum_signedTotientAF_mul_atom`, `signedTotientAF_apply`, `signedTotientAF_eq_prod_primeFactors` |
| **(4a)** `A ⋆ φ = δ`; `h(u) = Σ φ(n)n^{−1/2}R_∞(u+log n)` | `signedTotientAF_mul_eulerTotientAF`, `eulerTotientAF_apply`, `thetaSeedAtom_eq_totient_reconstruction` |
| **(4b)** `A_S(m) = ∏_{p∈S,p|m}(1−p)`, `R_S = Σ A_S(m)m^{−1/2}h(u+log m)` | `finiteSignedTotient_eq_prod`, `movingCuspSource_eq_finiteSignedTotientAtoms` |
| **(4b)** `T_φR_S(u) = Σ_{(m,P)=1} √m h(u+log m)` and `→ h` locally uniformly | `logShiftSeries_totient_movingCuspSource`, `eulerTotientAF_mul_finiteSignedTotientAF`, `PrimeExhaustion.tendstoUniformlyOn_totient_movingCuspSource` |
| **(5)** `∫e^{wu}R_∞ = F(w)/ζ(w−1/2)`, `Re w > 3/2`, absolute | `integral_cexp_mul_movingCuspDualLimit` |
| reconstruction multiplier `ζ(w−1/2)/ζ(w+1/2)` | `integral_seed_eq_multiplier_mul_dual` |
| spectral shear: dual transform order `+m` at `ρ−1/2`, `−m` at `ρ+1/2` | `meromorphicOrderAt_movingCuspDualTransform_sub_half`, `meromorphicOrderAt_movingCuspDualTransform_add_half` (`meromorphicOrderAt_xi_eq_riemannZeta`, `riemannZeta_ne_zero_of_neg_one_lt_re_neg`) |
| multiplier has the opposite pole and zero | `meromorphicOrderAt_totientReconstructionMultiplier` |
| product = zero-free seed transform in the open Xi strip | `movingCuspDualTransform_mul_multiplier_eq_seed`, `meromorphicOrderAt_movingCuspDualTransform_mul_multiplier` |
| wall `w = 3/2`: simple zero of `1/ζ(w−1/2)`, simple pole of the multiplier | `meromorphicOrderAt_wall` |
| `R_∞/k → 1`, `R_∞ > 0` on a far positive ray | `tendsto_movingCuspDualLimit_div_thetaCuspFullSource`, `eventually_movingCuspDualLimit_pos` |
| `R_∞` not nonnegative (Fatou/zeta-pole proof; totient proof) | `not_forall_movingCuspDualLimit_nonneg`, `not_forall_movingCuspDualLimit_nonneg'` |
| both signs arbitrarily far into the negative cusp (Landau) | `movingCuspDualLimit_takes_both_signs`, `movingCuspDualLimit_not_eventually_signed` |
| **(6)** `k(−log P−u)^{−c/P²} → exp(cπe^{2u})`; moving density converges | `tendsto_thetaCuspFullSource_moving_rpow`, `PrimeExhaustion.tendsto_moving_density` |
| positive tail of the limit density integrable iff `c < 2` | `integrableOn_movingCuspDualLimit_sq_mul_exp_iff` |
| **(7)** `R_∞ ∉ L²((−∞,0))` | `not_integrableOn_movingCuspDualLimit_sq_Iio` |
| **(7)** `P‖k_S‖²_{H_{c/P²}}` finite and `→ +∞` for every `0 < c < 2` | `PrimeExhaustion.tendsto_moving_weighted_energy` |

Proof-route notes:
- Cofinal limits are proved through a general log-shift series calculus: weights with `|a_n| ≤ n^K` against sources that are bounded with a right Gaussian tail. This covers convergence, smoothness and Tannery stability under pointwise convergence of the weights. All derivatives of `k` and the seed `h` are in this class.
- (4), (4a) and (4b) use one composition law: two log-shift series compose by Dirichlet convolution of their weights. Absolute summability comes from the fibre bound `d(m) ≤ m`.
- The sign-change theorem at the negative cusp applies the corpus Landau lemma for a countable closed singular set to `g(L) = ±R_∞(−L)e^{−L/4}`. The quarter shift aligns the thresholds with the lemma.
- (7a) uses an analytic continuation of `ζ(w−1/2)·ℒR_∞(w) = F(w)` across `Re w > 0` minus `{3/2}`, under the putative `L²` hypothesis, evaluated at `ρ+1/2`.
