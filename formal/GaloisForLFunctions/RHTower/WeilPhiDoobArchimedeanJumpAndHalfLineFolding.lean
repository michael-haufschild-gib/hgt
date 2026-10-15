import GaloisForLFunctions.RHTower.WeilPhiDoobGroundStateCancellationAndShortSupportNoGo
import GaloisForLFunctions.RHTower.RiemannKernelSpectralLocalization

/-!
# Exact Archimedean Doob Jump Cancellation (`markovArchRe k_{Φv} - mixedPhiArchRe (Φ v²) = E_arch^Doob(v) ≥ 0`), Pure-Dirichlet Biane–Pitman–Yor Criteria for RH, and Half-Line `(0, ∞)` Odd-Sector Folding

Building on `WeilPhiDoobGroundStateCancellationAndShortSupportNoGo` and
`RiemannKernelSpectralLocalization`, this module completes the archimedean ground-state Doob
cancellation and establishes the pure-Dirichlet representation of `markovEnergy (Φ v)`:

1. **Section 1 (`L¹`, `L²`, and Archimedean Spectral Integrability of `riemannPhiKernel` and the
   General Bochner Lévy Representation):**
   - We prove `integrable_riemannKernelReal`, `integrable_riemannKernelReal_sq`,
     `norm_phiFourier_sq_mul_one_add_sq_le`, `integrable_archSymbol_mul_normSq_fourier_riemannPhiKernel`,
     and `integrable_paperFT_riemannPhiKernel_sq_mul_gammaBracket`.
   - For any continuous `g ∈ L¹(ℝ) ∩ L²(ℝ)` whose paper Fourier transform satisfies
     `Integrable (fun r => ‖paperFT g r‖² * EF.gammaBracket r)`, we establish the Bochner-integral
     Lévy–Khintchine formula (`integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner`):
     `(1 / (2 * π)) ∫ ‖paperFT g r‖² * gammaBracket r dr = gammaBracket 0 * ∫ g² + ∫_{t > 0} ω(t) (∫ (g(u) - g(u+t))² du) dt`,
     together with `IntegrableOn` of the jump integrand on `Ioi 0`.

2. **Section 2 (Polarized Mixed Archimedean Lévy Representation for `mixedPhiArchRe H`):**
   - Applying `integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner` to `g₊ = Φ + H` and
     `g₋ = Φ - H` for any `H ∈ C²_c(ℝ)` and polarizing (`‖z₁ + z₂‖² - ‖z₁ - z₂‖² = 4 Re(z₁ z̄₂)`)
     yields the exact time-domain Bochner Lévy representation (`mixedPhiArchRe_eq_bochner_levy`):
     `mixedPhiArchRe H = EF.gammaBracket 0 * ∫ Φ(u) H(u) du + ∫_{t > 0} ω(t) (∫ (Φ(u) - Φ(u+t))(H(u) - H(u+t)) du) dt`.

3. **Section 3 (Exact Archimedean Doob Ground-State Cancellation and the Pure-Dirichlet
   Decomposition of `markovEnergy (Φ v)`):**
   - Specializing `mixedPhiArchRe_eq_bochner_levy` to `H = Φ v²` cancels the negative local term
     `EF.gammaBracket 0 * ∫ (Φ v)²` **identically** against `markovArchRe k_{Φv}` and combines the
     two shift integrals via the pointwise identity
     `(Φv(u) - Φv(u+t))² - (Φ(u) - Φ(u+t))(Φv²(u) - Φv²(u+t)) = Φ(u)Φ(u+t)(v(u) - v(u+t))²`:
     `markovArchRe k_{Φv} - mixedPhiArchRe (Φ v²) = phiDoobArchJumpEnergy v ≥ 0`
     (`markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy`, `phiDoobArchJumpEnergy_nonneg`).
   - Substituting into `phiDoob_markovEnergy_groundState_cancellation` yields the **Complete
     Pure-Dirichlet Doob Ground-State Identity** (`phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass`):
     `markovEnergy (Φ v) = phiDoobArchJumpEnergy v + (∑' n, ∫ phiDoobPrimeJump v n) - phiDoobCoshMass (v²)`,
     and the unconditional pure-Dirichlet Poincaré criteria for `RiemannHypothesis`
     (`riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`,
     `riemannHypothesis_iff_forall_phiDoobCoshMass_zero_dirichlet_poincare`).

4. **Section 4 (Exact Half-Line `(0, ∞)` Folding of Odd Doob Tests and Origin-Crossing Reflected
   Sum-Square Positivity):**
   - For any odd `v ∈ C²_c(ℝ)` and any shift `t > 0`, we fold the full-line Doob jump integral
     onto the positive half-line `(0, ∞)` (`integral_phiDoobArchShiftJump_eq_halfLine_of_odd`):
     `∫_ℝ Φ(x)Φ(x+t)(v(x) - v(x+t))² dx = 2 ∫_{x > 0} Φ(x)Φ(x+t)(v(x) - v(x+t))² dx + ∫_{x ∈ (0, t)} Φ(x)Φ(t-x)(v(x) + v(t-x))² dx`,
     where the origin-crossing collar `(0, t)` contributes the nonnegative reflected sum square
     `∫_{x ∈ (0, t)} Φ(x)Φ(t-x)(v(x) + v(t-x))² dx ≥ 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate FourierTransform ContDiff
open Zeta23
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: `L¹`, `L²`, and Archimedean Spectral Integrability of `riemannPhiKernel` and the General Bochner Lévy Representation -/

/-- `riemannKernelReal` is integrable on `ℝ`. -/
theorem integrable_riemannKernelReal : Integrable riemannKernelReal := by
  have h := integrable_riemannPhiKernel.re
  refine h.congr (Eventually.of_forall fun x => ?_)
  change (riemannPhiKernel x).re = riemannKernelReal x
  rw [riemannPhiKernel_eq_ofReal, Complex.ofReal_re]

/-- `riemannKernelReal` is square-integrable on `ℝ`. -/
theorem integrable_riemannKernelReal_sq :
    Integrable (fun x : ℝ => riemannKernelReal x ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  refine (integrable_riemannKernelReal.const_mul C).mono'
    (continuous_riemannKernelReal.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  change ‖riemannKernelReal x ^ 2‖ ≤ C * riemannKernelReal x
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  have hC1 : riemannKernelReal x ≤ C := by
    have hexp : Real.exp (-(4 * |x|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x])
    exact (hC x).trans (mul_le_of_le_one_right hC0 hexp)
  exact mul_le_mul_of_nonneg_right hC1 (riemannKernelReal_pos x).le

/-- Quadratic spectral decay bound `‖𝓕 riemannPhiKernel ξ‖ ^ 2 * (1 + ξ ^ 2) ≤ K₁` from the
first derivative of `Φ`. -/
theorem norm_phiFourier_sq_mul_one_add_sq_le :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ ξ : ℝ, ‖𝓕 riemannPhiKernel ξ‖ ^ 2 * (1 + ξ ^ 2) ≤ K₁ := by
  set A0 := ∫ u, ‖riemannPhiKernel u‖
  set A1 := ∫ u, ‖riemannKernelDeriv 1 u‖
  refine ⟨A0 ^ 2 + (A1 / (2 * π)) ^ 2, by positivity, fun ξ => ?_⟩
  have h0 : ‖phiFourier ξ‖ ≤ A0 := norm_fourier_le_integral_norm' _ ξ
  have h1 : |ξ| * ‖phiFourier ξ‖ ≤ A1 / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have := abs_mul_norm_phiFourier_le ξ
    linarith
  have hn0 := norm_nonneg (phiFourier ξ)
  have e : ‖phiFourier ξ‖ ^ 2 * (1 + ξ ^ 2) =
      ‖phiFourier ξ‖ ^ 2 + (|ξ| * ‖phiFourier ξ‖) ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  rw [show 𝓕 riemannPhiKernel ξ = phiFourier ξ from rfl, e]
  have ha : 0 ≤ |ξ| * ‖phiFourier ξ‖ := by positivity
  nlinarith [pow_le_pow_left₀ hn0 h0 2, pow_le_pow_left₀ ha h1 2]

/-- The archimedean Fourier energy `ξ ↦ gammaHardyPhaseRate (2 * π * ξ) * ‖𝓕 riemannPhiKernel ξ‖²`
is integrable on `ℝ`. -/
theorem integrable_archSymbol_mul_normSq_fourier_riemannPhiKernel :
    Integrable
      (fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 riemannPhiKernel ξ‖ ^ 2) := by
  obtain ⟨K₁, hK₁, h1⟩ := norm_phiFourier_sq_mul_one_add_sq_le
  obtain ⟨K₂, hK₂, hmu⟩ := EF.abs_mu_le_of_gammaFacts gammaFacts
  have hgamma (r : ℝ) : gammaHardyPhaseRate r = Real.pi * mu r := by
    have hgb := gammaBracket_eq_two_mul_gammaHardyPhaseRate r
    have hmu_eq : EF.gammaBracket r = 2 * Real.pi * mu r := by
      simp only [EF.gammaBracket, mu]
      field_simp
    linarith
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 riemannPhiKernel ξ‖ ^ 2)
      volume := by
    have hcont_mu : Continuous (fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ)) := by
      simp_rw [hgamma]
      exact continuous_const.mul
        (gammaFacts.smooth.continuous.comp (continuous_const.mul continuous_id))
    exact (hcont_mu.mul (continuous_phiFourier.norm.pow 2)).aestronglyMeasurable
  set C := 2 * Real.pi * (2 * Real.pi) ^ (1 / 2 : ℝ) * K₁ * K₂
  have hdom : Integrable (fun ξ : ℝ => C * (1 + ‖ξ‖) ^ (-(3 / 2) : ℝ)) :=
    (integrable_one_add_norm (by rw [Module.finrank_self]; norm_num)).const_mul C
  refine hdom.mono' hmeas (Eventually.of_forall fun ξ => ?_)
  change ‖gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 riemannPhiKernel ξ‖ ^ 2‖ ≤
    C * (1 + ‖ξ‖) ^ (-(3 / 2) : ℝ)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖𝓕 riemannPhiKernel ξ‖), hgamma, abs_mul,
    abs_of_pos Real.pi_pos]
  have hb : 0 < 1 + |ξ| := by linarith [abs_nonneg ξ]
  have h2π : 1 + |2 * Real.pi * ξ| ≤ 2 * Real.pi * (1 + |ξ|) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three, abs_nonneg ξ]
  have hmu_bound : |mu (2 * Real.pi * ξ)| ≤
      K₂ * (2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (1 / 2 : ℝ) := by
    calc |mu (2 * Real.pi * ξ)|
        ≤ K₂ * (1 + |2 * Real.pi * ξ|) ^ (1 / 2 : ℝ) := hmu (2 * Real.pi * ξ)
      _ ≤ K₂ * (2 * Real.pi * (1 + |ξ|)) ^ (1 / 2 : ℝ) := by gcongr
      _ = K₂ * (2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by positivity) hb.le]
          ring
  have hsq : (1 + |ξ|) ^ (2 : ℝ) ≤ 2 * (1 + ξ ^ 2) := by
    rw [Real.rpow_two]; nlinarith [sq_abs ξ, sq_nonneg (1 - |ξ|)]
  have key : (1 + |ξ|) ^ (1 / 2 : ℝ) ≤
      2 * (1 + ξ ^ 2) * (1 + |ξ|) ^ (-(3 / 2) : ℝ) := by
    rw [show (1 / 2 : ℝ) = 2 + (-(3 / 2)) by norm_num, Real.rpow_add hb]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hb.le _)
  calc Real.pi * |mu (2 * Real.pi * ξ)| * ‖𝓕 riemannPhiKernel ξ‖ ^ 2
      ≤ Real.pi * (K₂ * (2 * Real.pi) ^ (1 / 2 : ℝ) * (1 + |ξ|) ^ (1 / 2 : ℝ)) *
          ‖𝓕 riemannPhiKernel ξ‖ ^ 2 := by gcongr
    _ ≤ Real.pi * (K₂ * (2 * Real.pi) ^ (1 / 2 : ℝ) *
          (2 * (1 + ξ ^ 2) * (1 + |ξ|) ^ (-(3 / 2) : ℝ))) *
          ‖𝓕 riemannPhiKernel ξ‖ ^ 2 := by gcongr
    _ = (‖𝓕 riemannPhiKernel ξ‖ ^ 2 * (1 + ξ ^ 2)) *
          (2 * Real.pi * (2 * Real.pi) ^ (1 / 2 : ℝ) * K₂ *
            (1 + |ξ|) ^ (-(3 / 2) : ℝ)) := by ring
    _ ≤ K₁ * (2 * Real.pi * (2 * Real.pi) ^ (1 / 2 : ℝ) * K₂ *
          (1 + |ξ|) ^ (-(3 / 2) : ℝ)) := by
          gcongr
          exact h1 ξ
    _ = C * (1 + |ξ|) ^ (-(3 / 2) : ℝ) := by
          dsimp [C]; ring

/-- `r ↦ ‖paperFT riemannPhiKernel r‖ ^ 2 * EF.gammaBracket r` is integrable on `ℝ`. -/
theorem integrable_paperFT_riemannPhiKernel_sq_mul_gammaBracket :
    Integrable (fun r : ℝ => ‖paperFT riemannPhiKernel r‖ ^ 2 * EF.gammaBracket r) := by
  have hne : -(1 / (2 * Real.pi)) ≠ 0 :=
    neg_ne_zero.mpr (one_div_ne_zero (by positivity))
  have h := (integrable_archSymbol_mul_normSq_fourier_riemannPhiKernel.comp_mul_left'
    (R := -(1 / (2 * Real.pi))) hne).const_mul 2
  refine h.congr (Eventually.of_forall fun r => ?_)
  change 2 * (gammaHardyPhaseRate (2 * Real.pi * (-(1 / (2 * Real.pi)) * r)) *
    ‖𝓕 riemannPhiKernel (-(1 / (2 * Real.pi)) * r)‖ ^ 2) =
    ‖paperFT riemannPhiKernel r‖ ^ 2 * EF.gammaBracket r
  have h1 : 2 * Real.pi * (-(1 / (2 * Real.pi)) * r) = -r := by
    field_simp
  rw [fourier_eq_paperFT_neg_two_pi_mul, h1, neg_neg,
    gammaHardyPhaseRate_neg, gammaBracket_eq_two_mul_gammaHardyPhaseRate]
  ring

/-- **General Bochner Lévy–Khintchine Representation**:
for any continuous `g : ℝ → ℝ` with `g ∈ L¹(ℝ) ∩ L²(ℝ)` and
`Integrable (fun r => ‖paperFT g r‖ ^ 2 * EF.gammaBracket r)`, the jump integrand
`t ↦ archLevyDensity t * ∫ u, (g u - g (u + t)) ^ 2` is Bochner integrable on `Ioi 0` and
`(1 / (2 * π)) * ∫ r, ‖paperFT g r‖ ^ 2 * EF.gammaBracket r = EF.gammaBracket 0 * ∫ g² + ∫_{t > 0} archLevyDensity t * ∫ u, (g u - g (u + t)) ^ 2`. -/
theorem integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner {g : ℝ → ℝ}
    (hg_cont : Continuous g)
    (hg1 : Integrable g)
    (hg2 : Integrable (fun u : ℝ => g u ^ 2))
    (hintR : Integrable (fun r : ℝ => ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * EF.gammaBracket r)) :
    IntegrableOn (fun x : ℝ => archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2) (Ioi 0) ∧
      (1 / (2 * Real.pi)) * (∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) =
        EF.gammaBracket 0 * (∫ u : ℝ, g u ^ 2) +
          ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2 := by
  set G : ℝ → ℂ := fun u => (g u : ℂ) with hGdef
  have hGc : Continuous G := Complex.continuous_ofReal.comp hg_cont
  have hG1 : Integrable G := Complex.ofRealCLM.integrable_comp hg1
  have hGL2 : MemLp G 2 := by
    rw [memLp_two_iff_integrable_sq_norm hGc.aestronglyMeasurable]
    refine hg2.congr (Eventually.of_forall fun u => ?_)
    dsimp [G]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hint : Integrable (fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 G ξ‖ ^ 2) := by
    have h := (hintR.comp_mul_left' (R := -(2 * Real.pi)) (by
      have := Real.pi_pos; intro h; linarith)).div_const 2
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul, gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  have hsplit := integral_archSymbol_mul_normSq_fourier_eq hG1 hGL2 hint
  have htop := lintegral_archLevyDirichlet_ne_top hG1 hGL2 hint
  have hnorm : ∫ u : ℝ, ‖G u‖ ^ 2 = ∫ u : ℝ, g u ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [hGdef, Complex.norm_real, sq_abs]
  have hdiff_norm : ∀ x : ℝ,
      (∫ u : ℝ, ‖G u - G (u + x)‖ ^ 2) = ∫ u : ℝ, (g u - g (u + x)) ^ 2 := by
    intro x
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp [G]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hlev_eq : (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, ‖G u - G (u + x)‖ ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2) := by
    refine lintegral_congr fun x => ?_
    rw [hdiff_norm x]
  rw [hlev_eq] at htop hsplit
  have hc_pair : Continuous (fun p : ℝ × ℝ => (g p.2 - g (p.2 + p.1)) ^ 2) := by fun_prop
  have hmeas_int : StronglyMeasurable (fun x : ℝ => ∫ u : ℝ, (g u - g (u + x)) ^ 2) :=
    hc_pair.stronglyMeasurable.integral_prod_right'
  have hF_meas : AEStronglyMeasurable
      (fun x : ℝ => archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2)
      (volume.restrict (Ioi 0)) :=
    (measurable_archLevyDensity.stronglyMeasurable.mul hmeas_int).aestronglyMeasurable
  have hF_nn : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun _ => sq_nonneg _)
  have hintOn : IntegrableOn
      (fun x : ℝ => archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2) (Ioi 0) := by
    refine ⟨hF_meas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hF_nn]
    exact htop.lt_top
  have hbochner : (∫⁻ x in Ioi (0 : ℝ),
      ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2)).toReal =
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae hF_nn hF_meas]
  refine ⟨hintOn, ?_⟩
  rw [integral_paperFT_sq_mul_gammaBracket, hsplit, hnorm, hbochner,
    gammaBracket_eq_two_mul_gammaHardyPhaseRate]

/-- For any `f ∈ C²_c(ℝ)`, `(jumpEnergy f).toReal` equals the Bochner integral on `Ioi 0`, and
`markovArchRe (EF.weilTest F F)` equals the Bochner Lévy representation. -/
theorem markovArchRe_ofReal_eq_bochner_levy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x : ℝ => archLevyDensity x * ∫ u : ℝ, (f u - f (u + x)) ^ 2) (Ioi 0) ∧
      markovArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
        EF.gammaBracket 0 * (∫ u : ℝ, f u ^ 2) +
          ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (f u - f (u + x)) ^ 2 := by
  set F : ℝ → ℂ := fun u => (f u : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.continuous
  have hFcs : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hF2 : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hf
  have hf1 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hf2 : Integrable (fun u : ℝ => f u ^ 2) := by
    have hcs : HasCompactSupport (fun u : ℝ => f u ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hfc ⊢
      filter_upwards [hfc] with u hu; simp [hu]
    exact (hf.continuous.pow 2).integrable_of_hasCompactSupport hcs
  have hk : ∀ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest hFc hFc hFcs hFcs, Complex.conj_ofReal, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF2 hFcs hF2 hFcs
  have hintR : Integrable (fun r : ℝ => ‖paperFT F r‖ ^ 2 * EF.gammaBracket r) := by
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    change (paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ)).re = _
    rw [hk r, Complex.ofReal_re]
  obtain ⟨hintOn, hboch⟩ :=
    integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hf.continuous hf1 hf2 hintR
  refine ⟨hintOn, ?_⟩
  rw [← hboch]
  unfold markovArchRe WeilOneSided.weilArchRe weilPoleTerm
  have harch : ∫ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((∫ r : ℝ, ‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    simp_rw [hk]
    exact integral_complex_ofReal
  rw [harch]
  simp only [Complex.add_re, ← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, Complex.ofReal_re]
  ring

/-! ## Section 2: Polarized Mixed Archimedean Lévy Representation for `mixedPhiArchRe H` -/

/-- Complex norm-square polarization:
`‖z₁ + z₂‖ ^ 2 = ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 + 2 * (z₁ * conj z₂).re` and
`‖z₁ - z₂‖ ^ 2 = ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 - 2 * (z₁ * conj z₂).re`. -/
theorem norm_add_and_sub_sq_eq (z₁ z₂ : ℂ) :
    (‖z₁ + z₂‖ ^ 2 = ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 + 2 * (z₁ * conj z₂).re) ∧
      (‖z₁ - z₂‖ ^ 2 = ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 - 2 * (z₁ * conj z₂).re) := by
  constructor <;>
  · simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, sub_re, sub_im,
      mul_re, conj_re, conj_im]
    ring

/-- Linearity of `paperFT` for real `L¹` functions at a real frequency `r : ℝ`. -/
theorem paperFT_ofReal_add_and_sub {f h : ℝ → ℝ} (hf : Integrable f) (hh : Integrable h) (r : ℝ) :
    (paperFT (fun u : ℝ => ((f u + h u : ℝ) : ℂ)) r =
        paperFT (fun u : ℝ => (f u : ℂ)) r + paperFT (fun u : ℝ => (h u : ℂ)) r) ∧
      (paperFT (fun u : ℝ => ((f u - h u : ℝ) : ℂ)) r =
        paperFT (fun u : ℝ => (f u : ℂ)) r - paperFT (fun u : ℝ => (h u : ℂ)) r) := by
  have hfC : Integrable (fun u : ℝ => (f u : ℂ)) := Complex.ofRealCLM.integrable_comp hf
  have hhC : Integrable (fun u : ℝ => (h u : ℂ)) := Complex.ofRealCLM.integrable_comp hh
  have h1 := KernelStrip.integrable_mul_cexp_I_mul hfC r
  have h2 := KernelStrip.integrable_mul_cexp_I_mul hhC r
  constructor
  · unfold paperFT
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    push_cast
    ring
  · unfold paperFT
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    push_cast
    ring

/-- **Exact Time-Domain Bochner Lévy Representation of `mixedPhiArchRe H`**:
for every real test `H ∈ C²_c(ℝ)`, the mixed jump integrand
`x ↦ archLevyDensity x * ∫ u, (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))`
is Bochner integrable on `Ioi 0`, and
`mixedPhiArchRe H = EF.gammaBracket 0 * (∫ u, riemannKernelReal u * H u) + ∫ x in Ioi 0, archLevyDensity x * ∫ u, (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))`. -/
theorem mixedPhiArchRe_eq_bochner_levy {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) :
    IntegrableOn (fun x : ℝ => archLevyDensity x *
        ∫ u : ℝ, (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))) (Ioi 0) ∧
      mixedPhiArchRe H =
        EF.gammaBracket 0 * (∫ u : ℝ, riemannKernelReal u * H u) +
          ∫ x in Ioi (0 : ℝ), archLevyDensity x *
            ∫ u : ℝ, (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x)) := by
  set HC : ℝ → ℂ := fun u => (H u : ℂ)
  have hHCc : Continuous HC := Complex.continuous_ofReal.comp hH.continuous
  have hHCs : HasCompactSupport HC := hHc.comp_left Complex.ofReal_zero
  have hHC2 : ContDiff ℝ 2 HC := Complex.ofRealCLM.contDiff.comp hH
  have hH1 : Integrable H := hH.continuous.integrable_of_hasCompactSupport hHc
  have hH2 : Integrable (fun u : ℝ => H u ^ 2) := by
    have hcs : HasCompactSupport (fun u : ℝ => H u ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hHc ⊢
      filter_upwards [hHc] with u hu; simp [hu]
    exact (hH.continuous.pow 2).integrable_of_hasCompactSupport hcs
  have hΦH_int : Integrable (fun u : ℝ => riemannKernelReal u * H u) :=
    (continuous_riemannKernelReal.mul hH.continuous).integrable_of_hasCompactSupport hHc.mul_left
  set gP : ℝ → ℝ := fun u => riemannKernelReal u + H u
  set gM : ℝ → ℝ := fun u => riemannKernelReal u - H u
  have hgP_cont : Continuous gP := continuous_riemannKernelReal.add hH.continuous
  have hgM_cont : Continuous gM := continuous_riemannKernelReal.sub hH.continuous
  have hgP1 : Integrable gP := integrable_riemannKernelReal.add hH1
  have hgM1 : Integrable gM := integrable_riemannKernelReal.sub hH1
  have hgP2 : Integrable (fun u : ℝ => gP u ^ 2) := by
    refine ((integrable_riemannKernelReal_sq.add hH2).add (hΦH_int.const_mul 2)).congr
      (Eventually.of_forall fun u => ?_)
    dsimp [gP]; ring
  have hgM2 : Integrable (fun u : ℝ => gM u ^ 2) := by
    refine ((integrable_riemannKernelReal_sq.add hH2).sub (hΦH_int.const_mul 2)).congr
      (Eventually.of_forall fun u => ?_)
    dsimp [gM]; ring
  have hΦ_eq : (fun u : ℝ => (riemannKernelReal u : ℂ)) = riemannPhiKernel :=
    funext fun u => (riemannPhiKernel_eq_ofReal u).symm
  have hint_Φ : Integrable (fun r : ℝ =>
      ‖paperFT (fun u : ℝ => (riemannKernelReal u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) := by
    rw [hΦ_eq]
    exact integrable_paperFT_riemannPhiKernel_sq_mul_gammaBracket
  have hint_H : Integrable (fun r : ℝ => ‖paperFT HC r‖ ^ 2 * EF.gammaBracket r) := by
    have hk : ∀ r : ℝ, paperFT (EF.weilTest HC HC) r * (EF.gammaBracket r : ℂ) =
        ((‖paperFT HC r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
      rw [EF.paperFT_weilTest hHCc hHCc hHCs hHCs, Complex.conj_ofReal, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast; ring
    have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hHC2 hHCs hHC2 hHCs
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    change (paperFT (EF.weilTest HC HC) r * (EF.gammaBracket r : ℂ)).re = _
    rw [hk r, Complex.ofReal_re]
  have hint_mix : Integrable (fun r : ℝ =>
      (paperFT (EF.weilTest riemannPhiKernel HC) r * (EF.gammaBracket r : ℂ)).re) :=
    (integrable_mixed_riemannPhiKernel_gamma hHC2 hHCs).re
  have hpol_r : ∀ r : ℝ,
      (‖paperFT (fun u : ℝ => (gP u : ℂ)) r‖ ^ 2 * EF.gammaBracket r =
        ‖paperFT (fun u : ℝ => (riemannKernelReal u : ℂ)) r‖ ^ 2 * EF.gammaBracket r +
          ‖paperFT HC r‖ ^ 2 * EF.gammaBracket r +
          2 * (paperFT (EF.weilTest riemannPhiKernel HC) r * (EF.gammaBracket r : ℂ)).re) ∧
      (‖paperFT (fun u : ℝ => (gM u : ℂ)) r‖ ^ 2 * EF.gammaBracket r =
        ‖paperFT (fun u : ℝ => (riemannKernelReal u : ℂ)) r‖ ^ 2 * EF.gammaBracket r +
          ‖paperFT HC r‖ ^ 2 * EF.gammaBracket r -
          2 * (paperFT (EF.weilTest riemannPhiKernel HC) r * (EF.gammaBracket r : ℂ)).re) := by
    intro r
    obtain ⟨hftP, hftM⟩ := paperFT_ofReal_add_and_sub integrable_riemannKernelReal hH1 r
    obtain ⟨hnP, hnM⟩ := norm_add_and_sub_sq_eq
      (paperFT (fun u : ℝ => (riemannKernelReal u : ℂ)) r) (paperFT HC r)
    have hmix_r : (paperFT (EF.weilTest riemannPhiKernel HC) r * (EF.gammaBracket r : ℂ)).re =
        (paperFT (fun u : ℝ => (riemannKernelReal u : ℂ)) r * conj (paperFT HC r)).re *
          EF.gammaBracket r := by
      rw [paperFT_mixed_riemannPhiKernel hHCc hHCs r, Complex.conj_ofReal, hΦ_eq,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp [gP, gM]
    rw [hftP, hftM, hnP, hnM, hmix_r]
    exact ⟨by ring, by ring⟩
  have hint_gP : Integrable (fun r : ℝ =>
      ‖paperFT (fun u : ℝ => (gP u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) := by
    refine ((hint_Φ.add hint_H).add (hint_mix.const_mul 2)).congr (Eventually.of_forall fun r => ?_)
    simp only [Pi.add_apply]
    exact ((hpol_r r).1).symm
  have hint_gM : Integrable (fun r : ℝ =>
      ‖paperFT (fun u : ℝ => (gM u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) := by
    refine ((hint_Φ.add hint_H).sub (hint_mix.const_mul 2)).congr (Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply, Pi.add_apply]
    exact ((hpol_r r).2).symm
  obtain ⟨hintOnP, hbochP⟩ :=
    integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hgP_cont hgP1 hgP2 hint_gP
  obtain ⟨hintOnM, hbochM⟩ :=
    integral_paperFT_ofReal_sq_mul_gammaBracket_eq_bochner hgM_cont hgM1 hgM2 hint_gM
  have hshift_pol : ∀ x : ℝ,
      (∫ u : ℝ, (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))) =
        (1 / 4 : ℝ) * ((∫ u : ℝ, (gP u - gP (u + x)) ^ 2) -
          ∫ u : ℝ, (gM u - gM (u + x)) ^ 2) := by
    intro x
    have hiP : Integrable (fun u : ℝ => (gP u - gP (u + x)) ^ 2) := by
      have hi1 : Integrable (fun u : ℝ => (riemannKernelReal u - riemannKernelReal (u + x)) ^ 2) := by
        have h2 := integrable_riemannKernelReal_sq
        have h2s := h2.comp_add_right x
        have hcs : Integrable (fun u : ℝ => riemannKernelReal u * riemannKernelReal (u + x)) := by
          obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
          refine (integrable_riemannKernelReal.const_mul C).mono'
            (continuous_riemannKernelReal.mul
              (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).aestronglyMeasurable
            (Eventually.of_forall fun u => ?_)
          change ‖riemannKernelReal u * riemannKernelReal (u + x)‖ ≤ C * riemannKernelReal u
          rw [Real.norm_of_nonneg (mul_nonneg (riemannKernelReal_pos u).le
            (riemannKernelReal_pos (u + x)).le), mul_comm]
          have hC1 : riemannKernelReal (u + x) ≤ C :=
            (hC (u + x)).trans (mul_le_of_le_one_right hC0
              (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg (u + x)])))
          exact mul_le_mul_of_nonneg_right hC1 (riemannKernelReal_pos u).le
        refine ((h2.add h2s).sub (hcs.const_mul 2)).congr (Eventually.of_forall fun u => ?_)
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      have hi2 : Integrable (fun u : ℝ => (H u - H (u + x)) ^ 2) := by
        have hsub : HasCompactSupport (fun u : ℝ => H u - H (u + x)) :=
          hHc.sub (hHc.comp_homeomorph (Homeomorph.addRight x))
        have hsub2 : HasCompactSupport (fun u : ℝ => (H u - H (u + x)) ^ 2) := by
          rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
          filter_upwards [hsub] with u hu; simp [hu]
        exact ((hH.continuous.sub
          (hH.continuous.comp (continuous_id.add continuous_const))).pow 2).integrable_of_hasCompactSupport
          hsub2
      have hi3 : Integrable (fun u : ℝ =>
          (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))) := by
        have hsub : HasCompactSupport (fun u : ℝ => H u - H (u + x)) :=
          hHc.sub (hHc.comp_homeomorph (Homeomorph.addRight x))
        exact ((continuous_riemannKernelReal.sub
          (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
          (hH.continuous.sub
            (hH.continuous.comp (continuous_id.add continuous_const)))).integrable_of_hasCompactSupport
          hsub.mul_left
      refine ((hi1.add hi2).add (hi3.const_mul 2)).congr (Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply, gP]
      ring
    have hiM : Integrable (fun u : ℝ => (gM u - gM (u + x)) ^ 2) := by
      have hi3 : Integrable (fun u : ℝ =>
          (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))) := by
        have hsub : HasCompactSupport (fun u : ℝ => H u - H (u + x)) :=
          hHc.sub (hHc.comp_homeomorph (Homeomorph.addRight x))
        exact ((continuous_riemannKernelReal.sub
          (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
          (hH.continuous.sub
            (hH.continuous.comp (continuous_id.add continuous_const)))).integrable_of_hasCompactSupport
          hsub.mul_left
      refine (hiP.sub (hi3.const_mul 4)).congr (Eventually.of_forall fun u => ?_)
      simp only [Pi.sub_apply, gP, gM]
      ring
    rw [← integral_sub hiP hiM, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp [gP, gM]
    ring
  have hintOn_mix : IntegrableOn (fun x : ℝ => archLevyDensity x *
      ∫ u : ℝ, (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))) (Ioi 0) := by
    have hdiff : IntegrableOn (fun x : ℝ => (1 / 4 : ℝ) *
        (archLevyDensity x * (∫ u : ℝ, (gP u - gP (u + x)) ^ 2) -
          archLevyDensity x * ∫ u : ℝ, (gM u - gM (u + x)) ^ 2)) (Ioi 0) :=
      (hintOnP.sub hintOnM).const_mul (1 / 4 : ℝ)
    refine hdiff.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [hshift_pol x]
    ring
  refine ⟨hintOn_mix, ?_⟩
  have hint_boch_eq : (∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u : ℝ, (riemannKernelReal u - riemannKernelReal (u + x)) * (H u - H (u + x))) =
      (1 / 4 : ℝ) * ((∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (gP u - gP (u + x)) ^ 2) -
        ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u : ℝ, (gM u - gM (u + x)) ^ 2) := by
    rw [← integral_sub hintOnP hintOnM, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [hshift_pol x]
    ring
  have hloc_eq : (∫ u : ℝ, riemannKernelReal u * H u) =
      (1 / 4 : ℝ) * ((∫ u : ℝ, gP u ^ 2) - ∫ u : ℝ, gM u ^ 2) := by
    rw [← integral_sub hgP2 hgM2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp [gP, gM]
    ring
  have hspec_eq : mixedPhiArchRe H =
      (1 / 4 : ℝ) * ((1 / (2 * Real.pi)) *
          (∫ r : ℝ, ‖paperFT (fun u : ℝ => (gP u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) -
        (1 / (2 * Real.pi)) *
          (∫ r : ℝ, ‖paperFT (fun u : ℝ => (gM u : ℂ)) r‖ ^ 2 * EF.gammaBracket r)) := by
    unfold mixedPhiArchRe
    have hre : ((1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ,
        paperFT (EF.weilTest riemannPhiKernel HC) r * (EF.gammaBracket r : ℂ)).re =
        (1 / (2 * Real.pi)) * ∫ r : ℝ,
          (paperFT (EF.weilTest riemannPhiKernel HC) r * (EF.gammaBracket r : ℂ)).re := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact congr_arg ((1 / (2 * Real.pi)) * ·)
        (integral_re (integrable_mixed_riemannPhiKernel_gamma hHC2 hHCs)).symm
    rw [hre, ← mul_sub, ← integral_sub hint_gP hint_gM]
    have hcongr : (∫ r : ℝ, ‖paperFT (fun u : ℝ => (gP u : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
        ‖paperFT (fun u : ℝ => (gM u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) =
        4 * ∫ r : ℝ,
          (paperFT (EF.weilTest riemannPhiKernel HC) r * (EF.gammaBracket r : ℂ)).re := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      dsimp only
      rw [(hpol_r r).1, (hpol_r r).2]
      ring
    rw [hcongr]
    ring
  rw [hspec_eq, hbochP, hbochM, hloc_eq, hint_boch_eq]
  ring

/-! ## Section 3: Exact Archimedean Doob Ground-State Cancellation and the Pure-Dirichlet Decomposition of `markovEnergy (Φ v)` -/

/-- The archimedean Doob jump integrand at shift `t : ℝ` and position `x : ℝ`:
`phiDoobArchShiftJump v t x = Φ(x) Φ(x + t) (v(x) - v(x + t))² ≥ 0`. -/
def phiDoobArchShiftJump (v : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2

/-- The total archimedean Doob jump Dirichlet energy on `(0, ∞)`:
`phiDoobArchJumpEnergy v = ∫_{t > 0} archLevyDensity t * (∫_ℝ Φ(x) Φ(x + t) (v(x) - v(x + t))² dx) dt`. -/
def phiDoobArchJumpEnergy (v : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x : ℝ, phiDoobArchShiftJump v t x

/-- Pointwise nonnegativity of `phiDoobArchShiftJump v t x`. -/
theorem phiDoobArchShiftJump_nonneg (v : ℝ → ℝ) (t x : ℝ) :
    0 ≤ phiDoobArchShiftJump v t x := by
  unfold phiDoobArchShiftJump
  exact mul_nonneg
    (mul_nonneg (riemannKernelReal_pos x).le (riemannKernelReal_pos (x + t)).le)
    (sq_nonneg _)

/-- Nonnegativity of the inner spatial integral `∫ x, phiDoobArchShiftJump v t x ≥ 0`. -/
theorem integral_phiDoobArchShiftJump_nonneg (v : ℝ → ℝ) (t : ℝ) :
    0 ≤ ∫ x : ℝ, phiDoobArchShiftJump v t x :=
  integral_nonneg (phiDoobArchShiftJump_nonneg v t)

/-- Nonnegativity of the archimedean Doob jump Dirichlet energy `0 ≤ phiDoobArchJumpEnergy v`. -/
theorem phiDoobArchJumpEnergy_nonneg (v : ℝ → ℝ) :
    0 ≤ phiDoobArchJumpEnergy v := by
  unfold phiDoobArchJumpEnergy
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (archLevyDensity_pos ht).le (integral_phiDoobArchShiftJump_nonneg v t)

/-- **Pointwise Archimedean Doob Jump Factorization**:
subtracting the mixed difference product `(Φ(x) - Φ(x+t))((Φv²)(x) - (Φv²)(x+t))` from the
quadratic difference square `(Φv(x) - Φv(x+t))²` leaves the pure Doob jump
`Φ(x) Φ(x+t) (v(x) - v(x+t))²`. -/
theorem phiDoob_pointwise_jump_sub_mixed (v : ℝ → ℝ) (t x : ℝ) :
    (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2 -
        (riemannKernelReal x - riemannKernelReal (x + t)) *
          (phiDoobTest (fun y => v y ^ 2) x - phiDoobTest (fun y => v y ^ 2) (x + t)) =
      phiDoobArchShiftJump v t x := by
  unfold phiDoobTest phiDoobArchShiftJump
  ring

/-- **Exact Archimedean Doob Ground-State Cancellation Theorem**:
for every `v ∈ C²_c(ℝ)`, the negative local constant `EF.gammaBracket 0 * ∫ (Φ v)²` cancels
identically between `markovArchRe k_{Φv}` and `mixedPhiArchRe (Φ v²)`, and their difference equals
the manifestly nonnegative archimedean Doob jump energy `phiDoobArchJumpEnergy v`:
`markovArchRe k_{Φv} - mixedPhiArchRe (Φ v²) = phiDoobArchJumpEnergy v ≥ 0`. -/
theorem markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    IntegrableOn (fun t : ℝ => archLevyDensity t * ∫ x : ℝ, phiDoobArchShiftJump v t x) (Ioi 0) ∧
      markovArchRe (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
          (fun x => (phiDoobTest v x : ℂ))) -
        mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2)) =
        phiDoobArchJumpEnergy v := by
  have hv2c : HasCompactSupport (fun x => v x ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
    filter_upwards [hvc] with x hx; simp [hx]
  obtain ⟨hint_quad, hquad⟩ :=
    markovArchRe_ofReal_eq_bochner_levy (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc)
  obtain ⟨hint_mix, hmix⟩ :=
    mixedPhiArchRe_eq_bochner_levy (contDiff_phiDoobTest (hv.pow 2))
      (hasCompactSupport_phiDoobTest hv2c)
  have hloc : (∫ u : ℝ, riemannKernelReal u * phiDoobTest (fun x => v x ^ 2) u) =
      ∫ u : ℝ, phiDoobTest v u ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp [phiDoobTest]; ring
  have hshift_eq : ∀ t : ℝ,
      (∫ x : ℝ, phiDoobArchShiftJump v t x) =
        (∫ x : ℝ, (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2) -
          ∫ x : ℝ, (riemannKernelReal x - riemannKernelReal (x + t)) *
            (phiDoobTest (fun y => v y ^ 2) x -
              phiDoobTest (fun y => v y ^ 2) (x + t)) := by
    intro t
    have h1 : Integrable (fun x : ℝ => (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2) := by
      have hf := hasCompactSupport_phiDoobTest hvc
      have hsub : HasCompactSupport (fun x : ℝ => phiDoobTest v x - phiDoobTest v (x + t)) :=
        hf.sub (hf.comp_homeomorph (Homeomorph.addRight t))
      have hsub2 : HasCompactSupport (fun x : ℝ => (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2) := by
        rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
        filter_upwards [hsub] with x hx; simp [hx]
      exact (((contDiff_phiDoobTest hv).continuous.sub
        ((contDiff_phiDoobTest hv).continuous.comp
          (continuous_id.add continuous_const))).pow 2).integrable_of_hasCompactSupport hsub2
    have h2 : Integrable (fun x : ℝ => (riemannKernelReal x - riemannKernelReal (x + t)) *
        (phiDoobTest (fun y => v y ^ 2) x - phiDoobTest (fun y => v y ^ 2) (x + t))) := by
      have hH := hasCompactSupport_phiDoobTest hv2c
      have hsub : HasCompactSupport (fun x : ℝ =>
          phiDoobTest (fun y => v y ^ 2) x - phiDoobTest (fun y => v y ^ 2) (x + t)) :=
        hH.sub (hH.comp_homeomorph (Homeomorph.addRight t))
      have hHcont : Continuous (phiDoobTest (fun y => v y ^ 2)) :=
        continuous_riemannKernelReal.mul (hv.continuous.pow 2)
      exact ((continuous_riemannKernelReal.sub
        (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
        (hHcont.sub (hHcont.comp (continuous_id.add continuous_const)))).integrable_of_hasCompactSupport
        hsub.mul_left
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    exact (phiDoob_pointwise_jump_sub_mixed v t x).symm
  have hint_doob : IntegrableOn
      (fun t : ℝ => archLevyDensity t * ∫ x : ℝ, phiDoobArchShiftJump v t x) (Ioi 0) := by
    have hdiff : IntegrableOn (fun t : ℝ =>
        archLevyDensity t * (∫ x : ℝ, (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2) -
          archLevyDensity t * ∫ x : ℝ, (riemannKernelReal x - riemannKernelReal (x + t)) *
            (phiDoobTest (fun y => v y ^ 2) x - phiDoobTest (fun y => v y ^ 2) (x + t))) (Ioi 0) :=
      hint_quad.sub hint_mix
    refine hdiff.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [hshift_eq t]
    ring
  refine ⟨hint_doob, ?_⟩
  rw [hquad, hmix, hloc]
  have hboch_sub : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x : ℝ, (phiDoobTest v x - phiDoobTest v (x + t)) ^ 2) -
      (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x : ℝ, (riemannKernelReal x - riemannKernelReal (x + t)) *
          (phiDoobTest (fun y => v y ^ 2) x - phiDoobTest (fun y => v y ^ 2) (x + t))) =
      phiDoobArchJumpEnergy v := by
    unfold phiDoobArchJumpEnergy
    rw [← integral_sub hint_quad hint_mix]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hshift_eq t]
    ring
  linarith

/-- Nonnegativity of `markovArchRe k_{Φv} - mixedPhiArchRe (Φ v²)` for every `v ∈ C²_c(ℝ)`. -/
theorem markovArchRe_sub_mixedPhiArchRe_nonneg {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    0 ≤ markovArchRe (EF.weilTest (fun x => (phiDoobTest v x : ℂ))
        (fun x => (phiDoobTest v x : ℂ))) -
      mixedPhiArchRe (phiDoobTest (fun x => v x ^ 2)) := by
  rw [(markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy hv hvc).2]
  exact phiDoobArchJumpEnergy_nonneg v

/-- **The Complete Pure-Dirichlet Doob Ground-State Identity for `markovEnergy (Φ v)`**:
for every `v ∈ C²_c(ℝ)`, `markovEnergy (Φ v)` is the sum of the nonnegative archimedean Doob jump
Dirichlet form `phiDoobArchJumpEnergy v ≥ 0` and the nonnegative prime Doob jump Dirichlet form
`∑' n, ∫ phiDoobPrimeJump v n ≥ 0`, minus the single Biane–Pitman–Yor second moment
`phiDoobCoshMass (fun x => v x ^ 2) = ∫ Φ(x) v(x)² cosh(x / 2) dx`. -/
theorem phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    markovEnergy (fun x => (phiDoobTest v x : ℂ)) =
      phiDoobArchJumpEnergy v +
        (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) -
        phiDoobCoshMass (fun x => v x ^ 2) := by
  rw [phiDoob_markovEnergy_groundState_cancellation hv hvc,
    (markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy hv hvc).2]

/-- **Unconditional Odd Pure-Dirichlet Poincaré Criterion for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if for every odd `v ∈ C²_c(ℝ)`,
`phiDoobCoshMass (fun x => v x ^ 2) ≤ phiDoobArchJumpEnergy v + ∑' n, ∫ x, phiDoobPrimeJump v n x`. -/
theorem riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
        phiDoobCoshMass (fun x => v x ^ 2) ≤
          phiDoobArchJumpEnergy v + ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x := by
  rw [riemannHypothesis_iff_forall_odd_phiDoob_poincare_inequality]
  refine forall₄_congr fun v hv hvc _ => ?_
  rw [(markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy hv hvc).2]

/-- **Unconditional Primitive-Hyperplane Pure-Dirichlet Poincaré Criterion for `RiemannHypothesis`**:
`RiemannHypothesis` holds if and only if for every `v ∈ C²_c(ℝ)` with `phiDoobCoshMass v = 0`,
`phiDoobCoshMass (fun x => v x ^ 2) ≤ phiDoobArchJumpEnergy v + ∑' n, ∫ x, phiDoobPrimeJump v n x`. -/
theorem riemannHypothesis_iff_forall_phiDoobCoshMass_zero_dirichlet_poincare :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → phiDoobCoshMass v = 0 →
        phiDoobCoshMass (fun x => v x ^ 2) ≤
          phiDoobArchJumpEnergy v + ∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x := by
  rw [riemannHypothesis_iff_forall_phiDoobCoshMass_zero_poincare_inequality]
  refine forall₄_congr fun v hv hvc _ => ?_
  rw [(markovArchRe_sub_mixedPhiArchRe_eq_phiDoobArchJumpEnergy hv hvc).2]

/-! ## Section 4: Exact Half-Line `(0, ∞)` Folding of Odd Doob Tests and Origin-Crossing Reflected Sum-Square Positivity -/

/-- For any odd continuous compactly supported `v : ℝ → ℝ`, `phiDoobCoshMass (fun x => v x ^ 2)`
folds onto twice the half-line integral `2 * ∫ x in Ioi 0, Φ(x) v(x)² cosh(x / 2) dx`. -/
theorem phiDoobCoshMass_sq_eq_two_mul_integral_Ioi_of_odd {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) :
    phiDoobCoshMass (fun x => v x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), riemannKernelReal x * v x ^ 2 * Real.cosh (x / 2) := by
  unfold phiDoobCoshMass phiDoobTest
  set f : ℝ → ℝ := fun x => riemannKernelReal x * v x ^ 2 * Real.cosh (x / 2)
  have hf_int : Integrable f := by
    have hv2c : HasCompactSupport (fun x : ℝ => v x ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hvc ⊢
      filter_upwards [hvc] with x hx; simp [hx]
    have hfc : HasCompactSupport f := by
      have h1 : HasCompactSupport (fun x : ℝ => riemannKernelReal x * v x ^ 2) := hv2c.mul_left
      exact h1.mul_right
    exact ((continuous_riemannKernelReal.mul (hv.pow 2)).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport hfc
  have hsplit := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hf_int
  rw [compl_Iic] at hsplit
  have hneg : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    have h1 := integral_comp_neg_Iic (c := (0 : ℝ)) f
    rw [neg_zero] at h1
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Iic fun x _ => ?_
    dsimp [f]
    have hΦ : riemannKernelReal (-x) = riemannKernelReal x := by simp [riemannKernelReal]
    rw [hΦ, hodd x, neg_sq, neg_div, Real.cosh_neg]
  change (∫ x : ℝ, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x
  linarith

/-- **Exact Half-Line `(0, ∞)` Folding of the Doob Shift Jump for Odd `v`**:
for any odd continuous compactly supported `v : ℝ → ℝ` and any shift `t ≥ 0`,
`∫_ℝ Φ(x)Φ(x+t)(v(x) - v(x+t))² dx = 2 ∫_{x ∈ (0, ∞)} Φ(x)Φ(x+t)(v(x) - v(x+t))² dx + ∫_{x ∈ (0, t)} Φ(x)Φ(t - x)(v(x) + v(t - x))² dx`.
The origin-crossing collar `(0, t)` contributes the reflected sum-square integral
`∫_{x ∈ (0, t)} Φ(x)Φ(t - x)(v(x) + v(t - x))² dx ≥ 0`. -/
theorem integral_phiDoobArchShiftJump_eq_halfLine_of_odd {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, phiDoobArchShiftJump v t x) =
      2 * (∫ x in Ioi (0 : ℝ), phiDoobArchShiftJump v t x) +
        ∫ x in Ioo (0 : ℝ) t,
          riemannKernelReal x * riemannKernelReal (t - x) * (v x + v (t - x)) ^ 2 := by
  have hint : Integrable (phiDoobArchShiftJump v t) := by
    have hsub : HasCompactSupport (fun x : ℝ => v x - v (x + t)) :=
      hvc.sub (hvc.comp_homeomorph (Homeomorph.addRight t))
    have hsub2 : HasCompactSupport (fun x : ℝ => (v x - v (x + t)) ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
      filter_upwards [hsub] with x hx; simp [hx]
    have hc : Continuous (phiDoobArchShiftJump v t) := by
      unfold phiDoobArchShiftJump
      exact ((continuous_riemannKernelReal.mul
        (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))).mul
        ((hv.sub (hv.comp (continuous_id.add continuous_const))).pow 2))
    exact hc.integrable_of_hasCompactSupport hsub2.mul_left
  have hsplit0 := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint
  rw [compl_Iic] at hsplit0
  have hneg : (∫ x in Iic (0 : ℝ), phiDoobArchShiftJump v t x) =
      ∫ u in Ioi (0 : ℝ),
        riemannKernelReal u * riemannKernelReal (t - u) * (v u + v (t - u)) ^ 2 := by
    have h1 := integral_comp_neg_Ioi (c := (0 : ℝ)) (phiDoobArchShiftJump v t)
    rw [neg_zero] at h1
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold phiDoobArchShiftJump
    have hΦ1 : riemannKernelReal (-u) = riemannKernelReal u := by simp [riemannKernelReal]
    have hΦ2 : riemannKernelReal (-u + t) = riemannKernelReal (t - u) := by
      rw [show -u + t = t - u by ring]
    rw [hΦ1, hΦ2, show -u + t = t - u by ring, hodd u]
    ring
  set g : ℝ → ℝ := fun u =>
    riemannKernelReal u * riemannKernelReal (t - u) * (v u + v (t - u)) ^ 2
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hint_neg : IntegrableOn (fun u : ℝ => phiDoobArchShiftJump v t (-u)) (Ioi (0 : ℝ)) := by
      have h := hint.comp_neg
      exact h.integrableOn
    refine hint_neg.congr_fun (fun u _ => ?_) measurableSet_Ioi
    dsimp [g, phiDoobArchShiftJump]
    have hΦ1 : riemannKernelReal (-u) = riemannKernelReal u := by simp [riemannKernelReal]
    rw [hΦ1, show -u + t = t - u by ring, hodd u]
    ring
  have hsplit_t : (∫ u in Ioi (0 : ℝ), g u) =
      (∫ u in Ioo (0 : ℝ) t, g u) + ∫ u in Ioi t, g u := by
    have h_union_eq : Ioc (0 : ℝ) t ∪ Ioi t = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi ht
    have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioi t) := Ioc_disjoint_Ioi le_rfl
    rw [← h_union_eq, setIntegral_union hdisj measurableSet_Ioi
      (hg_int.mono_set Ioc_subset_Ioi_self) (hg_int.mono_set (Ioi_subset_Ioi ht)),
      integral_Ioc_eq_integral_Ioo]
  have htail : (∫ u in Ioi t, g u) = ∫ x in Ioi (0 : ℝ), phiDoobArchShiftJump v t x := by
    have hmp : MeasurePreserving (fun x : ℝ => x + t) volume volume :=
      measurePreserving_add_right volume t
    have hemb : MeasurableEmbedding (fun x : ℝ => x + t) :=
      (Homeomorph.addRight t).measurableEmbedding
    have hpre : (fun x : ℝ => x + t) ⁻¹' Ioi t = Ioi (0 : ℝ) := by ext x; simp
    have htr := hmp.setIntegral_preimage_emb hemb g (Ioi t)
    rw [hpre] at htr
    rw [← htr]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [g, phiDoobArchShiftJump]
    have hΦ : riemannKernelReal (t - (x + t)) = riemannKernelReal x := by
      rw [show t - (x + t) = -x by ring]
      simp [riemannKernelReal]
    rw [hΦ, show t - (x + t) = -x by ring, hodd x]
    ring
  rw [← hsplit0, hneg, hsplit_t, htail]
  ring

/-- The half-line Doob jump `2 * ∫ x in Ioi 0, phiDoobArchShiftJump v t x` is bounded above by the
full-line Doob jump `∫ x, phiDoobArchShiftJump v t x` for any odd `v ∈ C_c(ℝ)` and `t ≥ 0`. -/
theorem two_mul_integral_Ioi_phiDoobArchShiftJump_le_of_odd {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) {t : ℝ} (ht : 0 ≤ t) :
    2 * (∫ x in Ioi (0 : ℝ), phiDoobArchShiftJump v t x) ≤
      ∫ x : ℝ, phiDoobArchShiftJump v t x := by
  rw [integral_phiDoobArchShiftJump_eq_halfLine_of_odd hv hvc hodd ht]
  have hcollar : 0 ≤ ∫ x in Ioo (0 : ℝ) t,
      riemannKernelReal x * riemannKernelReal (t - x) * (v x + v (t - x)) ^ 2 := by
    refine setIntegral_nonneg measurableSet_Ioo fun x _ => ?_
    exact mul_nonneg
      (mul_nonneg (riemannKernelReal_pos x).le (riemannKernelReal_pos (t - x)).le)
      (sq_nonneg _)
  linarith

/-- **Exact Half-Line `(0, ∞)` Folding of Each Prime Doob Jump for Odd `v`**:
for any odd continuous compactly supported `v : ℝ → ℝ` and any `n : ℕ`,
`∫_ℝ phiDoobPrimeJump v n x dx = 2 ∫_{x ∈ (0, ∞)} phiDoobPrimeJump v n x dx + vonMangoldtAtom n * ∫_{x ∈ (0, log n)} Φ(x)Φ(log n - x)(v(x) + v(log n - x))² dx`. -/
theorem integral_phiDoobPrimeJump_eq_halfLine_of_odd {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) (n : ℕ) :
    (∫ x : ℝ, phiDoobPrimeJump v n x) =
      2 * (∫ x in Ioi (0 : ℝ), phiDoobPrimeJump v n x) +
        vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
          riemannKernelReal x * riemannKernelReal (Real.log n - x) *
            (v x + v (Real.log n - x)) ^ 2 := by
  have heq : phiDoobPrimeJump v n =
      fun x : ℝ => vonMangoldtAtom n * phiDoobArchShiftJump v (Real.log n) x := by
    funext x
    unfold phiDoobPrimeJump phiDoobArchShiftJump
    ring
  rw [heq, integral_const_mul, integral_const_mul,
    integral_phiDoobArchShiftJump_eq_halfLine_of_odd hv hvc hodd (Real.log_natCast_nonneg n)]
  ring

end RHTower

end
