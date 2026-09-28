import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.HTGeometry.PowerSeriesTailBound

/-!
# Möbius sub-orthogonality, the Gamma--Hankel blow-up exponent, and zero multiplicity

The finite Möbius Gamma--Hankel energy `E_r(N)` is the squared norm of the signed atom sum
`∑_{n ≤ N} μ(n) v_n`, where the atoms `v_n(x) = x^{(r-1)/2} e^{-n x}` have pairwise positive
inner products `Γ(r)/(m+n)^r`.

**Multiplicity law.**  If `E_{2σ}(N) ≤ C/(2σ-1)^k` for every cutoff `N` and every `σ` in an
interval `(1/2, σ₀)`, then the Riemann hypothesis holds and every zero of `ζ` in the critical
strip has order `n` with `2n ≤ k + 1`.  A critical zero of order `n` forces a Mellin floor
`c r⁻ⁿ` on the window of radius `r` at abscissa `1/2 + r`, hence line energy at least
`2c² r^{1-2n}`, while the ceiling and Plancherel give at most `2π C (2r)^{-k}`.

**Sub-orthogonality.**  Call the Möbius sign pattern *sub-orthogonal* near the critical line if
the signed off-diagonal covariance is nonpositive for every cutoff and every exponent
`1 < r < 2σ₀`:

`‖∑_{n≤N} μ(n) v_n‖² ≤ ∑_{n≤N} μ(n)² ‖v_n‖²`.

The diagonal is at most `2/(r-1)` for `1 < r ≤ 2`, so sub-orthogonality is the case `k = 1` of
the multiplicity law: it implies the Riemann hypothesis and simplicity of every zero in the
strip.  For the rank-one kernel (all atoms equal) the same inequality is the Mertens inequality
`M(N)² ≤ #{n ≤ N squarefree}`, which is false.  Sub-orthogonality itself is not proved here.
-/

open Complex Real MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace RHTower

/-- A boundary zero of analytic order `n` forces a `c/rⁿ` Mellin floor on the vertical window of
radius `r` just inside the half-plane of the canonical identity. -/
theorem exists_order_vertical_window_floor_of_canonical_identity
    {G : ℂ → ℂ} {sigma : ℝ} {rho : ℂ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hrho : rho.re = sigma) (hzero : riemannZeta rho = 0)
    (hidentity : ∀ z : ℂ, sigma < z.re →
      G z * zetaResidueUnit z = Complex.Gamma z * (z - 1)) :
    1 ≤ (analyticOrderAt riemannZeta rho).toNat ∧
      ∃ c > 0, ∃ delta > 0, ∀ r : ℝ, 0 < r → r < delta →
        ∀ t : ℝ, |t - rho.im| ≤ r →
          c / r ^ (analyticOrderAt riemannZeta rho).toNat ≤
            ‖G (((sigma + r : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
    linarith
  have hrhoPos : 0 < rho.re := by rw [hrho]; exact hsigma
  have hstrip : 0 < rho.re ∧ rho.re < 1 := by
    rw [hrho]
    exact ⟨hsigma, hsigmaOne⟩
  have horderEq := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
  have horderFinite : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    rw [← horderEq]
    exact xi_orderAt_ne_top rho
  set n : ℕ := (analyticOrderAt riemannZeta rho).toNat with hndef
  have hncoe : (n : ℕ∞) = analyticOrderAt riemannZeta rho :=
    ENat.coe_toNat horderFinite
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho hrhoOne
  obtain ⟨p, hp, hpzero, hfactor⟩ :=
    (hzetaAnalytic.analyticOrderAt_eq_natCast).mp hncoe.symm
  have hnzero : n ≠ 0 := by
    intro hn
    have horderZero : analyticOrderAt riemannZeta rho = 0 := by
      rw [← hncoe, hn]
      simp
    exact (analyticOrderAt_ne_zero.mpr ⟨hzetaAnalytic, hzero⟩) horderZero
  refine ⟨Nat.one_le_iff_ne_zero.mpr hnzero, ?_⟩
  have hnotGammaPole : ∀ m : ℕ, rho ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    rw [hrho] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  let q : ℂ → ℂ := fun z => Complex.Gamma z / p z
  have hqcont : ContinuousAt q rho := by
    exact (Complex.continuousAt_Gamma rho hnotGammaPole).div hp.continuousAt hpzero
  have hqzero : q rho ≠ 0 := by
    exact div_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhoPos) hpzero
  have hqpos : 0 < ‖q rho‖ := norm_pos_iff.mpr hqzero
  have hqfloor : ∀ᶠ z : ℂ in 𝓝 rho, ‖q rho‖ / 2 < ‖q z‖ :=
    hqcont.norm.eventually_const_lt (by linarith)
  have hpne : ∀ᶠ z : ℂ in 𝓝 rho, p z ≠ 0 :=
    hp.continuousAt.tendsto.eventually (isOpen_ne.mem_nhds hpzero)
  have hlocal : ∀ᶠ z : ℂ in 𝓝 rho,
      riemannZeta z = (z - rho) ^ n * p z ∧ p z ≠ 0 ∧
        ‖q rho‖ / 2 ≤ ‖q z‖ := by
    filter_upwards [hfactor, hpne, hqfloor] with z hz hpz hqz
    exact ⟨by simpa [smul_eq_mul] using hz, hpz, hqz.le⟩
  obtain ⟨eps, heps, hepsLocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  let delta : ℝ := min (eps / 2) (min ((1 - sigma) / 2) (1 / 2))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  refine ⟨‖q rho‖ / 2 ^ (n + 1), by positivity, delta, hdelta, ?_⟩
  intro r hr hrdelta t ht
  let z : ℂ := ((sigma + r : ℝ) : ℂ) + (t : ℂ) * I
  have hzre : z.re = sigma + r := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hrEps : 2 * r < eps := by
    have hle : delta ≤ eps / 2 := min_le_left _ _
    nlinarith
  have hrOneSub : r < (1 - sigma) / 2 := by
    have hle : delta ≤ (1 - sigma) / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    exact hrdelta.trans_le hle
  have hnorm : ‖z - rho‖ ≤ 2 * r := by
    calc
      ‖z - rho‖ ≤ |(z - rho).re| + |(z - rho).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = r + |t - rho.im| := by simp [hzre, hzim, hrho, abs_of_pos hr]
      _ ≤ 2 * r := by linarith
  have hzdist : dist z rho < eps := by
    rw [Complex.dist_eq]
    exact hnorm.trans_lt hrEps
  obtain ⟨hfactorz, hpnez, hqfloorz⟩ := hepsLocal hzdist
  have hzright : sigma < z.re := by rw [hzre]; linarith
  have hzone : z ≠ 1 := by
    intro hz1
    have hre := congrArg Complex.re hz1
    rw [hzre] at hre
    simp only [one_re] at hre
    nlinarith
  have hcanonical := hidentity z hzright
  simp only [zetaResidueUnit, Function.update_of_ne hzone] at hcanonical
  have hcancel : G z * riemannZeta z = Complex.Gamma z := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hzone)
    calc
      (G z * riemannZeta z) * (z - 1) =
          G z * ((z - 1) * riemannZeta z) := by ring
      _ = Complex.Gamma z * (z - 1) := hcanonical
  have hscaled : G z * (z - rho) ^ n = q z := by
    apply (eq_div_iff hpnez).2
    calc
      (G z * (z - rho) ^ n) * p z =
          G z * ((z - rho) ^ n * p z) := by ring
      _ = G z * riemannZeta z := by rw [hfactorz]
      _ = Complex.Gamma z := hcancel
  have hnormPow : ‖z - rho‖ ^ n ≤ 2 ^ n * r ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm n
  have hprod : ‖q rho‖ / 2 ≤ ‖G z‖ * (2 ^ n * r ^ n) := by
    calc
      ‖q rho‖ / 2 ≤ ‖q z‖ := hqfloorz
      _ = ‖G z‖ * ‖z - rho‖ ^ n := by
        rw [← hscaled, norm_mul, norm_pow]
      _ ≤ ‖G z‖ * (2 ^ n * r ^ n) :=
        mul_le_mul_of_nonneg_left hnormPow (norm_nonneg _)
  change ‖q rho‖ / 2 ^ (n + 1) / r ^ n ≤ ‖G z‖
  have hrn : 0 < r ^ n := pow_pos hr n
  have h2n : 0 < (2 : ℝ) ^ n := by positivity
  rw [div_le_iff₀ hrn, div_le_iff₀ (by positivity), pow_succ]
  nlinarith

/-- A uniform finite-section Gamma--Hankel energy ceiling on one line passes, by Fatou, to the
infinite logarithmic Möbius source with the same ceiling. -/
theorem memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    {sigma B : ℝ} (hsigma : 0 < sigma)
    (hB : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N (2 * sigma) ≤ B) :
    MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume ∧
      (∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2) ≤ B := by
  have hB0 : 0 ≤ B :=
    (finiteMobiusGammaHankelEnergy_nonneg 0 (by linarith : 0 < 2 * sigma)).trans (hB 0)
  let C₂ : ℝ≥0∞ := ENNReal.ofReal (B ^ (2 : ℝ)⁻¹)
  have hbound : ∀ N : ℕ,
      eLpNorm (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) 2 volume ≤ C₂ := by
    intro N
    have hmem := mobiusLaplaceFiniteSectionLogMellinLineSource_memLp_two N hsigma
    rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, C₂]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow
    · exact integral_nonneg fun _ => sq_nonneg _
    · rw [integral_norm_sq_mobiusLaplaceFiniteSectionLogMellinLineSource N hsigma]
      exact hB N
    · positivity
  have hmeas : ∀ N : ℕ,
      AEStronglyMeasurable (mobiusLaplaceFiniteSectionLogMellinLineSource N sigma) volume :=
    fun N => (continuous_mobiusLaplaceFiniteSectionLogMellinLineSource N sigma).aestronglyMeasurable
  have htend : ∀ᵐ u : ℝ ∂volume,
      Tendsto (fun N : ℕ => mobiusLaplaceFiniteSectionLogMellinLineSource N sigma u) atTop
        (nhds (mobiusLaplaceLogMellinLineSource sigma u)) :=
    Filter.Eventually.of_forall fun u =>
      tendsto_mobiusLaplaceFiniteSectionLogMellinLineSource_atTop sigma u
  have hnorm := MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (p := (2 : ℝ≥0∞)) (Filter.Eventually.of_forall hbound) hmeas htend
  have hmem : MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume :=
    ⟨(continuous_mobiusLaplaceLogMellinLineSource sigma).aestronglyMeasurable,
      hnorm.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hmem, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top] at hnorm
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, C₂] at hnorm
  have hI0 : 0 ≤ ∫ u : ℝ, ‖mobiusLaplaceLogMellinLineSource sigma u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hroot := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hnorm
  exact (Real.rpow_le_rpow_iff hI0 hB0 (by norm_num)).mp hroot

/-- **Power-aperture ceiling of exponent `k`.**  On the lines `1/2 < σ < σ₀` the finite Möbius
Gamma--Hankel energies are bounded by `C/(2σ-1)^k`, uniformly in the cutoff. -/
def MobiusGammaHankelPowerApertureCeiling (k : ℕ) : Prop :=
  ∃ C sigma₀ : ℝ, 1 / 2 < sigma₀ ∧
    ∀ sigma : ℝ, 1 / 2 < sigma → sigma < sigma₀ →
      ∀ N : ℕ, finiteMobiusGammaHankelEnergy N (2 * sigma) ≤ C / (2 * sigma - 1) ^ k

/-- **Möbius sub-orthogonality near the critical line.**  For every exponent `r = 2σ` in
`(1, 2σ₀)` and every cutoff, the signed off-diagonal Möbius covariance is nonpositive. -/
def MobiusGammaHankelSubOrthogonal : Prop :=
  ∃ sigma₀ : ℝ, 1 / 2 < sigma₀ ∧
    ∀ sigma : ℝ, 1 / 2 < sigma → sigma < sigma₀ →
      ∀ N : ℕ, finiteMobiusGammaHankelOffDiagonalCovariance N (2 * sigma) ≤ 0

/-- A power-aperture ceiling gives finite logarithmic energy on every line `1/2 < σ < σ₀`. -/
theorem memLp_mobiusLaplaceLogMellinLineSource_of_powerApertureCeiling
    {k : ℕ} {C sigma₀ : ℝ}
    (hceil : ∀ sigma : ℝ, 1 / 2 < sigma → sigma < sigma₀ →
      ∀ N : ℕ, finiteMobiusGammaHankelEnergy N (2 * sigma) ≤ C / (2 * sigma - 1) ^ k)
    {sigma : ℝ} (hlo : 1 / 2 < sigma) (hhi : sigma < sigma₀) :
    MemLp (mobiusLaplaceLogMellinLineSource sigma) 2 volume :=
  (memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    (by linarith) (hceil sigma hlo hhi)).1

/-- A power-aperture ceiling forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_powerApertureCeiling {k : ℕ}
    (h : MobiusGammaHankelPowerApertureCeiling k) : RiemannHypothesis := by
  obtain ⟨C, sigma₀, hsigma₀, hceil⟩ := h
  apply mobiusLaplaceCofinalStrictRightEnergyFinite_implies_riemannHypothesis
  intro ε hε
  let sigma : ℝ := 1 / 2 + min ε (sigma₀ - 1 / 2) / 2
  have hmin : 0 < min ε (sigma₀ - 1 / 2) := lt_min hε (by linarith)
  have hlo : 1 / 2 < sigma := by dsimp only [sigma]; linarith
  have hε' : sigma < 1 / 2 + ε := by
    have := min_le_left ε (sigma₀ - 1 / 2)
    dsimp only [sigma]
    linarith
  have hhi : sigma < sigma₀ := by
    have := min_le_right ε (sigma₀ - 1 / 2)
    dsimp only [sigma]
    linarith
  exact ⟨sigma, hlo, hε',
    memLp_mobiusLaplaceLogMellinLineSource_of_powerApertureCeiling hceil hlo hhi⟩

/-- Under a power-aperture ceiling the canonical Mellin identity holds on the whole open
half-plane `Re z > 1/2`. -/
theorem mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_powerApertureCeiling
    {k : ℕ} {C sigma₀ : ℝ} (hsigma₀ : 1 / 2 < sigma₀)
    (hceil : ∀ sigma : ℝ, 1 / 2 < sigma → sigma < sigma₀ →
      ∀ N : ℕ, finiteMobiusGammaHankelEnergy N (2 * sigma) ≤ C / (2 * sigma - 1) ^ k)
    (z : ℂ) (hz : 1 / 2 < z.re) :
    mellin mobiusDiscreteLaplaceTransform z * zetaResidueUnit z =
      Complex.Gamma z * (z - 1) := by
  let sigma : ℝ := min ((1 / 2 + z.re) / 2) ((1 / 2 + sigma₀) / 2)
  have hlo : 1 / 2 < sigma := lt_min (by linarith) (by linarith)
  have hhi : sigma < sigma₀ := (min_le_right _ _).trans_lt (by linarith)
  have hzs : sigma < z.re := (min_le_left _ _).trans_lt (by linarith)
  exact mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base
    (by linarith) (memLp_mobiusLaplaceLogMellinLineSource_of_powerApertureCeiling
      hceil hlo hhi) z hzs

/-- **Multiplicity law.**  Under a power-aperture ceiling of exponent `k`, every zero of `ζ` in
the critical strip has analytic order `n` with `2n ≤ k + 1`. -/
theorem two_mul_analyticOrderAt_toNat_le_of_powerApertureCeiling {k : ℕ}
    (h : MobiusGammaHankelPowerApertureCeiling k)
    {rho : ℂ} (hzero : riemannZeta rho = 0) (hpos : 0 < rho.re) (hlt : rho.re < 1) :
    2 * (analyticOrderAt riemannZeta rho).toNat ≤ k + 1 := by
  have hRH := riemannHypothesis_of_powerApertureCeiling h
  obtain ⟨C, sigma₀, hsigma₀, hceil⟩ := h
  have hrhoOne : rho ≠ 1 := by
    intro h1
    rw [h1, one_re] at hlt
    exact lt_irrefl _ hlt
  have hnotTrivial : ¬∃ n : ℕ, rho = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hline : rho.re = 1 / 2 := hRH rho hzero hnotTrivial hrhoOne
  have hidentity : ∀ z : ℂ, 1 / 2 < z.re →
      mellin mobiusDiscreteLaplaceTransform z * zetaResidueUnit z =
        Complex.Gamma z * (z - 1) :=
    mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_powerApertureCeiling
      hsigma₀ hceil
  obtain ⟨hn1, c, hc, delta, hdelta, hfloor⟩ :=
    exists_order_vertical_window_floor_of_canonical_identity
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
      hline hzero hidentity
  set n : ℕ := (analyticOrderAt riemannZeta rho).toNat with hndef
  by_contra hbig
  have hexp : k + 2 ≤ 2 * n := by omega
  let B : ℝ := |C| + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hCB : C ≤ B := by dsimp only [B]; linarith [le_abs_self C]
  let r : ℝ := min (delta / 2) (min ((sigma₀ - 1 / 2) / 2)
    (min (1 / 2) (c ^ 2 / (2 * (Real.pi * B)))))
  have hpiB : 0 < Real.pi * B := mul_pos Real.pi_pos hB
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (by linarith) (lt_min (by linarith)
      (lt_min (by norm_num) (div_pos (sq_pos_of_pos hc) (by positivity))))
  have hrdelta : r < delta := (min_le_left _ _).trans_lt (by linarith)
  have hrsig : r < sigma₀ - 1 / 2 :=
    (le_trans (min_le_right _ _) (min_le_left _ _)).trans_lt (by linarith)
  have hrhalf : r ≤ 1 / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrc : r ≤ c ^ 2 / (2 * (Real.pi * B)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hbaseLo : 1 / 2 < 1 / 2 + r / 2 := by linarith
  have hbaseHi : 1 / 2 + r / 2 < sigma₀ := by linarith
  have hbase :=
    memLp_mobiusLaplaceLogMellinLineSource_of_powerApertureCeiling hceil hbaseLo hbaseHi
  have hsplit : 1 / 2 + r / 2 + r / 2 = 1 / 2 + r := by ring
  have h2 : MemLp (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) 2 volume := by
    have := mobiusLaplaceLogMellinLineSource_memLp_two_of_base hbase (by linarith : 0 < r / 2)
    rwa [hsplit] at this
  have h1 : Integrable (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) volume := by
    have := integrable_mobiusLaplaceLogMellinLineSource_of_base hbase (by linarith : 0 < r / 2)
    rwa [hsplit] at this
  have htargetLo : 1 / 2 < 1 / 2 + r := by linarith
  have htargetHi : 1 / 2 + r < sigma₀ := by linarith
  have henergy :=
    (memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
      (by linarith : 0 < 1 / 2 + r) (hceil (1 / 2 + r) htargetLo htargetHi)).2
  have hden : 2 * (1 / 2 + r) - 1 = 2 * r := by ring
  rw [hden] at henergy
  have hlineInt : Integrable (fun t : ℝ =>
      ‖mellin mobiusDiscreteLaplaceTransform
        ((((1 / 2 : ℝ) + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) :=
    integrable_norm_sq_mellin_line_of_logMellinLineSource h1 h2
  -- the order-`n` floor, written as a `c' / r` floor with `c' = c / r^(n-1)`
  have hsplitPow : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hn1]
  let A : ℝ := c / r ^ (n - 1)
  have hA0 : 0 ≤ A := div_nonneg hc.le (pow_nonneg hr.le _)
  have hfloorA : ∀ t : ℝ, |t - rho.im| ≤ r →
      A / r ≤ ‖mellin mobiusDiscreteLaplaceTransform
        ((((1 / 2 : ℝ) + r : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    intro t ht
    have := hfloor r hr hrdelta t ht
    rwa [hsplitPow, ← div_div] at this
  have hlower := integral_norm_sq_ge_two_mul_sq_div_of_window_floor
    hr hA0 hlineInt hfloorA
  have hplancherel := integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_eq h1 h2
  have hupper :
      (∫ t : ℝ, ‖mellin mobiusDiscreteLaplaceTransform
        ((((1 / 2 : ℝ) + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        2 * Real.pi * (C / (2 * r) ^ k) := by
    rw [hplancherel]
    exact mul_le_mul_of_nonneg_left henergy (by positivity)
  have hchain := hlower.trans hupper
  -- `2 A² / r ≤ 2π C / (2r)^k` with `A r^(n-1) = c` forces `c² ≤ π B r`.
  have h2r : 0 < (2 * r) ^ k := by positivity
  have hstep : 2 * A ^ 2 * (2 * r) ^ k ≤ 2 * Real.pi * C * r := by
    rw [div_le_iff₀ hr] at hchain
    calc
      2 * A ^ 2 * (2 * r) ^ k = (2 * A ^ 2 / r * r) * (2 * r) ^ k := by
        field_simp
      _ ≤ (2 * Real.pi * (C / (2 * r) ^ k) * r) * (2 * r) ^ k := by
        apply mul_le_mul_of_nonneg_right _ h2r.le
        calc
          2 * A ^ 2 / r * r = 2 * A ^ 2 := by field_simp
          _ ≤ 2 * Real.pi * (C / (2 * r) ^ k) * r := hchain
      _ = 2 * Real.pi * C * r := by field_simp
  have hAr : A * r ^ (n - 1) = c := by
    dsimp only [A]
    field_simp
  have hcsq : c ^ 2 = A ^ 2 * r ^ (2 * (n - 1)) := by
    rw [← hAr, mul_pow, ← pow_mul, mul_comm (n - 1) 2]
  have hpowSplit : r ^ (2 * (n - 1) + 1) = r ^ k * r ^ (2 * n - 1 - k) := by
    rw [← pow_add]
    congr 1
    omega
  have he1 : 1 ≤ 2 * n - 1 - k := by omega
  have hre : r ^ (2 * n - 1 - k) ≤ r := by
    calc
      r ^ (2 * n - 1 - k) ≤ r ^ 1 :=
        pow_le_pow_of_le_one hr.le (by linarith) he1
      _ = r := pow_one r
  have hrk : 0 < r ^ k := pow_pos hr k
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hmain : c ^ 2 * 2 ^ k * r ^ k ≤ Real.pi * B * r ^ k * r := by
    have hA2 : A ^ 2 * (2 ^ k * r ^ k) ≤ Real.pi * C * r := by
      have := hstep
      rw [mul_pow] at this
      linarith
    have hmul := mul_le_mul_of_nonneg_right hA2 (pow_nonneg hr.le (2 * (n - 1)))
    have hlhs : A ^ 2 * (2 ^ k * r ^ k) * r ^ (2 * (n - 1)) = c ^ 2 * 2 ^ k * r ^ k := by
      rw [hcsq]
      ring
    have hrhs : Real.pi * C * r * r ^ (2 * (n - 1)) = Real.pi * C * (r ^ k * r ^ (2 * n - 1 - k)) := by
      rw [← hpowSplit, pow_succ]
      ring
    rw [hlhs, hrhs] at hmul
    have hC' : Real.pi * C * (r ^ k * r ^ (2 * n - 1 - k)) ≤
        Real.pi * B * (r ^ k * r ^ (2 * n - 1 - k)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCB Real.pi_pos.le)
        (by positivity)
    have hB' : Real.pi * B * (r ^ k * r ^ (2 * n - 1 - k)) ≤ Real.pi * B * (r ^ k * r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hre hrk.le) hpiB.le
    calc
      c ^ 2 * 2 ^ k * r ^ k ≤ Real.pi * B * (r ^ k * r) := hmul.trans (hC'.trans hB')
      _ = Real.pi * B * r ^ k * r := by ring
  have hfinal : c ^ 2 ≤ Real.pi * B * r := by
    have hdiv : c ^ 2 * 2 ^ k ≤ Real.pi * B * r := by
      have := hmain
      rw [show Real.pi * B * r ^ k * r = (Real.pi * B * r) * r ^ k by ring,
        mul_assoc] at this
      have h' : c ^ 2 * 2 ^ k * r ^ k ≤ Real.pi * B * r * r ^ k := by linarith
      exact le_of_mul_le_mul_right h' hrk
    have hc2 : c ^ 2 ≤ c ^ 2 * 2 ^ k := le_mul_of_one_le_right (sq_nonneg c) h2k
    linarith
  have hrsmall : Real.pi * B * r ≤ c ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left hrc hpiB.le
    calc
      Real.pi * B * r ≤ Real.pi * B * (c ^ 2 / (2 * (Real.pi * B))) := this
      _ = c ^ 2 / 2 := by field_simp
  have hcpos : 0 < c ^ 2 := sq_pos_of_pos hc
  linarith

/-- An analytic zero of order exactly one has nonzero derivative. -/
theorem deriv_riemannZeta_ne_zero_of_analyticOrderAt_eq_one
    {rho : ℂ} (hrhoOne : rho ≠ 1) (horder : analyticOrderAt riemannZeta rho = 1) :
    deriv riemannZeta rho ≠ 0 := by
  have hanalytic : AnalyticAt ℂ riemannZeta rho := analyticOn_riemannZeta rho hrhoOne
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    (hanalytic.analyticOrderAt_eq_natCast (n := 1)).mp (by simpa using horder)
  have hderivEq : deriv riemannZeta rho = deriv (fun z => (z - rho) * g z) rho := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hfactor] with z hz
    simpa [smul_eq_mul] using hz
  have hhas : HasDerivAt (fun z => (z - rho) * g z)
      (1 * g rho + (rho - rho) * deriv g rho) rho :=
    ((hasDerivAt_id rho).sub_const rho).mul hg.differentiableAt.hasDerivAt
  rw [hderivEq, hhas.deriv]
  simpa using hg0

/-- **Simplicity from the reciprocal-aperture ceiling.**  With exponent `k = 1`, every zero of
`ζ` in the critical strip is simple. -/
theorem analyticOrderAt_riemannZeta_eq_one_of_reciprocalApertureCeiling
    (h : MobiusGammaHankelPowerApertureCeiling 1)
    {rho : ℂ} (hzero : riemannZeta rho = 0) (hpos : 0 < rho.re) (hlt : rho.re < 1) :
    analyticOrderAt riemannZeta rho = 1 := by
  have hle := two_mul_analyticOrderAt_toNat_le_of_powerApertureCeiling h hzero hpos hlt
  have hrhoOne : rho ≠ 1 := by
    intro h1
    rw [h1, one_re] at hlt
    exact lt_irrefl _ hlt
  have hstrip : 0 < rho.re ∧ rho.re < 1 := ⟨hpos, hlt⟩
  have horderFinite : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip]
    exact xi_orderAt_ne_top rho
  have hne : analyticOrderAt riemannZeta rho ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta rho hrhoOne, hzero⟩
  have hncoe := ENat.coe_toNat horderFinite
  have hn0 : (analyticOrderAt riemannZeta rho).toNat ≠ 0 := by
    intro h0
    apply hne
    rw [← hncoe, h0]
    simp
  have hn : (analyticOrderAt riemannZeta rho).toNat = 1 := by omega
  rw [← hncoe, hn]
  simp

/-- **Sub-orthogonality gives the reciprocal-aperture ceiling.**  The diagonal Möbius energy is at
most `2/(r-1)` for `1 < r ≤ 2`, so a nonpositive off-diagonal covariance leaves the full energy
under the same ceiling. -/
theorem reciprocalApertureCeiling_of_subOrthogonal
    (h : MobiusGammaHankelSubOrthogonal) : MobiusGammaHankelPowerApertureCeiling 1 := by
  obtain ⟨sigma₀, hsigma₀, hsub⟩ := h
  refine ⟨2, min sigma₀ 1, lt_min hsigma₀ (by norm_num), ?_⟩
  intro sigma hlo hhi N
  have hhi₀ : sigma < sigma₀ := hhi.trans_le (min_le_left _ _)
  have hhi₁ : sigma < 1 := hhi.trans_le (min_le_right _ _)
  set r : ℝ := 2 * sigma with hrdef
  have hr1 : 1 < r := by rw [hrdef]; linarith
  have hr2 : r ≤ 2 := by rw [hrdef]; linarith
  have hGamma : Real.Gamma r ≤ 1 := by
    have := Real.convexOn_Gamma.le_max_of_mem_Icc (x := 1) (y := 2) (z := r)
      (by norm_num) (by norm_num) ⟨hr1.le, hr2⟩
    simpa [Real.Gamma_one, Real.Gamma_two] using this
  have hGamma0 : 0 < Real.Gamma r := Real.Gamma_pos_of_pos (by linarith)
  have hpartial : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, (1 / |(k : ℝ) + 1| ^ r) ≤ r / (r - 1) := by
    intro n
    have hterm : ∀ k : ℕ, 1 / |(k : ℝ) + 1| ^ r = ((k : ℝ) + 1) ^ (-r) := by
      intro k
      rw [abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1),
        Real.rpow_neg (by positivity), one_div]
    simp_rw [hterm]
    rcases n with _ | m
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact div_nonneg (by linarith) (by linarith)
    · rw [Finset.sum_range_succ']
      have htail := GaloisForLFunctions.sum_shift_rpow_tail_le hr1 0 m
      have hcongr : ∀ i ∈ Finset.range m,
          (((i + 1 : ℕ) : ℝ) + 1) ^ (-r) = (((0 : ℕ) : ℝ) + 1 + (i : ℝ) + 1) ^ (-r) := by
        intro i _
        push_cast
        ring_nf
      rw [Finset.sum_congr rfl hcongr]
      simp only [Nat.cast_zero, zero_add, Real.one_rpow] at htail ⊢
      have hsum : ∑ i ∈ Finset.range m, (1 + (i : ℝ) + 1) ^ (-r) ≤ 1 / (r - 1) := by
        simpa using htail
      have hsplitr : r / (r - 1) = 1 / (r - 1) + 1 := by
        rw [div_add_one (by linarith : r - 1 ≠ 0)]
        congr 1
        ring
      rw [hsplitr]
      linarith
  have htsum : (∑' n : ℕ, mobiusGammaHankelDiagonalMajorant r n) ≤
      Real.Gamma r * (r / (r - 1)) := by
    unfold mobiusGammaHankelDiagonalMajorant
    rw [tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ hGamma0.le
    exact Real.tsum_le_of_sum_range_le (fun n => by positivity) hpartial
  have hdiag : finiteMobiusGammaHankelDiagonalEnergy N r ≤ 2 / (r - 1) := by
    have h1 := finiteMobiusGammaHankelDiagonalEnergy_le_tsum N hr1
    have hr10 : 0 < r - 1 := by linarith
    have hbound : Real.Gamma r * (r / (r - 1)) ≤ 2 / (r - 1) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hr10]
      nlinarith
    linarith
  have hoff := hsub sigma hlo hhi₀ N
  rw [finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal, pow_one]
  have : finiteMobiusGammaHankelDiagonalEnergy N r +
      finiteMobiusGammaHankelOffDiagonalCovariance N r ≤ 2 / (r - 1) := by linarith
  simpa [hrdef] using this

/-- **Möbius sub-orthogonality implies the Riemann hypothesis and simplicity of every nontrivial
zero.**  The hypothesis is the Gamma--Hankel analogue of the (false) Mertens inequality
`M(N)² ≤ #{n ≤ N squarefree}`. -/
theorem riemannHypothesis_and_simple_zeros_of_subOrthogonal
    (h : MobiusGammaHankelSubOrthogonal) :
    RiemannHypothesis ∧
      ∀ rho : ℂ, riemannZeta rho = 0 → 0 < rho.re → rho.re < 1 →
        analyticOrderAt riemannZeta rho = 1 ∧ deriv riemannZeta rho ≠ 0 := by
  have hceil := reciprocalApertureCeiling_of_subOrthogonal h
  refine ⟨riemannHypothesis_of_powerApertureCeiling hceil, ?_⟩
  intro rho hzero hpos hlt
  have horder :=
    analyticOrderAt_riemannZeta_eq_one_of_reciprocalApertureCeiling hceil hzero hpos hlt
  have hrhoOne : rho ≠ 1 := by
    intro h1
    rw [h1, one_re] at hlt
    exact lt_irrefl _ hlt
  exact ⟨horder, deriv_riemannZeta_ne_zero_of_analyticOrderAt_eq_one hrhoOne horder⟩

end RHTower
