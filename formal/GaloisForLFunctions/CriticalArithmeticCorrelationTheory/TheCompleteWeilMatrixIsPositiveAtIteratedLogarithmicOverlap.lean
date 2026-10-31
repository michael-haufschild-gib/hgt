import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteConductorResidualsAreUniformOnLogarithmicFamilies
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NegativeWeilPacketsHaveExponentialConductorCutoffs
import GaloisForLFunctions.HTGeometry.RpowExpAsymptotics

/-!
# Complete Weil positivity at growing iterated-logarithmic overlap

Exponential conductor confinement becomes logarithmic conductor growth when
`c ≤ (log log N)^α`, `α < 1/16`. The common residual bound and polynomial
conductor floor then make the total coordinate error tend to zero. Finite
Ramanujan coordinate mass excludes every nonpositive eigenvector, retaining
the literal prime, archimedean and polar sources.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell ArithmeticElectrostatics

/-- Exponential conductor cutoffs at subcritical iterated-logarithmic overlap are subpowers of the logarithm. -/
theorem eventually_iteratedLog_cutoff_le_log_rpow {α δ : ℝ}
    (hα : 0 < α) (hα16 : α < 1 / 16) (hδ : 0 < δ)
    {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log N) ^ α →
      Real.exp (D * (C * c ^ 16 + 1)) + 2 ≤ Real.log N ^ δ := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim := Real.tendsto_log_atTop.comp hLlim
  have hb : 16 * α < 1 := by linarith only [hα16]
  have hb0 : 0 ≤ 16 * α := by positivity
  let F := D * (C + 1) + Real.log 3
  have hsmall := hllim.eventually (HTGeometry.eventually_mul_rpow_le F hb hδ)
  filter_upwards [hsmall, hllim.eventually_ge_atTop 1, hLlim.eventually_gt_atTop 0]
    with N hsmallN hll hL
  intro c hc hcup
  have hc0 := zero_le_one.trans hc
  have hll0 : 0 ≤ Real.log (Real.log (N : ℝ)) := zero_le_one.trans hll
  have hpow1 : 1 ≤ Real.log (Real.log (N : ℝ)) ^ (16 * α) :=
    Real.one_le_rpow hll hb0
  have hc16 : c ^ 16 ≤ Real.log (Real.log (N : ℝ)) ^ (16 * α) := by
    have hh := pow_le_pow_left₀ hc0 hcup 16
    have he : (Real.log (Real.log (N : ℝ)) ^ α) ^ (16 : ℕ) =
        Real.log (Real.log (N : ℝ)) ^ (16 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hll0]
      congr 1
      norm_num [mul_comm]
    exact hh.trans_eq he
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hexp0 : 0 ≤ D * (C * c ^ 16 + 1) := by positivity
  have hexp1 := Real.one_le_exp_iff.mpr hexp0
  have he : Real.log 3 + D * (C * c ^ 16 + 1) ≤
      δ * Real.log (Real.log (N : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hc16 (mul_nonneg hD.le hC.le)
    have h2 := mul_le_mul_of_nonneg_left hpow1 hD.le
    have h3 := mul_le_mul_of_nonneg_left hpow1 hlog3
    dsimp only [F, Function.comp_def] at hsmallN
    nlinarith only [h1, h2, h3, hsmallN]
  calc
    _ ≤ 3 * Real.exp (D * (C * c ^ 16 + 1)) := by linarith only [hexp1]
    _ = Real.exp (Real.log 3 + D * (C * c ^ 16 + 1)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ Real.exp (δ * Real.log (Real.log (N : ℝ))) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.rpow_def_of_pos hL]; congr 1; ring

/-- The overlap itself is smaller than every positive power of the horizon logarithm. -/
theorem eventually_iteratedLog_overlap_le_log_rpow {α δ : ℝ}
    (hα : α ≤ 1) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, c ≤ Real.log (Real.log N) ^ α →
      c ≤ Real.log N ^ δ := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := hLlim.eventually
    ((isLittleO_log_rpow_atTop hδ).bound (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, (Real.tendsto_log_atTop.comp hLlim).eventually_ge_atTop 1,
    hLlim.eventually_ge_atTop 1] with N hsmallN hll hL
  intro c hc
  have hpower := Real.rpow_le_rpow_of_exponent_le hll hα
  rw [Real.rpow_one] at hpower
  have hL0 := zero_le_one.trans hL
  have hlog : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) ^ δ := by
    have habs : |Real.log (Real.log (N : ℝ))| ≤ Real.log (N : ℝ) ^ δ := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hL0 _), one_mul] using hsmallN
    exact (le_abs_self _).trans habs
  exact hc.trans (hpower.trans hlog)

private theorem uniform_log_div_sq_le_inv_log {t : ℝ} (ht : 0 < t) (hlog : 0 < Real.log t) :
    (Real.log t / t) ^ 2 ≤ 1 / Real.log t := by
  have h := Real.pow_div_factorial_le_exp (2 * Real.log t) (by positivity) 3
  have he : Real.exp (2 * Real.log t) = t ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log ht]
    ring
  rw [he] at h
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  have hc : Real.log t ^ 3 ≤ t ^ 2 := by
    nlinarith only [h, pow_nonneg hlog.le 3]
  rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos ht) hlog]
  nlinarith only [hc]

private theorem uniform_complete_rate_le {c : ℝ} (hc : 1 ≤ c) {N : ℕ}
    (hN : 1 ≤ N) (hL : 1 ≤ Real.log (N : ℝ)) :
    c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
      c ^ 3 / Real.sqrt (Real.log N) ≤ 3 * c ^ 10 / Real.sqrt (Real.log N) := by
  have hc0 := zero_le_one.trans hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 := zero_lt_one.trans_le hL
  have hs1 : 1 ≤ Real.sqrt (Real.log (N : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hs0 := zero_lt_one.trans_le hs1
  have hsL : Real.sqrt (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    have he := Real.sq_sqrt hL0.le
    nlinarith only [he, hs1]
  have h5 := div_le_div_of_nonneg_right
    (pow_le_pow_right₀ hc (by norm_num : 5 ≤ 10)) hL0.le
  have h10 := div_le_div_of_nonneg_left (pow_nonneg hc0 10) hs0 hsL
  have h2 := mul_le_mul_of_nonneg_left (uniform_log_div_sq_le_inv_log hN0 hL0)
    (pow_nonneg hc0 10)
  rw [mul_one_div] at h2
  have h3 := div_le_div_of_nonneg_right
    (pow_le_pow_right₀ hc (by norm_num : 3 ≤ 10)) hs0.le
  have h1 := h5.trans h10
  have h2' := h2.trans h10
  calc
    _ ≤ c ^ 10 / Real.sqrt (Real.log N) + c ^ 10 / Real.sqrt (Real.log N) +
        c ^ 10 / Real.sqrt (Real.log N) := add_le_add (add_le_add h1 h2') h3
    _ = _ := by ring

private theorem uniform_conductor_budget_le_rpow {K a c : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hc : 1 ≤ c) {N Q : ℕ}
    (hN : 1 ≤ N) (hL : 1 ≤ Real.log (N : ℝ))
    (hQ : (Q : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 100 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ) ^ (1 / 100 : ℝ)) :
    K * (Q : ℝ) ^ 5 * (c ^ 5 / Real.log N +
      c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 3 / Real.sqrt (Real.log N)) /
      (a / c ^ 7) ^ 2 ≤
      (3 * K / a ^ 2) * Real.log (N : ℝ) ^ (-(21 / 100 : ℝ)) := by
  let L := Real.log (N : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hc0 := zero_lt_one.trans_le hc
  have hs0 := Real.sqrt_pos.mpr hL0
  have hQ5 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 5
  have hc24 := pow_le_pow_left₀ hc0.le hcL 24
  have hhalf : L ^ (1 / 2 : ℝ) = Real.sqrt L := by
    simpa only [Real.rpow_one] using Real.rpow_div_two_eq_sqrt 1 hL0.le
  have he : (L ^ (1 / 100 : ℝ)) ^ (5 : ℕ) *
      (L ^ (1 / 100 : ℝ)) ^ (24 : ℕ) / Real.sqrt L = L ^ (-(21 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, ← hhalf, ← Real.rpow_sub hL0]
    norm_num
  calc
    _ ≤ K * (Q : ℝ) ^ 5 * (3 * c ^ 10 / Real.sqrt L) / (a / c ^ 7) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (uniform_complete_rate_le hc hN hL) (by positivity))
        (sq_nonneg _)
    _ = (3 * K / a ^ 2) * ((Q : ℝ) ^ 5 * c ^ 24 / Real.sqrt L) := by
      field_simp [ha.ne', hc0.ne', hs0.ne']
    _ ≤ (3 * K / a ^ 2) *
        ((L ^ (1 / 100 : ℝ)) ^ (5 : ℕ) * (L ^ (1 / 100 : ℝ)) ^ (24 : ℕ) /
          Real.sqrt L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right
        (mul_le_mul hQ5 hc24 (by positivity) (by positivity)) hs0.le
    _ = _ := by rw [he]

private theorem eventually_const_mul_log_nat_le (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * Real.log (N : ℝ) ≤ N := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLlim.eventually (HTGeometry.eventually_mul_rpow_le_exp_rpow C
    (c := 1) (δ := 1) (p := 1) zero_lt_one zero_lt_one), eventually_ge_atTop 1]
    with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  simpa only [Real.rpow_one, one_mul, Real.exp_log hN0] using hN

/-- Exponential confinement and common conductor residuals transfer polynomial
spectral floors to the full matrix at iterated-logarithmic overlap. -/
theorem eventually_matrix_posDef_iteratedLog_of_conductor_bounds
    (family : ℝ → (N : ℕ) → Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
    (energy : ℝ → ℕ → ℝ) (hherm : ∀ c N, (family c N).IsHermitian)
    {a : ℝ} (ha : 0 < a)
    (hfloor : ∀ c : ℝ, 1 ≤ c → ∀ m : ℕ, 0 < m → a / c ^ 7 ≤ energy c m)
    (hconfinement : ∃ C D H : ℝ, 0 < C ∧ 0 < D ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∃ R : ℕ,
        (R : ℝ) ≤ Real.exp (D * (C * c ^ 16 + 1)) ∧
        ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
          ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ‖x‖ = 1 →
            ⟪Matrix.toEuclideanLin (family c N) x, x⟫ ≤ 0 →
            ∃ b : ℕ → ℝ, (∑ n ∈ Icc 1 N,
              (primeHorizonExtension x n -
                ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2) ≤ 1 / 4)
    (hresidual : ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (family c N) (normalizedRamanujanHorizonVector m N) -
          energy c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K * (m : ℝ) ^ 4 * (c ^ 5 / Real.log N +
            c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 3 / Real.sqrt (Real.log N)))
    {α : ℝ} (hα : 0 < α) (hα16 : α < 1 / 16) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      c ≤ Real.log (Real.log (N : ℝ)) ^ α → (family c N).PosDef := by
  classical
  obtain ⟨C, D, H, hC, hD, hH, hcut⟩ := hconfinement
  obtain ⟨K, hK, hres⟩ := hresidual
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbudgetlim : Tendsto
      (fun N : ℕ => (3 * K / a ^ 2) * Real.log (N : ℝ) ^ (-(21 / 100 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 21 / 100)).comp hLlim).const_mul
        (3 * K / a ^ 2)
  filter_upwards [hres (1 / 100) (by norm_num),
    eventually_iteratedLog_cutoff_le_log_rpow hα hα16 (by norm_num : (0 : ℝ) < 1 / 100) hC hD,
    eventually_iteratedLog_overlap_le_log_rpow (by linarith only [hα16] : α ≤ 1)
      (by norm_num : (0 : ℝ) < 1 / 100),
    eventually_const_mul_log_nat_le H,
    eventually_const_mul_log_nat_le (4 * (Real.exp 1 + 3) ^ 2),
    hbudgetlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 36),
    hLlim.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with N hresN hcutN hcN hHN hwidthN hbudgetN hL hN
  intro c hc hcup
  have hc0 := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 := zero_lt_one.trans_le hL
  have hcL := hcN c hcup
  have hcpow (k : ℕ) (hk : k ≤ 100) : c ^ k ≤ Real.log (N : ℝ) := by
    have hp := pow_le_pow_left₀ hc0.le hcL k
    have he : (Real.log (N : ℝ) ^ (1 / 100 : ℝ)) ^ k =
        Real.log (N : ℝ) ^ ((k : ℝ) / 100) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    have hkle : (k : ℝ) / 100 ≤ 1 := by
      have hh : (k : ℝ) ≤ 100 := by exact_mod_cast hk
      linarith only [hh]
    exact (hp.trans_eq he).trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL hkle)
  have hcutH : H * c ^ 8 ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left (hcpow 8 (by norm_num)) hH.le).trans hHN
  have hwidth : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left (hcpow 2 (by norm_num)) (by positivity)).trans hwidthN
  obtain ⟨R, hR, happ⟩ := hcut c hc
  let Q := R + 2
  have hQ : 2 ≤ Q := by omega
  have hQL : (Q : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 100 : ℝ) := by
    have hh := hcutN c hc hcup
    dsimp only [Q]
    push_cast
    linarith only [hR, hh]
  have hQN : Q ^ 4 ≤ N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQL 4
    have he : (Real.log (N : ℝ) ^ (1 / 100 : ℝ)) ^ (4 : ℕ) =
        Real.log (N : ℝ) ^ (1 / 25 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
    have hpow : Real.log (N : ℝ) ^ (1 / 25 : ℝ) ≤ Real.log (N : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 25 : ℝ) ≤ 1)
    have hlog : Real.log (N : ℝ) ≤ N :=
      (Real.log_le_sub_one_of_pos hN0).trans (by linarith only)
    have hh := ((hp.trans_eq he).trans hpow).trans hlog
    exact_mod_cast hh
  apply matrix_posDef_of_uniform_conductor_budget
    (rate := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
      c ^ 3 / Real.sqrt (Real.log N))
    (hherm c N) (energy c) (div_pos ha (pow_pos hc0 7)) hK (by positivity)
    (by omega : R ≤ Q) hQ hQN
    (fun m hm => hfloor c hc m (mem_Icc.mp hm).1) (happ N hcutH)
  · intro m hm
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
    exact hresN m hm0 (hmQ.trans hQL) c hc hwidth
  · exact (uniform_conductor_budget_le_rpow hK ha hc hN hL hQL hcL).trans hbudgetN

/-- Every coefficient vector has positive complete Weil energy at prescribed
iterated-logarithmic overlap, uniformly below exponent `1/16`. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_iteratedLog
    {α : ℝ} (hα : 0 < α) (hα16 : α < 1 / 16) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      c ≤ Real.log (Real.log (N : ℝ)) ^ α →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  have ha : 0 < 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2) :=
    div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos) integral_tiltedUnitSpline_sq_pos
  exact eventually_matrix_posDef_iteratedLog_of_conductor_bounds
    (completeWeilMatrix tiltedUnitSpline) (completedConductorEnergy tiltedUnitSpline)
    (completeWeilMatrix_isHermitian tiltedUnitSpline) ha
    (fun c hc m hm => tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc hm)
    (exists_negative_completeWeil_exponential_conductor_cutoff (by norm_num : (0 : ℝ) < 1 / 4))
    exists_tiltedUnitSpline_uniform_conductor_residual_bound hα hα16

/-- The literal Weil quadratic form is nonnegative on every atomic coefficient family
through the same prescribed growing overlap range. -/
theorem eventually_tiltedUnitSpline_weilQuad_nonneg_iteratedLog
    {α : ℝ} (hα : 0 < α) (hα16 : α < 1 / 16) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      c ≤ Real.log (Real.log (N : ℝ)) ^ α → ∀ y : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N y (atomDilate tiltedUnitSpline (c / N))) := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilMatrix_posDef_iteratedLog hα hα16,
    eventually_ge_atTop 1] with N hpos hN
  intro c hc hcup y
  have hc0 := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc0 hN0
  have hM : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hquad : 0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (horizonProfileVector y N), horizonProfileVector y N⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN] at hquad
  have htest : atomicTest N (primeHorizonExtension (horizonProfileVector y N))
      (atomDilate tiltedUnitSpline (c / N)) =
      atomicTest N y (atomDilate tiltedUnitSpline (c / N)) := by
    funext u
    unfold atomicTest
    apply sum_congr rfl
    intro n hn
    have hcoe : primeHorizonExtension (horizonProfileVector y N) n = y n :=
      primeHorizonExtension_coe (horizonProfileVector y N) ⟨n, hn⟩
    rw [hcoe]
  rw [htest, div_nonneg_iff] at hquad
  rcases hquad with ⟨hq, -⟩ | ⟨-, hneg⟩
  · exact hq
  · linarith only [hM, hneg]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_iteratedLog
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_weilQuad_nonneg_iteratedLog
