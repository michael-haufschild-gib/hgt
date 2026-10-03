import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralExponentLaw
import GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.PrimeVacuumErrorTransfer

/-!
# The exponent of `ψ(x) - x` is exactly `Θ = sup Re ρ`

Unconditionally, with `Θ = zeroReSup`:
* for every `b < Θ`, `ψ(x) - x > x^b` and `ψ(x) - x < -x^b` for arbitrarily large `x` (Landau's
  argument through the one-sided power receivers; below `½` Littlewood gives more);
* for every `b > Θ`, `|ψ(x) - x| ≤ C x^b` for `x ≥ 1` (the generalized von Koch theorem of the
  corpus).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- **A lower power bound on the Chebyshev error moves every zero to the left of `½ + a`.** -/
theorem re_le_half_add_of_chebyshevError_ge_rpow {C a x₁ : ℝ} (hC : 0 ≤ C) (ha0 : 0 < a)
    (ha : a < 1 / 2) (hx₁1 : 1 < x₁)
    (hpow : ∀ t, x₁ ≤ t → -(C * t ^ (1 / 2 + a)) ≤ chebyshevError t) (q : XiZeroCopy) :
    (q.1 : ℂ).re ≤ 1 / 2 + a := by
  have htail : ∀ x, x₁ ≤ x →
      -(C * (x ^ (a - 1 / 2) / (1 / 2 - a))) ≤ ∫ t in Ioi x, chebyshevError t / t ^ 2 := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi x) :=
      integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi (by linarith))
    have hint2 : IntegrableOn (fun t : ℝ => -(C) * t ^ (a - 3 / 2)) (Ioi x) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul _
    have hmono := setIntegral_mono_on hint2 hint measurableSet_Ioi (fun t ht => by
      have ht0 : 0 < t := lt_trans hx0 ht
      have h1 := hpow t (le_trans hx (le_of_lt ht))
      have h2 : -(C) * t ^ (a - 3 / 2) = -(C * t ^ (1 / 2 + a)) / t ^ 2 := by
        rw [show a - 3 / 2 = (1 / 2 + a) - 2 by ring, Real.rpow_sub ht0, Real.rpow_two]
        ring
      rw [h2]
      exact div_le_div_of_nonneg_right h1 (by positivity))
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
      show a - 3 / 2 + 1 = a - 1 / 2 by ring] at hmono
    have hd : -x ^ (a - 1 / 2) / (a - 1 / 2) = x ^ (a - 1 / 2) / (1 / 2 - a) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    have hneg : -(C) * (-x ^ (a - 1 / 2) / (a - 1 / 2))
        = -(C * (x ^ (a - 1 / 2) / (1 / 2 - a))) := by
      rw [hd]; ring
    linarith
  -- the exponential growth bound for large lags
  set K := C / (1 / 2 - a) + 1 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ C / (1 / 2 - a) := div_nonneg hC (by linarith)
    linarith
  have hlarge : ∀ L, Real.log x₁ ≤ L → weilLagFunctionReal L ≤ K * Real.exp (a * L) := by
    intro L hL
    have hx1L : x₁ ≤ Real.exp L := by
      rw [← Real.exp_log (show 0 < x₁ by linarith)]; exact Real.exp_le_exp.mpr hL
    set x := Real.exp L with hxdef
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hlogx : Real.log x = L := by rw [hxdef, Real.log_exp]
    have hid := weilLagFunctionReal_log_mul_sqrt hx1
    rw [hlogx] at hid
    have ht := htail x hx1L
    have hS := trivialZeroSeriesReal_le_one hx1.le
    have hl := one_lt_log_two_pi
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hxa : x ^ a = Real.exp (a * L) := by
      rw [hxdef, ← Real.exp_mul]; ring_nf
    have hxa' : x * x ^ (a - 1 / 2) = Real.sqrt x * x ^ a := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith), ← Real.rpow_add hx0]
      ring_nf
    -- Φ(L)√x ≤ (c/a)x·x^{a-1/2}/(1/2-a) + 1
    have h1 : weilLagFunctionReal L * Real.sqrt x
        ≤ C * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) + 1 := by
      have hxI := mul_le_mul_of_nonneg_left ht hx0.le
      have : x * (C * (x ^ (a - 1 / 2) / (1 / 2 - a)))
          = C * (x * x ^ (a - 1 / 2)) / (1 / 2 - a) := by ring
      linarith
    rw [hxa'] at h1
    have h2 : weilLagFunctionReal L ≤ C / (1 / 2 - a) * x ^ a + 1 / Real.sqrt x := by
      rw [← mul_le_mul_iff_of_pos_right hsx]
      have : (C / (1 / 2 - a) * x ^ a + 1 / Real.sqrt x) * Real.sqrt x
          = C * (Real.sqrt x * x ^ a) / (1 / 2 - a) + 1 := by
        field_simp
      rw [this]; exact h1
    have h3 : 1 / Real.sqrt x ≤ x ^ a := by
      have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx1.le ha0.le
      have hsx1 : 1 ≤ Real.sqrt x := by rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
      have : 1 / Real.sqrt x ≤ 1 := by rw [div_le_one hsx]; exact hsx1
      linarith
    rw [← hxa]
    nlinarith
  -- the compact range
  obtain ⟨L₀, hL₀mem, hL₀max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.log x₁)).exists_isMaxOn
    ⟨0, ⟨le_refl 0, (Real.log_pos hx₁1).le⟩⟩
    (Complex.continuous_re.comp continuous_weilLagFunction_unconditional).continuousOn
  set B := weilLagFunctionReal L₀ with hB
  have hM : ∀ L, 0 ≤ L → weilLagFunctionReal L ≤ max K |B| * Real.exp (a * L) := by
    intro L hL
    have hexp1 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (by positivity)
    rcases le_or_gt (Real.log x₁) L with hbig | hsmall
    · have := hlarge L hbig
      have : K * Real.exp (a * L) ≤ max K |B| * Real.exp (a * L) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      linarith
    · have h1 : weilLagFunctionReal L ≤ B := hL₀max ⟨hL, hsmall.le⟩
      have h2 : B ≤ |B| := le_abs_self B
      have h3 : |B| ≤ max K |B| := le_max_right _ _
      have h4 : max K |B| ≤ max K |B| * Real.exp (a * L) := by
        have : 0 ≤ max K |B| := le_trans (abs_nonneg B) h3
        nlinarith
      linarith
  exact re_le_half_add_of_weilLagFunctionReal_le_exp ha0.le ha hM q

/-- `x^b ≤ (c/14)√x logloglog x` for large `x` when `b < ½`. -/
theorem eventually_rpow_le_littlewood_psi {b : ℝ} (hb : b < 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      x ^ b ≤ littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x)) := by
  have hc0 : 0 < littlewoodConst / 14 := by have := littlewoodConst_pos; positivity
  have hd : 0 < 1 / 2 - b := by linarith
  filter_upwards [tendsto_logLogLog_atTop.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hd).eventually_ge_atTop (1 / (littlewoodConst / 14))] with x hL3 hx1 hxd
  have hx0 : 0 < x := by linarith
  have hsq : Real.sqrt x = x ^ b * x ^ (1 / 2 - b) := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; ring_nf
  have hxb : 0 ≤ x ^ b := Real.rpow_nonneg hx0.le _
  have h1 : 1 ≤ littlewoodConst / 14 * x ^ (1 / 2 - b) := by
    rw [div_le_iff₀ hc0] at hxd; linarith
  calc x ^ b ≤ x ^ b * (littlewoodConst / 14 * x ^ (1 / 2 - b)) := le_mul_of_one_le_right hxb h1
    _ = littlewoodConst / 14 * Real.sqrt x := by rw [hsq]; ring
    _ ≤ littlewoodConst / 14 * Real.sqrt x * Real.log (Real.log (Real.log x)) :=
        le_mul_of_one_le_right (by positivity) hL3

theorem zeroReSup_le_one : zeroReSup ≤ 1 := by
  haveI := nonempty_xiZeroCopy
  exact zeroReSup_le fun q => (xiZeroCopy_re_lt_one q).le

/-- From a zero copy bound at every `a > b - ½` to `Θ ≤ b`. -/
theorem zeroReSup_le_of_forall_re_le {b : ℝ} (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ b) :
    zeroReSup ≤ b := by
  haveI := nonempty_xiZeroCopy
  exact zeroReSup_le h

/-- **Landau, upper side.**  For every `b < Θ`, `ψ(x) - x > x^b` infinitely often. -/
theorem frequently_rpow_lt_chebyshevPsi_sub {b : ℝ} (hb : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, x ^ b < Chebyshev.psi x - x := by
  rcases lt_or_ge b (1 / 2) with hhalf | hhalf
  · exact (frequently_littlewood_lt_chebyshevPsi_sub.and_eventually
      (eventually_rpow_le_littlewood_psi hhalf)).mono fun x ⟨h1, h2⟩ => by linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hno
    have hΘ1 := zeroReSup_le_one
    have hb1 : b < 1 := lt_of_lt_of_le hb hΘ1
    -- every zero has real part `≤ b`
    have hre : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ b := by
      intro q
      by_cases hbh : b = 1 / 2
      · -- a power bound at every `a > 0`
        refine le_of_forall_pos_lt_add fun ε hε => ?_
        set a : ℝ := min (ε / 2) (1 / 4) with ha
        have ha0 : 0 < a := lt_min (by linarith) (by norm_num)
        have ha4 : a < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        have h := re_le_half_add_of_chebyshevError_le_rpow (C := 1) zero_le_one ha0 ha4
          (x₁ := max x₀ 2) (by linarith [le_max_right x₀ 2]) (fun t ht => by
            have ht0 : 0 < t := by linarith [le_max_right x₀ 2]
            have h1 := not_lt.mp (hx₀ t (le_trans (le_max_left _ _) ht))
            have h2 : t ^ b ≤ t ^ (1 / 2 + a) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [le_max_right x₀ 2]) (by linarith)
            unfold chebyshevError; linarith) q
        have := min_le_left (ε / 2) (1 / 4)
        linarith
      · have hbh' : 1 / 2 < b := lt_of_le_of_ne hhalf (Ne.symm hbh)
        exact re_le_half_add_of_chebyshevError_le_rpow (C := 1) (a := b - 1 / 2) zero_le_one
          (by linarith) (by linarith) (x₁ := max x₀ 2) (by linarith [le_max_right x₀ 2])
          (fun t ht => by
            have h1 := not_lt.mp (hx₀ t (le_trans (le_max_left _ _) ht))
            unfold chebyshevError
            rw [show 1 / 2 + (b - 1 / 2) = b by ring]; linarith) q |>.trans_eq (by ring)
    have := zeroReSup_le_of_forall_re_le hre
    linarith

/-- **Landau, lower side.**  For every `b < Θ`, `ψ(x) - x < -x^b` infinitely often. -/
theorem frequently_chebyshevPsi_sub_lt_neg_rpow {b : ℝ} (hb : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, Chebyshev.psi x - x < -x ^ b := by
  rcases lt_or_ge b (1 / 2) with hhalf | hhalf
  · exact (frequently_chebyshevPsi_sub_lt_littlewood.and_eventually
      (eventually_rpow_le_littlewood_psi hhalf)).mono fun x ⟨h1, h2⟩ => by linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hno
    have hΘ1 := zeroReSup_le_one
    have hb1 : b < 1 := lt_of_lt_of_le hb hΘ1
    have hre : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ b := by
      intro q
      by_cases hbh : b = 1 / 2
      · refine le_of_forall_pos_lt_add fun ε hε => ?_
        set a : ℝ := min (ε / 2) (1 / 4) with ha
        have ha0 : 0 < a := lt_min (by linarith) (by norm_num)
        have ha4 : a < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        have h := re_le_half_add_of_chebyshevError_ge_rpow (C := 1) zero_le_one ha0 ha4
          (x₁ := max x₀ 2) (by linarith [le_max_right x₀ 2]) (fun t ht => by
            have h1 := not_lt.mp (hx₀ t (le_trans (le_max_left _ _) ht))
            have h2 : t ^ b ≤ t ^ (1 / 2 + a) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [le_max_right x₀ 2]) (by linarith)
            unfold chebyshevError; linarith) q
        have := min_le_left (ε / 2) (1 / 4)
        linarith
      · have hbh' : 1 / 2 < b := lt_of_le_of_ne hhalf (Ne.symm hbh)
        exact re_le_half_add_of_chebyshevError_ge_rpow (C := 1) (a := b - 1 / 2) zero_le_one
          (by linarith) (by linarith) (x₁ := max x₀ 2) (by linarith [le_max_right x₀ 2])
          (fun t ht => by
            have h1 := not_lt.mp (hx₀ t (le_trans (le_max_left _ _) ht))
            unfold chebyshevError
            rw [show 1 / 2 + (b - 1 / 2) = b by ring]; linarith) q |>.trans_eq (by ring)
    have := zeroReSup_le_of_forall_re_le hre
    linarith

/-- `Θ ≥ ½`: zeros come in pairs `ρ, 1 - ρ̄`. -/
theorem half_le_zeroReSup : 1 / 2 ≤ zeroReSup := by
  haveI := nonempty_xiZeroCopy
  obtain ⟨q⟩ := (inferInstance : Nonempty XiZeroCopy)
  have h1 := re_le_zeroReSup q
  have h2 := re_le_zeroReSup ⟨supportPartner q.1, ⟨0, xiSupportMultiplicity_pos _⟩⟩
  rw [supportPartner_re] at h2
  linarith

/-- **The generalized von Koch bound above `Θ`.**  For every `b > Θ`, `|ψ(x) - x| ≤ C x^b`
for `x ≥ 1`. -/
theorem exists_abs_chebyshevPsi_sub_le_rpow {b : ℝ} (hb : zeroReSup < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ b := by
  have hΘ := half_le_zeroReSup
  set α : ℝ := zeroReSup - 1 / 2 with hα
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    rw [← hq]
    have := re_le_zeroReSup q
    rw [hα]; linarith
  obtain ⟨C, hC0, hC⟩ := chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound hα0 hXi
    (b - zeroReSup) (by linarith)
  refine ⟨C, hC0, fun x hx => ?_⟩
  have := hC x hx
  rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub, chebyshevPsiReal_eq_psi,
    show 1 / 2 + α + (b - zeroReSup) = b by rw [hα]; ring] at this
  exact this


/-- **The exponent law for `ψ`.**  Unconditionally `Θ = sup Re ρ` is the exact order of
`ψ(x) - x`: both signs reach `x^b` for every `b < Θ`, and `|ψ(x) - x| ≤ C x^b` for every `b > Θ`. -/
theorem chebyshevPsi_sub_exponent_law :
    (∀ b : ℝ, b < zeroReSup →
      (∃ᶠ x : ℝ in atTop, x ^ b < Chebyshev.psi x - x)
        ∧ ∃ᶠ x : ℝ in atTop, Chebyshev.psi x - x < -x ^ b)
    ∧ ∀ b : ℝ, zeroReSup < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ b :=
  ⟨fun _ hb => ⟨frequently_rpow_lt_chebyshevPsi_sub hb, frequently_chebyshevPsi_sub_lt_neg_rpow hb⟩,
    fun _ hb => exists_abs_chebyshevPsi_sub_le_rpow hb⟩

end

end RHTower
