import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.Renormalization
import GaloisForLFunctions.RHTower.HarmonicLogMascheroni

/-!
# The critical energy cutoff with and without a phase

At zero frequency the finite part includes the harmonic constant and the
shift in radial energy. Every nonzero frequency has bounded cutoff trace.
Logarithmic normalization therefore detects exactly the zero frequency.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Filter
open scoped Topology

private theorem harmonic_residual :
    Tendsto (fun X : ℕ => radialCutoff X 1-(Real.log X:ℂ)) atTop (𝓝 (Real.eulerMascheroniConstant:ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp Real.tendsto_harmonic_sub_log
  apply h.congr
  intro X
  change (((harmonic X:ℝ)-Real.log X:ℝ):ℂ) = _
  rw [Complex.ofReal_sub,← _root_.RHTower.sum_inv_Icc_eq_ratCast_harmonic]
  simp only [radialCutoff,Complex.cpow_neg_one,Complex.ofReal_sum,Complex.ofReal_inv,Complex.ofReal_natCast]

private theorem quotient_log (C : ℕ+) :
    Tendsto (fun X : ℕ => Real.log ((X/C.val:ℕ):ℝ) - Real.log (X:ℝ)) atTop (𝓝 (-Real.log C.val)) := by
  have hC : (0:ℝ) < C.val := Nat.cast_pos.mpr C.pos
  have hdiv : Tendsto (fun X : ℕ => (X:ℝ)/C.val) atTop atTop :=
    Filter.Tendsto.atTop_div_const hC tendsto_natCast_atTop_atTop
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hdiv
  have hratio : Tendsto (fun X : ℕ => ((X/C.val:ℕ):ℝ)/(X:ℝ)) atTop (𝓝 (C.val:ℝ)⁻¹) := by
    have h := hf.div_const (C.val:ℝ)
    rw [one_div] at h
    apply h.congr
    intro X
    change (⌊(X:ℝ)/C.val⌋₊:ℝ)/((X:ℝ)/C.val)/C.val = _
    rw [Nat.floor_div_natCast,Nat.floor_natCast]
    field_simp [hC.ne']
  have h := (Real.continuousAt_log (inv_ne_zero hC.ne')).tendsto.comp hratio
  rw [Real.log_inv] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℕ),(Nat.tendsto_div_const_atTop C.ne_zero).eventually_gt_atTop 0] with X hX hY
  exact Real.log_div (Nat.cast_ne_zero.mpr hY.ne') (Nat.cast_ne_zero.mpr hX.ne')

/-- The constant term after subtracting the logarithmic divergence of the finite occupation trace. -/
theorem critical_cutoff_finite_part (t : ExceptionalTime) (j : ℕ) :
    let C := tailRadix t j
    let D := 2/((C.val:ℂ)-1)
    Tendsto (fun X : ℕ => shellCutoff t j X 1-D*(Real.log X:ℂ)) atTop
      (𝓝 (D*(Real.eulerMascheroniConstant:ℂ)-2*(C.val:ℂ)*(Real.log C.val:ℂ)/((C.val:ℂ)-1)^2)) := by
  let C := tailRadix t j
  let c : ℂ := C.val
  let q := c⁻¹
  let D := 2/(c-1)
  let L := D*(Real.eulerMascheroniConstant:ℂ)-2*c*(Real.log C.val:ℂ)/(c-1)^2
  let U (X : ℕ) := shellCutoff t j X 1-D*(Real.log X:ℂ)
  have hc : 1 < C.val := radix_gt_one t j
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.mpr C.ne_zero
  have hc1 : c-1 ≠ 0 := sub_ne_zero.mpr (show (C.val:ℂ) ≠ 1 by exact_mod_cast hc.ne')
  have hheat : heat 1 C = q := by rw [heat_eq_cpow,Complex.cpow_neg_one]
  have hq : ‖q‖ < 1 := hheat ▸ heat_contraction C hc 1 (by norm_num)
  have hD : (2+D)*q = D := by
    dsimp only [D,q]
    field_simp [hc0,hc1]
    ring
  have hL : (1-q)*L = 2*q*(Real.eulerMascheroniConstant:ℂ)-D*(Real.log C.val:ℂ) := by
    dsimp only [L,D,q]
    field_simp [hc0,hc1]
  have hh := (harmonic_residual.comp (Nat.tendsto_div_const_atTop C.ne_zero)).const_mul (2*q)
  have hlog := (Complex.continuous_ofReal.continuousAt.tendsto.comp (quotient_log C)).const_mul D
  have h := (hh.add hlog).sub (tendsto_const_nhds (x := (1-q)*L))
  have hz : 2*q*(Real.eulerMascheroniConstant:ℂ) + D*((-Real.log C.val:ℝ):ℂ) -(1-q)*L = 0 := by
    rw [hL,Complex.ofReal_neg]
    ring
  rw [hz] at h
  have hres : Tendsto (fun X : ℕ => U X-L-q*(U (X/C.val)-L)) atTop (𝓝 0) := by
    apply h.congr
    intro X
    change 2*q*(radialCutoff (X/C.val) 1-(Real.log ((X/C.val:ℕ):ℝ):ℂ))+
      D*((Real.log ((X/C.val:ℕ):ℝ)-Real.log (X:ℝ):ℝ):ℂ)-(1-q)*L =
      (shellCutoff t j X 1-D*(Real.log X:ℂ))-L-q*(shellCutoff t j (X/C.val) 1-D*(Real.log ((X/C.val:ℕ):ℝ):ℂ)-L)
    rw [Complex.ofReal_sub,shell_cutoff_recursion t j X 1]
    change _ = (heat 1 C*(2*radialCutoff (X/C.val) 1+shellCutoff t j (X/C.val) 1)-D*(Real.log X:ℂ))-L-
      q*(shellCutoff t j (X/C.val) 1-D*(Real.log ((X/C.val:ℕ):ℝ):ℂ)-L)
    rw [hheat]
    linear_combination -(Real.log ((X/C.val:ℕ):ℝ):ℂ)*hD
  have hlim := (tendsto_zero_of_quotient_contraction C.val hc q hq (fun X => U X-L) hres).add_const L
  simpa only [sub_add_cancel,zero_add] using hlim

/-- Every nonzero frequency on the critical line has uniformly bounded complex cutoff sums. -/
theorem critical_phase_cutoff_bounded (t : ExceptionalTime) (j : ℕ) (τ : {r : ℝ // r ≠ 0}) :
    ∃ B : ℝ, ∀ X, ‖shellCutoff t j X ⟨1,τ.val⟩‖ ≤ B := by
  let w : ℂ := ⟨1,τ.val⟩
  let D := 2/((tailRadix t j).val-1:ℂ)
  let P (X : ℕ) := (X:ℂ)^(1-w)/(1-w)
  have hw : w ≠ 1 := fun he => τ.property (congrArg Complex.im he)
  have h := renormalized_cutoff_limit t j ⟨w,zero_lt_one,hw⟩
  have hlim := Metric.isBounded_range_of_tendsto _ h
  obtain ⟨B,hB⟩ := hlim.exists_norm_le
  let M := max ‖P 0‖ (1/‖1-w‖)
  have hp (X : ℕ) : ‖P X‖ ≤ M := by
    cases X with
    | zero => exact le_max_left _ _
    | succ n =>
      have hnorm := Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n) : (0:ℝ) < (n+1:ℕ)) (y := 1-w)
      have he : (1-w).re = 0 := sub_self _
      simp only [Complex.ofReal_natCast,he,Real.rpow_zero] at hnorm
      change ‖((n+1:ℕ):ℂ)^(1-w)/(1-w)‖ ≤ _
      rw [norm_div,hnorm]
      exact le_max_right _ _
  refine ⟨B+‖D‖*M,fun X => ?_⟩
  have hb := hB _ ⟨X,rfl⟩
  change ‖shellCutoff t j X w-D*P X‖ ≤ B at hb
  calc ‖shellCutoff t j X w‖ = ‖(shellCutoff t j X w-D*P X)+D*P X‖ := congrArg norm (sub_add_cancel _ _).symm
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hb (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hp X) (norm_nonneg D)))

private theorem normalized_zero (a : ℕ → ℂ) (hb : ∃ B : ℝ, ∀ X, ‖a X‖ ≤ B) :
    Tendsto (fun X : ℕ => a X/(Real.log X:ℂ)) atTop (𝓝 0) := by
  obtain ⟨B,hB⟩ := hb
  have hl : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ ((tendsto_const_nhds (x := B)).div_atTop hl)
  filter_upwards [hl.eventually_gt_atTop 0] with X hX
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  exact div_le_div_of_nonneg_right (hB X) hX.le

/-- The normalized complex trace selects the zero frequency, while the logarithmic singular trace detects every frequency. -/
theorem critical_phase_readout (t : ExceptionalTime) (j : ℕ) (τ : ℝ) :
    Tendsto (fun X : ℕ => shellCutoff t j X ⟨1,τ⟩/(Real.log X:ℂ)) atTop
      (𝓝 (if τ = 0 then 2/((tailRadix t j).val-1:ℂ) else 0)) := by
  by_cases ht : τ = 0
  · subst τ
    rw [if_pos rfl]
    let D := 2/((tailRadix t j).val-1:ℂ)
    let a (X : ℕ) := shellCutoff t j X 1-D*(Real.log X:ℂ)
    have h := Metric.isBounded_range_of_tendsto a (critical_cutoff_finite_part t j)
    obtain ⟨B,hB⟩ := h.exists_norm_le
    have hh := (normalized_zero a ⟨B,fun X => hB _ ⟨X,rfl⟩⟩).add_const D
    rw [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℕ)] with X hX
    have hn : (Real.log X:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hX)).ne'
    change (shellCutoff t j X 1-D*(Real.log X:ℂ))/(Real.log X:ℂ)+D = shellCutoff t j X 1/(Real.log X:ℂ)
    field_simp [hn]
    exact sub_add_cancel _ _
  · rw [if_neg ht]
    exact normalized_zero _ (critical_phase_cutoff_bounded t j ⟨τ,ht⟩)

#print axioms critical_cutoff_finite_part
#print axioms critical_phase_cutoff_bounded
#print axioms critical_phase_readout

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
