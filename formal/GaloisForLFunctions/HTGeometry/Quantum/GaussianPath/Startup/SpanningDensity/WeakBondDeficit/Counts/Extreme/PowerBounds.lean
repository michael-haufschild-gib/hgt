import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Extreme.Bracketing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.DisorderScales.PrefixPowers

/-! # Power-law scale of the weakest physical bonds -/
open Filter Real MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
noncomputable section

/-- With K comparable to j^(9(m+1)), all bonds exceed the j^(-m-2)
box and at least one removable odd bond lies in the j^(-m) box.
Both statements hold on the same draw at every exponent resolution. -/
theorem gaussian_extreme_bond_powers :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : ℕ, ∀ᶠ n : ℕ in atTop,
      let p := 9*(m+1)
      let j := powerPrefixIndex p n
      let u := pathPauliDisorderShell ω n
      0<j ∧ 4*j^p≤n+1 ∧ n+2≤4*(2*j)^p ∧
        (weakEdges u ((1/(j:ℝ))^(m+2))).card=0 ∧ 0<(removable u ((1/(j:ℝ))^m)).card := by
  apply ae_all_iff.mpr
  intro m
  let p := 9*(m+1)
  let h (j : ℕ) := (1/(j:ℝ))^(m+2)
  let g (j : ℕ) := (1/(j:ℝ))^m
  let M (j : ℕ) := 4*(2*j)^p
  let C := 4*(2:ℝ)^p*4^9
  let c := (2*gaussianDensityFloor)^9
  have hc : 0<c := pow_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) _
  have hs : Summable fun j => (M j:ℝ)*bondLaw.real (weakBond (h j)) := by
    apply ((Real.summable_one_div_nat_pow.mpr (by decide : 1<9)).mul_left C).of_norm_bounded_eventually_nat
    filter_upwards [eventually_gt_atTop (0:ℕ)] with j hj
    have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
    have h₁ : 1/(j:ℝ)≤1 := (div_le_one hJ).mpr (by exact_mod_cast hj)
    have hh : 0<h j := pow_pos (one_div_pos.mpr hJ) _
    have hb := (box_probability hh (pow_le_one₀ (one_div_pos.mpr hJ).le h₁)).2
    have he : (j:ℝ)^p*(h j)^9*(j:ℝ)^9=1 := by
      dsimp only [h]
      rw [←pow_mul,one_div_pow,show (m+2)*9=p+9 by dsimp only [p]; omega,pow_add]
      field_simp [hJ.ne']
    have hM : (M j:ℝ)=4*(2:ℝ)^p*(j:ℝ)^p := by
      dsimp only [M]
      push_cast
      rw [mul_pow,mul_assoc]
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg),mul_one_div]
    apply (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (M j))).trans_eq
    rw [hM]
    apply (eq_div_iff (pow_ne_zero _ hJ.ne')).mpr
    calc
      _ = C*((j:ℝ)^p*(h j)^9*(j:ℝ)^9) := by dsimp only [C]; ring
      _ = C := by rw [he,mul_one]
  obtain ⟨J,hJ⟩ := exists_nat_ge (16/c)
  have hm : ∀ᶠ j : ℕ in atTop, 16*log j≤bondLaw.real (weakBond (g j))*(j^p:ℕ) := by
    filter_upwards [eventually_ge_atTop J,eventually_gt_atTop (0:ℕ)] with j hjJ hj
    have hpos : (0:ℝ)<j := Nat.cast_pos.mpr hj
    have hj₁ : 1≤(j:ℝ) := by exact_mod_cast hj
    have hg : 0<g j := pow_pos (one_div_pos.mpr hpos) _
    have hb := (box_probability hg (pow_le_one₀ (one_div_pos.mpr hpos).le ((div_le_one hpos).mpr hj₁))).1
    have he : (g j)^9*(j:ℝ)^p=(j:ℝ)^9 := by
      dsimp only [g]
      rw [←pow_mul,one_div_pow,show p=m*9+9 by dsimp only [p]; omega,pow_add]
      field_simp [hpos.ne']
    have hs₀ := (div_le_iff₀ hc).mp (hJ.trans (Nat.cast_le.mpr hjJ))
    rw [Nat.cast_pow]
    calc
      _ ≤ 16*(j:ℝ) := mul_le_mul_of_nonneg_left
        ((log_le_sub_one_of_pos hpos).trans (sub_le_self _ zero_le_one)) (by norm_num)
      _ ≤ c*(j:ℝ)^2 := by linarith only [mul_le_mul_of_nonneg_right hs₀ hpos.le]
      _ ≤ c*(j:ℝ)^9 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj₁ (by decide : 2≤9)) hc.le
      _ = c*(g j)^9*(j:ℝ)^p := by rw [mul_assoc,he]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (pow_nonneg hpos.le _)
  have hw := gaussian_extreme_brackets M (fun j => j^p) h g hs hm
  filter_upwards [hw] with ω hω
  filter_upwards [(powerPrefixIndex_tendsto p).eventually hω,eventually_ge_atTop (3:ℕ)] with n hn hsize
  obtain ⟨hj,hl,hu⟩ := powerPrefixIndex_bounds p n (by dsimp only [p]; omega) hsize
  exact ⟨hj,hl,hu,hn n ((Nat.le_succ _).trans hu) (by omega)⟩

#print axioms gaussian_extreme_bond_powers
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
