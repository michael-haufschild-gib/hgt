import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.Outliers.LocalRows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianMass

/-! # Simultaneous Gaussian tail bound for bonds exceeding the transfer cap -/
open Filter MeasureTheory Finset Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open private exponential_mass from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianMass
noncomputable section

/-- One exponential moment controls the number of bad physical edges
at every cap simultaneously, on every sufficiently long frozen prefix. -/
theorem gaussian_edge_outliers :
    ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ R : ℝ, 0≤R →
      ((exceptionalEdges (pathPauliDisorderShell ω n) R).card:ℝ)*exp (R^2/4)≤B*((n+2:ℕ):ℝ) := by
  obtain ⟨B,hB,hw⟩ := exponential_mass
  refine ⟨3*B,by positivity,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro R hR
  let u := pathPauliDisorderShell ω n
  let L := largeLabels u R
  have hcard : ((exceptionalEdges u R).card:ℝ)≤3*(L.card:ℝ) := by exact_mod_cast exceptionalEdges_card u R
  have hmass : (L.card:ℝ)*exp (R^2/4)≤B*((n+2:ℕ):ℝ) := calc
    _ = ∑ _l∈L, exp (R^2/4) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ∑ l∈L, exp ((u l)^2/4) := by
      apply sum_le_sum
      intro l hl
      have h : R < |u l| := (mem_filter.mp hl).2
      have hs := pow_le_pow_left₀ hR h.le 2
      rw [sq_abs] at hs
      exact exp_le_exp.mpr (div_le_div_of_nonneg_right hs (by norm_num))
    _ ≤ ∑ l, exp ((u l)^2/4) := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun l _ _ => (exp_pos _).le)
    _ ≤ _ := hn
  linarith only [hmass,mul_le_mul_of_nonneg_right hcard (exp_pos (R^2/4)).le]

/-- At the cap 1/(3348t) the discarded bonds cost O(K t¹⁰), uniformly
at positive times. This is smaller than an eighth-power signal as t tends to zero. -/
theorem gaussian_tenth_power_outliers :
    ∃ A>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 0<t →
      ((exceptionalEdges (pathPauliDisorderShell ω n) (1/(3348*t))).card:ℝ)≤A*((n+2:ℕ):ℝ)*t^10 := by
  obtain ⟨B,hB,hw⟩ := gaussian_edge_outliers
  let V : ℝ := 20*3348^2
  have hV : 0<V := by dsimp only [V]; norm_num
  refine ⟨B*V^5,mul_pos hB (pow_pos hV _),?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro t ht
  let R := 1/(3348*t)
  let y := V*t^2
  have hy : 0<y := mul_pos hV (sq_pos_of_pos ht)
  have hr := hn R (one_div_nonneg.mpr (mul_nonneg (by norm_num) ht.le))
  have he : 5*(1/y)=R^2/4 := by dsimp only [y,R,V]; field_simp; ring
  have hx : (1/y)^5≤exp (R^2/4) := calc
    _ ≤ (exp (1/y))^5 := pow_le_pow_left₀ (one_div_pos.mpr hy).le
      (by linarith only [add_one_le_exp (1/y)]) _
    _ = exp (5*(1/y)) := by rw [show (5:ℝ)=(5:ℕ) by norm_num,exp_nat_mul]
    _ = _ := congrArg exp he
  let N : ℝ := (exceptionalEdges (pathPauliDisorderShell ω n) R).card
  have h := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hx
    (show 0≤N from Nat.cast_nonneg _)).trans hr) (pow_nonneg hy.le 5)
  rw [mul_assoc,←mul_pow,div_mul_cancel₀ _ hy.ne',one_pow,mul_one] at h
  exact h.trans_eq (by dsimp only [y]; ring)

#print axioms gaussian_edge_outliers
#print axioms gaussian_tenth_power_outliers
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
