import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # A fixed fraction of Hilbert dimension in gates at inverse-square precision -/
open Set Filter Real MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

private theorem fine_mesh {d : ℝ} (hd : 8 ≤ d) :
    1/d ≤ zeroGateArcTolerance (1/d)-zeroGateArcTolerance ((1/d)^2) := by
  have hd₀ : 0<d := by linarith only [hd]
  have hu : 1/d ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hd])
  have hl := three_mul_le_arcTolerance (one_div_nonneg.mpr hd₀.le) hu
  have hx : 0 ≤ (1/d)^2 := sq_nonneg _
  have hs := Real.sin_le (show 0 ≤ π*(1/d)^2/2 by positivity)
  have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hx
  have hsq : 4*(1/d)^2 ≤ 1/d := by
    have hh := (div_le_div_iff_of_pos_right hd₀).mpr (by linarith only [hd] : (4:ℝ)≤d)
    have he : 4*(1/d)^2=(4/d)/d := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (hh.trans_eq (div_self hd₀.ne')) hd₀.le
  change 1/d ≤ zeroGateArcTolerance (1/d)-2*sin (π*(1/d)^2/2)
  linarith only [hl,hs,hπ,hsq,one_div_nonneg.mpr hd₀.le]

/-- At arc width D⁻², a net for D/256 gates has mass below D⁻⁽ᴰ/²⁾.
The precision contributes order log D to each of the D independent
phase constraints. -/
theorem inverse_square_dimension_budget {n : ℕ} (hn : 3 ≤ n)
    (H : selfAdjoint (Register n)) (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (a : ℝ) :
    let D : ℕ := 2^n
    let s := D/256
    let ε := zeroGateArcTolerance ((1/(D:ℝ))^2)
    ∀ᶠ T : ℝ in atTop, ∀ j ≤ s, visitFraction H j ε a T < 1/(D:ℝ)^(D/2) := by
  intro D s ε
  have hD : 8 ≤ D := Nat.pow_le_pow_right (by decide : 0<2) hn
  have hd : (8:ℝ) ≤ D := by exact_mod_cast hD
  have hd₀ : (0:ℝ)<D := by linarith only [hd]
  have hd₁ : (1:ℝ)<D := by linarith only [hd]
  let y := 1/(D:ℝ)
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance (y^2)
  have hy : 0<y := one_div_pos.mpr hd₀
  have hyhalf : y<1/2 := one_div_lt_one_div_of_lt (by norm_num) (by linarith only [hd])
  have hxy : y^2<y := by nlinarith only [mul_pos hy (by linarith only [hyhalf] : 0<1-y)]
  have hmesh : y ≤ δ := fine_mesh hd
  have hδ : 0<δ := hy.trans_le hmesh
  have hs : (s:ℝ)+1 ≤ D := by exact_mod_cast (by dsimp only [s]; omega : s+1 ≤ D)
  have hnD : (n:ℝ)+1 ≤ D := by exact_mod_cast (show n+1 ≤ 2^n from Nat.lt_two_pow_self)
  have hnet : 1+4*(s:ℝ)/δ ≤ (D:ℝ)^3 := by
    have h₁ := div_le_div_of_nonneg_left (by positivity : 0≤4*(s:ℝ)) hy hmesh
    have he : 4*(s:ℝ)/y=4*(s:ℝ)*D := by dsimp only [y]; field_simp
    rw [he] at h₁
    have hs' : (s:ℝ)≤D := by linarith only [hs]
    have h₂ := mul_le_mul_of_nonneg_right hs' hd₀.le
    have h₃ := mul_nonneg (sq_nonneg (D:ℝ)) (show 0≤(D:ℝ)-5 by linarith only [hd])
    nlinarith only [h₁,h₂,h₃,one_le_pow₀ hd₁.le (n:=2)]
  have hg : (((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32 ≤ (D:ℝ)^98 := by
    apply (mul_le_mul (pow_le_pow_left₀ (by positivity) hnD 2)
      (pow_le_pow_left₀ (by positivity) hnet 32) (by positivity) (by positivity)).trans_eq
    ring
  have hN := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hg s) (by positivity) hd₀.le
  have hbound : (((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s)*zeroGateArcDensity D y <
      1/(D:ℝ)^(D/2) := by
    have hden : 0≤zeroGateArcDensity D y := mul_nonneg hd₀.le (pow_nonneg hy.le _)
    apply (mul_le_mul_of_nonneg_right hN hden).trans_lt
    have hrep : zeroGateArcDensity D y=(D:ℝ)/(D:ℝ)^(D-1) := by
      dsimp only [zeroGateArcDensity,y]
      rw [one_div_pow]
      ring
    rw [hrep,←pow_mul]
    have he : (D:ℝ)*D^(98*s)*((D:ℝ)/D^(D-1)) = (D:ℝ)^(98*s+2)/D^(D-1) := by
      rw [pow_add,pow_two]; ring
    rw [he,div_lt_div_iff₀ (pow_pos hd₀ _) (pow_pos hd₀ _),one_mul,←pow_add]
    exact pow_lt_pow_right₀ hd₁ (by dsimp only [s]; omega)
  have hh := finite_budget_eventually_lt H hmax s (sq_nonneg y) hxy hyhalf a _ hbound
  filter_upwards [hh,eventually_ge_atTop a] with T hT ha j hj
  exact (visitFraction_mono H hj ε a T ha).trans_lt hT

#print axioms inverse_square_dimension_budget
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
