import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.ScalarBracket

/-! # Relative errors for rare scalar occupations -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- Eroding an arc by δ loses at most a share Dδ/x of its scalar mass. -/
private theorem erode_mass (D : ℕ) {x δ α : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) (hd : δ ≤ x)
    (hcost : (D:ℝ)*δ ≤ α*x) :
    (1-α)*zeroGateArcDensity D x ≤ zeroGateArcDensity D (x-δ) := by
  let u := δ/x
  let n := D-1
  have hu : u ≤ 1 := (div_le_one hx).mpr hd
  have hnu : (n:ℝ)*u ≤ α := by
    change (n:ℝ)*(δ/x) ≤ α
    rw [←mul_div_assoc,div_le_iff₀ hx]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le D 1 : (n:ℝ) ≤ D) hδ).trans hcost
  have hbern := one_add_mul_le_pow (a := -u) (by linarith only [hu]) n
  have hp : 1-α ≤ (1-u)^n := by
    rw [←sub_eq_add_neg] at hbern
    linarith only [hbern,hnu]
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (pow_nonneg hx.le n)) (Nat.cast_nonneg (α:=ℝ) D)
  have hr : (1-u)*x=x-δ := by dsimp only [u]; field_simp [hx.ne']
  change (1-α)*((D:ℝ)*x^n) ≤ (D:ℝ)*(x-δ)^n
  rw [←hr,mul_pow]
  linarith only [h]

private theorem relative_error {p V G T α : ℝ} (hp : 0 < p) (hT : 0 < T) (hG : 0 ≤ G)
    (hα : 0 ≤ α) (hsmall : α ≤ 1/2)
    (hl : (1-α)*p*(T-G) ≤ V) (hu : (1-α)*V ≤ p*(T+G)) :
    |V/(p*T)-1| ≤ 2*(α+G/T) := by
  let w := G/T
  let y := V/(p*T)
  have hw : 0 ≤ w := div_nonneg hG hT.le
  have hy : (1-α)*(1-w) ≤ y := (le_div_iff₀ (mul_pos hp hT)).mpr (by
    calc
      _ = (1-α)*p*(T-G) := by dsimp only [w]; field_simp
      _ ≤ _ := hl)
  have hy' : (1-α)*y ≤ 1+w := by
    change (1-α)*(V/(p*T)) ≤ 1+w
    rw [←mul_div_assoc,div_le_iff₀ (mul_pos hp hT)]
    exact hu.trans_eq (by dsimp only [w]; field_simp)
  have hupper : y ≤ 1+2*(α+w) := by
    apply (mul_le_mul_iff_right₀ (show 0<1-α by linarith only [hsmall])).mp
    apply hy'.trans
    nlinarith only [mul_nonneg (show 0≤1-2*α by linarith only [hsmall]) (add_nonneg hα hw)]
  change |y-1| ≤ 2*(α+w)
  exact abs_le.mpr ⟨by nlinarith only [hy,mul_nonneg hα hw,hα,hw],by linarith only [hupper]⟩

/-- Relative error scales with the temporal boundary G/T and the angular
boundary Dδ/x. Both bounds hold for every observation origin. -/
theorem scalar_relative_error {N : ℕ} (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {δ G x : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (hd : δ ≤ x) (hx' : x+δ ≤ 1/2) (hG : 0 < G)
    (hclock : ∀ u : ℝ, ∃ τ ∈ Icc u (u+G), τ ∈ visitSet H 0 δ)
    (a T : ℝ) (hT : G < T) (hsmall : ((2^N:ℕ):ℝ)*δ/x ≤ 1/2) :
    |visitFraction H 0 (zeroGateArcTolerance x) a (a+T)/zeroGateArcDensity (2^N) x-1| ≤
      2*(((2^N:ℕ):ℝ)*δ/x+G/T) := by
  let D : ℕ := 2^N
  let α := (D:ℝ)*δ/x
  let p := zeroGateArcDensity D x
  let V := volume.real (visitSet H 0 (zeroGateArcTolerance x) ∩ Icc a (a+T))
  have hα : 0 ≤ α := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) hx.le
  have hp : 0 < p := mul_pos (Nat.cast_pos.mpr (Nat.two_pow_pos N)) (pow_pos hx _)
  change α ≤ 1/2 at hsmall
  have hc : (D:ℝ)*δ=α*x := (div_mul_cancel₀ _ hx.ne').symm
  have hl := erode_mass D hx hδ hd hc.le
  have hu := erode_mass D (add_pos_of_pos_of_nonneg hx hδ) hδ (le_add_of_nonneg_left hx.le)
    (hc.le.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ) hα))
  rw [show x+δ-δ=x by ring] at hu
  have hbox := scalar_mass_bracket H hmax hδ hd hx' hG hclock a T hT
  have htm : 0 ≤ T-G := (sub_pos.mpr hT).le
  have hplus := add_nonneg (hG.trans hT).le hG.le
  have hlow : (1-α)*p*(T-G) ≤ V := (mul_le_mul_of_nonneg_right hl htm).trans hbox.1
  have hhigh : (1-α)*V ≤ p*(T+G) := calc
    _ ≤ (1-α)*(zeroGateArcDensity D (x+δ)*(T+G)) :=
      mul_le_mul_of_nonneg_left hbox.2 (by linarith only [hsmall] : 0 ≤ 1-α)
    _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hu hplus
  change |V/(a+T-a)/p-1| ≤ _
  rw [add_sub_cancel_left,div_div,mul_comm T p]
  exact relative_error hp (hG.trans hT) hG.le hα hsmall hlow hhigh

#print axioms scalar_relative_error
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
