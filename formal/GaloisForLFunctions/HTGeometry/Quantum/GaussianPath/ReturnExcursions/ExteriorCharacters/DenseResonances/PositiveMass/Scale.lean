import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.Scale

/-! # Compulsory positive mass at the signed first-wait threshold -/

open Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
noncomputable section

/-- The half-degree character at a tenth-error fit supplies squared
weight at base $199/200$. The bin count and specified signed target
consume only base $(11/10)(9/10)$. -/
theorem positive_mass_price (C M : ℝ) (hM : 0≤M) :
    ∀ᶠ n : ℕ in atTop, ∀ (b Z : ℝ), 0≤b →
      b≤1+2*C*(4*n)^2*(11/10:ℝ)^(4*n) →
      let B : ℝ := (4*n).choose (2*n)
      B^2*(199/200:ℝ)^(4*n)≤b*4*(B*(2^n*(3/2)^(4*n))+2*Z) →
      M*B^2*(9/10)^(4*n)<Z := by
  let k := 4*(1+2*M)
  let c : ℝ := 199/200
  let p : ℝ := 9/10
  filter_upwards [bin_room C (k-1) (p:=p/c) (by norm_num [p,c]) (by norm_num [p,c]),
    quarter_price_of_base (c:=p) (by norm_num [p])] with n hb hp
  intro b Z hb₀ hh B hcount
  have hB : 0<B := by
    dsimp only [B]
    exact_mod_cast (Nat.choose_pos (by omega : 2*n≤4*n))
  have hk : 0≤k := by dsimp only [k]; linarith only [hM]
  have hnear : B*(2^n*(3/2)^(4*n)) ≤ B^2*p^(4*n) := by
    have h := mul_le_mul_of_nonneg_left hp hB.le
    change B*(2^n*(3/2)^(4*n))≤B*(1/2*B*p^(4*n)) at h
    nlinarith only [h,mul_nonneg (sq_nonneg B) (pow_nonneg (by norm_num [p] : 0≤p) (4*n))]
  have hratio : k*b*(p/c)^(4*n)<1 := by
    rw [sub_add_cancel] at hb
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hk)
      (pow_nonneg (by norm_num [p,c]) _)).trans_lt hb
  rw [div_pow,←mul_div_assoc,div_lt_one (pow_pos (by norm_num [c]) _)] at hratio
  by_contra! hz
  change Z≤M*B^2*p^(4*n) at hz
  change B^2*c^(4*n)≤_ at hcount
  have hsum := add_le_add hnear (mul_le_mul_of_nonneg_left hz (by norm_num : (0:ℝ)≤2))
  have hu := hcount.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hb₀ (by norm_num)))
  have hl := mul_lt_mul_of_pos_left hratio (sq_pos_of_pos hB)
  dsimp only [k] at hl
  nlinarith only [hu,hl]

#print axioms positive_mass_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
