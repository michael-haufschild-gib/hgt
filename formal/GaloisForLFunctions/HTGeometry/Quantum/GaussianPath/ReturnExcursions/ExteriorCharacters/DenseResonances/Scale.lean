import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.HammingPrice

/-! # Abundance of broad-support collisions on the elapsed horizon -/

open Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
noncomputable section

/-- A polynomial bandwidth prefactor cannot use up the exponential margin
between the bin count and the target signed threshold. -/
theorem bin_room (C M : ℝ) {p : ℝ} (hp : 0≤p) (hcut : (11/10)*p<1) :
    ∀ᶠ n : ℕ in atTop,
      (M+1)*(1+2*C*(4*n)^2*((11/10:ℝ)^(4*n)))*p^(4*n)<1 := by
  let t : ℝ := ((11/10:ℝ)*p)^4
  let z : ℝ := p^4
  have hp' : p<1 := by linarith only [hcut,hp]
  have htp : 0≤(11/10:ℝ)*p := by positivity
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one 2 (pow_nonneg htp 4)
    (pow_lt_one₀ htp hcut (by norm_num : (4:ℕ)≠0))
  have hz := tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hp 4)
    (pow_lt_one₀ hp hp' (by norm_num : (4:ℕ)≠0))
  have h : Tendsto (fun n : ℕ => (M+1)*(z^n+(32*C)*((n:ℝ)^2*t^n))) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero] using (hz.add (ht.const_mul (32*C))).const_mul (M+1)
  filter_upwards [h.eventually_lt_const zero_lt_one] with n hn
  dsimp only [z,t] at hn
  simp only [pow_mul,mul_pow] at hn ⊢
  linarith only [hn]

/-- For any fixed multiplier, the mandatory close-pair count eventually
exceeds that multiplier times the target scale. -/
theorem many_collisions (C M : ℝ) (hM : 0≤M) :
    ∀ᶠ n : ℕ in atTop, ∀ (Z b : ℝ), 0≤b →
      b≤1+2*C*(4*n)^2*(11/10:ℝ)^(4*n) →
      let B : ℝ := (4*n).choose (2*n)
      B^2≤b*(Z+B*(2^n*(3/2)^(4*n))) → M*B^2*(9/10)^(4*n)<Z := by
  filter_upwards [bin_room C M (p:=9/10) (by norm_num) (by norm_num),
    quarter_price_of_base (c:=9/10) (by norm_num)] with n hb hp
  intro Z b hb₀ hh B hcount
  let x := (9/10:ℝ)^(4*n)
  have bx : 0≤x := by positivity
  have hB : 0<B := by
    dsimp only [B]
    exact_mod_cast (Nat.choose_pos (by omega : 2*n≤4*n))
  have hnear : B*(2^n*(3/2)^ (4*n)) ≤ B^2*x := by
    have h := mul_le_mul_of_nonneg_left hp hB.le
    change B*(2^n*(3/2)^(4*n)) ≤ B*(1/2*B*x) at h
    nlinarith only [h,mul_nonneg (sq_nonneg B) bx]
  by_contra! h
  have hl := hcount.trans (mul_le_mul_of_nonneg_left (add_le_add h hnear) hb₀)
  have hx' : (M+1)*b*x<1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by linarith only [hM])) bx).trans_lt hb
  have hc := mul_lt_mul_of_pos_left hx' (sq_pos_of_pos hB)
  nlinarith only [hl,hc]

#print axioms many_collisions
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
