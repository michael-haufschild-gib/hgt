import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks.Binary

/-!
# Diameter of a row of accepted occupations

Logarithmic bins keep the phase difference between two row entries within
one half-turn. Jordan's inequality then converts the two acceptance tests
into a bound on their integer separation, uniformly over all windings.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks

private theorem arc_bound (t : ℝ) (a b : ℕ+) (h : |t*(energy a-energy b)| ≤ Real.pi) :
    |t| *|energy a-energy b| ≤ Real.pi/2 * dist (clockPhase t a) (clockPhase t b) := by
  let u := t*(energy a-energy b)/2
  have hu : |u| ≤ Real.pi/2 := by
    dsimp [u]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [h]
  have hsin : Real.sin |u| ≤ |Real.sin u| := by
    by_cases hs : 0 ≤ u
    · rw [abs_of_nonneg hs]
      exact le_abs_self _
    · rw [abs_of_neg (lt_of_not_ge hs),Real.sin_neg]
      exact neg_le_abs _
  have hj := (Real.mul_le_sin (abs_nonneg u) hu).trans hsin
  rw [chord]
  change _ ≤ Real.pi/2 * (2*|Real.sin u|)
  calc
    _ = Real.pi * (2/Real.pi*|u|) := by
      dsimp [u]
      rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      field_simp [Real.pi_ne_zero]
    _ ≤ Real.pi * |Real.sin u| := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    _ = _ := by ring

private theorem exp_increment (x y : ℝ) : Real.exp y - Real.exp x ≤ Real.exp y*(y-x) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
  rw [← Real.exp_add,sub_add_cancel] at h
  nlinarith only [h]

private theorem exp_lip {x y u : ℝ} (hx : x ≤ u) (hy : y ≤ u) :
    |Real.exp x-Real.exp y| ≤ Real.exp u * |x-y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact (exp_increment y x).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) (sub_nonneg.mpr h))
  · rw [abs_sub_comm (Real.exp x),abs_sub_comm x,abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact (exp_increment x y).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hy) (sub_nonneg.mpr h))

namespace Clock

variable (M : Clock)

def step := Real.pi / (|M.time| +1)

theorem step_pos : 0 < M.step := div_pos Real.pi_pos (by positivity)

def base (j : ℕ) := (j : ℝ)*M.step

def bin (n : ℕ+) := ⌊energy n/M.step⌋₊

theorem base_nonneg (j : ℕ) : 0 ≤ M.base j := mul_nonneg (Nat.cast_nonneg _) M.step_pos.le

theorem bin_mono {n m : ℕ+} (h : n ≤ m) : M.bin n ≤ M.bin m :=
  Nat.floor_mono (div_le_div_of_nonneg_right (energy_mono h) M.step_pos.le)

theorem bin_lower (n : ℕ+) : M.base (M.bin n) ≤ energy n :=
  (le_div_iff₀ M.step_pos).mp (Nat.floor_le (div_nonneg (energy_nonneg n) M.step_pos.le))

theorem bin_upper (n : ℕ+) : energy n ≤ M.base (M.bin n)+M.step := by
  have h := (div_lt_iff₀ M.step_pos).mp (Nat.lt_floor_add_one (energy n/M.step))
  simpa only [bin,base,add_mul,one_mul] using h.le

theorem weight_le {σ : ℝ} (hσ : 0 ≤ σ) (a b : ℕ+) :
    weight σ (a,b) ≤ Real.exp (-σ*(M.base (M.bin a)+M.base (M.bin b))) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (add_le_add (M.bin_lower a) (M.bin_lower b)) (neg_nonpos.mpr hσ))

def spread := Real.pi*M.scale.val/|M.time| *Real.exp M.step

theorem spread_nonneg : 0 ≤ M.spread :=
  mul_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le M.scale.property.le) (abs_nonneg _)) (Real.exp_pos _).le

private theorem energy_diameter (ht : M.time ≠ 0) (a a' b : ℕ+) (hi : M.bin a' = M.bin a)
    (ha : M.Passes (a,b)) (ha' : M.Passes (a',b)) :
    |energy a-energy a'| ≤ Real.pi*M.scale.val/|M.time| *
      Real.exp (-(M.exponent : ℝ)*(M.base (M.bin a)+M.base (M.bin b))) := by
  let w := Real.exp (-(M.exponent : ℝ)*(M.base (M.bin a)+M.base (M.bin b)))
  have h₁ : dist (clockPhase M.time a) (clockPhase M.time b) ≤ M.scale.val*w :=
    ha.le.trans (mul_le_mul_of_nonneg_left (M.weight_le M.exponent.property a b) M.scale.property.le)
  have h₂ : dist (clockPhase M.time a') (clockPhase M.time b) ≤ M.scale.val*w := by
    have hw : weight M.exponent (a',b) ≤ w := by
      change weight M.exponent (a',b) ≤ Real.exp (-(M.exponent : ℝ)*(M.base (M.bin a)+M.base (M.bin b)))
      rw [← hi]
      exact M.weight_le M.exponent.property a' b
    exact ha'.le.trans (mul_le_mul_of_nonneg_left hw M.scale.property.le)
  have hg : |energy a-energy a'| ≤ M.step := by
    have hu := M.bin_upper a'
    have hl := M.bin_lower a'
    rw [hi] at hu hl
    exact abs_le.mpr ⟨by linarith only [hu,M.bin_lower a],by linarith only [hl,M.bin_upper a]⟩
  have htπ : |M.time| *M.step ≤ Real.pi := by
    have h := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one : |M.time| ≤ |M.time| +1) M.step_pos.le
    exact h.trans_eq (by unfold step; field_simp)
  have hang : |M.time*(energy a-energy a')| ≤ Real.pi := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hg (abs_nonneg _)).trans htπ
  have hdist := (dist_triangle_right (clockPhase M.time a) (clockPhase M.time a') (clockPhase M.time b)).trans
    (add_le_add h₁ h₂)
  have hgap := (arc_bound M.time a a' hang).trans
    (mul_le_mul_of_nonneg_left hdist (by positivity))
  have hpos : 0 < |M.time| := abs_pos.mpr ht
  change _ ≤ Real.pi*M.scale.val/|M.time| *w
  rw [div_mul_eq_mul_div,le_div_iff₀ hpos]
  calc
    _ = |M.time| *|energy a-energy a'| := mul_comm _ _
    _ ≤ _ := hgap.trans_eq (by ring)

theorem row_diameter (ht : M.time ≠ 0) (a a' b : ℕ+) (hi : M.bin a' = M.bin a)
    (ha : M.Passes (a,b)) (ha' : M.Passes (a',b)) :
    |((a : ℕ) : ℝ)-(a' : ℕ)| ≤ M.spread * Real.exp
      (M.base (M.bin a)-(M.exponent : ℝ)*(M.base (M.bin a)+M.base (M.bin b))) := by
  have hu := M.bin_upper a'
  rw [hi] at hu
  rw [← exp_energy a,← exp_energy a']
  refine (exp_lip (M.bin_upper a) hu).trans ?_
  refine (mul_le_mul_of_nonneg_left (M.energy_diameter ht a a' b hi ha ha') (Real.exp_pos _).le).trans_eq ?_
  rw [Real.exp_add,sub_eq_add_neg,Real.exp_add,neg_mul,spread]
  ring

#print axioms row_diameter

end Clock
end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AdaptiveClocks
