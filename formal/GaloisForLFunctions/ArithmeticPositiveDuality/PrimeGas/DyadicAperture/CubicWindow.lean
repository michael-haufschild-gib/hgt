import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Angles

/-!
# Dyadic preimages of the cubic clock phases

Below the strict cutoff 4π/5 an orbit entering the upper branch can
never leave it. Deviations from its cubic fixed angle then double.
A fifth-root two-cycle gives the exact upper endpoint of this classification.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture

def cubic : ℝ := 2*Real.pi/3
def fifth : ℝ := 4*Real.pi/5

def CubicAngle (u : ℝ) := u = 0 ∨ ∃ k : ℕ, u = cubic / (2:ℝ)^k

private theorem cubic_pos : 0 < cubic := by unfold cubic; positivity
private theorem cubic_le_pi : cubic ≤ Real.pi := by unfold cubic; linarith only [Real.pi_pos]
private theorem cubic_high : Real.pi/2 ≤ cubic := by unfold cubic; linarith only [Real.pi_pos]
private theorem cubic_lt_fifth : cubic < fifth := by unfold fifth cubic; linarith only [Real.pi_pos]

/-- A nonnegative quantity that doubles forever and stays bounded starts at zero. -/
private theorem doubling_zero (v : ℕ → ℝ) (h₀ : 0 ≤ v 0)
    (hs : ∀ n, v (n+1) = 2*v n) (B : ℝ) (hb : ∀ n, v n ≤ B) : v 0 = 0 := by
  have grow (n : ℕ) : ((n:ℝ)+1)*v 0 ≤ v n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ,hs n]
      nlinarith only [ih,mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) h₀]
  by_contra hn
  have hp := lt_of_le_of_ne h₀ (Ne.symm hn)
  obtain ⟨n,hn⟩ := exists_nat_gt (B/v 0)
  have hh := (div_lt_iff₀ hp).mp hn
  linarith only [grow n,hb n,hh,h₀]

/-- Phase after n doublings. -/
def orbit (z : Circle) (n : ℕ) := z^(2^n : ℕ)

private theorem orbit_next (z : Circle) (n : ℕ) : orbit z (n+1) = (orbit z n)^2 := by
  unfold orbit
  rw [pow_succ,pow_mul]

/-- No other initial angle can stay strictly below the fifth-root cutoff. -/
theorem necessary (z : Circle) (h : Survives fifth z) : CubicAngle (angle z) := by
  let a (n : ℕ) := angle (orbit z n)
  have bound (n : ℕ) : a n < fifth := h n
  have low (n : ℕ) (hn : a n ≤ Real.pi/2) : a (n+1) = 2*a n :=
    (congrArg angle (orbit_next z n)).trans (square_low _ hn)
  have high (n : ℕ) (hn : Real.pi/2 ≤ a n) : a (n+1) = 2*Real.pi-2*a n :=
    (congrArg angle (orbit_next z n)).trans (square_high _ hn)
  have trapped (n : ℕ) (hn : Real.pi/2 ≤ a n) : Real.pi/2 ≤ a (n+1) := by
    by_contra! hh
    have h₁ := bound n
    have h₂ := bound (n+1+1)
    unfold fifth at h₁ h₂
    linarith only [h₁,h₂,high n hn,low (n+1) hh.le]
  have fixed (n : ℕ) (hn : Real.pi/2 ≤ a n) : a n = cubic := by
    have live (j : ℕ) : Real.pi/2 ≤ a (n+j) := by
      induction j with
      | zero => exact hn
      | succ j ih => exact trapped (n+j) ih
    have hs (j : ℕ) : |a (n+(j+1))-cubic| = 2*|a (n+j)-cubic| := by
      rw [show n+(j+1) = (n+j)+1 by omega,high _ (live j)]
      have he : 2*Real.pi-2*a (n+j)-cubic = -(2*(a (n+j)-cubic)) := by unfold cubic; ring
      rw [he,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hb (j : ℕ) : |a (n+j)-cubic| ≤ Real.pi := abs_le.mpr
      ⟨by linarith only [(angle_mem (orbit z (n+j))).1,cubic_le_pi],
       by linarith only [(angle_mem (orbit z (n+j))).2,cubic_pos]⟩
    exact sub_eq_zero.mp (abs_eq_zero.mp (doubling_zero (fun j => |a (n+j)-cubic|) (abs_nonneg _) hs _ hb))
  have start : a 0 = angle z := by simp [a,orbit]
  classical
  by_cases hit : ∃ n, Real.pi/2 ≤ a n
  · let k := Nat.find hit
    have first (j : ℕ) (hj : j ≤ k) : a j = (2:ℝ)^j*a 0 := by
      induction j with
      | zero => simp
      | succ j ih =>
        have hj' : j < k := Nat.lt_of_succ_le hj
        rw [low j (le_of_lt (lt_of_not_ge (Nat.find_min hit hj'))),ih hj'.le,pow_succ]
        ring
    right
    refine ⟨k,(eq_div_iff (by positivity : (2:ℝ)^k ≠ 0)).mpr ?_⟩
    rw [← start,mul_comm,← first k le_rfl]
    exact fixed k (Nat.find_spec hit)
  · left
    have lo (n : ℕ) : a n ≤ Real.pi/2 := le_of_lt (lt_of_not_ge (fun hn => hit ⟨n,hn⟩))
    rw [← start]
    exact doubling_zero a (angle_mem _).1 (fun n => low n (lo n)) _ (fun n => (angle_mem (orbit z n)).2)

private theorem fixed_survives {z : Circle} {u θ : ℝ} (h : angle z = u)
    (step : ∀ w : Circle, angle w = u → angle (w^2) = u) (hu : u < θ) : Survives θ z := by
  have hs (n : ℕ) : angle (orbit z n) = u := by
    induction n with
    | zero => simpa [orbit] using h
    | succ n ih => rw [orbit_next]; exact step _ ih
  exact fun n => (hs n).trans_lt hu

theorem sufficient {θ : ℝ} (hθ : cubic < θ) (z : Circle) (h : CubicAngle (angle z)) : Survives θ z := by
  rcases h with h | ⟨k,h⟩
  · refine fixed_survives h (fun w hw => ?_) (cubic_pos.trans hθ)
    rw [square_low w (by rw [hw]; linarith only [Real.pi_pos]),hw,mul_zero]
  · induction k generalizing z with
    | zero =>
      have hz : angle z = cubic := by simpa only [pow_zero,div_one] using h
      refine fixed_survives hz (fun w hw => ?_) hθ
      rw [square_high w (hw ▸ cubic_high),hw]
      unfold cubic
      ring
    | succ k ih =>
      have hp : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
      have hd : angle z = (cubic/(2:ℝ)^k)/2 := by rw [h,pow_succ,div_mul_eq_div_div]
      have hb := div_le_self cubic_pos.le hp
      have low : angle z ≤ Real.pi/2 := by linarith only [hd,hb,cubic_le_pi]
      apply (survives_square θ z).mpr
      refine ⟨by linarith only [hd,hb,hθ,cubic_pos],ih _ ?_⟩
      rw [square_low z low,hd]
      ring

/-- The complete list of surviving unsigned angles throughout the strict cubic window. -/
theorem survives_iff (θ : Set.Ioc cubic fifth) (z : Circle) : Survives θ.val z ↔ CubicAngle (angle z) :=
  ⟨fun h => necessary z (fun k => (h k).trans_le θ.property.2),sufficient θ.property.1 z⟩

private theorem family_le {u : ℝ} (h : CubicAngle u) : u ≤ cubic := by
  rcases h with rfl | ⟨k,rfl⟩
  · exact cubic_pos.le
  · exact div_le_self cubic_pos.le (one_le_pow₀ (by norm_num))

/-- A fifth-root orbit alternates between 4π/5 and 2π/5. -/
theorem fifth_orbit (n : ℕ) : angle (orbit (Circle.exp fifth) n) = fifth ∨
    angle (orbit (Circle.exp fifth) n) = fifth/2 := by
  have hπ := Real.pi_pos
  induction n with
  | zero =>
    left
    simpa only [orbit,pow_zero,pow_one] using exp_angle fifth (by unfold fifth; constructor <;> linarith only [hπ])
  | succ n ih =>
    rw [orbit_next]
    rcases ih with h | h
    · right
      rw [square_high _ (by rw [h]; unfold fifth; linarith only [hπ]),h]
      unfold fifth
      ring
    · left
      rw [square_low _ (by rw [h]; unfold fifth; linarith only [hπ]),h]
      ring

/-- The strict lower and closed upper endpoints are both necessary for this exact phase list. -/
theorem classification_range (θ : ℝ) :
    (∀ z : Circle, Survives θ z ↔ CubicAngle (angle z)) ↔ cubic < θ ∧ θ ≤ fifth := by
  constructor
  · intro h
    have hc := exp_angle cubic ⟨cubic_pos.le,cubic_le_pi⟩
    have hz := (h (Circle.exp cubic)).mpr (Or.inr ⟨0,by simpa only [pow_zero,div_one] using hc⟩)
    refine ⟨hc.symm.trans_lt ((survives_square θ _).mp hz).1,?_⟩
    by_contra! hθ
    have hs : Survives θ (Circle.exp fifth) := by
      intro n
      rcases fifth_orbit n with hn | hn
      · exact hn.trans_lt hθ
      · have hpos := cubic_pos.trans cubic_lt_fifth
        exact hn.trans_lt (by linarith only [hθ,hpos])
    have hf := family_le ((h _).mp hs)
    rw [exp_angle fifth (by unfold fifth; constructor <;> linarith only [Real.pi_pos])] at hf
    exact (not_le.mpr cubic_lt_fifth) hf
  · exact fun ht => survives_iff ⟨θ,ht⟩

#print axioms necessary
#print axioms survives_iff
#print axioms fifth_orbit
#print axioms classification_range

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture
