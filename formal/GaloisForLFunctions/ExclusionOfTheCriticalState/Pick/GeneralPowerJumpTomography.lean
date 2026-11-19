import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianJumpReadings

/-!
# Tomography with any nonlinear monomial momentum jump

Fixing the linear jump fixes the separation of the momenta. Up to exchange
and simultaneous reflection, their remaining parameter is their nonnegative
midpoint. Every power of degree at least two has strictly increasing gap
there. Any such jump therefore replaces the quadratic jump in the Weil
tomography. The image of the two decay rates has an even–odd boundary.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open Set

def halfGap (x y : ℝ) := |x-y|/2
def midMagnitude (x y : ℝ) := |x+y|/2
private def difference (k : ℕ) (d s : ℝ) := (s+d)^k-(s-d)^k

/-- Canonical representative of a pair modulo exchange and reflection. -/
theorem canonical_power_pair (x y : ℝ) :
    let s := midMagnitude x y
    let d := halfGap x y
    indistinguishablePair x y (s+d) (s-d) := by
  dsimp only [midMagnitude,halfGap]
  rcases le_or_gt 0 (x+y) with hs|hs <;> rcases le_or_gt 0 (x-y) with hd|hd
  · rw [abs_of_nonneg hs,abs_of_nonneg hd]
    exact Or.inr (Or.inl ⟨by ring,by ring⟩)
  · rw [abs_of_nonneg hs,abs_of_neg hd]
    exact Or.inr (Or.inr (Or.inl ⟨by ring,by ring⟩))
  · rw [abs_of_neg hs,abs_of_nonneg hd]
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by ring,by ring⟩)))
  · rw [abs_of_neg hs,abs_of_neg hd]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by ring,by ring⟩)))

private theorem canonical_rate (k : ℕ) (x y : ℝ) :
    powerRate k x y = (difference k (halfGap x y) (midMagnitude x y))^2/8 :=
  (all_power_rates_iff _ _ _ _).mpr (canonical_power_pair x y) k

private theorem linear_gap (x y : ℝ) : powerRate 1 x y = halfGap x y^2/2 := by
  simp only [powerRate,gapCost,pow_one,halfGap,div_pow,sq_abs]
  ring

private theorem half_nonneg (x y : ℝ) : 0 ≤ halfGap x y := div_nonneg (abs_nonneg _) (by norm_num)
private theorem mid_nonneg (x y : ℝ) : 0 ≤ midMagnitude x y := div_nonneg (abs_nonneg _) (by norm_num)

private theorem difference_nonneg (k : ℕ) {d s : ℝ} (hd : 0 ≤ d) (hs : 0 ≤ s) :
    0 ≤ difference k d s := by
  have hab : |s-d| ≤ s+d := abs_le.mpr ⟨by linarith,by linarith⟩
  apply sub_nonneg.mpr
  calc (s-d)^k ≤ |(s-d)^k| := le_abs_self _
       _ = |s-d|^k := abs_pow _ _
       _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hab k

private theorem difference_pos (n : ℕ) {d s : ℝ} (hd : 0 < d) (hs : 0 < s) :
    0 < difference (n+1) d s := by
  have hab : |s-d| < s+d := abs_lt.mpr ⟨by linarith,by linarith⟩
  apply sub_pos.mpr
  calc (s-d)^(n+1) ≤ |(s-d)^(n+1)| := le_abs_self _
       _ = |s-d|^(n+1) := abs_pow _ _
       _ < _ := pow_lt_pow_left₀ hab (abs_nonneg _) (Nat.succ_ne_zero _)

private theorem midpoint_strict (n : ℕ) {d : ℝ} (hd : 0 < d) :
    StrictMonoOn (difference (n+2) d) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · unfold difference; fun_prop
  intro s hs
  rw [interior_Ici] at hs
  have h : HasDerivAt (difference (n+2) d)
      (((n+2:ℕ):ℝ)*(s+d)^(n+1)-((n+2:ℕ):ℝ)*(s-d)^(n+1)) s := by
    change HasDerivAt (fun x : ℝ => (x+d)^(n+2)-(x-d)^(n+2)) _ s
    simpa only [show n+2-1=n+1 by omega,id_eq,mul_one] using
      ((((hasDerivAt_id s).add_const d).pow (n+2)).sub (((hasDerivAt_id s).sub_const d).pow (n+2)))
  rw [h.deriv,← mul_sub]
  exact mul_pos (by positivity) (difference_pos n hd hs)

/-- At every degree k≥2, the linear and kth power jumps classify a pair
up to exchange and common reflection, with all diagonal pairs invisible. -/
theorem any_nonlinear_pair_classifies (n : ℕ) (x y u v : ℝ) :
    powerRate 1 x y = powerRate 1 u v ∧ powerRate (n+2) x y = powerRate (n+2) u v ↔
      indistinguishablePair x y u v := by
  constructor
  · rintro ⟨h1,hk⟩
    rw [linear_gap,linear_gap] at h1
    have hd := (sq_eq_sq₀ (half_nonneg x y) (half_nonneg u v)).mp
      (by linarith only [h1] : halfGap x y^2=halfGap u v^2)
    by_cases hd0 : halfGap x y=0
    · have zero {a b : ℝ} (h : halfGap a b=0) : a=b := by
        apply sub_eq_zero.mp
        simpa [halfGap] using h
      exact Or.inl ⟨zero hd0,zero (hd.symm.trans hd0)⟩
    have hdpos := lt_of_le_of_ne (half_nonneg x y) (Ne.symm hd0)
    rw [canonical_rate,canonical_rate,← hd] at hk
    have hp := difference_nonneg (n+2) (half_nonneg x y) (mid_nonneg x y)
    have hq := difference_nonneg (n+2) (half_nonneg x y) (mid_nonneg u v)
    have he : difference (n+2) (halfGap x y) (midMagnitude x y) =
        difference (n+2) (halfGap x y) (midMagnitude u v) :=
      (sq_eq_sq₀ hp hq).mp (by linarith only [hk])
    have hm := (midpoint_strict n hdpos).injOn (mid_nonneg x y) (mid_nonneg u v) he
    apply (all_power_rates_iff _ _ _ _).mp
    intro k
    rw [canonical_rate,canonical_rate,hm,hd]
  · intro h
    exact ⟨(all_power_rates_iff _ _ _ _).mpr h 1,(all_power_rates_iff _ _ _ _).mpr h (n+2)⟩

private theorem gap_image (n : ℕ) {d : ℝ} (hd : 0 < d) (z : ℝ)
    (hz : difference (n+2) d 0 ≤ z) : ∃ s ∈ Ici (0:ℝ), difference (n+2) d s = z := by
  let S := max (max d 1) (z/(2*d))
  have h0 : d ≤ S := (le_max_left d 1).trans (le_max_left _ _)
  have h1 : 1 ≤ S := (le_max_right d 1).trans (le_max_left _ _)
  have hZ : z ≤ 2*d*S := by
    have he := (div_le_iff₀ (by positivity : 0 < 2*d)).mp (le_max_right (max d 1) (z/(2*d)))
    linarith only [he]
  have hp : S+d ≤ (S+d)^(n+1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_left (by linarith only [hd,h1]) (one_le_pow₀ (by linarith only [h1,hd]))
  have hq := pow_le_pow_left₀ (sub_nonneg.mpr h0) (show S-d ≤ S+d by linarith only [hd]) (n+1)
  have hdiff : 2*d*(S+d)^(n+1) ≤ difference (n+2) d S := by
    unfold difference
    rw [pow_succ (S+d) (n+1),pow_succ (S-d) (n+1)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr hq)]
  have hb := hZ.trans ((mul_le_mul_of_nonneg_left
    ((le_add_of_nonneg_right hd.le).trans hp) (by positivity : 0 ≤ 2*d)).trans hdiff)
  have hc : Continuous (difference (n+2) d) := by unfold difference; fun_prop
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc (hd.le.trans h0) hc.continuousOn
    (show z ∈ Icc (difference (n+2) d 0) (difference (n+2) d S) from ⟨hz,hb⟩)
  exact ⟨s,hs.1,he⟩

/-- Lowest nonlinear rate at a specified positive linear rate. An even
power is blind on a reflected pair. An odd power retains its full separation. -/
def minimumPowerRate (k : ℕ) (a : ℝ) := if Even k then 0 else (2*a)^k/2

private theorem minimum_gap (k : ℕ) (d : ℝ) :
    difference k d 0 ^ 2/8 = minimumPowerRate k (d^2/2) := by
  rcases Nat.even_or_odd k with he|ho
  · simp [difference,minimumPowerRate,he,he.neg_pow]
  · have he : ¬ Even k := by
      rintro ⟨i,hi⟩
      obtain ⟨j,hj⟩ := ho
      omega
    simp only [minimumPowerRate,if_neg he,difference,zero_add,zero_sub,ho.neg_pow,
      sub_neg_eq_add,show 2*(d^2/2) = d^2 by ring,← pow_mul]
    rw [Nat.mul_comm 2 k,pow_mul]
    ring

/-- Exact joint image of linear decay and arbitrary higher monomial decay.
Every allowed pair is attained by actual real momenta. -/
theorem nonlinear_rate_image (n : ℕ) (a b : ℝ) :
    (∃ x y, powerRate 1 x y=a ∧ powerRate (n+2) x y=b) ↔
      (a=0 ∧ b=0) ∨ (0<a ∧ minimumPowerRate (n+2) a ≤ b) := by
  constructor
  · rintro ⟨x,y,rfl,rfl⟩
    by_cases hxy : x=y
    · left; simp [powerRate,gapCost,hxy]
    let d := halfGap x y
    let s := midMagnitude x y
    have hd : 0 < d := div_pos (abs_pos.mpr (sub_ne_zero.mpr hxy)) (by norm_num)
    have hmono := (midpoint_strict n hd).monotoneOn (show (0:ℝ) ∈ Ici 0 from le_refl (0:ℝ))
      (show s ∈ Ici 0 from mid_nonneg x y) (mid_nonneg x y)
    rw [linear_gap,canonical_rate (n+2)]
    right
    refine ⟨div_pos (sq_pos_of_pos hd) (by norm_num),?_⟩
    rw [← minimum_gap]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (difference_nonneg _ hd.le le_rfl) hmono 2)
      (by norm_num)
  · rintro (⟨rfl,rfl⟩|⟨ha,hb⟩)
    · exact ⟨0,0,by simp [powerRate,gapCost],by simp [powerRate,gapCost]⟩
    let d := Real.sqrt (2*a)
    have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
    have he : d^2 = 2*a := Real.sq_sqrt (by positivity)
    have ha' : d^2/2=a := by rw [he]; ring
    rw [← ha',← minimum_gap] at hb
    have h0 := difference_nonneg (n+2) hd.le (le_refl 0)
    have hbp : 0 ≤ 8*b := by linarith only [hb,sq_nonneg (difference (n+2) d 0)]
    have hz : difference (n+2) d 0 ≤ Real.sqrt (8*b) :=
      (Real.le_sqrt h0 hbp).mpr (by linarith only [hb])
    obtain ⟨s,_,hs⟩ := gap_image n hd _ hz
    refine ⟨s+d,s-d,?_,?_⟩
    · simp only [powerRate,gapCost,pow_one]
      linear_combination he/2
    · change difference (n+2) d s^2/8=b
      rw [hs,Real.sq_sqrt hbp]
      ring

/-- Either nonlinear monomial, together with the linear jump, reads the
entire power-jump experiment on the arithmetic matrix. -/
theorem any_nonlinear_weil_readouts {n : ℕ} (k : ℕ) (r s : Fin n → ℝ)
    (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (jumpReadout 1 r p=jumpReadout 1 s p ∧ jumpReadout (k+2) r p=jumpReadout (k+2) s p) ↔
      ∀ j, jumpReadout j r p=jumpReadout j s p := by
  constructor
  · rintro ⟨h1,hk⟩
    apply (two_readouts_determine_all r s p).mpr
    apply (jumpReadouts_classify r s p).mpr
    have rateEq (j : ℕ) (h : jumpReadout j r p=jumpReadout j s p) (a b : Fin n) :
        powerRate j (r a) (r b)=powerRate j (s a) (s b) := by
      have hab := congrFun (congrFun h a) b
      change (Real.exp (-powerRate j (r a) (r b)) : ℂ)*_ =
        (Real.exp (-powerRate j (s a) (s b)) : ℂ)*_ at hab
      exact neg_inj.mp (Real.exp_injective (Complex.ofReal_inj.mp
        (mul_right_cancel₀ (safe_probeGram_entry_ne_zero p a b) hab)))
    intro a b
    exact (any_nonlinear_pair_classifies k _ _ _ _).mp ⟨rateEq _ h1 _ _,rateEq _ hk _ _⟩
  · exact fun h => ⟨h 1,h (k+2)⟩

#print axioms canonical_power_pair
#print axioms any_nonlinear_pair_classifies
#print axioms nonlinear_rate_image
#print axioms any_nonlinear_weil_readouts
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
