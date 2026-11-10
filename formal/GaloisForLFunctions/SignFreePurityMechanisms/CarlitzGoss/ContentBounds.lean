import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentPartitions

/-!
# Removing one digit-content layer

The constant content p−1 has inverse coordinates one. Since every coefficient
of the inverse cyclic difference is positive, any strictly smaller content
vector has all inverse coordinates strictly below one. Removing a proper
sublayer therefore preserves a strict feasibility margin.

Weighted divisibility makes all inverse coordinates integral, so a strict
natural-number threshold rounds up to the next integer.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss
variable {s : ℕ}

theorem inverseContent_sub (p : ℚ) (u v : ZMod s → ℚ) (h : ZMod s) :
    inverseContent p (u - v) h = inverseContent p u h - inverseContent p v h := by
  simp only [inverseContent, cyclicWeighted, Pi.sub_apply, mul_sub, sum_sub_distrib, sub_div]

variable [NeZero s]

theorem inverseContent_mono {p : ℚ} (hp : 1 < p) {u v : ZMod s → ℚ}
    (huv : ∀ h, u h ≤ v h) (h : ZMod s) : inverseContent p u h ≤ inverseContent p v h := by
  apply div_le_div_of_nonneg_right
  · exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (huv _) (pow_nonneg (by linarith only [hp]) _)
  · exact (sub_pos.mpr (one_lt_pow₀ hp (NeZero.ne s))).le

/-- Constant content p−1 has every inverse coordinate equal to one. -/
theorem inverseContent_full_layer {p : ℚ} (hp : 1 < p) :
    inverseContent p (fun _ : ZMod s => p - 1) = fun _ => 1 := by
  have he : (fun _ : ZMod s => p - 1) = cyclicDifference p (fun _ => 1) := by
    funext h
    simp only [cyclicDifference, mul_one]
  rw [he, inverseContent_cyclicDifference p (ne_of_gt (one_lt_pow₀ hp (NeZero.ne s)))]

/-- A digit-content vector bounded by p−1 in every class has inverse coordinates at most one. -/
theorem inverseContent_le_one {p : ℚ} (hp : 1 < p) {v : ZMod s → ℚ}
    (hv : ∀ h, v h ≤ p - 1) (h : ZMod s) : inverseContent p v h ≤ 1 := by
  have hh := inverseContent_mono hp hv h
  simpa only [inverseContent_full_layer hp] using hh

/-- The upper bound is strict in every coordinate unless the whole constant layer is removed. -/
theorem inverseContent_lt_one {p : ℚ} (hp : 1 < p) {v : ZMod s → ℚ}
    (hv : ∀ h, v h ≤ p - 1) (hne : v ≠ fun _ => p - 1) (h : ZMod s) :
    inverseContent p v h < 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hpos := inverseContent_pos hp (u := (fun _ : ZMod s => p - 1) - v)
    (fun k => sub_nonneg.mpr (hv k))
    ⟨j, sub_pos.mpr (lt_of_le_of_ne (hv j) hj)⟩ h
  rw [inverseContent_sub, inverseContent_full_layer hp] at hpos
  linarith only [hpos]

/-- Removing at most one full layer lowers every inverse-content coordinate by at most one. -/
theorem inverseContent_sub_layer_ge {p : ℚ} (hp : 1 < p) {u v : ZMod s → ℚ} {c : ℚ}
    (hu : ∀ h, c ≤ inverseContent p u h) (hv : ∀ h, v h ≤ p - 1) (h : ZMod s) :
    c - 1 ≤ inverseContent p (u - v) h := by
  rw [inverseContent_sub]
  have hh := inverseContent_le_one hp hv h
  linarith only [hu h, hh]

/-- A proper sublayer leaves a strict margin in every inverse-content coordinate. -/
theorem inverseContent_sub_layer_gt {p : ℚ} (hp : 1 < p) {u v : ZMod s → ℚ} {c : ℚ}
    (hu : ∀ h, c ≤ inverseContent p u h) (hv : ∀ h, v h ≤ p - 1)
    (hne : v ≠ fun _ => p - 1) (h : ZMod s) :
    c - 1 < inverseContent p (u - v) h := by
  rw [inverseContent_sub]
  have hh := inverseContent_lt_one hp hv hne h
  linarith only [hu h, hh]

/-- The weighted divisibility congruence makes every inverse-content coordinate integral. -/
theorem inverseContent_integral (p : ℕ) (hp : 2 ≤ p) (u : ZMod s → ℤ)
    (hu : ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) u 0) :
    ∃ a : ZMod s → ℤ, inverseContent (p : ℚ) (fun h => (u h : ℚ)) = fun h => (a h : ℚ) := by
  obtain ⟨a, ha⟩ := (exists_cyclicDifference_eq_iff p hp u).mpr hu
  have hE : cyclicDifference (p : ℚ) (fun h => (a h : ℚ)) = fun h => (u h : ℚ) := by
    funext h
    have hh := congrFun ha h
    dsimp only [cyclicDifference] at hh ⊢
    exact_mod_cast hh
  have hpQ : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
  refine ⟨a, ?_⟩
  rw [← hE, inverseContent_cyclicDifference _ (ne_of_gt (one_lt_pow₀ hpQ (NeZero.ne s)))]

/-- A strict integer threshold for divisible content rounds up to the next integer. -/
theorem inverseContent_ge_succ_of_divisible (p k : ℕ) (hp : 2 ≤ p) (u : ZMod s → ℤ)
    (hu : ((p : ℤ) ^ s - 1) ∣ cyclicWeighted (p : ℤ) u 0)
    (hgt : ∀ h, (k : ℚ) < inverseContent (p : ℚ) (fun j => (u j : ℚ)) h) :
    ∀ h, ((k + 1 : ℕ) : ℚ) ≤ inverseContent (p : ℚ) (fun j => (u j : ℚ)) h := by
  obtain ⟨a, ha⟩ := inverseContent_integral p hp u hu
  intro h
  have hh := hgt h
  rw [ha] at hh ⊢
  dsimp only at hh ⊢
  have hi : (k : ℤ) < a h := by exact_mod_cast hh
  exact_mod_cast (show (k : ℤ) + 1 ≤ a h by omega)

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.inverseContent_sub_layer_gt

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.inverseContent_ge_succ_of_divisible
