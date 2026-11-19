import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianLimitOfProbeDephasing
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.WeilPairScattering

/-!
# Which momentum jumps can a finite Weil probe distinguish?

In the Gaussian weak-step limit the linear and quadratic jump rates
determine every power-jump rate. Positive entries of the signed Weil
matrix expose every pair. Two different momenta are identified up to exchange and common
reflection. A diagonal pair has zero decay at every power.
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk

/-- Decay exponent for the jump p ↦ pᵏ in the weak-step normalization. -/
def powerRate (k : ℕ) (x y : ℝ) := gapCost (x^k) (y^k)

private theorem sq_choices {a b : ℝ} (h : a^2 = b^2) : a = b ∨ a = -b := by
  have e : (a-b)*(a+b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp e with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linarith only [h])

/-- The observable equivalence relation on pairs of momenta. -/
def indistinguishablePair (x y u v : ℝ) : Prop :=
  (x = y ∧ u = v) ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) ∨
    (x = -u ∧ y = -v) ∨ (x = -v ∧ y = -u)

private theorem reflected_rate (k : ℕ) (x y : ℝ) : powerRate k (-x) (-y) = powerRate k x y := by
  unfold powerRate gapCost
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_pow,h.neg_pow]
  · rw [h.neg_pow,h.neg_pow]
    ring

private theorem swapped_rate (k : ℕ) (x y : ℝ) : powerRate k x y = powerRate k y x := by
  unfold powerRate gapCost
  ring

private theorem all_rates {x y u v : ℝ} (h : indistinguishablePair x y u v) (k : ℕ) :
    powerRate k x y = powerRate k u v := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simp [powerRate,gapCost]
  · rfl
  · exact swapped_rate _ _ _
  · exact reflected_rate _ _ _
  · exact (reflected_rate _ _ _).trans (swapped_rate _ _ _)

/-- Two jump measurements classify a pair, including the entire unobservable diagonal. -/
theorem pair_two_rates_iff (x y u v : ℝ) :
    powerRate 1 x y = powerRate 1 u v ∧ powerRate 2 x y = powerRate 2 u v ↔
      indistinguishablePair x y u v := by
  constructor
  · rintro ⟨h1,h2⟩
    simp only [powerRate,gapCost,pow_one] at h1 h2
    have hd : (x-y)^2 = (u-v)^2 := by linarith only [h1]
    by_cases hxy : x = y
    · left
      have hz : (u-v)^2 = 0 := by simpa [hxy] using hd.symm
      exact ⟨hxy,sub_eq_zero.mp (sq_eq_zero_iff.mp hz)⟩
    have hmult : (x-y)^2 * (x+y)^2 = (x-y)^2 * (u+v)^2 := by
      conv_rhs => rw [hd]
      nlinarith only [h2]
    have hs := mul_left_cancel₀ (pow_ne_zero 2 (sub_ne_zero.mpr hxy)) hmult
    rcases sq_choices hd with h | h <;> rcases sq_choices hs with g | g
    · exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith,by linarith⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩)))
  · intro h
    exact ⟨all_rates h 1,all_rates h 2⟩

/-- All powers, including the quartic model, have precisely the same joint
identifiability as powers one and two. -/
theorem all_power_rates_iff (x y u v : ℝ) :
    (∀ k, powerRate k x y = powerRate k u v) ↔ indistinguishablePair x y u v :=
  ⟨fun h => (pair_two_rates_iff _ _ _ _).mp ⟨h 1,h 2⟩, all_rates⟩

/-- Elimination of the unobserved momenta gives an exact consistency test
for the three decay rates in the linear, quadratic and quartic models. -/
theorem quartic_readout_identity (x y : ℝ) :
    let a := powerRate 1 x y
    let b := powerRate 2 x y
    let c := powerRate 4 x y
    4*a^2*c = b*(8*a^2+b)^2 := by
  simp only [powerRate,gapCost,pow_one]
  ring

/-- Finite Gaussian readout on the signed arithmetic Gram matrix. -/
def jumpReadout {n : ℕ} (k : ℕ) (r : Fin n → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j =>
  (Real.exp (-powerRate k (r i) (r j)) : ℂ) * probeGram (fun l => (p l).val) i j

theorem reading_eq_iff (a b : ℝ) (z : ℂ) :
    (Real.exp (-a) : ℂ)*z = (Real.exp (-b) : ℂ)*z ↔ z = 0 ∨ a = b := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz,false_or,mul_left_inj' hz,Complex.ofReal_inj,Real.exp_injective.eq_iff,neg_inj]

/-- The actual Weil matrix reveals the two-label class on every pair. -/
theorem jumpReadouts_classify {n : ℕ} (r s : Fin n → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (jumpReadout 1 r p = jumpReadout 1 s p ∧ jumpReadout 2 r p = jumpReadout 2 s p) ↔
      ∀ i j, indistinguishablePair (r i) (r j) (s i) (s j) := by
  constructor
  · rintro ⟨h1,h2⟩ i j
    have hz := safe_probeGram_entry_ne_zero p i j
    apply (pair_two_rates_iff _ _ _ _).mp
    exact ⟨((reading_eq_iff _ _ _).mp (Matrix.ext_iff.mpr h1 i j)).resolve_left hz,
      ((reading_eq_iff _ _ _).mp (Matrix.ext_iff.mpr h2 i j)).resolve_left hz⟩
  · intro h
    have hread (k : ℕ) : jumpReadout k r p = jumpReadout k s p := by
      ext i j
      exact (reading_eq_iff _ _ _).mpr (Or.inr (all_rates (h i j) k))
    exact ⟨hread 1,hread 2⟩

/-- Equality of the first two arithmetic matrices is sufficient for equality
of the whole power-jump experiment, without any nonvanishing condition on probes. -/
theorem two_readouts_determine_all {n : ℕ} (r s : Fin n → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (∀ k, jumpReadout k r p = jumpReadout k s p) ↔
      jumpReadout 1 r p = jumpReadout 1 s p ∧ jumpReadout 2 r p = jumpReadout 2 s p := by
  refine ⟨fun h => ⟨h 1,h 2⟩,fun h k => ?_⟩
  ext i j
  exact (reading_eq_iff _ _ _).mpr (Or.inr (all_rates ((jumpReadouts_classify r s p).mp h i j) k))

private theorem line_isometry {ι : Type*} (o : ι) (r s : ι → ℝ)
    (h : ∀ i j, powerRate 1 (r i) (r j) = powerRate 1 (s i) (s j)) :
    ∃ e b : ℝ, (e = 1 ∨ e = -1) ∧ ∀ i, s i = e*(r i+b) := by
  have hd (i j : ι) : (r i-r j)^2 = (s i-s j)^2 := by
    have hij := h i j
    simp only [powerRate,gapCost,pow_one] at hij
    linarith only [hij]
  have hp (i j : ι) :
      (r i-r o)*(r j-r o) = (s i-s o)*(s j-s o) := by
    linarith only [hd i o,hd j o,hd i j]
  by_cases hn : ∃ j, r j ≠ r o
  · obtain ⟨j,hj⟩ := hn
    obtain ⟨e,he,hj'⟩ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ s j-s o = e*(r j-r o) := by
      rcases sq_choices (hd j o).symm with h | h
      · exact ⟨1,Or.inl rfl,by simpa only [one_mul] using h⟩
      · exact ⟨-1,Or.inr rfl,by simpa only [neg_one_mul] using h⟩
    refine ⟨e,e*s o-r o,he,fun i => ?_⟩
    have hi : s i-s o = e*(r i-r o) := by
      apply mul_right_cancel₀ (sub_ne_zero.mpr hj)
      have hg := hp i j
      rw [hj'] at hg
      rcases he with rfl | rfl <;> linarith only [hg]
    rcases he with rfl | rfl <;> linarith only [hi]
  · push Not at hn
    refine ⟨1,s o-r o,Or.inl rfl,fun i => ?_⟩
    have hz : (s i-s o)^2 = 0 := by simpa [hn i] using (hd i o).symm
    rw [sub_eq_zero.mp (sq_eq_zero_iff.mp hz),hn i]
    ring

/-- The quadratic jump detects an arbitrary translation of a pair except at
a collision or at the unique shift that exchanges the negated endpoints. -/
theorem quadratic_shift_iff (x y b : ℝ) :
    powerRate 2 (x+b) (y+b) = powerRate 2 x y ↔
      b = 0 ∨ x = y ∨ x+y = -b := by
  have he : powerRate 2 (x+b) (y+b) - powerRate 2 x y =
      (b*(x-y)^2*(x+y+b))/2 := by unfold powerRate gapCost; ring
  rw [← sub_eq_zero,he]
  simp only [div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false,mul_eq_zero,
    sq_eq_zero_iff,sub_eq_zero,add_eq_zero_iff_eq_neg,or_assoc]

/-- The complete ambiguity of the linear and quadratic Weil readouts is a
common reflection and a translation. A nonzero translation is allowed only
when all distinct-value pairs have the same sum. -/
theorem jumpReadouts_global_iff {n : ℕ} (r s : Fin (n+1) → ℝ)
    (p : Fin (n+1) → {x : ℝ // 1 ≤ x}) :
    (jumpReadout 1 r p = jumpReadout 1 s p ∧ jumpReadout 2 r p = jumpReadout 2 s p) ↔
      ∃ e b : ℝ, (e = 1 ∨ e = -1) ∧ (∀ i, s i = e*(r i+b)) ∧
        (b = 0 ∨ ∀ i j, r i = r j ∨ r i+r j = -b) := by
  rw [jumpReadouts_classify]
  constructor
  · intro h
    obtain ⟨e,b,he,hs⟩ := line_isometry 0 r s (fun i j => all_rates (h i j) 1)
    refine ⟨e,b,he,hs,?_⟩
    by_cases hb : b = 0
    · exact Or.inl hb
    · right
      intro i j
      have h2 := (all_rates (h i j) 2).symm
      rw [hs i,hs j] at h2
      rcases he with rfl | rfl
      · simp only [one_mul] at h2
        exact ((quadratic_shift_iff _ _ _).mp h2).resolve_left hb
      · simp only [neg_one_mul,reflected_rate] at h2
        exact ((quadratic_shift_iff _ _ _).mp h2).resolve_left hb
  · rintro ⟨e,b,he,hs,hb⟩ i j
    apply (pair_two_rates_iff _ _ _ _).mp
    have h2 := (quadratic_shift_iff (r i) (r j) b).mpr (hb.imp_right fun h => h i j)
    have h1 : powerRate 1 (r i+b) (r j+b) = powerRate 1 (r i) (r j) := by
      unfold powerRate gapCost
      ring
    rw [hs i,hs j]
    rcases he with rfl | rfl <;> simp only [one_mul,neg_one_mul,reflected_rate] <;>
      exact ⟨h1.symm,h2.symm⟩

/-- Every unresolved translation forces a two-level spectrum. In particular,
three distinct momenta determine the whole bank up to common reflection. -/
theorem jumpReadouts_three_levels {n : ℕ} (r s : Fin (n+1) → ℝ)
    (p : Fin (n+1) → {x : ℝ // 1 ≤ x}) :
    (jumpReadout 1 r p = jumpReadout 1 s p ∧ jumpReadout 2 r p = jumpReadout 2 s p) →
      s = r ∨ s = -r ∨ ∀ i j k, r i = r j ∨ r i = r k ∨ r j = r k := by
  intro h
  obtain ⟨e,b,he,hs,hb⟩ := (jumpReadouts_global_iff r s p).mp h
  rcases hb with rfl | hsum
  · rcases he with rfl | rfl
    · left; funext i; simpa only [add_zero,one_mul] using hs i
    · right; left; funext i
      simpa only [Pi.neg_apply,add_zero,neg_one_mul] using hs i
  · right; right
    intro i j k
    rcases hsum i j with h | hij
    · exact Or.inl h
    rcases hsum i k with h | hik
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by linarith only [hij,hik]))

#print axioms quadratic_shift_iff
#print axioms jumpReadouts_global_iff
#print axioms jumpReadouts_three_levels
#print axioms pair_two_rates_iff
#print axioms all_power_rates_iff
#print axioms quartic_readout_identity
#print axioms jumpReadouts_classify
#print axioms two_readouts_determine_all
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
