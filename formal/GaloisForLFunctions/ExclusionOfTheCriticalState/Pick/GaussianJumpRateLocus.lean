import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianJumpReadings

/-!
# Realizable Gaussian momentum-jump rates

Linear and quartic jumps already resolve the same pairs as linear and
quadratic jumps. The exact image of all three measurements is a surface
with a collapsed zero-rate fiber. Two even-power measurements instead
recover both squared momenta up to exchange, away from their common
zero-rate fiber. These distinctions persist in the signed Weil readouts.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk

private theorem rate_nonneg (k : ℕ) (x y : ℝ) : 0 ≤ powerRate k x y :=
  div_nonneg (sq_nonneg _) (by norm_num)

/-- Any positive linear rate and nonnegative quadratic rate occur together.
The adjacent and total momenta are their two square-root coordinates. -/
theorem realize_linear_quadratic (a b : ℝ) :
    (∃ x y, powerRate 1 x y = a ∧ powerRate 2 x y = b) ↔
      (a = 0 ∧ b = 0) ∨ (0 < a ∧ 0 ≤ b) := by
  constructor
  · rintro ⟨x,y,rfl,rfl⟩
    by_cases h : x = y
    · left; simp [powerRate,gapCost,h]
    · exact Or.inr ⟨div_pos (by simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (by norm_num),
        rate_nonneg _ _ _⟩
  · rintro (⟨rfl,rfl⟩|⟨ha,hb⟩)
    · exact ⟨0,0,by simp [powerRate,gapCost],by simp [powerRate,gapCost]⟩
    · let d := Real.sqrt (8*a)
      let s := Real.sqrt (b/a)
      have hd : d^2 = 8*a := Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)
      have hs : s^2 = b/a := Real.sq_sqrt (div_nonneg hb ha.le)
      refine ⟨(s+d)/2,(s-d)/2,?_,?_⟩
      · unfold powerRate gapCost
        simp only [pow_one]
        linear_combination hd/8
      · have hfac : ((s+d)/2)^2-((s-d)/2)^2 = s*d := by ring
        simp only [powerRate,gapCost,hfac,mul_pow,hd,hs]
        field_simp [ha.ne']

/-- Exact semialgebraic criterion for three Gaussian jump rates to come
from a single pair. The isolated boundary in the linear coordinate forces
all three rates to vanish. -/
theorem gaussian_rate_locus (a b c : ℝ) :
    (∃ x y, powerRate 1 x y = a ∧ powerRate 2 x y = b ∧ powerRate 4 x y = c) ↔
      (a = 0 ∧ b = 0 ∧ c = 0) ∨ (0 < a ∧ 0 ≤ b ∧ 4*a^2*c = b*(8*a^2+b)^2) := by
  constructor
  · rintro ⟨x,y,rfl,rfl,rfl⟩
    by_cases h : x = y
    · left; simp [powerRate,gapCost,h]
    · right
      exact ⟨div_pos (by simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (by norm_num),
        rate_nonneg _ _ _,quartic_readout_identity x y⟩
  · rintro (⟨rfl,rfl,rfl⟩|⟨ha,hb,hc⟩)
    · exact ⟨0,0,by simp [powerRate,gapCost],by simp [powerRate,gapCost],by simp [powerRate,gapCost]⟩
    · obtain ⟨x,y,hx,hy⟩ := (realize_linear_quadratic a b).mpr (Or.inr ⟨ha,hb⟩)
      have he := quartic_readout_identity x y
      dsimp only at he
      rw [hx,hy,← hc] at he
      exact ⟨x,y,hx,hy,mul_left_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha.ne')) he⟩

private theorem monotone_cubic (u : ℝ) (hu : 0 ≤ u) {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) :
    b*(u+b)^2 = d*(u+d)^2 → b = d := by
  have strict {x y : ℝ} (hx : 0 ≤ x) (h : x < y) : x*(u+x)^2 < y*(u+y)^2 := by
    have hs : (u+x)^2 ≤ (u+y)^2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr h.le) (show 0 ≤ 2*u+x+y by linarith only [hu,hx,h])]
    exact (mul_le_mul_of_nonneg_left hs hx).trans_lt
      (mul_lt_mul_of_pos_right h (sq_pos_of_pos (by linarith only [hu,hx,h])))
  intro he
  rcases lt_trichotomy b d with h|h|h
  · exact False.elim ((strict hb h).ne he)
  · exact h
  · exact False.elim ((strict hd h).ne he.symm)

/-- Quartic decay can replace quadratic decay in two-measurement tomography.
The result includes collisions where all power rates vanish. -/
theorem linear_quartic_classify (x y u v : ℝ) :
    powerRate 1 x y = powerRate 1 u v ∧ powerRate 4 x y = powerRate 4 u v ↔
      indistinguishablePair x y u v := by
  constructor
  · rintro ⟨h1,h4⟩
    apply (pair_two_rates_iff _ _ _ _).mp
    refine ⟨h1,?_⟩
    have hs := quartic_readout_identity x y
    have ht := quartic_readout_identity u v
    dsimp only at hs ht
    rw [h1,h4] at hs
    exact monotone_cubic _ (mul_nonneg (by norm_num) (sq_nonneg _)) (rate_nonneg _ _ _)
      (rate_nonneg _ _ _) (hs.symm.trans ht)
  · intro h
    have hr := (all_power_rates_iff _ _ _ _).mpr h
    exact ⟨hr 1,hr 4⟩

/-- The quadratic and quartic rates have the sharp parabolic lower bound.
Equality holds exactly at equal squared momenta or a zero momentum. -/
theorem even_rate_boundary (x y : ℝ) :
    8*(powerRate 2 x y)^2 ≤ powerRate 4 x y ∧
      (8*(powerRate 2 x y)^2 = powerRate 4 x y ↔ x^2 = y^2 ∨ x = 0 ∨ y = 0) := by
  have he : powerRate 4 x y-8*(powerRate 2 x y)^2 = ((x^2-y^2)*x*y)^2/2 := by
    unfold powerRate gapCost
    ring
  refine ⟨sub_nonneg.mp (by rw [he]; positivity),?_⟩
  rw [eq_comm,← sub_eq_zero,he]
  simp [mul_eq_zero,sub_eq_zero,or_assoc]

/-- Every point strictly above the zero quadratic rate and on or above
the parabola is physically realized, even with nonnegative momenta. -/
theorem even_rates_realizable (b c : ℝ) :
    (∃ x y : ℝ, 0 ≤ y ∧ y ≤ x ∧ powerRate 2 x y = b ∧ powerRate 4 x y = c) ↔
      (b = 0 ∧ c = 0) ∨ (0 < b ∧ 8*b^2 ≤ c) := by
  constructor
  · rintro ⟨x,y,_,_,rfl,rfl⟩
    rcases (rate_nonneg 2 x y).eq_or_lt with h|h
    · left
      have he : x^2 = y^2 := by
        apply sub_eq_zero.mp
        simpa [powerRate,gapCost] using h.symm
      exact ⟨h.symm,by simp [powerRate,gapCost,show x^4 = y^4 by linear_combination (x^2+y^2)*he]⟩
    · exact Or.inr ⟨h,(even_rate_boundary x y).1⟩
  · rintro (⟨rfl,rfl⟩|⟨hb,hc⟩)
    · exact ⟨0,0,le_rfl,le_rfl,by simp [powerRate,gapCost],by simp [powerRate,gapCost]⟩
    · let d := Real.sqrt (8*b)
      let s := Real.sqrt (c/b)
      have h8 : 8*b ≤ c/b := (le_div_iff₀ hb).mpr (by linear_combination hc)
      have hs : d ≤ s := Real.sqrt_le_sqrt h8
      have hd : d^2 = 8*b := Real.sq_sqrt (by positivity)
      have ht : s^2 = c/b := Real.sq_sqrt ((by positivity : 0 ≤ 8*b).trans h8)
      let x := Real.sqrt ((s+d)/2)
      let y := Real.sqrt ((s-d)/2)
      have hx : x^2 = (s+d)/2 := Real.sq_sqrt (by dsimp only [s,d]; positivity)
      have hy : y^2 = (s-d)/2 := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hs) (by norm_num))
      have hn : 0 ≤ d := Real.sqrt_nonneg _
      have hxy : y ≤ x := Real.sqrt_le_sqrt (by linarith only [hn])
      have he : x^2-y^2 = d := by rw [hx,hy]; ring
      have hf : x^4-y^4 = d*s := by
        rw [show x^4-y^4 = (x^2-y^2)*(x^2+y^2) by ring,he,hx,hy]
        ring
      refine ⟨x,y,Real.sqrt_nonneg _,hxy,?_,?_⟩
      · simp only [powerRate,gapCost,he,hd]; ring
      · simp only [powerRate,gapCost,hf,mul_pow,hd,ht]; field_simp [hb.ne']

/-- The two even powers measure the unordered squared momenta. When
both readings vanish, any pair with equal magnitudes is indistinguishable. -/
theorem even_rates_classify (x y u v : ℝ) :
    powerRate 2 x y = powerRate 2 u v ∧ powerRate 4 x y = powerRate 4 u v ↔
      ((x^2 = y^2 ∧ u^2 = v^2) ∨
       (x^2 = u^2 ∧ y^2 = v^2) ∨ (x^2 = v^2 ∧ y^2 = u^2)) := by
  have h (a b : ℝ) : powerRate 2 (a^2) (b^2) = powerRate 4 a b := by
    simp only [powerRate,gapCost,← pow_mul]
  have hl (a b : ℝ) : powerRate 1 (a^2) (b^2) = powerRate 2 a b := by
    simp only [powerRate,gapCost,pow_one]
  rw [← h,← h,← hl,← hl,pair_two_rates_iff]
  constructor
  · rintro (hz|hp|hp|⟨hx,hy⟩|⟨hx,hy⟩)
    · exact Or.inl hz
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr hp)
    all_goals left; constructor <;> linarith only [hx,hy,sq_nonneg x,sq_nonneg y,sq_nonneg u,sq_nonneg v]
  · rintro (hz|hp|hp)
    · exact Or.inl hz
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hp))

#print axioms realize_linear_quadratic
#print axioms gaussian_rate_locus
#print axioms linear_quartic_classify
#print axioms even_rate_boundary
#print axioms even_rates_realizable
#print axioms even_rates_classify
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
