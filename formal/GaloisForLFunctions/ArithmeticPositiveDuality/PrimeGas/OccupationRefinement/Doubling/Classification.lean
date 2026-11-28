import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling.Profiles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Probabilities

/-! # A single doubling equation forces all prime-particle occupation laws -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling

open ArithmeticFunction ModeCapacities

private theorem zero_law : law (0 : ArithmeticFunction ℝ) := by
  intro n
  simp

private theorem zero_vacuum {F : ArithmeticFunction ℝ} (h : law F) (unit : F 1=0) : F=0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 1<n
    · have eqn := recursion h hn
      rw [unit,mul_zero,sub_zero,interior_congr (G:=0) hn ih] at eqn
      have vanish : interior (0 : ArithmeticFunction ℝ) n=0 := by simp [interior]
      rw [vanish] at eqn
      exact (mul_eq_zero.mp eqn).resolve_left (pow_ne_zero _ (by norm_num))
    · rcases (by omega : n=0 ∨ n=1) with rfl|rfl
      · simp
      · simpa using unit

private theorem determined {F G : ArithmeticFunction ℝ} (hf : law F) (hg : law G)
    (uf : F 1=1) (ug : G 1=1) (prime : ∀ p, p.Prime → F p=G p) : F=G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 1<n
    · by_cases hp : n.Prime
      · exact prime n hp
      · have eqn := (recursion hf hn).trans ((interior_congr hn ih).trans (recursion hg hn).symm)
        rw [uf,ug,mul_one] at eqn
        exact mul_left_cancel₀ (composite_coefficient hn hp).ne' eqn
    · rcases (by omega : n=0 ∨ n=1) with rfl|rfl
      · simp
      · exact uf.trans ug.symm

/-- The doubling equation implies multiplicativity and determines every composite
coefficient from the free single-particle weights. -/
theorem classification (F : ArithmeticFunction ℝ) :
    law F ↔ F=0 ∨ F=profile (fun p => F p) := by
  constructor
  · intro h
    rcases vacuum h with hv|hv
    · exact Or.inl (zero_vacuum h hv)
    · exact Or.inr (determined h (profile_law _) hv (profile_one _)
        (fun p hp => (prime_value _ hp).symm))
  · rintro (rfl|h)
    · exact zero_law
    · exact (congrArg law h).mpr (profile_law _)

theorem multiplicative_of_nonzero {F : ArithmeticFunction ℝ} (h : law F) (nz : F≠0) :
    F.IsMultiplicative := by
  have eqn := ((classification F).mp h).resolve_left nz
  exact (congrArg (fun H : ArithmeticFunction ℝ => H.IsMultiplicative) eqn).mpr
    (RHTower.Sieve.localEuler_isMultiplicative _)

/-- Even signed or missing modes have the same balanced branch weights on
every shell of nonzero mass. The undivided identity includes zero-mass shells. -/
theorem balanced_weights (F : ArithmeticFunction ℝ) (h : law F) (a b : ℕ+) :
    F a.val*F b.val=(F*F) (a*b).val*branch 1 1 a.val b.val := by
  rcases (classification F).mp h with rfl|eqn
  · simp
  let g : ℕ → ℝ := fun p => F p
  have shape (m : ℕ+) : F m.val=twistFactor g m*profile 1 m.val := by
    exact (congrArg (fun H : ArithmeticFunction ℝ => H m.val) eqn).trans
      (by simpa only [mul_one] using twist_profile g 1 m)
  have doubled : g+g=g*(1+1) := by rw [mul_add,mul_one]
  have total : (F*F) (a*b).val=twistFactor g (a*b)*profile (1+1) (a*b).val := by
    calc
      _ = (profile g*profile g) (a*b).val := congrArg (fun H : ArithmeticFunction ℝ => (H*H) (a*b).val) eqn
      _ = _ := by rw [profile_add,doubled,twist_profile]
  have pos : positive (1 : ℕ → ℝ) := fun _ => zero_lt_one
  have nz := (profile_pos (positive_add pos pos) (a*b)).ne'
  rw [shape a,shape b,total,twist_mul]
  change _ = _ * (profile 1 a.val*profile 1 b.val/profile (1+1) (a*b).val)
  field_simp [nz]

theorem normalized_routing (F : ArithmeticFunction ℝ) (h : law F) (a b : ℕ+)
    (hn : (F*F) (a*b).val≠0) :
    F a.val*F b.val/(F*F) (a*b).val=branch 1 1 a.val b.val := by
  rw [balanced_weights F h,mul_div_cancel_left₀ _ hn]

#print axioms classification
#print axioms multiplicative_of_nonzero
#print axioms balanced_weights
#print axioms normalized_routing

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Doubling
