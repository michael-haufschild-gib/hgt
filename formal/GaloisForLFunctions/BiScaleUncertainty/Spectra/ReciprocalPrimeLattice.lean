import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# Collisions in reciprocal spectral lattices

The two spacings `b` and `1/b` give distinct lattice labels exactly when
`b²` is irrational. Taking `b² = log q / log p` identifies the obstruction
with equality of the two primes. A common spectral offset changes no collisions.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

/-- Two reciprocal spacings with a common spectral offset. -/
def reciprocalLattice (b c : ℝ) (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) * b + (z.2 : ℝ) / b + c

/-- Rationality of the squared spacing is exactly the collision obstruction. -/
theorem reciprocalLattice_injective_iff (b c : ℝ) :
    Function.Injective (reciprocalLattice b c) ↔ Irrational (b ^ 2) := by
  constructor
  · intro hinj
    have hb : b ≠ 0 := by
      intro hb
      have h := hinj (a₁ := (1, 0)) (a₂ := (0, 0)) (by simp [reciprocalLattice, hb])
      have := congrArg Prod.fst h
      norm_num at this
    rw [irrational_iff_ne_rational]
    intro a d hd he
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have hm := (eq_div_iff hdR).mp he
    have h := hinj (a₁ := (d, 0)) (a₂ := (0, a)) (by
      simp only [reciprocalLattice, Int.cast_zero, zero_div, add_zero, zero_mul, zero_add]
      congr 1
      apply (eq_div_iff hb).mpr
      nlinarith only [hm])
    exact hd (congrArg Prod.fst h)
  · intro hirr
    have hb : b ≠ 0 := by
      intro hb
      exact hirr.ne_rat 0 (by simp [hb])
    intro x y hxy
    have he : (x.1 : ℝ) * b + (x.2 : ℝ) / b =
        (y.1 : ℝ) * b + (y.2 : ℝ) / b := add_right_cancel hxy
    have hm : ((x.1 : ℝ) - y.1) * b ^ 2 = (y.2 : ℝ) - x.2 := by
      have h := congrArg (fun r : ℝ => r * b) he
      field_simp [hb] at h
      nlinarith only [h]
    have hfst : x.1 = y.1 := by
      by_contra hne
      have hd : x.1 - y.1 ≠ 0 := sub_ne_zero.mpr hne
      apply hirr.ne_rational (y.2 - x.2) (x.1 - y.1)
      rw [Int.cast_sub, Int.cast_sub]
      apply (eq_div_iff (by exact_mod_cast hd)).mpr
      nlinarith only [hm]
    have hsnd : x.2 = y.2 := by
      rw [hfst, sub_self, zero_mul] at hm
      exact_mod_cast (sub_eq_zero.mp hm.symm).symm
    exact Prod.ext hfst hsnd

/-- The nonnegative spectral lattice inherits collision freedom. -/
theorem reciprocalLattice_nat_injective {b : ℝ} (h : Irrational (b ^ 2)) (c : ℝ) :
    Function.Injective (fun z : ℕ × ℕ => reciprocalLattice b c (z.1, z.2)) := by
  intro x y he
  have hxy := (reciprocalLattice_injective_iff b c).mpr h he
  apply Prod.ext
  · exact_mod_cast congrArg Prod.fst hxy
  · exact_mod_cast congrArg Prod.snd hxy

/-- Distinct primes give a nonresonant reciprocal spacing. -/
def reciprocalPrimeSpacing (p q : ℕ) : ℝ := Real.sqrt (Real.log q / Real.log p)

/-- Prime equality is the complete collision criterion for the integer lattice. -/
theorem reciprocalPrimeLattice_injective_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (c : ℝ) :
    Function.Injective (reciprocalLattice (reciprocalPrimeSpacing p q) c) ↔ p ≠ q := by
  have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hq0 : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  rw [reciprocalLattice_injective_iff, reciprocalPrimeSpacing,
    Real.sq_sqrt (div_pos hq0 hp0).le]
  constructor
  · intro h he
    subst q
    rw [div_self hp0.ne'] at h
    exact h.ne_rat 1 (by norm_num)
  · exact RHTower.irrational_log_ratio hp hq

#print axioms reciprocalLattice_injective_iff
#print axioms reciprocalLattice_nat_injective
#print axioms reciprocalPrimeLattice_injective_iff

end GaloisForLFunctions.BiScaleUncertainty
