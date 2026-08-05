import GaloisForLFunctions.HTGeometry.HerglotzDiscreteSupportSeries

/-!
# The discrete Herglotz summability hypothesis is realized, and is a genuine restriction

`(H7)` asks that the atomic weights be summable against the reciprocal Nevanlinna denominator.
Every absolutely summable weight family has it against *every* atom family, because the denominator
is at least one; so the hypothesis costs nothing on summable skeletons and is inherited by every
dominated family.

It is not vacuous in the other direction either: the constant unit weight on the integer atoms
fails it, since the harmonic series diverges.  So `(H7)` separates two nonempty classes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The zero weight family satisfies `(H7)` against every atom family. -/
theorem discreteHerglotzH7_zero (atoms : ℕ → ℝ) :
    DiscreteHerglotzH7 (fun _ => 0) atoms := by
  simp [DiscreteHerglotzH7]

/-- **Absolute summability of the weights implies `(H7)`,** for every atom family: the Nevanlinna
denominator is at least one. -/
theorem discreteHerglotzH7_of_summable_abs {ε : ℕ → ℝ} (atoms : ℕ → ℝ)
    (h : Summable fun n => |ε n|) : DiscreteHerglotzH7 ε atoms := by
  refine Summable.of_norm_bounded h fun n => ?_
  have hden : (1 : ℝ) ≤ 1 + |atoms n| := by
    have := abs_nonneg (atoms n)
    linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + |atoms n|)]
  exact div_le_self (abs_nonneg _) hden

/-- A weight family supported on a finite set satisfies `(H7)`. -/
theorem discreteHerglotzH7_of_support_subset {ε : ℕ → ℝ} (atoms : ℕ → ℝ) {s : Finset ℕ}
    (h : ∀ n ∉ s, ε n = 0) : DiscreteHerglotzH7 ε atoms :=
  summable_of_ne_finset_zero (s := s) fun n hn => by rw [h n hn, zero_div]

/-- `(H7)` is inherited by every family dominated in modulus. -/
theorem discreteHerglotzH7_of_abs_le {ε δ atoms : ℕ → ℝ} (h : DiscreteHerglotzH7 ε atoms)
    (hle : ∀ n, |δ n| ≤ ε n) : DiscreteHerglotzH7 δ atoms := by
  refine Summable.of_norm_bounded h fun n => ?_
  have hden : (0 : ℝ) < 1 + |atoms n| := by
    have := abs_nonneg (atoms n)
    linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
  gcongr
  exact hle n

/-- **`(H7)` is a genuine restriction.**  The constant unit weight on the integer atoms fails it. -/
theorem not_discreteHerglotzH7_one_natAtoms :
    ¬ DiscreteHerglotzH7 (fun _ => 1) (fun n : ℕ => (n : ℝ)) := by
  intro h
  have hcongr : (fun n : ℕ => (1 : ℝ) / (1 + |(n : ℝ)|)) = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n
    rw [abs_of_nonneg (Nat.cast_nonneg n), add_comm]
  rw [DiscreteHerglotzH7, hcongr] at h
  have hshift : Summable fun n : ℕ => 1 / ((n : ℝ)) := by
    refine (summable_nat_add_iff 1).mp ?_
    refine h.congr fun n => ?_
    push_cast
    ring
  exact Real.not_summable_one_div_natCast hshift

end

end GaloisForLFunctions.HTGeometry
