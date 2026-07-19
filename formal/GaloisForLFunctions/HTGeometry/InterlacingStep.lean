import GaloisForLFunctions.HTGeometry.SturmAlternation

/-!
# The interlacing step

Between two roots of `Q_{n+1}` at which `Qₙ` takes opposite signs, `Q_{n+2}` has a root.  The Sturm
collapse turns the sign condition on `Qₙ` into the same condition on `Q_{n+2}`, up to the positive
factor `bₙ`, and the intermediate value theorem does the rest.

This is the inductive step of the interlacing theorem, isolated so that the induction itself becomes
bookkeeping over the sorted root lists.
-/

open scoped BigOperators
open Polynomial Set

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The interlacing step.** -/
theorem exists_root_between (h : PositiveMomentForm s) (n : ℕ) {a b : ℝ} (hab : a < b)
    (ha : (monicOrtho s (n + 1)).eval a = 0) (hb : (monicOrtho s (n + 1)).eval b = 0)
    (hsign : (monicOrtho s n).eval a * (monicOrtho s n).eval b < 0) :
    ∃ z, a < z ∧ z < b ∧ (monicOrtho s (n + 2)).eval z = 0 := by
  have hcont : ContinuousOn (fun x => (monicOrtho s (n + 2)).eval x) (Set.Icc a b) :=
    (monicOrtho s (n + 2)).continuous_aeval.continuousOn
  have hfa : (monicOrtho s (n + 2)).eval a = -recurOff s n * (monicOrtho s n).eval a :=
    monicOrtho_eval_succ_succ_of_root h n ha
  have hfb : (monicOrtho s (n + 2)).eval b = -recurOff s n * (monicOrtho s n).eval b :=
    monicOrtho_eval_succ_succ_of_root h n hb
  have hbpos := recurOff_pos h n
  have hprod : (monicOrtho s (n + 2)).eval a * (monicOrtho s (n + 2)).eval b < 0 := by
    rw [hfa, hfb]
    have hb2 : 0 < recurOff s n * recurOff s n := mul_pos hbpos hbpos
    nlinarith [mul_pos hb2 (neg_pos.mpr hsign)]
  rcases mul_neg_iff.mp hprod with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
  · have hmem : (0 : ℝ) ∈ Set.Ioo ((monicOrtho s (n + 2)).eval b)
        ((monicOrtho s (n + 2)).eval a) := ⟨hnb, hpa⟩
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Ioo' hab.le hcont hmem
    exact ⟨z, hz.1, hz.2, hfz⟩
  · have hmem : (0 : ℝ) ∈ Set.Ioo ((monicOrtho s (n + 2)).eval a)
        ((monicOrtho s (n + 2)).eval b) := ⟨hna, hpb⟩
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Ioo hab.le hcont hmem
    exact ⟨z, hz.1, hz.2, hfz⟩

end HTGeometry
