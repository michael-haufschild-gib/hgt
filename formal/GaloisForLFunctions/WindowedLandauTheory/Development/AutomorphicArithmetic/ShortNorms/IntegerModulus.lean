import Mathlib

/-! A nontrivial positive integer generates a proper ideal in a ring of integers. -/

open NumberField

theorem Ideal.span_natCast_not_top_le (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : 1 < m) :
    ¬ (⊤ : Ideal (𝓞 K)) ≤ Ideal.span {(m : 𝓞 K)} := by
  intro h
  have hu : IsUnit (m : 𝓞 K) := Ideal.span_singleton_eq_top.mp (top_le_iff.mp h)
  have hn := hu.map (Algebra.norm ℤ (S := 𝓞 K))
  rw [show ((m : 𝓞 K)) = algebraMap ℤ (𝓞 K) (m : ℤ) by simp, Algebra.norm_algebraMap] at hn
  have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hd, Int.isUnit_iff] at hn
  omega
