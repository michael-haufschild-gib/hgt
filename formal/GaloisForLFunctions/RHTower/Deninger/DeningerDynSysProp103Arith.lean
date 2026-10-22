import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The arithmetic and limit steps of Proposition 10.3

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 10.3.

Two elementary ingredients of the approximation argument.  The numbers `ν = ν₀ + A ∏ p^{M₀}` used
there have no prime factor among the finitely many primes outside `char N₀`, because each such
prime divides the product but not `ν₀`; and they are congruent to `ν₀` modulo that product, so
they inherit its congruence conditions.  Finally, for any `v > 0` one can choose the two sequences
`(A_n)` and `(A'_n)` of positive integers tending to infinity with `A'_n A_n⁻¹ → v`.

The structural half of the proposition — that these approximations suffice — is
`HTGeometry.irreducibleSpace_of_nhds_one`.
-/

namespace RHTower

open Filter Topology

/-- **Deninger, Proposition 10.3, the arithmetic step.**  If a prime divides `Q` but not `ν₀`,
it does not divide `ν₀ + A · Q`.  This is why the numbers `ν = ν₀ + A ∏_{p ∈ S' ∪ S} p^{M₀}` have
no prime factor in `S`, hence lie in `N₀`. -/
theorem deningerNotDvd_add_mul {p ν₀ Q A : ℕ} (hpQ : p ∣ Q) (hpν₀ : ¬ p ∣ ν₀) :
    ¬ p ∣ (ν₀ + A * Q) := by
  intro hdvd
  exact hpν₀ ((Nat.dvd_add_right (Dvd.dvd.mul_left hpQ A)).mp (by rwa [Nat.add_comm] at hdvd))

/-- The numbers `ν₀ + A · Q` are congruent to `ν₀` modulo `Q`, so they satisfy the same
congruence conditions at the primes dividing `Q`. -/
theorem deningerModEq_add_mul (ν₀ Q A : ℕ) : (ν₀ + A * Q) ≡ ν₀ [MOD Q] := by
  show (ν₀ + A * Q) % Q = ν₀ % Q
  rw [Nat.add_mul_mod_self_right]

/-- **Deninger, Proposition 10.3, the limit step.**  For every positive real there are two
sequences of positive integers tending to infinity whose ratio tends to it; this produces the
sequences `(A_n)`, `(A'_n)` with `A'_n A_n⁻¹ → v`. -/
theorem deningerExists_seq_ratio_tendsto (v : ℝ) (hv : 0 < v) :
    ∃ A A' : ℕ → ℕ, (∀ n, 0 < A n) ∧ (∀ n, 0 < A' n) ∧
      Tendsto A atTop atTop ∧ Tendsto A' atTop atTop ∧
      Tendsto (fun n => (A' n : ℝ) / (A n : ℝ)) atTop (𝓝 v) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hlin : Tendsto (fun n : ℕ => v * ((n : ℝ) + 1)) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop hv ?_
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  refine ⟨fun n => n + 1, fun n => ⌈v * ((n : ℝ) + 1)⌉₊, fun n => Nat.succ_pos n, fun n => ?_,
    ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.2 (by positivity)
  · exact tendsto_add_atTop_nat 1
  · refine tendsto_natCast_atTop_iff (R := ℝ) |>.mp ?_
    exact tendsto_atTop_mono (fun n => Nat.le_ceil _) hlin
  · have hlow : ∀ n : ℕ, v ≤ (⌈v * ((n : ℝ) + 1)⌉₊ : ℝ) / (((n + 1 : ℕ) : ℝ)) := by
      intro n
      rw [le_div_iff₀ (by push_cast; exact hpos n)]
      have := Nat.le_ceil (v * ((n : ℝ) + 1))
      push_cast
      linarith
    have hhigh : ∀ n : ℕ,
        (⌈v * ((n : ℝ) + 1)⌉₊ : ℝ) / (((n + 1 : ℕ) : ℝ)) ≤ v + 1 / ((n : ℝ) + 1) := by
      intro n
      rw [div_le_iff₀ (by push_cast; exact hpos n)]
      have hc := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < v * ((n : ℝ) + 1)))
      have hne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (hpos n)
      push_cast
      field_simp
      nlinarith [hc, hpos n]
    have hupper : Tendsto (fun n : ℕ => v + 1 / ((n : ℝ) + 1)) atTop (𝓝 v) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := v) (f := atTop (α := ℕ))).add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hlow hhigh

end RHTower
