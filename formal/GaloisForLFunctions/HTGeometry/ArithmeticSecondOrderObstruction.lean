import GaloisForLFunctions.HTGeometry.ArithmeticControlledLeibniz
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Controlled second-order arithmetic obstructions

Let a natural-number-indexed map satisfy the Leibniz product rule. If its bilinear square
is the multiplicative defect of a second map whose additive defect is bounded by total
input mass, every bilinear interaction vanishes. The converse holds with zero second map.

The mechanism uses both integer operations: repeated addition bounds the second map's
multiplicative remainder, while taking arbitrary powers forces every linearly bounded
Leibniz map to vanish. No bound on the first map, completeness, or dimension restriction
is imposed.

For exact formal deformations over a reduced real normed algebra, control of all positive
even coefficients suffices for triviality. The first potentially nonzero coefficient is
a Leibniz map; its doubled degree supplies the obstructed second-order lift.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear additive defect bounds the cost of any fixed number of repeated additions. -/
theorem arithmetic_repeated_add_defect_bound {g : ℕ → F} {C : ℝ}
    (hC : 0 ≤ C) (h0 : g 0 = 0)
    (hb : ∀ m n, ‖g (m + n) - g m - g n‖ ≤ C * ((m + n : ℕ) : ℝ)) :
    ∀ m n, ‖g (m * n) - (m : ℝ) • g n‖ ≤ C * (m : ℝ) ^ (2 : ℕ) * (n : ℝ) := by
  intro m n
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    have hsplit : g ((m + 1) * n) - ((m + 1 : ℕ) : ℝ) • g n =
        (g (m * n + n) - g (m * n) - g n) + (g (m * n) - (m : ℝ) • g n) := by
      simp only [Nat.add_mul, one_mul, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
    have ht := norm_add_le (g (m * n + n) - g (m * n) - g n)
      (g (m * n) - (m : ℝ) • g n)
    rw [hsplit]
    have hstep := hb (m * n) n
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hstep ⊢
    have hmn := mul_nonneg (mul_nonneg hC (Nat.cast_nonneg m)) (Nat.cast_nonneg n)
    exact (ht.trans (add_le_add hstep ih)).trans (by nlinarith)

/-- A controlled second-order arithmetic law annihilates its entire bilinear source. -/
theorem arithmetic_second_order_obstruction {f : ℕ → E} {g : ℕ → F}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] F) (hf : IsArithmeticLeibniz f)
    (hg : ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + B (f m) (f n))
    (hb : HasLinearArithmeticAddDefect g) : ∀ m n, B (f m) (f n) = 0 := by
  have hg0 : g 0 = 0 := by simpa [hf.map_zero] using hg 0 0
  obtain ⟨C, hC, hb⟩ := hb
  intro m
  let d : ℕ → F := fun n => B (f m) (f n)
  have hd : IsArithmeticLeibniz d := by
    intro n k
    simpa [d] using congrArg (B (f m)) (hf n k)
  have hlin : ∀ n, ‖d n‖ ≤ (C * (m : ℝ) ^ (2 : ℕ) + ‖g m‖) * (n : ℝ) := by
    intro n
    have hsplit : d n = (g (m * n) - (m : ℝ) • g n) - (n : ℝ) • g m := by
      rw [hg m n]
      dsimp [d]
      abel
    rw [hsplit]
    calc
      _ ≤ ‖g (m * n) - (m : ℝ) • g n‖ + ‖(n : ℝ) • g m‖ := norm_sub_le _ _
      _ ≤ C * (m : ℝ) ^ (2 : ℕ) * (n : ℝ) + (n : ℝ) * ‖g m‖ := by
        rw [norm_smul, Real.norm_natCast]
        exact add_le_add (arithmetic_repeated_add_defect_bound hC hg0 hb m n) le_rfl
      _ = (C * (m : ℝ) ^ (2 : ℕ) + ‖g m‖) * (n : ℝ) := by ring
  have hz := hd.eq_zero_of_linear_bound hlin
  intro n
  exact congrFun hz n

/-- Exact classification of which bilinear sources admit a controlled second-order primitive. -/
theorem arithmetic_second_order_primitive_iff {f : ℕ → E}
    (B : E →ₗ[ℝ] E →ₗ[ℝ] F) (hf : IsArithmeticLeibniz f) :
    (∃ g : ℕ → F, HasLinearArithmeticAddDefect g ∧
      ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + B (f m) (f n)) ↔
    ∀ m n, B (f m) (f n) = 0 := by
  constructor
  · rintro ⟨g, hb, hg⟩
    exact arithmetic_second_order_obstruction B hf hg hb
  · intro h
    refine ⟨0, ⟨0, le_rfl, ?_⟩, ?_⟩
    · intro m n
      simp
    · intro m n
      simp [h m n]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [IsReduced A]

/-- In a reduced algebra, the controlled quadratic lift forces its tangent to zero. -/
theorem arithmetic_second_order_tangent_eq_zero {f g : ℕ → A}
    (hf : IsArithmeticLeibniz f)
    (hg : ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + f m * f n)
    (hb : HasLinearArithmeticAddDefect g) : f = 0 := by
  funext n
  have h := arithmetic_second_order_obstruction (LinearMap.mul ℝ A) hf hg hb n n
  change f n * f n = 0 at h
  exact eq_zero_of_pow_eq_zero (n := 2) (by simpa [pow_two] using h)

/-- Even coefficient control suffices to prohibit every nonconstant exact formal deformation. -/
theorem arithmetic_formalDeformation_eq_constant (P : ℕ → PowerSeries A)
    (hmul : ∀ m n, P (m * n) = P m * P n)
    (hconstant : ∀ n, PowerSeries.constantCoeff (P n) = (n : A))
    (hbound : ∀ k, 0 < k → HasLinearArithmeticAddDefect
      (fun n => PowerSeries.coeff (2 * k) (P n))) :
    ∀ n, P n = PowerSeries.C (n : A) := by
  have hzero : ∀ k, 0 < k → ∀ n, PowerSeries.coeff k (P n) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hfirst : IsArithmeticLeibniz (fun n => PowerSeries.coeff k (P n)) := by
        intro m n
        dsimp only
        rw [hmul, PowerSeries.coeff_mul]
        have hsub : ({(0, k), (k, 0)} : Finset (ℕ × ℕ)) ⊆ Finset.antidiagonal k := by
          intro ij hij
          simp only [Finset.mem_insert, Finset.mem_singleton] at hij
          rcases hij with rfl | rfl <;> simp
        have hsum := Finset.sum_subset (f := fun ij : ℕ × ℕ =>
            PowerSeries.coeff ij.1 (P m) * PowerSeries.coeff ij.2 (P n)) hsub (by
          rintro ⟨i, j⟩ hij hnot
          have hs : i + j = k := Finset.mem_antidiagonal.mp hij
          have hi : 0 < i := by
            by_contra hn
            have hi0 : i = 0 := by omega
            have hjk : j = k := by omega
            exact hnot (by simp [hi0, hjk])
          have hj : 0 < j := by
            by_contra hn
            have hj0 : j = 0 := by omega
            have hik : i = k := by omega
            exact hnot (by simp [hj0, hik])
          rw [ih i (by omega) hi m, zero_mul])
        rw [← hsum]
        have hpair : (0, k) ≠ (k, 0) := by
          intro hh
          have := congrArg Prod.fst hh
          omega
        simp [hpair, PowerSeries.coeff_zero_eq_constantCoeff, hconstant, Algebra.smul_def]
        rw [(Nat.cast_commute n (PowerSeries.coeff k (P m))).eq]
      have hsecond : ∀ m n, PowerSeries.coeff (2 * k) (P (m * n)) =
          (m : ℝ) • PowerSeries.coeff (2 * k) (P n) +
          (n : ℝ) • PowerSeries.coeff (2 * k) (P m) +
          PowerSeries.coeff k (P m) * PowerSeries.coeff k (P n) := by
        intro m n
        rw [hmul, PowerSeries.coeff_mul]
        have hsub : ({(0, 2 * k), (k, k), (2 * k, 0)} : Finset (ℕ × ℕ)) ⊆
            Finset.antidiagonal (2 * k) := by
          intro ij hij
          simp only [Finset.mem_insert, Finset.mem_singleton] at hij
          rcases hij with rfl | rfl | rfl <;> simp [two_mul]
        have hsum := Finset.sum_subset (f := fun ij : ℕ × ℕ =>
            PowerSeries.coeff ij.1 (P m) * PowerSeries.coeff ij.2 (P n)) hsub (by
          rintro ⟨i, j⟩ hij hnot
          have hs : i + j = 2 * k := Finset.mem_antidiagonal.mp hij
          have hi : 0 < i := by
            by_contra hn
            have hi0 : i = 0 := by omega
            have hjk : j = 2 * k := by omega
            exact hnot (by simp [hi0, hjk])
          have hj : 0 < j := by
            by_contra hn
            have hj0 : j = 0 := by omega
            have hik : i = 2 * k := by omega
            exact hnot (by simp [hj0, hik])
          by_cases hik : i < k
          · rw [ih i hik hi m, zero_mul]
          · have hjk : j < k := by
              by_contra hjk
              have hiEq : i = k := by omega
              have hjEq : j = k := by omega
              exact hnot (by simp [hiEq, hjEq])
            rw [ih j hjk hj n, mul_zero])
        rw [← hsum]
        have h01 : (0, 2 * k) ≠ (k, k) := by
          intro hh
          have := congrArg Prod.fst hh
          omega
        have h02 : (0, 2 * k) ≠ (2 * k, 0) := by
          intro hh
          have := congrArg Prod.fst hh
          omega
        have h12 : (k, k) ≠ (2 * k, 0) := by
          intro hh
          have := congrArg Prod.snd hh
          omega
        simp [h01, h02, h12, PowerSeries.coeff_zero_eq_constantCoeff,
          hconstant, Algebra.smul_def]
        rw [(Nat.cast_commute n (PowerSeries.coeff (2 * k) (P m))).eq]
        abel
      have hz := arithmetic_second_order_tangent_eq_zero hfirst hsecond (hbound k hk)
      intro n
      exact congrFun hz n
  intro n
  apply PowerSeries.ext
  intro k
  by_cases hk : k = 0
  · simp [hk, PowerSeries.coeff_zero_eq_constantCoeff, hconstant]
  · rw [hzero k (Nat.pos_of_ne_zero hk) n, PowerSeries.coeff_C_of_ne_zero hk]

/-- The complete class of multiplicative formal deformations with even coefficient control. -/
theorem arithmetic_formalDeformation_iff_constant (P : ℕ → PowerSeries A) :
    ((∀ m n, P (m * n) = P m * P n) ∧
      (∀ n, PowerSeries.constantCoeff (P n) = (n : A)) ∧
      (∀ k, 0 < k → HasLinearArithmeticAddDefect
        (fun n => PowerSeries.coeff (2 * k) (P n)))) ↔
    ∀ n, P n = PowerSeries.C (n : A) := by
  constructor
  · rintro ⟨hmul, hconstant, hbound⟩
    exact arithmetic_formalDeformation_eq_constant P hmul hconstant hbound
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro m n
      simp [h]
    · intro n
      simp [h]
    · intro k _
      refine ⟨0, le_rfl, ?_⟩
      intro m n
      simp [h]

end GaloisForLFunctions.HTGeometry
