import GaloisForLFunctions.RHTower.MackeyFlatDivisorSelection
import GaloisForLFunctions.HTGeometry.ProKummerHolonomyCapacity

/-!
# Linear depth capacity selects the Euler-shell divisor

Linear depth capacity is the first polynomial scale whose pro-Kummer action is infinite on every
nonzero charge.  Applied to the strict-right local charges of the survival transfer, finiteness,
vanishing, and uniform boundedness of the truncated action are each equivalent to the Riemann
hypothesis.
-/

open Complex GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Linear depth capacity has a divergent comparison profile: it is the harmonic series. -/
theorem not_summable_linearCapacityProfile :
    ¬ Summable (fun n : ℕ => capacityProfile (fun m => (m : ℝ)) (n + 2)) := by
  have hcong : ∀ n : ℕ,
      capacityProfile (fun m => (m : ℝ)) (n + 2) = (((n + 2 : ℕ) : ℝ))⁻¹ := by
    intro n
    have hpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [capacityProfile, sq]
    field_simp
  rw [summable_congr hcong]
  rw [summable_nat_add_iff (f := fun n : ℕ => ((n : ℕ) : ℝ)⁻¹) 2]
  exact Real.not_summable_natCast_inv

/-- **Theorem 4.1 at linear capacity** (PKH.10).  Finite linear pro-Kummer action selects the zero
charge. -/
theorem summable_linear_proKummerTerm_iff_eq_zero (q : ℤ) :
    Summable (fun n : ℕ => proKummerTerm (fun m => (m : ℝ)) q (n + 2)) ↔ q = 0 :=
  summable_proKummerTerm_iff_eq_zero (fun n => Nat.cast_nonneg n)
    not_summable_linearCapacityProfile q

/-- **Corollary 6.1 — the Euler-shell specialization.**  For the strict-right local charges of the
survival transfer, finiteness, vanishing and uniform boundedness of the linear pro-Kummer action
are each equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_tfae_proKummer :
    List.TFAE
      [ RiemannHypothesis,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 → localFormationCharge ρ = 0,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          Summable (fun n : ℕ =>
            proKummerTerm (fun m => (m : ℝ)) (localFormationCharge ρ) (n + 2)),
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          ∀ n : ℕ, proKummerTerm (fun m => (m : ℝ)) (localFormationCharge ρ) (n + 2) = 0,
        ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ ≠ 1 →
          ∃ C : ℝ, ∀ N : ℕ,
            ∑ n ∈ Finset.range N,
              proKummerTerm (fun m => (m : ℝ)) (localFormationCharge ρ) (n + 2) ≤ C ] := by
  tfae_have 1 → 2 := by
    intro hrh ρ hρ hρ1
    exact (localFormationCharge_eq_zero_iff hρ1).2
      (riemannHypothesis_iff_zetaZeroFreeRight.1 hrh ρ hρ hρ1)
  tfae_have 2 → 4 := by
    intro h ρ hρ hρ1 n
    rw [proKummerTerm, h ρ hρ hρ1, chordSq_zero, mul_zero]
  tfae_have 4 → 5 := by
    intro h ρ hρ hρ1
    refine ⟨0, fun N => ?_⟩
    rw [Finset.sum_congr rfl fun n _ => h ρ hρ hρ1 n, Finset.sum_const_zero]
  tfae_have 5 → 3 := by
    intro h ρ hρ hρ1
    obtain ⟨C, hC⟩ := h ρ hρ hρ1
    refine summable_of_sum_range_le (c := C) (fun n => ?_) hC
    exact mul_nonneg (Nat.cast_nonneg _) (chordSq_nonneg _ _)
  tfae_have 3 → 1 := by
    intro h
    refine riemannHypothesis_iff_zetaZeroFreeRight.2 fun ρ hρ hρ1 => ?_
    refine (localFormationCharge_eq_zero_iff hρ1).1 ?_
    exact (summable_linear_proKummerTerm_iff_eq_zero _).1 (h ρ hρ hρ1)
  tfae_finish

/-- **The contour form at a zeta zero.**  A strict-right zero of zeta has divergent linear
pro-Kummer action, so no capacity at or above the linear scale can be finite there. -/
theorem not_summable_linear_proKummerTerm_of_zetaZero {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    ¬ Summable (fun n : ℕ =>
      proKummerTerm (fun m => (m : ℝ)) (localFormationCharge ρ) (n + 2)) := by
  intro h
  exact ((localFormationCharge_eq_zero_iff hρ1).1
    ((summable_linear_proKummerTerm_iff_eq_zero _).1 h)) hzero

end

end RHTower
