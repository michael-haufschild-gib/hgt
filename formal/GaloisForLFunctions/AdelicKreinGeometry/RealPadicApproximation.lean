import Mathlib.NumberTheory.Ostrowski

/-!
# Independent real and p-adic rational approximation

Weak approximation for the real and p-adic absolute values allows rational
slopes arbitrarily close to any positive real target inside any prescribed
p-adic neighborhood.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry.LocalApproximation

variable (p : ℕ) [Fact p.Prime]

private def places : Fin 2 → AbsoluteValue ℚ ℝ :=
  ![Rat.AbsoluteValue.real, Rat.AbsoluteValue.padic p]

private theorem places_nontrivial (i : Fin 2) : (places p i).IsNontrivial := by
  fin_cases i
  · refine ⟨2, by norm_num, ?_⟩
    norm_num [places, Rat.AbsoluteValue.real_eq_abs]
  · refine ⟨p, by exact_mod_cast (Fact.out : p.Prime).ne_zero, ?_⟩
    change Rat.AbsoluteValue.padic p (p : ℚ) ≠ 1
    rw [Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime]
    push_cast
    have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact (inv_lt_one_of_one_lt₀ hp).ne

private theorem places_inequivalent :
    Pairwise fun i j => ¬ (places p i).IsEquiv (places p j) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact Rat.AbsoluteValue.not_real_isEquiv_padic p
  · exact fun h => Rat.AbsoluteValue.not_real_isEquiv_padic p h.symm
  · exact (hij rfl).elim

/-- Rational approximation in independent real and p-adic neighborhoods. -/
theorem exists_rat_near (a b : ℚ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ q : ℚ, |(q : ℝ) - a| < δ ∧ Rat.AbsoluteValue.padic p (q - b) < ε := by
  let z : (i : Fin 2) → WithAbs (places p i) :=
    fun i => WithAbs.toAbs (places p i) ((![a, b] : Fin 2 → ℚ) i)
  obtain ⟨q, hq⟩ := Metric.denseRange_iff.mp
    (AbsoluteValue.denseRange_algebraMap_pi (places_nontrivial p) (places_inequivalent p))
    z (min δ ε) (lt_min hδ hε)
  rw [dist_comm] at hq
  have h0 := (dist_le_pi_dist (algebraMap ℚ ((i : Fin 2) → WithAbs (places p i)) q) z 0).trans_lt hq
  have h1 := (dist_le_pi_dist (algebraMap ℚ ((i : Fin 2) → WithAbs (places p i)) q) z 1).trans_lt hq
  have e0 : dist (algebraMap ℚ ((i : Fin 2) → WithAbs (places p i)) q 0) (z 0) =
      |(q : ℝ) - a| := by
    rw [dist_eq_norm]
    change Rat.AbsoluteValue.real (q - a) = _
    rw [Rat.AbsoluteValue.real_eq_abs]
    push_cast
    rfl
  have e1 : dist (algebraMap ℚ ((i : Fin 2) → WithAbs (places p i)) q 1) (z 1) =
      Rat.AbsoluteValue.padic p (q - b) := by rw [dist_eq_norm]; rfl
  exact ⟨q, (e0 ▸ h0).trans_le (min_le_left _ _), (e1 ▸ h1).trans_le (min_le_right _ _)⟩

theorem exists_rat_near_real (x : ℝ) (b : ℚ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ q : ℚ, |(q : ℝ) - x| < δ ∧ Rat.AbsoluteValue.padic p (q - b) < ε := by
  obtain ⟨a, ha0, ha1⟩ := exists_rat_btwn (show x - δ / 2 < x + δ / 2 by linarith)
  obtain ⟨q, hq, hp⟩ := exists_rat_near p a b (half_pos hδ) hε
  refine ⟨q, ?_, hp⟩
  have ha : |(a : ℝ) - x| < δ / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  calc |(q : ℝ) - x| = |((q : ℝ) - a) + ((a : ℝ) - x)| := by congr 1; ring
    _ ≤ |(q : ℝ) - a| + |(a : ℝ) - x| := by
      simpa only [Real.norm_eq_abs] using norm_add_le ((q : ℝ) - a) ((a : ℝ) - x)
    _ < δ := by linarith
end GaloisForLFunctions.AdelicKreinGeometry.LocalApproximation

