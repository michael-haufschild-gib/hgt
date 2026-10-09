import GaloisForLFunctions.HTGeometry.QKrawtchoukCoefficientLimits
import GaloisForLFunctions.HTGeometry.QuasiMomentLimit
import GaloisForLFunctions.HTGeometry.QuasiMeasureLowerBound

/-!
# Probability measures for the actual finite q-Krawtchouk recurrences

Both balanced finite recurrences have strictly positive lower coefficients
inside their `2K+1` dimensional block. Extend the lower sequence positively
beyond that block and take the Gaussian quadrature at level `2K`. Its nodes
are zeros of the original finite recurrence polynomial, independently of
the artificial continuation. Each fixed moment eventually agrees with the
original finite Favard moment and converges to the corresponding edge moment.

This realizes the finite-moment step in arXiv:2609.24149, Sections 3, 6, and 8,
as actual probability measures. Identification with the paper's explicit
q-product spectral weights is a separate statement.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace HTGeometry

private theorem cutoff_pos (t : ℝ) (K : ℕ) (i : Fin (2 * K)) :
    0 < qKrawtchoukEdgeCutoff t K ((i : ℕ) + 1) := by
  rw [qKrawtchoukEdgeCutoff_eq]
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hi : (i : ℝ) < 2 * (K : ℝ) := by exact_mod_cast i.isLt
  have ht := mul_pos (Real.exp_pos t) (sub_pos.mpr hi)
  push_cast
  nlinarith

/-- Every off-diagonal inside either finite block is strictly positive. -/
theorem qKrawtchoukFiniteLower_pos (t u : ℝ) (K : ℕ) (i : Fin (2 * K)) :
    0 < qKrawtchoukHermiteFiniteLower t K ((i : ℕ) + 1) ∧
    0 < qKrawtchoukCompanionFiniteLower t u K ((i : ℕ) + 1) :=
  ⟨mul_pos (inverseQHermiteLower_succ_pos t i) (cutoff_pos t K i),
    mul_pos (alSalamCarlitzLower_succ_pos t u i) (cutoff_pos t K i)⟩

private def extendedLower (β : ℕ → ℝ) (K n : ℕ) : ℝ :=
  if n ≤ 2 * K then β n else 1

private theorem extendedLower_pos (β : ℕ → ℝ) (K : ℕ)
    (hβ : ∀ i : Fin (2 * K), 0 < β ((i : ℕ) + 1)) (n : ℕ) :
    0 < extendedLower β K (n + 1) := by
  unfold extendedLower
  split_ifs with hn
  · exact hβ ⟨n, by omega⟩
  · exact zero_lt_one

private theorem polynomial_lower_congr (α β γ : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, β j = γ j) : favardPoly α β n = favardPoly α γ n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n hn hn1 =>
      rw [favardPoly_succ_succ, favardPoly_succ_succ,
        hn (fun j hj => h j (by omega)), hn1 (fun j hj => h j (by omega)),
        h (n + 1) (by omega)]

private theorem moment_lower_congr (α β γ : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, β j = γ j) : favardMoment α β n = favardMoment α γ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [favardMoment_eq, favardMoment_eq]
      split_ifs with hn
      · rfl
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [polynomial_lower_congr α β γ n h,
          ih i i.isLt (fun j hj => h j (by omega))]

private def finiteLaw (α β : ℕ → ℝ) (K : ℕ)
    (hβ : ∀ i : Fin (2 * K), 0 < β ((i : ℕ) + 1)) : ProbabilityMeasure ℝ :=
  quasiProbMeasure (favard_positiveMomentForm α (extendedLower β K)
    (extendedLower_pos β K hβ)) (2 * K) 0

private theorem finiteLaw_integrable (α β : ℕ → ℝ) (K : ℕ)
    (hβ : ∀ i : Fin (2 * K), 0 < β ((i : ℕ) + 1)) (f : ℝ → ℝ) :
    Integrable f (finiteLaw α β K hβ : Measure ℝ) :=
  integrable_quasiProb (favard_positiveMomentForm α (extendedLower β K)
    (extendedLower_pos β K hβ)) (2 * K) 0 f

private theorem finiteLaw_moment (α β : ℕ → ℝ) (K : ℕ)
    (hβ : ∀ i : Fin (2 * K), 0 < β ((i : ℕ) + 1)) (n : ℕ) (hn : n ≤ 2 * K) :
    (∫ y, y ^ n ∂(finiteLaw α β K hβ : Measure ℝ)) = favardMoment α β n := by
  change (∫ y, y ^ n ∂quasiProb (favardMoment α (extendedLower β K)) (2 * K) 0) = _
  rw [integral_pow_quasiProb (favard_positiveMomentForm α (extendedLower β K)
    (extendedLower_pos β K hβ)) (2 * K) 0 n (by omega),
    favardMoment_zero, inv_one, one_mul]
  apply moment_lower_congr
  intro j hj
  simp only [extendedLower, if_pos (show j ≤ 2 * K by omega)]

private theorem finiteLaw_characteristic (α β : ℕ → ℝ) (K : ℕ)
    (hβ : ∀ i : Fin (2 * K), 0 < β ((i : ℕ) + 1)) :
    (∫ y, ((favardPoly α β (2 * K + 1)).eval y) ^ 2
      ∂(finiteLaw α β K hβ : Measure ℝ)) = 0 := by
  let h := favard_positiveMomentForm α (extendedLower β K) (extendedLower_pos β K hβ)
  have hp : monicOrtho (favardMoment α (extendedLower β K)) (2 * K + 1) =
      favardPoly α β (2 * K + 1) := by
    rw [monicOrtho_favardMoment α (extendedLower β K) (extendedLower_pos β K hβ)]
    apply polynomial_lower_congr
    intro j hj
    simp only [extendedLower, if_pos (show j ≤ 2 * K by omega)]
  change (∫ y, ((favardPoly α β (2 * K + 1)).eval y) ^ 2
    ∂quasiProb (favardMoment α (extendedLower β K)) (2 * K) 0) = 0
  rw [quasiProb_eq_quasiMeasure (favardMoment_zero α (extendedLower β K)),
    integral_quasiMeasure h]
  apply Finset.sum_eq_zero
  intro y hy
  have hr := (mem_quasiNodes_iff (2 * K) 0 y).mp hy
  rw [quasiOrtho_eval, zero_mul, add_zero, hp] at hr
  simp only [hr, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

/-- The Gaussian spectral law of the actual finite inverse-q Hermite recurrence. -/
def qKrawtchoukHermiteFiniteMeasure (t u : ℝ) (K : ℕ) : ProbabilityMeasure ℝ :=
  finiteLaw (qKrawtchoukHermiteFiniteDiagonal t u K) (qKrawtchoukHermiteFiniteLower t K)
    K (fun i => (qKrawtchoukFiniteLower_pos t u K i).1)

/-- The Gaussian spectral law of the actual finite Al-Salam--Carlitz recurrence. -/
def qKrawtchoukCompanionFiniteMeasure (t u : ℝ) (K : ℕ) : ProbabilityMeasure ℝ :=
  finiteLaw (qKrawtchoukCompanionFiniteDiagonal t u K) (qKrawtchoukCompanionFiniteLower t u K)
    K (fun i => (qKrawtchoukFiniteLower_pos t u K i).2)

/-- All real observables are integrable against the concrete finite Hermite law. -/
theorem qKrawtchoukHermiteFiniteMeasure_integrable (t u : ℝ) (K : ℕ) (f : ℝ → ℝ) :
    Integrable f (qKrawtchoukHermiteFiniteMeasure t u K : Measure ℝ) :=
  finiteLaw_integrable _ _ _ _ f

/-- All real observables are integrable against the concrete finite companion law. -/
theorem qKrawtchoukCompanionFiniteMeasure_integrable (t u : ℝ) (K : ℕ) (f : ℝ → ℝ) :
    Integrable f (qKrawtchoukCompanionFiniteMeasure t u K : Measure ℝ) :=
  finiteLaw_integrable _ _ _ _ f

/-- The finite Hermite characteristic polynomial vanishes in squared integral. -/
theorem qKrawtchoukHermiteFiniteMeasure_characteristic (t u : ℝ) (K : ℕ) :
    (∫ y, ((favardPoly (qKrawtchoukHermiteFiniteDiagonal t u K)
      (qKrawtchoukHermiteFiniteLower t K) (2 * K + 1)).eval y) ^ 2
      ∂(qKrawtchoukHermiteFiniteMeasure t u K : Measure ℝ)) = 0 :=
  finiteLaw_characteristic _ _ _ _

/-- The finite companion characteristic polynomial vanishes in squared integral. -/
theorem qKrawtchoukCompanionFiniteMeasure_characteristic (t u : ℝ) (K : ℕ) :
    (∫ y, ((favardPoly (qKrawtchoukCompanionFiniteDiagonal t u K)
      (qKrawtchoukCompanionFiniteLower t u K) (2 * K + 1)).eval y) ^ 2
      ∂(qKrawtchoukCompanionFiniteMeasure t u K : Measure ℝ)) = 0 :=
  finiteLaw_characteristic _ _ _ _

/-- Every fixed moment of the actual finite Hermite laws has the predicted edge limit. -/
theorem qKrawtchoukHermiteFiniteMeasure_moment_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => ∫ y, y ^ n ∂(qKrawtchoukHermiteFiniteMeasure t u K : Measure ℝ))
      atTop (𝓝 (inverseQHermiteMoment t u n)) := by
  apply (qKrawtchoukHermiteFiniteMoment_tendsto t u n).congr'
  filter_upwards [eventually_ge_atTop n] with K hK
  exact (finiteLaw_moment _ _ _ _ n (by omega)).symm

/-- Every fixed moment of the actual finite companion laws has the predicted edge limit. -/
theorem qKrawtchoukCompanionFiniteMeasure_moment_tendsto (t u : ℝ) (n : ℕ) :
    Tendsto (fun K => ∫ y, y ^ n ∂(qKrawtchoukCompanionFiniteMeasure t u K : Measure ℝ))
      atTop (𝓝 (alSalamCarlitzMoment t u n)) := by
  apply (qKrawtchoukCompanionFiniteMoment_tendsto t u n).congr'
  filter_upwards [eventually_ge_atTop n] with K hK
  exact (finiteLaw_moment _ _ _ _ n (by omega)).symm

end HTGeometry
