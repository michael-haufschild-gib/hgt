import GaloisForLFunctions.RHTower.SelbergMaassStripGap
import GaloisForLFunctions.HTGeometry.FiniteRegularReynolds

/-!
# Exact cancellation and variance of the original Maass deck representation

The full scalar deck trace retains the actual eigen-equation, real C2
regularity, and all integral-cusp decay conditions. Its full modular
invariance descends it to principal level one. The proved small-level
exclusion therefore forces this actual trace to vanish at every level.

The resulting finite regular representation has zero Reynolds average.
Its full displacement-energy identity recovers the original source trace
density exactly, with the finite-group normalization retained.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassDeckAverage
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassCuspTransport
  SelbergMaassStripGap
open GaloisForLFunctions.HTGeometry
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Scalar sum of the original complex Maass fields over the full congruence deck group. -/
def scalarTrace (z : ℍ) : ℂ := ∑ q : Deck N, (quotientForm N f q).1.1 z

/-- The scalar deck trace is invariant under the full modular group. -/
theorem scalarTrace_invariant (A : SL2Z) (z : ℍ) :
    scalarTrace N f (A • z) = scalarTrace N f z := by
  have hv (q : Deck N) : (quotientForm N f q).1.1 (A • z) =
      (quotientForm N f (q * QuotientGroup.mk A)).1.1 z := by
    simp only [quotientForm_mul, translate_apply]
  unfold scalarTrace
  simp_rw [hv]
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N))
    (fun q : Deck N => (quotientForm N f q).1.1 z)

/-- Finite summation retains the original real C2 chart regularity. -/
theorem scalarTrace_smooth : IsRealSmoothUpperHalfPlane (scalarTrace N f) :=
  ContDiffOn.sum (fun q _ => (quotientForm N f q).2.2.1.1)

/-- The actual scalar deck trace has the original eigenvalue, including when it vanishes. -/
theorem scalarTrace_eigen (z : ℍ) :
    positiveHyperbolicLaplacian (scalarTrace N f) z = (lam : ℂ) * scalarTrace N f z := by
  have hq (q : Deck N) : ContDiffAt ℝ 2 ((quotientForm N f q).1.1 ∘ ofComplex) (z : ℂ) :=
    (quotientForm N f q).2.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  simp only [Function.comp_def] at hq
  change -(z.im : ℂ) ^ (2 : ℕ) *
    (dir 1 (dir 1 (fun w : ℂ => ∑ q : Deck N, (quotientForm N f q).1.1 (ofComplex w))) (z : ℂ) +
      dir Complex.I (dir Complex.I (fun w : ℂ => ∑ q : Deck N,
        (quotientForm N f q).1.1 (ofComplex w))) (z : ℂ)) = _
  rw [second_dir_sum Finset.univ (fun q _ => hq q),
    second_dir_sum Finset.univ (fun q _ => hq q), ← Finset.sum_add_distrib, Finset.mul_sum]
  change (∑ q : Deck N, positiveHyperbolicLaplacian (quotientForm N f q).1.1 z) =
    (lam : ℂ) * ∑ q : Deck N, (quotientForm N f q).1.1 z
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun q _ => (quotientForm N f q).2.2.1.2 z)

/-- Every original integral-cusp decay condition survives the scalar deck sum. -/
theorem scalarTrace_cuspidal : IsCuspidalAtIntegralCusps (scalarTrace N f) := by
  intro A
  change Tendsto (fun z : ℍ => ∑ q : Deck N,
    (quotientForm N f q).1.1 (integralSL2ToReal A • z)) atImInfty (𝓝 0)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ
    (fun q _ => (quotientForm N f q).2.2.2 A)

/-- The actual scalar trace descends to the original level-one invariant-function space. -/
def levelOneTrace : upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma 1)) :=
  ⟨scalarTrace N f, by
    intro γ z
    obtain ⟨A, _, he⟩ := γ.2
    simpa only [← he, integral_action] using scalarTrace_invariant N f A z⟩

/-- Values of the original congruence field as an actual finite regular representation vector. -/
def deckVector (z : ℍ) : EuclideanSpace ℂ (Deck N) :=
  WithLp.toLp 2 (fun q : Deck N => (quotientForm N f q).1.1 z)

/-- The actual deck-vector norm is exactly the source trace density. -/
theorem deckVector_norm_sq (z : ℍ) : ‖deckVector N f z‖ ^ (2 : ℕ) = density N f z := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ q : Deck N, ‖(quotientForm N f q).1.1 z‖ ^ (2 : ℕ)) =
    ∑ q : Deck N, Complex.normSq ((quotientForm N f q).1.1 z)
  simp only [Complex.normSq_eq_norm_sq]

/-- Actual modular transport is the finite regular action on the source-value vector. -/
theorem deckVector_modular (A : SL2Z) (z : ℍ) :
    deckVector N f (A • z) = finiteRegularUnitary (QuotientGroup.mk A : Deck N) (deckVector N f z) := by
  ext q
  change (quotientForm N f q).1.1 (A • z) = (quotientForm N f (q * QuotientGroup.mk A)).1.1 z
  simp only [quotientForm_mul, translate_apply]

section Exceptional
variable (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

/-- Level-one source exclusion forces exact scalar deck-trace cancellation at every level. -/
theorem scalarTrace_eq_zero : scalarTrace N f = 0 := by
  by_contra hn
  have hg : levelOneTrace N f ≠ 0 := by
    intro h
    exact hn (congrArg Subtype.val h)
  let g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma 1)) (lam : ℝ) :=
    ⟨levelOneTrace N f, hg, ⟨scalarTrace_smooth N f, scalarTrace_eigen N f⟩,
      scalarTrace_cuspidal N f⟩
  exact (small_level_no_exceptional (0 : Fin 7) lam).false g

/-- At each point the full original complex deck sum is zero. -/
theorem sum_deck_values_zero (z : ℍ) : ∑ q : Deck N, (quotientForm N f q).1.1 z = 0 :=
  congrFun (scalarTrace_eq_zero N lam f) z

/-- The genuine finite regular averaging operator annihilates the actual source vector. -/
theorem deck_average_zero (z : ℍ) : finiteRegularAverage (deckVector N f z) = 0 := by
  ext q
  rw [finiteRegularAverage_apply]
  change (Fintype.card (Deck N) : ℂ)⁻¹ *
    (∑ r : Deck N, (quotientForm N f r).1.1 z) = 0
  rw [sum_deck_values_zero, mul_zero]

/-- Full finite-group displacement recovers all actual source-vector variance. -/
theorem deck_displacement_energy (z : ℍ) :
    (2 * (Fintype.card (Deck N) : ℝ))⁻¹ *
        ∑ g : Deck N, ‖finiteRegularUnitary g (deckVector N f z) - deckVector N f z‖ ^ (2 : ℕ) =
      density N f z := by
  rw [finiteRegularAverage_energy, deck_average_zero, norm_zero, zero_pow (by norm_num), sub_zero,
    deckVector_norm_sq]

end Exceptional
end
end GaloisForLFunctions.RHTower.SelbergMaassDeckAverage
