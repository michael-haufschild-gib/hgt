import GaloisForLFunctions.CompletedArithmeticForms.SuccessorMixture
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSeventhRankStrict

/-!
# Complete weighted tails and the compact center-successor boundary

Every critical aperture has the same logarithmic rank boundary for strict
weighted native tails. The center successor retains the full quadratic energy
of its global minimizer on both pieces of the source. At the strict rank-seven
center head this gives an unconditional positive tail allowance for the next
successor, expressed through the actual integrated tail inverse.
-/

noncomputable section

open MeasureTheory Matrix Finset Set

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower

/-- Actual weighted native moments on a measurable part of the center domain. -/
def nativeWeightedMoment (a : ℝ) (U : Set ℝ) (k : ℕ) : ℝ :=
  ∫ r in U, r * Real.sinh (a * r) * thetaCuspNativeSignedJet (r / 2) k

/-- The compact part of the literal center moment. -/
def nativeWeightedCenterBandMoment (a R : ℝ) : ℕ → ℝ :=
  nativeWeightedMoment a (Ioc 0 R)

/-- The complete far part of the literal center moment. -/
def nativeWeightedCenterTailMoment (a R : ℝ) : ℕ → ℝ :=
  nativeWeightedMoment a (Ioi R)

/-- Finite mixed tests commute exactly with weighted source integration. -/
theorem nativeWeightedMoment_quadratic_eq_integral
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) {U : Set ℝ} (hU : U ⊆ Ioi 0)
    {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ finiteHankelMatrix (nativeWeightedMoment a U) N *ᵥ v =
      ∫ r in U, r * Real.sinh (a * r) * thetaCuspNativeSignedHankelForm (r / 2) v := by
  have hi (i j : Fin N) :=
    ((integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha (i.val + j.val)).mono_set hU).const_mul
      (v i * v j)
  have hpoint (r : ℝ) : r * Real.sinh (a * r) * thetaCuspNativeSignedHankelForm (r / 2) v =
      ∑ i : Fin N, ∑ j : Fin N,
        (v i * v j) * (r * Real.sinh (a * r) * thetaCuspNativeSignedJet (r / 2) (i.val + j.val)) := by
    simp only [thetaCuspNativeSignedHankelForm, Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum univ (fun i _ => integrable_finsetSum univ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum univ (fun j _ => hi _ j), integral_const_mul]
  simp only [dotProduct, Matrix.mulVec, finiteHankelMatrix, nativeWeightedMoment, Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

/-- The literal center moments split into the compact interval and its complete tail. -/
theorem centerSignedMoment_eq_band_add_tail {a R : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hR : 0 ≤ R) (k : ℕ) :
    thetaCuspCenterMixedSignedJet a k =
      nativeWeightedCenterBandMoment a R k + nativeWeightedCenterTailMoment a R k := by
  rw [thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0 ha]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := by
    ext r
    constructor
    · intro hr
      rcases le_or_gt r R with h | h
      · exact Or.inl ⟨hr, h⟩
      · exact Or.inr h
    · rintro (⟨hr, _⟩ | hr)
      · exact hr
      · exact lt_of_le_of_lt hR hr
  have hdisj : Disjoint (Ioc (0 : ℝ) R) (Ioi R) := by
    rw [Set.disjoint_left]
    rintro r ⟨_, hr⟩ ht
    exact (not_lt.mpr hr) ht
  have hi := integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha k
  rw [hsplit]
  exact setIntegral_union hdisj measurableSet_Ioi (hi.mono_set (fun _ h => h.1))
    (hi.mono_set (fun _ h => lt_of_le_of_lt hR h))

/-- Weighted native tails are strict on an aperture-independent logarithmic rank domain. -/
theorem nativeWeightedCenterTail_posDef (N : ℕ) {a R : ℝ}
    (ha0 : 0 < a) (ha : a < 1 / 2)
    (hR : 2 * nativeQuadraticRankHorizon (N + 1) ≤ R) :
    (finiteHankelMatrix (nativeWeightedCenterTailMoment a R) N).PosDef := by
  have hH : 0 ≤ nativeQuadraticRankHorizon (N + 1) := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith only [hR, hH]
  have hU : Ioi R ⊆ Ioi (0 : ℝ) := fun _ h => lt_of_le_of_lt hR0 h
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, finiteHankelMatrix, Nat.add_comm]
  · intro v hv
    have hpos (r : ℝ) (hr : r ∈ Ioi R) :
        0 < r * Real.sinh (a * r) * thetaCuspNativeSignedHankelForm (r / 2) v := by
      have hr0 : 0 < r := hU hr
      have hnative : 0 < thetaCuspNativeSignedHankelForm (r / 2) v :=
        nativeSignedHankelForm_pos_of_quadratic_rank_horizon hv
          (by have hr' : R < r := hr; linarith only [hR, hr'])
      exact mul_pos (mul_pos hr0 (Real.sinh_pos_iff.mpr (mul_pos ha0 hr0))) hnative
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi R)] (fun r =>
        r * Real.sinh (a * r) * thetaCuspNativeSignedHankelForm (r / 2) v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (hpos r hr).le
    have hi := (integrableOn_thetaCuspWeightedNativeSignedHankelForm ha0.le ha v).mono_set hU
    rw [star_trivial]
    change 0 < v ⬝ᵥ finiteHankelMatrix (nativeWeightedMoment a (Ioi R)) N *ᵥ v
    rw [nativeWeightedMoment_quadratic_eq_integral ha0.le ha hU,
      setIntegral_pos_iff_support_of_nonneg_ae hnn hi]
    have hs : Ioi R ⊆ Function.support (fun r =>
        r * Real.sinh (a * r) * thetaCuspNativeSignedHankelForm (r / 2) v) :=
      fun r hr => (hpos r hr).ne'
    rw [Set.inter_eq_right.mpr hs]
    exact isOpen_Ioi.measure_pos volume ⟨R + 1, by change R < R + 1; linarith⟩

/-- Exact weighted-tail successors are positive on their own logarithmic rank domain. -/
theorem nativeWeightedCenterTail_successor_pos (N : ℕ) {a R : ℝ}
    (ha0 : 0 < a) (ha : a < 1 / 2)
    (hR : 2 * nativeQuadraticRankHorizon (N + 2) ≤ R) :
    0 < finiteHankelSuccessorSchur (nativeWeightedCenterTailMoment a R) N := by
  have hfull := nativeWeightedCenterTail_posDef (N + 1) ha0 ha hR
  have he : Function.Injective (Fin.castSucc : Fin N → Fin (N + 1)) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin (N + 1) => z.val) hij)
  exact (finiteHankelMatrix_succ_posDef_iff_schur_pos (hfull.submatrix he)).mp hfull

/-- The complete center successor is the sum of two energies at its exact global minimizer. -/
theorem centerSuccessor_eq_globalMinimizer_band_add_tail {N : ℕ} {a R : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (hR : 0 ≤ R)
    (hm : (finiteHankelMatrix (thetaCuspCenterMixedSignedJet a) N).PosDef) :
    finiteHankelSuccessorSchur (thetaCuspCenterMixedSignedJet a) N =
      successorTestVector (thetaCuspCenterMixedSignedJet a) N ⬝ᵥ
        finiteHankelMatrix (nativeWeightedCenterBandMoment a R) (N + 1) *ᵥ
          successorTestVector (thetaCuspCenterMixedSignedJet a) N +
      successorTestVector (thetaCuspCenterMixedSignedJet a) N ⬝ᵥ
        finiteHankelMatrix (nativeWeightedCenterTailMoment a R) (N + 1) *ᵥ
          successorTestVector (thetaCuspCenterMixedSignedJet a) N := by
  rw [← successorTestVector_energy_eq hm]
  have he : finiteHankelMatrix (thetaCuspCenterMixedSignedJet a) (N + 1) =
      finiteHankelMatrix (nativeWeightedCenterBandMoment a R) (N + 1) +
        finiteHankelMatrix (nativeWeightedCenterTailMoment a R) (N + 1) := by
    ext i j
    exact centerSignedMoment_eq_band_add_tail ha0 ha hR (i.val + j.val)
  rw [he, add_mulVec, dotProduct_add]

/-- The first unpaid center successor retains a strictly positive exact tail allowance. -/
theorem centerSeventhSuccessor_compact_allowance {a R : ℝ}
    (ha0 : 0 < a) (ha : a < 1 / 2)
    (hR : 2 * nativeQuadraticRankHorizon 9 ≤ R) :
    0 < finiteHankelSuccessorSchur (nativeWeightedCenterTailMoment a R) 7 ∧
      successorTestVector (thetaCuspCenterMixedSignedJet a) 7 ⬝ᵥ
        finiteHankelMatrix (nativeWeightedCenterBandMoment a R) 8 *ᵥ
          successorTestVector (thetaCuspCenterMixedSignedJet a) 7 +
        finiteHankelSuccessorSchur (nativeWeightedCenterTailMoment a R) 7 ≤
          finiteHankelSuccessorSchur (thetaCuspCenterMixedSignedJet a) 7 := by
  have hH : 0 ≤ nativeQuadraticRankHorizon 9 := le_max_left _ _
  have hR0 : 0 ≤ R := by linarith only [hR, hH]
  have hm : (finiteHankelMatrix (thetaCuspCenterMixedSignedJet a) 7).PosDef :=
    thetaCuspCenterMixedSignedHankel_seven_posDef ha0 ha
  have ht := nativeWeightedCenterTail_posDef 8 ha0 ha hR
  have he : Function.Injective (Fin.castSucc : Fin 7 → Fin 8) := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin 8 => z.val) hij)
  have hb := successorSchur_le_monic_energy (ht.submatrix he)
    (successorMinimizer (thetaCuspCenterMixedSignedJet a) 7)
  refine ⟨nativeWeightedCenterTail_successor_pos 7 ha0 ha hR, ?_⟩
  rw [centerSuccessor_eq_globalMinimizer_band_add_tail ha0.le ha hR0 hm]
  exact add_le_add_left hb _

#print axioms nativeWeightedMoment_quadratic_eq_integral
#print axioms nativeWeightedCenterTail_posDef
#print axioms nativeWeightedCenterTail_successor_pos
#print axioms centerSuccessor_eq_globalMinimizer_band_add_tail
#print axioms centerSeventhSuccessor_compact_allowance

end GaloisForLFunctions.CompletedArithmeticForms
