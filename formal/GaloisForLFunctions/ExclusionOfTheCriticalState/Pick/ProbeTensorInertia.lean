import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TwoSupportProbeRigidity
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.MobiusProbeKernel
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheRealProbeKernelIsAKreinForm
import GaloisForLFunctions.HTGeometry.TensorPolarizationAmplification
import GaloisForLFunctions.HeckeKreinToeplitz.IntegerFamiliesCarryTheWholeIndex

/-!
# Two positive directions in every indefinite probe matrix

Two distinct safe probe nodes give a strictly positive principal plane.
A family with only one physical node is positive semidefinite. Hence a
negative direction forces at least two positive directions, and the exact
Kronecker inertia formula multiplies the negative index by at least four.
-/

open Matrix
open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
open HTGeometry
noncomputable section

private theorem probeGram_hermQuad {n : ℕ} (p : Fin n → ℝ) (c : Fin n → ℂ) :
    hermQuad (probeGram (fun i => node (p i))) c = complexProbeQuadratic n p c := by
  unfold hermQuad complexProbeQuadratic dotProduct Matrix.mulVec
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply, Complex.star_def, probeGram]
  ring

private theorem two_probe_real (s t : ℝ) (c : Fin 2 → ℝ) :
    sourceQuadratic 2 ![s, t] c = twoProbeQuadratic s t (c 0) (c 1) := by
  simp only [sourceQuadratic, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsym : safeProbeEntry t s = safeProbeEntry s t :=
    bareMixedEnergy_probe_symm (by unfold node; linarith only [abs_nonneg t])
      (by unfold node; linarith only [abs_nonneg s])
  change c 0 * c 0 * safeProbeEntry s s + c 0 * c 1 * safeProbeEntry s t +
    (c 1 * c 0 * safeProbeEntry t s + c 1 * c 1 * safeProbeEntry t t) = _
  rw [hsym]
  unfold twoProbeQuadratic
  ring

/-- Distinct physical nodes span a positive complex plane. -/
theorem two_probe_positive_plane (s t : ℝ) (hst : node s ≠ node t) :
    IsPosDefOn (probeGram (fun i : Fin 2 => node (![s, t] i))) ⊤ := by
  intro c _ hc
  rw [probeGram_hermQuad, complexProbeQuadratic_re_im, two_probe_real, two_probe_real]
  have hr := twoProbeQuadratic_nonneg s t (c 0).re (c 1).re
  have hi := twoProbeQuadratic_nonneg s t (c 0).im (c 1).im
  apply lt_of_le_of_ne (add_nonneg hr hi)
  intro hz
  have hr0 : twoProbeQuadratic s t (c 0).re (c 1).re = 0 := by linarith only [hr, hi, hz]
  have hi0 : twoProbeQuadratic s t (c 0).im (c 1).im = 0 := by linarith only [hr, hi, hz]
  have hre := (twoProbeQuadratic_zero_iff s t (c 0).re (c 1).re).mp hr0
  have him := (twoProbeQuadratic_zero_iff s t (c 0).im (c 1).im).mp hi0
  rw [if_neg hst] at hre him
  apply hc
  funext i
  fin_cases i
  · exact Complex.ext hre.1 him.1
  · exact Complex.ext hre.2 him.2

/-- Every family containing distinct physical nodes has positive index at least two. -/
theorem probe_positive_index_two {n : ℕ} (p : Fin n → ℝ)
    (i j : Fin n) (hij : node (p i) ≠ node (p j)) :
    2 ≤ hermPosIndex (probeGram (fun k => node (p k))) := by
  have htwo := finrank_le_posIndex (two_probe_positive_plane (p i) (p j) hij)
  have hsub := HeckeKreinToeplitz.hermNegIndex_submatrix_le
    (-(probeGram (fun k => node (p k)))) (![i, j] : Fin 2 → Fin n)
  have hneg : (-(probeGram (fun k => node (p k)))).submatrix ![i, j] ![i, j] =
      -((probeGram (fun k => node (p k))).submatrix ![i, j] ![i, j]) := rfl
  rw [hneg] at hsub
  unfold hermNegIndex at hsub
  rw [neg_neg, neg_neg] at hsub
  have he : (probeGram (fun k => node (p k))).submatrix ![i, j] ![i, j] =
      probeGram (fun k : Fin 2 => node (![p i, p j] k)) := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [he] at hsub
  have hd : Module.finrank ℂ (⊤ : Submodule ℂ (Fin 2 → ℂ)) = 2 := by simp
  rw [hd] at htwo
  exact htwo.trans hsub

private theorem probeGram_isHermitian {n : ℕ} (p : Fin n → ℝ) :
    (probeGram (fun i => node (p i))).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, probeGram, Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact bareMixedEnergy_probe_symm
    (by unfold node; linarith only [abs_nonneg (p j)])
    (by unfold node; linarith only [abs_nonneg (p i)])

private theorem probe_index_zero_of_collapsed {n : ℕ} (p : Fin n → ℝ)
    (h : ∀ i j, node (p i) = node (p j)) :
    hermNegIndex (probeGram (fun i => node (p i))) = 0 := by
  have hq (c : Fin n → ℂ) : 0 ≤ hermQuad (probeGram (fun i => node (p i))) c := by
    rw [probeGram_hermQuad, complexProbeQuadratic_re_im]
    have hr (b : Fin n → ℝ) : 0 ≤ sourceQuadratic n p b := by
      by_cases hn : n = 0
      · subst n
        simp [sourceQuadratic]
      · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
        have he : sourceQuadratic n p b = safeProbeEntry (p i) (p i) * (∑ j, b j) ^ 2 := by
          unfold sourceQuadratic safeProbeEntry
          simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [h j i, h k i]
          ring
        rw [he]
        exact mul_nonneg (ProbeCuts.probeEntry_pos _ _).le (sq_nonneg _)
    exact add_nonneg (hr _) (hr _)
  obtain ⟨W, hd, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex
    (-(probeGram (fun i => node (p i))))
  have hw : W = ⊥ := by
    apply Submodule.eq_bot_iff.mpr
    intro c hc
    by_contra hz
    have hp := hW c hc hz
    rw [hermQuad_neg] at hp
    linarith only [hp, hq c]
  rw [hw] at hd
  simpa using hd.symm

/-- A negative probe direction forces a positive plane in the same finite matrix. -/
theorem negative_probe_has_two_positive {n : ℕ} (p : Fin n → ℝ) :
    0 < hermNegIndex (probeGram (fun i => node (p i))) →
      2 ≤ hermPosIndex (probeGram (fun i => node (p i))) := by
  intro hn
  by_cases h : ∃ i j, node (p i) ≠ node (p j)
  · obtain ⟨i, j, hij⟩ := h
    exact probe_positive_index_two p i j hij
  · have he : ∀ i j, node (p i) = node (p j) := by
      intro i j
      by_contra hij
      exact h ⟨i, j, hij⟩
    rw [probe_index_zero_of_collapsed p he] at hn
    omega

/-- Tensor squaring multiplies every actual safe-probe negative index by at least four. -/
theorem probe_tensor_negative_index_four {n : ℕ} (p : Fin n → ℝ) :
    4 * hermNegIndex (probeGram (fun i => node (p i))) ≤
      hermNegIndex (Matrix.kronecker (probeGram (fun i => node (p i)))
        (probeGram (fun i => node (p i)))) := by
  rw [negIndex_kronecker (probeGram_isHermitian p) (probeGram_isHermitian p)]
  by_cases hn : hermNegIndex (probeGram (fun i => node (p i))) = 0
  · simp only [hn, mul_zero, zero_mul, add_zero, le_refl]
  · have hp := negative_probe_has_two_positive p (Nat.pos_of_ne_zero hn)
    nlinarith only [Nat.mul_le_mul_right (hermNegIndex (probeGram (fun i => node (p i)))) hp]

#print axioms two_probe_positive_plane
#print axioms negative_probe_has_two_positive
#print axioms probe_tensor_negative_index_four
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
