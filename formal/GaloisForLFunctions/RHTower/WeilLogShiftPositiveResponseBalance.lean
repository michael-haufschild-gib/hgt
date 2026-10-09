import GaloisForLFunctions.RHTower.WeilLogShiftAlignedImpulseCone
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex

/-!
# A positive balance law for factorial-regular finite responses

The native aligned cone excludes the standard simplex from the regular
response submodule after a diagonal parity change. Strict separation then
produces a positive coordinate functional annihilating that submodule.
-/

noncomputable section

namespace RHTower

private theorem exists_positive_annihilator_of_disjoint_simplex {d : ℕ}
    (L : Submodule ℝ (Fin d → ℝ))
    (hdisj : Disjoint (L : Set (Fin d → ℝ)) (stdSimplex ℝ (Fin d))) :
    ∃ w : Fin d → ℝ, (∀ i, 0 < w i) ∧
      ∀ b : Fin d → ℝ, b ∈ L → ∑ i, w i * b i = 0 := by
  obtain ⟨f, u, v, hL, huv, hΔ⟩ := geometric_hahn_banach_closed_compact
    L.convex L.closed_of_finiteDimensional (convex_stdSimplex ℝ (Fin d))
    (isCompact_stdSimplex ℝ (Fin d)) hdisj
  have hu : 0 < u := by simpa only [map_zero] using hL 0 L.zero_mem
  have hzero (b : Fin d → ℝ) (hb : b ∈ L) : f b = 0 := by
    by_contra hfb
    have h := hL ((u / f b) • b) (L.smul_mem _ hb)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ u hfb] at h
    exact (lt_irrefl u) h
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · intro i
    exact (hu.trans huv).trans (hΔ _ (single_mem_stdSimplex ℝ i))
  · intro b hb
    have hbasis (i : Fin d) : (fun j : Fin d => if i = j then (1 : ℝ) else 0) =
        (Pi.single i 1 : Fin d → ℝ) := by
      funext j
      simp only [Pi.single_apply, eq_comm]
    have hexp : f b = ∑ i, b i * f (Pi.single i 1) := by
      have h := f.toLinearMap.pi_apply_eq_sum_univ b
      change f b = ∑ i, b i • f (fun j : Fin d => if i = j then (1 : ℝ) else 0) at h
      simpa only [smul_eq_mul, hbasis] using h
    calc
      _ = f b := by rw [hexp]; simp only [mul_comm]
      _ = 0 := hzero b hb

/-- Every finite all-late index list admits strictly positive weights whose
parity-adjusted linear functional annihilates every factorial-regular origin
response. The threshold precedes the dimension and index list. -/
theorem exists_weilLogShiftFiniteImpulse_positive_response_balance :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ),
      (∀ i, K ≤ indices i) → ∃ w : Fin d → ℝ, (∀ i, 0 < w i) ∧
      ∀ a : Fin d → ℝ, WeilLogShiftHasFactorialMajorant
        (fun n => ∑ i, a i * weilLogShiftRecoveryMomentResponse 0 n (indices i)) →
        ∑ i, w i * (-1 : ℝ) ^ indices i * a i = 0 := by
  obtain ⟨K, hK, hcone⟩ := exists_weilLogShiftAlignedResponse_no_factorial_majorant
  refine ⟨K, hK, ?_⟩
  intro d indices hk
  let s : Fin d → ℝ := fun i => (-1 : ℝ) ^ indices i
  have hs (i : Fin d) : s i * s i = 1 := by
    dsimp only [s]
    rw [← mul_pow]
    norm_num
  let R : (Fin d → ℝ) →ₗ[ℝ] (ℕ → ℝ) :=
    { toFun := fun b n => ∑ i, (s i * b i) *
        weilLogShiftRecoveryMomentResponse 0 n (indices i)
      map_add' := by
        intro b c
        funext n
        simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c b
        funext n
        change (∑ i, (s i * (c • b i)) *
          weilLogShiftRecoveryMomentResponse 0 n (indices i)) =
          c • (∑ i, (s i * b i) * weilLogShiftRecoveryMomentResponse 0 n (indices i))
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  let L := weilLogShiftFactorialSequenceSubmodule.comap R
  have hdisj : Disjoint (L : Set (Fin d → ℝ)) (stdSimplex ℝ (Fin d)) := by
    apply Set.disjoint_left.mpr
    intro b hbL hbΔ
    have halign (i : Fin d) : 0 ≤ (s i * b i) * (-1 : ℝ) ^ indices i := by
      change 0 ≤ (s i * b i) * s i
      have heq : (s i * b i) * s i = b i := by
        calc
          _ = (s i * s i) * b i := by ring
          _ = b i := by rw [hs, one_mul]
      rw [heq]
      exact hbΔ.1 i
    obtain ⟨i, hi⟩ : ∃ i : Fin d, b i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      have hsum := hbΔ.2
      simp only [hnone, Finset.sum_const_zero] at hsum
      norm_num at hsum
    have hnonzero : ∃ i : Fin d, s i * b i ≠ 0 := by
      refine ⟨i, ?_⟩
      intro hzero
      have heq : s i * (s i * b i) = b i := by rw [← mul_assoc, hs, one_mul]
      rw [hzero, mul_zero] at heq
      exact hi heq.symm
    change WeilLogShiftHasFactorialMajorant
      (fun n => ∑ i, (s i * b i) * weilLogShiftRecoveryMomentResponse 0 n (indices i)) at hbL
    exact hcone d indices (fun i => s i * b i) hk halign hnonzero 0 hbL
  obtain ⟨w, hw, hann⟩ := exists_positive_annihilator_of_disjoint_simplex L hdisj
  refine ⟨w, hw, ?_⟩
  intro a ha
  have hmem : (fun i => s i * a i) ∈ L := by
    change WeilLogShiftHasFactorialMajorant (R (fun i => s i * a i))
    have heq : R (fun i => s i * a i) =
        (fun n => ∑ i, a i * weilLogShiftRecoveryMomentResponse 0 n (indices i)) := by
      funext n
      change (∑ i, (s i * (s i * a i)) * weilLogShiftRecoveryMomentResponse 0 n (indices i)) = _
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, hs, one_mul]
    rw [heq]
    exact ha
  simpa only [s, mul_assoc] using hann (fun i => s i * a i) hmem

end RHTower
