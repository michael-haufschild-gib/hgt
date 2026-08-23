import GaloisForLFunctions.HTGeometry.FiniteDeterminantZeros
import GaloisForLFunctions.RHTower.HermitianDeterminantRH
import GaloisForLFunctions.RHTower.XiCRealZeroVitaliBlowup

/-!
# Hilbert--Schmidt energy blow-up for finite Hermitian Xi determinants

Vitali local boundedness becomes automatic for finite Hilbert--Carleman determinants whose
Hilbert--Schmidt energies have one uniform cap.  The Carleman inequality supplies the local bound,
while Hermiticity puts every determinant zero on the real axis.  Therefore pointwise convergence
to centered Xi on any uniqueness set proves RH.

The normalization by `XiC 0` is forced: every finite `det₂(I + zM)` equals one at `z = 0`.
Its contrapositive is a physical obstruction.  If RH is false, every pointwise-convergent finite
Hermitian determinant model must have unbounded Hilbert--Schmidt energy.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Finite Hilbert--Carleman determinant with the source-forced centered-Xi normalization. -/
noncomputable def xiCNormalizedFiniteDet2
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : ℂ :=
  XiC 0 * finiteDet2 M z

/-- A finite Hermitian Hilbert--Carleman determinant has only real zeros. -/
theorem xiCNormalizedFiniteDet2_zero_im_eq_zero
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsHermitian) {z : ℂ}
    (hz : xiCNormalizedFiniteDet2 M z = 0) :
    z.im = 0 := by
  have hdet : finiteDet2 M z = 0 := by
    exact (mul_eq_zero.mp hz).resolve_left XiC_zero_ne
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp [finiteDet2] at hdet
  obtain ⟨v, hv0, hv⟩ :=
    (finiteDet2_eq_zero_iff_exists_eigenvector M hz0).mp hdet
  have hchar : M.charpoly.eval (-z⁻¹) = 0 := by
    rw [Matrix.eval_charpoly]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec]
    simpa using congrArg (fun x => (-z⁻¹) • v - x) hv
  have hinvIm : (-z⁻¹).im = 0 :=
    hermitian_charpoly_zero_im_eq_zero hM hchar
  rw [neg_im, Complex.inv_im] at hinvIm
  have hnormSq : Complex.normSq z ≠ 0 :=
    (Complex.normSq_pos.mpr hz0).ne'
  field_simp [hnormSq] at hinvIm
  simpa using hinvIm

/-- A uniform Hilbert--Schmidt energy cap gives local boundedness of the normalized finite
determinants, independently of matrix dimension. -/
theorem locallyBoundedEntireSequence_xiCNormalizedFiniteDet2_of_hsEnergy_le
    {d : ℕ → ℕ} {M : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ}
    {B : ℝ} (hB : ∀ k, matHSNormSq (M k) ≤ B) :
    LocallyBoundedEntireSequence (fun k => xiCNormalizedFiniteDet2 (M k)) := by
  intro z
  have hB0 : 0 ≤ B :=
    (matHSNormSq_nonneg (M 0)).trans (hB 0)
  refine ⟨1, by norm_num, ‖XiC 0‖ * Real.exp ((‖z‖ + 1) ^ 2 * B / 2), ?_⟩
  intro k w hw
  have hwDiff : ‖w - z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hwNorm : ‖w‖ ≤ ‖z‖ + 1 := by
    calc
      ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 1 := by linarith
  have hwSq : ‖w‖ ^ 2 ≤ (‖z‖ + 1) ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg z]
  have hExponent :
      ‖w‖ ^ 2 * matHSNormSq (M k) / 2 ≤
        (‖z‖ + 1) ^ 2 * B / 2 := by
    nlinarith [matHSNormSq_nonneg (M k), hB k]
  change ‖XiC 0 * finiteDet2 (M k) w‖ ≤ _
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_finiteDet2_fin_le (M k) w).trans
    (Real.exp_le_exp.mpr hExponent)

/-- **[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] Finite-det₂ Vitali criterion.**
For finite Hermitian matrices of arbitrary growing dimension, uniform Hilbert--Schmidt energy and
pointwise convergence of their normalized regularized determinants to `XiC` on one uniqueness set
already prove RH.  Compact-open convergence is not an input. -/
theorem riemannHypothesis_of_XiC_finiteDet2_pointwise_of_hsEnergy_le
    {d : ℕ → ℕ} {M : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ}
    {Y : Set ℂ} {z₀ : ℂ} {B : ℝ}
    (hM : ∀ k, (M k).IsHermitian)
    (hB : ∀ k, matHSNormSq (M k) ≤ B)
    (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hpointwise : ∀ z ∈ Y,
      Tendsto (fun k => xiCNormalizedFiniteDet2 (M k) z) atTop (𝓝 (XiC z))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_XiC_vitali_realZero_approximants
  · intro k
    exact (differentiable_const (XiC 0)).mul (differentiable_finiteDet2 (M k))
  · exact locallyBoundedEntireSequence_xiCNormalizedFiniteDet2_of_hsEnergy_le hB
  · exact hacc
  · exact hpointwise
  · intro k z hz
    exact xiCNormalizedFiniteDet2_zero_im_eq_zero (hM k) hz

/-- **[LEAN-PROVED] [OBSTRUCTION] [NOVELTY UNVERIFIED] Hilbert--Schmidt energy blow-up.**
Under false RH, a pointwise Xi limit of finite Hermitian regularized determinants on a uniqueness
set cannot have any global Hilbert--Schmidt energy cap. -/
theorem hsEnergy_unbounded_of_not_riemannHypothesis_of_XiC_finiteDet2_pointwise
    {d : ℕ → ℕ} {M : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ}
    {Y : Set ℂ} {z₀ : ℂ}
    (hnot : ¬ RiemannHypothesis)
    (hM : ∀ k, (M k).IsHermitian)
    (hacc : ∃ᶠ z in 𝓝[≠] z₀, z ∈ Y)
    (hpointwise : ∀ z ∈ Y,
      Tendsto (fun k => xiCNormalizedFiniteDet2 (M k) z) atTop (𝓝 (XiC z))) :
    ∀ B : ℝ, ∃ k : ℕ, B < matHSNormSq (M k) := by
  by_contra hbounded
  push Not at hbounded
  obtain ⟨B, hB⟩ := hbounded
  exact hnot (riemannHypothesis_of_XiC_finiteDet2_pointwise_of_hsEnergy_le
    hM hB hacc hpointwise)

end RHTower
