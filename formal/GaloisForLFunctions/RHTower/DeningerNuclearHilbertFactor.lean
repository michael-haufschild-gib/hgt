import GaloisForLFunctions.RHTower.DeningerNuclearBalanced
import GaloisForLFunctions.RHTower.DeningerNuclearHilbertSchmidt

/-!
# A nuclear map is dominated by a Hilbertian seminorm

In a balanced representation the functional norms are square-summable, so the coefficient family
of a vector lies in `ℓ²` and its `ℓ²` norm is bounded by a multiple of the norm of the vector.
Cauchy–Schwarz then bounds the norm of the image of the map by the same multiple of that `ℓ²`
norm.

So a nuclear map factors, up to the two inequalities, through a Hilbert space: it is dominated by
a Hilbertian seminorm which is itself dominated by the norm.  This is the refinement that makes a
presenting family of seminorms Hilbertian, and hence the input the permanence theory for closed
subspaces needs.

* `deningerTsum_mul_le_sqrt` : Cauchy–Schwarz for sums of nonnegative families.
* `DeningerIsNuclear.exists_hilbert_factor` : a nuclear map is dominated by a Hilbertian seminorm.
-/

namespace RHTower

open scoped ENNReal NNReal

section CauchySchwarz

/-- **Cauchy–Schwarz for sums.**  The sum of a product of nonnegative square-summable families is
at most the product of the square roots of the sums of squares. -/
theorem deningerTsum_mul_le_sqrt {κ : Type*} {f g : κ → ℝ}
    (hf : Summable fun i => f i ^ 2) (hg : Summable fun i => g i ^ 2)
    (hfn : ∀ i, 0 ≤ f i) (hgn : ∀ i, 0 ≤ g i) :
    ∑' i, f i * g i ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
  have hmul : Summable fun i => f i * g i := deningerSummable_mul_of_sq hf hg hfn hgn
  refine hmul.tsum_le_of_sum_le fun s => ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s f g
  have hf' : ∑ i ∈ s, f i ^ 2 ≤ ∑' i, f i ^ 2 :=
    Summable.sum_le_tsum s (fun i _ => sq_nonneg (f i)) hf
  have hg' : ∑ i ∈ s, g i ^ 2 ≤ ∑' i, g i ^ 2 :=
    Summable.sum_le_tsum s (fun i _ => sq_nonneg (g i)) hg
  have hnn : 0 ≤ ∑ i ∈ s, f i * g i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hfn i) (hgn i)
  have hsq : (∑ i ∈ s, f i * g i) ^ 2
      ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
    refine hcs.trans (mul_le_mul hf' hg' (Finset.sum_nonneg fun i _ => sq_nonneg (g i)) ?_)
    exact le_trans (Finset.sum_nonneg fun i _ => sq_nonneg (f i)) hf'
  have hprod : Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2)
      = Real.sqrt ((∑' i, f i ^ 2) * ∑' i, g i ^ 2) :=
    (Real.sqrt_mul (le_trans (Finset.sum_nonneg fun i _ => sq_nonneg (f i)) hf') _).symm
  rw [hprod, ← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hsq

end CauchySchwarz

section HilbertFactor

variable {𝕜 X Y : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A nuclear map is dominated by a Hilbertian seminorm.**  There is a bounded map into an `ℓ²`
space whose norm dominates the norm of the image of the map, and is itself dominated by the norm
of the argument. -/
theorem DeningerIsNuclear.exists_hilbert_factor {T : X →L[𝕜] Y} (hT : DeningerIsNuclear T) :
    ∃ (ι : Type) (A : X →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2) (C : ℝ), 0 ≤ C ∧
      (∀ x, ‖A x‖ ≤ C * ‖x‖) ∧ (∀ x, ‖T x‖ ≤ C * ‖A x‖) := by
  classical
  obtain ⟨ι, φ, y, hbal, hsq, happ⟩ := hT.exists_balanced_summable_sq
  set M : ℝ := ∑' a, ‖φ a‖ ^ 2 with hM
  have hMnn : 0 ≤ M := tsum_nonneg fun a => sq_nonneg _
  have hcoefsq : ∀ x : X, Summable fun a => ‖φ a x‖ ^ 2 := by
    intro x
    refine Summable.of_nonneg_of_le (fun a => sq_nonneg _) (fun a => ?_)
      (hsq.mul_right (‖x‖ ^ 2))
    calc ‖φ a x‖ ^ 2 ≤ (‖φ a‖ * ‖x‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ((φ a).le_opNorm x) 2
      _ = ‖φ a‖ ^ 2 * ‖x‖ ^ 2 := by ring
  have hp2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have htwo : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  have hmem : ∀ x : X, Memℓp (fun a => φ a x) 2 := by
    intro x
    refine memℓp_gen ?_
    rw [htwo]
    simpa only [Real.rpow_natCast] using hcoefsq x
  set A : X →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2 :=
    { toFun := fun x => ⟨fun a => φ a x, hmem x⟩
      map_add' := by
        intro x z
        refine lp.ext ?_
        funext a
        simp
      map_smul' := by
        intro c x
        refine lp.ext ?_
        funext a
        simp } with hA
  have hAnorm : ∀ x : X, ‖A x‖ ^ 2 = ∑' a, ‖φ a x‖ ^ 2 := by
    intro x
    have h := lp.norm_rpow_eq_tsum hp2 (A x)
    rw [htwo] at h
    simp only [Real.rpow_natCast] at h
    exact h
  refine ⟨ι, A, Real.sqrt M, Real.sqrt_nonneg M, ?_, ?_⟩
  · intro x
    have hle : ‖A x‖ ^ 2 ≤ (Real.sqrt M * ‖x‖) ^ 2 := by
      rw [hAnorm x, mul_pow, Real.sq_sqrt hMnn, hM, ← tsum_mul_right]
      refine Summable.tsum_le_tsum (fun a => ?_) (hcoefsq x) (hsq.mul_right (‖x‖ ^ 2))
      calc ‖φ a x‖ ^ 2 ≤ (‖φ a‖ * ‖x‖) ^ 2 := by
            refine pow_le_pow_left₀ (norm_nonneg _) ((φ a).le_opNorm x) 2
        _ = ‖φ a‖ ^ 2 * ‖x‖ ^ 2 := by ring
    have h1 : (0:ℝ) ≤ ‖A x‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ Real.sqrt M * ‖x‖ := by positivity
    nlinarith [hle, h1, h2]
  · intro x
    have hsummable : Summable fun a => ‖φ a x • y a‖ := by
      have heq : (fun a => ‖φ a x • y a‖) = fun a => ‖φ a x‖ * ‖φ a‖ := by
        funext a
        rw [norm_smul, hbal a]
      rw [heq]
      exact deningerSummable_mul_of_sq (hcoefsq x) hsq (fun _ => norm_nonneg _)
        (fun _ => norm_nonneg _)
    have hTx : T x = ∑' a, φ a x • y a := (happ x).tsum_eq.symm
    calc ‖T x‖ = ‖∑' a, φ a x • y a‖ := by rw [hTx]
      _ ≤ ∑' a, ‖φ a x • y a‖ := norm_tsum_le_tsum_norm hsummable
      _ = ∑' a, ‖φ a x‖ * ‖φ a‖ := by
          refine tsum_congr fun a => ?_
          rw [norm_smul, hbal a]
      _ ≤ Real.sqrt (∑' a, ‖φ a x‖ ^ 2) * Real.sqrt (∑' a, ‖φ a‖ ^ 2) :=
          deningerTsum_mul_le_sqrt (hcoefsq x) hsq (fun _ => norm_nonneg _)
            (fun _ => norm_nonneg _)
      _ = Real.sqrt M * ‖A x‖ := by
          rw [hM, ← hAnorm x, Real.sqrt_sq (norm_nonneg _), mul_comm]

end HilbertFactor

end RHTower

