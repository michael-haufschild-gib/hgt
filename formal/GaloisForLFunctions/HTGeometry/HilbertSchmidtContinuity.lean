/-
# Continuity of the Hilbert–Schmidt power traces

The regularized determinant of a Hilbert–Schmidt kernel is built from the traces `tr(Kⁿ)`.  To pass
from finite truncations to the kernel itself one needs those traces to be continuous in the
Hilbert–Schmidt norm, uniformly over a norm-bounded family.  That is what this file proves:

  `‖tr(Aⁿ⁺²) − tr(Bⁿ⁺²)‖ ≤ (n+2)·Mⁿ⁺¹·‖A − B‖_HS`   whenever `‖A‖_HS, ‖B‖_HS ≤ M`,

from the telescoping identity `Aᵐ⁺¹ − Bᵐ⁺¹ = A(Aᵐ − Bᵐ) + (A − B)Bᵐ` and Cauchy–Schwarz.

Supporting algebra proved here, absent from the kernel layer: the Hilbert–Schmidt kernels are closed
under addition and subtraction, their norm satisfies the triangle inequality, the composition is
bilinear, and the inner product is additive in each slot.

Main results:
* `isHS_add`, `isHS_sub`, `hsNorm_add_le`, `hsNorm_sub_le` — the normed-space structure.
* `hsComp_sub_left`, `hsComp_sub_right`, `hsNorm_hsComp_le` — the algebra structure.
* `hsNorm_hsPow_sub_le` — the telescoping estimate for powers.
* `hsTrace_hsPow_sub_norm_le` — continuity of the power traces.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidt

namespace HilbertSchmidt

open scoped BigOperators

variable {ι : Type*}

/-! ## The normed-space structure of Hilbert–Schmidt kernels -/

theorem isHS_add {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) : IsHS (A + B) := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    ((hA.mul_left 2).add (hB.mul_left 2))
  have h := norm_add_le (A p) (B p)
  have h1 : (0 : ℝ) ≤ ‖A p‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖B p‖ := norm_nonneg _
  have h3 : ‖(A + B) p‖ ≤ ‖A p‖ + ‖B p‖ := by simpa using h
  nlinarith [sq_nonneg (‖A p‖ - ‖B p‖), norm_nonneg ((A + B) p)]

theorem isHS_neg {A : ι × ι → ℂ} (hA : IsHS A) : IsHS (-A) := by
  refine hA.congr fun p => ?_
  simp

theorem isHS_sub {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) : IsHS (A - B) := by
  have := isHS_add hA (isHS_neg hB)
  refine this.congr fun p => ?_
  simp [sub_eq_add_neg]

theorem hsNorm_eq_lp_norm {K : ι × ι → ℂ} (hK : IsHS K) :
    hsNorm K = ‖(⟨K, hK.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)‖ := by
  rw [hsNorm, ← lp_norm_sq hK, Real.sqrt_sq (norm_nonneg _)]

theorem hsNorm_add_le {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) :
    hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  have hAB : IsHS (A + B) := isHS_add hA hB
  have hEq : (⟨A + B, hAB.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2)
      = (⟨A, hA.memℓp⟩ : lp (fun _ : ι × ι => ℂ) 2) + ⟨B, hB.memℓp⟩ := rfl
  rw [hsNorm_eq_lp_norm hAB, hsNorm_eq_lp_norm hA, hsNorm_eq_lp_norm hB, hEq]
  exact norm_add_le _ _

theorem hsNorm_neg (A : ι × ι → ℂ) : hsNorm (-A) = hsNorm A := by
  rw [hsNorm, hsNorm, hsNormSq, hsNormSq]
  exact congrArg Real.sqrt (tsum_congr fun p => by simp)

theorem hsNorm_sub_le {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) :
    hsNorm (A - B) ≤ hsNorm A + hsNorm B := by
  have h := hsNorm_add_le hA (isHS_neg hB)
  rw [hsNorm_neg] at h
  refine le_trans (le_of_eq ?_) h
  exact congrArg hsNorm (by funext p; simp [sub_eq_add_neg])

/-! ## Bilinearity of the composition -/

theorem hsComp_sub_left {A B C : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) (hC : IsHS C) :
    hsComp (A - B) C = hsComp A C - hsComp B C := by
  funext p
  simp only [hsComp, Pi.sub_apply]
  rw [← (hsComp_summable hA hC p.1 p.2).tsum_sub (hsComp_summable hB hC p.1 p.2)]
  exact tsum_congr fun k => by simp [sub_mul]

theorem hsComp_sub_right {A B C : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) (hC : IsHS C) :
    hsComp A (B - C) = hsComp A B - hsComp A C := by
  funext p
  simp only [hsComp, Pi.sub_apply]
  rw [← (hsComp_summable hA hB p.1 p.2).tsum_sub (hsComp_summable hA hC p.1 p.2)]
  exact tsum_congr fun k => by simp [mul_sub]

theorem hsNorm_hsComp_le {K L : ι × ι → ℂ} (hK : IsHS K) (hL : IsHS L) :
    hsNorm (hsComp K L) ≤ hsNorm K * hsNorm L := by
  rw [hsNorm, hsNorm, hsNorm, ← Real.sqrt_mul (hsNormSq_nonneg K)]
  exact Real.sqrt_le_sqrt (hsNormSq_hsComp_le hK hL)

/-! ## Additivity of the inner product -/

theorem hsInner_sub_left {A B L : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) (hL : IsHS L) :
    hsInner (A - B) L = hsInner A L - hsInner B L := by
  rw [hsInner, hsInner, hsInner,
    ← (hsInner_summable hA hL).tsum_sub (hsInner_summable hB hL)]
  refine tsum_congr fun p => ?_
  simp only [Pi.sub_apply, map_sub]
  ring

theorem hsInner_sub_right {K A B : ι × ι → ℂ} (hK : IsHS K) (hA : IsHS A) (hB : IsHS B) :
    hsInner K (A - B) = hsInner K A - hsInner K B := by
  rw [hsInner, hsInner, hsInner,
    ← (hsInner_summable hK hA).tsum_sub (hsInner_summable hK hB)]
  refine tsum_congr fun p => ?_
  simp only [Pi.sub_apply]
  ring

/-! ## The telescoping estimate -/

/-- **Powers are Lipschitz on a norm ball.**  `‖Aⁿ⁺¹ − Bⁿ⁺¹‖_HS ≤ (n+1)·Mⁿ·‖A − B‖_HS` when both
norms are at most `M`, by the telescoping identity `Aᵐ⁺¹ − Bᵐ⁺¹ = A(Aᵐ − Bᵐ) + (A − B)Bᵐ`. -/
theorem hsNorm_hsPow_sub_le {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) {M : ℝ}
    (hAM : hsNorm A ≤ M) (hBM : hsNorm B ≤ M) :
    ∀ n : ℕ, hsNorm (hsPow A n - hsPow B n) ≤ (n + 1 : ℝ) * M ^ n * hsNorm (A - B)
  | 0 => by simp [hsPow]
  | (n + 1) => by
    have hM : 0 ≤ M := le_trans (hsNorm_nonneg A) hAM
    have hAn := isHS_hsPow hA n
    have hBn := isHS_hsPow hB n
    have hsplit : hsPow A (n + 1) - hsPow B (n + 1)
        = hsComp A (hsPow A n - hsPow B n) + hsComp (A - B) (hsPow B n) := by
      rw [hsComp_sub_right hA hAn hBn, hsComp_sub_left hA hB hBn]
      funext p
      simp only [hsPow, Pi.add_apply, Pi.sub_apply]
      ring
    have h1 : hsNorm (hsComp A (hsPow A n - hsPow B n)) ≤ M * ((n + 1 : ℝ) * M ^ n * hsNorm (A - B)) := by
      refine le_trans (hsNorm_hsComp_le hA (isHS_sub hAn hBn)) ?_
      exact mul_le_mul hAM (hsNorm_hsPow_sub_le hA hB hAM hBM n) (hsNorm_nonneg _) hM
    have h2 : hsNorm (hsComp (A - B) (hsPow B n)) ≤ hsNorm (A - B) * M ^ (n + 1) := by
      refine le_trans (hsNorm_hsComp_le (isHS_sub hA hB) hBn) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hsNorm_nonneg _)
      exact le_trans (hsNorm_hsPow_le hB n) (pow_le_pow_left₀ (hsNorm_nonneg B) hBM _)
    calc hsNorm (hsPow A (n + 1) - hsPow B (n + 1))
        ≤ hsNorm (hsComp A (hsPow A n - hsPow B n))
            + hsNorm (hsComp (A - B) (hsPow B n)) := by
          rw [hsplit]
          exact hsNorm_add_le (isHS_hsComp hA (isHS_sub hAn hBn))
            (isHS_hsComp (isHS_sub hA hB) hBn)
      _ ≤ M * ((n + 1 : ℝ) * M ^ n * hsNorm (A - B)) + hsNorm (A - B) * M ^ (n + 1) :=
          add_le_add h1 h2
      _ = ((n + 1 : ℕ) + 1 : ℝ) * M ^ (n + 1) * hsNorm (A - B) := by push_cast; ring

/-! ## Continuity of the power traces -/

/-- **The power traces are Lipschitz on a Hilbert–Schmidt norm ball.**  This is what lets the
regularized determinant of a Hilbert–Schmidt kernel be obtained as a limit of truncations. -/
theorem hsTrace_hsPow_sub_norm_le {A B : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) {M : ℝ}
    (hAM : hsNorm A ≤ M) (hBM : hsNorm B ≤ M) (n : ℕ) :
    ‖(∑' i : ι, hsPow A (n + 1) (i, i)) - ∑' i : ι, hsPow B (n + 1) (i, i)‖
      ≤ (n + 2 : ℝ) * M ^ (n + 1) * hsNorm (A - B) := by
  have hM : 0 ≤ M := le_trans (hsNorm_nonneg A) hAM
  have hAn := isHS_hsPow hA n
  have hBn := isHS_hsPow hB n
  rw [hsTrace_hsPow_succ hA, hsTrace_hsPow_succ hB]
  have hsplit : hsInner (hsAdjoint A) (hsPow A n) - hsInner (hsAdjoint B) (hsPow B n)
      = hsInner (hsAdjoint A - hsAdjoint B) (hsPow A n)
        + hsInner (hsAdjoint B) (hsPow A n - hsPow B n) := by
    rw [hsInner_sub_left (isHS_hsAdjoint hA) (isHS_hsAdjoint hB) hAn,
      hsInner_sub_right (isHS_hsAdjoint hB) hAn hBn]
    ring
  have hadjsub : hsAdjoint A - hsAdjoint B = hsAdjoint (A - B) := by
    funext p; simp [hsAdjoint]
  have h1 : ‖hsInner (hsAdjoint A - hsAdjoint B) (hsPow A n)‖ ≤ hsNorm (A - B) * M ^ (n + 1) := by
    rw [hadjsub]
    refine le_trans (hsInner_norm_le (isHS_hsAdjoint (isHS_sub hA hB)) hAn) ?_
    have hleft : Real.sqrt (hsNormSq (hsAdjoint (A - B))) = hsNorm (A - B) := by
      rw [← hsNorm, hsNorm_hsAdjoint]
    have hright : Real.sqrt (hsNormSq (hsPow A n)) = hsNorm (hsPow A n) := rfl
    rw [hleft, hright]
    refine mul_le_mul_of_nonneg_left ?_ (hsNorm_nonneg _)
    exact le_trans (hsNorm_hsPow_le hA n) (pow_le_pow_left₀ (hsNorm_nonneg A) hAM _)
  have h2 : ‖hsInner (hsAdjoint B) (hsPow A n - hsPow B n)‖
      ≤ M * ((n + 1 : ℝ) * M ^ n * hsNorm (A - B)) := by
    refine le_trans (hsInner_norm_le (isHS_hsAdjoint hB) (isHS_sub hAn hBn)) ?_
    have hleft : Real.sqrt (hsNormSq (hsAdjoint B)) = hsNorm B := by
      rw [← hsNorm, hsNorm_hsAdjoint]
    have hright : Real.sqrt (hsNormSq (hsPow A n - hsPow B n)) = hsNorm (hsPow A n - hsPow B n) :=
      rfl
    rw [hleft, hright]
    exact mul_le_mul hBM (hsNorm_hsPow_sub_le hA hB hAM hBM n) (hsNorm_nonneg _) hM
  calc ‖hsInner (hsAdjoint A) (hsPow A n) - hsInner (hsAdjoint B) (hsPow B n)‖
      = ‖hsInner (hsAdjoint A - hsAdjoint B) (hsPow A n)
          + hsInner (hsAdjoint B) (hsPow A n - hsPow B n)‖ := by rw [hsplit]
    _ ≤ ‖hsInner (hsAdjoint A - hsAdjoint B) (hsPow A n)‖
          + ‖hsInner (hsAdjoint B) (hsPow A n - hsPow B n)‖ := norm_add_le _ _
    _ ≤ hsNorm (A - B) * M ^ (n + 1) + M * ((n + 1 : ℝ) * M ^ n * hsNorm (A - B)) :=
        add_le_add h1 h2
    _ = (n + 2 : ℝ) * M ^ (n + 1) * hsNorm (A - B) := by ring

end HilbertSchmidt
