import GaloisForLFunctions.RHTower.PhotonicLosslessHeatCosinePhaseDiagram
import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks

/-!
# Finite defects on the whole open heat–cosine quadrant

For `h, t > 0` let `A_{h,t}(z) = (H_t(z + ih) + H_t(z − ih))/2 = cos(hD) H_t`. A non-real zero `z` of
`A_{h,t}` lies in the defect disk of a zero `ζ` of `H_t` with `(Im ζ)² ≥ (Re ζ − Re z)² + (Im z)² + h²`
(`DeBruijn.exists_zero_mem_defectDisk` applied to `f = H_t`). Such a `ζ` is non-real, so by
Ki–Kim–Lee `|Re ζ| < X₀(t)`. The zero `z` therefore lies in the bounded box `|Re z| ≤ X₀(t) + ½`,
`|Im z| ≤ ½`, and the non-real zeros of `A_{h,t}` are finitely many
(`finite_nonreal_zeroCopy_heatCosine`). The finite-defect factorisation then gives:

* `exists_heatCosine_eq_defect_mul_ptr`: for all `h, t > 0`, `cos(hD) H_t` is a polynomial whose
  roots are exactly its non-real zeros, times a lossless product-port limit.

So on the whole open quadrant `h, t > 0` the lossless producer has a finite polynomial defect, and RH
says that every one of these defects is trivial
(`riemannHypothesis_iff_forall_isPtrProductPortLimit_heatCosine`). Only the closed boundary
`t = 0` can carry infinitely many defects (`h < ½`).
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

/-- The kernel `Φ(x) cosh(hx) e^{tx²}` of `cos(hD) H_t`. -/
theorem heatCosine_superExp (h t : ℝ) (ht : 0 ≤ t) :
    DeBruijn.SuperExpKernel
      (fun x => riemannKernelReal x * Real.cosh (h * x) * Real.exp (t * x ^ 2)) :=
  (DeBruijn.riemannKernel_mul_cosh_superExp h).mul_exp_sq ht

/-- **Finitely many defects.** For `h, t > 0`, `cos(hD) H_t` has finitely many non-real zero
copies. -/
theorem finite_nonreal_zeroCopy_heatCosine {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    {q : ZeroCopy (fun z => (DeBruijn.riemannHeat t (z + h * I) +
        DeBruijn.riemannHeat t (z - h * I)) / 2) |
      (zeroCopyPoint (fun z => (DeBruijn.riemannHeat t (z + h * I) +
        DeBruijn.riemannHeat t (z - h * I)) / 2) q).im ≠ 0}.Finite := by
  set A : ℂ → ℂ := fun z => (DeBruijn.riemannHeat t (z + h * I) +
    DeBruijn.riemannHeat t (z - h * I)) / 2 with hAdef
  have hkA := heatCosine_superExp h t ht.le
  have hAeq : DeBruijn.cosTransform
      (fun x => riemannKernelReal x * Real.cosh (h * x) * Real.exp (t * x ^ 2)) = A :=
    (heatCosine_eq_cosTransform h t ht.le).symm
  obtain ⟨CA, hCA0, hCA⟩ := hkA.exists_envelope
  rw [hAeq] at hCA
  have hAan : AnalyticOnNhd ℂ A univ := by
    rw [← hAeq]; exact hkA.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hA0 : A 0 ≠ 0 := by rw [← hAeq]; exact hkA.cosTransform_zero_ne
  -- the heat transform itself
  have hkH := DeBruijn.riemannKernel_superExp.mul_exp_sq ht.le
  obtain ⟨CH, hCH0, hCH⟩ := hkH.exists_envelope
  obtain ⟨X₀, hX₀⟩ := DeBruijn.exists_riemannHeat_zeros_real ht
  refine (finite_zeroCopy_norm_le hCA0 hAan hA0 hCA (|X₀| + 2)).subset ?_
  intro q hq
  simp only [mem_setOf_eq] at hq ⊢
  set z := zeroCopyPoint A q
  have hz : A z = 0 := DeBruijn.apply_zeroCopyPoint hAan q
  have hsum : DeBruijn.riemannHeat t (z + h * I) + DeBruijn.riemannHeat t (z - h * I) = 0 := by
    have : A z = 0 := hz
    simp only [hAdef] at this
    linear_combination 2 * this
  obtain ⟨ζ, hζ, hdisk⟩ := DeBruijn.exists_zero_mem_defectDisk hCH0
    (DeBruijn.riemannHeat_analytic ht.le) (riemannHeat_zero_ne ht.le)
    (DeBruijn.riemannHeat_neg ht.le) (DeBruijn.riemannHeat_conj ht.le) hCH hh hq hsum
  have hzim : 0 < z.im ^ 2 := by positivity
  have hζim : ζ.im ≠ 0 := by
    intro h0; rw [h0] at hdisk; nlinarith [sq_nonneg (ζ.re - z.re)]
  have hζre : |ζ.re| < X₀ := by
    by_contra hle
    exact hζim (hX₀ ζ hζ (not_lt.mp hle))
  have hζsq : ζ.im ^ 2 ≤ 1 / 4 := by
    have h1 := DeBruijn.riemannHeat_zeros_im_sq_le ht hζ
    exact h1.trans (max_le (by linarith) (by norm_num))
  have hzim2 : z.im ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (ζ.re - z.re)]
  have hclose : (ζ.re - z.re) ^ 2 ≤ 1 / 4 := by nlinarith
  have habs1 : |ζ.re - z.re| ≤ 1 / 2 := by
    have := sq_le_sq.mp (show (ζ.re - z.re) ^ 2 ≤ (1 / 2) ^ 2 by linarith)
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  have habs2 : |z.im| ≤ 1 / 2 := by
    have := sq_le_sq.mp (show z.im ^ 2 ≤ (1 / 2) ^ 2 by linarith)
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  have hre : |z.re| ≤ |X₀| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub z.re ζ.re
    rw [abs_sub_comm] at habs1
    linarith [le_abs_self X₀]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |X₀| + 2 := by linarith

/-- **Finite-defect producer on the open quadrant.** For all `h, t > 0`, `cos(hD) H_t` is a
polynomial whose roots are exactly its non-real zeros, times a lossless product-port limit. -/
theorem exists_heatCosine_eq_defect_mul_ptr {h t : ℝ} (hh : 0 < h) (ht : 0 < t) :
    ∃ N : Finset (ZeroCopy (fun z => (DeBruijn.riemannHeat t (z + h * I) +
        DeBruijn.riemannHeat t (z - h * I)) / 2)),
      (∀ q, q ∈ N ↔ (zeroCopyPoint (fun z => (DeBruijn.riemannHeat t (z + h * I) +
        DeBruijn.riemannHeat t (z - h * I)) / 2) q).im ≠ 0) ∧
      ∃ G : ℂ → ℂ, IsPtrProductPortLimit G ∧
        ∀ z, (DeBruijn.riemannHeat t (z + h * I) + DeBruijn.riemannHeat t (z - h * I)) / 2 =
          (∏ q ∈ N, (1 - z / zeroCopyPoint (fun z => (DeBruijn.riemannHeat t (z + h * I) +
            DeBruijn.riemannHeat t (z - h * I)) / 2) q)) * G z := by
  have hkA := heatCosine_superExp h t ht.le
  have hAeq := (heatCosine_eq_cosTransform h t ht.le).symm
  obtain ⟨CA, hCA0, hCA⟩ := hkA.exists_envelope
  rw [hAeq] at hCA
  have hAan : AnalyticOnNhd ℂ (fun z => (DeBruijn.riemannHeat t (z + h * I) +
      DeBruijn.riemannHeat t (z - h * I)) / 2) univ := by
    rw [← hAeq]; exact hkA.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hA0 : (fun z => (DeBruijn.riemannHeat t (z + h * I) +
      DeBruijn.riemannHeat t (z - h * I)) / 2) 0 ≠ 0 := by
    rw [← hAeq]; exact hkA.cosTransform_zero_ne
  have hAev : ∀ z, (fun z => (DeBruijn.riemannHeat t (z + h * I) +
      DeBruijn.riemannHeat t (z - h * I)) / 2) (-z) =
      (fun z => (DeBruijn.riemannHeat t (z + h * I) +
        DeBruijn.riemannHeat t (z - h * I)) / 2) z := by
    rw [← hAeq]; exact hkA.cosTransform_neg
  exact exists_eq_defect_mul_ptr_of_finite_nonreal hCA0 hAan hA0 hAev hCA
    (finite_nonreal_zeroCopy_heatCosine hh ht)

end

end RHTower
