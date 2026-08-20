/-
# The spectral phase is real-analytic on the simple-spectrum cone

Normalising a nonzero vector is real-analytic -- the Euclidean norm is the square root of a
polynomial, and the square root is `exp ∘ (log/2)` on the positive axis -- and the canonically
labelled spectral action is real-analytic wherever the spectrum is simple.  The discriminant
detects simplicity and is homogeneous, so it does not vanish at the normalised point either.
Composing gives analyticity of the phase on the whole simple-spectrum cone.

Main results:
* `analyticAt_rsqrt`, `analyticAt_normInv`, `analyticAt_normalise` — normalisation is analytic.
* `injective_eigenvalues_of_disc_ne_zero` — the discriminant detects a simple spectrum.
* `analyticOnNhd_spectralActionPhase` — **the phase is analytic on the simple-spectrum cone**.
-/
import GaloisForLFunctions.HTGeometry.SortedEigenbranchAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Filter Topology Set Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The square root is real-analytic at every positive point. -/
theorem analyticAt_rsqrt {t : ℝ} (ht : 0 < t) : AnalyticAt ℝ Real.sqrt t := by
  have hbase : AnalyticAt ℝ (fun s : ℝ => Real.exp (Real.log s * (1 / 2))) t :=
    analyticAt_rexp.comp ((analyticAt_log ht).mul analyticAt_const)
  refine hbase.congr ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [← Real.rpow_def_of_pos hs, ← Real.sqrt_eq_rpow]

variable {N : ℕ}

theorem norm_eq_sqrt_sum_sq (y : EuclideanSpace ℝ (Fin N)) :
    ‖y‖ = Real.sqrt (∑ a, ((WithLp.ofLp y) a) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [Real.norm_eq_abs, sq_abs]

theorem analyticAt_sumSq (y₀ : EuclideanSpace ℝ (Fin N)) :
    AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin N) => ∑ a, ((WithLp.ofLp y) a) ^ 2) y₀ := by
  refine Finset.analyticAt_fun_sum (Finset.univ : Finset (Fin N)) fun a _ => ?_
  exact ((EuclideanSpace.proj (𝕜 := ℝ) a).analyticAt y₀).pow 2

theorem analyticAt_norm {y₀ : EuclideanSpace ℝ (Fin N)} (hy : y₀ ≠ 0) :
    AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin N) => ‖y‖) y₀ := by
  have hpos : 0 < ∑ a, ((WithLp.ofLp y₀) a) ^ 2 := by
    have h := norm_eq_sqrt_sum_sq y₀
    have hnn : (0 : ℝ) ≤ ∑ a, ((WithLp.ofLp y₀) a) ^ 2 :=
      Finset.sum_nonneg fun a _ => sq_nonneg _
    rcases lt_or_eq_of_le hnn with hlt | heq
    · exact hlt
    · exfalso
      rw [← heq, Real.sqrt_zero] at h
      exact hy (norm_eq_zero.mp h)
  have hcomp : AnalyticAt ℝ
      (fun y : EuclideanSpace ℝ (Fin N) => Real.sqrt (∑ a, ((WithLp.ofLp y) a) ^ 2)) y₀ :=
    AnalyticAt.comp (g := Real.sqrt)
      (f := fun y : EuclideanSpace ℝ (Fin N) => ∑ a, ((WithLp.ofLp y) a) ^ 2)
      (analyticAt_rsqrt hpos) (analyticAt_sumSq y₀)
  exact hcomp.congr (Filter.Eventually.of_forall fun y => (norm_eq_sqrt_sum_sq y).symm)

theorem analyticAt_normInv {y₀ : EuclideanSpace ℝ (Fin N)} (hy : y₀ ≠ 0) :
    AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin N) => ‖y‖⁻¹) y₀ :=
  (analyticAt_inv (norm_ne_zero_iff.mpr hy)).comp (analyticAt_norm hy)

/-- **Normalisation is real-analytic away from the origin.** -/
theorem analyticAt_normalise {y₀ : EuclideanSpace ℝ (Fin N)} (hy : y₀ ≠ 0) :
    AnalyticAt ℝ
      (fun y : EuclideanSpace ℝ (Fin N) => (fun a => ‖y‖⁻¹ * (WithLp.ofLp y) a)) y₀ :=
  AnalyticAt.pi fun a =>
    (analyticAt_normInv hy).mul ((EuclideanSpace.proj (𝕜 := ℝ) a).analyticAt y₀)

variable {D : ℕ}

/-- **A nonvanishing discriminant is a simple spectrum.** -/
theorem injective_eigenvalues_of_disc_ne_zero {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) {θ : Fin N → ℝ}
    (h : MvPolynomial.eval θ (spectralDiscriminantPoly P) ≠ 0) :
    Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues := by
  classical
  rw [eval_spectralDiscriminantPoly hP θ] at h
  have hprod : (∏ i, ∏ j ∈ Finset.Ioi i,
      ((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j
        - (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)) ≠ 0 := by
    intro hz
    exact h (by rw [hz]; ring)
  intro i j hij
  by_contra hne
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact hprod (Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_Ioi.mpr hlt) (sub_eq_zero.mpr hij.symm)))
  · exact hne heq
  · exact hprod (Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_Ioi.mpr hgt) (sub_eq_zero.mpr hij)))

section Cone

variable {m : ℕ}

/-- **The spectral phase is real-analytic on the simple-spectrum cone.** -/
theorem analyticOnNhd_spectralActionPhase {P : Fin m → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) :
    AnalyticOnNhd ℝ (spectralActionPhase hP k) (simpleSpectrumCone P) := by
  intro y hy
  obtain ⟨hdisc, hball⟩ := hy
  have hyne : y ≠ 0 := hball.2
  have hnormpos : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  have htne : (‖y‖⁻¹ : ℝ) ≠ 0 := inv_ne_zero hnormpos.ne'
  have hdisc' : MvPolynomial.eval (fun a => ‖y‖⁻¹ * (WithLp.ofLp y) a)
      (spectralDiscriminantPoly P) ≠ 0 := by
    rw [eval_smul_of_isHomogeneous (isHomogeneous_spectralDiscriminantPoly hP) (‖y‖⁻¹)]
    exact mul_ne_zero (pow_ne_zero _ htne) hdisc
  have hinj := injective_eigenvalues_of_disc_ne_zero hP hdisc'
  exact (analyticAt_sortedSpectralAction hP k hinj).comp (analyticAt_normalise hyne)

end Cone

end

end GaloisForLFunctions.HTGeometry
