import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.ZeroDensity.Definitions
import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality

/-! Apply the finite-dimensional Schur bound to the character Gram matrix. -/

open scoped InnerProductSpace

namespace QH.ZeroDensity

theorem duality_inequality : DualIneq := by
  intro ι κ S I b v Δ hΔ hrow
  classical
  let φ (i : ι) : EuclideanSpace ℂ I := WithLp.toLp 2 fun n => star (v i n)
  let a : EuclideanSpace ℂ I := WithLp.toLp 2 fun n => b n
  have hgram (i j : ι) : ⟪φ i, φ j⟫_ℂ = ∑ n ∈ I, v i n * starRingEnd ℂ (v j n) := by
    dsimp only [φ]
    rw [EuclideanSpace.inner_toLp_toLp]
    change (∑ n : I, star (v j n) * star (star (v i n))) = _
    simp only [star_star]
    rw [Finset.sum_coe_sort I (fun n => star (v j n) * v i n)]
    exact Finset.sum_congr rfl (fun n _ => mul_comm (star (v j n)) (v i n))
  have hlin (i : ι) : ⟪φ i, a⟫_ℂ = ∑ n ∈ I, b n * v i n := by
    dsimp only [φ, a]
    rw [EuclideanSpace.inner_toLp_toLp]
    change (∑ n : I, b n * star (star (v i n))) = _
    simp only [star_star]
    exact Finset.sum_coe_sort I (fun n => b n * v i n)
  have hnorm : ‖a‖ ^ 2 = ∑ n ∈ I, ‖b n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_coe_sort I (fun n => ‖b n‖ ^ 2)
  have h := RHTower.Sieve.sum_norm_inner_sq_le_of_schur S φ hΔ
    (fun i hi => by simpa only [hgram] using hrow i hi) a
  simpa only [hlin, hnorm, mul_comm Δ] using h

end QH.ZeroDensity
