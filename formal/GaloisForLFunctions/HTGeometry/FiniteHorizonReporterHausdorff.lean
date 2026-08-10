import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-horizon Hausdorff stability of a weighted reporter orbit

A finite reporter family is a finite set of observables `B a` with nonnegative weights `λ a`.  Its
scale is

```text
𝓑 = (∑_a λ_a ‖B_a‖²)^{1/2},
```

the `ℓ²` norm of the weighted family.  The Heisenberg orbit of the family under a self-adjoint
generator is the curve of weighted conjugates, and the pointwise `C⋆` stability bound gives the
same factor on the whole family at once.  Consequently the orbits of two generators over a finite
horizon `[-T, T]` are Hausdorff-close:

```text
d_H(X_H(T), X_K(T)) ≤ 2 T ‖H - K‖ 𝓑,
```

which for a coupling family `H_g = H + g V` is `2 T |g| ‖V‖ 𝓑`: no bounded-time observation of a
finite reporter family can resolve an order-one profile change before time of order
`ε / (|g| ‖V‖ 𝓑)`.
-/

open NormedSpace Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] {N : Type*} [Fintype N]

/-- The weighted reporter family as a vector of the `ℓ²` product of the algebra. -/
def reporterFamily (lam : N → ℝ) (B : N → A) : PiLp 2 fun _ : N => A :=
  WithLp.toLp 2 fun a => Real.sqrt (lam a) • B a

/-- The scale `𝓑 = (∑ λ_a ‖B_a‖²)^{1/2}` of a reporter family. -/
theorem norm_reporterFamily (lam : N → ℝ) (hlam : ∀ a, 0 ≤ lam a) (B : N → A) :
    ‖reporterFamily lam B‖ = Real.sqrt (∑ a, lam a * ‖B a‖ ^ 2) := by
  rw [reporterFamily, PiLp.norm_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have : ‖Real.sqrt (lam a) • B a‖ = Real.sqrt (lam a) * ‖B a‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [show (WithLp.toLp 2 fun a => Real.sqrt (lam a) • B a).ofLp a =
      Real.sqrt (lam a) • B a from rfl, this, mul_pow, Real.sq_sqrt (hlam a)]

/-- The Heisenberg orbit of a weighted reporter family under a self-adjoint generator. -/
def reporterOrbit (lam : N → ℝ) (B : N → A) (H : A) (t : ℝ) : PiLp 2 fun _ : N => A :=
  WithLp.toLp 2 fun a =>
    Real.sqrt (lam a) •
      (exp (t • ((-Complex.I) • H)) * B a * star (exp (t • ((-Complex.I) • H))))

/-- **Pointwise finite-horizon stability of the whole family.**  The single-observable `C⋆` bound
is uniform in the family and rescales by its `ℓ²` scale. -/
theorem norm_reporterOrbit_sub_le (lam : N → ℝ) (hlam : ∀ a, 0 ≤ lam a) (B : N → A)
    (H K : A) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (t : ℝ) :
    ‖reporterOrbit lam B H t - reporterOrbit lam B K t‖ ≤
      2 * |t| * ‖H - K‖ * ‖reporterFamily lam B‖ := by
  have hpoint : ∀ a : N,
      ‖(reporterOrbit lam B H t - reporterOrbit lam B K t).ofLp a‖ ≤
        2 * |t| * ‖H - K‖ * (Real.sqrt (lam a) * ‖B a‖) := by
    intro a
    have hcstar := selfAdjoint_heisenbergEvolution_norm_sub_le H K (B a) hH hK t
    have hsplit : (reporterOrbit lam B H t - reporterOrbit lam B K t).ofLp a =
        Real.sqrt (lam a) •
          (exp (t • ((-Complex.I) • H)) * B a * star (exp (t • ((-Complex.I) • H))) -
            exp (t • ((-Complex.I) • K)) * B a * star (exp (t • ((-Complex.I) • K)))) := by
      rw [smul_sub]
      rfl
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (lam a) *
          ‖exp (t • ((-Complex.I) • H)) * B a * star (exp (t • ((-Complex.I) • H))) -
            exp (t • ((-Complex.I) • K)) * B a * star (exp (t • ((-Complex.I) • K)))‖
        ≤ Real.sqrt (lam a) * (2 * |t| * ‖H - K‖ * ‖B a‖) := by
          exact mul_le_mul_of_nonneg_left hcstar (Real.sqrt_nonneg _)
      _ = 2 * |t| * ‖H - K‖ * (Real.sqrt (lam a) * ‖B a‖) := by ring
  have hC : (0 : ℝ) ≤ 2 * |t| * ‖H - K‖ := by positivity
  rw [PiLp.norm_eq_of_L2, norm_reporterFamily lam hlam B]
  rw [show 2 * |t| * ‖H - K‖ * Real.sqrt (∑ a, lam a * ‖B a‖ ^ 2) =
      Real.sqrt ((2 * |t| * ‖H - K‖) ^ 2 * ∑ a, lam a * ‖B a‖ ^ 2) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC]]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have hsq := hpoint a
  have hnn : (0 : ℝ) ≤ ‖(reporterOrbit lam B H t - reporterOrbit lam B K t).ofLp a‖ :=
    norm_nonneg _
  calc ‖(reporterOrbit lam B H t - reporterOrbit lam B K t).ofLp a‖ ^ 2
      ≤ (2 * |t| * ‖H - K‖ * (Real.sqrt (lam a) * ‖B a‖)) ^ 2 := by
        apply pow_le_pow_left₀ hnn hsq
    _ = (2 * |t| * ‖H - K‖) ^ 2 * (lam a * ‖B a‖ ^ 2) := by
        rw [mul_pow]
        congr 1
        rw [mul_pow, Real.sq_sqrt (hlam a)]

/-- **Finite-horizon Hausdorff stability.**  Over the horizon `[-T, T]` the reporter orbits of two
self-adjoint generators are Hausdorff-close, with the constant carried entirely by the reporter
scale. -/
theorem hausdorffDist_reporterOrbit_le (lam : N → ℝ) (hlam : ∀ a, 0 ≤ lam a) (B : N → A)
    (H K : A) (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) {T : ℝ} (hT : 0 ≤ T) :
    hausdorffDist (reporterOrbit lam B H '' Icc (-T) T) (reporterOrbit lam B K '' Icc (-T) T) ≤
      2 * T * ‖H - K‖ * ‖reporterFamily lam B‖ := by
  have hbound : ∀ t ∈ Icc (-T) T,
      dist (reporterOrbit lam B H t) (reporterOrbit lam B K t) ≤
        2 * T * ‖H - K‖ * ‖reporterFamily lam B‖ := by
    intro t ht
    rw [dist_eq_norm]
    refine le_trans (norm_reporterOrbit_sub_le lam hlam B H K hH hK t) ?_
    have habs : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    have hmul : (0 : ℝ) ≤ ‖H - K‖ * ‖reporterFamily lam B‖ := by positivity
    nlinarith [norm_nonneg (H - K), norm_nonneg (reporterFamily lam B), abs_nonneg t]
  refine hausdorffDist_le_of_mem_dist (by positivity) ?_ ?_
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨reporterOrbit lam B K t, mem_image_of_mem _ ht, hbound t ht⟩
  · rintro x ⟨t, ht, rfl⟩
    refine ⟨reporterOrbit lam B H t, mem_image_of_mem _ ht, ?_⟩
    rw [dist_comm]
    exact hbound t ht

/-- **The one-knob finite-horizon law.**  For the coupling family `H_g = H + g V` the finite-horizon
reporter orbits differ by at most `2 T |g| ‖V‖ 𝓑`, so the observation time needed to resolve a fixed
profile separation grows like `1/|g|`. -/
theorem hausdorffDist_coupledReporterOrbit_le (lam : N → ℝ) (hlam : ∀ a, 0 ≤ lam a) (B : N → A)
    (H V : A) (hH : IsSelfAdjoint H) (hV : IsSelfAdjoint V) (g : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    hausdorffDist (reporterOrbit lam B (H + g • V) '' Icc (-T) T)
        (reporterOrbit lam B H '' Icc (-T) T) ≤
      2 * T * |g| * ‖V‖ * ‖reporterFamily lam B‖ := by
  have hgV : IsSelfAdjoint (g • V) := by
    show star (g • V) = g • V
    rw [star_smul, star_trivial, hV.star_eq]
  have hHg : IsSelfAdjoint (H + g • V) := hH.add hgV
  have hdiff : ‖(H + g • V) - H‖ = |g| * ‖V‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have h := hausdorffDist_reporterOrbit_le lam hlam B (H + g • V) H hHg hH hT
  rw [hdiff] at h
  calc hausdorffDist (reporterOrbit lam B (H + g • V) '' Icc (-T) T)
        (reporterOrbit lam B H '' Icc (-T) T)
      ≤ 2 * T * (|g| * ‖V‖) * ‖reporterFamily lam B‖ := h
    _ = 2 * T * |g| * ‖V‖ * ‖reporterFamily lam B‖ := by ring

end

end GaloisForLFunctions.HTGeometry
