import GaloisForLFunctions.RHTower.XiShiftedHardEdgePolynomialGaussianCarrier
import GaloisForLFunctions.RHTower.DeningerLogSeries
import GaloisForLFunctions.HTGeometry.HermitePolynomialDerivativeEnergy

/-!
# Exponential-Schwartz certificate for the Route-U polynomial--Gaussian carrier

The complex Paley--Wiener cutoff passage needs more than ordinary Schwartz decay: its uncut
physical carrier and all derivatives must beat every real exponential.  This module proves that
property unconditionally for polynomial Gaussians, their Fourier transforms, dilations, and the
exact Route-U heat carrier.
-/

open scoped FourierTransform SchwartzMap
open Complex

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- A polynomial times the self-dual Gaussian, viewed as a complex Schwartz function, and all of
its derivatives decay faster than every exponential. -/
theorem polyGaussSchwartz_mem_deningerExpSchwartz (P : Polynomial ℝ) :
    polyGaussSchwartz P ∈ DeningerExpSchwartz := by
  intro A n
  obtain ⟨Q, hQ⟩ := exists_poly_iteratedDeriv_polyGauss P n
  let QC : Polynomial ℂ := Q.map (algebraMap ℝ ℂ)
  let S : ℝ := coeffNormSum QC
  let d : ℕ := Q.natDegree
  let B : ℝ := |A| + d
  refine ⟨S * Real.exp (B ^ 2 / (4 * Real.pi)), fun x => ?_⟩
  have hcomp :
      (fun y : ℝ => (((P.eval y * gaussReal y : ℝ) : ℂ))) =
        Complex.ofRealLI ∘ (fun y : ℝ => P.eval y * gaussReal y) := rfl
  change Real.exp (A * |x|) *
      ‖iteratedFDeriv ℝ n
        (fun y : ℝ => (((P.eval y * gaussReal y : ℝ) : ℂ))) x‖ ≤ _
  rw [hcomp, Complex.ofRealLI.norm_iteratedFDeriv_comp_left
    ((contDiff_polyGauss P (n := (n : WithTop ℕ∞))).contDiffAt) le_rfl,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, hQ x, Real.norm_eq_abs,
    abs_mul, abs_of_pos (gaussReal_pos x)]
  have hS : 0 ≤ S := coeffNormSum_nonneg QC
  have hpoly : |Q.eval x| ≤ S * (1 + |x|) ^ d := by
    have hmap : QC.eval (x : ℂ) = ((Q.eval x : ℝ) : ℂ) := by
      simpa [QC] using Polynomial.eval_map_apply
        (f := algebraMap ℝ ℂ) (p := Q) x
    have hdeg : QC.natDegree = d := by
      simpa only [QC, d] using
        Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective Q
    simpa [S, hmap, hdeg, Complex.norm_real, Real.norm_eq_abs] using
      norm_eval_le_coeffNormSum QC (x : ℂ)
  have hpow : (1 + |x|) ^ d ≤ Real.exp ((d : ℝ) * |x|) := by
    have hbase : 1 + |x| ≤ Real.exp |x| := by
      linarith [Real.add_one_le_exp (abs x)]
    calc
      (1 + |x|) ^ d ≤ (Real.exp |x|) ^ d :=
        pow_le_pow_left₀ (by positivity) hbase d
      _ = Real.exp ((d : ℝ) * |x|) := by
        exact (Real.exp_nat_mul (abs x) d).symm
  have hpoly' : |Q.eval x| ≤ S * Real.exp ((d : ℝ) * |x|) :=
    hpoly.trans (mul_le_mul_of_nonneg_left hpow hS)
  have hA : A ≤ |A| := le_abs_self A
  have hquad : B * |x| - Real.pi * x ^ 2 ≤ B ^ 2 / (4 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * Real.pi)]
    rw [← sq_abs x]
    nlinarith [sq_nonneg (2 * Real.pi * |x| - B)]
  calc
    Real.exp (A * |x|) * (|Q.eval x| * gaussReal x) ≤
        Real.exp (A * |x|) *
          (S * Real.exp ((d : ℝ) * |x|) * gaussReal x) := by
      gcongr
      exact (gaussReal_pos x).le
    _ = S * Real.exp ((A + d) * |x| - Real.pi * x ^ 2) := by
      rw [gaussReal]
      calc
        Real.exp (A * |x|) *
            (S * Real.exp ((d : ℝ) * |x|) * Real.exp (-(Real.pi * x ^ 2))) =
          S * ((Real.exp (A * |x|) * Real.exp ((d : ℝ) * |x|)) *
            Real.exp (-(Real.pi * x ^ 2))) := by ring
        _ = S * Real.exp ((A + d) * |x| - Real.pi * x ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
    _ ≤ S * Real.exp (B * |x| - Real.pi * x ^ 2) := by
      gcongr
      dsimp only [B]
      nlinarith [abs_nonneg x]
    _ ≤ S * Real.exp (B ^ 2 / (4 * Real.pi)) := by
      gcongr

/-- The Fourier transform of every polynomial Gaussian also lies in the exponential-Schwartz
source.  The proof expands the polynomial in the finite Hermite basis and uses exact Fourier
eigenfunction identities. -/
theorem fourier_polyGaussSchwartz_mem_deningerExpSchwartz (P : Polynomial ℝ) :
    FourierTransform.fourier (polyGaussSchwartz P) ∈ DeningerExpSchwartz := by
  have hdeg : P.degree < ((P.natDegree + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_self P.natDegree
  have hmem := mem_span_hermitePoly_fin_of_degree_lt (P.natDegree + 1) P hdeg
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hpoly :
      polyGaussSchwartz P =
        ∑ j : Fin (P.natDegree + 1), (c j : ℂ) • hermiteSchwartz (j : ℕ) := by
    calc
      polyGaussSchwartz P = polyGaussSchwartz
          (∑ j : Fin (P.natDegree + 1), c j • hermitePoly (j : ℕ)) :=
        congrArg _ hc.symm
      _ = _ := polyGaussSchwartz_sum_hermitePoly c
  change fourierSCLM (polyGaussSchwartz P) ∈ DeningerExpSchwartz
  rw [hpoly, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul, fourierSCLM_hermiteSchwartz]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  change polyGaussSchwartz (hermitePoly (j : ℕ)) ∈ DeningerExpSchwartz
  exact polyGaussSchwartz_mem_deningerExpSchwartz _

/-- Nonzero real dilation preserves the exponential-Schwartz source. -/
theorem schwartzDilate_mem_deningerExpSchwartz {f : SchwartzMap ℝ ℂ}
    (hf : f ∈ DeningerExpSchwartz) {c : ℝ} (hc : c ≠ 0) :
    schwartzDilate f hc ∈ DeningerExpSchwartz := by
  intro A n
  obtain ⟨C, hC⟩ := hf (A / |c|) n
  refine ⟨|c| ^ n * C, fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change Real.exp (A * |x|) *
      ‖iteratedDeriv n (fun y : ℝ => f (c * y)) x‖ ≤ _
  rw [congrFun (iteratedDeriv_comp_const_smul (f.smooth n) c) x,
    norm_smul, Real.norm_eq_abs, abs_pow]
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hexp : Real.exp (A * |x|) =
      Real.exp ((A / |c|) * |c * x|) := by
    rw [abs_mul]
    congr 1
    field_simp
  rw [hexp]
  have h := hC (c * x)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  nlinarith [pow_nonneg (abs_nonneg c) n]

/-- Fourier transform after a positive real dilation remains exponential-Schwartz whenever the
undilated Fourier transform is exponential-Schwartz. -/
theorem fourier_schwartzDilate_mem_deningerExpSchwartz {f : SchwartzMap ℝ ℂ}
    (hf : FourierTransform.fourier f ∈ DeningerExpSchwartz)
    {c : ℝ} (hc : 0 < c) :
    FourierTransform.fourier (schwartzDilate f hc.ne') ∈ DeningerExpSchwartz := by
  have heq :
      FourierTransform.fourier (schwartzDilate f hc.ne') =
        ((c : ℂ)⁻¹) • schwartzDilate (FourierTransform.fourier f)
          (inv_ne_zero hc.ne') := by
    apply SchwartzMap.ext
    intro w
    change 𝓕 (fun v : ℝ => f (c * v)) w =
      (c : ℂ)⁻¹ * 𝓕 (f : ℝ → ℂ) (c⁻¹ * w)
    rw [fourier_comp_mul_left hc]
    congr 2
    field_simp
  rw [heq]
  exact Submodule.smul_mem _ _
    (schwartzDilate_mem_deningerExpSchwartz hf (inv_ne_zero hc.ne'))

/-- Route U's rescaled heat profile belongs to the exponential-Schwartz source. -/
theorem routeUXiHeatProfileSchwartz_mem_deningerExpSchwartz
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    routeUXiHeatProfileSchwartz P t ∈ DeningerExpSchwartz := by
  exact schwartzDilate_mem_deningerExpSchwartz
    (polyGaussSchwartz_mem_deningerExpSchwartz _) _

/-- **Route-U carrier certificate.**  The exact physical polynomial--Gaussian amplitude used by
the finite-Hankel lift, including every derivative, decays faster than every exponential. -/
theorem routeUXiHeatPhysicalComplex_mem_deningerExpSchwartz
    (P : Polynomial ℝ) (t : {τ : ℝ // 0 < τ}) :
    routeUXiHeatPhysicalComplex P t ∈ DeningerExpSchwartz := by
  exact fourier_schwartzDilate_mem_deningerExpSchwartz
    (fourier_polyGaussSchwartz_mem_deningerExpSchwartz _)
    (routeUXiHeatProfileScale_pos t)

end RHTower
