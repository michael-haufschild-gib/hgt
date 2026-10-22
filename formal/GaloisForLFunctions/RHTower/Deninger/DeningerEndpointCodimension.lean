import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerRadialEndpoints
import GaloisForLFunctions.HTGeometry.HermiteFourierEigen

/-!
# The two endpoint maps are the only boundary data

Meyer's space is the common kernel of evaluation at the origin and evaluation of the Fourier
transform at the origin on the even Schwartz functions.  The two functionals are independent: the
Hermite functions `h₀` and `h₂` are even, do not vanish at the origin, and are Fourier
eigenfunctions with the opposite eigenvalues `+1` and `−1`, so already their span realizes every
pair of endpoint values.  Consequently the pair of endpoint maps is a surjection of the even
Schwartz functions onto `ℂ²` with kernel exactly Meyer's space, which therefore has codimension
exactly two.  No further boundary functional survives.

* `hermitePoly_two_eval_zero`, `hermiteSchwartz_two_zero_ne_zero` : the second Hermite function
  does not vanish at the origin.
* `exists_even_endpoint_values` : **every pair of endpoint values is realized by an even Schwartz
  function.**
* `deningerEndpointPair`, `deningerEndpointPair_surjective`, `ker_deningerEndpointPair` : the pair
  of endpoint maps, its surjectivity, and its kernel.
* `deningerEndpointQuotientEquiv`, `deningerMeyerCap_finrank_quotient` : **Meyer's space has
  codimension exactly two in the even Schwartz functions.**
-/

open scoped Real SchwartzMap
open Complex GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## Two even Hermite functions with opposite Fourier eigenvalue -/

theorem hermitePoly_two_eval_zero : (hermitePoly 2).eval 0 = -(1 / π) := by
  show (hermiteStep (hermiteStep (hermitePoly 0))).eval 0 = _
  rw [hermitePoly_zero]
  simp [hermiteStep]

theorem hermiteSchwartz_zero_zero_ne_zero : hermiteSchwartz 0 0 ≠ 0 := by
  rw [hermiteSchwartz_zero, gaussianSchwartz_apply]
  exact Complex.ofReal_ne_zero.mpr (gaussReal_pos 0).ne'

theorem hermiteSchwartz_two_zero_ne_zero : hermiteSchwartz 2 0 ≠ 0 := by
  rw [hermiteSchwartz_apply, hermitePoly_two_eval_zero]
  refine Complex.ofReal_ne_zero.mpr (mul_ne_zero ?_ (gaussReal_pos 0).ne')
  simp

/-! ## The endpoint values of the Hermite functions -/

theorem deningerSchwartzEval_zero_hermiteSchwartz (n : ℕ) :
    deningerSchwartzEval 0 (hermiteSchwartz n) = hermiteSchwartz n 0 :=
  deningerSchwartzEval_apply 0 _

theorem deningerFourierEval_hermiteSchwartz (n : ℕ) :
    deningerFourierEval (hermiteSchwartz n) = (-I) ^ n * hermiteSchwartz n 0 := by
  rw [deningerFourierEval_apply, FourierTransform.fourierCLE_apply, ← fourierSCLM_eq,
    fourierSCLM_hermiteSchwartz, _root_.smul_apply, smul_eq_mul]

/-! ## Both endpoint values are free -/

/-- **Every pair of endpoint values is realized by an even Schwartz function.**  The Hermite
functions `h₀` and `h₂` are even with Fourier eigenvalues `+1` and `−1`, so the two endpoint
functionals take independent values on their span. -/
theorem exists_even_endpoint_values (z w : ℂ) :
    ∃ f ∈ deningerEvenSchwartz,
      deningerSchwartzEval 0 f = z ∧ deningerFourierEval f = w := by
  have hg : hermiteSchwartz 0 0 ≠ 0 := hermiteSchwartz_zero_zero_ne_zero
  have hc : hermiteSchwartz 2 0 ≠ 0 := hermiteSchwartz_two_zero_ne_zero
  set a : ℂ := (z + w) / (2 * hermiteSchwartz 0 0) with ha
  set b : ℂ := (z - w) / (2 * hermiteSchwartz 2 0) with hb
  refine ⟨a • hermiteSchwartz 0 + b • hermiteSchwartz 2, ?_, ?_, ?_⟩
  · refine (deningerEvenSchwartz_mem_iff _).mpr fun x => ?_
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    have h0 : hermiteSchwartz 0 (-x) = hermiteSchwartz 0 x := by
      have := hermiteSchwartz_even 0 x
      simpa using this
    have h2 : hermiteSchwartz 2 (-x) = hermiteSchwartz 2 x := by
      have := hermiteSchwartz_even 1 x
      simpa using this
    rw [h0, h2]
  · rw [map_add, map_smul, map_smul, deningerSchwartzEval_zero_hermiteSchwartz,
      deningerSchwartzEval_zero_hermiteSchwartz, smul_eq_mul, smul_eq_mul, ha, hb]
    field_simp
    ring
  · rw [map_add, map_smul, map_smul, deningerFourierEval_hermiteSchwartz,
      deningerFourierEval_hermiteSchwartz, smul_eq_mul, smul_eq_mul, ha, hb]
    have hI : (-I) ^ (2 : ℕ) = -1 := by
      rw [pow_two, neg_mul_neg, Complex.I_mul_I]
    rw [pow_zero, hI, one_mul]
    field_simp
    ring

/-! ## The pair of endpoint maps -/

/-- The pair of endpoint maps of `(10)`, restricted to the even Schwartz functions. -/
def deningerEndpointPair : deningerEvenSchwartz →ₗ[ℂ] ℂ × ℂ :=
  ((deningerSchwartzEval 0 : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ).prod
      (deningerFourierEval : 𝓢(ℝ, ℂ) →ₗ[ℂ] ℂ)).comp deningerEvenSchwartz.subtype

theorem deningerEndpointPair_apply (f : deningerEvenSchwartz) :
    deningerEndpointPair f
      = (deningerSchwartzEval 0 (f : 𝓢(ℝ, ℂ)), deningerFourierEval (f : 𝓢(ℝ, ℂ))) := rfl

/-- **The pair of endpoint maps is surjective** onto `ℂ²`. -/
theorem deningerEndpointPair_surjective : Function.Surjective deningerEndpointPair := by
  rintro ⟨z, w⟩
  obtain ⟨f, hf, h1, h2⟩ := exists_even_endpoint_values z w
  refine ⟨⟨f, hf⟩, ?_⟩
  rw [deningerEndpointPair_apply]
  exact Prod.ext h1 h2

/-- **Meyer's space is exactly the kernel of the pair of endpoint maps** inside the even Schwartz
functions. -/
theorem ker_deningerEndpointPair :
    LinearMap.ker deningerEndpointPair
      = DeningerMeyerCap.comap deningerEvenSchwartz.subtype := by
  refine Submodule.ext fun f => ?_
  rw [LinearMap.mem_ker, Submodule.mem_comap, deningerEndpointPair_apply, Prod.ext_iff,
    deningerMeyerCap_mem_iff]
  simp only [Prod.fst_zero, Prod.snd_zero, deningerSchwartzEval_apply,
    deningerFourierEval_apply, Submodule.subtype_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(deningerEvenSchwartz_mem_iff _).mp f.2, h1, h2⟩
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

/-! ## Codimension two -/

/-- **The two endpoint maps carry the whole quotient**: the even Schwartz functions modulo Meyer's
space are the pair of endpoint values. -/
def deningerEndpointQuotientEquiv :
    (deningerEvenSchwartz ⧸ DeningerMeyerCap.comap deningerEvenSchwartz.subtype) ≃ₗ[ℂ] ℂ × ℂ :=
  (Submodule.quotEquivOfEq _ _ ker_deningerEndpointPair.symm).trans
    (deningerEndpointPair.quotKerEquivOfSurjective deningerEndpointPair_surjective)

/-- **Meyer's space has codimension exactly two in the even Schwartz functions.**  No boundary
functional beyond the two endpoint maps of `(10)` survives. -/
theorem deningerMeyerCap_finrank_quotient :
    Module.finrank ℂ
        (deningerEvenSchwartz ⧸ DeningerMeyerCap.comap deningerEvenSchwartz.subtype) = 2 := by
  rw [deningerEndpointQuotientEquiv.finrank_eq]
  simp

end RHTower

end
