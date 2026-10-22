import GaloisForLFunctions.RHTower.Deninger.DeningerPhaseGenerator

/-!
# The absolute value of the phase generator

For a diagonal operator the absolute value is the diagonal of the absolute values: it has the same
maximal domain, because the coordinates have the same moduli, it is self-adjoint, and the
characters are eigenvectors with the absolute frequencies as eigenvalues.

The sign of the frequency is a unimodular multiplier, and multiplying the absolute value by it
returns the generator: this is the polar decomposition of the phase generator, valid coordinate by
coordinate including at zero frequency.

* `deningerAbsGenerator` : the absolute value of the generator.
* `deningerAbsGenerator_domain_eq` : it has the same maximal domain.
* `deningerAbsGenerator_apply_basis` : the characters are eigenvectors of the absolute values.
* `deningerPolarDecomposition` : the sign multiplier times the absolute value is the generator.
-/

namespace RHTower

open HilbertSchmidt

noncomputable section

universe u

variable {ι : Type u} [DecidableEq ι]

/-- **The sign times the absolute value is the frequency**, at every frequency including zero. -/
theorem deningerFreqSign_mul_abs' (μ : ℝ) : deningerFreqSign μ * |μ| = μ := by
  by_cases hμ : μ = 0
  · rw [hμ]
    simp
  · exact deningerFreqSign_mul_abs hμ

/-- **The absolute value of the phase generator**: the diagonal of the absolute frequencies. -/
def deningerAbsGenerator (ℓ : ι → ℝ) : DiagonalL2 ι →ₗ.[ℂ] DiagonalL2 ι :=
  maximalRealDiagonal fun i => |ℓ i|

omit [DecidableEq ι] in
/-- **The absolute value has the same maximal domain**, because the coordinates have the same
moduli. -/
theorem deningerAbsGenerator_domain_eq (ℓ : ι → ℝ) :
    (deningerAbsGenerator ℓ).domain = (deningerPhaseGenerator ℓ).domain := by
  refine Submodule.ext fun x => ?_
  have hnorm : ∀ i : ι, ‖((|ℓ i| : ℝ) : ℂ) * (x : ι → ℂ) i‖ = ‖((ℓ i : ℝ) : ℂ) * (x : ι → ℂ) i‖ := by
    intro i
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_abs]
  constructor
  · intro hx
    have hx' : Memℓp (fun i => ((|ℓ i| : ℝ) : ℂ) * (x : ι → ℂ) i) 2 := hx
    have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    refine memℓp_gen ?_
    exact (hx'.summable htwo).congr fun i => by rw [hnorm i]
  · intro hx
    have hx' : Memℓp (fun i => ((ℓ i : ℝ) : ℂ) * (x : ι → ℂ) i) 2 := hx
    have htwo : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    refine memℓp_gen ?_
    exact (hx'.summable htwo).congr fun i => by rw [← hnorm i]

/-- **The characters are eigenvectors of the absolute value.** -/
theorem deningerAbsGenerator_apply_basis (ℓ : ι → ℝ) (i : ι) :
    deningerAbsGenerator ℓ ⟨lpBasis ι i, lpBasis_mem_maximalRealDiagonalDomain _ i⟩
      = ((|ℓ i| : ℝ) : ℂ) • lpBasis ι i := by
  refine lp.ext ?_
  funext j
  show ((|ℓ j| : ℝ) : ℂ) * (lpBasis ι i) j = ((|ℓ i| : ℝ) : ℂ) * (lpBasis ι i) j
  by_cases hji : j = i
  · rw [hji]
  · rw [lpBasis_apply, lp.single_apply_ne _ _ _ hji]
    simp

/-- **The absolute value is self-adjoint on its maximal domain.** -/
theorem deningerAbsGenerator_isSelfAdjoint (ℓ : ι → ℝ) :
    IsSelfAdjoint (deningerAbsGenerator ℓ) :=
  maximalRealDiagonal_isSelfAdjoint _

/-- The unimodular sign family of the frequency. -/
def deningerRealSignFamily (ℓ : ι → ℝ) (i : ι) : ℂ := ((deningerFreqSign (ℓ i) : ℝ) : ℂ)

omit [DecidableEq ι] in
theorem deningerRealSignFamily_norm_le (ℓ : ι → ℝ) (i : ι) :
    ‖deningerRealSignFamily ℓ i‖ ≤ 1 := by
  rw [deningerRealSignFamily, Complex.norm_real, Real.norm_eq_abs, deningerFreqSign]
  split_ifs <;> norm_num

/-- The sign multiplier of the frequency, as a contraction. -/
def deningerSignOperator (ℓ : ι → ℝ) : DiagonalL2 ι →L[ℂ] DiagonalL2 ι :=
  deningerMultiplier (deningerRealSignFamily_norm_le ℓ)

omit [DecidableEq ι] in
/-- **The polar decomposition of the phase generator.**  The sign multiplier applied to the
absolute value returns the generator, coordinate by coordinate, including at zero frequency. -/
theorem deningerPolarDecomposition (ℓ : ι → ℝ) (x : DiagonalL2 ι)
    (hx : x ∈ (deningerPhaseGenerator ℓ).domain)
    (hx' : x ∈ (deningerAbsGenerator ℓ).domain) :
    deningerSignOperator ℓ (deningerAbsGenerator ℓ ⟨x, hx'⟩)
      = deningerPhaseGenerator ℓ ⟨x, hx⟩ := by
  refine lp.ext ?_
  funext i
  show deningerRealSignFamily ℓ i * (((|ℓ i| : ℝ) : ℂ) * (x : ι → ℂ) i)
    = ((ℓ i : ℝ) : ℂ) * (x : ι → ℂ) i
  rw [deningerRealSignFamily, ← mul_assoc]
  congr 1
  exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (deningerFreqSign_mul_abs' (ℓ i))

end

end RHTower
