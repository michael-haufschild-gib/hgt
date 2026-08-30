import GaloisForLFunctions.HTGeometry.PeriodCotangentMeroDA
import GaloisForLFunctions.HTGeometry.CotangentMeromorphicIdentification

/-!
# The period cotangent in cylinder coordinates

The order-one boundary of the multiple sine was built as a quotient of the entire solutions of the
harmonic equation of the period.  It is the same meromorphic element as the corpus's cotangent
germ, rescaled by the period:

```text
(π/ω) cot(π z/ω) = (π/ω) · cot((π/ω) z),
```

and therefore, under the cylinder embedding with coordinate `u = exp(2πi z/ω)`, it is the image of
the rational cotangent model `(iπ/ω)(X+1)/(X-1)`.

That identification is what turns the exact double-sine difference equation into an increment
lying in the two-cylinder function field, the base over which the character obstruction is proved.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance periodCotDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance periodCotComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance periodCotComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

/-! ### The two germ presentations agree -/

private theorem analyticFunctionElement_congr {f g : ℂ → ℂ} (h : ∀ z, f z = g z)
    (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ)) :
    analyticFunctionElement f hf = analyticFunctionElement g hg := by
  have hfg : f = g := funext h
  subst hfg
  rfl

theorem analyticFunctionElement_periodSin (w : ℂ) :
    analyticFunctionElement (periodSin w) (analyticOnNhd_periodSin w)
      = sinAnalytic ((Real.pi : ℂ) / w) := by
  have hfun : ∀ z : ℂ, periodSin w z = Complex.sin (((Real.pi : ℂ) / w) * z) := by
    intro z
    unfold periodSin
    congr 1
    ring
  have := analyticFunctionElement_congr hfun (analyticOnNhd_periodSin w)
    (analyticOnNhd_sin_linear ((Real.pi : ℂ) / w))
  rw [this]
  rfl

theorem analyticFunctionElement_periodCosScaled (w : ℂ) :
    analyticFunctionElement (periodCosScaled w) (analyticOnNhd_periodCosScaled w)
      = constToAnalytic (Set.univ : Set ℂ) ((Real.pi : ℂ) / w)
        * cosAnalytic ((Real.pi : ℂ) / w) := by
  apply Subtype.ext
  show Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (periodCosScaled w)
    = (constToAnalytic (Set.univ : Set ℂ) ((Real.pi : ℂ) / w) :
        analyticSubring (Set.univ : Set ℂ)) * (cosAnalytic ((Real.pi : ℂ) / w) :
        analyticSubring (Set.univ : Set ℂ))
  show Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ)) (periodCosScaled w)
    = Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ)) (fun _ : ℂ => (Real.pi : ℂ) / w) *
      Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ)) (fun z : ℂ => Complex.cos (((Real.pi : ℂ) / w) * z))
  rw [← Germ.coe_mul, Germ.coe_eq]
  refine eventually_principal.mpr fun z _ => ?_
  show periodCosScaled w z
    = ((Real.pi : ℂ) / w) * Complex.cos (((Real.pi : ℂ) / w) * z)
  unfold periodCosScaled
  congr 2
  ring

/-! ### The identification -/

/-- **The period cotangent is the corpus cotangent germ, rescaled.** -/
theorem periodCotMero_eq_cotMero (w : ℂ) :
    periodCotMero w
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((Real.pi : ℂ) / w)
        * cotMero ((Real.pi : ℂ) / w) := by
  rw [periodCotMero, analyticMeroElement, analyticMeroElement,
    analyticFunctionElement_periodSin, analyticFunctionElement_periodCosScaled, map_mul, cotMero]
  have hconst : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic (Set.univ : Set ℂ) ((Real.pi : ℂ) / w))
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((Real.pi : ℂ) / w) := rfl
  rw [hconst, mul_div_assoc]

/-- **The period cotangent is the embedded rational cotangent model.**  Under the cylinder
embedding with coordinate `u = exp(2πi z/ω)`, the order-one multiple-sine boundary is the image of
`(iπ/ω)(X+1)/(X-1)`. -/
theorem periodCotMero_eq_cylinderEmbed {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) (j : Fin 2)
    {w : ℂ} (hw : w ≠ 0) (hlj : l j = 2 * (Real.pi : ℂ) * Complex.I / w) :
    periodCotMero w = cylinderEmbed hl j (cotModel ((Real.pi : ℂ) / w * Complex.I)) := by
  rw [cylinderEmbed_cotModel_period hl j hw hlj, periodCotMero_eq_cotMero]

end

end GaloisForLFunctions.HTGeometry
