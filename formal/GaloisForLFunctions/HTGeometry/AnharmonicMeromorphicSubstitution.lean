import GaloisForLFunctions.HTGeometry.MeromorphicReflection
import GaloisForLFunctions.HTGeometry.AnharmonicRatFunc
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.MobiusJetTransfer
import GaloisForLFunctions.HTGeometry.MeromorphicRatFuncTranslation
import GaloisForLFunctions.HTGeometry.LocalInverseHypertranscendence

/-!
# The anharmonic substitution of the meromorphic differential field

The Möbius transformation `r z = 1/(1-z)` has order three and permutes the three points
`0, 1, ∞`.  It therefore restricts to an analytic automorphism of the twice-punctured plane
`ℂ ∖ {0,1}`, whose inverse is `r² z = 1 - 1/z`.

Precomposition with `r` is a field automorphism of the meromorphic function field of that domain.
It does not commute with differentiation: the chain rule inserts the factor `r'(z) = (1-z)⁻²`.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Bottcher

noncomputable section

/-! ## The twice-punctured plane -/

/-- The plane with the two finite points of the anharmonic orbit removed. -/
def anharmonicDomain : Set ℂ := ({0, 1} : Set ℂ)ᶜ

theorem mem_anharmonicDomain {z : ℂ} : z ∈ anharmonicDomain ↔ z ≠ 0 ∧ z ≠ 1 := by
  simp [anharmonicDomain, not_or]

theorem anharmonicDomain_isOpen : IsOpen anharmonicDomain :=
  ((Set.toFinite ({0, 1} : Set ℂ)).isClosed).isOpen_compl

theorem anharmonicDomain_isPreconnected : IsPreconnected anharmonicDomain :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (E := ℂ) (by simp)
    ((Set.countable_singleton (1 : ℂ)).insert 0)).isPreconnected

theorem anharmonicDomain_nonempty : anharmonicDomain.Nonempty :=
  ⟨2, mem_anharmonicDomain.mpr ⟨by norm_num, by norm_num⟩⟩

theorem anharmonicDomain_infinite : anharmonicDomain.Infinite := by
  refine Set.Infinite.mono (s := (Set.range fun n : ℕ => (n : ℂ) + 2)) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    refine mem_anharmonicDomain.mpr ⟨?_, ?_⟩
    · intro h
      have := congrArg Complex.re h
      simp at this
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · intro h
      have := congrArg Complex.re h
      simp at this
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  · refine Set.infinite_range_of_injective ?_
    intro a b hab
    have : (a : ℂ) = (b : ℂ) := by linear_combination hab
    exact_mod_cast this

/-! ## The order-three Möbius map -/

/-- The anharmonic substitution `r z = 1/(1-z)`. -/
def anharmonicMap : ℂ → ℂ := fun z => (1 - z)⁻¹

/-- Its inverse `r² z = 1 - 1/z`. -/
def anharmonicMapInv : ℂ → ℂ := fun z => 1 - z⁻¹

/-- The derivative factor `r'(z) = (1-z)⁻²`. -/
def anharmonicFactorFun : ℂ → ℂ := fun z => ((1 - z) ^ 2)⁻¹

theorem one_sub_ne_zero_of_mem {z : ℂ} (hz : z ∈ anharmonicDomain) : (1 : ℂ) - z ≠ 0 := by
  intro h
  exact (mem_anharmonicDomain.mp hz).2 (by linear_combination -h)

theorem ne_zero_of_mem {z : ℂ} (hz : z ∈ anharmonicDomain) : z ≠ 0 :=
  (mem_anharmonicDomain.mp hz).1

theorem anharmonicMap_mapsTo : Set.MapsTo anharmonicMap anharmonicDomain anharmonicDomain := by
  intro z hz
  have h1 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem hz
  refine mem_anharmonicDomain.mpr ⟨?_, ?_⟩
  · exact inv_ne_zero h1
  · intro h
    simp only [anharmonicMap] at h
    have h2 : (1 - z) * (1 - z)⁻¹ = (1 - z) * 1 := by rw [h]
    rw [mul_inv_cancel₀ h1, mul_one] at h2
    exact (mem_anharmonicDomain.mp hz).1 (by linear_combination h2)

theorem anharmonicMapInv_mapsTo :
    Set.MapsTo anharmonicMapInv anharmonicDomain anharmonicDomain := by
  intro z hz
  have h0 : z ≠ 0 := ne_zero_of_mem hz
  refine mem_anharmonicDomain.mpr ⟨?_, ?_⟩
  · intro h
    simp only [anharmonicMapInv] at h
    have hinv : z⁻¹ = 1 := by linear_combination -h
    have h2 : z * z⁻¹ = z * 1 := by rw [hinv]
    rw [mul_inv_cancel₀ h0, mul_one] at h2
    exact (mem_anharmonicDomain.mp hz).2 h2.symm
  · intro h
    simp only [anharmonicMapInv] at h
    have hz0 : z⁻¹ = 0 := by linear_combination -h
    exact h0 (inv_eq_zero.mp hz0)

theorem anharmonicMap_comp_inv :
    Set.EqOn (anharmonicMap ∘ anharmonicMapInv) id anharmonicDomain := by
  intro z hz
  have h0 : z ≠ 0 := ne_zero_of_mem hz
  simp only [Function.comp_apply, anharmonicMap, anharmonicMapInv, id_eq]
  rw [show (1 : ℂ) - (1 - z⁻¹) = z⁻¹ by ring, inv_inv]

theorem anharmonicMapInv_comp :
    Set.EqOn (anharmonicMapInv ∘ anharmonicMap) id anharmonicDomain := by
  intro z hz
  have h1 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem hz
  simp only [Function.comp_apply, anharmonicMap, anharmonicMapInv, id_eq]
  rw [inv_inv]
  ring

theorem analyticOnNhd_anharmonicMap :
    AnalyticOnNhd ℂ anharmonicMap anharmonicDomain :=
  (analyticOnNhd_const.sub analyticOnNhd_id).inv
    (fun _ hz => one_sub_ne_zero_of_mem hz)

theorem analyticOnNhd_anharmonicMapInv :
    AnalyticOnNhd ℂ anharmonicMapInv anharmonicDomain :=
  analyticOnNhd_const.sub (analyticOnNhd_id.inv (fun _ hz => ne_zero_of_mem hz))

theorem analyticOnNhd_anharmonicFactorFun :
    AnalyticOnNhd ℂ anharmonicFactorFun anharmonicDomain :=
  ((analyticOnNhd_const.sub analyticOnNhd_id).pow 2).inv
    (fun _ hz => pow_ne_zero _ (one_sub_ne_zero_of_mem hz))

theorem deriv_anharmonicMap {z : ℂ} (hz : z ∈ anharmonicDomain) :
    deriv anharmonicMap z = anharmonicFactorFun z := by
  have h1 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem hz
  have hd : HasDerivAt (fun w : ℂ => 1 - w) (-1) z :=
    HasDerivAt.const_sub (1 : ℂ) (hasDerivAt_id z)
  have hinv : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) (-(-1) / (1 - z) ^ 2) z := hd.inv h1
  rw [(show anharmonicMap = fun w : ℂ => (1 - w)⁻¹ from rfl), hinv.deriv]
  simp only [anharmonicFactorFun]
  field_simp

/-! ## The substitution automorphism of the meromorphic field -/

/-- Precomposition with the anharmonic map on the analytic germs of the twice-punctured plane. -/
def anharmonicAnalyticEquiv :
    analyticSubring anharmonicDomain ≃+* analyticSubring anharmonicDomain :=
  precompAnalyticEquiv analyticOnNhd_anharmonicMap analyticOnNhd_anharmonicMapInv
    anharmonicMap_mapsTo anharmonicMapInv_mapsTo anharmonicMap_comp_inv anharmonicMapInv_comp

/-- Precomposition with the anharmonic map on the meromorphic function field. -/
def anharmonicMeroEquiv : meroField anharmonicDomain ≃+* meroField anharmonicDomain :=
  precompMeroEquiv analyticOnNhd_anharmonicMap analyticOnNhd_anharmonicMapInv
    anharmonicMap_mapsTo anharmonicMapInv_mapsTo anharmonicMap_comp_inv anharmonicMapInv_comp
    anharmonicDomain_isOpen anharmonicDomain_isPreconnected anharmonicDomain_nonempty

theorem anharmonicMeroEquiv_algebraMap (a : analyticSubring anharmonicDomain) :
    letI := Bottcher.isDomain_analyticSubring anharmonicDomain anharmonicDomain_isOpen
      anharmonicDomain_isPreconnected anharmonicDomain_nonempty
    anharmonicMeroEquiv
        (algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain) a)
      = algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
          (anharmonicAnalyticEquiv a) := by
  letI := Bottcher.isDomain_analyticSubring anharmonicDomain anharmonicDomain_isOpen
    anharmonicDomain_isPreconnected anharmonicDomain_nonempty
  exact precompMeroEquiv_algebraMap analyticOnNhd_anharmonicMap analyticOnNhd_anharmonicMapInv
    anharmonicMap_mapsTo anharmonicMapInv_mapsTo anharmonicMap_comp_inv anharmonicMapInv_comp
    anharmonicDomain_isOpen anharmonicDomain_isPreconnected anharmonicDomain_nonempty a

/-- The derivative factor `(1-z)⁻²` as an analytic germ. -/
def anharmonicFactorElement : analyticSubring anharmonicDomain :=
  analyticFunctionElement anharmonicFactorFun analyticOnNhd_anharmonicFactorFun

/-- **The chain rule on analytic germs.**  Differentiating after the anharmonic substitution
multiplies by `r'(z) = (1-z)⁻²`. -/
theorem anharmonicAnalyticEquiv_deriv (a : analyticSubring anharmonicDomain) :
    analyticSubringDeriv anharmonicDomain_isOpen (anharmonicAnalyticEquiv a)
      = anharmonicFactorElement *
        anharmonicAnalyticEquiv (analyticSubringDeriv anharmonicDomain_isOpen a) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  let htr : Tendsto anharmonicMap (𝓟 anharmonicDomain) (𝓟 anharmonicDomain) :=
    tendsto_principal_principal.mpr anharmonicMap_mapsTo
  change analyticGermDeriv anharmonicDomain_isOpen
      ((a : Germ (𝓟 anharmonicDomain) ℂ).compTendsto anharmonicMap htr)
    = (anharmonicFactorFun : Germ (𝓟 anharmonicDomain) ℂ) *
      (analyticGermDeriv anharmonicDomain_isOpen
        (a : Germ (𝓟 anharmonicDomain) ℂ)).compTendsto anharmonicMap htr
  rw [← hfa]
  change (Germ.ofFun (l := 𝓟 anharmonicDomain) (deriv (fun z => f (anharmonicMap z)))) =
    (Germ.ofFun (l := 𝓟 anharmonicDomain) anharmonicFactorFun) *
      (Germ.ofFun (l := 𝓟 anharmonicDomain) (fun z => deriv f (anharmonicMap z)))
  rw [← Germ.coe_mul, Germ.coe_eq]
  refine eventually_principal.mpr fun z hz => ?_
  have hrz : anharmonicMap z ∈ anharmonicDomain := anharmonicMap_mapsTo hz
  have hdf : DifferentiableAt ℂ f (anharmonicMap z) := (hf _ hrz).differentiableAt
  have hdr : DifferentiableAt ℂ anharmonicMap z :=
    (analyticOnNhd_anharmonicMap z hz).differentiableAt
  have hchain := deriv_comp (h₂ := f) (h := anharmonicMap) z hdf hdr
  simp only [Pi.mul_apply]
  rw [show (fun z => f (anharmonicMap z)) = f ∘ anharmonicMap from rfl, hchain,
    deriv_anharmonicMap hz]
  ring

/-- **The chain rule on the meromorphic field.**  The anharmonic substitution is a field
automorphism which rescales the derivation by the analytic germ of `r'`. -/
theorem anharmonicMeroEquiv_deriv (x : meroField anharmonicDomain) :
    letI := Bottcher.isDomain_analyticSubring anharmonicDomain anharmonicDomain_isOpen
      anharmonicDomain_isPreconnected anharmonicDomain_nonempty
    letI := meroFieldDifferential anharmonicDomain_isOpen anharmonicDomain_isPreconnected
      anharmonicDomain_nonempty
    (anharmonicMeroEquiv x)′
      = algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
          anharmonicFactorElement * anharmonicMeroEquiv (x′) := by
  let A := analyticSubring anharmonicDomain
  let F := meroField anharmonicDomain
  letI hdom := Bottcher.isDomain_analyticSubring anharmonicDomain anharmonicDomain_isOpen
    anharmonicDomain_isPreconnected anharmonicDomain_nonempty
  letI : Algebra ℤ A := Ring.toIntAlgebra _
  letI : Algebra ℤ F := Ring.toIntAlgebra _
  letI hdiff := meroFieldDifferential anharmonicDomain_isOpen anharmonicDomain_isPreconnected
    anharmonicDomain_nonempty
  let sigmaA : A ≃+* A := anharmonicAnalyticEquiv
  let sigmaF : F ≃+* F := anharmonicMeroEquiv
  let w : F := algebraMap A F anharmonicFactorElement
  have hDc : (Differential.equiv sigmaF : Differential F).deriv
      = (sigmaF.symm w) • (Differential.deriv : Derivation ℤ F F) := by
    apply fractionRing_derivation_ext (A := A) (F := F)
    intro a
    change sigmaF.symm (Differential.deriv (sigmaF (algebraMap A F a)))
      = sigmaF.symm w * Differential.deriv (algebraMap A F a)
    have hsigma : sigmaF (algebraMap A F a) = algebraMap A F (sigmaA a) :=
      anharmonicMeroEquiv_algebraMap a
    rw [hsigma, meroFieldDifferential_algebraMap, meroFieldDifferential_algebraMap,
      anharmonicAnalyticEquiv_deriv a, map_mul]
    have hback : sigmaF (algebraMap A F (analyticSubringDeriv anharmonicDomain_isOpen a))
        = algebraMap A F (sigmaA (analyticSubringDeriv anharmonicDomain_isOpen a)) :=
      anharmonicMeroEquiv_algebraMap _
    rw [← hback, map_mul, RingEquiv.symm_apply_apply]
  have hx := Derivation.congr_fun hDc x
  change sigmaF.symm (Differential.deriv (sigmaF x)) = sigmaF.symm w * Differential.deriv x at hx
  have h := congrArg sigmaF hx
  rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply] at h
  exact h

/-! ## The rational coordinate field as a differential base -/

local instance anharmonicIsDomain : IsDomain (analyticSubring anharmonicDomain) :=
  Bottcher.isDomain_analyticSubring anharmonicDomain anharmonicDomain_isOpen
    anharmonicDomain_isPreconnected anharmonicDomain_nonempty

local instance anharmonicIntAlgebraAnalytic : Algebra ℤ (analyticSubring anharmonicDomain) :=
  Ring.toIntAlgebra _

local instance anharmonicIntAlgebraMero : Algebra ℤ (meroField anharmonicDomain) :=
  Ring.toIntAlgebra _

local instance anharmonicMeroDifferential : Differential (meroField anharmonicDomain) :=
  meroFieldDifferential anharmonicDomain_isOpen anharmonicDomain_isPreconnected
    anharmonicDomain_nonempty

/-- The embedding of the rational coordinate field into the anharmonic meromorphic field. -/
@[reducible] def anharmonicRatfuncToMero : RatFunc ℂ →+* meroField anharmonicDomain :=
  ratfuncToMero anharmonicDomain anharmonicDomain_isOpen anharmonicDomain_isPreconnected
    anharmonicDomain_nonempty anharmonicDomain_infinite

local instance anharmonicRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField anharmonicDomain) :=
  anharmonicRatfuncToMero.toAlgebra

local instance anharmonicRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

theorem analyticSubringDeriv_polyToAnalytic_anharmonic (p : Polynomial ℂ) :
    analyticSubringDeriv anharmonicDomain_isOpen (polyToAnalytic anharmonicDomain p) =
      polyToAnalytic anharmonicDomain p.derivative := by
  apply Subtype.ext
  change Germ.ofFun (l := 𝓟 anharmonicDomain) (deriv (fun z : ℂ => p.eval z)) =
    Germ.ofFun (l := 𝓟 anharmonicDomain) (fun z : ℂ => p.derivative.eval z)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => Polynomial.deriv p

theorem meroField_deriv_polyToMero_anharmonic (p : Polynomial ℂ) :
    (polyToMero anharmonicDomain p)′ = polyToMero anharmonicDomain p.derivative := by
  change (algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
    (polyToAnalytic anharmonicDomain p))′ = _
  rw [meroFieldDifferential_algebraMap anharmonicDomain_isOpen anharmonicDomain_isPreconnected
    anharmonicDomain_nonempty, analyticSubringDeriv_polyToAnalytic_anharmonic]
  rfl

theorem anharmonicRatfuncToMero_algebraMap_polynomial (p : Polynomial ℂ) :
    anharmonicRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = polyToMero anharmonicDomain p :=
  ratfuncToMero_algebraMap_polynomial anharmonicDomain anharmonicDomain_isOpen
    anharmonicDomain_isPreconnected anharmonicDomain_nonempty anharmonicDomain_infinite p

/-- The meromorphic derivation of the twice-punctured plane restricts to the rational coordinate
derivation on `ℂ(z)`. -/
theorem anharmonic_deriv_ratfuncToMero (r : RatFunc ℂ) :
    (anharmonicRatfuncToMero r)′
      = anharmonicRatfuncToMero (HTGeometry.ratFuncCoordinateDerivation ℂ r) := by
  induction r using RatFunc.induction_on with
  | f p q hq =>
      let pR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      let qR : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) q
      change (anharmonicRatfuncToMero (pR / qR))′ =
        anharmonicRatfuncToMero (HTGeometry.ratFuncCoordinateDerivation ℂ (pR / qR))
      rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div]
      simp only [map_mul, map_sub, map_pow, map_inv₀, smul_eq_mul]
      rw [show anharmonicRatfuncToMero pR = polyToMero anharmonicDomain p from
            anharmonicRatfuncToMero_algebraMap_polynomial p,
        show anharmonicRatfuncToMero qR = polyToMero anharmonicDomain q from
            anharmonicRatfuncToMero_algebraMap_polynomial q]
      rw [meroField_deriv_polyToMero_anharmonic, meroField_deriv_polyToMero_anharmonic]
      rw [show HTGeometry.ratFuncCoordinateDerivation ℂ pR =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative by simp [pR],
        show HTGeometry.ratFuncCoordinateDerivation ℂ qR =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative by simp [qR]]
      rw [show anharmonicRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) p.derivative) =
            polyToMero anharmonicDomain p.derivative from
            anharmonicRatfuncToMero_algebraMap_polynomial p.derivative,
        show anharmonicRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) q.derivative) =
            polyToMero anharmonicDomain q.derivative from
            anharmonicRatfuncToMero_algebraMap_polynomial q.derivative]

local instance anharmonicDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField anharmonicDomain) :=
  { deriv_algebraMap := fun r => anharmonic_deriv_ratfuncToMero r }

/-! ## Compatibility with the rational coordinate substitution -/

/-- The coordinate germ, substituted, is the germ of the anharmonic map. -/
theorem anharmonicAnalyticEquiv_coordinate :
    anharmonicAnalyticEquiv (polyToAnalytic anharmonicDomain Polynomial.X)
      = analyticFunctionElement anharmonicMap analyticOnNhd_anharmonicMap := by
  apply Subtype.ext
  change Germ.ofFun (l := 𝓟 anharmonicDomain)
      (fun z : ℂ => (Polynomial.X : Polynomial ℂ).eval (anharmonicMap z))
    = Germ.ofFun (l := 𝓟 anharmonicDomain) anharmonicMap
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by simp

/-- The germ of the anharmonic map is the image of the rational function `1/(1-z)`. -/
theorem anharmonicRatfuncToMero_anharmonicRatFunc :
    anharmonicRatfuncToMero anharmonicRatFunc
      = algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
          (analyticFunctionElement anharmonicMap analyticOnNhd_anharmonicMap) := by
  have honeSub : analyticFunctionElement anharmonicMap analyticOnNhd_anharmonicMap
      * (1 - polyToAnalytic anharmonicDomain Polynomial.X) = 1 := by
    apply Subtype.ext
    change Germ.ofFun (l := 𝓟 anharmonicDomain) anharmonicMap
        * (1 - Germ.ofFun (l := 𝓟 anharmonicDomain)
            (fun z : ℂ => (Polynomial.X : Polynomial ℂ).eval z)) = 1
    have hone : (1 : Germ (𝓟 anharmonicDomain) ℂ)
        = Germ.ofFun (l := 𝓟 anharmonicDomain) (fun _ : ℂ => (1 : ℂ)) := rfl
    rw [hone, ← Germ.coe_sub, ← Germ.coe_mul, Germ.coe_eq]
    refine eventually_principal.mpr fun z hz => ?_
    have h1 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem hz
    simp only [Pi.sub_apply, Pi.mul_apply, anharmonicMap, Polynomial.eval_X]
    field_simp
  have hXrf : anharmonicRatfuncToMero (1 - RatFunc.X)
      = algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
          (1 - polyToAnalytic anharmonicDomain Polynomial.X) := by
    rw [map_sub, map_one, ← RatFunc.algebraMap_X,
      anharmonicRatfuncToMero_algebraMap_polynomial]
    rw [map_sub, map_one]
    rfl
  have hmul : anharmonicRatfuncToMero anharmonicRatFunc
      * anharmonicRatfuncToMero (1 - RatFunc.X) = 1 := by
    rw [← map_mul]
    rw [show anharmonicRatFunc * (1 - RatFunc.X) = 1 by
      rw [anharmonicRatFunc, inv_mul_cancel₀]
      intro h
      have : (RatFunc.X : RatFunc ℂ) = 1 := by linear_combination -h
      exact RatFunc.transcendental_X (this ▸ isAlgebraic_one)]
    exact map_one _
  rw [hXrf] at hmul
  have hmul2 : algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
      (analyticFunctionElement anharmonicMap analyticOnNhd_anharmonicMap)
      * algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
        (1 - polyToAnalytic anharmonicDomain Polynomial.X) = 1 := by
    rw [← map_mul, honeSub, map_one]
  have hne : algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
      (1 - polyToAnalytic anharmonicDomain Polynomial.X) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul2
    exact one_ne_zero hmul2.symm
  exact mul_right_cancel₀ hne (hmul.trans hmul2.symm)

/-- **The substitution restricts to the anharmonic substitution of `ℂ(z)`.** -/
theorem anharmonicMeroEquiv_ratfuncToMero (r : RatFunc ℂ) :
    anharmonicMeroEquiv (anharmonicRatfuncToMero r)
      = anharmonicRatfuncToMero (anharmonicRatFuncEquiv r) := by
  have hhom : (anharmonicMeroEquiv : meroField anharmonicDomain →+* meroField anharmonicDomain).comp
      anharmonicRatfuncToMero
      = anharmonicRatfuncToMero.comp
        (anharmonicRatFuncEquiv : RatFunc ℂ →+* RatFunc ℂ) := by
    refine ratFunc_ringHom_ext (fun c => ?_) ?_
    · show anharmonicMeroEquiv (anharmonicRatfuncToMero (RatFunc.C c))
        = anharmonicRatfuncToMero (anharmonicRatFuncEquiv (RatFunc.C c))
      have hconst : anharmonicRatfuncToMero (RatFunc.C c)
          = algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
            (polyToAnalytic anharmonicDomain (Polynomial.C c)) := by
        rw [show (RatFunc.C c : RatFunc ℂ)
            = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) from
          (RatFunc.algebraMap_C c).symm, anharmonicRatfuncToMero_algebraMap_polynomial]
        rfl
      have hfix : anharmonicAnalyticEquiv (polyToAnalytic anharmonicDomain (Polynomial.C c))
          = polyToAnalytic anharmonicDomain (Polynomial.C c) := by
        apply Subtype.ext
        change Germ.ofFun (l := 𝓟 anharmonicDomain)
            (fun z : ℂ => (Polynomial.C c).eval (anharmonicMap z))
          = Germ.ofFun (l := 𝓟 anharmonicDomain)
            (fun z : ℂ => (Polynomial.C c).eval z)
        rw [Germ.coe_eq]
        exact eventually_principal.mpr fun z _ => by simp
      have hCalg : (RatFunc.C c : RatFunc ℂ) = algebraMap ℂ (RatFunc ℂ) c := by
        rw [RatFunc.algebraMap_eq_C]
      have hfixC : anharmonicRatFuncEquiv (RatFunc.C c) = RatFunc.C c := by
        rw [hCalg, AlgEquiv.commutes]
      rw [hconst, anharmonicMeroEquiv_algebraMap, hfix, hfixC, hconst]
    · show anharmonicMeroEquiv (anharmonicRatfuncToMero RatFunc.X)
        = anharmonicRatfuncToMero (anharmonicRatFuncEquiv RatFunc.X)
      rw [anharmonicRatFuncEquiv_X, anharmonicRatfuncToMero_anharmonicRatFunc,
        show (RatFunc.X : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X from
          (RatFunc.algebraMap_X).symm,
        anharmonicRatfuncToMero_algebraMap_polynomial]
      show anharmonicMeroEquiv
          (algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
            (polyToAnalytic anharmonicDomain Polynomial.X)) = _
      rw [anharmonicMeroEquiv_algebraMap, anharmonicAnalyticEquiv_coordinate]
  exact RingHom.congr_fun hhom r

/-- The derivative factor is the square of the anharmonic coordinate. -/
theorem anharmonicFactorElement_eq :
    algebraMap (analyticSubring anharmonicDomain) (meroField anharmonicDomain)
        anharmonicFactorElement
      = anharmonicRatfuncToMero (anharmonicRatFunc ^ 2) := by
  have hsq : anharmonicFactorElement
      = (analyticFunctionElement anharmonicMap analyticOnNhd_anharmonicMap) ^ 2 := by
    apply Subtype.ext
    change Germ.ofFun (l := 𝓟 anharmonicDomain) anharmonicFactorFun
      = (Germ.ofFun (l := 𝓟 anharmonicDomain) anharmonicMap) ^ 2
    rw [← Germ.coe_pow, Germ.coe_eq]
    refine eventually_principal.mpr fun z hz => ?_
    have h1 : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem hz
    simp only [anharmonicFactorFun, anharmonicMap, Pi.pow_apply]
    field_simp
  rw [hsq, map_pow, map_pow, anharmonicRatfuncToMero_anharmonicRatFunc]

/-! ## The rescaled substitution automorphism over the rational coordinate field -/

theorem one_sub_ratFuncX_ne_zero : (1 : RatFunc ℂ) - RatFunc.X ≠ 0 := by
  intro h
  have hX : (RatFunc.X : RatFunc ℂ) = 1 := by linear_combination -h
  exact RatFunc.transcendental_X (hX ▸ isAlgebraic_one)

theorem anharmonicRatFunc_ne_zero : anharmonicRatFunc ≠ 0 := by
  rw [anharmonicRatFunc]
  exact inv_ne_zero one_sub_ratFuncX_ne_zero

local instance anharmonicMeroCharZero : CharZero (meroField anharmonicDomain) :=
  charZero_of_injective_algebraMap (R := RatFunc ℂ) (A := meroField anharmonicDomain)
    anharmonicRatfuncToMero.injective

/-- **The anharmonic substitution as a rescaled differential automorphism.**  Precomposition with
`r z = 1/(1-z)` is a field automorphism of the meromorphic function field of the twice-punctured
plane which carries `ℂ(z)` onto itself and rescales the derivation by `r'(z) = (1-z)⁻²`. -/
def anharmonicRescaledEquiv :
    DifferentialRescaledEquiv (RatFunc ℂ) (meroField anharmonicDomain) where
  baseEquiv := anharmonicRatFuncEquiv.toRingEquiv
  ambientEquiv := anharmonicMeroEquiv
  factor := anharmonicRatFunc ^ 2
  factor_ne_zero := pow_ne_zero 2 anharmonicRatFunc_ne_zero
  map_algebraMap' := fun c => anharmonicMeroEquiv_ratfuncToMero c
  map_deriv' := fun x => by
    rw [anharmonicMeroEquiv_deriv x, anharmonicFactorElement_eq]
    rfl

@[simp] theorem anharmonicRescaledEquiv_ambientEquiv :
    anharmonicRescaledEquiv.ambientEquiv = anharmonicMeroEquiv := rfl

/-! ## Transporting global hypertranscendence to the anharmonic meromorphic field -/

/-- An entire function satisfying no algebraic differential equation is hypertranscendental over
`ℂ(z)` inside the meromorphic field of the twice-punctured plane.  The identity theorem upgrades a
relation on that open set to a global relation. -/
theorem hypertranscendentalOver_analyticMeroElement_of_hypertranscendental
    {f : ℂ → ℂ} (hfd : Differentiable ℂ f) (hf : AnalyticOnNhd ℂ f anharmonicDomain)
    (hHT : Hypertranscendental f) :
    HypertranscendentalOver (RatFunc ℂ) (analyticMeroElement f hf) := by
  intro hDA
  have h2 : DifferentiallyAlgebraicOn f anharmonicDomain :=
    (differentialAlgebraicOver_analyticMeroElement_iff anharmonicDomain_isOpen
      anharmonicDomain_isPreconnected anharmonicDomain_nonempty anharmonicDomain_infinite
      hf).mp hDA
  exact hHT (differentiallyAlgebraic_of_differentiallyAlgebraicOn hfd
    anharmonicDomain_isOpen anharmonicDomain_nonempty h2)

end

end GaloisForLFunctions.HTGeometry
