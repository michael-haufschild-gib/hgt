import GaloisForLFunctions.RHTower.WeldBoundedSpectralGauge
import GaloisForLFunctions.RHTower.SeamSpectralFlow

/-!
# The weld class determines an area form, not a complex structure

The external `ClassInducesJ` interface points in the wrong direction.  The scalar weld line has a
canonical, injective realization as alternating area forms on the real generator plane.  It cannot
canonically determine a complex structure: the area-preserving upper shear fixes the weld form, and
any natural `J` would commute with that shear, acquire a real eigendirection, and contradict `J²=-1`.

With a complex structure supplied independently, an invariant alternating form canonically produces
the positive metric `Q(x,y)=Ω(x,Jy)`.  The functional equation supplies a different fixed operator:
coefficient reflection is an anti-symplectic involution.  Twisting by it gives the hyperbolic form
`K_θ(x,y)=θ(x₁y₂+x₂y₁)`, with one positive and one negative direction.  In light-cone coordinates it
is exactly the existing one-pair `factoredKreinForm`.  Thus the class does not induce `J`; the fixed
FE parity converts its canonical area directly into the local Krein block.  What remains is the
arithmetic activation/assembly of these blocks, not an arbitrary polarization relation.
-/

open Complex Matrix GaloisForLFunctions

noncomputable section
namespace GaloisForLFunctions.RHTower

/-- Twist an alternating form in the right slot by an independently supplied complex structure. -/
def SymmetricFormOfAlt {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) (Ω : LinearMap.BilinForm ℝ V) :
    LinearMap.BilinForm ℝ V :=
  Ω.compl₂ C.J

/-- A `J`-invariant alternating form yields a symmetric right-`J` twist. -/
theorem symmetricFormOfAlt_isSymm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) (Ω : LinearMap.BilinForm ℝ V)
    (hΩ : Ω.IsAlt) (hpres : PreservesBilin Ω C.J) :
    (SymmetricFormOfAlt C Ω).IsSymm := by
  refine ⟨?_⟩
  intro x y
  change Ω x (C.J y) = Ω y (C.J x)
  have hmove := hpres (C.J x) y
  have hmove' : -Ω x (C.J y) = Ω (C.J x) y := by
    simpa [C.apply_sq] using hmove
  calc
    Ω x (C.J y) = -Ω (C.J x) y := by linarith
    _ = Ω y (C.J x) := hΩ.neg_eq (C.J x) y

/-- The symmetric form obtained from an invariant alternating form is itself `J`-invariant. -/
theorem symmetricFormOfAlt_preserves {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) (Ω : LinearMap.BilinForm ℝ V)
    (_hΩ : Ω.IsAlt) (hpres : PreservesBilin Ω C.J) :
    PreservesBilin (SymmetricFormOfAlt C Ω) C.J := by
  intro x y
  change Ω (C.J x) (C.J (C.J y)) = Ω x (C.J y)
  rw [C.apply_sq]
  have hmove := hpres (C.J x) y
  have hmove' : -Ω x (C.J y) = Ω (C.J x) y := by
    simpa [C.apply_sq] using hmove
  simpa using (congrArg Neg.neg hmove').symm

/-- Construct a polarization from a fixed complex structure and compatible alternating form. -/
def polarizedOfAlt {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) (Ω : LinearMap.BilinForm ℝ V)
    (hΩ : Ω.IsAlt) (hpres : PreservesBilin Ω C.J) :
    PolarizedOmegaComplexStructure V (SymmetricFormOfAlt C Ω) where
  complex := C
  preserves := symmetricFormOfAlt_preserves C Ω hΩ hpres

/-- Twisting the resulting symmetric form by `J` recovers the original alternating form up to sign. -/
theorem polarizedOfAlt_recovers_neg {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : OmegaComplexStructure V) (Ω : LinearMap.BilinForm ℝ V)
    (hΩ : Ω.IsAlt) (hpres : PreservesBilin Ω C.J) :
    (SymmetricFormOfAlt C Ω).compl₂ (polarizedOfAlt C Ω hΩ hpres).complex.J = -Ω := by
  ext x y
  simp [SymmetricFormOfAlt, polarizedOfAlt, LinearMap.compl₂_apply, C.apply_sq]

/-- The alternating area form encoded by conversion rate `θ` on the real weld-generator plane. -/
def weldAreaForm (θ : ℝ) : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun x y : ℝ × ℝ => θ * (x.1 * y.2 - x.2 * y.1))
    (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

theorem weldAreaForm_isAlt (θ : ℝ) : (weldAreaForm θ).IsAlt := by
  intro x
  change θ * (x.1 * x.2 - x.2 * x.1) = 0
  ring

/-- Standard quarter-turn preserves every weld area form. -/
theorem weldAreaForm_planeJ_preserves (θ : ℝ) :
    PreservesBilin (weldAreaForm θ) planeJ := by
  intro x y
  change θ * ((-x.2) * y.1 - x.1 * (-y.2)) =
    θ * (x.1 * y.2 - x.2 * y.1)
  ring

/-- Conversion rate maps additively and faithfully to weld area forms. -/
def weldAreaHom : ℝ →+ LinearMap.BilinForm ℝ (ℝ × ℝ) where
  toFun := weldAreaForm
  map_zero' := by
    apply LinearMap.BilinForm.ext
    intro x y
    change 0 * (x.1 * y.2 - x.2 * y.1) = 0
    ring
  map_add' θ η := by
    apply LinearMap.BilinForm.ext
    intro x y
    change (θ + η) * (x.1 * y.2 - x.2 * y.1) =
      θ * (x.1 * y.2 - x.2 * y.1) + η * (x.1 * y.2 - x.2 * y.1)
    ring

theorem weldAreaHom_injective : Function.Injective weldAreaHom := by
  intro θ η h
  have heval := congrArg (fun Ω : LinearMap.BilinForm ℝ (ℝ × ℝ) => Ω (1, 0) (0, 1)) h
  simpa [weldAreaHom, weldAreaForm] using heval

/-- The one-dimensional subgroup of scalar cohomology consisting of weld classes. -/
abbrev WeldClassLine := weldClassHom.range

/-- The weld-class line is additively equivalent to its conversion-rate coordinate. -/
def weldClassLineEquiv : ℝ ≃+ WeldClassLine :=
  AddEquiv.ofBijective weldClassHom.rangeRestrict
    ⟨by
      intro θ η h
      apply weldClassHom_injective
      exact congrArg Subtype.val h,
     weldClassHom.rangeRestrict_surjective⟩

/-- **Correct canonical direction.**  A weld class determines its alternating area form. -/
def weldClassLineToArea : WeldClassLine →+ LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  weldAreaHom.comp weldClassLineEquiv.symm.toAddMonoidHom

theorem weldClassLineToArea_injective : Function.Injective weldClassLineToArea :=
  weldAreaHom_injective.comp weldClassLineEquiv.symm.injective

theorem weldClassLineToArea_apply (θ : ℝ) :
    weldClassLineToArea (weldClassHom.rangeRestrict θ) = weldAreaForm θ := by
  change weldAreaForm (weldClassLineEquiv.symm (weldClassHom.rangeRestrict θ)) = _
  rw [show weldClassHom.rangeRestrict θ = weldClassLineEquiv θ from rfl,
    weldClassLineEquiv.symm_apply_apply]

/-- Symmetric generator-plane form obtained from the weld area and the independently fixed `planeJ`. -/
def weldPlaneQ (θ : ℝ) : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  SymmetricFormOfAlt planeOmegaComplexStructure (weldAreaForm θ)

theorem weldPlaneQ_apply (θ : ℝ) (x y : ℝ × ℝ) :
    weldPlaneQ θ x y = θ * (x.1 * y.1 + x.2 * y.2) := by
  simp [weldPlaneQ, SymmetricFormOfAlt, weldAreaForm, planeOmegaComplexStructure, planeJ,
    LinearMap.compl₂_apply]

theorem weldPlaneQ_isSymm (θ : ℝ) : (weldPlaneQ θ).IsSymm :=
  symmetricFormOfAlt_isSymm planeOmegaComplexStructure (weldAreaForm θ)
    (weldAreaForm_isAlt θ) (weldAreaForm_planeJ_preserves θ)

/-- The fixed plane complex structure polarizes the weld area form. -/
def weldPlanePolarization (θ : ℝ) :
    PolarizedOmegaComplexStructure (ℝ × ℝ) (weldPlaneQ θ) :=
  polarizedOfAlt planeOmegaComplexStructure (weldAreaForm θ)
    (weldAreaForm_isAlt θ) (weldAreaForm_planeJ_preserves θ)

theorem weldPlanePolarization_recovers_neg_area (θ : ℝ) :
    (weldPlaneQ θ).compl₂ (weldPlanePolarization θ).complex.J = -weldAreaForm θ :=
  polarizedOfAlt_recovers_neg planeOmegaComplexStructure (weldAreaForm θ)
    (weldAreaForm_isAlt θ) (weldAreaForm_planeJ_preserves θ)

/-- Positive conversion rate makes the local generator-plane form positive definite. -/
theorem weldPlaneQ_posDef {θ : ℝ} (hθ : 0 < θ) :
    ∀ x : ℝ × ℝ, x ≠ 0 → 0 < weldPlaneQ θ x x := by
  intro x hx
  rw [weldPlaneQ_apply]
  have hcoord : x.1 ≠ 0 ∨ x.2 ≠ 0 := by
    by_contra h
    rw [not_or, not_ne_iff, not_ne_iff] at h
    exact hx (Prod.ext h.1 h.2)
  have hsum : 0 < x.1 * x.1 + x.2 * x.2 := by
    rcases hcoord with h1 | h2
    · nlinarith [mul_self_pos.mpr h1, mul_self_nonneg x.2]
    · nlinarith [mul_self_nonneg x.1, mul_self_pos.mpr h2]
  exact mul_pos hθ hsum

/-- Every prime weld produces a positive-definite local generator-plane form. -/
theorem prime_weldPlaneQ_posDef {p : ℕ} (hp : p.Prime) :
    ∀ x : ℝ × ℝ, x ≠ 0 → 0 < weldPlaneQ (Real.log p) x x :=
  weldPlaneQ_posDef (Real.log_pos (by exact_mod_cast hp.one_lt))

/-- Functional-equation parity on affine coefficients: derivation odd, scalar identity even. -/
def weldFEReflectionLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (-x.1, x.2)
  map_add' x y := by
    ext
    · simp
      ring
    · simp
  map_smul' a x := by
    ext
    · simp
    · simp

/-- FE coefficient reflection is an involution. -/
theorem weldFEReflectionLinear_sq :
    weldFEReflectionLinear.comp weldFEReflectionLinear = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext <;> simp [weldFEReflectionLinear, LinearMap.comp_apply]

/-- FE coefficient reflection is anti-symplectic for the canonical weld area. -/
theorem weldFEReflectionLinear_reverses_area (θ : ℝ) :
    ∀ x y, weldAreaForm θ (weldFEReflectionLinear x) (weldFEReflectionLinear y) =
      -weldAreaForm θ x y := by
  intro x y
  change θ * ((-x.1) * y.2 - x.2 * (-y.1)) =
    -(θ * (x.1 * y.2 - x.2 * y.1))
  ring

/-- **Explicit FE Krein form.**  Twist the weld area by the fixed anti-symplectic FE reflection. -/
def weldFEKreinQ (θ : ℝ) : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  (weldAreaForm θ).compl₂ weldFEReflectionLinear

theorem weldFEKreinQ_apply (θ : ℝ) (x y : ℝ × ℝ) :
    weldFEKreinQ θ x y = θ * (x.1 * y.2 + x.2 * y.1) := by
  simp [weldFEKreinQ, weldAreaForm, weldFEReflectionLinear, LinearMap.compl₂_apply]

/-- Anti-symplectic twisting makes the weld form symmetric. -/
theorem weldFEKreinQ_isSymm (θ : ℝ) : (weldFEKreinQ θ).IsSymm := by
  refine ⟨?_⟩
  intro x y
  rw [weldFEKreinQ_apply, weldFEKreinQ_apply]
  ring

/-- Positive conversion rate gives the FE-twisted form split signature: one positive and one
negative light-cone direction. -/
theorem weldFEKreinQ_split_signature {θ : ℝ} (hθ : 0 < θ) :
    0 < weldFEKreinQ θ (1, 1) (1, 1) ∧ weldFEKreinQ θ (1, -1) (1, -1) < 0 := by
  rw [weldFEKreinQ_apply, weldFEKreinQ_apply]
  constructor <;> norm_num <;> linarith

/-- Complex Gram of the FE-reflection twist: the hyperbolic plane with off-diagonal rate `θ`. -/
def weldFEKreinGram (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, (θ : ℂ); (θ : ℂ), 0]

/-- The FE weld Gram has an explicit negative direction whenever the conversion rate is positive. -/
theorem weldFEKreinGram_not_kreinNonneg {θ : ℝ} (hθ : 0 < θ) :
    ¬_root_.RHTower.KreinNonneg (weldFEKreinGram θ) := by
  intro h
  have hneg := h ![(1 : ℂ), -1]
  simp [weldFEKreinGram, dotProduct] at hneg
  linarith

/-- Positive light-cone vector used in the one-pair Krein factorization. -/
def weldLightPositive (c : ℝ) : Fin 1 → (Fin 2 → ℂ) :=
  fun _ => ![(c : ℂ), (c : ℂ)]

/-- Negative light-cone vector used in the one-pair Krein factorization. -/
def weldLightNegative (c : ℝ) : Fin 1 → (Fin 2 → ℂ) :=
  fun _ => ![(c : ℂ), -(c : ℂ)]

/-- The difference of the two light-cone rank-one squares is exactly the FE hyperbolic block. -/
theorem factoredKrein_weldLight_eq (c : ℝ) :
    _root_.RHTower.factoredKreinForm (weldLightPositive c) (weldLightNegative c) =
      weldFEKreinGram (2 * c ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weldLightPositive, weldLightNegative, _root_.RHTower.factoredKreinForm,
      weldFEKreinGram]
  all_goals ring

/-- Normalization placing a prescribed nonnegative rate on the light-cone block. -/
def weldLightScale (θ : ℝ) : ℝ := Real.sqrt (θ / 2)

/-- **Local identification.**  The FE-reflection twist of a nonnegative weld rate is exactly the
existing one-pair `factoredKreinForm`. -/
theorem factoredKrein_weldLight_eq_rate {θ : ℝ} (hθ : 0 ≤ θ) :
    _root_.RHTower.factoredKreinForm
        (weldLightPositive (weldLightScale θ)) (weldLightNegative (weldLightScale θ)) =
      weldFEKreinGram θ := by
  rw [factoredKrein_weldLight_eq]
  congr 1
  unfold weldLightScale
  rw [show (Real.sqrt (θ / 2)) ^ 2 = θ / 2 by
    exact Real.sq_sqrt (div_nonneg hθ (by norm_num))]
  ring

/-- Every prime weld supplies the canonical one-pair factored Krein hyperbolic block. -/
theorem prime_factoredKrein_weldLight_eq_rate {p : ℕ} (hp : p.Prime) :
    _root_.RHTower.factoredKreinForm
        (weldLightPositive (weldLightScale (Real.log p)))
        (weldLightNegative (weldLightScale (Real.log p))) =
      weldFEKreinGram (Real.log p) :=
  factoredKrein_weldLight_eq_rate
    (le_of_lt (Real.log_pos (by exact_mod_cast hp.one_lt)))

/-- Complex Gram matrix of the local weld-plane metric. -/
def weldPlaneGram (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (θ : ℂ) • 1

/-- Nonnegative conversion rate gives a nonnegative local Krein Gram. -/
theorem weldPlaneGram_kreinNonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    _root_.RHTower.KreinNonneg (weldPlaneGram θ) := by
  intro x
  simp [weldPlaneGram, dotProduct]
  have h0r : 0 ≤ θ * ((x 0).re * (x 0).re) := mul_nonneg hθ (mul_self_nonneg _)
  have h0i : 0 ≤ θ * ((x 0).im * (x 0).im) := mul_nonneg hθ (mul_self_nonneg _)
  have h1r : 0 ≤ θ * ((x 1).re * (x 1).re) := mul_nonneg hθ (mul_self_nonneg _)
  have h1i : 0 ≤ θ * ((x 1).im * (x 1).im) := mul_nonneg hθ (mul_self_nonneg _)
  nlinarith

/-- Every congruence pullback of a nonnegative local weld Gram remains nonnegative. -/
theorem weldPlaneGram_congr_kreinNonneg {θ : ℝ} (hθ : 0 ≤ θ)
    (P : Matrix (Fin 2) (Fin 2) ℂ) :
    _root_.RHTower.KreinNonneg (Pᴴ * weldPlaneGram θ * P) :=
  _root_.RHTower.kreinNonneg_congr_of (weldPlaneGram θ) P
    (weldPlaneGram_kreinNonneg hθ)

/-- A form with a negative Krein direction is not a congruence pullback of the local weld Gram. -/
theorem not_eq_congr_weldPlaneGram_of_not_kreinNonneg
    {θ : ℝ} (hθ : 0 ≤ θ) {H : Matrix (Fin 2) (Fin 2) ℂ}
    (hH : ¬_root_.RHTower.KreinNonneg H) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    H ≠ Pᴴ * weldPlaneGram θ * P := by
  intro hEq
  apply hH
  rw [hEq]
  exact weldPlaneGram_congr_kreinNonneg hθ P

/-- **Positive-pullback no-go.**  A nondegenerate factored Krein form carrying an off-line pair
cannot be obtained by congruence from the positive local weld metric. -/
theorem factoredKrein_ne_congr_weldPlaneGram_of_pos {k : ℕ} (hk : 0 < k)
    (w u : Fin k → (Fin 2 → ℂ))
    (Φ Ψ : (Fin 2 → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hΦ : ∀ (y : Fin 2 → ℂ) (i : Fin k), Φ y i = star (w i) ⬝ᵥ y)
    (hΨ : ∀ (y : Fin 2 → ℂ) (i : Fin k), Ψ y i = star (u i) ⬝ᵥ y)
    (hT : Function.Surjective (Φ.prod Ψ)) {θ : ℝ} (hθ : 0 ≤ θ)
    (P : Matrix (Fin 2) (Fin 2) ℂ) :
    _root_.RHTower.factoredKreinForm w u ≠ Pᴴ * weldPlaneGram θ * P :=
  not_eq_congr_weldPlaneGram_of_not_kreinNonneg hθ
    (_root_.RHTower.factoredKrein_not_kreinNonneg_of_pos hk w u Φ Ψ hΦ hΨ hT) P

/-- An area-preserving upper shear of the real weld-generator plane. -/
def weldUpperShear : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (z.1 + z.2, z.2)
  invFun z := (z.1 - z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by
    ext
    · simp
      ring
    · simp
  map_smul' a x := by
    ext
    · simp
      ring
    · simp

theorem weldUpperShear_preserves_area (θ : ℝ) :
    PreservesBilin (weldAreaForm θ) weldUpperShear.toLinearMap := by
  intro x y
  change θ * ((x.1 + x.2) * y.2 - x.2 * (y.1 + y.2)) =
    θ * (x.1 * y.2 - x.2 * y.1)
  ring

/-- A hypothetical complex structure canonically natural under every weld-area automorphism. -/
structure WeldClassNaturalComplexStructure (θ : ℝ) where
  complex : OmegaComplexStructure (ℝ × ℝ)
  natural : ∀ P : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ),
    PreservesBilin (weldAreaForm θ) P.toLinearMap →
      complex.J.comp P.toLinearMap = P.toLinearMap.comp complex.J

/-- **No canonical `J` from the weld class.**  Naturality under the area-preserving upper shear
would force a real eigendirection, impossible for `J²=-1`. -/
theorem no_weldClassNaturalComplexStructure (θ : ℝ) :
    IsEmpty (WeldClassNaturalComplexStructure θ) := by
  refine ⟨?_⟩
  intro N
  let e₁ : ℝ × ℝ := (1, 0)
  have hcomm := N.natural weldUpperShear (weldUpperShear_preserves_area θ)
  have heval := congrArg (fun T : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) => T e₁) hcomm
  have hfixed : weldUpperShear (N.complex.J e₁) = N.complex.J e₁ := by
    simpa [LinearMap.comp_apply, e₁, weldUpperShear] using heval.symm
  have hsnd : (N.complex.J e₁).2 = 0 := by
    have hfst := congrArg Prod.fst hfixed
    change (N.complex.J e₁).1 + (N.complex.J e₁).2 = (N.complex.J e₁).1 at hfst
    linarith
  have heigen : N.complex.J e₁ = (N.complex.J e₁).1 • e₁ := by
    ext
    · simp [e₁]
    · simp [e₁, hsnd]
  have hzero : e₁ = 0 := N.complex.eq_zero_of_apply_eq_smul heigen
  have hfirst := congrArg Prod.fst hzero
  norm_num [e₁] at hfirst

end GaloisForLFunctions.RHTower
