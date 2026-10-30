import GaloisForLFunctions.AdelicKreinGeometry.HeckeSupportedStatesHaveIndexZeroOrInfinity
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-!
# The Pontryagin extensions of Weil's correlation

Weil's correlation `ratCorr(r) = W(B(· + log r), B)` of the cubic spline `B` lives on the dilations
`x ↦ rx`, `r ∈ ℚ_{>0}`, of `Aff(ℚ)`. It is the Weil kernel `K_ζ` of the Hecke lattice
(`ratCorr_eq_zetaKernel`), so its index is the number of zeros right of the critical line
(`negIndex_ratCorr`). This file classifies its Hermitian extensions to the affine group by index.

* **The blind extension is index-minimal** (`negIndex_blindWeilState`, `negIndex_le_of_weil_extension`).
  Every extension has index at least `κ(K_ζ)`; the pullback along `g ↦ |slope g|`, whose
  successor is constant, has index exactly `κ(K_ζ)`.
* **The regular extension** (`negIndex_regularWeilState`): extension by zero off the dilations has
  index `0` under RH and `∞` otherwise. The dilations have infinitely many cosets, and each carries
  a copy of every negative square.
* **Hecke-supported extensions** (`riemannHypothesis_of_isHeckeSupported_weil_extension`,
  `negIndex_eq_top_of_isHeckeSupported_weil_extension`). A Hecke-supported Hermitian extension
  of finite index is positive and proves RH; off RH every Hecke-supported extension has infinite
  index.
* **No Pontryagin state carries Weil's correlation and the Haar successor**
  (`negIndex_eq_top_of_weil_haarSuccessor`). A Hecke-supported Hermitian extension whose successor
  is `c·1_ℤ`, `c ≠ 0`, has infinite index, unconditionally: finite index would make it positive,
  and a positive state with Weil's dilation part has a blind successor.

So indefiniteness does not open the integer successor to Weil's correlation: within the
integer-supported class the only finite index is zero, and then the successor is blind. A
finite-index carrier of Weil's correlation with a visible successor must leave Hecke support.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Weil's correlation is the Weil kernel of the Hecke lattice -/

/-- The positive rational units are the Hecke lattice. -/
def posUnitsToHecke : posUnits →* HeckeLattice where
  toFun u := ⟨((u : ℚˣ) : ℚ), u.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem posUnitsToHecke_surjective : Function.Surjective posUnitsToHecke := fun q =>
  ⟨⟨Units.mk0 (q : ℚ) q.2.ne', by simpa [posUnits] using q.2⟩, Subtype.ext rfl⟩

/-- **Weil's correlation is the Weil kernel of `ζ`.** -/
theorem ratCorr_eq_zetaKernel (u : posUnits) : ratCorr u = zetaKernel (posUnitsToHecke u) := by
  have hB := cx_contDiff contDiff_cubicSpline
  have hBc := cx_hasCompactSupport hasCompactSupport_cubicSpline
  have hW := RHTower.zeta_W_eq_weilFullFunctional_mixed hB hBc
    (ArithmeticCastelnuovoSeveri.translate_contDiff hB (scale heckeLogScale (posUnitsToHecke u)))
    (ArithmeticCastelnuovoSeveri.translate_hasCompactSupport hBc _)
  have h0 : ArithmeticCastelnuovoSeveri.translate 0 (cx cubicSpline) = cx cubicSpline :=
    funext fun t => by simp [ArithmeticCastelnuovoSeveri.translate]
  have htr := weilTest_translate_translate 0 (scale heckeLogScale (posUnitsToHecke u)) cubicSpline
  rw [h0, zero_sub] at htr
  rw [zetaKernel, orbitKernel, hW, htr, ratCorr, splineCorr]
  rfl

theorem ratCorr_eq_comp : ratCorr = zetaKernel ∘ posUnitsToHecke := funext ratCorr_eq_zetaKernel

theorem isHermKernel_ratCorr : IsHermKernel ratCorr := by
  rw [ratCorr_eq_comp]; exact isHermKernel_zetaKernel.comp _

/-- **The index of Weil's correlation is the index of `K_ζ`**, the number of zeros right of the
critical line. -/
theorem negIndex_ratCorr : negIndex ratCorr = negIndex zetaKernel := by
  rw [ratCorr_eq_comp, negIndex_comp_of_surjective _ _ posUnitsToHecke_surjective]

/-! ### The blind extension -/

/-- The slope of an affine map as a unit. -/
def slopeUnit : AffineGroupQ →* ℚˣ where
  toFun g := Units.mk0 (affSlope g) (affSlope_ne_zero g)
  map_one' := Units.ext (by simp [affSlope_one])
  map_mul' g h := Units.ext (by simp [affSlope_mul])

/-- The absolute value of a rational unit. -/
def absUnit : ℚˣ →* posUnits where
  toFun u := ⟨Units.mk0 |(u : ℚ)| (abs_ne_zero.mpr u.ne_zero), by
    show (0 : ℚ) < ((Units.mk0 |(u : ℚ)| _ : ℚˣ) : ℚ)
    rw [Units.val_mk0]; exact abs_pos.mpr u.ne_zero⟩
  map_one' := Subtype.ext (Units.ext (by simp))
  map_mul' u v := Subtype.ext (Units.ext (by simp [abs_mul]))

/-- The absolute slope `g ↦ |slope g|`, a retraction of `Aff(ℚ)` onto the positive dilations. -/
def slopeAbs : AffineGroupQ →* posUnits := absUnit.comp slopeUnit

theorem slopeAbs_dilation (u : posUnits) : slopeAbs (dilation u) = u := by
  apply Subtype.ext
  apply Units.ext
  simp [slopeAbs, absUnit, slopeUnit, affSlope_dilation, abs_of_pos (show (0 : ℚ) < (u : ℚˣ) from u.2)]

theorem slopeAbs_translation (b : ℚ) : slopeAbs (translation b) = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [slopeAbs, absUnit, slopeUnit, affSlope_translation]

/-- The **blind extension** of Weil's correlation: `φ(x ↦ ax + b) = ratCorr(|a|)`. -/
def blindWeilState : AffineGroupQ → ℂ := ratCorr ∘ slopeAbs

theorem blindWeilState_dilation (u : posUnits) : blindWeilState (dilation u) = ratCorr u := by
  simp [blindWeilState, slopeAbs_dilation]

/-- The successor of the blind extension is constant. -/
theorem blindWeilState_translation (b : ℚ) : blindWeilState (translation b) = splineCorr 0 := by
  simp [blindWeilState, slopeAbs_translation, ratCorr, logPos]

/-- **Every affine extension of Weil's correlation has index at least `κ(K_ζ)`.** -/
theorem negIndex_le_of_weil_extension {φ : AffineGroupQ → ℂ}
    (hdil : ∀ u : posUnits, φ (dilation u) = ratCorr u) : negIndex zetaKernel ≤ negIndex φ := by
  have e : φ ∘ (dilation.comp posUnits.subtype) = ratCorr := funext hdil
  rw [← negIndex_ratCorr, ← e]
  exact negIndex_comp_le φ _

/-- **The blind extension is index-minimal**: its index is exactly `κ(K_ζ)`. -/
theorem negIndex_blindWeilState : negIndex blindWeilState = negIndex zetaKernel := by
  rw [blindWeilState, negIndex_comp_of_surjective _ _ fun u => ⟨dilation u, slopeAbs_dilation u⟩,
    negIndex_ratCorr]

/-! ### The regular extension -/

/-- The dilations of `Aff(ℚ)` have infinitely many cosets: the integer translations lie in
distinct ones. -/
theorem infinite_quotient_dilationSubgroup : Infinite (AffineGroupQ ⧸ dilationSubgroup) := by
  refine Infinite.of_injective (fun n : ℕ => ((translation n : AffineGroupQ) :
    AffineGroupQ ⧸ dilationSubgroup)) fun m n hmn => ?_
  have hmem := QuotientGroup.eq.mp hmn
  rw [translation_inv_mul] at hmem
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp hmem
  have h := congrArg affShift hu
  rw [affShift_dilation, affShift_translation] at h
  exact_mod_cast (sub_eq_zero.mp h.symm).symm

/-- The positive dilations as a homomorphism onto the dilation subgroup. -/
def toDilationSubgroup : posUnits →* dilationSubgroup where
  toFun u := ⟨dilation u, Subgroup.mem_map_of_mem _ u.2⟩
  map_one' := by ext; simp
  map_mul' u v := by ext; simp

theorem toDilationSubgroup_surjective : Function.Surjective toDilationSubgroup := fun h => by
  obtain ⟨u, hu⟩ := exists_eq_dilation h
  exact ⟨u, Subtype.ext hu⟩

theorem dilationCorr_comp : dilationCorr ∘ toDilationSubgroup = ratCorr :=
  funext dilationCorr_dilation

theorem negIndex_dilationCorr : negIndex dilationCorr = negIndex zetaKernel := by
  rw [← negIndex_comp_of_surjective _ _ toDilationSubgroup_surjective, dilationCorr_comp,
    negIndex_ratCorr]

theorem isHermKernel_dilationCorr : IsHermKernel dilationCorr := fun h => by
  obtain ⟨u, rfl⟩ := toDilationSubgroup_surjective h
  rw [← map_inv]
  simp only [← Function.comp_apply (f := dilationCorr), dilationCorr_comp]
  exact isHermKernel_ratCorr u

/-- The **regular extension** of Weil's correlation: zero off the dilations. -/
def regularWeilState : AffineGroupQ → ℂ := extendFromSubgroup dilationSubgroup dilationCorr

/-- **The regular extension has index `0` or `∞`**: `0` under RH, `∞` otherwise. -/
theorem negIndex_regularWeilState :
    negIndex regularWeilState = if RiemannHypothesis then 0 else ⊤ := by
  haveI := infinite_quotient_dilationSubgroup
  rw [regularWeilState, negIndex_extendFromSubgroup isHermKernel_dilationCorr,
    ENat.card_eq_top_of_infinite, negIndex_dilationCorr]
  split_ifs with h
  · rw [riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp h, mul_zero]
  · exact ENat.top_mul (fun h0 => h (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mpr h0))

/-! ### Hecke-supported extensions -/

/-- A Hecke-supported Hermitian extension of Weil's correlation of finite index proves RH. -/
theorem riemannHypothesis_of_isHeckeSupported_weil_extension {φ : AffineGroupQ → ℂ}
    (hk : IsHermKernel φ) (hφ : IsHeckeSupported φ)
    (hdil : ∀ u : posUnits, φ (dilation u) = ratCorr u) (hfin : negIndex φ < ⊤) :
    RiemannHypothesis :=
  riemannHypothesis_iff_exists_affine_posDef.mpr
    ⟨φ, isPosDefOnGroup_of_isHeckeSupported hk hφ hfin, hdil⟩

/-- Off RH every Hecke-supported Hermitian extension of Weil's correlation has infinite index. -/
theorem negIndex_eq_top_of_isHeckeSupported_weil_extension {φ : AffineGroupQ → ℂ}
    (hk : IsHermKernel φ) (hφ : IsHeckeSupported φ)
    (hdil : ∀ u : posUnits, φ (dilation u) = ratCorr u) (hRH : ¬ RiemannHypothesis) :
    negIndex φ = ⊤ := by
  by_contra h
  exact hRH (riemannHypothesis_of_isHeckeSupported_weil_extension hk hφ hdil
    (lt_top_iff_ne_top.mpr h))

/-- **No Pontryagin state carries Weil's correlation and the Haar successor.** A Hecke-supported
Hermitian function on `Aff(ℚ)` with Weil's correlation on the dilations and successor `c·1_ℤ`,
`c ≠ 0`, has infinitely many negative squares. -/
theorem negIndex_eq_top_of_weil_haarSuccessor {φ : AffineGroupQ → ℂ} (hk : IsHermKernel φ)
    (hφ : IsHeckeSupported φ) (hdil : ∀ u : posUnits, φ (dilation u) = ratCorr u) {c : ℂ}
    (hc0 : c ≠ 0) (hc : ∀ b : ℚ, φ (translation b) = c * if b.den = 1 then 1 else 0) :
    negIndex φ = ⊤ := by
  by_contra h
  have hpd := isPosDefOnGroup_of_isHeckeSupported hk hφ (lt_top_iff_ne_top.mpr h)
  exact hc0 (splineCorr_zero_of_integer_successor hpd hdil hc).1

/-- The integer successor `1_ℤ` itself. -/
theorem negIndex_eq_top_of_weil_integerSuccessor {φ : AffineGroupQ → ℂ} (hk : IsHermKernel φ)
    (hφ : IsHeckeSupported φ) (hdil : ∀ u : posUnits, φ (dilation u) = ratCorr u)
    (hs : HasIntegerSuccessor φ) : negIndex φ = ⊤ :=
  negIndex_eq_top_of_weil_haarSuccessor hk hφ hdil one_ne_zero fun b => by rw [hs b, one_mul]

end GaloisForLFunctions.AdelicKreinGeometry
