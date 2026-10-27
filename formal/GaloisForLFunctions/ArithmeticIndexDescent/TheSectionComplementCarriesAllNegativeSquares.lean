import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionProjection
import GaloisForLFunctions.ArithmeticIndexDescent.SingularRefinement
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw
import GaloisForLFunctions.RHTower.WeilPaperPacketRealification
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowPrimeTwoMargin

/-!
# The actual section complement carries every negative square

The real Weil pairing complexifies to the actual complete Weil Gram. Removing
a finite narrow arithmetic section span therefore gives an exact index descent
for that Gram. The old block may be singular: its relations are actual test
relations, so its mixed block lies in its range. All negative squares belong
to the Gram of the actual residual tests.
-/

open Matrix MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics HTGeometry RHTower

/-- Complex mixed Gram of the complete real Weil pairing. -/
def complexWeilMixed {ι κ : Type*} (f : ι → realTests) (g : κ → realTests) : Matrix ι κ ℂ :=
  fun i j => (realWeilForm (f i) (g j) : ℂ)

theorem complexWeilMixed_conjTranspose {ι κ : Type*}
    (f : ι → realTests) (g : κ → realTests) :
    (complexWeilMixed f g)ᴴ = complexWeilMixed g f := by
  ext i j
  simp only [Matrix.conjTranspose_apply, complexWeilMixed, Complex.star_def,
    Complex.conj_ofReal]
  exact congrArg Complex.ofReal (realWeilForm_symm _ _)

theorem complexWeilMixed_isHermitian {ι : Type*} (f : ι → realTests) :
    (complexWeilMixed f f).IsHermitian := complexWeilMixed_conjTranspose f f

/-- This complexification is the literal full Weil matrix, including primes, Gamma and poles. -/
theorem complexWeilMixed_eq_weilGram {ι : Type*} (f : ι → realTests) :
    complexWeilMixed f f =
      weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (fun i => cx (f i).1) := by
  ext i j
  apply Complex.ext
  · rfl
  · change (0 : ℝ) = (weilFullFunctional _ (EF.weilTest (cx (f i).1) (cx (f j).1))).im
    have hcorr : EF.weilTest (cx (f i).1) (cx (f j).1) =
        fun y => ((∫ t : ℝ, (f i).1 t * (f j).1 (t - y) : ℝ) : ℂ) := by
      funext y
      rw [WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
      simp only [cx, Complex.conj_ofReal, Complex.ofReal_mul]
    rw [hcorr]
    exact (WeilWorkPBAP.weilFullFunctional_ofReal_im _ _).symm

theorem complexWeilMixed_synthesis_right {ι κ η : Type*} [Fintype κ]
    (f : ι → realTests) (g : κ → realTests) (X : Matrix κ η ℝ) :
    complexWeilMixed f (fun j => realTestSynthesis g (fun k => X k j)) =
      complexWeilMixed f g * (X.map Complex.ofReal) := by
  ext i j
  change (realWeilForm (f i) (realTestSynthesis g (fun k => X k j)) : ℂ) = _
  rw [← realWeilMixed_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.map_apply,
    realWeilMixed, complexWeilMixed, Complex.ofReal_sum, Complex.ofReal_mul]

theorem complexWeilMixed_synthesis_left {ι κ η : Type*} [Fintype κ]
    (f : κ → realTests) (g : ι → realTests) (X : Matrix κ η ℝ) :
    complexWeilMixed (fun j => realTestSynthesis f (fun k => X k j)) g =
      (X.map Complex.ofReal)ᴴ * complexWeilMixed f g := by
  have h := congrArg Matrix.conjTranspose (complexWeilMixed_synthesis_right g f X)
  simpa only [complexWeilMixed_conjTranspose, Matrix.conjTranspose_mul] using h

theorem complexWeilMixed_synthesis {ι κ : Type*} [Fintype ι]
    (f : ι → realTests) (X : Matrix ι κ ℝ) :
    complexWeilMixed (fun j => realTestSynthesis f (fun i => X i j))
        (fun j => realTestSynthesis f (fun i => X i j)) =
      (X.map Complex.ofReal)ᴴ * complexWeilMixed f f * X.map Complex.ofReal := by
  rw [complexWeilMixed_synthesis_right, complexWeilMixed_synthesis_left]

theorem hermQuad_complexWeilMixed_ofReal {ι : Type*} [Fintype ι]
    (f : ι → realTests) (x : ι → ℝ) :
    hermQuad (complexWeilMixed f f) (fun i => (x i : ℂ)) =
      realWeilForm (realTestSynthesis f x) (realTestSynthesis f x) := by
  rw [realWeilForm_synthesis_self]
  simp only [hermQuad, dotProduct, Matrix.mulVec, complexWeilMixed, realWeilMixed,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum, Complex.im_sum,
    zero_mul, sub_zero, Finset.sum_const_zero, mul_zero]

/-- Narrow arithmetic section Grams have no negative square even for complex coefficients. -/
theorem negIndex_arithmeticSection_eq_zero {n : ℕ} {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : Fin n → arithmeticSectionTests N w) :
    hermNegIndex (complexWeilMixed (fun i => (f i).1) (fun i => (f i).1)) = 0 := by
  have hreal (x : Fin n → ℝ) :
      0 ≤ realWeilForm (realTestSynthesis (fun i => (f i).1) x)
        (realTestSynthesis (fun i => (f i).1) x) := by
    let q := realTestSynthesis (fun i => (f i).1) x
    have hq : q ∈ arithmeticSectionTests N w :=
      (arithmeticSectionTests N w).sum_mem fun i _ =>
        (arithmeticSectionTests N w).smul_mem (x i) (f i).2
    exact (integral_nonneg fun u => sq_nonneg (q.1 u)).trans
      (integral_sq_le_weilPair_arithmeticSection hN hw0 hw ⟨q, hq⟩)
  apply negIndex_eq_zero_of_hermQuad_nonneg
  intro x
  have hsplit := hermQuad_map_ofReal_eq_add
    (realWeilMixed (fun i => (f i).1) (fun i => (f i).1)) x
  change hermQuad (complexWeilMixed (fun i => (f i).1) (fun i => (f i).1)) x = _ at hsplit
  rw [hsplit, hermQuad_complexWeilMixed_ofReal, hermQuad_complexWeilMixed_ofReal]
  exact add_nonneg (hreal fun i => (x i).re) (hreal fun i => (x i).im)

theorem complexWeilMixed_sum {ι κ : Type*} (f : ι → realTests) (g : κ → realTests) :
    complexWeilMixed (Sum.elim f g) (Sum.elim f g) =
      Matrix.fromBlocks (complexWeilMixed f f) (complexWeilMixed f g)
        (complexWeilMixed f g)ᴴ (complexWeilMixed g g) := by
  ext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases j with
    | inl j =>
      change (realWeilForm (g i) (f j) : ℂ) = star (realWeilForm (f j) (g i) : ℂ)
      rw [Complex.star_def, Complex.conj_ofReal, realWeilForm_symm]
    | inr j => rfl

/-- All negative squares of an arithmetic section extension lie in its actual residual tests. -/
theorem negIndex_arithmeticSection_extension_eq_residual {n m : ℕ} {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : Fin n → arithmeticSectionTests N w) (g : Fin m → realTests) :
    hermNegIndex (complexWeilMixed (Sum.elim (fun i => (f i).1) g)
      (Sum.elim (fun i => (f i).1) g)) =
    hermNegIndex (complexWeilMixed
      (fun j => g j - arithmeticSectionProjection hN hw0 hw f (g j))
      (fun j => g j - arithmeticSectionProjection hN hw0 hw f (g j))) := by
  classical
  choose c hc using fun j => (arithmeticSectionProjection_spec hN hw0 hw f (g j)).1
  let X : Matrix (Fin n) (Fin m) ℝ := fun i j => c j i
  let p : Fin m → realTests := fun j => arithmeticSectionProjection hN hw0 hw f (g j)
  have hp : p = fun j => realTestSynthesis (fun i => (f i).1) (fun i => X i j) :=
    funext hc
  have hB : complexWeilMixed (fun i => (f i).1) g =
      complexWeilMixed (fun i => (f i).1) (fun i => (f i).1) * X.map Complex.ofReal := by
    calc
      _ = complexWeilMixed (fun i => (f i).1) p := by
        ext i j
        have horth := (arithmeticSectionProjection_spec hN hw0 hw f (g j)).2 i
        rw [map_sub] at horth
        exact congrArg Complex.ofReal (sub_eq_zero.mp horth)
      _ = _ := by rw [hp, complexWeilMixed_synthesis_right]
  have hPP : complexWeilMixed p p =
      (X.map Complex.ofReal)ᴴ * complexWeilMixed (fun i => (f i).1) (fun i => (f i).1) *
        X.map Complex.ofReal := by
    rw [hp, complexWeilMixed_synthesis]
  have hres : complexWeilMixed (fun j => g j - p j) (fun j => g j - p j) =
      complexWeilMixed g g -
        (X.map Complex.ofReal)ᴴ * complexWeilMixed (fun i => (f i).1) (fun i => (f i).1) *
          X.map Complex.ofReal := by
    rw [← hPP]
    ext i j
    change (realWeilForm (g i - p i) (g j - p j) : ℂ) =
      (realWeilForm (g i) (g j) : ℂ) - (realWeilForm (p i) (p j) : ℂ)
    rw [arithmeticSectionProjection_residual_pair, Complex.ofReal_sub]
  rw [complexWeilMixed_sum, hB,
    negIndex_singular_refinement (complexWeilMixed_isHermitian _) _
      (complexWeilMixed_isHermitian _),
    negIndex_arithmeticSection_eq_zero hN hw0 hw f, zero_add, ← hres]

/-- Exact descent for the literal completed Weil Gram, with no nonsingularity assumption. -/
theorem negIndex_weilGram_section_extension_eq_residual {n m : ℕ} {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : Fin n → arithmeticSectionTests N w) (g : Fin m → realTests) :
    hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
      (fun a => cx ((Sum.elim (fun i => (f i).1) g) a).1)) =
    hermNegIndex (weilGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
      (fun j => cx (g j - arithmeticSectionProjection hN hw0 hw f (g j)).1)) := by
  simpa only [complexWeilMixed_eq_weilGram] using
    negIndex_arithmeticSection_extension_eq_residual hN hw0 hw f g

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.negIndex_weilGram_section_extension_eq_residual
