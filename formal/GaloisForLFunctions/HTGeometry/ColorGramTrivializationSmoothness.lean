import GaloisForLFunctions.HTGeometry.ColorGramGlobalTrivialization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Normed

/-!
# Smoothness of the global product decomposition

In the ambient real coordinates given by the matrix entries, both directions of the product
decomposition of the regular colour locus are `C^∞`.  The Cholesky formulas involve one positive
square root and one division, so they are smooth on the open set where the leading entry and the
determinant have nonvanishing real part; that open set contains the whole positive definite cone.
-/

open Matrix
open scoped ComplexOrder Matrix Matrix.Norms.Elementwise

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Coordinates

/-- Every matrix entry is a smooth real-linear coordinate. -/
theorem contDiff_matrixEntry {m n : ℕ} (i : Fin m) (j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) fun A : Matrix (Fin m) (Fin n) ℂ => A i j := by
  have hlin : IsLinearMap ℝ (fun A : Matrix (Fin m) (Fin n) ℂ => A i j) :=
    { map_add := by intros; rfl, map_smul := by intros; rfl }
  exact ((hlin.mk' _).toContinuousLinearMap).contDiff

/-- Complex conjugation is a smooth real-linear map. -/
theorem contDiff_starComplex : ContDiff ℝ (⊤ : ℕ∞) fun z : ℂ => star z := by
  have hlin : IsLinearMap ℝ (fun z : ℂ => star z) :=
    { map_add := by intro x y; exact star_add x y
      map_smul := by
        intro c x
        simp [Complex.real_smul, mul_comm] }
  exact ((hlin.mk' _).toContinuousLinearMap).contDiff

theorem contDiff_matrixEntry_star {m n : ℕ} (i : Fin m) (j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) fun A : Matrix (Fin m) (Fin n) ℂ => star (A i j) :=
  contDiff_starComplex.comp (contDiff_matrixEntry i j)

/-- The `2 × 2` determinant is a smooth function of the entries. -/
theorem contDiff_gramDet :
    ContDiff ℝ (⊤ : ℕ∞) fun H : Matrix (Fin 2) (Fin 2) ℂ => H.det := by
  have hexp : (fun H : Matrix (Fin 2) (Fin 2) ℂ => H.det)
      = fun H => H 0 0 * H 1 1 - H 0 1 * H 1 0 := by
    funext H
    exact Matrix.det_fin_two H
  rw [hexp]
  exact ((contDiff_matrixEntry 0 0).mul (contDiff_matrixEntry 1 1)).sub
    ((contDiff_matrixEntry 0 1).mul (contDiff_matrixEntry 1 0))

/-- Every colour Gram entry is a smooth function of the event entries. -/
theorem contDiff_colorGramEntry (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun X : ColorEventMatrix => colorGramMatrix X i j := by
  have hexp : (fun X : ColorEventMatrix => colorGramMatrix X i j)
      = fun X => star (X 0 i) * X 0 j + (star (X 1 i) * X 1 j + star (X 2 i) * X 2 j) := by
    funext X
    simp [colorGramMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three]
    ring
  rw [hexp]
  exact ((contDiff_matrixEntry_star 0 i).mul (contDiff_matrixEntry 0 j)).add
    (((contDiff_matrixEntry_star 1 i).mul (contDiff_matrixEntry 1 j)).add
      ((contDiff_matrixEntry_star 2 i).mul (contDiff_matrixEntry 2 j)))

/-- Every completed frame entry is a smooth function of the event entries. -/
theorem contDiff_colorEventFrameEntry (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun X : ColorEventMatrix => colorEventFrame X i j := by
  fin_cases j
  · exact contDiff_matrixEntry i 0
  · exact contDiff_matrixEntry i 1
  · show ContDiff ℝ (⊤ : ℕ∞) fun X : ColorEventMatrix => colorEventNormal X i
    fin_cases i
    · show ContDiff ℝ (⊤ : ℕ∞) fun X : ColorEventMatrix => star (colorMinor12 X)
      have hexp : (fun X : ColorEventMatrix => star (colorMinor12 X))
          = fun X => star (X 1 0) * star (X 2 1) - star (X 2 0) * star (X 1 1) := by
        funext X
        simp [colorMinor12, star_sub, star_mul, mul_comm]
      rw [hexp]
      exact ((contDiff_matrixEntry_star 1 0).mul (contDiff_matrixEntry_star 2 1)).sub
        ((contDiff_matrixEntry_star 2 0).mul (contDiff_matrixEntry_star 1 1))
    · show ContDiff ℝ (⊤ : ℕ∞) fun X : ColorEventMatrix => -star (colorMinor02 X)
      have hexp : (fun X : ColorEventMatrix => -star (colorMinor02 X))
          = fun X => -(star (X 0 0) * star (X 2 1) - star (X 2 0) * star (X 0 1)) := by
        funext X
        simp [colorMinor02, star_sub, star_mul, mul_comm]
      rw [hexp]
      exact (((contDiff_matrixEntry_star 0 0).mul (contDiff_matrixEntry_star 2 1)).sub
        ((contDiff_matrixEntry_star 2 0).mul (contDiff_matrixEntry_star 0 1))).neg
    · show ContDiff ℝ (⊤ : ℕ∞) fun X : ColorEventMatrix => star (colorMinor01 X)
      have hexp : (fun X : ColorEventMatrix => star (colorMinor01 X))
          = fun X => star (X 0 0) * star (X 1 1) - star (X 1 0) * star (X 0 1) := by
        funext X
        simp [colorMinor01, star_sub, star_mul, mul_comm]
      rw [hexp]
      exact ((contDiff_matrixEntry_star 0 0).mul (contDiff_matrixEntry_star 1 1)).sub
        ((contDiff_matrixEntry_star 1 0).mul (contDiff_matrixEntry_star 0 1))

end Coordinates

section SmoothDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quotients of smooth complex-valued functions are smooth away from the zeros of the
denominator. -/
theorem contDiffAt_complex_div {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (hgx : g x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => f y / g y) x := by
  simpa [div_eq_mul_inv, Pi.mul_def, Pi.inv_def] using hf.mul (hg.inv hgx)

/-- The open neighbourhood of the positive cone on which the Cholesky formulas are smooth. -/
def gramSmoothDomain : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {H | 0 < (H 0 0).re ∧ 0 < H.det.re}

theorem isOpen_gramSmoothDomain : IsOpen gramSmoothDomain := by
  have h1 : Continuous fun H : Matrix (Fin 2) (Fin 2) ℂ => (H 0 0).re :=
    Complex.continuous_re.comp (contDiff_matrixEntry 0 0).continuous
  have h2 : Continuous fun H : Matrix (Fin 2) (Fin 2) ℂ => H.det.re :=
    Complex.continuous_re.comp contDiff_gramDet.continuous
  exact (isOpen_Ioi.preimage h1).inter (isOpen_Ioi.preimage h2)

theorem posDef_mem_gramSmoothDomain {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.PosDef) :
    H ∈ gramSmoothDomain :=
  ⟨posDef_diag_zero_re_pos hH, posDef_det_re_pos hH⟩

theorem gramDiagOne_ne_zero_of_mem {H : Matrix (Fin 2) (Fin 2) ℂ} (h : H ∈ gramSmoothDomain) :
    ((gramDiagOne H : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < gramDiagOne H := Real.sqrt_pos.2 h.1
  exact_mod_cast this.ne'

theorem gramDiagTwo_ne_zero_of_mem {H : Matrix (Fin 2) (Fin 2) ℂ} (h : H ∈ gramSmoothDomain) :
    ((gramDiagTwo H : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < gramDiagTwo H := Real.sqrt_pos.2 (div_pos h.2 h.1)
  exact_mod_cast this.ne'

/-- The open neighbourhood of the regular locus on which the trivialization is smooth. -/
def colorSmoothDomain : Set ColorEventMatrix := colorGramMatrix ⁻¹' gramSmoothDomain

theorem isOpen_colorSmoothDomain : IsOpen colorSmoothDomain := by
  refine isOpen_gramSmoothDomain.preimage ?_
  refine continuous_matrix fun i j => ?_
  exact (contDiff_colorGramEntry i j).continuous

theorem regular_mem_colorSmoothDomain {X : ColorEventMatrix}
    (hX : (colorGramMatrix X).PosDef) : X ∈ colorSmoothDomain :=
  posDef_mem_gramSmoothDomain hX

/-- The determinant of a smooth family of `2 × 2` records is smooth. -/
theorem contDiffAt_det_comp {F : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y i j) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (F y).det) x := by
  have hexp : (fun y => (F y).det)
      = fun y => F y 0 0 * F y 1 1 - F y 0 1 * F y 1 0 := by
    funext y
    exact Matrix.det_fin_two _
  rw [hexp]
  exact ((hF 0 0).mul (hF 1 1)).sub ((hF 0 1).mul (hF 1 0))

theorem contDiffAt_gramDiagOne_comp {F : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y i j) x)
    (hdom : F x ∈ gramSmoothDomain) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ((gramDiagOne (F y) : ℝ) : ℂ)) x := by
  have hre : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (F y 0 0).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (hF 0 0) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t) ((F x 0 0).re) :=
    Real.contDiffAt_sqrt hdom.1.ne'
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Real.sqrt ((F y 0 0).re)) x := by
    simpa [Function.comp_def] using hsqrt.comp x hre
  simpa [Function.comp_def, gramDiagOne] using
    (Complex.ofRealCLM.contDiff.contDiffAt).comp x hcomp

theorem contDiffAt_gramDiagTwo_comp {F : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y i j) x)
    (hdom : F x ∈ gramSmoothDomain) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ((gramDiagTwo (F y) : ℝ) : ℂ)) x := by
  have hnum : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (F y).det.re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (contDiffAt_det_comp hF)
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hden : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (F y 0 0).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (hF 0 0) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hquot : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (F y).det.re / (F y 0 0).re) x := by
    simpa [Pi.div_def] using hnum.div hden hdom.1.ne'
  have hne : (F x).det.re / (F x 0 0).re ≠ 0 := (div_pos hdom.2 hdom.1).ne'
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t)
      ((F x).det.re / (F x 0 0).re) := Real.contDiffAt_sqrt hne
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => Real.sqrt ((F y).det.re / (F y 0 0).re)) x := by
    simpa [Function.comp_def] using hsqrt.comp x hquot
  simpa [Function.comp_def, gramDiagTwo] using
    (Complex.ofRealCLM.contDiff.contDiffAt).comp x hcomp

theorem contDiffAt_gramCholeskyEntry_comp {F : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y i j) x)
    (hdom : F x ∈ gramSmoothDomain) (i j : Fin 2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => gramCholesky (F y) i j) x := by
  fin_cases i <;> fin_cases j <;>
    simp only [gramCholesky, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · exact contDiffAt_gramDiagOne_comp hF hdom
  · exact contDiffAt_complex_div (hF 0 1) (contDiffAt_gramDiagOne_comp hF hdom)
      (gramDiagOne_ne_zero_of_mem hdom)
  · exact contDiffAt_const
  · exact contDiffAt_gramDiagTwo_comp hF hdom

theorem contDiffAt_gramSectionEntry_comp {F : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y i j) x)
    (hdom : F x ∈ gramSmoothDomain) (i : Fin 3) (j : Fin 2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => gramSection (F y) i j) x := by
  fin_cases i
  · simpa using contDiffAt_gramCholeskyEntry_comp hF hdom 0 j
  · simpa using contDiffAt_gramCholeskyEntry_comp hF hdom 1 j
  · simpa using (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℂ)) x)

theorem contDiffAt_gramFrameInverseEntry_comp {F : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y i j) x)
    (hdom : F x ∈ gramSmoothDomain) (i j : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => gramFrameInverse (F y) i j) x := by
  have hrne := gramDiagOne_ne_zero_of_mem hdom
  have htne := gramDiagTwo_ne_zero_of_mem hdom
  fin_cases i <;> fin_cases j <;>
    simp only [gramFrameInverse, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · exact (contDiffAt_gramDiagOne_comp hF hdom).inv hrne
  · refine ContDiffAt.neg ?_
    refine contDiffAt_complex_div (hF 0 1)
      (((contDiffAt_gramDiagOne_comp hF hdom).mul (contDiffAt_gramDiagOne_comp hF hdom)).mul
        (contDiffAt_gramDiagTwo_comp hF hdom)) ?_
    exact mul_ne_zero (mul_ne_zero hrne hrne) htne
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact (contDiffAt_gramDiagTwo_comp hF hdom).inv htne
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact ((contDiffAt_gramDiagOne_comp hF hdom).mul
      (contDiffAt_gramDiagTwo_comp hF hdom)).inv (mul_ne_zero hrne htne)

end SmoothDomain

section Capstone

/-- **The trivialization is smooth.**  Every entry of the `SU(3)` coordinate is `C^∞` on an open
neighbourhood of the regular locus. -/
theorem contDiffOn_colorTransporterEntry (i j : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun X : ColorEventMatrix => colorTransporter X i j)
      colorSmoothDomain := by
  intro X hX
  refine ContDiffAt.contDiffWithinAt ?_
  have hF : ∀ a b : Fin 2, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun Y : ColorEventMatrix => colorGramMatrix Y a b) X :=
    fun a b => (contDiff_colorGramEntry a b).contDiffAt
  have hexp : (fun Y : ColorEventMatrix => colorTransporter Y i j)
      = fun Y => ∑ k : Fin 3,
          colorEventFrame Y i k * gramFrameInverse (colorGramMatrix Y) k j := by
    funext Y
    simp [colorTransporter, Matrix.mul_apply]
  rw [hexp]
  refine ContDiffAt.sum fun k _ => ?_
  exact (contDiff_colorEventFrameEntry i k).contDiffAt.mul
    (contDiffAt_gramFrameInverseEntry_comp hF hX k j)

/-- The Gram coordinate of the trivialization is globally smooth. -/
theorem contDiff_trivializationGramEntry (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun X : ColorEventMatrix => colorGramMatrix X i j :=
  contDiff_colorGramEntry i j

/-- **The inverse trivialization is smooth.**  Every entry of `(U, H) ↦ U · S(H)` is `C^∞` on the
open set where the record formulas are defined. -/
theorem contDiffOn_trivializationInverseEntry (i : Fin 3) (j : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ =>
        (p.1 * gramSection p.2) i j)
      (Set.univ ×ˢ gramSmoothDomain) := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  have hdom : p.2 ∈ gramSmoothDomain := hp.2
  have hF : ∀ a b : Fin 2, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ => q.2 a b) p :=
    fun a b => ((contDiff_matrixEntry a b).comp contDiff_snd).contDiffAt
  have hfirst : ∀ (a : Fin 3) (b : Fin 3), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ => q.1 a b) p :=
    fun a b => ((contDiff_matrixEntry a b).comp contDiff_fst).contDiffAt
  have hexp : (fun q : Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ =>
      (q.1 * gramSection q.2) i j)
      = fun q => ∑ k : Fin 3, q.1 i k * gramSection q.2 k j := by
    funext q
    simp [Matrix.mul_apply]
  rw [hexp]
  refine ContDiffAt.sum fun k _ => ?_
  exact (hfirst i k).mul (contDiffAt_gramSectionEntry_comp hF hdom k j)

end Capstone

end GaloisForLFunctions.HTGeometry