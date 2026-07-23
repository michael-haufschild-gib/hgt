import GaloisForLFunctions.RHTower.CCMSingularLoewnerPoleForcing
import GaloisForLFunctions.RHTower.CCMSourcePencilRadicalEvans

/-!
# CCM source-descent Evans-pole universality law

The singular Loewner law locates a real quotient pole from strict descent of the source between
two clock nodes.  The radical Evans law identifies the same quotient determinant with the first
surviving coefficient of a kernel-vector-free ambient source pencil.  Their conjunction removes
the quotient frame, right inverse, and selected radical vector from the detected pole: strict
source descent forces a zero of an explicit divided-difference source-pencil coefficient.
-/

open Complex Set
open scoped Matrix

namespace RHTower

noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- Matrix-vector multiplication commutes with real-to-complex scalar extension. -/
theorem realMatrix_mulVec_map_complex
    (M : Matrix n n ℝ) (v : n → ℝ) :
    (fun i => ((M *ᵥ v) i : ℂ)) =
      M.map (algebraMap ℝ ℂ) *ᵥ (fun i => (v i : ℂ)) := by
  funext i
  change ((∑ j, M i j * v j : ℝ) : ℂ) =
    ∑ j, (M i j : ℂ) * (v j : ℂ)
  push_cast
  rfl

omit [DecidableEq n] in
/-- Real active-even completion commutes with complexification and becomes the complex CCM source
completion in the constant-boundary channel. -/
theorem ccmEvenBoundaryCompletion_map_complex
    (D : Matrix n n ℝ) (eta e : n → ℝ) :
    (ccmEvenBoundaryCompletion D eta e).map (algebraMap ℝ ℂ) =
      ccmSourceCompletion (D.map (algebraMap ℝ ℂ))
        (fun i => (e i : ℂ)) (fun i => (eta i : ℂ)) := by
  have hmul := realMatrix_mulVec_map_complex D e
  ext i j
  change ((D i j - (D *ᵥ e) i * eta j : ℝ) : ℂ) =
    (D i j : ℂ) -
      (D.map (algebraMap ℝ ℂ) *ᵥ (fun i => (e i : ℂ))) i *
        star (eta j : ℂ)
  push_cast
  rw [congrFun hmul i]
  simp

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Split quotient compression commutes with complexification. -/
theorem realSemimetricQuotientCompression_map_complex
    (B : Matrix m n ℝ) (A : Matrix n n ℝ) (R : Matrix n m ℝ) :
    (realSemimetricQuotientCompression B A R).map (algebraMap ℝ ℂ) =
      HTGeometry.splitQuotientCompression
        (B.map (algebraMap ℝ ℂ)) (A.map (algebraMap ℝ ℂ))
          (R.map (algebraMap ℝ ℂ)) := by
  rw [realSemimetricQuotientCompression, HTGeometry.splitQuotientCompression,
    Matrix.map_mul, Matrix.map_mul]

/-- **CCM source-descent Evans-pole universality law.**  Strict descent of any active-even CCM
source between ordered clock nodes forces a real zero, in that clock interval, of the first
surviving radical coefficient of the explicit complexified source pencil.  The asserted zero no
longer mentions a radical vector, a quotient compression, or its right inverse. -/
theorem ccmActiveEven_sourceDescent_forces_sourcePencilCoeff_zero
    (clock source diagonal : n → ℝ) (e : n → ℝ)
    (hclock : Function.Injective clock)
    (he : ccmDividedDifferenceMatrix clock source diagonal *ᵥ e = 0)
    (heta : ccmConstantBoundary ⬝ᵥ e = 1)
    (hbeta : source ⬝ᵥ e = 0)
    (B : Matrix m n ℝ) (R : Matrix n m ℝ)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hBR : B * R = 1)
    (hGram : B.transpose * B = ccmDividedDifferenceMatrix clock source diagonal)
    (i j : n) (hij : i ≠ j) (hclockij : clock i < clock j)
    (hsourceij : source j < source i) :
    ∃ x : ℝ, x ∈ Set.Icc (clock i) (clock j) ∧
      let T := (ccmDividedDifferenceMatrix clock source diagonal).map
        (algebraMap ℝ ℂ)
      let D := (ccmDiagonalClock clock).map (algebraMap ℝ ℂ)
      let eta : n → ℂ := fun _ => 1
      let beta : n → ℂ := fun q => source q
      ((T * (D - (x : ℂ) • 1) + Matrix.vecMulVec beta (star eta)).charpoly).coeff
          (Fintype.card n - Fintype.card m) = 0 := by
  obtain ⟨x, hx, hroot⟩ :=
    ccmActiveEven_sourceDescent_forces_quotientCharpoly_zero
      clock source diagonal e hclock he heta hbeta B R hBR hGram
        i j hij hclockij hsourceij
  refine ⟨x, hx, ?_⟩
  dsimp only
  let Q := ccmDividedDifferenceMatrix clock source diagonal
  let Dreal := ccmDiagonalClock clock
  let Areal := ccmEvenBoundaryCompletion Dreal ccmConstantBoundary e
  let Bc := B.map (algebraMap ℝ ℂ)
  let Rc := R.map (algebraMap ℝ ℂ)
  let T := Q.map (algebraMap ℝ ℂ)
  let D := Dreal.map (algebraMap ℝ ℂ)
  let ec : n → ℂ := fun q => e q
  let eta : n → ℂ := fun _ => 1
  let beta : n → ℂ := fun q => source q
  let A := ccmSourceCompletion D ec eta
  have hQtranspose : Q.transpose = Q := by
    exact ccmDividedDifferenceMatrix_transpose clock source diagonal
  have hDtranspose : Dreal.transpose = Dreal := ccmDiagonalClock_transpose clock
  have hdisp : Dreal * Q - Q * Dreal =
      Matrix.vecMulVec source ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary source :=
    ccmDividedDifference_displacement clock source diagonal hclock
  have hactive := ccmEvenBoundaryCompletion_active
    Q Dreal ccmConstantBoundary source e hQtranspose hDtranspose hdisp he heta hbeta
  have hradicalReal : B * Areal * (1 - R * B) = 0 := by
    apply realMetricAdjoint_splitRadical B Areal R hBR
    simpa only [Areal, Q, hGram] using hactive.1
  have hBRc : Bc * Rc = 1 := by
    have hmap := congrArg (fun M : Matrix m m ℝ => M.map (algebraMap ℝ ℂ)) hBR
    simpa only [Matrix.map_mul, Matrix.map_one, map_zero, map_one, Bc, Rc] using hmap
  have hBcStar : Bcᴴ = (B.transpose).map (algebraMap ℝ ℂ) := by
    ext q r
    simp [Bc]
  have hGramC : Bcᴴ * Bc = T := by
    rw [hBcStar, ← Matrix.map_mul]
    simp [T, Q, hGram]
  have hAmap : Areal.map (algebraMap ℝ ℂ) = A := by
    simpa only [Areal, A, D, Dreal, ec, eta] using
      ccmEvenBoundaryCompletion_map_complex Dreal ccmConstantBoundary e
  have hradical : Bc * A * (1 - Rc * Bc) = 0 := by
    have hmap := congrArg
      (fun M : Matrix m n ℝ => M.map (algebraMap ℝ ℂ)) hradicalReal
    change (B * Areal * (1 - R * B)).map (algebraMap ℝ ℂ) =
      (0 : Matrix m n ℝ).map (algebraMap ℝ ℂ) at hmap
    rw [Matrix.map_mul, Matrix.map_mul,
      Matrix.map_sub _ (map_sub _), Matrix.map_mul] at hmap
    have hone : (1 : Matrix n n ℝ).map (algebraMap ℝ ℂ) = 1 := by
      ext q r
      by_cases hqr : q = r
      · subst r
        simp
      · simp [hqr]
    have hzero : (0 : Matrix m n ℝ).map (algebraMap ℝ ℂ) = 0 := by
      ext q r
      simp
    rw [hone, hzero, hAmap] at hmap
    exact hmap
  have hboundaryReal : Q *ᵥ (Dreal *ᵥ e) = -source :=
    ccmEvenBoundary_source Q Dreal ccmConstantBoundary source e hdisp he heta hbeta
  have hboundary : T *ᵥ (D *ᵥ ec) = -beta := by
    have hDmap := realMatrix_mulVec_map_complex Dreal e
    have hQmap := realMatrix_mulVec_map_complex Q (Dreal *ᵥ e)
    calc
      T *ᵥ (D *ᵥ ec) =
          T *ᵥ (fun q => ((Dreal *ᵥ e) q : ℂ)) := by
            rw [hDmap]
      _ = fun q => ((Q *ᵥ (Dreal *ᵥ e)) q : ℂ) := by
            exact hQmap.symm
      _ = -beta := by
            rw [hboundaryReal]
            ext q
            simp [beta]
  have hcoeff := ccmSourceCompletion_sourcePencil_lowestCoeff
    T D ec eta beta Bc Rc (x : ℂ) hle hGramC hradical hboundary
  have hquotient :
      HTGeometry.splitQuotientCompression Bc A Rc =
        (realSemimetricQuotientCompression B Areal R).map (algebraMap ℝ ℂ) := by
    rw [← hAmap]
    exact (realSemimetricQuotientCompression_map_complex B Areal R).symm
  have hroot' :
      ((realSemimetricQuotientCompression B Areal R).map
        (algebraMap ℝ ℂ)).charpoly.eval (x : ℂ) = 0 := by
    simpa only [Areal, Dreal] using hroot
  have hdet : Matrix.det
      (HTGeometry.splitQuotientCompression Bc A Rc - (x : ℂ) • 1) = 0 := by
    rw [hquotient]
    rw [Matrix.eval_charpoly] at hroot'
    have hneg :
        (realSemimetricQuotientCompression B Areal R).map (algebraMap ℝ ℂ) -
            (x : ℂ) • 1 =
          -(Matrix.scalar m (x : ℂ) -
            (realSemimetricQuotientCompression B Areal R).map (algebraMap ℝ ℂ)) := by
      ext q r
      by_cases hqr : q = r <;> simp [Matrix.scalar, hqr]
    rw [hneg, Matrix.det_neg, hroot', mul_zero]
  rw [hdet, zero_mul] at hcoeff
  simpa only [T, D, eta, beta] using hcoeff

end

end RHTower
