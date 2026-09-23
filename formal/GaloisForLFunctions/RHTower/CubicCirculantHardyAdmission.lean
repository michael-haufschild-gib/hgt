import GaloisForLFunctions.RHTower.CubicFiniteChannelHardySource
import GaloisForLFunctions.RHTower.CubicCirculantSourceCurrent
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Hardy admission of the literal amplitude-retaining circulant source

A smooth nowhere-zero complex function, constant outside a compact set, is encoded
pointwise by the previously constructed six-channel projection family. Smoothness,
Schwartz admission, source flatness, and exact recovery are proved for that same
family. Hardy rounding then gives genuine projections and the ordinary cubic trace
of the literal matrix first-jet current, with coefficient i/(4*pi).

The two-copy phase-winding integral and arithmetic contour specialization remain
separate obligations. No zero count, trace value, RH, or source budget is assumed.
-/

open MeasureTheory ContinuousLinearMap
open scoped BigOperators ComplexConjugate Kronecker ContDiff
noncomputable section
namespace RHTower

def cubicSmoothConstantSymbol (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport (fun x => f x-c)) : CubicSymbols :=
  cubicConstSchwartzSymbol c (hc.toSchwartzMap (hf.sub contDiff_const))

@[simp] theorem cubicSmoothConstantSymbol_apply (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport (fun x => f x-c)) (x : ℝ) :
    cubicSmoothConstantSymbol f c hf hc x = f x := by
  rw [cubicSmoothConstantSymbol, cubicConstSchwartzSymbol_apply]
  change c+(f x-c)=f x
  ring

theorem cubicSmoothConstantSymbol_admissible (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport (fun x => f x-c)) :
    CubicSchwartzAdmissible (cubicSmoothConstantSymbol f c hf hc) :=
  ⟨c, hc.toSchwartzMap (hf.sub contDiff_const), rfl⟩

/-- Pointwise source encoding preserves the same compact deviation set. -/
theorem cubic_source_compact_deviation {f : ℝ → ℂ} {c : ℂ}
    (hf : HasCompactSupport (fun x => f x-c)) (F : ℂ → ℂ) :
    HasCompactSupport (fun x => F (f x)-F c) := by
  have h := hf.comp_left (g := fun z => F (z+c)-F c) (by simp)
  simpa only [Function.comp_def, sub_add_cancel] using h

def cyclicFaithfulSourceProjection (t b : ℝ) (z : ℂ) (j : Fin 3) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  cyclicAmplitudeGraph ‖z‖ ⊗ₖ cyclicFrameProjection (t:ℂ)
    ((b:ℂ)*(z/(‖z‖:ℂ))) (conj ((b:ℂ)*(z/(‖z‖:ℂ)))) j

theorem cyclicFaithfulSourceProjection_orthogonal (t b : ℝ)
    (hnorm : t^(2 : ℕ)+b^(2 : ℕ)=1) {z : ℂ} (hz : z ≠ 0) (j : Fin 3) :
    let P := cyclicFaithfulSourceProjection t b z j
    P*P=P ∧ P.conjTranspose=P := by
  apply cyclicAmplitudeGraph_projection_lift
  have hncomplex : (t:ℂ)^(2 : ℕ)+(b:ℂ)^(2 : ℕ)=1 := by exact_mod_cast hnorm
  have hphase := cyclicSource_phase_unit hz
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination hncomplex + (b:ℂ)^(2 : ℕ)*hphase

private theorem cubicCirculant_smooth {f g h : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => cubicCirculant (f x) (g x) (h x) i j) := by
  fin_cases i <;> fin_cases j <;> simpa [cubicCirculant, Matrix.cons_val_two] using
    (by first | exact hf | exact hg | exact hh)

theorem cyclicFaithfulSourceProjection_smooth (t b : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (j : Fin 3) (i k : Fin 2 × Fin 3) :
    ContDiff ℝ ∞ (fun x => cyclicFaithfulSourceProjection t b (f x) j i k) := by
  have hn : ContDiff ℝ ∞ (fun x => (‖f x‖:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf.norm ℂ hz)
  have hne (x : ℝ) : (‖f x‖:ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (hz x)
  have hu : ContDiff ℝ ∞ (fun x => (b:ℂ)*(f x/(‖f x‖:ℂ))) := by
    simp only [div_eq_mul_inv]
    exact contDiff_const.mul (hf.mul (hn.inv hne))
  have hv : ContDiff ℝ ∞ (fun x => conj ((b:ℂ)*(f x/(‖f x‖:ℂ)))) :=
    Complex.conjCLE.contDiff.comp hu
  have hd (x : ℝ) : 1+(‖f x‖:ℂ)^(2 : ℕ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0:ℝ)<1+‖f x‖^(2 : ℕ)))
  have hden : ContDiff ℝ ∞ (fun x => (1+(‖f x‖:ℂ)^(2 : ℕ))⁻¹) :=
    (contDiff_const.add (hn.pow 2)).inv hd
  have hgraph (i k : Fin 2) :
      ContDiff ℝ ∞ (fun x => cyclicAmplitudeGraph ‖f x‖ i k) := by
    fin_cases i <;> fin_cases k <;>
      simp only [cyclicAmplitudeGraph, div_eq_mul_inv, one_mul]
    · exact hden
    · exact hn.mul hden
    · exact hn.mul hden
    · exact (hn.pow 2).mul hden
  exact (hgraph i.1 k.1).mul
    ((cubicCirculant_smooth contDiff_const hu contDiff_const i.2 j).mul
      (cubicCirculant_smooth contDiff_const contDiff_const hv j k.2))

def cyclicFaithfulSourceSymbol (t b : ℝ) (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) (j : Fin 3) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) CubicSymbols :=
  fun i k => cubicSmoothConstantSymbol
    (fun x => cyclicFaithfulSourceProjection t b (f x) j i k)
    (cyclicFaithfulSourceProjection t b c j i k)
    (cyclicFaithfulSourceProjection_smooth t b hf hz j i k)
    (cubic_source_compact_deviation hc (fun z => cyclicFaithfulSourceProjection t b z j i k))

@[simp] theorem cyclicFaithfulSourceSymbol_apply (t b : ℝ) (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) (j : Fin 3)
    (i k : Fin 2 × Fin 3) (x : ℝ) :
    cyclicFaithfulSourceSymbol t b f c hf hz hc j i k x =
      cyclicFaithfulSourceProjection t b (f x) j i k :=
  cubicSmoothConstantSymbol_apply _ _ _ _ _

theorem cyclicFaithfulSourceSymbol_admissible (t b : ℝ) (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) (j : Fin 3)
    (i k : Fin 2 × Fin 3) :
    CubicSchwartzAdmissible (cyclicFaithfulSourceSymbol t b f c hf hz hc j i k) :=
  cubicSmoothConstantSymbol_admissible _ _ _ _

theorem cyclicFaithfulSourceProjection_sum (t b : ℝ)
    (hnorm : t^(2 : ℕ)+b^(2 : ℕ)=1) {z : ℂ} (hz : z ≠ 0) :
    cyclicFaithfulSourceProjection t b z 0 + cyclicFaithfulSourceProjection t b z 1 +
      cyclicFaithfulSourceProjection t b z 2 = cyclicFaithfulSourceAggregate (t*b) z := by
  let u : ℂ := (b:ℂ)*(z/(‖z‖:ℂ))
  have hncomplex : (t:ℂ)^(2 : ℕ)+(b:ℂ)^(2 : ℕ)=1 := by exact_mod_cast hnorm
  have hu : (t:ℂ)^(2 : ℕ)+u*conj u=1 := by
    dsimp [u]
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination hncomplex + (b:ℂ)^(2 : ℕ)*(cyclicSource_phase_unit hz)
  have hs := congrArg (fun M => cyclicAmplitudeGraph ‖z‖ ⊗ₖ M)
    (cyclicFrameProjection_sum (t:ℂ) u (conj u) hu)
  simpa [cyclicFaithfulSourceProjection, Matrix.kronecker_add,
    cyclicFaithfulSourceAggregate, u, map_mul, mul_assoc] using hs

theorem cyclicFaithfulSourceProjection_flat (t b : ℝ)
    (hnorm : t^(2 : ℕ)+b^(2 : ℕ)=1) {z : ℂ} (hz : z ≠ 0) :
    let P := cyclicFaithfulSourceProjection t b z
    let S := P 0+P 1+P 2
    let K := (P 0*P 1-P 1*P 0)+(P 1*P 2-P 2*P 1)+(P 2*P 0-P 0*P 2)
    S*K=K*S := by
  let E := cyclicAmplitudeGraph ‖z‖
  let u : ℂ := (b:ℂ)*(z/(‖z‖:ℂ))
  have hncomplex : (t:ℂ)^(2 : ℕ)+(b:ℂ)^(2 : ℕ)=1 := by exact_mod_cast hnorm
  have hu : (t:ℂ)^(2 : ℕ)+u*conj u=1 := by
    dsimp [u]
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination hncomplex + (b:ℂ)^(2 : ℕ)*(cyclicSource_phase_unit hz)
  have hm (M N : Matrix (Fin 3) (Fin 3) ℂ) : (E⊗ₖM)*(E⊗ₖN)=E⊗ₖ(M*N) := by
    rw [← Matrix.mul_kronecker_mul, cyclicAmplitudeGraph_idempotent]
  have hs (M N : Matrix (Fin 3) (Fin 3) ℂ) : E⊗ₖ(M-N)=E⊗ₖM-E⊗ₖN := by
    ext i j
    simp [Matrix.kroneckerMap_apply, mul_sub]
  dsimp only [E] at hm hs
  dsimp only [cyclicFaithfulSourceProjection]
  simp only [hm, ← hs, ← Matrix.kronecker_add]
  apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => E⊗ₖM)
  change (cyclicFrameProjection (t:ℂ) u (conj u) 0+
      cyclicFrameProjection (t:ℂ) u (conj u) 1+cyclicFrameProjection (t:ℂ) u (conj u) 2)*
      (cyclicTripleCurrent (cyclicFrameProjection (t:ℂ) u (conj u) 0)
        (cyclicFrameProjection (t:ℂ) u (conj u) 1)
        (cyclicFrameProjection (t:ℂ) u (conj u) 2)) =
      (cyclicTripleCurrent (cyclicFrameProjection (t:ℂ) u (conj u) 0)
        (cyclicFrameProjection (t:ℂ) u (conj u) 1)
        (cyclicFrameProjection (t:ℂ) u (conj u) 2))*
      (cyclicFrameProjection (t:ℂ) u (conj u) 0+
        cyclicFrameProjection (t:ℂ) u (conj u) 1+cyclicFrameProjection (t:ℂ) u (conj u) 2)
  rw [cyclicFrameProjection_sum _ _ _ hu, cyclicFrameProjection_current _ _ _ hu,
    cyclicSource_flat]

section SymbolEvaluation
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem cubicFiniteSymbolValue_mul (A B : Matrix n n CubicSymbols) (x : ℝ) :
    cubicFiniteSymbolValue (A*B) x = cubicFiniteSymbolValue A x * cubicFiniteSymbolValue B x := by
  ext i j
  simp [cubicFiniteSymbolValue, Matrix.mul_apply]

omit [Fintype n] [DecidableEq n] in
theorem cubicFiniteSymbolValue_add (A B : Matrix n n CubicSymbols) (x : ℝ) :
    cubicFiniteSymbolValue (A+B) x = cubicFiniteSymbolValue A x + cubicFiniteSymbolValue B x := rfl

omit [Fintype n] [DecidableEq n] in
theorem cubicFiniteSymbolValue_sub (A B : Matrix n n CubicSymbols) (x : ℝ) :
    cubicFiniteSymbolValue (A-B) x = cubicFiniteSymbolValue A x - cubicFiniteSymbolValue B x := rfl

omit [Fintype n] [DecidableEq n] in
theorem cubicFiniteSymbolValue_conjTranspose (A : Matrix n n CubicSymbols) (x : ℝ) :
    cubicFiniteSymbolValue A.conjTranspose x = (cubicFiniteSymbolValue A x).conjTranspose := rfl

omit [Fintype n] [DecidableEq n] in
theorem cubicFiniteSymbolValue_injective (A B : Matrix n n CubicSymbols)
    (h : ∀ x, cubicFiniteSymbolValue A x = cubicFiniteSymbolValue B x) : A=B := by
  apply Matrix.ext
  intro i j
  apply BoundedContinuousFunction.ext
  intro x
  exact congrFun (congrFun (h x) i) j

end SymbolEvaluation

set_option maxHeartbeats 400000 in
/-- The same literal source family has genuine Hardy admission; no independent admission field
is postulated. Every coefficient is obtained by pointwise evaluation of the input function. -/
theorem cyclicFaithfulSourceSymbol_orthogonal_flat (t b : ℝ) (hnorm : t^(2 : ℕ)+b^(2 : ℕ)=1)
    (f : ℝ → ℂ) (c : ℂ) (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) :
    let P := cyclicFaithfulSourceSymbol t b f c hf hz hc
    (∀ j, P j*P j=P j ∧ (P j).conjTranspose=P j) ∧
    (P 0+P 1+P 2)*cubicFiniteSourceCurrent (P 0) (P 1) (P 2) =
      cubicFiniteSourceCurrent (P 0) (P 1) (P 2)*(P 0+P 1+P 2) := by
  let P := cyclicFaithfulSourceSymbol t b f c hf hz hc
  have heval (j : Fin 3) (x : ℝ) :
      cubicFiniteSymbolValue (P j) x = cyclicFaithfulSourceProjection t b (f x) j := by
    ext i k
    exact cyclicFaithfulSourceSymbol_apply _ _ _ _ _ _ _ _ _ _ _
  change (∀ j, P j*P j=P j ∧ (P j).conjTranspose=P j) ∧
    (P 0+P 1+P 2)*cubicFiniteSourceCurrent (P 0) (P 1) (P 2) =
      cubicFiniteSourceCurrent (P 0) (P 1) (P 2)*(P 0+P 1+P 2)
  constructor
  · intro j
    constructor
    · apply cubicFiniteSymbolValue_injective
      intro x
      rw [cubicFiniteSymbolValue_mul, heval]
      exact (cyclicFaithfulSourceProjection_orthogonal t b hnorm (hz x) j).1
    · apply cubicFiniteSymbolValue_injective
      intro x
      rw [cubicFiniteSymbolValue_conjTranspose, heval]
      exact (cyclicFaithfulSourceProjection_orthogonal t b hnorm (hz x) j).2
  · apply cubicFiniteSymbolValue_injective
    intro x
    simp only [cubicFiniteSourceCurrent]
    simp only [cubicFiniteSymbolValue_mul, cubicFiniteSymbolValue_add,
      cubicFiniteSymbolValue_sub, heval]
    exact cyclicFaithfulSourceProjection_flat t b hnorm (hz x)

theorem cyclicFaithfulSourceSymbol_recovery (t b : ℝ) (hnorm : t^(2 : ℕ)+b^(2 : ℕ)=1)
    (hne : t*b ≠ 0) (f : ℝ → ℂ) (c : ℂ)
    (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) (x : ℝ) :
    let A := cyclicFaithfulSourceSymbol t b f c hf hz hc
    cyclicFaithfulSourceRecover (t*b) (cubicFiniteSymbolValue (A 0+A 1+A 2) x) = f x := by
  have heval (j : Fin 3) :
      cubicFiniteSymbolValue (cyclicFaithfulSourceSymbol t b f c hf hz hc j) x =
        cyclicFaithfulSourceProjection t b (f x) j := by
    ext i k
    exact cyclicFaithfulSourceSymbol_apply _ _ _ _ _ _ _ _ _ _ _
  dsimp only
  rw [cubicFiniteSymbolValue_add, cubicFiniteSymbolValue_add, heval, heval, heval,
    cyclicFaithfulSourceProjection_sum t b hnorm (hz x), cyclicFaithfulSourceRecover_eq _ hne]

theorem exists_rounded_faithful_circulant_source (t b : ℝ) (hnorm : t^(2 : ℕ)+b^(2 : ℕ)=1)
    (hne : t*b ≠ 0)
    (f : ℝ → ℂ) (c : ℂ) (hf : ContDiff ℝ ∞ f) (hz : ∀ x, f x ≠ 0)
    (hc : HasCompactSupport (fun x => f x-c)) :
    let A := cyclicFaithfulSourceSymbol t b f c hf hz hc
    (∀ x, cyclicFaithfulSourceRecover (t*b) (cubicFiniteSymbolValue (A 0+A 1+A 2) x) = f x) ∧
    ∃ P Q R : CubicFiniteChannel (Fin 2 × Fin 3) SoninL2 →L[ℂ]
        CubicFiniteChannel (Fin 2 × Fin 3) SoninL2,
      IsSelfAdjoint P ∧ IsSelfAdjoint Q ∧ IsSelfAdjoint R ∧
      IsIdempotentElem P ∧ IsIdempotentElem Q ∧ IsIdempotentElem R ∧
      MemSchattenClass 1 (P-cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 0)*cubicFiniteHardyCutoff) ∧
      MemSchattenClass 1 (Q-cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 1)*cubicFiniteHardyCutoff) ∧
      MemSchattenClass 1 (R-cubicFiniteHardyCutoff*cubicFiniteMatrixMultiplier (A 2)*cubicFiniteHardyCutoff) ∧
      MemSchattenClass 1 (formationAnchoredCubicAssociator R Q P) ∧
      opTrace (formationAnchoredCubicAssociator R Q P) =
        (Complex.I / (4 * (Real.pi : ℂ))) *
          ∫ x : ℝ, Matrix.trace (cubicFiniteSymbolValue (A 0+A 1+A 2) x *
            cubicFiniteSymbolJet (cubicFiniteSourceCurrent (A 0) (A 1) (A 2)) x) := by
  have h := cyclicFaithfulSourceSymbol_orthogonal_flat t b hnorm f c hf hz hc
  refine ⟨cyclicFaithfulSourceSymbol_recovery t b hnorm hne f c hf hz hc, ?_⟩
  exact exists_rounded_finiteSource_cubic_with_local_charge _ _ _
    (h.1 0).1 (h.1 1).1 (h.1 2).1 (h.1 0).2 (h.1 1).2 (h.1 2).2
    (cyclicFaithfulSourceSymbol_admissible t b f c hf hz hc 0)
    (cyclicFaithfulSourceSymbol_admissible t b f c hf hz hc 1)
    (cyclicFaithfulSourceSymbol_admissible t b f c hf hz hc 2) h.2

end RHTower

