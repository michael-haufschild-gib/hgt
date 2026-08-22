import GaloisForLFunctions.HTGeometry.HaferkampFlattenedTerminalPhaseRank
import GaloisForLFunctions.HTGeometry.ObserverCriticalCarrierConfinementLaw
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Operator
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace BackwardsLightCone

theorem TerminalBlockPrefixAssembly.terminalPhaseTangentMap_injective
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    Function.Injective assembly.terminalPhaseTangentMap := by
  let D := assembly.terminalPhaseTangentMap
  have hLI : LinearIndependent ℝ (fun i : Fin labels.length =>
      D (Pi.single i 1)) := by
    change LinearIndependent ℝ (fun i : Fin labels.length =>
      assembly.terminalPhaseTangentMap (Pi.single i 1))
    have hT := assembly.linearIndependent_terminalPhaseTangents hlabels
    simpa [terminalPhaseTangentMap] using hT
  have hD : D.toLinearMap = Fintype.linearCombination ℝ
      (fun i : Fin labels.length => D (Pi.single i 1)) := by
    have hsingle (i : Fin labels.length) : D (Pi.single i 1) =
        Complex.I • haferkampUnitaryListCoordinateOutput assembly.liftedWord
          (assembly.terminalIndices i)
          (finitePauliMatrix (Function.update (fun _ => none) root (some 2))) := by
      simp [D, terminalPhaseTangentMap]
    apply LinearMap.ext
    intro x
    change (∑ i, x i • (Complex.I •
      haferkampUnitaryListCoordinateOutput assembly.liftedWord
        (assembly.terminalIndices i)
        (finitePauliMatrix (Function.update (fun _ => none) root (some 2))))) = _
    rw [Fintype.linearCombination_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsingle]
  rw [show (D : (Fin labels.length → ℝ) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      Fintype.linearCombination ℝ
        (fun i : Fin labels.length => D (Pi.single i 1)) by
          funext x
          exact DFunLike.congr_fun hD x]
  exact hLI.fintypeLinearCombination_injective

def TerminalBlockPrefixAssembly.terminalPhaseTangentLeftInverse
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ →L[ℝ] (Fin labels.length → ℝ) :=
  assembly.terminalPhaseTangentMap.toLinearMap.leftInverse.toContinuousLinearMap

theorem TerminalBlockPrefixAssembly.terminalPhaseTangentLeftInverse_comp
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    assembly.terminalPhaseTangentLeftInverse.comp
      assembly.terminalPhaseTangentMap =
      ContinuousLinearMap.id ℝ (Fin labels.length → ℝ) := by
  apply ContinuousLinearMap.ext
  intro x
  have hinj : Function.Injective assembly.terminalPhaseTangentMap :=
    TerminalBlockPrefixAssembly.terminalPhaseTangentMap_injective assembly hlabels
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot_of_injective hinj) x

def TerminalBlockPrefixAssembly.terminalPhaseObservedMap
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    EuclideanSpace ℝ (Fin labels.length) → EuclideanSpace ℝ (Fin labels.length) :=
  fun z => (EuclideanSpace.equiv (Fin labels.length) ℝ).symm
    (assembly.terminalPhaseTangentLeftInverse
      ((assembly.terminalPhaseLiftedWord
        ((EuclideanSpace.equiv (Fin labels.length) ℝ) z)).reverse.prod))

theorem TerminalBlockPrefixAssembly.analyticAt_terminalPhaseObservedMap
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (z : EuclideanSpace ℝ (Fin labels.length)) :
    AnalyticAt ℝ assembly.terminalPhaseObservedMap z := by
  let e : EuclideanSpace ℝ (Fin labels.length) →L[ℝ] (Fin labels.length → ℝ) :=
    (EuclideanSpace.equiv (Fin labels.length) ℝ).toContinuousLinearMap
  let einv : (Fin labels.length → ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin labels.length) :=
    (EuclideanSpace.equiv (Fin labels.length) ℝ).symm.toContinuousLinearMap
  let L := assembly.terminalPhaseTangentLeftInverse
  let C : (Fin labels.length → ℝ) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod
  have hC := assembly.analyticAt_terminalPhaseContraction (e z)
  have he : AnalyticAt ℝ (fun w => e w) z := e.analyticAt _
  have hCe := AnalyticAt.comp (f := fun w => e w) (g := C) hC he
  have hL : AnalyticAt ℝ (fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L M)
      (C (e z)) := L.analyticAt _
  have hLC := AnalyticAt.comp (f := fun w => C (e w))
    (g := fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L M) hL hCe
  have heinv : AnalyticAt ℝ (fun w => einv w) (L (C (e z))) := einv.analyticAt _
  have h := AnalyticAt.comp (f := fun w => L (C (e w)))
    (g := fun q : Fin labels.length → ℝ => einv q) heinv hLC
  exact h

theorem TerminalBlockPrefixAssembly.hasFDerivAt_terminalPhaseObservedMap_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    HasFDerivAt assembly.terminalPhaseObservedMap
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin labels.length))) 0 := by
  let e : EuclideanSpace ℝ (Fin labels.length) →L[ℝ] (Fin labels.length → ℝ) :=
    (EuclideanSpace.equiv (Fin labels.length) ℝ).toContinuousLinearMap
  let einv : (Fin labels.length → ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin labels.length) :=
    (EuclideanSpace.equiv (Fin labels.length) ℝ).symm.toContinuousLinearMap
  let D := assembly.terminalPhaseTangentMap
  let L := assembly.terminalPhaseTangentLeftInverse
  let C : (Fin labels.length → ℝ) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod
  have hC : HasFDerivAt C D (e 0) := by
    simpa [C, D, e] using assembly.hasFDerivAt_terminalPhaseContraction_zero
  have he : HasFDerivAt (fun w => e w) e 0 := e.hasFDerivAt
  have hCe := HasFDerivAt.comp (f := fun w => e w) (g := C) 0 hC he
  have hL : HasFDerivAt (fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L M)
      L (C (e 0)) := L.hasFDerivAt
  have hLC := HasFDerivAt.comp (f := fun w => C (e w))
    (g := fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L M) 0 hL hCe
  have heinv : HasFDerivAt (fun w => einv w) einv (L (C (e 0))) := einv.hasFDerivAt
  have h := HasFDerivAt.comp (f := fun w => L (C (e w)))
    (g := fun q : Fin labels.length → ℝ => einv q) 0 heinv hLC
  have hLD : L.comp D = ContinuousLinearMap.id ℝ (Fin labels.length → ℝ) := by
    exact assembly.terminalPhaseTangentLeftInverse_comp hlabels
  have hderiv : einv.comp (L.comp (D.comp e)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin labels.length)) := by
    apply ContinuousLinearMap.ext
    intro z
    change einv (L (D (e z))) = z
    rw [show L (D (e z)) = e z by
      exact DFunLike.congr_fun hLD (e z)]
    exact (EuclideanSpace.equiv (Fin labels.length) ℝ).symm_apply_apply z
  rw [show assembly.terminalPhaseObservedMap =
      (fun z => einv (L (C (e z)))) by rfl]
  exact h.congr_fderiv hderiv

theorem TerminalBlockPrefixAssembly.observedPhaseCriticalSet_volume_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    volume {z | ¬ Function.Surjective
      (fderiv ℝ assembly.terminalPhaseObservedMap z)} = 0 := by
  let u : Fin labels.length → EuclideanSpace ℝ (Fin labels.length) :=
    fun i => (EuclideanSpace.equiv (Fin labels.length) ℝ).symm (Pi.single i 1)
  have hF : AnalyticOnNhd ℝ assembly.terminalPhaseObservedMap Set.univ := by
    intro z _
    exact assembly.analyticAt_terminalPhaseObservedMap z
  have hderiv := assembly.hasFDerivAt_terminalPhaseObservedMap_zero hlabels |>.fderiv
  have hminor : (observerMinor
      (fun z => fderiv ℝ assembly.terminalPhaseObservedMap z) u 0).det ≠ 0 := by
    unfold observerMinor
    change (Matrix.det fun i j =>
      (fderiv ℝ assembly.terminalPhaseObservedMap 0) (u j) i) ≠ 0
    rw [hderiv]
    have hmatrix : (fun i j =>
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin labels.length))) (u j) i) =
        (1 : Matrix (Fin labels.length) (Fin labels.length) ℝ) := by
      dsimp [u]
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    rw [hmatrix, Matrix.det_one]
    exact one_ne_zero
  exact analytic_observer_criticalSet_volume_zero hF u hminor

def TerminalBlockPrefixAssembly.terminalPhaseEuclideanChart
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    EuclideanSpace ℝ (Fin labels.length) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun z => (assembly.terminalPhaseLiftedWord
    ((EuclideanSpace.equiv (Fin labels.length) ℝ) z)).reverse.prod

def TerminalBlockPrefixAssembly.terminalPhaseObserverOutput
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ →L[ℝ]
      EuclideanSpace ℝ (Fin labels.length) :=
  (EuclideanSpace.equiv (Fin labels.length) ℝ).symm.toContinuousLinearMap.comp
    assembly.terminalPhaseTangentLeftInverse

theorem TerminalBlockPrefixAssembly.analyticAt_terminalPhaseEuclideanChart
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (z : EuclideanSpace ℝ (Fin labels.length)) :
    AnalyticAt ℝ assembly.terminalPhaseEuclideanChart z := by
  let e : EuclideanSpace ℝ (Fin labels.length) →L[ℝ] (Fin labels.length → ℝ) :=
    (EuclideanSpace.equiv (Fin labels.length) ℝ).toContinuousLinearMap
  let C : (Fin labels.length → ℝ) →
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun x => (assembly.terminalPhaseLiftedWord x).reverse.prod
  have hC := assembly.analyticAt_terminalPhaseContraction (e z)
  have he : AnalyticAt ℝ (fun w => e w) z := e.analyticAt _
  have h := AnalyticAt.comp (f := fun w => e w) (g := C) hC he
  exact h

theorem TerminalBlockPrefixAssembly.fderiv_observed_eq_output_comp_fderiv_chart
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (z : EuclideanSpace ℝ (Fin labels.length)) :
    fderiv ℝ assembly.terminalPhaseObservedMap z =
      assembly.terminalPhaseObserverOutput.comp
        (fderiv ℝ assembly.terminalPhaseEuclideanChart z) := by
  let C := assembly.terminalPhaseEuclideanChart
  let L := assembly.terminalPhaseObserverOutput
  have hC : HasFDerivAt C (fderiv ℝ C z) z :=
    (assembly.analyticAt_terminalPhaseEuclideanChart z).differentiableAt.hasFDerivAt
  have hL : HasFDerivAt (fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L M)
      L (C z) := L.hasFDerivAt
  have h := HasFDerivAt.comp
    (f := C) (g := fun M : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => L M) z hL hC
  rw [show assembly.terminalPhaseObservedMap = fun z => L (C z) by rfl]
  exact h.fderiv

theorem finrank_range_comp_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : X →L[ℝ] Y) (C : Y →L[ℝ] Z) :
    Module.finrank ℝ (C.comp A).range ≤ Module.finrank ℝ A.range := by
  let g : A.range →ₗ[ℝ] Z := C.toLinearMap.domRestrict A.range
  have hrange : (C.comp A).toLinearMap.range = g.range := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨⟨A x, ⟨x, rfl⟩⟩, hx⟩
    · rintro ⟨x, hx⟩
      rcases x with ⟨x, ⟨w, hw⟩⟩
      change C x = z at hx
      rw [← hw] at hx
      exact ⟨w, hx⟩
  rw [show (C.comp A).range = (C.comp A).toLinearMap.range by rfl, hrange]
  exact LinearMap.finrank_range_le g

theorem TerminalBlockPrefixAssembly.finrank_chart_fderiv_of_surjective_observer_fderiv
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {pre : Matrix.unitaryGroup (Fin n → Bool) ℂ}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone pre labels)
    (z : EuclideanSpace ℝ (Fin labels.length))
    (hsurj : Function.Surjective (fderiv ℝ assembly.terminalPhaseObservedMap z)) :
    labels.length ≤ Module.finrank ℝ
      (fderiv ℝ assembly.terminalPhaseEuclideanChart z).range := by
  let A := fderiv ℝ assembly.terminalPhaseEuclideanChart z
  let C := assembly.terminalPhaseObserverOutput
  have hderiv : fderiv ℝ assembly.terminalPhaseObservedMap z = C.comp A := by
    exact assembly.fderiv_observed_eq_output_comp_fderiv_chart z
  have htop : (C.comp A).toLinearMap.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    rw [← hderiv]
    exact hsurj
  calc
    labels.length = Module.finrank ℝ (EuclideanSpace ℝ (Fin labels.length)) := by
      simp
    _ = Module.finrank ℝ (C.comp A).range := by
      rw [show (C.comp A).range = (C.comp A).toLinearMap.range by rfl, htop,
        finrank_top]
    _ ≤ Module.finrank ℝ A.range := finrank_range_comp_le A C

theorem TerminalBlockPrefixAssembly.euclideanPhaseChart_lowRank_volume_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i))) :
    volume {z | Module.finrank ℝ
      (fderiv ℝ assembly.terminalPhaseEuclideanChart z).range < labels.length} = 0 := by
  apply measure_mono_null (t := {z | ¬ Function.Surjective
      (fderiv ℝ assembly.terminalPhaseObservedMap z)})
  · intro z hz hsurj
    exact (not_lt_of_ge
      (assembly.finrank_chart_fderiv_of_surjective_observer_fderiv z hsurj)) hz
  · exact assembly.observedPhaseCriticalSet_volume_zero hlabels

theorem TerminalBlockPrefixAssembly.euclideanPhaseChart_lowRank_measure_zero
    {n : ℕ} {edges : List (Fin n × Fin n)} {root : Fin n}
    {cone : BackwardsLightCone n edges root}
    {labels : List (Fin n → Option (Fin 3))}
    (assembly : TerminalBlockPrefixAssembly cone 1 labels)
    (hlabels : LinearIndependent ℂ (fun i : Fin labels.length =>
      finitePauliMatrix (labels.get i)))
    {μ : Measure (EuclideanSpace ℝ (Fin labels.length))}
    (hμ : μ ≪ volume) :
    μ {z | Module.finrank ℝ
      (fderiv ℝ assembly.terminalPhaseEuclideanChart z).range < labels.length} = 0 :=
  hμ (assembly.euclideanPhaseChart_lowRank_volume_zero hlabels)

end BackwardsLightCone

end

end GaloisForLFunctions.HTGeometry
