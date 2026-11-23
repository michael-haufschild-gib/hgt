import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.CoordinateCost
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.ProductMoment

/-! # Concentration of fixed-error gate count among physical spectral phases -/
open Matrix MeasureTheory ProbabilityTheory Set Real
open scoped Classical Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseFluctuations
open DiagonalSynthesis
noncomputable section
private abbrev Config (n : ℕ) := Fin n → Bool
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private theorem cap {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) (x : Fin d → UnitAddCircle) :
    HasProjectiveCircuitApproximation n ε ((4*n+1)*(2*n+2)*(2^n)^2) (projectiveSpectralMatrix e V x) :=
  (eigenbasis_phases hn V (fun j => fourier 1 (RHTower.zeroAnchoredPhase d x (e j)))
    (fun _ => by rw [fourier_apply,Circle.norm_coe])).approx hε

/-- Least number of physical two-qubit gates at the specified error
for phases on the given eigenbasis. -/
def phaseCost {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) (x : Fin d → UnitAddCircle) : ℕ :=
  Nat.find (show ∃ s, HasProjectiveCircuitApproximation n ε s (projectiveSpectralMatrix e V x)
    from ⟨_,cap hn e V hε x⟩)

theorem phaseCost_le {n d s : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) (x : Fin d → UnitAddCircle) :
    phaseCost hn e V hε x ≤ s ↔ HasProjectiveCircuitApproximation n ε s (projectiveSpectralMatrix e V x) := by
  constructor
  · intro h
    obtain ⟨z,hz,C,hC,he⟩ := Nat.find_spec
      (show ∃ s, HasProjectiveCircuitApproximation n ε s (projectiveSpectralMatrix e V x) from ⟨_,cap hn e V hε x⟩)
    exact ⟨z,hz,C,hC.trans h,he⟩
  · exact fun h => Nat.find_min' _ h

/-- Changing k specified phases shifts the minimum in either direction
by at most k exact eigenline rotations. -/
theorem phaseCost_change_on {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) (S : Finset (Fin d))
    (x y : Fin d → UnitAddCircle) (hxy : ∀ j, j∉S → x j=y j) :
    phaseCost hn e V hε x ≤ S.card*eigenphaseCost n+phaseCost hn e V hε y := by
  let f := phaseCost hn e V hε
  induction S using Finset.induction_on generalizing x with
  | empty =>
    have he : x=y := funext fun j => hxy j (Finset.notMem_empty _)
    simp [he]
  | @insert i S hi ih =>
    let z := Function.update x i (y i)
    have hz (j) (hj : j∉S) : z j=y j := by
      by_cases he : j=i
      · subst j; exact Function.update_self ..
      · dsimp only [z]
        rw [Function.update_of_ne he]
        exact hxy j (fun h => (Finset.mem_insert.mp h).elim he hj)
    have hbase := (phaseCost_le hn e V hε z).mp (show f z ≤ f z from le_rfl)
    have hstep := (phaseCost_le hn e V hε x).mpr (replace_coordinate hn e V i
      (fun j hj => (Function.update_of_ne hj _ _).symm) hbase)
    rw [Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul]
    exact hstep.trans ((Nat.add_le_add_left (ih z hz) _).trans_eq (by omega))

theorem measurable_phaseCost {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) : Measurable (phaseCost hn e V hε) := by
  let f := phaseCost hn e V hε
  have h (s : ℕ) : MeasurableSet {x | f x ≤ s} := by
    have he : {x | f x ≤ s}=projectiveContinuousCircuitCaptureTarget e V s ε :=
      Set.ext fun x => (phaseCost_le hn e V hε x).trans (mem_projectiveContinuousCircuitCaptureTarget_iff e V s ε x).symm
    rw [he]
    exact (isClosed_projectiveContinuousCircuitCaptureTarget e V s ε).measurableSet
  apply measurable_to_countable'
  intro s
  cases s with
  | zero =>
    convert h 0 using 1
    ext x
    change f x=0 ↔ f x≤0
    omega
  | succ s =>
    have he : f ⁻¹' {s+1}={x | f x ≤ s+1} \ {x | f x ≤ s} := by
      ext x
      change f x = s+1 ↔ f x ≤ s+1 ∧ ¬f x ≤ s
      omega
    change MeasurableSet (f ⁻¹' {s+1})
    rw [he]
    exact (h _).diff (h _)

/-- The conditional Haar mean of the physical minimum at one fixed error. -/
def meanCost {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) : ℝ :=
  ∫ x, (phaseCost hn e V hε x:ℝ)

theorem integrable_phaseCost {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) :
    Integrable (fun x => (phaseCost hn e V hε x : ℝ)) volume :=
  Integrable.of_mem_Icc (μ:=volume) 0 (((4*n+1)*(2*n+2)*(2^n)^2:ℕ):ℝ)
    (((measurable_from_nat : Measurable ((↑) : ℕ → ℝ)).comp (measurable_phaseCost hn e V hε)).aemeasurable)
    (Filter.Eventually.of_forall fun x =>
      ⟨Nat.cast_nonneg _,Nat.cast_le.mpr ((phaseCost_le hn e V hε x).mpr (cap hn e V hε x))⟩)

/-- The concentration parameter depends on the number of free relative
phases and the exact cost of rotating one eigenline. -/
theorem phaseCost_moment {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε : ℝ} (hε : 0≤ε) :
    HasSubgaussianMGF (fun x => (phaseCost hn e V hε x:ℝ)-meanCost hn e V hε)
      ((d:NNReal)*((eigenphaseCost n:NNReal)/2)^2) volume := by
  let f := phaseCost hn e V hε
  apply product_moment (volume : Measure UnitAddCircle) _ _ (fun x => (f x:ℝ))
    ((measurable_from_nat : Measurable ((↑) : ℕ → ℝ)).comp (measurable_phaseCost hn e V hε))
    (a:=0) (b:=((4*n+1)*(2*n+2)*(2^n)^2:ℕ))
  · intro x
    exact ⟨Nat.cast_nonneg _,Nat.cast_le.mpr ((phaseCost_le hn e V hε x).mpr (cap hn e V hε x))⟩
  · intro i x y h
    have hs := (phaseCost_le hn e V hε y).mp (show f y≤f y from le_rfl)
    have hx := (phaseCost_le hn e V hε x).mpr (replace_coordinate hn e V i h hs)
    have h' : (f x:ℝ) ≤ eigenphaseCost n+(f y:ℝ) := by exact_mod_cast hx
    change (f x:ℝ)-(f y:ℝ) ≤ (eigenphaseCost n:ℝ)
    linarith only [h']

#print axioms phaseCost_moment
end
end GaloisForLFunctions.HTGeometry.PhaseFluctuations
