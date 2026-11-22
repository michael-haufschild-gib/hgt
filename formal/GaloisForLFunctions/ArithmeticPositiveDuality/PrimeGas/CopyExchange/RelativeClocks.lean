import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleBoundary
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.LogarithmicPhaseContinuity
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert
import GaloisForLFunctions.HTGeometry.LpInjectionCoordinates
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseWeilBridge

/-!
# Stationarity under relative Hamiltonian time

Opposite clock times on successive copies detect every unequal pair of
energies. Their joint stationary vectors form the full fixed-label Hilbert
space, whose heat is transported by zero extension.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open GaloisForLFunctions.HTGeometry ContinuousLinearMap
open scoped Classical

variable {I : Type*}

/-- The phase from running successive copies for opposite times. -/
def relativePhase (π : Equiv.Perm I) (i : I) (t : ℝ) (x : I → ℕ+) : Circle :=
  Circle.exp (t * (energy (x i) - energy (x (π i))))

theorem relativePhase_clocks (π : Equiv.Perm I) (i : I) (t : ℝ) (x : I → ℕ+) :
    relativePhase π i t x = clockPhase t (x i) * clockPhase (-t) (x (π i)) := by
  change _ = Circle.exp _ * Circle.exp _
  rw [← Circle.exp_add]
  unfold relativePhase
  congr 1
  ring

def relativeClock (π : Equiv.Perm I) (i : I) (t : ℝ) : LabelSpace (I → ℕ+) ≃ₗᵢ[ℂ] LabelSpace (I → ℕ+) :=
  lpPhaseUnitary (fun x => (relativePhase π i t x : ℂ)) (fun _ => Circle.norm_coe _)

private theorem energy_inj {a b : ℕ+} (h : energy a = energy b) : a = b := by
  have he := congrArg Real.exp h
  rw [energy,energy,Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at he
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) he)

/-- Continuous relative clocks fix a vector exactly when it vanishes off the cycle-constant tuples. -/
theorem relative_stationary_iff (π : Equiv.Perm I) (f : LabelSpace (I → ℕ+)) :
    (∀ i t, relativeClock π i t f = f) ↔ ∀ x, x ∘ π ≠ x → f x = 0 := by
  constructor
  · intro h x hx
    obtain ⟨i,hi⟩ : ∃ i, x (π i) ≠ x i := by
      by_contra! he
      exact hx (funext he)
    let d := energy (x i) - energy (x (π i))
    have hd : d ≠ 0 := fun hzero => hi (energy_inj (sub_eq_zero.mp hzero)).symm
    have he := congrArg (fun v : LabelSpace (I → ℕ+) => v x) (h i (Real.pi/d))
    change Complex.exp (((Real.pi/d*d : ℝ) : ℂ)*Complex.I) * f x = f x at he
    rw [div_mul_cancel₀ _ hd,Complex.exp_pi_mul_I,neg_one_mul] at he
    linear_combination (-1/2 : ℂ) * he
  · intro h i t
    apply lp.ext
    funext x
    change (relativePhase π i t x : ℂ) * f x = f x
    by_cases hx : x ∘ π = x
    · have hi : x (π i) = x i := congrFun hx i
      simp [relativePhase,hi]
    · rw [h x hx,mul_zero]

variable [Fintype I]

/-- Zero extension from tuples of synchronized clocks. -/
def fixedEmbedding (π : Equiv.Perm I) : LabelSpace (FixedWord π) →ₗᵢ[ℂ] LabelSpace (I → ℕ+) :=
  _root_.RHTower.lpScalarInjection Subtype.val Subtype.val_injective

abbrev stationarySpace (π : Equiv.Perm I) := (fixedEmbedding π).toLinearMap.range

instance stationaryComplete (π : Equiv.Perm I) : CompleteSpace (stationarySpace π) :=
  (fixedEmbedding π).isometry.isClosedEmbedding.isClosed_range.completeSpace_coe

def stationaryEquiv (π : Equiv.Perm I) : LabelSpace (FixedWord π) ≃ₗᵢ[ℂ] stationarySpace π :=
  (fixedEmbedding π).equivRange

private theorem embed_coordinate (π : Equiv.Perm I) (f : LabelSpace (FixedWord π)) (x : FixedWord π) :
    (stationaryEquiv π f : LabelSpace (I → ℕ+)) x.val = f x :=
  _root_.RHTower.lpScalarInjection_coordinate Subtype.val Subtype.val_injective f x

private theorem read_coordinate (π : Equiv.Perm I) (v : stationarySpace π) (x : FixedWord π) :
    (stationaryEquiv π).symm v x = (v : LabelSpace (I → ℕ+)) x.val := by
  have h := embed_coordinate π ((stationaryEquiv π).symm v) x
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm

theorem mem_stationarySpace_iff (π : Equiv.Perm I) (f : LabelSpace (I → ℕ+)) :
    f ∈ stationarySpace π ↔ ∀ i t, relativeClock π i t f = f := by
  rw [relative_stationary_iff]
  have miss (x : I → ℕ+) (h : x ∘ π ≠ x) : x ∉ Set.range (Subtype.val : FixedWord π → _) := by
    rintro ⟨u,rfl⟩
    exact h u.property
  constructor
  · rintro ⟨g,rfl⟩ x hx
    exact _root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ g x (miss x hx)
  · intro hf
    let g := _root_.RHTower.lpCoordinatePullback (E := ℂ) (Subtype.val : FixedWord π → _) Subtype.val_injective f
    refine ⟨g,?_⟩
    apply lp.ext
    funext x
    by_cases hx : x ∘ π = x
    · exact _root_.RHTower.lpScalarInjection_coordinate _ _ g (⟨x,hx⟩ : FixedWord π)
    · exact (_root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ g x (miss x hx)).trans (hf x hx).symm

/-- Heat on the genuine joint invariant subspace of the relative clocks. -/
def stationaryHeat (π : Equiv.Perm I) (s : {w : ℂ // InCycleDomain π w}) :
    stationarySpace π →L[ℂ] stationarySpace π :=
  (stationaryEquiv π).toLinearIsometry.toContinuousLinearMap ∘L fixedHeat π s ∘L
    (stationaryEquiv π).symm.toLinearIsometry.toContinuousLinearMap

private theorem fixed_tc (π : Equiv.Perm I) (s : {w : ℂ // InCycleDomain π w}) : (fixedHeat π s).IsTraceClass :=
  (HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_isTraceClass (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)

theorem stationaryHeat_trace (π : Equiv.Perm I) (s : {w : ℂ // InCycleDomain π w}) :
    opTrace (stationaryHeat π s) = cyclePartition π s.val :=
  (_root_.RHTower.opTrace_unitaryConjugate_of_isTraceClass (stationaryEquiv π).symm _ (fixed_tc π s)).trans
    (fixedHeat_trace π s)

def HasStationaryHeat (π : Equiv.Perm I) (s : ℂ) : Prop :=
  ∃ T : stationarySpace π →L[ℂ] stationarySpace π, T.IsTraceClass ∧
    ∀ (v : stationarySpace π) (x : FixedWord π),
      (T v : LabelSpace (I → ℕ+)) x.val = wordHeat s x.val * (v : LabelSpace (I → ℕ+)) x.val

theorem stationaryHeat_traceClass_iff (π : Equiv.Perm I) (s : ℂ) : HasStationaryHeat π s ↔ InCycleDomain π s := by
  constructor
  · rintro ⟨T,hT,ha⟩
    apply (fixedHeat_traceClass_iff π s).mp
    let e := stationaryEquiv π
    refine ⟨e.symm.toLinearIsometry.toContinuousLinearMap ∘L T ∘L e.toLinearIsometry.toContinuousLinearMap,
      _root_.RHTower.ccmIsTraceClass_unitaryConjugate e T hT,?_⟩
    intro f x
    change (stationaryEquiv π).symm (T (stationaryEquiv π f)) x = _
    rw [read_coordinate,ha,embed_coordinate]
  · intro h
    refine ⟨stationaryHeat π ⟨s,h⟩,
      _root_.RHTower.ccmIsTraceClass_unitaryConjugate (stationaryEquiv π).symm _ (fixed_tc π ⟨s,h⟩),?_⟩
    intro f x
    change (stationaryEquiv π (fixedHeat π ⟨s,h⟩ ((stationaryEquiv π).symm f)) : LabelSpace (I → ℕ+)) x.val = _
    rw [embed_coordinate,fixedHeat_apply,read_coordinate]

/-- Two oppositely running copies select the critical line through stationarity alone. -/
theorem relative_clock_split_iff (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
    (¬HasStationaryHeat (finRotate 2) s ∧ ∀ δ : ℝ, 0 < δ → HasStationaryHeat (finRotate 2) (s+(δ : ℂ))) := by
  have hs (w : ℂ) : HasStationaryHeat (finRotate 2) w ↔ (1/2 : ℝ) < w.re :=
    (stationaryHeat_traceClass_iff _ w).trans ((fixedHeat_traceClass_iff _ w).symm.trans (by
      simpa using rotation_boundary 1 w))
  simp only [split_isometric_iff,hs,not_lt,Complex.add_re,Complex.ofReal_re]
  constructor
  · intro h
    exact ⟨h.le,fun δ hδ => by linarith only [h,hδ]⟩
  · rintro ⟨hl,hr⟩
    apply le_antisymm hl
    by_contra! h
    have hh := hr _ (sub_pos.mpr h)
    linarith only [hh]

#print axioms relativePhase_clocks
#print axioms relative_stationary_iff
#print axioms mem_stationarySpace_iff
#print axioms stationaryHeat_trace
#print axioms stationaryHeat_traceClass_iff
#print axioms relative_clock_split_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
