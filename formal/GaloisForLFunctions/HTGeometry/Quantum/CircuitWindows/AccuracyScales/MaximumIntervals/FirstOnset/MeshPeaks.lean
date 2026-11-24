import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.RecordHeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.LogarithmicGrid

/-! # Threshold clearance for the worst circuit fit on a prefix of the time mesh -/

open Filter Set MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals.FirstOnset
open DiagonalSynthesis (Register)
open IntervalMinima
noncomputable section

private theorem attained {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (a : ℝ) (b i : ℕ) :
    let I := Icc a (a+logMesh N b i)
    ∃ w ∈ I, ∀ t ∈ I, orbitCircuitDistance H s t ≤ orbitCircuitDistance H s w := by
  intro I
  have hT : 0 ≤ logMesh N b i := by
    apply sub_nonneg.mpr
    exact one_le_exp (by positivity)
  obtain ⟨w,hw,h⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (le_add_of_nonneg_right (a:=a) hT))
    (orbitCircuitDistance_lipschitz H s).continuous.continuousOn
  exact ⟨w,hw,isMaxOn_iff.mp h⟩

/-- The highest observed distance to the gate budget in one mesh interval. -/
def peak {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (a : ℝ) (b i : ℕ) : ℝ :=
  orbitCircuitDistance H s (attained H s a b i).choose

private def row (ω : PathPauliDisorder) (a : ℕ → ℝ) (b k j : ℕ) : ℝ :=
  let B := 2^(6*(k+3))
  peak (chainGenerator ω k) (j%B) (a k) b (j/B)

/-- Exceptional errors for cumulative maxima at every budget on the
relative-time mesh, from origins selected before the error. -/
def peakExceptional (ω : PathPauliDisorder) (a : ℕ → ℝ) (C b : ℕ) : Set ℝ :=
  exceptionalTolerances (embedRows (fun k => (C+b+2)*(k+3)) (row ω a b))

/-- Whenever the budget reaches an error threshold by a given date,
an exponential margin is reached by a date with logarithmic excess
at most D⁻ᵇ. All budgets and all dates up to the deadline are included. -/
theorem mesh_peak_clearance (ω : PathPauliDisorder) (a : ℕ → ℝ) (C b : ℕ) :
    dimH (peakExceptional ω a C b)=0 ∧ ∀ e ∉ peakExceptional ω a C b,
      ∃ c : ℕ, ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∀ s < 2^(6*N), ∀ v ∈ Icc (a k) (a k+(2:ℝ)^((2^N)^C : ℕ)),
          e ≤ orbitCircuitDistance H s v →
          ∃ w ≥ a k, 1+(w-a k) ≤ (1+(v-a k))*exp (1/(2:ℝ)^(b*N)) ∧
            e+1/(2:ℝ)^(c*N) < orbitCircuitDistance H s w := by
  let M := C+b+2
  let B (k : ℕ) := M*(k+3)
  have hM : 0<M := by dsimp only [M]; omega
  have hB : StrictMono B := fun i j h => Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right h 3) hM
  refine ⟨dimH_exceptionalTolerances _,?_⟩
  intro e he
  obtain ⟨q,hq⟩ := row_clearance B hB (row ω a b) e he
  refine ⟨q*M,?_⟩
  filter_upwards [hq] with k hfar
  intro N H s hs v hv he
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hn : N ≤ B k := Nat.le_mul_of_pos_left _ hM
  obtain ⟨i,hi,hlo,hbound⟩ := round_wait hN C b (sub_nonneg.mpr hv.1)
    (show v-a k ≤ (2:ℝ)^((2^N)^C : ℕ) by linarith only [hv.2])
  let A := 2^(6*N)
  let j := A*i+s
  have hA : 0<A := by dsimp only [A]; positivity
  have hj : j < 2^(8*(B k+3)) := by
    have h₀ : j < A*(i+1) := by rw [Nat.mul_succ]; dsimp only [j]; omega
    have h₁ := h₀.trans_le (Nat.mul_le_mul_left A (Nat.succ_le_of_lt hi))
    have h₂ : A*2^(B k) ≤ 2^(8*(B k+3)) := by
      dsimp only [A]; rw [←pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact h₁.trans_le h₂
  let w := (attained H s (a k) b i).choose
  obtain ⟨hw,hmax⟩ := (attained H s (a k) b i).choose_spec
  have hvalue : row ω a b k j = orbitCircuitDistance H s w := by
    change peak H ((A*i+s)%A) (a k) b ((A*i+s)/A) = _
    rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hs,Nat.mul_add_div hA,
      Nat.div_eq_of_lt hs,add_zero]
    rfl
  have hew : e ≤ orbitCircuitDistance H s w := he.trans
    (hmax v ⟨hv.1,by linarith only [hlo]⟩)
  refine ⟨w,hw.1,?_,?_⟩
  · have hw' : w ≤ a k+logMesh N b i := hw.2
    exact (add_le_add le_rfl (show w-a k ≤ logMesh N b i by linarith only [hw'])).trans hbound
  · by_contra! h
    apply hfar ⟨j,hj,?_⟩
    rw [hvalue,abs_of_nonpos (sub_nonpos.mpr hew)]
    change -(e-orbitCircuitDistance H s w) ≤ 1/(2:ℝ)^(q*(M*N))
    rw [←Nat.mul_assoc]
    linarith only [h]

#print axioms mesh_peak_clearance
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals.FirstOnset
