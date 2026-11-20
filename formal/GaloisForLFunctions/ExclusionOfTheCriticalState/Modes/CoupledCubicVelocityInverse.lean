import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.CoupledCubicProbeRecovery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Short-time Hankel measurements of coupled cubic oscillators

Each component has a known spatial operator and unknown linear and mixed
cubic forces at every site, with the two couplings from the wave system of
Kumar–Senapati–Vashisth. Picard–Lindelöf gives local trajectories. Four
initial displacements distinguish all eight coefficient fields from velocity
observations accumulating at the initial time. The observation times can
differ between experiments.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery
namespace Oscillator

abbrev Sites (n : ℕ) := Fin n → ℝ
abbrev Pair (n : ℕ) := Sites n × Sites n
abbrev State (n : ℕ) := Pair n × Pair n
abbrev Coefficients (n : ℕ) := Row (Sites n) × Row (Sites n)

variable {n : ℕ}

private def localRow (R : Row (Sites n)) (i : Fin n) := R.map (fun v => v i)

/-- Known linear propagation may mix sites. The cubic source is local in
position and couples the two components. -/
def field (K : Sites n →L[ℝ] Sites n) (R : Coefficients n) (z : State n) : State n :=
  (z.2, (K z.1.1 + fun i => response false (localRow R.1 i) (z.1.1 i) (z.1.2 i),
         K z.1.2 + fun i => response true (localRow R.2 i) (z.1.1 i) (z.1.2 i)))

private def start (x y : ℝ) : State n := ((fun _ => x,fun _ => y),0)

private theorem local_solution (K : Sites n →L[ℝ] Sites n) (R : Coefficients n) (x y : ℝ) :
    ∃ γ : ℝ → State n, γ 0 = start x y ∧ ∃ ε > (0:ℝ),
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (field K R (γ t)) t := by
  have hf : ContDiff ℝ 1 (field K R) := by
    unfold field response
    simp only [Bool.false_eq_true,if_false,if_true]
    fun_prop
  obtain ⟨γ,h0,ε,hε,hγ⟩ :=
    hf.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := start x y) 0
  exact ⟨γ,h0,ε,hε,by simpa only [zero_sub,zero_add] using hγ⟩

/-- Local trajectory starting from constant displacements and zero velocities. -/
def trajectory (K : Sites n →L[ℝ] Sites n) (R : Coefficients n) (x y : ℝ) : ℝ → State n :=
  (local_solution K R x y).choose

theorem trajectory_solves (K : Sites n →L[ℝ] Sites n) (R : Coefficients n) (x y : ℝ) :
    let γ := trajectory K R x y
    γ 0 = ((fun _ => x,fun _ => y),0) ∧ ∃ ε > (0:ℝ),
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (field K R (γ t)) t :=
  (local_solution K R x y).choose_spec

private def velocity (K : Sites n →L[ℝ] Sites n) (R : Coefficients n) (x y t : ℝ) :=
  (trajectory K R x y t).2

private theorem initial_acceleration (K : Sites n →L[ℝ] Sites n) (R : Coefficients n) (x y : ℝ) :
    HasDerivAt (velocity K R x y) (field K R (start x y)).2 0 := by
  obtain ⟨h0,ε,hε,h⟩ := trajectory_solves K R x y
  have hd := h 0 ⟨neg_lt_zero.mpr hε,hε⟩
  rw [h0] at hd
  apply hasDerivAt_iff_tendsto_slope.mpr
  change Tendsto (fun t => slope (velocity K R x y) 0 t) _ _
  simpa only [slope_def_module,velocity,start,Prod.smul_snd,Prod.snd_sub] using hd.tendsto_slope.snd_nhds

/-- Velocities of the two components observed through the actual exponential probe bank. -/
def observation (s : ℝ) (time shift : Fin n ↪ ℕ) (K : Sites n →L[ℝ] Sites n)
    (R : Coefficients n) (x y t : ℝ) : Pair n :=
  let v := velocity K R x y t
  ((bank s time shift).mulVec v.1,(bank s time shift).mulVec v.2)

private theorem acceleration_of_sparse (s : ℝ) (time shift : Fin n ↪ ℕ) (K : Sites n →L[ℝ] Sites n)
    (R S : Coefficients n) (x y : ℝ)
    (h : ∃ᶠ t in 𝓝[≠] (0:ℝ), observation s time shift K R x y t = observation s time shift K S x y t) :
    (field K R (start x y)).2 = (field K S (start x y)).2 := by
  have hv : ∃ᶠ t in 𝓝[≠] (0:ℝ), velocity K R x y t = velocity K S x y t := by
    apply h.mono
    intro t ht
    exact Prod.ext ((bank_bijective s time shift).1 (congrArg Prod.fst ht))
      ((bank_bijective s time shift).1 (congrArg Prod.snd ht))
  have zeroV (T : Coefficients n) : velocity K T x y 0 = 0 :=
    congrArg Prod.snd (trajectory_solves K T x y).1
  apply tendsto_nhds_unique_of_frequently_eq
    (hasDerivAt_iff_tendsto_slope.mp (initial_acceleration K R x y))
    (hasDerivAt_iff_tendsto_slope.mp (initial_acceleration K S x y))
  exact hv.mono fun t ht => by simp only [slope_def_module,zeroV,ht]

private theorem row_ext {R S : Row (Sites n)} (h : ∀ i, localRow R i = localRow S i) : R = S := by
  cases R with
  | mk a b c d =>
    cases S with
    | mk e f g k =>
      congr 1
      · exact funext fun i => congrArg Row.linearX (h i)
      · exact funext fun i => congrArg Row.linearY (h i)
      · exact funext fun i => congrArg Row.cubicX (h i)
      · exact funext fun i => congrArg Row.cubicY (h i)

private def amplitude (large : Bool) : ℝ := if large then 2 else 1
private def direction (large minus : Bool) : ℝ := if minus then -amplitude large else amplitude large

private theorem reads_row {second : Bool} {r s : Row ℝ}
    (h : ∀ large minus, response second r (amplitude large) (direction large minus) =
      response second s (amplitude large) (direction large minus)) : r = s := by
  have he : measureRow second r = measureRow second s := by
    unfold measureRow
    congr 1
    · exact h false false
    · exact h false true
    · exact h true false
    · exact h true true
  exact (recover_measure second r).symm.trans ((congrArg recover he).trans (recover_measure second s))

/-- Agreement on arbitrarily short nonzero times in each of the four shots
is equivalent to equality of all site coefficients. Each shot may use a
different sequence and the propagation operator can mix all sites. -/
theorem four_sparse_shots_identify (s : ℝ) (time shift : Fin n ↪ ℕ) (K : Sites n →L[ℝ] Sites n)
    (R S : Coefficients n) :
    (∀ large minus : Bool, ∃ᶠ t in 𝓝[≠] (0:ℝ),
      observation s time shift K R (if large then 2 else 1)
        (if minus then -(if large then 2 else 1) else (if large then 2 else 1)) t =
      observation s time shift K S (if large then 2 else 1)
        (if minus then -(if large then 2 else 1) else (if large then 2 else 1)) t) ↔ R = S := by
  constructor
  · intro h
    have he (b e : Bool) := acceleration_of_sparse s time shift K R S (amplitude b) (direction b e) (h b e)
    apply Prod.ext <;> apply row_ext <;> intro i
    · apply reads_row (second := false)
      intro b e
      exact add_left_cancel (congrArg (fun z : Pair n => z.1 i) (he b e))
    · apply reads_row (second := true)
      intro b e
      exact add_left_cancel (congrArg (fun z : Pair n => z.2 i) (he b e))
  · rintro rfl _ _
    exact (Eventually.of_forall fun _ => rfl).frequently

end Oscillator
end GaloisForLFunctions.ExclusionOfTheCriticalState.CubicRecovery
