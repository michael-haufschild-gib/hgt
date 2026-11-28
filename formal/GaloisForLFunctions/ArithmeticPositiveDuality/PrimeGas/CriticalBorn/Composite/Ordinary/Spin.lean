import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Distance
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Transition
import GaloisForLFunctions.HTGeometry.PhaseOrbitCubeStability

/-! # Spin transitions of the ordinary bosonic occupation states -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Filter Real Crossover
open GaloisForLFunctions.HTGeometry
open scoped Topology

private theorem unit_le (u : Gas) : ‖unitWave u‖ ≤ 1 := by
  rw [unitWave,norm_smul,norm_inv,Real.norm_of_nonneg (norm_nonneg _)]
  by_cases h : ‖u‖=0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

private theorem unit_complex (u : Gas) : unitWave u=(((‖u‖:ℂ)⁻¹) • u) := by
  apply Subtype.ext
  funext n
  change (‖u‖⁻¹:ℝ) • u n=(‖u‖:ℂ)⁻¹*u n
  rw [Complex.real_smul,Complex.ofReal_inv]

private theorem unit_score (u v : Gas) :
    normalizedPureStateFidelity u v=‖inner ℂ (unitWave u) (unitWave v)‖^2 := by
  simp only [normalizedPureStateFidelity,unit_complex,inner_smul_left,inner_smul_right,norm_mul,
    RCLike.norm_conj,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_pow,
    inv_pow,div_eq_mul_inv,mul_inv_rev]
  ring

private theorem change_both (a b u v : Gas) :
    |normalizedPureStateFidelity a b-normalizedPureStateFidelity u v| ≤
      2*(‖unitWave a-unitWave u‖+‖unitWave b-unitWave v‖) := by
  rw [unit_score,unit_score]
  have first := abs_score_sub_le (unitWave b) (unitWave a) (unitWave u) (unit_le b) (unit_le a) (unit_le u)
  have second := abs_score_sub_le (unitWave u) (unitWave b) (unitWave v) (unit_le u) (unit_le b) (unit_le v)
  rw [norm_inner_symm (𝕜:=ℂ) (unitWave b) (unitWave a),norm_inner_symm (𝕜:=ℂ) (unitWave b) (unitWave u)] at first
  exact (abs_sub_le _ _ _).trans ((add_le_add first second).trans_eq (mul_add _ _ _).symm)

def movingWave (m : ℕ) (c t h : ℝ) (N : ℕ) :=
  wave m (indexParameter (drift c N/log N) (t+h/log N)) N

/-- Ordinary Bose heat states on distinct positive-integer labels realize
the m-th power of the qubit fidelity throughout the moving window. -/
theorem chordal_power (m : ℕ) (c d t h k : ℝ) :
    Tendsto (fun N : ℕ => normalizedPureStateFidelity (movingWave m c t h N) (movingWave m d t k N))
      atTop (𝓝 ((1-_root_.Bottcher.chordalDist (Spin.coordinate c h) (Spin.coordinate d k)^2)^m)) := by
  let ordered N := normalizedPureStateFidelity (Composite.movingWave m c t h N) (Composite.movingWave m d t k N)
  let plain N := normalizedPureStateFidelity (movingWave m c t h N) (movingWave m d t k N)
  have hi := ((unit_distance_limit m c (fun N => t+h/log N)).add
    (unit_distance_limit m d (fun N => t+k/log N))).const_mul 2
  rw [add_zero,mul_zero] at hi
  have gap : Tendsto (fun N => ordered N-plain N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi (fun _ => norm_nonneg _) _
    intro N
    exact change_both _ _ _ _
  have z := (Composite.chordal_power m c d t h k).sub gap
  rw [sub_zero] at z
  apply z.congr
  intro N
  change ordered N-(ordered N-plain N)=plain N
  ring

#print axioms chordal_power

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
