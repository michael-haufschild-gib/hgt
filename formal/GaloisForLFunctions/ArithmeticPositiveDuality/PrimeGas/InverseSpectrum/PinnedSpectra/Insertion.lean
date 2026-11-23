import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.CoordinateSubsequence
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineMoments
import GaloisForLFunctions.RHTower.PrimeCoShiftModel

/-! # Inserting prime factors into a missing wave -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Multiplication embeds each occupation into a higher shell. -/
def insertLabels (a : ℕ+) : ℕ+ ↪ ℕ+ :=
  ⟨fun n => a*n, _root_.RHTower.PrimeCoShift.mulLeft_injective a⟩

abbrev insertWave := _root_.RHTower.PrimeCoShift.primeShift

/-- Multiplication preserves exteriority because coordinate restriction recovers the original wave. -/
def insertMissing (a : ℕ+) (v : MissingWave) : MissingWave :=
  ⟨insertWave a v.val,extendModes_outside (f := insertLabels a)
    (fun n => show n.val ≤ a.val*n.val from Nat.le_mul_of_pos_left _ a.pos) v.property⟩

theorem insertWave_at (a : ℕ+) (v : Gas) (n : ℕ+) : insertWave a v (a*n) = v n :=
  _root_.RHTower.lpScalarInjection_coordinate (insertLabels a) (insertLabels a).injective v n

theorem insertWave_off (a : ℕ+) (v : Gas) (n : ℕ+) (hn : n ∉ Set.range (insertLabels a)) :
    insertWave a v n = 0 :=
  _root_.RHTower.lpScalarInjection_coordinate_of_not_mem (insertLabels a) (insertLabels a).injective v n hn

private theorem attenuation_mul (a b : ℕ+) : (attenuation (a*b):ℂ) = (attenuation a:ℂ)*(attenuation b:ℂ) := by
  simp only [critical_heat,heat_mul]

/-- Inserting a factor intertwines the critical heat with its scalar multiple. -/
theorem heat_insertWave (a : ℕ+) (v : Gas) :
    criticalOperator (insertWave a v) = (attenuation a:ℂ) • insertWave a (criticalOperator v) := by
  apply lp.ext
  funext n
  change criticalOperator (insertWave a v) n = (attenuation a:ℂ)*insertWave a (criticalOperator v) n
  rw [critical_apply]
  by_cases hn : n ∈ Set.range (insertLabels a)
  · obtain ⟨k,rfl⟩ := hn
    change (attenuation (a*k):ℂ)*insertWave a v (a*k) = (attenuation a:ℂ)*insertWave a (criticalOperator v) (a*k)
    rw [insertWave_at,insertWave_at,critical_apply,attenuation_mul,mul_assoc]
  · rw [insertWave_off _ _ _ hn,insertWave_off _ _ _ hn,mul_zero,mul_zero]

private theorem heat_insert_norm (a : ℕ+) (v : Gas) :
    ‖criticalOperator (insertWave a v)‖ = attenuation a*‖criticalOperator v‖ := by
  rw [heat_insertWave,norm_smul,LinearIsometry.norm_map,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos a).le]

theorem firstMoment_insert (a : ℕ+) (v : Gas) : firstMoment (insertWave a v) = attenuation a^2*firstMoment v := by
  rw [firstMoment,firstMoment,heat_insert_norm,LinearIsometry.norm_map,mul_pow,mul_div_assoc]

theorem secondMoment_insert (a : ℕ+) (v : Gas) : secondMoment (insertWave a v) = attenuation a^4*secondMoment v := by
  change ‖criticalOperator (criticalOperator (insertWave a v))‖^2/‖insertWave a v‖^2 =
    attenuation a^4*(‖criticalOperator (criticalOperator v)‖^2/‖v‖^2)
  rw [heat_insertWave,map_smul,norm_smul,heat_insert_norm,LinearIsometry.norm_map,
    Complex.norm_real,Real.norm_of_nonneg (attenuation_pos a).le]
  ring

/-- Every fixed missing direction has the same fourth-trace scaling under insertion. -/
theorem fourth_loss_insert (a : ℕ+) (v : Gas) :
    traceLoss (projected (omitLine (insertWave a v))) = attenuation a^4*traceLoss (projected (omitLine v)) := by
  rw [traceLoss_omitLine,traceLoss_omitLine,lineLoss_eq_moments,lineLoss_eq_moments,firstMoment_insert,secondMoment_insert]
  ring

/-- Dividing the fourth-trace losses measures the inverse square of the inserted integer. -/
theorem insertion_trace_ratio (a : ℕ+) (v : MissingWave) :
    traceLoss (projected (omitLine (insertWave a v.val)))/traceLoss (projected (omitLine v.val)) = ((a.val:ℝ)^2)⁻¹ := by
  have hpos : traceLoss (projected (omitLine v.val)) ≠ 0 := by
    rw [traceLoss_omitLine]
    exact (line_loss_bounds v).1.ne'
  apply (div_eq_iff hpos).mpr
  rw [fourth_loss_insert,attenuation,inv_pow,show (4:ℕ) = 2*2 from rfl,pow_mul,gain_sq]

/-- Two ordinary fourth traces recover the added Hamiltonian energy independently of the omitted direction. -/
theorem insertion_energy_from_traces (a : ℕ+) (v : MissingWave) :
    -Real.log (traceLoss (projected (omitLine (insertWave a v.val)))/traceLoss (projected (omitLine v.val)))/2 =
      energy a := by
  rw [insertion_trace_ratio,Real.log_inv,Real.log_pow,energy]
  ring

#print axioms insertion_energy_from_traces
#print axioms insertion_trace_ratio
#print axioms heat_insertWave
#print axioms fourth_loss_insert

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
