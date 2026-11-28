import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Isometry
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.TimeRefinement
import GaloisForLFunctions.HTGeometry.LpInjectionCompression

/-! # Zeta as the trace of the actual no-emission output of an isometry -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

open CoassociativeSplitting

abbrev Duration := Set.Ioi (0:ℝ)
abbrev Conserving := {s : ℂ // s.re=1/2}
abbrev TracePoint := {z : ℂ // 1<z.re}

private theorem has_instrument (s : Conserving) (t : Duration) : isometric (kernel s.val (emit t.val) (survive t.val)) :=
  (conserving_iff s.val (emit_pos t.property) (survive_pos t.val)).mpr s.property

/-- The full emitted/surviving two-output experiment. -/
def instrument (s : Conserving) (t : Duration) : Gas →ₗᵢ[ℂ] PairGas :=
  Classical.choose (has_instrument s t)

theorem instrument_apply (s : Conserving) (t : Duration) (f : Gas) (x : ℕ+ × ℕ+) :
    instrument s t f x=wave (kernel s.val (emit t.val) (survive t.val)) f x :=
  Classical.choose_spec (has_instrument s t) f x

/-- Project the emitted output onto its vacuum and retain the surviving gas. -/
def vacuumSlice : PairGas →L[ℂ] Gas :=
  RHTower.lpCoordinatePullback (fun n : ℕ+ => ((1:ℕ+),n)) (fun _ _ h => congrArg Prod.snd h)

def noEmission (s : Conserving) (t : Duration) := vacuumSlice ∘L (instrument s t).toContinuousLinearMap

theorem noEmission_apply (s : Conserving) (t : Duration) (f : Gas) (n : ℕ+) :
    noEmission s t f n=heat ((t.val:ℂ)*s.val) n * f n := by
  change instrument s t f (1,n)=_
  rw [instrument_apply,wave,one_mul,vacuum_heat]

/-- Requiring no emission on consecutive intervals composes the two
postselected operators on the surviving gas. -/
theorem noEmission_add (s : Conserving) (t r : Duration) :
    noEmission s ⟨t.val+r.val,show 0<t.val+r.val from add_pos t.property r.property⟩ =
      noEmission s t ∘L noEmission s r := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  simp only [ContinuousLinearMap.comp_apply,noEmission_apply,Complex.ofReal_add,add_mul,
    heat_add,mul_assoc]

def observationTime (z : TracePoint) : Duration :=
  ⟨2*z.val.re,mul_pos (by norm_num) (lt_trans zero_lt_one z.property)⟩

def conservingExponent (z : TracePoint) : Conserving :=
  ⟨z.val/((observationTime z).val:ℂ),by
    rw [Complex.div_ofReal_re]
    change z.val.re/(2*z.val.re)=1/2
    have pos := lt_trans zero_lt_one z.property
    exact (div_eq_iff (mul_pos (by norm_num) pos).ne').mpr (by ring)⟩

/-- Every trace-class logarithmic heat operator is exactly a vacuum output
of a norm-preserving quantum experiment. -/
theorem noEmission_eq_gibbs (z : TracePoint) :
    noEmission (conservingExponent z) (observationTime z)=gibbsOperator z := by
  have nz := Complex.ofReal_ne_zero.mpr (observationTime z).property.ne'
  have eqn : ((observationTime z).val:ℂ)*(conservingExponent z).val=z.val := by
    change ((observationTime z).val:ℂ)*(z.val/((observationTime z).val:ℂ))=z.val
    exact mul_div_cancel₀ _ nz
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext n
  rw [noEmission_apply,eqn,gibbsOperator_apply]

theorem noEmission_trace (z : TracePoint) :
    ContinuousLinearMap.opTrace (noEmission (conservingExponent z) (observationTime z))=riemannZeta z.val := by
  rw [noEmission_eq_gibbs,partition_eq_zeta]

#print axioms instrument_apply
#print axioms noEmission_apply
#print axioms noEmission_add
#print axioms noEmission_eq_gibbs
#print axioms noEmission_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities
