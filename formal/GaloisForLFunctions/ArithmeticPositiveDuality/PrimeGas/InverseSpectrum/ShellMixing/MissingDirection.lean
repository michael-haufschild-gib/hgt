import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.Projected
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.TraceRecovery
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalPacketOverlap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Which thermal directions can be omitted?

The preimage of a heat packet at s under the critical amplitude has
parameter s − 1/2. Its square summability decides whether a conserving
positive propagator can omit the line through that packet.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap
open _root_.RHTower.PrimeCoShift
open scoped InnerProductSpace

def packet (s : HeatVectorDomain) : Gas := groundState s.val

theorem packet_apply (s : HeatVectorDomain) (n : ℕ+) : packet s n = heat s.val n :=
  (groundState_apply s.property n).trans (heat_eq_cpow _ _).symm

def advanced (s : HeatVectorDomain) : HeatVectorDomain :=
  ⟨1/2+s.val,by
    rw [Complex.add_re,Complex.div_ofNat_re,Complex.one_re]
    linarith only [s.property]⟩

theorem critical_packet (s : HeatVectorDomain) : criticalOperator (packet s) = packet (advanced s) := by
  apply lp.ext
  funext n
  rw [critical_apply,critical_heat,packet_apply,packet_apply,← heat_add]
  rfl

theorem packet_in_range_iff (s : HeatVectorDomain) : packet s ∈ Set.range criticalOperator ↔ 1 < s.val.re := by
  have hr : (s.val-1/2).re = s.val.re-1/2 := by rw [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
  constructor
  · rintro ⟨f,hf⟩
    have he (n : ℕ+) : f n = heat (s.val-1/2) n := by
      apply mul_left_cancel₀ (Complex.exp_ne_zero _ : heat (1/2) n ≠ 0)
      calc
        heat (1/2) n*f n = criticalOperator f n := by rw [critical_apply,critical_heat]
        _ = heat (1/2) n*heat (s.val-1/2) n := by
          rw [hf,packet_apply,← heat_add,show (1/2:ℂ)+(s.val-1/2) = s.val by ring]
    have h := HTGeometry.lp_summable_norm_sq f
    simp_rw [he] at h
    have hb := (summable_heat_sq_iff _).mp h
    rw [hr] at hb
    linarith only [hb]
  · intro h
    let t : HeatVectorDomain := ⟨s.val-1/2,by rw [hr]; linarith only [h]⟩
    refine ⟨packet t,(critical_packet t).trans (congrArg packet (Subtype.ext ?_))⟩
    change 1/2+(s.val-1/2) = s.val
    abel

def omitLine (v : Gas) : Projection :=
  ⟨(ℂ ∙ v)ᗮ.starProjection,isStarProjection_starProjection⟩

theorem omitLine_kills (v : Gas) : (omitLine v).val v = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero _

private theorem omitLine_injective_iff (v : {v : Gas // v ≠ 0}) :
    Function.Injective ((omitLine v.val).val*criticalOperator) ↔ v.val ∉ Set.range criticalOperator := by
  constructor
  · intro hi hv
    obtain ⟨f,hf⟩ := hv
    have he : (omitLine v.val).val (criticalOperator f) = (omitLine v.val).val (criticalOperator 0) := by
      rw [hf,omitLine_kills,map_zero,map_zero]
    have hz : f = 0 := hi he
    exact v.property (by rw [← hf,hz,map_zero])
  · intro hout x y h
    have hz : (omitLine v.val).val (criticalOperator (x-y)) = 0 := by
      change (omitLine v.val).val (criticalOperator x) = (omitLine v.val).val (criticalOperator y) at h
      rw [map_sub,map_sub,h,sub_self]
    have hmem : criticalOperator (x-y) ∈ ℂ ∙ v.val := by
      have hm : criticalOperator (x-y) ∈ (ℂ ∙ v.val)ᗮ.starProjection.toLinearMap.ker := hz
      rwa [Submodule.ker_starProjection,Submodule.orthogonal_orthogonal] at hm
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hmem
    by_cases h₀ : a = 0
    · rw [h₀,zero_smul,map_sub] at ha
      exact critical_injective (sub_eq_zero.mp ha.symm)
    · exfalso
      apply hout
      refine ⟨a⁻¹ • (x-y),?_⟩
      rw [map_smul,← ha,smul_smul,inv_mul_cancel₀ h₀,one_smul]

/-- Throughout the heat-vector domain, full conservation allows precisely the strip through one. -/
theorem packet_omission_iff (s : HeatVectorDomain) :
    Conserving (projected (omitLine (packet s))) ↔ s.val.re ≤ 1 := by
  rw [projected_conserves_iff,omitLine_injective_iff ⟨packet s,groundState_ne_zero s.property⟩,
    packet_in_range_iff,not_lt]

theorem omitted_packet_ne_critical (s : HeatVectorDomain) :
    projected (omitLine (packet s)) ≠ criticalOperator := by
  intro h
  have hI := (projected_eq_critical_iff _).mp h
  have hk := omitLine_kills (packet s)
  rw [hI,one_apply] at hk
  exact groundState_ne_zero s.property hk

/-- Every admissible thermal omission produces strict fourth-trace loss. -/
theorem packet_omission_loss (s : {s : HeatVectorDomain // s.val.re ≤ 1}) :
    (fourthMoment (projected (omitLine (packet s.val)))).re < (riemannZeta 2).re := by
  let G := projected (omitLine (packet s.val))
  have hp : G.IsPositive := projected_positive _
  have hc : Conserving G := (packet_omission_iff _).mpr s.property
  apply lt_of_le_of_ne (fourth_trace_bound ⟨G,hc⟩)
  intro he
  have hz := (fourthMoment_of_positive hp).symm.trans ((moment_eq_iff_re ⟨G,hc⟩).mpr he)
  exact omitted_packet_ne_critical _ ((positive_fourth_iff G).mp ⟨hp,hc,hz⟩)

/-- At the upper endpoint the omitted direction has the reciprocal shell amplitudes. -/
theorem missing_direction :
    let P := omitLine (packet ⟨1,by norm_num⟩)
    (projected P).IsPositive ∧ Conserving (projected P) ∧ projected P ≠ criticalOperator ∧
      (fourthMoment (projected P)).re < (riemannZeta 2).re := by
  let s : HeatVectorDomain := ⟨1,by norm_num⟩
  have hs : s.val.re ≤ 1 := by norm_num [s]
  exact ⟨projected_positive _,(packet_omission_iff s).mpr hs,
    omitted_packet_ne_critical s,packet_omission_loss ⟨s,hs⟩⟩

#print axioms packet_in_range_iff
#print axioms packet_omission_iff
#print axioms packet_omission_loss
#print axioms missing_direction

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
