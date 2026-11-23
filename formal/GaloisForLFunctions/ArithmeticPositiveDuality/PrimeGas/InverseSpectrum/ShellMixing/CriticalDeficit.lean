import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.HoleMoment
import GaloisForLFunctions.RHTower.InvZetaCriticalLaurent

/-!
# Sharp loss of the fourth trace near the critical line

A missing heat direction at distance δ from the critical line costs
4 ζ(3) δ to first order, independently of the clock height.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ContinuousLinearMap

def approachingPacket (t : ℝ) (δ : PacketScale) : HeatVectorDomain :=
  ⟨((1/2+δ.val : ℝ):ℂ)+(t:ℂ)*Complex.I,by simpa using δ.property⟩

private theorem mass_approaching (t : ℝ) (δ : PacketScale) :
    massParameter (approachingPacket t δ) = 1+2*(δ.val:ℂ) := by
  rw [massParameter_real]
  simp only [approachingPacket,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  push_cast
  ring

def approachingPropagator (t : ℝ) (δ : PacketScale) : GasOp :=
  projected (omitLine (packet (approachingPacket t δ)))

/-- The omitted packets conserve on the entire half-open interval of distances through one half. -/
theorem approaching_conservation (t : ℝ) (δ : PacketScale) :
    Conserving (approachingPropagator t δ) ↔ δ.val ≤ 1/2 := by
  rw [approachingPropagator,packet_omission_iff]
  simp only [approachingPacket,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  constructor <;> intro h <;> linarith only [h]

private theorem scale_tends : Tendsto (fun δ : PacketScale => (δ.val:ℂ)) packetPole (𝓝 0) :=
  (Complex.continuous_ofReal.tendsto 0).comp
    (tendsto_comap.mono_right nhdsWithin_le_nhds : Tendsto Subtype.val packetPole (𝓝 (0:ℝ)))

private theorem translated_partition (a : {z : ℂ // z ≠ 1}) :
    Tendsto (fun δ : PacketScale => riemannZeta (a.val+2*(δ.val:ℂ))) packetPole (𝓝 (riemannZeta a.val)) := by
  have h := tendsto_const_nhds (x := a.val) |>.add (scale_tends.const_mul 2)
  rw [mul_zero,add_zero] at h
  exact (differentiableAt_riemannZeta a.property).continuousAt.tendsto.comp h

/-- The fourth-trace deficit per unit distance has the universal limit four times zeta at three. -/
theorem critical_deficit_slope (t : ℝ) :
    Tendsto (fun δ : PacketScale => (riemannZeta 2-opTrace ((approachingPropagator t δ)^4))/(δ.val:ℂ))
      packetPole (𝓝 (4*riemannZeta 3)) := by
  let q := fun δ : PacketScale => (riemannZeta (1+2*(δ.val:ℂ)))⁻¹/(δ.val:ℂ)
  have hq : Tendsto q packetPole (𝓝 2) :=
    _root_.RHTower.tendsto_inv_riemannZeta_one_add_two_mul_div.comp tendsto_comap
  have h₂ := translated_partition ⟨2,by norm_num⟩
  have h₃ := translated_partition ⟨3,by norm_num⟩
  have h := ((h₃.mul hq).const_mul 2).sub (scale_tends.mul ((h₂.mul hq).pow 2))
  change Tendsto _ packetPole (𝓝 (2*(riemannZeta 3*2)-0*(riemannZeta 2*2)^2)) at h
  rw [zero_mul,sub_zero,show 2*(riemannZeta 3*2) = 4*riemannZeta 3 by ring] at h
  apply h.congr
  intro δ
  rw [approachingPropagator,omitted_packet_trace,mass_approaching]
  dsimp only [q]
  rw [show (1+2*(δ.val:ℂ))+2 = 3+2*(δ.val:ℂ) by ring,
    show (1+2*(δ.val:ℂ))+1 = 2+2*(δ.val:ℂ) by ring]
  have hδ := Complex.ofReal_ne_zero.mpr δ.property.ne'
  simp only [div_eq_mul_inv]
  generalize (riemannZeta (1+2*(δ.val:ℂ)))⁻¹ = r
  field_simp [hδ]
  ring

/-- The strict noncanonical trace readings accumulate at the canonical reading at every height. -/
theorem critical_trace_limit (t : ℝ) :
    Tendsto (fun δ : PacketScale => opTrace ((approachingPropagator t δ)^4)) packetPole (𝓝 (riemannZeta 2)) := by
  have h := tendsto_const_nhds (x := riemannZeta 2) |>.sub ((critical_deficit_slope t).mul scale_tends)
  rw [mul_zero,sub_zero] at h
  apply h.congr
  intro δ
  rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr δ.property.ne'),sub_sub_cancel]

#print axioms approaching_conservation
#print axioms critical_deficit_slope
#print axioms critical_trace_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
