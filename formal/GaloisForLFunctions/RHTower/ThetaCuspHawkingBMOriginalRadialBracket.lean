import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceWronskian
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSpatialODE

/-! The actual original radial Green bracket, including its forcing weight. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The physical integrating factor applied to the actual two radial jets. -/
def radialBracket (U D V E : ℝ → ℂ) (b : ℝ) : ℂ :=
  integratingFactor b * (U b * E b - D b * V b)

/-- The weight dictated by the original normalized radial equation. -/
def radialPairingWeight (b : ℝ) : ℂ := power (1/2) (1-b) / (1-(b:ℂ))

/-- Differentiated Green identity for the original operator, with actual jets. -/
theorem radialBracket_hasDerivAt (w chi : ℂ) {U D DD V E EE : ℝ → ℂ}
    {b : ℝ} (hb : b ∈ Ioo 0 1)
    (hU : HasDerivAt U (D b) b) (hD : HasDerivAt D (DD b) b)
    (hV : HasDerivAt V (E b) b) (hE : HasDerivAt E (EE b) b) :
    HasDerivAt (radialBracket U D V E)
      (radialPairingWeight b *
        (U b * D4BMPhysicalMaster.radialJet (I*w) chi b (V b) (E b) (EE b) -
         V b * D4BMPhysicalMaster.radialJet (I*w) chi b (U b) (D b) (DD b))) b := by
  have hp := (power_derivatives (1/2) (sub_pos.mpr hb.2)).1.scomp b
    ((hasDerivAt_id b).const_sub (1:ℝ))
  have hfac : HasDerivAt integratingFactor
      (power (1/2) (1-b)-(b:ℂ)*powerFirst (1/2) (1-b)) b := by
    convert! ((hasDerivAt_id b).ofReal_comp.mul hp) using 1
    simp [sub_eq_add_neg]
  apply (hfac.mul ((hU.mul hE).sub (hD.mul hV))).congr_deriv
  have hb0 : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.1.ne'
  have hx0 : 1-(b:ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hb.2).ne'
  dsimp [radialPairingWeight,integratingFactor,powerFirst,D4BMPhysicalMaster.radialJet]
  push_cast
  field_simp [hb0,hx0]
  ring

/-- Abel constancy for any two actual homogeneous solutions of the original equation. -/
theorem radialBracket_constant (w chi : ℂ) {U D DD V E EE : ℝ → ℂ}
    (hU : ∀ b ∈ Ioo 0 1, HasDerivAt U (D b) b)
    (hD : ∀ b ∈ Ioo 0 1, HasDerivAt D (DD b) b)
    (hV : ∀ b ∈ Ioo 0 1, HasDerivAt V (E b) b)
    (hE : ∀ b ∈ Ioo 0 1, HasDerivAt E (EE b) b)
    (hLU : ∀ b : ℝ, b ∈ Ioo 0 1 → D4BMPhysicalMaster.radialJet (I*w) chi b (U b) (D b) (DD b)=0)
    (hLV : ∀ b : ℝ, b ∈ Ioo 0 1 → D4BMPhysicalMaster.radialJet (I*w) chi b (V b) (E b) (EE b)=0)
    {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    radialBracket U D V E x = radialBracket U D V E y := by
  have hd (b : ℝ) (hb : b ∈ Ioo 0 1) : HasDerivAt (radialBracket U D V E) 0 b := by
    simpa only [hLU b hb,hLV b hb,mul_zero,sub_self] using
      radialBracket_hasDerivAt w chi hb (hU b hb) (hD b hb) (hV b hb) (hE b hb)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun b hb => (hd b hb).differentiableAt.differentiableWithinAt)
    (fun b hb => (hd b hb).deriv) hx hy

end
end RHTower.D4BMLaplaceRadial
