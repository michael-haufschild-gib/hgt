import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# Xi depth-successor Stokes normal layer

Fixed spectral points see the infinitesimal depth successor as the Xi logarithmic
connection. At a moving Xi zero that limit is nonuniform. Blowing up the spectral
coordinate at the same rate as exponent depth gives a universal rational nearby-cycle
profile. Centering depth at the functional-equation fixed point exposes the full
horizontal displacement and multiplicity.

This is a local source-to-divisor interface, not an RH proof. The final theorem records
the exact same-fibre pole identification which a source-derived dagger landing would
have to provide.
-/

open Complex Filter Set
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Normal-layer profile of one depth-successor step at a zero of order `m`. -/
def depthSuccessorNearbyCycle (rho : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  (z / (z + rho)) ^ m

/-- Depth transport after centering the dilation at `center`. -/
def centeredDepthSuccessorTransport
    (center : ℂ) (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  f u / f (center + (1 + ε) * (u - center))

/-- The corresponding moving-zero normal layer. -/
def centeredDepthSuccessorNearbyCycle
    (center rho : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  depthSuccessorNearbyCycle (rho - center) m z

/-- Centered transport is ordinary depth transport of the translated carrier. -/
theorem centeredDepthSuccessorTransport_eq_translated
    (center : ℂ) (f : ℂ → ℂ) (ε u : ℂ) :
    centeredDepthSuccessorTransport center f ε u =
      depthSuccessorTransport (fun v => f (center + v)) ε (u - center) := by
  rw [centeredDepthSuccessorTransport, depthSuccessorTransport]
  congr 2 <;> ring

private theorem factorized_depth_ratio
    {ε z shift g₀ g₁ : ℂ} {m : ℕ}
    (hε : ε ≠ 0) (hshift : shift ≠ 0) (hg₁ : g₁ ≠ 0) :
    ((ε * z) ^ m * g₀) / ((ε * shift) ^ m * g₁) =
      (z / shift) ^ m * (g₀ / g₁) := by
  rw [mul_pow, mul_pow, div_pow]
  field_simp

/-- A moving depth successor through a zero has a universal rational normal profile.
The theorem needs only a local order-`m` factorization, so it applies to every analytic
carrier of finite vanishing order. -/
theorem tendsto_depthSuccessorTransport_movingZero
    {f g : ℂ → ℂ} {rho z : ℂ} {m : ℕ}
    (hfac :
      f =ᶠ[𝓝 rho] fun w => (w - rho) ^ m * g w)
    (hg : ContinuousAt g rho) (hg0 : g rho ≠ 0)
    (hz : z + rho ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        depthSuccessorTransport f ε (rho + ε * z))
      (𝓝[≠] 0)
      (𝓝 (depthSuccessorNearbyCycle rho m z)) := by
  have harg0 :
      Tendsto (fun ε : ℂ => rho + ε * z) (𝓝 0) (𝓝 rho) := by
    simpa using
      (tendsto_const_nhds.add
        ((tendsto_id : Tendsto (fun ε : ℂ => ε) (𝓝 0) (𝓝 0)).mul_const z))
  have harg1 :
      Tendsto (fun ε : ℂ => (1 + ε) * (rho + ε * z))
        (𝓝 0) (𝓝 rho) := by
    have hone :
        Tendsto (fun ε : ℂ => 1 + ε) (𝓝 0) (𝓝 1) := by
      simpa using
        (tendsto_const_nhds.add
          (tendsto_id : Tendsto (fun ε : ℂ => ε) (𝓝 0) (𝓝 0)))
    simpa using hone.mul harg0
  have hshift :
      Tendsto (fun ε : ℂ => z + rho + ε * z)
        (𝓝 0) (𝓝 (z + rho)) := by
    simpa using
      (tendsto_const_nhds.add
        ((tendsto_id : Tendsto (fun ε : ℂ => ε) (𝓝 0) (𝓝 0)).mul_const z))
  have hgarg0 :
      Tendsto (fun ε : ℂ => g (rho + ε * z))
        (𝓝 0) (𝓝 (g rho)) :=
    hg.tendsto.comp harg0
  have hgarg1 :
      Tendsto (fun ε : ℂ => g ((1 + ε) * (rho + ε * z)))
        (𝓝 0) (𝓝 (g rho)) :=
    hg.tendsto.comp harg1
  have hprofile :
      Tendsto
        (fun ε : ℂ =>
          (z / (z + rho + ε * z)) ^ m *
            (g (rho + ε * z) /
              g ((1 + ε) * (rho + ε * z))))
        (𝓝 0)
        (𝓝 (depthSuccessorNearbyCycle rho m z)) := by
    have hfirst :
        Tendsto (fun ε : ℂ => z / (z + rho + ε * z))
          (𝓝 0) (𝓝 (z / (z + rho))) :=
      tendsto_const_nhds.div hshift hz
    have hsecond :
        Tendsto
          (fun ε : ℂ =>
            g (rho + ε * z) /
              g ((1 + ε) * (rho + ε * z)))
          (𝓝 0) (𝓝 (1 : ℂ)) := by
      change Tendsto
        ((fun ε : ℂ => g (rho + ε * z)) /
          (fun ε : ℂ => g ((1 + ε) * (rho + ε * z))))
        (𝓝 0) (𝓝 (1 : ℂ))
      have hraw := hgarg0.div hgarg1 hg0
      simpa only [div_self hg0] using hraw
    simpa [depthSuccessorNearbyCycle] using
      (hfirst.pow m).mul hsecond
  refine (hprofile.mono_left nhdsWithin_le_nhds).congr' ?_
  have hpunc : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hfac0 :
      ∀ᶠ ε : ℂ in 𝓝[≠] 0,
        f (rho + ε * z) =
          (rho + ε * z - rho) ^ m * g (rho + ε * z) :=
    (harg0.mono_left hpunc).eventually hfac
  have hfac1 :
      ∀ᶠ ε : ℂ in 𝓝[≠] 0,
        f ((1 + ε) * (rho + ε * z)) =
          ((1 + ε) * (rho + ε * z) - rho) ^ m *
            g ((1 + ε) * (rho + ε * z)) :=
    (harg1.mono_left hpunc).eventually hfac
  have hshift_ne :
      ∀ᶠ ε : ℂ in 𝓝[≠] 0, z + rho + ε * z ≠ 0 :=
    (hshift.mono_left hpunc).eventually
      (eventually_ne_nhds hz)
  have hg1_ne :
      ∀ᶠ ε : ℂ in 𝓝[≠] 0,
        g ((1 + ε) * (rho + ε * z)) ≠ 0 :=
    (hgarg1.mono_left hpunc).eventually
      (eventually_ne_nhds hg0)
  filter_upwards [self_mem_nhdsWithin, hfac0, hfac1,
    hshift_ne, hg1_ne] with ε hε h0 h1 hs hg1
  symm
  rw [depthSuccessorTransport, h0, h1]
  have hnum : rho + ε * z - rho = ε * z := by ring
  have hden :
      (1 + ε) * (rho + ε * z) - rho =
        ε * (z + rho + ε * z) := by ring
  rw [hnum, hden]
  exact factorized_depth_ratio hε hs hg1

/-- Centering changes the normal-layer displacement from `rho` to `rho - center`. -/
theorem tendsto_centeredDepthSuccessorTransport_movingZero
    {f g : ℂ → ℂ} {center rho z : ℂ} {m : ℕ}
    (hfac :
      f =ᶠ[𝓝 rho] fun w => (w - rho) ^ m * g w)
    (hg : ContinuousAt g rho) (hg0 : g rho ≠ 0)
    (hz : z + (rho - center) ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        centeredDepthSuccessorTransport center f ε (rho + ε * z))
      (𝓝[≠] 0)
      (𝓝 (centeredDepthSuccessorNearbyCycle center rho m z)) := by
  let F : ℂ → ℂ := fun v => f (center + v)
  let G : ℂ → ℂ := fun v => g (center + v)
  have htranslate :
      Tendsto (fun v : ℂ => center + v)
        (𝓝 (rho - center)) (𝓝 rho) := by
    have hraw :
        Tendsto (fun v : ℂ => center + v)
          (𝓝 (rho - center)) (𝓝 (center + (rho - center))) :=
      (continuousAt_const.add continuousAt_id).tendsto
    convert hraw using 1
    ring
  have hfacF :
      F =ᶠ[𝓝 (rho - center)]
        fun v => (v - (rho - center)) ^ m * G v := by
    have hpull := htranslate.eventually hfac
    filter_upwards [hpull] with v hv
    dsimp only [F, G]
    rw [hv]
    congr 2
    ring
  have hG : ContinuousAt G (rho - center) := by
    rw [ContinuousAt]
    change Tendsto (fun v : ℂ => g (center + v))
      (𝓝 (rho - center)) (𝓝 (g (center + (rho - center))))
    have hraw := hg.tendsto.comp htranslate
    convert hraw using 1
    · ext v
      rfl
    · congr 3
      ring
  have hlim :=
    tendsto_depthSuccessorTransport_movingZero
      hfacF hG (by simpa [G] using hg0) hz
  apply hlim.congr'
  filter_upwards [] with ε
  rw [centeredDepthSuccessorTransport_eq_translated]
  congr 2
  ring

/-- The nearby-cycle profile retains the full algebraic multiplicity. -/
theorem denominator_pow_mul_depthSuccessorNearbyCycle
    {rho z : ℂ} {m : ℕ} (hz : z + rho ≠ 0) :
    (z + rho) ^ m * depthSuccessorNearbyCycle rho m z = z ^ m := by
  rw [depthSuccessorNearbyCycle, div_pow]
  field_simp

/-- Pole coordinate of a nonconstant nearby-cycle profile. -/
def depthSuccessorNearbyPole (shift : ℂ) : ℂ := -shift

/-- Equality of source-inverse and analytic-adjoint nearby-cycle poles forces
the centered displacement to be purely imaginary. -/
theorem re_eq_zero_of_inverse_adjoint_nearbyPole_eq
    {a : ℂ}
    (h :
      depthSuccessorNearbyPole (-a) =
        depthSuccessorNearbyPole (starRingEnd ℂ a)) :
    a.re = 0 := by
  have hre := congrArg Complex.re h
  simp [depthSuccessorNearbyPole] at hre
  linarith

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Xi depth transport centered at the functional-equation fixed point. -/
def xiBalancedDepthSuccessorTransport (ε u : ℂ) : ℂ :=
  centeredDepthSuccessorTransport (1 / 2) xi ε u

/-- The completed Xi depth successor has an explicit normal-layer limit at every
divisor point. Its exponent is the full analytic multiplicity of that point. -/
theorem tendsto_xiDepthSuccessorTransport_movingZero
    {rho z : ℂ} (_hzero : xi rho = 0) (hz : z + rho ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        xiDepthSuccessorTransport ε (rho + ε * z))
      (𝓝[≠] 0)
      (𝓝 (depthSuccessorNearbyCycle rho
        (analyticOrderAt xi rho).toNat z)) := by
  have hfinite : analyticOrderAt xi rho ≠ ⊤ :=
    xi_order_ne_top rho
  have horder :
      analyticOrderAt xi rho =
        (((analyticOrderAt xi rho).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat hfinite).symm
  obtain ⟨g, hgan, hg0, hfac⟩ :=
    (xi_analyticOnNhd_univ rho (Set.mem_univ rho)).analyticOrderAt_eq_natCast.mp
      horder
  have hfac' :
      xi =ᶠ[𝓝 rho]
        fun w => (w - rho) ^ (analyticOrderAt xi rho).toNat * g w := by
    filter_upwards [hfac] with w hw
    simpa only [smul_eq_mul] using hw
  simpa only [xiDepthSuccessorTransport] using
    tendsto_depthSuccessorTransport_movingZero
      hfac' hgan.continuousAt hg0 hz

/-- The balanced Xi depth successor exposes the centered displacement
`rho - 1/2` as its exact moving-zero normal profile. -/
theorem tendsto_xiBalancedDepthSuccessorTransport_movingZero
    {rho z : ℂ} (_hzero : xi rho = 0)
    (hz : z + (rho - 1 / 2) ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        xiBalancedDepthSuccessorTransport ε (rho + ε * z))
      (𝓝[≠] 0)
      (𝓝 (centeredDepthSuccessorNearbyCycle
        (1 / 2) rho (analyticOrderAt xi rho).toNat z)) := by
  have hfinite : analyticOrderAt xi rho ≠ ⊤ :=
    xi_order_ne_top rho
  have horder :
      analyticOrderAt xi rho =
        (((analyticOrderAt xi rho).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat hfinite).symm
  obtain ⟨g, hgan, hg0, hfac⟩ :=
    (xi_analyticOnNhd_univ rho (Set.mem_univ rho)).analyticOrderAt_eq_natCast.mp
      horder
  have hfac' :
      xi =ᶠ[𝓝 rho]
        fun w => (w - rho) ^ (analyticOrderAt xi rho).toNat * g w := by
    filter_upwards [hfac] with w hw
    simpa only [smul_eq_mul] using hw
  simpa only [xiBalancedDepthSuccessorTransport] using
    tendsto_centeredDepthSuccessorTransport_movingZero
      hfac' hgan.continuousAt hg0 hz

/-- Literal nearby-pole RH consumer: if source inverse and analytic adjoint
identify the same centered normal-layer pole, the point is critical. -/
theorem criticalLine_of_inverse_adjoint_nearbyPole_eq
    (rho : ℂ)
    (h :
      depthSuccessorNearbyPole (-(rho - 1 / 2)) =
        depthSuccessorNearbyPole (starRingEnd ℂ (rho - 1 / 2))) :
    rho.re = 1 / 2 := by
  have ha :
      (rho - 1 / 2).re = 0 :=
    re_eq_zero_of_inverse_adjoint_nearbyPole_eq h
  norm_num at ha ⊢
  linarith

/-- At an actual Xi zero, the normal-layer exponent is positive. -/
theorem xiDepthSuccessorNearbyCycle_multiplicity_pos
    {rho : ℂ} (hzero : xi rho = 0) :
    0 < (analyticOrderAt xi rho).toNat :=
  Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)

end RHTower
