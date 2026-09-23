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

/-- Literal defect of one depth-successor transport. -/
def depthSuccessorTransportDefect
    (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  depthSuccessorTransport f ε u - 1

/-- Depth transport after centering the dilation at `center`. -/
def centeredDepthSuccessorTransport
    (center : ℂ) (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  f u / f (center + (1 + ε) * (u - center))

/-- Depth transport reflected through the upper endpoint `1`. -/
def reflectedDepthSuccessorTransport
    (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  f u / f (1 - (1 + ε) * (1 - u))

/-- Balanced transport obtained by composing one literal lower-endpoint depth
step and one literal upper-endpoint reflected depth step, both at half aperture. -/
def twoEndpointBalancedDepthSuccessorTransport
    (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  f u /
    f (1 - (1 + ε / 2) * (1 - (1 + ε / 2) * u))

/-- Exact affine formula (11b) for the composite of the two literal endpoint
depth steps. -/
theorem twoEndpointBalancedDepthSuccessor_argument_eq
    (ε u : ℂ) :
    1 - (1 + ε / 2) * (1 - (1 + ε / 2) * u) =
      u + ε * (u - 1 / 2) + ε ^ (2 : ℕ) * u / 4 := by
  ring

/-- Exact moving-zero expansion (11d) of the two-endpoint composite. -/
theorem twoEndpointBalancedDepthSuccessor_argument_movingZero_sub
    (rho z ε : ℂ) :
    1 - (1 + ε / 2) *
        (1 - (1 + ε / 2) * (rho + ε * z)) - rho =
      ε * (z + rho - 1 / 2 +
        ε * (z + rho / 4) + ε ^ (2 : ℕ) * z / 4) := by
  ring

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
  congr 2 ; ring

/-- Upper-endpoint reflection is ordinary depth transport after reflecting the
carrier and spectral coordinate through `1`. -/
theorem reflectedDepthSuccessorTransport_eq_reflected
    (f : ℂ → ℂ) (ε u : ℂ) :
    reflectedDepthSuccessorTransport f ε u =
      depthSuccessorTransport (fun v => f (1 - v)) ε (1 - u) := by
  rw [reflectedDepthSuccessorTransport, depthSuccessorTransport]
  congr 2
  ring

/-- The balanced quotient factors through the two actual endpoint source steps.
The intermediate nonvanishing hypothesis is exactly what quotient cancellation
requires; the balanced quotient itself remains defined without it. -/
theorem twoEndpointBalancedDepthSuccessorTransport_eq_mul
    (f : ℂ → ℂ) (ε u : ℂ)
    (hmid : f ((1 + ε / 2) * u) ≠ 0) :
    twoEndpointBalancedDepthSuccessorTransport f ε u =
      depthSuccessorTransport f (ε / 2) u *
        reflectedDepthSuccessorTransport f (ε / 2)
          ((1 + ε / 2) * u) := by
  have hmid' : f (u * (ε + 2) / 2) ≠ 0 := by
    convert hmid using 2
    ring
  rw [twoEndpointBalancedDepthSuccessorTransport,
    depthSuccessorTransport, reflectedDepthSuccessorTransport]
  ring_nf
  field_simp [hmid']

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

/-- The literal depth defect has nearby layer `P_{rho,m} - 1` at a moving
order-`m` zero. -/
theorem tendsto_depthSuccessorTransportDefect_movingZero
    {f g : ℂ → ℂ} {rho z : ℂ} {m : ℕ}
    (hfac :
      f =ᶠ[𝓝 rho] fun w => (w - rho) ^ m * g w)
    (hg : ContinuousAt g rho) (hg0 : g rho ≠ 0)
    (hz : z + rho ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        depthSuccessorTransportDefect f ε (rho + ε * z))
      (𝓝[≠] 0)
      (𝓝 (depthSuccessorNearbyCycle rho m z - 1)) := by
  simpa only [depthSuccessorTransportDefect] using
    (tendsto_depthSuccessorTransport_movingZero
      hfac hg hg0 hz).sub_const 1

/-- At a fixed nonzero carrier value, the literal depth defect divided by its
aperture converges to the Euler logarithmic current. -/
theorem tendsto_depthSuccessorTransportDefect_differenceQuotient
    {f : ℂ → ℂ} {u : ℂ} (hf : DifferentiableAt ℂ f u)
    (hfu : f u ≠ 0) :
    Tendsto
      (fun ε : ℂ => ε⁻¹ * depthSuccessorTransportDefect f ε u)
      (𝓝[≠] 0)
      (𝓝 (-u * logDeriv f u)) := by
  have hzero : depthSuccessorTransport f 0 u = 1 := by
    simp [depthSuccessorTransport, hfu]
  simpa only [depthSuccessorTransportDefect, hzero,
    zero_add, smul_eq_mul] using
    (hasDerivAt_depthSuccessorTransport_zero hf hfu).tendsto_slope_zero

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
    convert hraw using 2
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

/-- The balanced critical-center profile is generated by two literal source
operations: lower-endpoint depth followed by upper-endpoint reflected depth.
Their composite differs from affine centering only at second order, which
disappears in the moving-zero normal layer. -/
theorem tendsto_twoEndpointBalancedDepthSuccessorTransport_movingZero
    {f g : ℂ → ℂ} {rho z : ℂ} {m : ℕ}
    (hfac :
      f =ᶠ[𝓝 rho] fun w => (w - rho) ^ m * g w)
    (hg : ContinuousAt g rho) (hg0 : g rho ≠ 0)
    (hz : z + (rho - 1 / 2) ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        twoEndpointBalancedDepthSuccessorTransport
          f ε (rho + ε * z))
      (𝓝[≠] 0)
      (𝓝 (centeredDepthSuccessorNearbyCycle
        (1 / 2) rho m z)) := by
  let shift : ℂ → ℂ := fun ε =>
    z + (rho - 1 / 2) +
      ε * (z + rho / 4) + ε ^ (2 : ℕ) * z / 4
  let target : ℂ → ℂ := fun ε =>
    1 - (1 + ε / 2) *
      (1 - (1 + ε / 2) * (rho + ε * z))
  have htarget_eq :
      ∀ ε : ℂ, target ε - rho = ε * shift ε := by
    intro ε
    dsimp only [target, shift]
    ring
  have harg0 :
      Tendsto (fun ε : ℂ => rho + ε * z) (𝓝 0) (𝓝 rho) := by
    simpa using
      (tendsto_const_nhds.add
        ((tendsto_id : Tendsto (fun ε : ℂ => ε) (𝓝 0) (𝓝 0)).mul_const z))
  have hshift :
      Tendsto shift (𝓝 0) (𝓝 (z + (rho - 1 / 2))) := by
    dsimp only [shift]
    have hε :
        Tendsto (fun ε : ℂ => ε) (𝓝 0) (𝓝 0) :=
      tendsto_id
    have hlinear :
        Tendsto (fun ε : ℂ => ε * (z + rho / 4))
          (𝓝 0) (𝓝 0) :=
      by simpa using hε.mul_const (z + rho / 4)
    have hquadratic :
        Tendsto (fun ε : ℂ => ε ^ (2 : ℕ) * z / 4)
          (𝓝 0) (𝓝 0) := by
      simpa using (hε.pow 2).mul_const z |>.div_const 4
    simpa using
      (tendsto_const_nhds.add hlinear).add hquadratic
  have htarget_fun :
      target = fun ε : ℂ => rho + ε * shift ε := by
    funext ε
    have h := htarget_eq ε
    have h' := sub_eq_iff_eq_add.mp h
    simpa [add_comm] using h'
  have harg1 : Tendsto target (𝓝 0) (𝓝 rho) := by
    rw [htarget_fun]
    simpa using
      (tendsto_const_nhds.add
        ((tendsto_id : Tendsto (fun ε : ℂ => ε) (𝓝 0) (𝓝 0)).mul hshift))
  have hgarg0 :
      Tendsto (fun ε : ℂ => g (rho + ε * z))
        (𝓝 0) (𝓝 (g rho)) :=
    hg.tendsto.comp harg0
  have hgarg1 :
      Tendsto (fun ε : ℂ => g (target ε))
        (𝓝 0) (𝓝 (g rho)) :=
    hg.tendsto.comp harg1
  have hprofile :
      Tendsto
        (fun ε : ℂ =>
          (z / shift ε) ^ m *
            (g (rho + ε * z) / g (target ε)))
        (𝓝 0)
        (𝓝 (centeredDepthSuccessorNearbyCycle
          (1 / 2) rho m z)) := by
    have hfirst :
        Tendsto (fun ε : ℂ => z / shift ε)
          (𝓝 0) (𝓝 (z / (z + (rho - 1 / 2)))) :=
      tendsto_const_nhds.div hshift hz
    have hsecond :
        Tendsto
          (fun ε : ℂ =>
            g (rho + ε * z) / g (target ε))
          (𝓝 0) (𝓝 (1 : ℂ)) := by
      change Tendsto
        ((fun ε : ℂ => g (rho + ε * z)) /
          (fun ε : ℂ => g (target ε)))
        (𝓝 0) (𝓝 (1 : ℂ))
      have hraw := hgarg0.div hgarg1 hg0
      simpa only [div_self hg0] using hraw
    simpa [centeredDepthSuccessorNearbyCycle,
      depthSuccessorNearbyCycle] using
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
        f (target ε) =
          (target ε - rho) ^ m * g (target ε) :=
    (harg1.mono_left hpunc).eventually hfac
  have hshift_ne :
      ∀ᶠ ε : ℂ in 𝓝[≠] 0, shift ε ≠ 0 :=
    (hshift.mono_left hpunc).eventually
      (eventually_ne_nhds hz)
  have hg1_ne :
      ∀ᶠ ε : ℂ in 𝓝[≠] 0, g (target ε) ≠ 0 :=
    (hgarg1.mono_left hpunc).eventually
      (eventually_ne_nhds hg0)
  filter_upwards [self_mem_nhdsWithin, hfac0, hfac1,
    hshift_ne, hg1_ne] with ε hε h0 h1 hs hg1
  symm
  rw [twoEndpointBalancedDepthSuccessorTransport, h0, h1]
  have hnum : rho + ε * z - rho = ε * z := by ring
  rw [hnum, htarget_eq ε]
  exact factorized_depth_ratio hε hs hg1

/-- The nearby-cycle profile retains the full algebraic multiplicity. -/
theorem denominator_pow_mul_depthSuccessorNearbyCycle
    {rho z : ℂ} {m : ℕ} (hz : z + rho ≠ 0) :
    (z + rho) ^ m * depthSuccessorNearbyCycle rho m z = z ^ m := by
  rw [depthSuccessorNearbyCycle, div_pow]
  field_simp

private theorem analyticOrderAt_sub_self_xiDepthNearby (w : ℂ) :
    analyticOrderAt (fun z : ℂ => z - w) w = 1 := by
  have h : AnalyticAt ℂ (fun z : ℂ => z - w) w :=
    analyticAt_id.sub analyticAt_const
  have hc := h.analyticOrderAt_eq_natCast (n := 1)
  rw [Nat.cast_one] at hc
  rw [hc]
  exact ⟨fun _ => 1, analyticAt_const, one_ne_zero,
    by filter_upwards with z using by simp⟩

/-- For a nonzero displacement, the nearby-cycle profile has a zero of
exact order `m` at `z = 0`. -/
theorem meromorphicOrderAt_depthSuccessorNearbyCycle_zero
    {rho : ℂ} (hrho : rho ≠ 0) (m : ℕ) :
    meromorphicOrderAt (depthSuccessorNearbyCycle rho m) 0 = (m : ℤ) := by
  let num : ℂ → ℂ := fun z => z ^ m
  let den : ℂ → ℂ := fun z => (z + rho) ^ m
  have hnumAn : AnalyticAt ℂ num 0 := by
    dsimp [num]
    fun_prop
  have hdenAn : AnalyticAt ℂ den 0 := by
    dsimp [den]
    fun_prop
  have hnumOrder : analyticOrderAt num 0 = (m : ℕ∞) := by
    have hbaseAn : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
    have hpow := analyticOrderAt_pow hbaseAn m
    have hbaseOrder : analyticOrderAt (fun z : ℂ => z) 0 = 1 := by
      change analyticOrderAt id 0 = 1
      exact analyticOrderAt_id
    rw [hbaseOrder] at hpow
    rw [show num = (fun z : ℂ => z) ^ m by
      funext z
      simp [num]]
    simpa using hpow
  have hdenOrder : analyticOrderAt den 0 = 0 := by
    exact hdenAn.analyticOrderAt_eq_zero.mpr (by
      simpa [den] using pow_ne_zero m hrho)
  rw [show depthSuccessorNearbyCycle rho m = num / den by
    funext z
    simp [depthSuccessorNearbyCycle, num, den, div_pow]]
  rw [meromorphicOrderAt_div hnumAn.meromorphicAt hdenAn.meromorphicAt,
    hnumAn.meromorphicOrderAt_eq, hdenAn.meromorphicOrderAt_eq,
    hnumOrder, hdenOrder]
  simp

/-- For a nonzero displacement, the nearby-cycle profile has a pole of
exact order `m` at `z = -rho`. -/
theorem meromorphicOrderAt_depthSuccessorNearbyCycle_pole
    {rho : ℂ} (hrho : rho ≠ 0) (m : ℕ) :
    meromorphicOrderAt (depthSuccessorNearbyCycle rho m) (-rho) =
      -(m : ℤ) := by
  let num : ℂ → ℂ := fun z => z ^ m
  let den : ℂ → ℂ := fun z => (z + rho) ^ m
  have hnumAn : AnalyticAt ℂ num (-rho) := by
    dsimp [num]
    fun_prop
  have hdenAn : AnalyticAt ℂ den (-rho) := by
    dsimp [den]
    fun_prop
  have hnumOrder : analyticOrderAt num (-rho) = 0 := by
    exact hnumAn.analyticOrderAt_eq_zero.mpr
      (pow_ne_zero m (neg_ne_zero.mpr hrho))
  have hlinearOrder : analyticOrderAt (fun z : ℂ => z + rho) (-rho) = 1 := by
    rw [show (fun z : ℂ => z + rho) = fun z => z - (-rho) by
      funext z
      ring]
    exact analyticOrderAt_sub_self_xiDepthNearby (-rho)
  have hdenOrder : analyticOrderAt den (-rho) = (m : ℕ∞) := by
    have hbaseAn : AnalyticAt ℂ (fun z : ℂ => z + rho) (-rho) :=
      analyticAt_id.add analyticAt_const
    have hpow := analyticOrderAt_pow hbaseAn m
    rw [hlinearOrder] at hpow
    rw [show den = (fun z : ℂ => z + rho) ^ m by
      funext z
      simp [den]]
    simpa using hpow
  rw [show depthSuccessorNearbyCycle rho m = num / den by
    funext z
    simp [depthSuccessorNearbyCycle, num, den, div_pow]]
  rw [meromorphicOrderAt_div hnumAn.meromorphicAt hdenAn.meromorphicAt,
    hnumAn.meromorphicOrderAt_eq, hdenAn.meromorphicOrderAt_eq,
    hnumOrder, hdenOrder]
  simp

/-- The inner nearby cycle matches the outer logarithmic connection. In the
inverse coordinate `w = 1 / z`, its first outer defect is exactly the
multiplicity-weighted connection residue `-m * shift`. -/
theorem tendsto_depthSuccessorNearbyCycle_outerCharge
    (shift : ℂ) (m : ℕ) :
    Tendsto
      (fun w : ℂ =>
        w⁻¹ * (depthSuccessorNearbyCycle shift m w⁻¹ - 1))
      (𝓝[≠] 0)
      (𝓝 (-((m : ℂ) * shift))) := by
  have hbase :
      Tendsto (fun w : ℂ => 1 + shift * w)
        (𝓝 0) (𝓝 1) := by
    simpa using
      (tendsto_const_nhds.add
        ((tendsto_id : Tendsto (fun w : ℂ => w) (𝓝 0) (𝓝 0)).const_mul shift))
  have hsum :
      Tendsto
        (fun w : ℂ =>
          ∑ i ∈ Finset.range m, (1 + shift * w) ^ i)
        (𝓝 0)
        (𝓝 (m : ℂ)) := by
    simpa using
      tendsto_finsetSum (Finset.range m)
        (fun i _ => hbase.pow i)
  have hprofile :
      Tendsto
        (fun w : ℂ =>
          (-shift) *
            (∑ i ∈ Finset.range m, (1 + shift * w) ^ i) /
              (1 + shift * w) ^ m)
        (𝓝 0)
        (𝓝 (-((m : ℂ) * shift))) := by
    have hconst :
        Tendsto (fun _ : ℂ => -shift)
          (𝓝 0) (𝓝 (-shift)) :=
      tendsto_const_nhds
    have hraw :=
      (hconst.mul hsum).div
        (hbase.pow m) (by simp)
    change Tendsto
      ((fun w : ℂ =>
          (-shift) *
            (∑ i ∈ Finset.range m, (1 + shift * w) ^ i)) /
        (fun w : ℂ => (1 + shift * w) ^ m))
      (𝓝 0)
      (𝓝 (-((m : ℂ) * shift)))
    simpa [mul_comm, mul_left_comm] using hraw
  refine (hprofile.mono_left nhdsWithin_le_nhds).congr' ?_
  have hbase_ne :
      ∀ᶠ w : ℂ in 𝓝[≠] 0, 1 + shift * w ≠ 0 :=
    (hbase.mono_left nhdsWithin_le_nhds).eventually
      (eventually_ne_nhds one_ne_zero)
  filter_upwards [self_mem_nhdsWithin, hbase_ne] with w hw hb
  have hwe : w ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using hw
  have hnearby :
      depthSuccessorNearbyCycle shift m w⁻¹ =
        ((1 + shift * w)⁻¹) ^ m := by
    rw [depthSuccessorNearbyCycle]
    congr 1
    have hden :
        w⁻¹ + shift = w⁻¹ * (1 + w * shift) := by
      symm
      rw [mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ hwe, one_mul]
    calc
      w⁻¹ / (w⁻¹ + shift)
          = w⁻¹ * (w⁻¹ * (1 + w * shift))⁻¹ := by
              rw [div_eq_mul_inv, hden]
      _ = w⁻¹ * ((1 + w * shift)⁻¹ * (w⁻¹)⁻¹) := by
            rw [mul_inv_rev]
      _ = (1 + shift * w)⁻¹ := by
            rw [inv_inv, mul_comm ((1 + w * shift)⁻¹) w,
              ← mul_assoc, inv_mul_cancel₀ hwe, one_mul]
            congr 1
            ring
  rw [hnearby]
  simp only [inv_pow]
  have hgeom :=
    geom_sum_mul (1 + shift * w) m
  have hqsub : 1 + shift * w - 1 = shift * w := by ring
  rw [hqsub] at hgeom
  field_simp [hwe, hb]
  linear_combination -hgeom

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

/-- Equality of the full source-inverse and analytic-adjoint nearby-cycle
profiles at positive multiplicity already forces the centered displacement
to be purely imaginary.  This supplies the divisor-equality implication
used in the paper, rather than assuming equality of encoded pole coordinates. -/
theorem re_eq_zero_of_inverse_adjoint_nearbyCycle_eq
    {a : ℂ} {m : ℕ} (hm : 0 < m)
    (h :
      depthSuccessorNearbyCycle (-a) m =
        depthSuccessorNearbyCycle (starRingEnd ℂ a) m) :
    a.re = 0 := by
  by_contra hre
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp at hre
  have hden : a + starRingEnd ℂ a ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp at hreal
    exact hre (by linarith)
  have hlhs : depthSuccessorNearbyCycle (-a) m a = 0 := by
    simp [depthSuccessorNearbyCycle, Nat.ne_of_gt hm]
  have hrhs : depthSuccessorNearbyCycle (starRingEnd ℂ a) m a ≠ 0 := by
    rw [depthSuccessorNearbyCycle]
    exact pow_ne_zero _ (div_ne_zero ha hden)
  have hvalue := congrFun h a
  rw [hlhs] at hvalue
  exact hrhs hvalue.symm

/-- Equality of the full inverse/adjoint profiles implies equality of their
encoded pole divisors when the multiplicity is positive. -/
theorem inverse_adjoint_nearbyPole_eq_of_nearbyCycle_eq
    {a : ℂ} {m : ℕ} (hm : 0 < m)
    (h :
      depthSuccessorNearbyCycle (-a) m =
        depthSuccessorNearbyCycle (starRingEnd ℂ a) m) :
    depthSuccessorNearbyPole (-a) =
      depthSuccessorNearbyPole (starRingEnd ℂ a) := by
  have hre := re_eq_zero_of_inverse_adjoint_nearbyCycle_eq hm h
  have haeq : a = -(starRingEnd ℂ a) := by
    apply Complex.ext
    · simp [hre]
    · simp
  simpa [depthSuccessorNearbyPole] using haeq

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Xi depth transport balanced by the two literal endpoint source steps. -/
def xiBalancedDepthSuccessorTransport (ε u : ℂ) : ℂ :=
  twoEndpointBalancedDepthSuccessorTransport xi ε u

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

/-- At an actual Xi zero, the literal unrenormalized depth defect converges
on the moving scale to the rational nearby cycle minus one. -/
theorem tendsto_xiDepthSuccessorTransportDefect_movingZero
    {rho z : ℂ} (hzero : xi rho = 0) (hz : z + rho ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        depthSuccessorTransportDefect xi ε (rho + ε * z))
      (𝓝[≠] 0)
      (𝓝 (depthSuccessorNearbyCycle rho
        (analyticOrderAt xi rho).toNat z - 1)) := by
  simpa only [depthSuccessorTransportDefect,
    xiDepthSuccessorTransport] using
    (tendsto_xiDepthSuccessorTransport_movingZero hzero hz).sub_const 1

/-- Away from the Xi divisor, the same literal defect has the outer
fixed-spectral-point limit `-u * Xi'/Xi`. -/
theorem tendsto_xiDepthSuccessorTransportDefect_differenceQuotient
    {u : ℂ} (hu : xi u ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        ε⁻¹ * depthSuccessorTransportDefect xi ε u)
      (𝓝[≠] 0)
      (𝓝 (-u * logDeriv xi u)) := by
  exact tendsto_depthSuccessorTransportDefect_differenceQuotient
    (xi_differentiable u) hu

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
    tendsto_twoEndpointBalancedDepthSuccessorTransport_movingZero
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

/-- At an actual Xi zero, the balanced nearby cycle has exact zero order
equal to the full Xi multiplicity. -/
theorem meromorphicOrderAt_xiCenteredNearbyCycle_zero
    {rho : ℂ} (hzero : xi rho = 0) :
    meromorphicOrderAt
        (centeredDepthSuccessorNearbyCycle (1 / 2) rho
          (analyticOrderAt xi rho).toNat) 0 =
      ((analyticOrderAt xi rho).toNat : ℤ) := by
  let q : ↥(MeromorphicOn.divisor xi Set.univ).support :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hshift : rho - 1 / 2 ≠ 0 :=
    sub_ne_zero.mpr (xi_divisor_support_ne_half q)
  rw [show centeredDepthSuccessorNearbyCycle (1 / 2) rho
      (analyticOrderAt xi rho).toNat =
      depthSuccessorNearbyCycle (rho - 1 / 2)
        (analyticOrderAt xi rho).toNat by rfl]
  exact meromorphicOrderAt_depthSuccessorNearbyCycle_zero hshift
    (analyticOrderAt xi rho).toNat

/-- At an actual Xi zero, the balanced nearby cycle has exact pole order
equal to the negative full Xi multiplicity. -/
theorem meromorphicOrderAt_xiCenteredNearbyCycle_pole
    {rho : ℂ} (hzero : xi rho = 0) :
    meromorphicOrderAt
        (centeredDepthSuccessorNearbyCycle (1 / 2) rho
          (analyticOrderAt xi rho).toNat)
        (-(rho - 1 / 2)) =
      -((analyticOrderAt xi rho).toNat : ℤ) := by
  let q : ↥(MeromorphicOn.divisor xi Set.univ).support :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hshift : rho - 1 / 2 ≠ 0 :=
    sub_ne_zero.mpr (xi_divisor_support_ne_half q)
  rw [show centeredDepthSuccessorNearbyCycle (1 / 2) rho
      (analyticOrderAt xi rho).toNat =
      depthSuccessorNearbyCycle (rho - 1 / 2)
        (analyticOrderAt xi rho).toNat by rfl]
  exact meromorphicOrderAt_depthSuccessorNearbyCycle_pole hshift
    (analyticOrderAt xi rho).toNat

/-- Full-profile form of the nearby-layer RH consumer.  At an actual Xi
zero, equality of the source-inverse and analytic-adjoint rational cycles
forces the critical line; equality of their pole coordinates is derived. -/
theorem criticalLine_of_inverse_adjoint_nearbyCycle_eq
    {rho : ℂ} (hzero : xi rho = 0)
    (h :
      depthSuccessorNearbyCycle (-(rho - 1 / 2))
          (analyticOrderAt xi rho).toNat =
        depthSuccessorNearbyCycle (starRingEnd ℂ (rho - 1 / 2))
          (analyticOrderAt xi rho).toNat) :
    rho.re = 1 / 2 := by
  apply criticalLine_of_inverse_adjoint_nearbyPole_eq rho
  exact inverse_adjoint_nearbyPole_eq_of_nearbyCycle_eq
    (xiDepthSuccessorNearbyCycle_multiplicity_pos hzero) h

end RHTower
