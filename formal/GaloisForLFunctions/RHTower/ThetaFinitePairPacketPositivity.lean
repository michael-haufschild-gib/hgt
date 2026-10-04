import GaloisForLFunctions.RHTower.ThetaFinitePairPacketTail
import GaloisForLFunctions.RHTower.ThetaTailOrderedRowMonotonicity

/-! Global positivity of the actual matched finite-pair transport packet.
The exact signed forcing has one crossing, while the source-weighted packet
has zero tail. An integrating factor transfers those facts without dropping
the signed normalized packet coordinate. -/

noncomputable section
open Set Filter Topology MeasureTheory
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => H 0 0
local notation "s" => ThetaSturmCrossing.secant
local notation "j" => ThetaSturmCrossing.intercept
local notation "F" => ThetaSturmCrossing.forcing

private theorem center_pos : 0 < J := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0

/-- The complete packet evolution retains both its signed coordinates. -/
theorem matchedPacket_hasDerivAt {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (matchedPacket x)
      ((p t+p (t+x)+2*j x t)*matchedPacket x t+F x t*transportPrimitive x t) t := by
  convert! (normalizedPacket_hasDerivAt hx t).add
    ((ThetaSturmCrossing.secant_hasDerivAt x t).mul (transportPrimitive_hasDerivAt hx t)) using 1
  dsimp only [matchedPacket,ThetaSturmCrossing.intercept,ThetaSturmCrossing.forcing,
    ThetaSturmCrossing.secant]
  rw [add_comm x t]
  field_simp [hx.ne']
  ring

theorem weightedPacket_hasDerivAt {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (weightedPacket x)
      (2*j x t*weightedPacket x t+F x t*prefixBalance x t/(x*J)) t := by
  have hk := (actualSource_hasDerivAt (t+x)).comp t ((hasDerivAt_id t).add_const x)
  convert! ((actualSource_hasDerivAt t).mul hk).mul (matchedPacket_hasDerivAt hx t) using 1
  dsimp only [weightedPacket,transportPrimitive,Function.comp_apply,Pi.mul_apply,id_eq]
  rw [add_comm x t]
  field_simp [hx.ne',center_pos.ne',(thetaCuspFullSource_pos_all t).ne',
    (thetaCuspFullSource_pos_all (t+x)).ne']
  ring

def packetDamping (x t : ℝ) : ℝ := Real.exp (-2*(∫ u in 0..t, j x u))
def dampedPacket (x t : ℝ) : ℝ := packetDamping x t*weightedPacket x t

private theorem intercept_continuous (x : ℝ) : Continuous (j x) :=
  continuous_iff_continuousAt.mpr fun t => (ThetaSturmCrossing.intercept_hasDerivAt x t).continuousAt

theorem packetDamping_hasDerivAt (x t : ℝ) :
    HasDerivAt (packetDamping x) (-2*j x t*packetDamping x t) t := by
  have hc := intercept_continuous x
  have hi := intervalIntegral.integral_hasDerivAt_right (a := 0) (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt
  convert! (hi.const_mul (-2)).exp using 1
  dsimp only [packetDamping]
  ring

private theorem packetDamping_pos (x t : ℝ) : 0 < packetDamping x t := Real.exp_pos _

private theorem intercept_nonneg {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) : 0 ≤ j x t := by
  rcases ht.eq_or_lt with he | he
  · rw [← he]
    simp only [ThetaSturmCrossing.intercept,zero_mul,thetaCuspLogDecaySlope,
      iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero,sub_self,le_refl]
  · exact (ThetaSturmCrossing.intercept_pos hx he).le

private theorem packetDamping_le_one {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    packetDamping x t ≤ 1 := by
  have hi : 0 ≤ ∫ u in 0..t, j x u :=
    intervalIntegral.integral_nonneg ht (fun u hu => intercept_nonneg hx hu.1)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hi)

/-- The integrating factor exposes exactly the already classified source forcing. -/
theorem dampedPacket_hasDerivAt {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasDerivAt (dampedPacket x)
      (packetDamping x t*F x t*prefixBalance x t/(x*J)) t := by
  convert! (packetDamping_hasDerivAt x t).mul (weightedPacket_hasDerivAt hx t) using 1
  ring

theorem dampedPacket_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (dampedPacket x) atTop (𝓝 0) := by
  apply bdd_le_mul_tendsto_zero (b := 0) (B := 1)
  · exact Eventually.of_forall fun t => (packetDamping_pos x t).le
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact packetDamping_le_one hx ht
  · exact weightedPacket_limit hx

theorem matchedPacket_zero_pos {x : ℝ} (hx : 0 < x) : 0 < matchedPacket x 0 := by
  have h := ThetaTailRow.strictAntiOn_normalized_row (x := 0) (le_refl 0)
    (show (0:ℝ) ∈ Ici 0 by simp) hx.le hx
  dsimp only [ThetaTailRow.normalized] at h
  have hk0 := thetaCuspFullSource_pos_all 0
  have hkx := thetaCuspFullSource_pos_all x
  have hm := (div_lt_div_iff₀ (mul_pos hk0 hkx) (mul_pos hk0 hk0)).mp h
  have hsmall : H 0 x*k 0 < J*k x := by
    apply (mul_lt_mul_iff_right₀ hk0).mp
    nlinarith only [hm]
  have hr : H 0 x/J*(k 0/k x) < 1 := by
    have he : H 0 x/J*(k 0/k x)=(H 0 x*k 0)/(J*k x) := by ring
    rw [he]
    exact (div_lt_one (mul_pos center_pos hkx)).mpr hsmall
  simp only [matchedPacket,transportPrimitive_zero,mul_zero,add_zero]
  dsimp only [normalizedPacket]
  simp only [add_zero]
  exact div_pos (sub_pos.mpr hr) hx

private theorem dampedPacket_zero_pos {x : ℝ} (hx : 0 < x) : 0 < dampedPacket x 0 := by
  apply mul_pos (packetDamping_pos x 0)
  exact mul_pos (mul_pos (thetaCuspFullSource_pos_all 0) (thetaCuspFullSource_pos_all (0+x)))
    (matchedPacket_zero_pos hx)

/-- Positivity of the literal finite-pair packet on the entire nonnegative ray. -/
theorem matchedPacket_pos {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    0 < matchedPacket x t := by
  obtain ⟨z,⟨hz,hf⟩,_⟩ := ThetaSturmCrossing.forcing_has_unique_positive_zero hx
  have hm : StrictMonoOn (dampedPacket x) (Icc 0 z) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro u _; exact (dampedPacket_hasDerivAt hx u).continuousAt.continuousWithinAt
    · intro u hu
      have hu0 : u ∈ Ioo 0 z := by simpa only [interior_Icc] using hu
      rw [(dampedPacket_hasDerivAt hx u).deriv]
      exact div_pos (mul_pos (mul_pos (packetDamping_pos x u)
        (ThetaSturmCrossing.forcing_pos_before_zero hx hu0.1.le hu0.2 hf))
        (prefixBalance_pos hx hu0.1)) (mul_pos hx center_pos)
  have ha : StrictAntiOn (dampedPacket x) (Ici z) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _)
    · intro u _; exact (dampedPacket_hasDerivAt hx u).continuousAt.continuousWithinAt
    · intro u hu
      have hzu : z < u := by simpa only [interior_Ici,mem_Ioi] using hu
      rw [(dampedPacket_hasDerivAt hx u).deriv]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (packetDamping_pos x u)
          (ThetaSturmCrossing.forcing_neg_after hx hz.le hzu hf.le))
        (prefixBalance_pos hx (hz.trans hzu))) (mul_pos hx center_pos)
  have hw : 0 < dampedPacket x t := by
    by_cases htz : t ≤ z
    · exact (dampedPacket_zero_pos hx).trans_le
        (hm.monotoneOn ⟨le_rfl,hz.le⟩ ⟨ht,htz⟩ ht)
    · have hzt : z < t := lt_of_not_ge htz
      have hnonneg : 0 ≤ dampedPacket x (t+1) := by
        apply le_of_tendsto (dampedPacket_limit hx)
        filter_upwards [eventually_ge_atTop (t+1)] with u hu
        exact ha.antitoneOn (show t+1 ∈ Ici z by change z ≤ t+1; linarith)
          (show u ∈ Ici z by change z ≤ u; linarith) hu
      have hstrict := ha hzt.le (show t+1 ∈ Ici z by change z ≤ t+1; linarith)
        (show t < t+1 by linarith)
      exact hnonneg.trans_lt hstrict
  have hw' : 0 < weightedPacket x t :=
    (mul_pos_iff_of_pos_left (packetDamping_pos x t)).mp hw
  exact (mul_pos_iff_of_pos_left
    (mul_pos (thetaCuspFullSource_pos_all t) (thetaCuspFullSource_pos_all (t+x)))).mp hw'

end RHTower.ThetaFiniteTransport
