import GaloisForLFunctions.RHTower.ThetaFinitePairPacketExtension

/-! The actual diagonal bulk current has a continuously differentiable node
extension. Consequently its compact source-time integral can be differentiated
at the singular corner before the endpoint flux is restored. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaFiniteTransport
open GaloisForLFunctions.HTGeometry

local notation "k" => thetaCuspFullSource
local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "c₂" => thetaCuspLogCurvatureJetTwo
local notation "J" => thetaTailFirstMomentKernel 0 0
local notation "I" => ThetaConfluent.derivativeMass

private theorem cont_p : Continuous p := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
private theorem cont_c : Continuous c := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
private theorem cont_v : Continuous v := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvatureJet t).continuousAt
private theorem cont_c₂ : Continuous c₂ := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvatureJetTwo t).continuousAt
private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

def secantSecondNodeJet (x t : ℝ) : ℝ :=
  compactNodeAverage 2 (fun u t => c₂ (t+u)) x t

theorem secantExtension_continuous : Continuous fun z : ℝ × ℝ => smoothSecant z.1 z.2 := by
  change Continuous fun z : ℝ × ℝ => compactNodeAverage 0 (fun u t => c (t+u)) z.1 z.2
  exact compactNodeAverage_continuous 0 (cont_c.comp (continuous_snd.add continuous_fst))

theorem secantNodeExtension_continuous : Continuous fun z : ℝ × ℝ => smoothSecantNodeJet z.1 z.2 := by
  change Continuous fun z : ℝ × ℝ => compactNodeAverage 1 (fun u t => v (t+u)) z.1 z.2
  exact compactNodeAverage_continuous 1 (cont_v.comp (continuous_snd.add continuous_fst))

theorem secantSecondNodeJet_continuous : Continuous fun z : ℝ × ℝ => secantSecondNodeJet z.1 z.2 :=
  compactNodeAverage_continuous 2 (cont_c₂.comp (continuous_snd.add continuous_fst))

theorem secantExtension_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => smoothSecant z t) (smoothSecantNodeJet x t) x := by
  change HasDerivAt (fun z => compactNodeAverage 0 (fun u t => c (t+u)) z t)
    (compactNodeAverage 1 (fun u t => v (t+u)) x t) x
  apply compactNodeAverage_hasDerivAt 0
    (cont_c.comp (continuous_snd.add continuous_fst))
    (cont_v.comp (continuous_snd.add continuous_fst))
  intro z r
  convert! (hasDerivAt_thetaCuspLogCurvature (r+z)).comp z
    ((hasDerivAt_id z).const_add r) using 1
  simp only [mul_one]

theorem secantNodeExtension_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => smoothSecantNodeJet z t) (secantSecondNodeJet x t) x := by
  change HasDerivAt (fun z => compactNodeAverage 1 (fun u t => v (t+u)) z t)
    (compactNodeAverage 2 (fun u t => c₂ (t+u)) x t) x
  apply compactNodeAverage_hasDerivAt 1
    (cont_v.comp (continuous_snd.add continuous_fst))
    (cont_c₂.comp (continuous_snd.add continuous_fst))
  intro z r
  convert! (hasDerivAt_thetaCuspLogCurvatureJet (r+z)).comp z
    ((hasDerivAt_id z).const_add r) using 1
  simp only [mul_one]

theorem secantExtension_zero (t : ℝ) : smoothSecant 0 t=c t := by
  change compactNodeAverage 0 (fun u t => c (t+u)) 0 t=c t
  simp only [compactNodeAverage_zero,add_zero,Nat.cast_zero,zero_add,div_one]
theorem secantNodeExtension_zero (t : ℝ) : smoothSecantNodeJet 0 t=v t/2 := by
  change compactNodeAverage 1 (fun u t => v (t+u)) 0 t=v t/2
  simp only [compactNodeAverage_zero,add_zero,Nat.cast_one]
  norm_num
theorem secantSecondNodeJet_zero (t : ℝ) : secantSecondNodeJet 0 t=c₂ t/3 := by
  simp only [secantSecondNodeJet,compactNodeAverage_zero,add_zero,Nat.cast_ofNat]
  norm_num

def diagonalWeight (x t : ℝ) : ℝ := k (t+x)^2/k x^2
def momentExtension (x t : ℝ) : ℝ :=
  packetExtension x t+smoothSecant x t*primitiveExtension x t
def momentExtensionJet (x t : ℝ) : ℝ :=
  packetExtensionJet x t+smoothSecantNodeJet x t*primitiveExtension x t+
    smoothSecant x t*primitiveExtensionJet x t
def centerMomentVariation (t : ℝ) : ℝ :=
  I/J-(c t+p t^2)/2+t*v t/2+c t*centerPrimitiveVariation t

theorem diagonalWeight_continuous : Continuous fun z : ℝ × ℝ => diagonalWeight z.1 z.2 :=
  ((thetaCuspSchwartzReal.continuous.comp (continuous_snd.add continuous_fst)).pow 2).div
    ((thetaCuspSchwartzReal.continuous.comp continuous_fst).pow 2)
    (fun z => pow_ne_zero 2 (thetaCuspFullSource_pos_all z.1).ne')

theorem diagonalWeight_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => diagonalWeight z t)
      ((-2*p (t+x)+2*p x)*diagonalWeight x t) x := by
  have hk := (actualSource_hasDerivAt (t+x)).comp x ((hasDerivAt_id x).const_add t)
  convert! (hk.pow 2).div ((actualSource_hasDerivAt x).pow 2)
    (pow_ne_zero 2 (thetaCuspFullSource_pos_all x).ne') using 1
  dsimp only [Pi.pow_apply,Function.comp_apply]
  simp only [diagonalWeight,mul_one]
  field_simp [(thetaCuspFullSource_pos_all x).ne']
  ring

theorem momentExtension_continuous : Continuous fun z : ℝ × ℝ => momentExtension z.1 z.2 :=
  packetExtension_continuous.add (secantExtension_continuous.mul primitiveExtension_continuous)
theorem momentExtensionJet_continuous : Continuous fun z : ℝ × ℝ => momentExtensionJet z.1 z.2 :=
  (packetExtensionJet_continuous.add
    (secantNodeExtension_continuous.mul primitiveExtension_continuous)).add
      (secantExtension_continuous.mul primitiveExtensionJet_continuous)

theorem momentExtension_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => momentExtension z t) (momentExtensionJet x t) x := by
  convert! (packetExtension_hasDerivAt x t).add
    ((secantExtension_hasDerivAt x t).mul (primitiveExtension_hasDerivAt x t)) using 1
  unfold momentExtensionJet
  ring

theorem momentExtension_eq {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    momentExtension x t=matchedPacket x t := by
  simp only [momentExtension,matchedPacket,packetExtension_eq hx,
    primitiveExtension_eq hx,smoothSecant_eq hx]

theorem momentExtension_zero (t : ℝ) : momentExtension 0 t=t*c t-p t := by
  simp only [momentExtension,packetExtension_zero,primitiveExtension_zero,secantExtension_zero]
  ring

theorem momentExtensionJet_zero (t : ℝ) : momentExtensionJet 0 t=centerMomentVariation t := by
  simp only [momentExtensionJet,packetExtensionJet_zero,primitiveExtension_zero,
    primitiveExtensionJet_zero,secantExtension_zero,secantNodeExtension_zero,centerMomentVariation]
  ring

def regularizedBulk (x t : ℝ) : ℝ := diagonalWeight x t*
  (smoothSecantNodeJet x t*primitiveExtension x t-(p (t+x)-p x)*momentExtension x t)
def regularizedBulkJet (x t : ℝ) : ℝ :=
  (-2*p (t+x)+2*p x)*regularizedBulk x t+diagonalWeight x t*
    (secantSecondNodeJet x t*primitiveExtension x t+
      smoothSecantNodeJet x t*primitiveExtensionJet x t-
      (c (t+x)-c x)*momentExtension x t-(p (t+x)-p x)*momentExtensionJet x t)
def centerBulkVariation (t : ℝ) : ℝ := diagonalWeight 0 t*
  (t*c₂ t/3+v t*centerPrimitiveVariation t/2-(c t-c 0)*(t*c t-p t)-
    p t*centerMomentVariation t-2*p t*(t*v t/2-p t*(t*c t-p t)))

theorem regularizedBulk_continuous : Continuous fun z : ℝ × ℝ => regularizedBulk z.1 z.2 :=
  diagonalWeight_continuous.mul
    ((secantNodeExtension_continuous.mul primitiveExtension_continuous).sub
      (((cont_p.comp (continuous_snd.add continuous_fst)).sub (cont_p.comp continuous_fst)).mul
        momentExtension_continuous))

theorem regularizedBulkJet_continuous : Continuous fun z : ℝ × ℝ => regularizedBulkJet z.1 z.2 := by
  have hp := cont_p.comp (continuous_snd.add continuous_fst : Continuous fun z : ℝ × ℝ => z.2+z.1)
  have hc := cont_c.comp (continuous_snd.add continuous_fst : Continuous fun z : ℝ × ℝ => z.2+z.1)
  exact ((((hp.const_mul (-2)).add ((cont_p.comp continuous_fst).const_mul 2)).mul
    regularizedBulk_continuous).add
    (diagonalWeight_continuous.mul ((((secantSecondNodeJet_continuous.mul primitiveExtension_continuous).add
      (secantNodeExtension_continuous.mul primitiveExtensionJet_continuous)).sub
        ((hc.sub (cont_c.comp continuous_fst)).mul momentExtension_continuous)).sub
          ((hp.sub (cont_p.comp continuous_fst)).mul momentExtensionJet_continuous))))

theorem regularizedBulk_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun z => regularizedBulk z t) (regularizedBulkJet x t) x := by
  have hp := ((hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp x
    ((hasDerivAt_id x).const_add t)).sub (hasDerivAt_thetaCuspLogDecaySlope x)
  convert! (diagonalWeight_hasDerivAt x t).mul
    (((secantNodeExtension_hasDerivAt x t).mul (primitiveExtension_hasDerivAt x t)).sub
      (hp.mul (momentExtension_hasDerivAt x t))) using 1
  dsimp only [Pi.mul_apply,Pi.sub_apply,Function.comp_apply]
  simp only [regularizedBulkJet,regularizedBulk,mul_one]
  ring

theorem regularizedBulk_zero (t : ℝ) :
    regularizedBulk 0 t=diagonalWeight 0 t*(t*v t/2-p t*(t*c t-p t)) := by
  simp only [regularizedBulk,secantNodeExtension_zero,primitiveExtension_zero,
    momentExtension_zero,add_zero,p_zero,sub_zero]
  ring

theorem regularizedBulkJet_zero (t : ℝ) : regularizedBulkJet 0 t=centerBulkVariation t := by
  simp only [regularizedBulkJet,regularizedBulk_zero,secantSecondNodeJet_zero,
    secantNodeExtension_zero,primitiveExtension_zero,primitiveExtensionJet_zero,
    momentExtension_zero,momentExtensionJet_zero,add_zero,p_zero,mul_zero,add_zero,sub_zero,
    centerBulkVariation]
  ring

/-- Compact bulk differentiation is justified by actual joint source regularity. -/
theorem integral_regularizedBulk_hasDerivAt_zero (T : ℝ) :
    HasDerivAt (fun x => ∫ t in (0:ℝ)..T, regularizedBulk x t)
      (∫ t in (0:ℝ)..T, centerBulkVariation t) 0 := by
  convert! hasDerivAt_parametric_intervalIntegral regularizedBulk_continuous
    regularizedBulkJet_continuous regularizedBulk_hasDerivAt 0 T 0 using 1
  simp only [regularizedBulkJet_zero]

end RHTower.ThetaFiniteTransport
