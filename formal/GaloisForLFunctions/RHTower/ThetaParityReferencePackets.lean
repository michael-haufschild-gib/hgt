import GaloisForLFunctions.RHTower.ThetaParityReferenceFourier

/-!
# Source packets for the theta parity reference operator

The Fourier-limit primitive has an exact source integral formula. On negative
source supports this is pi/2 times the Volterra pairing. Three-interval input
packets have zero mass; their middle-interval readouts form a scalar diagonal
matrix in the limit, for every finite selection of packet indices.

The packets are literal vectors of unweighted source L2. Their elementary norm
bounds and the exact matrix limit supply the subsequent approximation-number
lower bound. No spectral-divergence or residue-sign claim is made in this file.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace
namespace RHTower
open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt
noncomputable section
local notation "H" => Lp ℂ 2 unitIntervalMeasure

private theorem ae_cdfFun_of_ae {β : Type*} {u v : ℝ → β}
    (h : u =ᵐ[unitIntervalMeasure] v) :
    (fun x => u (thetaSource.cdfFun x)) =ᵐ[volume] fun x => v (thetaSource.cdfFun x) := by
  have h' : u =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v := by
    simpa only [unitIntervalMeasure_eq] using h
  exact thetaSource.law_ae_eq.1 (thetaSource.measurePreserving_cdfFun.quasiMeasurePreserving.ae h')

theorem flatField_unitReflection (f : H) :
    flatField (unitReflection f) =ᵐ[volume] fun x => flatField f (-x) := by
  filter_upwards [ae_cdfFun_of_ae (unitReflection_ae f)] with x hx
  have he : thetaSource.normalized (-x) = thetaSource.normalized x := by
    change thetaSource.k (-x) / thetaSource.mass = thetaSource.k x / thetaSource.mass
    rw [thetaSource_even]
  rw [flatField, hx, flatField, he,
    HedenmalmIntervalAnomaly.cdfFun_neg thetaSource thetaSource_even]

theorem flatField_sub (f g : H) :
    flatField (f - g) =ᵐ[volume] fun x => flatField f x - flatField g x := by
  filter_upwards [ae_cdfFun_of_ae (Lp.coeFn_sub f g)] with x hx
  simp only [flatField, hx, Pi.sub_apply]
  ring

private theorem inner_pinnedVolterraCLM_flat (f g : H) (hf : pinnedMean f = 0) :
    inner ℂ g (pinnedVolterraCLM f) =
      ∫ x, (starRingEnd ℂ) (flatField g x) * flatPrimitive f x := by
  rw [inner_lp_eq]
  have hae : (fun t => (starRingEnd ℂ) (g t) * (pinnedVolterraCLM f : H) t)
      =ᵐ[unitIntervalMeasure] fun t => (starRingEnd ℂ) (g t) * pinnedPrefix f t := by
    filter_upwards [pinnedVolterra_coeFn f] with t h1
    change _ * (pinnedVolterra f) t = _
    rw [h1, pinnedVolterraFun, hf, mul_zero, sub_zero]
  have hm : AEStronglyMeasurable (fun t => (starRingEnd ℂ) (g t) * pinnedPrefix f t) unitIntervalMeasure :=
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable g)).mul
      (aestronglyMeasurable_pinnedPrefix f)
  rw [integral_congr_ae hae, integral_unitInterval_eq_cdf hm]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [pinnedPrefix_cdfFun, flatField, map_mul, Complex.conj_ofReal, Complex.real_smul]
  ring

theorem inner_parityPrimitive_flat (f g : H) :
    inner ℂ g (parityPrimitive f) = ((Real.pi / 2 : ℝ) : ℂ) *
      ∫ x, (starRingEnd ℂ) (flatField g x) *
        ∫ y in Iic x, (flatField f y - flatField f (-y)) := by
  have hm : pinnedMean (f - unitReflection f) = 0 := by
    rw [← inner_constMode_eq_pinnedMean, inner_sub_right, inner_constMode_unitReflection, sub_self]
  rw [parityPrimitive, smul_apply, ContinuousLinearMap.comp_apply, sub_apply,
    one_apply_eq_self, inner_smul_right, inner_pinnedVolterraCLM_flat _ _ hm]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  unfold flatPrimitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (flatField_sub f (unitReflection f)),
    ae_restrict_of_ae (flatField_unitReflection f)] with y h1 h2
  rw [h1, h2]

theorem inner_parityPrimitive_preFlat {u v : ℝ → ℂ} (hu : IsFlatTest u) (hv : IsFlatTest v) :
    inner ℂ (preFlat hv) (parityPrimitive (preFlat hu)) = ((Real.pi / 2 : ℝ) : ℂ) *
      ∫ x, (starRingEnd ℂ) (v x) * ∫ y in Iic x, (u y - u (-y)) := by
  rw [inner_parityPrimitive_flat]
  have hu' := flatField_preFlat hu
  have hur : ∀ᵐ y ∂volume, flatField (preFlat hu) (-y) = u (-y) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hu'
  have he : ∀ x, (∫ y in Iic x, (flatField (preFlat hu) y - flatField (preFlat hu) (-y))) =
      ∫ y in Iic x, (u y - u (-y)) := by
    intro x
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hu', ae_restrict_of_ae hur] with y h1 h2
    rw [h1, h2]
  congr 1
  apply integral_congr_ae
  filter_upwards [flatField_preFlat hv] with x hx
  rw [hx, he]

theorem tendsto_thetaParityReference_preFlat {u v : ℝ → ℂ}
    (hu : IsFlatTest u) (hv : IsFlatTest v) :
    Tendsto (fun N => inner ℂ (flatLp (preFlat hv))
      (thetaParityReferenceOperator (N + 1) (flatLp (preFlat hu)))) atTop
      (𝓝 (((Real.pi / 2 : ℝ) : ℂ) *
        ∫ x, (starRingEnd ℂ) (v x) * ∫ y in Iic x, (u y - u (-y)))) := by
  simpa only [inner_parityPrimitive_preFlat hu hv] using
    tendsto_inner_flatLp_thetaParityReferenceOperator (preFlat hu) (preFlat hv)

/-- On negative source supports the directed reference limit is the literal Volterra form. -/
theorem tendsto_thetaParityReference_negativeTest {u v : ℝ → ℂ}
    (hu : IsFlatTest u) (hv : IsFlatTest v)
    (hu0 : ∀ x, 0 ≤ x → u x = 0) (hv0 : ∀ x, 0 ≤ x → v x = 0) :
    Tendsto (fun N => inner ℂ (flatLp (preFlat hv))
      (thetaParityReferenceOperator (N + 1) (flatLp (preFlat hu)))) atTop
      (𝓝 (((Real.pi / 2 : ℝ) : ℂ) *
        ∫ x, (starRingEnd ℂ) (v x) * ∫ y in Iic x, u y)) := by
  have he : (∫ x, (starRingEnd ℂ) (v x) * ∫ y in Iic x, (u y - u (-y))) =
      ∫ x, (starRingEnd ℂ) (v x) * ∫ y in Iic x, u y := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · rw [hv0 x hx, map_zero, zero_mul, zero_mul]
    · congr 1
      apply setIntegral_congr_fun measurableSet_Iic
      intro y hy
      dsimp only
      rw [hu0 (-y) (by have : y ≤ x := hy; linarith), sub_zero]
  simpa only [he] using tendsto_thetaParityReference_preFlat hu hv

/-- Unnormalized source interval packet. -/
def parityInterval (a b : ℝ) : ℝ → ℂ := (Ico a b).indicator (fun _ => 1)

theorem isFlatTest_parityInterval (a b : ℝ) : IsFlatTest (parityInterval a b) where
  measurable := measurable_const.indicator measurableSet_Ico
  bounded := ⟨1, fun x => by
    exact (norm_indicator_le_norm_self _ _).trans_eq (norm_one)⟩
  compact := ⟨|a| + |b|, fun x hx => by
    apply indicator_of_notMem
    intro h
    have habs : |x| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor
      · have ha := neg_abs_le a; have hb := abs_nonneg b
        have hax : a ≤ x := h.1
        linarith
      · have hb := le_abs_self b; have ha := abs_nonneg a
        have hxb : x < b := h.2
        linarith
    exact (not_le_of_gt hx) habs⟩

theorem integrable_parityInterval (a b : ℝ) : Integrable (parityInterval a b) :=
  (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (measure_Ico_lt_top.ne) (by simp))

theorem integral_parityInterval (a b : ℝ) :
    (∫ x, parityInterval a b x) = ((max (b - a) 0 : ℝ) : ℂ) := by
  rw [parityInterval, integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico,
    Complex.real_smul, mul_one]

theorem setIntegral_parityInterval (a b x : ℝ) :
    (∫ y in Iic x, parityInterval a b y) = ((max (min b x - a) 0 : ℝ) : ℂ) := by
  rw [parityInterval, integral_indicator_const _ measurableSet_Ico,
    measureReal_restrict_apply measurableSet_Ico]
  have he : (volume : Measure ℝ).real (Ico a b ∩ Iic x) = max (min b x - a) 0 := by
    have hset : (Ico a b ∩ Iic x : Set ℝ) =ᵐ[(volume : Measure ℝ)] (Ioc a b ∩ Iic x : Set ℝ) :=
      Ico_ae_eq_Ioc.inter Filter.EventuallyEq.rfl
    rw [measureReal_congr hset, Ioc_inter_Iic, Real.volume_real_Ioc]
  rw [he, Complex.real_smul, mul_one]

private theorem isFlatTest_sub {u v : ℝ → ℂ} (hu : IsFlatTest u) (hv : IsFlatTest v) :
    IsFlatTest (fun x => u x - v x) where
  measurable := hu.measurable.sub hv.measurable
  bounded := by
    obtain ⟨C, hC⟩ := hu.bounded
    obtain ⟨D, hD⟩ := hv.bounded
    exact ⟨C + D, fun x => (norm_sub_le _ _).trans (add_le_add (hC x) (hD x))⟩
  compact := by
    obtain ⟨C, hC⟩ := hu.compact
    obtain ⟨D, hD⟩ := hv.compact
    refine ⟨max C D, fun x hx => ?_⟩
    rw [hC x ((le_max_left _ _).trans_lt hx), hD x ((le_max_right _ _).trans_lt hx), sub_self]

def parityPacketInput (a l : ℝ) (x : ℝ) : ℂ :=
  parityInterval a (a + l) x - parityInterval (a + 2 * l) (a + 3 * l) x

theorem isFlatTest_parityPacketInput (a l : ℝ) : IsFlatTest (parityPacketInput a l) :=
  isFlatTest_sub (isFlatTest_parityInterval _ _) (isFlatTest_parityInterval _ _)

theorem integrable_parityPacketInput (a l : ℝ) : Integrable (parityPacketInput a l) :=
  (integrable_parityInterval _ _).sub (integrable_parityInterval _ _)

theorem integral_parityPacketInput (a l : ℝ) : ∫ x, parityPacketInput a l x = 0 := by
  simp only [parityPacketInput]
  rw [integral_sub (integrable_parityInterval _ _) (integrable_parityInterval _ _),
    integral_parityInterval, integral_parityInterval]
  rw [show a + l - a = l by ring, show a + 3 * l - (a + 2 * l) = l by ring, sub_self]

private theorem packetPrefix (a l x : ℝ) :
    (∫ y in Iic x, parityPacketInput a l y) =
      ((max (min (a + l) x - a) 0 - max (min (a + 3 * l) x - (a + 2 * l)) 0 : ℝ) : ℂ) := by
  simp only [parityPacketInput]
  rw [integral_sub (integrable_parityInterval _ _).integrableOn (integrable_parityInterval _ _).integrableOn,
    setIntegral_parityInterval, setIntegral_parityInterval, Complex.ofReal_sub]

theorem packetPrefix_middle {a l x : ℝ} (hl : 0 < l) (hx : x ∈ Ico (a + l) (a + 2 * l)) :
    (∫ y in Iic x, parityPacketInput a l y) = (l : ℂ) := by
  rw [packetPrefix, min_eq_left hx.1, min_eq_right (by linarith [hx.2]),
    max_eq_left (by linarith), max_eq_right (by linarith [hx.2])]
  congr 1
  ring

theorem packetPrefix_before {a l x : ℝ} (hl : 0 < l) (hx : x ≤ a) :
    (∫ y in Iic x, parityPacketInput a l y) = 0 := by
  rw [packetPrefix, min_eq_right (by linarith), min_eq_right (by linarith),
    max_eq_right (by linarith), max_eq_right (by linarith)]
  simp

theorem packetPrefix_after {a l x : ℝ} (hl : 0 < l) (hx : a + 3 * l ≤ x) :
    (∫ y in Iic x, parityPacketInput a l y) = 0 := by
  rw [packetPrefix, min_eq_left (by linarith), min_eq_left hx,
    max_eq_left (by linarith), max_eq_left (by linarith)]
  rw [show a + l - a - (a + 3 * l - (a + 2 * l)) = 0 by ring, Complex.ofReal_zero]

theorem parityPacket_diagonal {a l : ℝ} (hl : 0 < l) :
    (∫ x, (starRingEnd ℂ) (parityInterval (a + l) (a + 2 * l) x) *
      ∫ y in Iic x, parityPacketInput a l y) = ((l ^ 2 : ℝ) : ℂ) := by
  have he : (fun x => (starRingEnd ℂ) (parityInterval (a + l) (a + 2 * l) x) *
      ∫ y in Iic x, parityPacketInput a l y) =
      (Ico (a + l) (a + 2 * l)).indicator (fun _ => (l : ℂ)) := by
    funext x
    by_cases hx : x ∈ Ico (a + l) (a + 2 * l)
    · rw [parityInterval, indicator_of_mem hx, indicator_of_mem hx, map_one, one_mul,
        packetPrefix_middle hl hx]
    · rw [parityInterval, indicator_of_notMem hx, indicator_of_notMem hx, map_zero, zero_mul]
  rw [he, integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico,
    max_eq_left (by linarith), Complex.real_smul]
  push_cast
  ring

theorem parityPacket_offDiagonal {a b l : ℝ} (hl : 0 < l)
    (hsep : b + 3 * l ≤ a ∨ a + 3 * l ≤ b) :
    (∫ x, (starRingEnd ℂ) (parityInterval (b + l) (b + 2 * l) x) *
      ∫ y in Iic x, parityPacketInput a l y) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hx : x ∈ Ico (b + l) (b + 2 * l)
  · have hp : (∫ y in Iic x, parityPacketInput a l y) = 0 := by
      rcases hsep with h | h
      · exact packetPrefix_before hl (by linarith [hx.2])
      · exact packetPrefix_after hl (by linarith [hx.1])
    rw [hp, mul_zero]
    rfl
  · rw [parityInterval, indicator_of_notMem hx, map_zero, zero_mul]
    rfl

def parityPacketStart (l : ℝ) (i : ℕ) : ℝ := -3 * (i + 1) * l

def thetaParityInputPacket (l : ℝ) (i : ℕ) : ThetaParitySourceL2 :=
  flatLp (preFlat (isFlatTest_parityPacketInput (parityPacketStart l i) l))

def thetaParityOutputPacket (l : ℝ) (i : ℕ) : ThetaParitySourceL2 :=
  flatLp (preFlat (isFlatTest_parityInterval (parityPacketStart l i + l) (parityPacketStart l i + 2 * l)))

private theorem parityInterval_nonnegative {a b : ℝ} (hb : b ≤ 0) (x : ℝ) (hx : 0 ≤ x) :
    parityInterval a b x = 0 := by
  apply indicator_of_notMem
  intro h
  have : x < b := h.2
  linarith

private theorem parityPacketStart_end {l : ℝ} (hl : 0 < l) (i : ℕ) :
    parityPacketStart l i + 3 * l ≤ 0 := by
  unfold parityPacketStart
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith [mul_nonneg hi hl.le]

/-- Every finite source packet matrix converges to a nonzero scalar diagonal. -/
theorem tendsto_thetaParityPacket_matrix {l : ℝ} (hl : 0 < l) (i j : ℕ) :
    Tendsto (fun N => inner ℂ (thetaParityOutputPacket l j)
      (thetaParityReferenceOperator (N + 1) (thetaParityInputPacket l i))) atTop
      (𝓝 (if i = j then ((Real.pi / 2 * l ^ 2 : ℝ) : ℂ) else 0)) := by
  have hi := parityPacketStart_end hl i
  have hj := parityPacketStart_end hl j
  have hu0 : ∀ x, 0 ≤ x → parityPacketInput (parityPacketStart l i) l x = 0 := by
    intro x hx
    rw [parityPacketInput, parityInterval_nonnegative (by linarith) x hx,
      parityInterval_nonnegative hi x hx, sub_self]
  have hv0 : ∀ x, 0 ≤ x →
      parityInterval (parityPacketStart l j + l) (parityPacketStart l j + 2 * l) x = 0 :=
    parityInterval_nonnegative (by linarith)
  have ht := tendsto_thetaParityReference_negativeTest
    (isFlatTest_parityPacketInput (parityPacketStart l i) l)
    (isFlatTest_parityInterval (parityPacketStart l j + l) (parityPacketStart l j + 2 * l)) hu0 hv0
  by_cases hij : i = j
  · subst j
    simpa only [thetaParityInputPacket, thetaParityOutputPacket, parityPacket_diagonal hl,
      ite_true, Complex.ofReal_mul] using ht
  · have hsep : parityPacketStart l j + 3 * l ≤ parityPacketStart l i ∨
        parityPacketStart l i + 3 * l ≤ parityPacketStart l j := by
      rcases lt_or_gt_of_ne hij with h | h
      · left
        have hh : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        unfold parityPacketStart
        nlinarith [mul_nonneg (sub_nonneg.mpr hh) hl.le]
      · right
        have hh : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        unfold parityPacketStart
        nlinarith [mul_nonneg (sub_nonneg.mpr hh) hl.le]
    simpa only [thetaParityInputPacket, thetaParityOutputPacket, parityPacket_offDiagonal hl hsep,
      if_neg hij, mul_zero] using ht

theorem flatLp_preFlat_parityInterval (a b : ℝ) :
    flatLp (preFlat (isFlatTest_parityInterval a b)) =
      indicatorConstLp 2 (measurableSet_Ico (a := a) (b := b)) measure_Ico_lt_top.ne (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [flatLp_ae (preFlat (isFlatTest_parityInterval a b)),
    flatField_preFlat (isFlatTest_parityInterval a b),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ico (a := a) (b := b))
      (hμs := measure_Ico_lt_top.ne) (c := (1 : ℂ))] with x h1 h2 h3
  rw [h1, h2, h3]
  rfl

theorem norm_flatLp_preFlat_parityInterval (a b : ℝ) :
    ‖flatLp (preFlat (isFlatTest_parityInterval a b))‖ = Real.sqrt (max (b - a) 0) := by
  rw [flatLp_preFlat_parityInterval, norm_indicatorConstLp (by norm_num) (by norm_num),
    norm_one, one_mul, Real.volume_real_Ico, Real.sqrt_eq_rpow]
  norm_num

theorem flatLp_preFlat_parityPacketInput (a l : ℝ) :
    flatLp (preFlat (isFlatTest_parityPacketInput a l)) =
      flatLp (preFlat (isFlatTest_parityInterval a (a + l))) -
        flatLp (preFlat (isFlatTest_parityInterval (a + 2 * l) (a + 3 * l))) := by
  apply Lp.ext
  filter_upwards [flatLp_ae (preFlat (isFlatTest_parityPacketInput a l)),
    flatField_preFlat (isFlatTest_parityPacketInput a l),
    Lp.coeFn_sub (flatLp (preFlat (isFlatTest_parityInterval a (a + l))))
      (flatLp (preFlat (isFlatTest_parityInterval (a + 2 * l) (a + 3 * l)))),
    flatLp_ae (preFlat (isFlatTest_parityInterval a (a + l))),
    flatLp_ae (preFlat (isFlatTest_parityInterval (a + 2 * l) (a + 3 * l))),
    flatField_preFlat (isFlatTest_parityInterval a (a + l)),
    flatField_preFlat (isFlatTest_parityInterval (a + 2 * l) (a + 3 * l))]
    with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, h2, h3, Pi.sub_apply, h4, h5, h6, h7]
  rfl

theorem norm_thetaParityInputPacket_le {l : ℝ} (hl : 0 < l) (i : ℕ) :
    ‖thetaParityInputPacket l i‖ ≤ 2 * Real.sqrt l := by
  rw [thetaParityInputPacket, flatLp_preFlat_parityPacketInput]
  refine (norm_sub_le _ _).trans_eq ?_
  rw [norm_flatLp_preFlat_parityInterval, norm_flatLp_preFlat_parityInterval,
    show parityPacketStart l i + l - parityPacketStart l i = l by ring,
    show parityPacketStart l i + 3 * l - (parityPacketStart l i + 2 * l) = l by ring,
    max_eq_left hl.le]
  ring

theorem norm_thetaParityOutputPacket {l : ℝ} (hl : 0 < l) (i : ℕ) :
    ‖thetaParityOutputPacket l i‖ = Real.sqrt l := by
  rw [thetaParityOutputPacket, norm_flatLp_preFlat_parityInterval,
    show parityPacketStart l i + 2 * l - (parityPacketStart l i + l) = l by ring,
    max_eq_left hl.le]

end
end RHTower
