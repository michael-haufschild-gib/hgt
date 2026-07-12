import GaloisForLFunctions.RHTower.CCMShiftedXiNormalConvergence
import GaloisForLFunctions.RHTower.CCMShiftedXiPoleJet

/-!
# Global multiplicity order of the Xi-cancelled rectangular carrier

Local normal convergence transports a common finite vanishing-order floor
through an infinite sum.  Applied to the off-support Xi fibers, this proves
that the full cancelled carrier has order exactly one less than the analytic
multiplicity at every right shifted Xi pole.
-/

open Complex Filter Function Metric Set

namespace RHTower

noncomputable section

/-- An injective subfamily of a locally normally summable family remains
locally normally summable. -/
theorem SummableLocallyUniformlyOn.comp_injective_local
    {alpha beta iota kappa : Type*} [AddCommGroup alpha] [UniformSpace alpha]
    [IsUniformAddGroup alpha] [CompleteSpace alpha]
    [TopologicalSpace beta] [LocallyCompactSpace beta]
    {f : iota → beta → alpha} {U : Set beta}
    (hU : IsOpen U) (h : SummableLocallyUniformlyOn f U)
    {e : kappa → iota} (he : Injective e) :
    SummableLocallyUniformlyOn (fun k => f (e k)) U := by
  apply summableLocallyUniformlyOn_of_of_forall_exists_nhds
  intro x hx
  obtain ⟨K, ⟨hKnhds, hKcompact⟩, hKU⟩ :=
    (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  refine ⟨K, nhdsWithin_le_nhds hKnhds, ?_⟩
  have hcanon := h.hasSumLocallyUniformlyOn
  have hloc : TendstoUniformlyOn
      (fun t : Finset iota => fun y => ∑ i ∈ t, f i y)
      (fun y => ∑' i, f i y) atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hcanon
      K hKU hKcompact
  have huni : HasSumUniformlyOn f (fun y => ∑' i, f i y) K :=
    hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr hloc
  change Summable (UniformOnFun.ofFun {K} ∘ fun k => f (e k))
  exact huni.summableUniformlyOn.comp_injective he

/-- A locally normal sum of analytic functions preserves every common finite
vanishing-order floor. -/
theorem natCast_le_analyticOrderAt_tsum_of_summableLocallyUniformlyOn
    {iota : Type*} {f : iota → ℂ → ℂ} {U : Set ℂ} {z0 : ℂ} {n : ℕ}
    (hU : IsOpen U) (hz0 : z0 ∈ U)
    (hsum : SummableLocallyUniformlyOn f U)
    (hfa : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hord : ∀ i, (n : ℕ∞) ≤ analyticOrderAt (f i) z0) :
    (n : ℕ∞) ≤ analyticOrderAt (fun z => ∑' i, f i z) z0 := by
  classical
  let F : Finset iota → ℂ → ℂ := fun t z => ∑ i ∈ t, f i z
  let S : ℂ → ℂ := fun z => ∑' i, f i z
  have hSdiff : DifferentiableOn ℂ S U :=
    hsum.differentiableOn hU fun i z hz => (hfa i z hz).differentiableAt
  have hSan : AnalyticAt ℂ S z0 :=
    (hSdiff.analyticOnNhd hU) z0 hz0
  rw [show (fun z => ∑' i, f i z) = S from rfl]
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hSan]
  intro k hk
  have hconv0 : TendstoLocallyUniformlyOn F S atTop U := by
    exact hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      hsum.hasSumLocallyUniformlyOn
  have hconv : ∀ j : ℕ,
      TendstoLocallyUniformlyOn
        (fun t : Finset iota => (deriv^[j]) (F t))
        ((deriv^[j]) S) atTop U := by
    intro j
    induction j with
    | zero => simpa using hconv0
    | succ j ih =>
        have hdiff : ∀ᶠ t : Finset iota in atTop,
            DifferentiableOn ℂ ((deriv^[j]) (F t)) U := by
          filter_upwards with t
          intro z hz
          have hFan : AnalyticAt ℂ (F t) z := by
            dsimp only [F]
            exact Finset.analyticAt_fun_sum t fun i _ => hfa i z hz
          exact (hFan.iterated_deriv j).differentiableAt.differentiableWithinAt
        simpa only [Function.iterate_succ_apply'] using ih.deriv hdiff hU
  have hpoint := (hconv k).tendsto_at hz0
  have hpartial : ∀ t : Finset iota, (deriv^[k]) (F t) z0 = 0 := by
    intro t
    rw [← iteratedDeriv_eq_iterate]
    change iteratedDeriv k (fun z => ∑ i ∈ t, f i z) z0 = 0
    rw [iteratedDeriv_fun_sum
      (fun i hi => (hfa i z0 hz0).contDiffAt)]
    apply Finset.sum_eq_zero
    intro i hi
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (hfa i z0 hz0)).mp (hord i) k hk
  have hzero : Tendsto
      (fun t : Finset iota => (deriv^[k]) (F t) z0)
      atTop (nhds 0) := by
    simpa only [hpartial] using
      (tendsto_const_nhds : Tendsto
        (fun _ : Finset iota => (0 : ℂ)) atTop (nhds 0))
  have hpoint' : Tendsto
      (fun t : Finset iota => (deriv^[k]) (F t) z0)
      atTop (nhds (iteratedDeriv k S z0)) := by
    simpa only [iteratedDeriv_eq_iterate] using hpoint
  exact tendsto_nhds_unique hpoint' hzero

/-- Right-half multiplicity copies over supports different from that of `q`. -/
abbrev XiRightOtherSupport (q : XiRightZeroCopy) :=
  {r : XiRightZeroCopy // r.1.1 ≠ q.1.1}

/-- The finite equal-support part of the cancelled carrier. -/
def xiRectangularSameSupportSeries
    (L : ℝ) (q : XiRightZeroCopy) (s : ℂ) : ℂ :=
  ∑' r : XiRightSupportFiber q, xiRectangularCancelledTerm L r.1 s

/-- The infinite off-support part of the cancelled carrier. -/
def xiRectangularOtherSupportSeries
    (L : ℝ) (q : XiRightZeroCopy) (s : ℂ) : ℂ :=
  ∑' r : XiRightOtherSupport q, xiRectangularCancelledTerm L r.1 s

/-- A positive rectangular window does not change the local order of its
cancelled shifted-zeta term. -/
theorem xiRectangularCancelledTerm_order
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    analyticOrderAt (xiRectangularCancelledTerm L q) (xiRightShiftedPole q) =
      (xiRightMultiplicity q - 1 : ℕ) := by
  have hc : AnalyticAt ℂ (fun _ : ℂ => xiRectangularRightCoefficient L q)
      (xiRightShiftedPole q) := analyticAt_const
  have ht : AnalyticAt ℂ (xiShiftedZetaCancelledTerm q)
      (xiRightShiftedPole q) :=
    differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt _
  rw [show xiRectangularCancelledTerm L q =
      (fun _ : ℂ => xiRectangularRightCoefficient L q) *
        xiShiftedZetaCancelledTerm q by rfl,
    analyticOrderAt_mul hc ht,
    hc.analyticOrderAt_eq_zero.mpr
      (xiRectangularRightCoefficient_ne_zero hL q),
    xiShiftedZetaCancelledTerm_order, zero_add]

/-- The exact finite support fiber is its cardinality times any one of its
identical terms. -/
theorem xiRectangularSameSupportSeries_eq_card_mul
    (L : ℝ) (q : XiRightZeroCopy) :
    xiRectangularSameSupportSeries L q =
      fun s => (Fintype.card (XiRightSupportFiber q) : ℂ) *
        xiRectangularCancelledTerm L q s := by
  funext s
  rw [xiRectangularSameSupportSeries, tsum_fintype]
  calc
    ∑ r : XiRightSupportFiber q, xiRectangularCancelledTerm L r.1 s =
        ∑ _r : XiRightSupportFiber q, xiRectangularCancelledTerm L q s := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [xiRectangularCancelledTerm,
        xiRectangularRightCoefficient_eq_of_support_eq L r.2,
        xiShiftedZetaCancelledTerm_eq_of_support_eq r.2]
      rfl
    _ = (Fintype.card (XiRightSupportFiber q) : ℂ) *
        xiRectangularCancelledTerm L q s := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The equal-support fiber has the exact exceptional order `m-1`. -/
theorem xiRectangularSameSupportSeries_order
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    analyticOrderAt (xiRectangularSameSupportSeries L q)
        (xiRightShiftedPole q) =
      (xiRightMultiplicity q - 1 : ℕ) := by
  rw [xiRectangularSameSupportSeries_eq_card_mul]
  letI : Nonempty (XiRightSupportFiber q) := ⟨⟨q, rfl⟩⟩
  have hcard : (Fintype.card (XiRightSupportFiber q) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc : AnalyticAt ℂ
      (fun _ : ℂ => (Fintype.card (XiRightSupportFiber q) : ℂ))
      (xiRightShiftedPole q) := analyticAt_const
  have ht : AnalyticAt ℂ (xiRectangularCancelledTerm L q)
      (xiRightShiftedPole q) :=
    analyticAt_const.mul
      (differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt _)
  rw [show (fun s => (Fintype.card (XiRightSupportFiber q) : ℂ) *
      xiRectangularCancelledTerm L q s) =
      (fun _ : ℂ => (Fintype.card (XiRightSupportFiber q) : ℂ)) *
        xiRectangularCancelledTerm L q by rfl,
    analyticOrderAt_mul hc ht,
    hc.analyticOrderAt_eq_zero.mpr hcard,
    xiRectangularCancelledTerm_order hL q, zero_add]

/-- Every off-support term is divisible by the full multiplicity, and local
normal convergence preserves this order floor through their infinite sum. -/
theorem xiRectangularOtherSupportSeries_order_ge
    (L : ℝ) (q : XiRightZeroCopy) :
    (xiRightMultiplicity q : ℕ∞) ≤
      analyticOrderAt (xiRectangularOtherSupportSeries L q)
        (xiRightShiftedPole q) := by
  let U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := by
    change 1 < (xiRightShiftedPole q).re
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hnormal : SummableLocallyUniformlyOn
      (fun r : XiRightOtherSupport q =>
        xiRectangularCancelledTerm L r.1) U :=
    SummableLocallyUniformlyOn.comp_injective_local hU
      (summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne (L := L))
      Subtype.val_injective
  apply natCast_le_analyticOrderAt_tsum_of_summableLocallyUniformlyOn
    hU hpoleU hnormal
  · intro r s hs
    exact analyticAt_const.mul
      (differentiable_xiShiftedZetaCancelledTerm r.1 |>.analyticAt s)
  · intro r
    have hterm : AnalyticAt ℂ (xiRectangularCancelledTerm L r.1)
        (xiRightShiftedPole q) := analyticAt_const.mul
      (differentiable_xiShiftedZetaCancelledTerm r.1 |>.analyticAt _)
    rw [natCast_le_analyticOrderAt hterm]
    obtain ⟨u, hu, hev⟩ :=
      exists_xiShiftedZetaCancelledTerm_off_support_factorization
        q r.1 r.2.symm
    refine ⟨fun s => xiRectangularRightCoefficient L r.1 * u s,
      analyticAt_const.mul hu, ?_⟩
    filter_upwards [hev] with s hs
    rw [xiRectangularCancelledTerm, hs]
    simp only [smul_eq_mul]
    ring

/-- Near a chosen right Xi pole, the complete cancelled carrier splits into
its exact finite multiplicity fiber and the off-support tail. -/
theorem xiRectangularCancelledSeries_eventuallyEq_same_add_other
    (L : ℝ) (q : XiRightZeroCopy) :
    xiRectangularCancelledSeries L =ᶠ[nhds (xiRightShiftedPole q)]
      xiRectangularSameSupportSeries L q +
        xiRectangularOtherSupportSeries L q := by
  let U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := by
    change 1 < (xiRightShiftedPole q).re
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  filter_upwards [hU.mem_nhds hpoleU] with s hs
  have hsum : Summable (fun r : XiRightZeroCopy =>
      xiRectangularCancelledTerm L r s) :=
    (summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne
      (L := L)).summable hs
  let P : Set XiRightZeroCopy := {r | r.1.1 = q.1.1}
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl P
  change (∑' r : XiRightZeroCopy, xiRectangularCancelledTerm L r s) =
    (∑' r : XiRightSupportFiber q, xiRectangularCancelledTerm L r.1 s) +
      ∑' r : XiRightOtherSupport q, xiRectangularCancelledTerm L r.1 s
  simpa only [P, Set.mem_setOf_eq, Set.mem_compl_iff] using hsplit.symm

/-- The complete cancelled rectangular carrier loses exactly one order at
an actual right Xi pole, independently of the zero multiplicity. -/
theorem xiRectangularCancelledSeries_order
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    analyticOrderAt (xiRectangularCancelledSeries L)
        (xiRightShiftedPole q) =
      (xiRightMultiplicity q - 1 : ℕ) := by
  have heq := xiRectangularCancelledSeries_eventuallyEq_same_add_other L q
  rw [analyticOrderAt_congr heq]
  have hsame := xiRectangularSameSupportSeries_order hL q
  have hother := xiRectangularOtherSupportSeries_order_ge L q
  have hm : 0 < xiRightMultiplicity q := xiRightMultiplicity_pos q
  have hnat : xiRightMultiplicity q - 1 < xiRightMultiplicity q :=
    Nat.sub_one_lt (Nat.ne_of_gt hm)
  have henat : (xiRightMultiplicity q - 1 : ℕ∞) <
      (xiRightMultiplicity q : ℕ∞) := by exact_mod_cast hnat
  have hlt : analyticOrderAt (xiRectangularSameSupportSeries L q)
      (xiRightShiftedPole q) <
        analyticOrderAt (xiRectangularOtherSupportSeries L q)
          (xiRightShiftedPole q) := by
    rw [hsame]
    exact henat.trans_le hother
  rw [analyticOrderAt_add_eq_left_of_lt hlt, hsame]

/-- Translation by the shifted pole preserves the full Xi multiplicity. -/
theorem xi_shifted_half_order (q : XiRightZeroCopy) :
    analyticOrderAt (fun s : ℂ => xi (s - 1 / 2))
        (xiRightShiftedPole q) = xiRightMultiplicity q := by
  obtain ⟨R, hR, h, hhan, hh0, hfact⟩ := xi_peel_ball (q.1.1 : ℂ)
  let u : ℂ → ℂ := fun s => h (s - 1 / 2)
  have hball : (q.1.1 : ℂ) ∈ ball (q.1.1 : ℂ) R := mem_ball_self hR
  have hshift : xiRightShiftedPole q - 1 / 2 = (q.1.1 : ℂ) :=
    xiRightShiftedPole_sub_half q
  have hu : AnalyticAt ℂ u (xiRightShiftedPole q) :=
    (hhan (q.1.1 : ℂ) hball).comp_of_eq
      (analyticAt_id.sub analyticAt_const) hshift
  have hu0 : u (xiRightShiftedPole q) ≠ 0 := by
    dsimp only [u]
    rw [hshift]
    exact hh0 (q.1.1 : ℂ) hball
  have hev : (fun s : ℂ => xi (s - 1 / 2)) =ᶠ[nhds (xiRightShiftedPole q)]
      fun s => (s - xiRightShiftedPole q) ^ xiRightMultiplicity q * u s := by
    have hpoleball : xiRightShiftedPole q - 1 / 2 ∈ ball (q.1.1 : ℂ) R := by
      rw [hshift]
      exact hball
    filter_upwards [((continuousAt_id.sub_const (1 / 2 : ℂ)).eventually
      (isOpen_ball.mem_nhds hpoleball))] with s hs
    have hcoord : (s - 1 / 2) - (q.1.1 : ℂ) =
        s - xiRightShiftedPole q := by
      rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
      ring
    simpa only [xiRightMultiplicity, u, hcoord] using hfact (s - 1 / 2) hs
  have hxi : AnalyticAt ℂ (fun s : ℂ => xi (s - 1 / 2))
      (xiRightShiftedPole q) :=
    (xi_analyticOnNhd_univ
      (xiRightShiftedPole q - 1 / 2) (Set.mem_univ _)).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl
  exact (hxi.analyticOrderAt_eq_natCast (n := xiRightMultiplicity q)).2
    ⟨u, hu, hu0, hev⟩

end

end RHTower
