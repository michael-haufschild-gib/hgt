import GaloisForLFunctions.RHTower.XiZeroDensity
import GaloisForLFunctions.RHTower.ModulusSlopeField
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.DiscJump

/-!
# A height-adaptive finite RH ladder

The full cofinal RH ladder is stronger than necessary.  The unconditional Xi zero-count estimate
bounds every local multiplicity in `B(2,r)` by one common `O(r log r)` envelope.  Hence it is
enough, on each such disc, to impose one finite dyadic divisibility rung whose degree exceeds that
envelope.  A positive order cannot simultaneously be divisible by and strictly smaller than the
same power of two.

This is a quantitative top-down reduction.  It does not construct the regional Kummer roots or
source congruences which would supply the height-adaptive rungs.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- The multiplicity of one Xi zero in a closed ball is at most the total Xi divisor mass of the
ball. -/
theorem xiOrderToNat_le_xiBallOrderSum {c z : ℂ} {r : ℝ}
    (hz : z ∈ closedBall c r) :
    ((analyticOrderAt xi z).toNat : ℤ) ≤ xiBallOrderSum c r := by
  by_cases horder : (analyticOrderAt xi z).toNat = 0
  · rw [horder]
    exact xiBallOrderSum_nonneg c r
  · have hT := (MeromorphicOn.divisor xi (closedBall c r)).finiteSupport
      (isCompact_closedBall c r)
    have hDz : MeromorphicOn.divisor xi (closedBall c r) z =
        ((analyticOrderAt xi z).toNat : ℤ) := xi_divisor_closedBall_eq_order_toNat hz
    have hzT : z ∈ hT.toFinset := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, hDz]
      exact_mod_cast horder
    have hsum : xiBallOrderSum c r =
        ∑ u ∈ hT.toFinset, MeromorphicOn.divisor xi (closedBall c r) u := by
      rw [xiBallOrderSum]
      exact finsum_eq_sum_of_support_subset _ (by rw [Set.Finite.coe_toFinset])
    have hnn : ∀ u ∈ hT.toFinset,
        0 ≤ MeromorphicOn.divisor xi (closedBall c r) u := by
      intro u hu
      have hudom : u ∈ closedBall c r :=
        (MeromorphicOn.divisor xi (closedBall c r)).supportWithinDomain
          (by rwa [Set.Finite.mem_toFinset] at hu)
      rw [xi_divisor_closedBall_eq_order_toNat hudom]
      positivity
    rw [hsum, ← hDz]
    exact Finset.single_le_sum hnn hzT

/-- One finite dyadic rung restricted to right-half Xi zeros in the disc `B(2,r)`. -/
def XiDiscRHLadder (k : ℕ) (r : ℝ) : Prop :=
  ∀ ρ : ℂ, ρ ∈ rightHalf → ρ ∈ closedBall (2 : ℂ) r → xi ρ = 0 →
    2 ^ k ∣ (analyticOrderAt xi ρ).toNat

/-- A height-adaptive ladder uses only one rung on each bounded disc, with its degree fixed above
the supplied source-independent zero-count envelope. -/
def XiHeightAdaptiveDiscLadder (C : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r →
    ∃ k : ℕ,
      C * (1 + r) * Real.log (2 + r) < (2 ^ k : ℕ) ∧
      XiDiscRHLadder k r

/-! ## Regional analytic-root entrance -/

/-- Open right-half neighborhood of the closed disc window used by the regional ladder. -/
def xiDiscRootRegion (r : ℝ) : Set ℂ :=
  rightHalf ∩ ball (2 : ℂ) (r + 1)

theorem isOpen_xiDiscRootRegion (r : ℝ) : IsOpen (xiDiscRootRegion r) :=
  isOpen_rightHalf.inter isOpen_ball

/-- One finite analytic Kummer root on an open neighborhood of the bounded right-half window. -/
def XiDiscKummerRoot (k : ℕ) (r : ℝ) : Prop :=
  ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g (xiDiscRootRegion r) ∧
      ∀ s ∈ xiDiscRootRegion r, g s ^ (2 ^ k) = xi s

/-- A regional analytic Kummer root supplies the corresponding regional divisor rung. -/
theorem xiDiscRHLadder_of_kummerRoot
    {k : ℕ} {r : ℝ} (hroot : XiDiscKummerRoot k r) :
    XiDiscRHLadder k r := by
  obtain ⟨g, hg, hgpow⟩ := hroot
  intro ρ hρ hρball _hzero
  have hρregion : ρ ∈ xiDiscRootRegion r := by
    refine ⟨hρ, ?_⟩
    rw [mem_ball]
    have hdist : dist ρ (2 : ℂ) ≤ r := by
      simpa only [mem_closedBall, dist_comm] using hρball
    linarith
  have hdvdE : ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ :=
    root_orders_dvd (isOpen_xiDiscRootRegion r) hg hgpow hρregion
  have hcoe : analyticOrderAt xi ρ =
      (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  rw [hcoe] at hdvdE
  exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hdvdE

/-- Source-facing height-adaptive hypothesis: on each bounded window, construct only one finite
analytic root whose degree dominates the unconditional zero-count envelope. -/
def XiHeightAdaptiveDiscKummerRoots (C : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r →
    ∃ k : ℕ,
      C * (1 + r) * Real.log (2 + r) < (2 ^ k : ℕ) ∧
      XiDiscKummerRoot k r

/-- Countable source-facing version: regional roots are required only on cofinal integer discs. -/
def XiNatHeightAdaptiveDiscKummerRoots (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ,
      C * (1 + (n : ℝ)) * Real.log (2 + (n : ℝ)) < (2 ^ k : ℕ) ∧
      XiDiscKummerRoot k (n : ℝ)

theorem xiHeightAdaptiveDiscLadder_of_kummerRoots {C : ℝ}
    (hroots : XiHeightAdaptiveDiscKummerRoots C) :
    XiHeightAdaptiveDiscLadder C := by
  intro r hr
  obtain ⟨k, hk, hroot⟩ := hroots r hr
  exact ⟨k, hk, xiDiscRHLadder_of_kummerRoot hroot⟩

/-- Any zero-count envelope together with its height-adaptive regional ladder excludes all
right-half Xi zeros. -/
theorem riemannHypothesis_of_xiHeightAdaptiveDiscLadder_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r))
    (hladder : XiHeightAdaptiveDiscLadder C) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let r : ℝ := max 1 (dist ρ (2 : ℂ))
  have hr1 : 1 ≤ r := le_max_left _ _
  have hρball : ρ ∈ closedBall (2 : ℂ) r := by
    rw [mem_closedBall]
    simpa only [r, dist_comm] using
      (le_max_right (1 : ℝ) (dist ρ (2 : ℂ)))
  obtain ⟨k, hkLarge, hkDisc⟩ := hladder r hr1
  have hdvd : 2 ^ k ∣ (analyticOrderAt xi ρ).toNat :=
    hkDisc ρ hρ hρball hzero
  have hmne : (analyticOrderAt xi ρ).toNat ≠ 0 :=
    xi_order_toNat_ne_zero hzero
  have hmInt := xiOrderToNat_le_xiBallOrderSum hρball
  have hmReal : (((analyticOrderAt xi ρ).toNat : ℕ) : ℝ) ≤
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) := by
    exact_mod_cast hmInt
  have hmltReal : (((analyticOrderAt xi ρ).toNat : ℕ) : ℝ) <
      ((2 ^ k : ℕ) : ℝ) :=
    lt_of_le_of_lt (hmReal.trans (hcount r hr1)) hkLarge
  have hmlt : (analyticOrderAt xi ρ).toNat < 2 ^ k := by
    exact_mod_cast hmltReal
  have hle : 2 ^ k ≤ (analyticOrderAt xi ρ).toNat :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hmne) hdvd
  omega

/-- A fixed unconditional constant witnessing the Xi disc zero-count envelope. -/
noncomputable def xiZeroCountEnvelopeConstant : ℝ :=
  Classical.choose xi_zeroCount_growth

theorem xiZeroCountEnvelopeConstant_pos : 0 < xiZeroCountEnvelopeConstant :=
  (Classical.choose_spec xi_zeroCount_growth).1

theorem xiBallOrderSum_le_zeroCountEnvelope
    (r : ℝ) (hr : 1 ≤ r) :
    ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
      xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r) := by
  simpa only [xiZeroCountEnvelopeConstant, xiBallOrderSum] using
    (Classical.choose_spec xi_zeroCount_growth).2 r hr

/-- **Height-adaptive finite-ladder capstone.**  For the unconditional Xi zero-count envelope, one
sufficiently deep finite rung on every bounded disc already proves RH. -/
theorem riemannHypothesis_of_xiHeightAdaptiveDiscLadder
    (hladder : XiHeightAdaptiveDiscLadder xiZeroCountEnvelopeConstant) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiHeightAdaptiveDiscLadder_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope hladder

/-- **Regional finite-root chain to RH.**  Analytic roots of height-adapted finite degree on
bounded right-half windows imply the regional divisor ladder and therefore RH.  No global branch
and no compatibility across all higher Kummer depths is assumed. -/
theorem riemannHypothesis_of_xiHeightAdaptiveDiscKummerRoots
    (hroots : XiHeightAdaptiveDiscKummerRoots xiZeroCountEnvelopeConstant) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiHeightAdaptiveDiscLadder
    (xiHeightAdaptiveDiscLadder_of_kummerRoots hroots)

/-- Integer discs already exhaust the plane, so a countable family of height-adapted regional
Kummer roots suffices for any valid zero-count envelope. -/
theorem riemannHypothesis_of_xiNatHeightAdaptiveDiscKummerRoots_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r))
    (hroots : XiNatHeightAdaptiveDiscKummerRoots C) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max 1 (dist ρ (2 : ℂ)))
  have hn1real : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn1real.le
  have hρball : ρ ∈ closedBall (2 : ℂ) (n : ℝ) := by
    rw [mem_closedBall]
    have hdist : dist ρ (2 : ℂ) < (n : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hn
    simpa only [dist_comm] using hdist.le
  obtain ⟨k, hkLarge, hroot⟩ := hroots n hn1
  have hdvd := (xiDiscRHLadder_of_kummerRoot hroot) ρ hρ hρball hzero
  have hmne : (analyticOrderAt xi ρ).toNat ≠ 0 :=
    xi_order_toNat_ne_zero hzero
  have hmInt := xiOrderToNat_le_xiBallOrderSum hρball
  have hmReal : (((analyticOrderAt xi ρ).toNat : ℕ) : ℝ) ≤
      ((xiBallOrderSum (2 : ℂ) (n : ℝ) : ℤ) : ℝ) := by
    exact_mod_cast hmInt
  have hmltReal : (((analyticOrderAt xi ρ).toNat : ℕ) : ℝ) <
      ((2 ^ k : ℕ) : ℝ) :=
    lt_of_le_of_lt (hmReal.trans (hcount n (by exact_mod_cast hn1))) hkLarge
  have hmlt : (analyticOrderAt xi ρ).toNat < 2 ^ k := by
    exact_mod_cast hmltReal
  have hle : 2 ^ k ≤ (analyticOrderAt xi ρ).toNat :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hmne) hdvd
  omega

/-- **Countable regional-root capstone.**  One finite analytic Kummer root on each integer
right-half disc, at a degree dominating the unconditional Xi zero-count envelope, proves RH. -/
theorem riemannHypothesis_of_xiNatHeightAdaptiveDiscKummerRoots
    (hroots : XiNatHeightAdaptiveDiscKummerRoots xiZeroCountEnvelopeConstant) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiNatHeightAdaptiveDiscKummerRoots_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope hroots

/-! ## Scalar right-half census weakening -/

/-- The total right-half upper-box multiplicity below height `T` is bounded by the Xi divisor mass
of the global disc `B(2,T+2)`. -/
theorem boxOrderSum_le_xiBallOrderSum {T : ℝ} :
    (boxOrderSum T : ℤ) ≤ xiBallOrderSum (2 : ℂ) (T + 2) := by
  let D := MeromorphicOn.divisor xi (closedBall (2 : ℂ) (T + 2))
  have hS := D.finiteSupport (isCompact_closedBall (2 : ℂ) (T + 2))
  have hboxBall : ∀ z ∈ boxFinset T, z ∈ closedBall (2 : ℂ) (T + 2) := by
    intro z hz
    rw [mem_boxFinset] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hre : |(z - 2).re| < 2 := by
      change |z.re - 2| < 2
      rw [abs_lt]
      constructor <;> linarith [hz.1.1, hz.1.2.1]
    have him : |(z - 2).im| = z.im := by
      rw [sub_im]
      norm_num
      exact hz.1.2.2.1
    apply le_of_lt
    calc
      ‖z - 2‖ ≤ |(z - 2).re| + |(z - 2).im| := norm_le_abs_re_add_abs_im _
      _ < T + 2 := by rw [him]; linarith [hz.1.2.2.2]
  have hsub : boxFinset T ⊆ hS.toFinset := by
    intro z hz
    have hzbox := mem_boxFinset.mp hz
    have hzball := hboxBall z hz
    have hDz : D z = ((analyticOrderAt xi z).toNat : ℤ) :=
      xi_divisor_closedBall_eq_order_toNat hzball
    rw [Set.Finite.mem_toFinset, Function.mem_support, hDz]
    exact_mod_cast xi_order_toNat_ne_zero hzbox.2
  have hsumBall : xiBallOrderSum (2 : ℂ) (T + 2) =
      ∑ z ∈ hS.toFinset, D z := by
    rw [xiBallOrderSum]
    exact finsum_eq_sum_of_support_subset _ (by rw [Set.Finite.coe_toFinset])
  calc
    (boxOrderSum T : ℤ) =
        ∑ z ∈ boxFinset T, ((analyticOrderAt xi z).toNat : ℤ) := by
          simp [boxOrderSum]
    _ = ∑ z ∈ boxFinset T, D z := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (xi_divisor_closedBall_eq_order_toNat (hboxBall z hz)).symm
    _ ≤ ∑ z ∈ hS.toFinset, D z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro z hzS _hzbox
      have hzdom : z ∈ closedBall (2 : ℂ) (T + 2) :=
        D.supportWithinDomain (by rwa [Set.Finite.mem_toFinset] at hzS)
      rw [xi_divisor_closedBall_eq_order_toNat hzdom]
      positivity
    _ = xiBallOrderSum (2 : ℂ) (T + 2) := hsumBall.symm

/-- The right-half upper box has zero total multiplicity exactly when it has no Xi zero. -/
theorem boxOrderSum_eq_zero_iff_boxZeros_empty (T : ℝ) :
    boxOrderSum T = 0 ↔ boxZeros T = ∅ := by
  rw [boxOrderSum, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzfin : z ∈ boxFinset T := mem_boxFinset.mpr hz
    exact xi_order_toNat_ne_zero hz.2 (h z hzfin)
  · intro h z hz
    rw [mem_boxFinset, h] at hz
    exact absurd hz (Set.notMem_empty z)

/-- Weakest height-adaptive scalar hypothesis: at each integer height, one sufficiently large
dyadic modulus annihilates the single right-half DISC census value. -/
def XiNatHeightAdaptiveBoxCensus (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ,
      C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)) <
        (2 ^ k : ℕ) ∧
      discCensusH k (n : ℝ) = 0

/-- One scalar census congruence above the global zero-count envelope at every integer height
forces every right-half box to be empty and hence proves RH. -/
theorem riemannHypothesis_of_xiNatHeightAdaptiveBoxCensus_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r))
    (hcensus : XiNatHeightAdaptiveBoxCensus C) :
    RiemannHypothesis := by
  have hboxNat : ∀ n : ℕ, 1 ≤ n → boxOrderSum (n : ℝ) = 0 := by
    intro n hn
    obtain ⟨k, hkLarge, hcensusZero⟩ := hcensus n hn
    haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
    have hdvd : 2 ^ k ∣ boxOrderSum (n : ℝ) := by
      rw [discCensusH, ZMod.natCast_eq_zero_iff] at hcensusZero
      exact hcensusZero
    by_contra hboxne
    have hlePow : 2 ^ k ≤ boxOrderSum (n : ℝ) :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hboxne) hdvd
    have hboxInt := boxOrderSum_le_xiBallOrderSum (T := (n : ℝ))
    have hboxReal : (boxOrderSum (n : ℝ) : ℝ) ≤
        ((xiBallOrderSum (2 : ℂ) ((n : ℝ) + 2) : ℤ) : ℝ) := by
      exact_mod_cast hboxInt
    have hr1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      linarith
    have hboxLtReal : (boxOrderSum (n : ℝ) : ℝ) < ((2 ^ k : ℕ) : ℝ) :=
      lt_of_le_of_lt (hboxReal.trans (hcount ((n : ℝ) + 2) hr1)) hkLarge
    have hboxLt : boxOrderSum (n : ℝ) < 2 ^ k := by
      exact_mod_cast hboxLtReal
    omega
  rw [rh_iff_forall_boxZeros_empty]
  intro T
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max 1 T)
  have hn1real : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn1real.le
  have hTn : T ≤ (n : ℝ) :=
    (le_max_right (1 : ℝ) T).trans hn.le
  have hsumT : boxOrderSum T = 0 := by
    have hle := boxOrderSum_mono hTn
    rw [hboxNat n hn1] at hle
    omega
  exact (boxOrderSum_eq_zero_iff_boxZeros_empty T).mp hsumT

/-- **Scalar census capstone.**  For the unconditional Xi zero-count envelope, one vanishing DISC
census value at a sufficiently large dyadic modulus for every integer height already proves RH. -/
theorem riemannHypothesis_of_xiNatHeightAdaptiveBoxCensus
    (hcensus : XiNatHeightAdaptiveBoxCensus xiZeroCountEnvelopeConstant) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiNatHeightAdaptiveBoxCensus_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope hcensus

end

end RHTower
