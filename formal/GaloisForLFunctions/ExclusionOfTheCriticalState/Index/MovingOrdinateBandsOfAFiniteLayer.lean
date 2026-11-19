import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConditionalOrdinateLawOnMultiplicativeBands

/-!
# Critical-line mass on moving ordinate bands

Ponge and Tian's moving-dilation law for regularly varying functions
(arXiv:2605.25591, Lemma 2.17) applies to the ordinate tail of a threshold
state in the finite stratum. Two cutoffs asymptotic to aT and bT select
mass with coefficient C(1/a − 1/max(a,b)). Bands of sublinear thickness
are invisible at this normalization. A band of positive relative thickness
gives a localized test for exclusion of a finite off-line divisor.
-/

noncomputable section

open Filter Set MeasureTheory Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem band_eq_tail_sub {F : ℝ → ℝ}
    (hs : Summable (fun q : onLineCopies => zeroValueMass F q)) (u v : ℝ) :
    ordinateBandMass F u v = ordinateTailMass F u - ordinateTailMass F (max u v) := by
  have hs' (t : ℝ) : Summable (fun q : onLineCopies =>
      if t < |(centredZero q).im| then zeroValueMass F q else 0) :=
    hs.of_nonneg_of_le (fun q => ite_zero_nonneg (zeroValueMass_nonneg F q))
      (fun q => ite_zero_le (zeroValueMass_nonneg F q))
  rw [ordinateBandMass, ordinateTailMass, ordinateTailMass, ← (hs' u).tsum_sub (hs' _)]
  apply tsum_congr
  intro q
  by_cases hu : u < |(centredZero q).im| <;> by_cases hv : v < |(centredZero q).im| <;>
    simp [← not_lt, hu, hv, max_lt_iff]

private theorem coefficient_pos {W : ℝ} {F : ℝ → ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    (hF : IsCriticalHalfLineGroundState W F) : 0 < ordinateCuspConstant W F := by
  have ha := criticalAliasCoefficient_positive hW
  have hm := exponentialPair_self_pos (criticalHalfLineEnergyDomain_of_groundState hF)
    (isConfinedNullVector_of_groundState hW ht hF).2.1
  have he : (∫ u : ℝ, F u ^ 2 * Real.exp (-(8*u))) = criticalHalfLineExponentialPair F F := by
    unfold criticalHalfLineExponentialPair
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  rw [ordinateCuspConstant, he]
  positivity

private theorem move_cut {ι : Type*} {l : Filter ι} {T u : ι → ℝ} {f : ℝ → ℝ} {c a : ℝ}
    (htail : Tendsto (fun t => t*f t) atTop (𝓝 c)) (hT : Tendsto T l atTop)
    (hu : Tendsto u l (𝓝 a)) (ha : 0 < a) :
    Tendsto (fun i => T i*f (T i*u i)) l (𝓝 (c/a)) := by
  have h := (htail.comp (hT.atTop_mul_pos ha hu)).div hu ha.ne'
  refine h.congr' ?_
  filter_upwards [hu.eventually_ne ha.ne'] with i hi
  change (T i*u i*f (T i*u i))/u i = _
  field_simp <;> ring

/-- Moving bands have an exact coefficient, including when their cutoffs
cross infinitely often. The formula also allows discrete subsequences. -/
theorem moving_ordinate_band_limit {ι : Type*} {l : Filter ι} {T u v : ι → ℝ}
    {a b W : ℝ} {F : ℝ → ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    (hT : Tendsto T l atTop) (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b)) (ha : 0 < a) :
    Tendsto (fun i => T i * ordinateBandMass F (T i*u i) (T i*v i)) l
      (𝓝 (ordinateCuspConstant W F/a - ordinateCuspConstant W F/max a b)) := by
  have hs := (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  have hh : Tendsto (fun t => t * ordinateTailMass F t) atTop (𝓝 (ordinateCuspConstant W F)) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  have h := (move_cut hh hT hu ha).sub (move_cut hh hT (hu.max hv) (ha.trans_le (le_max_left ..)))
  refine h.congr' ?_
  filter_upwards [hT.eventually (eventually_ge_atTop (0:ℝ))] with i hi
  rw [band_eq_tail_sub hs, mul_sub, ← mul_max_of_nonneg _ _ hi]

/-- Conditional on exceeding t, the relative tail at bt is asymptotic to
1/b. Relative error is uniform for every b ≥ 1, including unbounded b. -/
theorem uniform_relative_ordinate_tail {W : ℝ} {F : ℝ → ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t : ℝ in atTop, 0 < ordinateTailMass F t ∧
      ∀ b : ℝ, 1 ≤ b → |b*ordinateTailMass F (b*t)/ordinateTailMass F t - 1| < ε := by
  let C := ordinateCuspConstant W F
  have hC : 0 < C := coefficient_pos hW ht hF
  have h : Tendsto (fun t => t*ordinateTailMass F t) atTop (𝓝 C) :=
    criticalState_criticalLine_tail_asymptotic hW ht hF hf
  let δ := min (C/2) (ε*C/8)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨A,hA⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp h) δ hδ)
  filter_upwards [eventually_ge_atTop A,eventually_gt_atTop (0:ℝ)] with t htA ht₀
  have he (v : ℝ) (hv : A ≤ v) : |v*ordinateTailMass F v-C| < δ := by
    simpa only [Real.dist_eq] using hA v hv
  have htlo := (abs_lt.mp (he t htA)).1
  have hden : C/2 < t*ordinateTailMass F t := by linarith only [htlo,min_le_left (C/2) (ε*C/8)]
  have hprod := (half_pos hC).trans hden
  have htail := pos_of_mul_pos_right hprod ht₀.le
  refine ⟨htail,fun b hb => ?_⟩
  have hbt := htA.trans (le_mul_of_one_le_left ht₀.le hb)
  have hdiff := abs_sub_le (b*t*ordinateTailMass F (b*t)) C (t*ordinateTailMass F t)
  rw [abs_sub_comm C] at hdiff
  have h₁ := he (b*t) hbt
  have h₂ := he t htA
  have hnum : |b*t*ordinateTailMass F (b*t)-t*ordinateTailMass F t| < ε*(t*ordinateTailMass F t) := by
    have hbound := min_le_right (C/2) (ε*C/8)
    linarith only [hdiff,h₁,h₂,hbound,mul_lt_mul_of_pos_left hden hε,mul_pos hε hC]
  have heq : b*ordinateTailMass F (b*t)/ordinateTailMass F t-1 =
      (b*t*ordinateTailMass F (b*t)-t*ordinateTailMass F t)/(t*ordinateTailMass F t) := by
    field_simp <;> ring
  rw [heq,abs_div,abs_of_pos hprod]
  exact (div_lt_iff₀ hprod).mpr hnum

/-- Combined mass of all zero copies with one absolute ordinate. -/
def ordinateAtomMass (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' q : onLineCopies, if |(centredZero q).im| = t then zeroValueMass F q else 0

private theorem ordinate_atom_nonneg (F : ℝ → ℝ) (t : ℝ) : 0 ≤ ordinateAtomMass F t :=
  tsum_nonneg fun q => ite_zero_nonneg (zeroValueMass_nonneg F q)

private theorem atom_le_band {F : ℝ → ℝ} (hs : Summable (fun q : onLineCopies => zeroValueMass F q))
    {u t : ℝ} (hu : u < t) : ordinateAtomMass F t ≤ ordinateBandMass F u t := by
  have hsum (P : onLineCopies → Prop) [DecidablePred P] :
      Summable (fun q : onLineCopies => if P q then zeroValueMass F q else 0) :=
    hs.of_nonneg_of_le (fun q => ite_zero_nonneg (zeroValueMass_nonneg F q))
      (fun q => ite_zero_le (zeroValueMass_nonneg F q))
  apply Summable.tsum_le_tsum _ (hsum _) (hsum _)
  intro q
  by_cases h : |(centredZero q).im| = t
  · simp only [if_pos h, h, hu, le_refl, and_self, if_true]
  · rw [if_neg h]; exact ite_zero_nonneg (zeroValueMass_nonneg F q)

/-- A single ordinate, even with all its multiplicities and both signs
combined, carries a vanishing fraction of the critical tail. -/
theorem single_ordinate_mass_vanishes {W : ℝ} {F : ℝ → ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun t : ℝ => t*ordinateAtomMass F t) atTop (𝓝 0) := by
  have hs := (domain_zeroParseval_of_finiteOffLine (criticalHalfLineEnergyDomain_of_groundState hF) hf).1
  have hu : Tendsto (fun t : ℝ => 1-1/t) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub
      ((tendsto_const_nhds (x := (1:ℝ))).div_atTop
        (show Tendsto (fun t : ℝ => t) atTop atTop from tendsto_id))
  have h := moving_ordinate_band_limit hW ht hF hf tendsto_id hu
    (tendsto_const_nhds (x := (1:ℝ))) zero_lt_one
  rw [max_self,sub_self] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t h₀
    exact mul_nonneg h₀ (ordinate_atom_nonneg F t)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t h₀
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left (atom_le_band hs
      (by rw [mul_sub,mul_one,mul_one_div_cancel h₀.ne']; linarith)) h₀.le

/-- Uniformly over all moving packets of at most k ordinate heights above
T, their total mass is o(1/T). The number of copies at any selected height
is unrestricted. -/
theorem bounded_ordinate_packets_vanish {W : ℝ} {F : ℝ → ℝ} (hW : 0 < W)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal))
    (hF : IsCriticalHalfLineGroundState W F) (hf : BacklundConverse.FiniteOffLine)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ S : Finset ℝ, S.card ≤ k → (∀ u ∈ S, t ≤ u) →
      t*(∑ u ∈ S, ordinateAtomMass F u) < ε := by
  let δ := ε/((k:ℝ)+1)
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hk
  obtain ⟨A,hA⟩ := eventually_atTop.mp
    ((single_ordinate_mass_vanishes hW ht hF hf).eventually_lt_const hδ)
  filter_upwards [eventually_ge_atTop A] with t htA
  intro S hS hloc
  have h (u : ℝ) (hu : u ∈ S) : t*ordinateAtomMass F u ≤ δ :=
    (mul_le_mul_of_nonneg_right (hloc u hu) (ordinate_atom_nonneg F u)).trans
      (hA u (htA.trans (hloc u hu))).le
  have hsum := Finset.sum_le_sum h
  rw [←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hsum
  have hc := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hS : (S.card:ℝ) ≤ k) hδ.le)
  have he : ((k:ℝ)+1)*δ = ε := by dsimp only [δ]; field_simp
  exact (hsum.trans hc).trans_lt (by linarith only [he,hδ])

/-- Existence of a vanishing sequence in one prescribed multiplicative band,
for every threshold state in the finite stratum. -/
def sequentialBandVanishing (p q : ℝ) : Prop :=
  BacklundConverse.FiniteOffLine → ∀ (W : ℝ) (F : ℝ → ℝ), 0 < W →
    (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal) →
    IsCriticalHalfLineGroundState W F →
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ Tendsto
      (fun n => T n * ordinateBandMass F (T n * Real.exp p) (T n * Real.exp q)) atTop (𝓝 0)

/-- A vanishing sequence on any fixed band of positive logarithmic width
is equivalent to finite-layer exclusion. At zero or negative width the
vanishing test always holds. -/
theorem sequential_band_vanishing_iff (p q : ℝ) :
    sequentialBandVanishing p q ↔ q ≤ p ∨ (BacklundConverse.FiniteOffLine → RiemannHypothesis) := by
  have hnone : (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
      (BacklundConverse.FiniteOffLine → ¬ ∃ (W : ℝ) (F : ℝ → ℝ), 0 < W ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W : EReal) ∧
        IsCriticalHalfLineGroundState W F) := finiteLayer_ecs_b13_tfae.out 0 1
  constructor
  · intro test
    by_cases h : q ≤ p
    · exact Or.inl h
    right
    apply hnone.mpr
    rintro hf ⟨W,F,hW,ht,hF⟩
    obtain ⟨T,hT,hv⟩ := test hf W F hW ht hF
    have hab := Real.exp_lt_exp.mpr (lt_of_not_ge h)
    have he := moving_ordinate_band_limit hW ht hF hf hT
      (tendsto_const_nhds (x := Real.exp p)) (tendsto_const_nhds (x := Real.exp q)) (Real.exp_pos _)
    rw [max_eq_right hab.le] at he
    have hp := div_lt_div_of_pos_left (coefficient_pos hW ht hF) (Real.exp_pos _) hab
    exact (sub_pos.mpr hp).ne' (tendsto_nhds_unique he hv)
  · rintro (hp|hex) hf W F hW ht hF
    · refine ⟨fun n => (n:ℝ), tendsto_natCast_atTop_atTop, ?_⟩
      have h := moving_ordinate_band_limit hW ht hF hf (T := fun n : ℕ => (n:ℝ))
        tendsto_natCast_atTop_atTop (tendsto_const_nhds (x := Real.exp p))
        (tendsto_const_nhds (x := Real.exp q)) (Real.exp_pos _)
      simpa only [max_eq_left (Real.exp_le_exp.mpr hp), sub_self] using h
    · exact False.elim (hnone.mp hex hf ⟨W,F,hW,ht,hF⟩)

#print axioms uniform_relative_ordinate_tail
#print axioms single_ordinate_mass_vanishes
#print axioms bounded_ordinate_packets_vanish
#print axioms moving_ordinate_band_limit
#print axioms sequential_band_vanishing_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState
