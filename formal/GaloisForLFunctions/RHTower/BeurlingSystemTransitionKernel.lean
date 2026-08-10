import GaloisForLFunctions.RHTower.BeurlingSystemTailBound

/-!
# The one-large-prime kernel and its single sign transition

The kernel `(BF7)` of the critical seam is `e^{-t}(1 - ∑_{|p| > z} e^{-(|p|-1)t})`.  Its prime sum
converges for every positive `t`, is strictly decreasing there, tends to zero at infinity and, when
the system has infinitely many primes above the cutoff, blows up at the origin.  Hence the kernel
changes sign exactly once, at the unique solution of `∑_{|p| > z} e^{-(|p|-1)τ} = 1`.
-/

open scoped BigOperators
open Filter Topology

namespace RHTower

namespace BeurlingSystem

variable (B : BeurlingSystem)

/-- The large-prime sum of the kernel `(BF7)`. -/
noncomputable def largeTail (z t : ℝ) : ℝ :=
  ∑' p : {p : B.Label // z < B.labelNorm p},
    Real.exp (-(B.labelNorm (p : B.Label) - 1) * t)

/-- The one-large-prime kernel `(BF7)`. -/
noncomputable def transitionKernel (z t : ℝ) : ℝ :=
  Real.exp (-t) * (1 - B.largeTail z t)

variable {B}

/-! ## Convergence -/

theorem summable_expNegLabelNorm (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {t : ℝ} (ht : 0 < t) :
    Summable fun p : B.Label => Real.exp (-t * B.labelNorm p) := by
  have hinj : Function.Injective fun p : B.Label => ({p} : Multiset B.Label) := by
    intro p q hpq
    exact Multiset.singleton_inj.mp hpq
  have hsum := (summable_expNegNorm hdisc hC ht).comp_injective hinj
  refine hsum.congr fun p => ?_
  rw [Function.comp_apply, intNorm_singleton]

theorem summable_largeTailTerm (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (z : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable fun p : {p : B.Label // z < B.labelNorm p} =>
      Real.exp (-(B.labelNorm (p : B.Label) - 1) * t) := by
  have hbase := (summable_expNegLabelNorm hdisc hC ht).mul_left (Real.exp t)
  have hrw : ∀ p : B.Label, Real.exp t * Real.exp (-t * B.labelNorm p)
      = Real.exp (-(B.labelNorm p - 1) * t) := by
    intro p
    rw [← Real.exp_add]
    congr 1
    ring
  exact ((hbase.congr hrw).subtype _)

/-! ## Monotonicity -/

theorem largeTail_strictAnti (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (z : ℝ) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht : t₁ < t₂)
    (hne : Nonempty {p : B.Label // z < B.labelNorm p}) :
    B.largeTail z t₂ < B.largeTail z t₁ := by
  obtain ⟨p₀⟩ := hne
  have hlt : ∀ p : {p : B.Label // z < B.labelNorm p},
      Real.exp (-(B.labelNorm (p : B.Label) - 1) * t₂)
        ≤ Real.exp (-(B.labelNorm (p : B.Label) - 1) * t₁) := by
    intro p
    refine Real.exp_le_exp.mpr ?_
    have hp1 : 1 < B.labelNorm (p : B.Label) := B.one_lt_labelNorm _
    nlinarith
  have hstrict : Real.exp (-(B.labelNorm (p₀ : B.Label) - 1) * t₂)
      < Real.exp (-(B.labelNorm (p₀ : B.Label) - 1) * t₁) := by
    refine Real.exp_lt_exp.mpr ?_
    have hp1 : 1 < B.labelNorm (p₀ : B.Label) := B.one_lt_labelNorm _
    nlinarith
  exact Summable.tsum_lt_tsum (i := p₀) hlt hstrict
    (summable_largeTailTerm hdisc hC z (lt_trans ht₁ ht))
    (summable_largeTailTerm hdisc hC z ht₁)

theorem largeTail_nonneg (z t : ℝ) : 0 ≤ B.largeTail z t :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-! ## The sign of the kernel -/

theorem transitionKernel_pos_iff (z t : ℝ) :
    0 < B.transitionKernel z t ↔ B.largeTail z t < 1 := by
  rw [transitionKernel]
  constructor
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    have : Real.exp (-t) * (1 - B.largeTail z t) ≤ 0 := by
      have hexp : 0 < Real.exp (-t) := Real.exp_pos _
      nlinarith
    linarith
  · intro h
    have hexp : 0 < Real.exp (-t) := Real.exp_pos _
    have : 0 < 1 - B.largeTail z t := by linarith
    positivity

theorem transitionKernel_neg_iff (z t : ℝ) :
    B.transitionKernel z t < 0 ↔ 1 < B.largeTail z t := by
  rw [transitionKernel]
  have hexp : 0 < Real.exp (-t) := Real.exp_pos _
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem transitionKernel_eq_zero_iff (z t : ℝ) :
    B.transitionKernel z t = 0 ↔ B.largeTail z t = 1 := by
  rw [transitionKernel]
  have hexp : 0 < Real.exp (-t) := Real.exp_pos _
  constructor
  · intro h
    have := mul_eq_zero.mp h
    rcases this with h1 | h2
    · exact absurd h1 (ne_of_gt hexp)
    · linarith
  · intro h
    rw [h]
    ring


/-! ## Continuity and the two limits -/

theorem continuousOn_largeTail (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (z : ℝ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => B.largeTail z t) (Set.Ici a) := by
  refine continuousOn_tsum (fun p => ?_) (summable_largeTailTerm hdisc hC z ha) ?_
  · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  · intro p t ht
    have hp1 : 1 < B.labelNorm (p : B.Label) := B.one_lt_labelNorm _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have hta : a ≤ t := ht
    nlinarith

theorem tendsto_largeTail_atTop (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (z : ℝ) :
    Tendsto (fun t => B.largeTail z t) atTop (nhds 0) := by
  have hlim : ∀ p : {p : B.Label // z < B.labelNorm p},
      Tendsto (fun t : ℝ => Real.exp (-(B.labelNorm (p : B.Label) - 1) * t)) atTop (nhds 0) := by
    intro p
    have hp1 : 1 < B.labelNorm (p : B.Label) := B.one_lt_labelNorm _
    have hpos : 0 < B.labelNorm (p : B.Label) - 1 := by linarith
    have h1 : Tendsto (fun t : ℝ => (B.labelNorm (p : B.Label) - 1) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hpos tendsto_id
    have hneg : Tendsto (fun t : ℝ => -(B.labelNorm (p : B.Label) - 1) * t) atTop atBot := by
      refine (tendsto_neg_atTop_atBot.comp h1).congr fun t => ?_
      show -((B.labelNorm (p : B.Label) - 1) * t) = -(B.labelNorm (p : B.Label) - 1) * t
      ring
    exact Real.tendsto_exp_atBot.comp hneg
  have hdom : ∀ᶠ t : ℝ in atTop, ∀ p : {p : B.Label // z < B.labelNorm p},
      ‖Real.exp (-(B.labelNorm (p : B.Label) - 1) * t)‖
        ≤ Real.exp (-(B.labelNorm (p : B.Label) - 1) * 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht p
    have hp1 : 1 < B.labelNorm (p : B.Label) := B.one_lt_labelNorm _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hmain := tendsto_tsum_of_dominated_convergence
    (summable_largeTailTerm hdisc hC z (by norm_num : (0:ℝ) < 1)) hlim hdom
  have hzero : (∑' _p : {p : B.Label // z < B.labelNorm p}, (0 : ℝ)) = 0 := tsum_zero
  rw [hzero] at hmain
  exact hmain

theorem tendsto_largeTail_atZero (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (z : ℝ) (hinf : Infinite {p : B.Label // z < B.labelNorm p}) :
    Tendsto (fun t => B.largeTail z t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq {p : B.Label // z < B.labelNorm p} (⌈b⌉₊ + 1)
  have hfinlim : Tendsto (fun t : ℝ =>
      ∑ p ∈ S, Real.exp (-(B.labelNorm (p : B.Label) - 1) * t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((⌈b⌉₊ : ℝ) + 1)) := by
    have hterm : ∀ p ∈ S, Tendsto (fun t : ℝ =>
        Real.exp (-(B.labelNorm (p : B.Label) - 1) * t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      intro p _
      have hcont : Continuous fun t : ℝ => Real.exp (-(B.labelNorm (p : B.Label) - 1) * t) :=
        Real.continuous_exp.comp (by fun_prop)
      have h0 : Tendsto (fun t : ℝ => Real.exp (-(B.labelNorm (p : B.Label) - 1) * t))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (Real.exp (-(B.labelNorm (p : B.Label) - 1) * 0))) :=
        (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h0
    have hsum := tendsto_finsetSum S hterm
    rw [Finset.sum_const, hS, nsmul_eq_mul, mul_one] at hsum
    push_cast at hsum
    exact hsum
  have hb : b < (⌈b⌉₊ : ℝ) + 1 := by
    have := Nat.le_ceil b
    linarith
  filter_upwards [hfinlim.eventually_const_lt hb, self_mem_nhdsWithin] with t ht htpos
  have hsum : ∑ p ∈ S, Real.exp (-(B.labelNorm (p : B.Label) - 1) * t) ≤ B.largeTail z t := by
    refine (summable_largeTailTerm hdisc hC z htpos).sum_le_tsum S ?_
    intro p _
    exact (Real.exp_pos _).le
  linarith

/-! ## The single sign transition -/

/-- **The one-large-prime kernel has exactly one sign transition `(BF7)`.**  There is a unique
positive time at which the kernel vanishes; below it the kernel is negative and above it
positive. -/
theorem exists_unique_transition (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (z : ℝ) (hinf : Infinite {p : B.Label // z < B.labelNorm p}) :
    ∃! τ : ℝ, 0 < τ ∧ B.largeTail z τ = 1 := by
  have hne : Nonempty {p : B.Label // z < B.labelNorm p} := inferInstance
  obtain ⟨t₁, ht₁⟩ := ((tendsto_largeTail_atZero hdisc hC z hinf).eventually_gt_atTop 1 |>.and
    self_mem_nhdsWithin).exists
  obtain ⟨ht₁gt, ht₁pos⟩ := ht₁
  obtain ⟨t₂, ht₂lt, ht₂gt⟩ := ((tendsto_largeTail_atTop hdisc hC z).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)) |>.and (eventually_gt_atTop t₁)).exists
  have ht₂pos : 0 < t₂ := lt_trans ht₁pos ht₂gt
  have hcont : ContinuousOn (fun t => B.largeTail z t) (Set.Icc t₁ t₂) :=
    (continuousOn_largeTail hdisc hC z ht₁pos).mono
      (fun t ht => le_trans (le_of_eq rfl) ht.1)
  have hmem : (1 : ℝ) ∈ Set.Icc (B.largeTail z t₂) (B.largeTail z t₁) :=
    ⟨ht₂lt.le, ht₁gt.le⟩
  obtain ⟨τ, hτmem, hτ⟩ := intermediate_value_Icc' ht₂gt.le hcont hmem
  have hτ' : B.largeTail z τ = 1 := hτ
  have hτpos : 0 < τ := lt_of_lt_of_le ht₁pos hτmem.1
  refine ⟨τ, ⟨hτpos, hτ'⟩, ?_⟩
  rintro σ ⟨hσpos, hσ⟩
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hstep := largeTail_strictAnti hdisc hC z hσpos hlt hne
    rw [hσ, hτ'] at hstep
    linarith
  · have hstep := largeTail_strictAnti hdisc hC z hτpos hgt hne
    rw [hσ, hτ'] at hstep
    linarith


/-- **The sign pattern across the transition `(BF7)`.**  The kernel is negative before the
transition time and positive after it. -/
theorem transitionKernel_sign (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (z : ℝ) (hinf : Infinite {p : B.Label // z < B.labelNorm p}) {τ : ℝ} (hτpos : 0 < τ)
    (hτ : B.largeTail z τ = 1) :
    (∀ t : ℝ, 0 < t → t < τ → B.transitionKernel z t < 0) ∧
      (∀ t : ℝ, τ < t → 0 < B.transitionKernel z t) := by
  have hne : Nonempty {p : B.Label // z < B.labelNorm p} := inferInstance
  constructor
  · intro t ht0 htτ
    rw [transitionKernel_neg_iff]
    have hstep := largeTail_strictAnti hdisc hC z ht0 htτ hne
    rw [hτ] at hstep
    exact hstep
  · intro t htτ
    rw [transitionKernel_pos_iff]
    have hstep := largeTail_strictAnti hdisc hC z hτpos htτ hne
    rw [hτ] at hstep
    exact hstep

end BeurlingSystem

end RHTower
