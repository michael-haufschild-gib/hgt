import GaloisForLFunctions.ExceptionalLayerTheory.RecoveringZeroMultiplicityFromParabolicHadamardReadings
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorqueContinuationPole

/-!
# Exact bad heights of horizontal logarithmic derivative tests

A horizontal segment has readings unbounded below precisely when it
contains a zero after its left endpoint. Rational abscissae alone detect
it. Each fixed threshold in the open right half-plane therefore needs
only some height-dependent lower bound to characterize zero approach.
In contrast, almost every height satisfies all segment bounds
unconditionally.
-/

noncomputable section
open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.BacklundConverse RHTower.LindelofSparse RHTower.DeBruijn
open RHTower.CosineDefectBudget
namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev pt (x t : ℝ) : ℂ := ⟨x,t⟩
/-- Horizontal abscissa x at fixed ordinate t. -/
def horizontalHadamardReading (t x : ℝ) := (logDeriv xi (⟨x,t⟩:ℂ)).re

private theorem same_height_bound (a t : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, 0≤K ∧ ∀ x : ℝ, |x-a| < r →
      |horizontalHadamardReading t x-(hadamardOrder (pt a t):ℝ)/(x-a)|≤K := by
  obtain ⟨r,hr,K,hK,h⟩ := local_hadamard_principal_part_bound (pt a t)
  refine ⟨r,hr,K,hK,fun x hx => ?_⟩
  have he : pt x t-pt a t=((x-a:ℝ):ℂ) := by
    apply Complex.ext <;> simp [pt]
  have hb : pt x t∈ball (pt a t) r := by
    simpa only [mem_ball,dist_eq_norm,he,Complex.norm_real,Real.norm_eq_abs] using hx
  simpa only [horizontalHadamardReading,he,←Complex.ofReal_natCast,←Complex.ofReal_div,Complex.ofReal_re] using h _ hb

private theorem zero_free_of_rational_bound (a b t : ℝ) :
    (∃ B : ℝ, ∀ q : ℚ, (q:ℝ)∈Icc a b → B≤horizontalHadamardReading t q) →
    ∀ x ∈ Ioc a b, xi (pt x t)≠0 := by
  rintro ⟨B,hB⟩ x hx hz
  obtain ⟨r,hr,K,hK,h⟩ := same_height_bound x t
  let m : ℝ := hadamardOrder (pt x t)
  have hm : 0 < m := Nat.cast_pos.mpr
    (Nat.pos_of_ne_zero fun hn => (hadamardOrder_zero_iff _).mp hn hz)
  let D := |B|+K+1
  have hD : 0<D := by dsimp only [D]; positivity
  let u := min (min (x-a) r) (m/D)
  have hu : 0<u := lt_min (lt_min (sub_pos.mpr hx.1) hr) (div_pos hm hD)
  obtain ⟨q,hq,hl⟩ := exists_rat_btwn (show x-u<x by linarith only [hu])
  have hs : x-(q:ℝ)<u := by linarith only [hq]
  have hqr : x-(q:ℝ) < r := hs.trans_le ((min_le_left ..).trans (min_le_right ..))
  have hqa : x-(q:ℝ)<x-a := hs.trans_le ((min_le_left ..).trans (min_le_left ..))
  have hnear := h (q:ℝ) (by rw [abs_sub_comm,abs_of_pos (sub_pos.mpr hl)]; exact hqr)
  have he : (q:ℝ)-x= -(x-q) := by ring
  rw [he,div_neg,sub_neg_eq_add] at hnear
  have hqB := hB q ⟨by linarith only [hqa],hl.le.trans hx.2⟩
  have hDm := (lt_div_iff₀ hD).mp (hs.trans_le (min_le_right ..) : x-(q:ℝ) < m/D)
  have hlarge : D < m/(x-(q:ℝ)) := (lt_div_iff₀ (sub_pos.mpr hl)).mpr (by linarith only [hDm])
  change |horizontalHadamardReading t q+m/(x-q)|≤K at hnear
  dsimp only [D] at hlarge
  linarith only [hqB,(abs_le.mp hnear).2,hlarge,neg_abs_le B]

/-- All real abscissae give a lower-bounded reading precisely in the
absence of zeros in the half-open segment (a,b]. -/
theorem horizontal_lower_bound_iff (a b t : ℝ) :
    (∃ B : ℝ, ∀ x ∈ Icc a b, B≤horizontalHadamardReading t x) ↔
      ∀ x ∈ Ioc a b, xi (pt x t)≠0 := by
  constructor
  · rintro ⟨B,hB⟩
    exact zero_free_of_rational_bound a b t ⟨B,fun q hq => hB q hq⟩
  · intro hzero
    obtain ⟨r,hr,K,_,h⟩ := same_height_bound a t
    have hn (x : ℝ) (hx : x∈Icc (a+r/2) b) := hzero x
      (show x∈Ioc a b from ⟨by linarith only [hx.1,hr],hx.2⟩)
    have hc : ContinuousOn (horizontalHadamardReading t) (Icc (a+r/2) b) := by
      intro x hx
      have ha := xi_differentiable.analyticAt (pt x t)
      have hp : Continuous (fun x : ℝ => pt x t) := by
        have he (x : ℝ) : pt x t=(x:ℂ)+(t:ℂ)*I := (Complex.re_add_im (pt x t)).symm
        simp_rw [he]
        fun_prop
      exact (Complex.continuous_re.continuousAt.comp
        ((ha.deriv.continuousAt.div ha.continuousAt (hn x hx)).comp (f := fun y : ℝ => pt y t) (x := x)
          hp.continuousAt)).continuousWithinAt
    obtain ⟨B,hB⟩ := isCompact_Icc.bddBelow_image hc
    refine ⟨min B (-K),fun x hx => ?_⟩
    by_cases hfar : a+r/2≤x
    · exact (min_le_left ..).trans (hB (mem_image_of_mem _ ⟨hfar,hx.2⟩))
    have hn := sub_nonneg.mpr hx.1
    have hnear := h x (by rw [abs_of_nonneg hn]; linarith only [not_le.mp hfar,hr])
    have hp := div_nonneg (Nat.cast_nonneg (hadamardOrder (pt a t)) : (0:ℝ)≤_) hn
    exact (min_le_right ..).trans (by linarith only [(abs_le.mp hnear).1,hp])

/-- Rational horizontal samples already detect every zero after the
left endpoint. At such a zero an entire interval to its left violates
any fixed candidate lower bound. -/
theorem rational_horizontal_lower_bound_iff (a b t : ℝ) :
    (∃ B : ℝ, ∀ q : ℚ, (q:ℝ)∈Icc a b → B≤horizontalHadamardReading t q) ↔
      ∀ x ∈ Ioc a b, xi (pt x t)≠0 := by
  constructor
  · exact zero_free_of_rational_bound a b t
  · intro hz
    obtain ⟨B,hB⟩ := (horizontal_lower_bound_iff a b t).mpr hz
    exact ⟨B,fun q hq => hB q hq⟩

/-- Outside a single null set of heights every horizontal lower bound
holds simultaneously, for every pair of endpoints. -/
theorem almost_every_height_all_horizontal_bounds :
    ∀ᵐ t : ℝ, ∀ a b : ℝ, ∃ B : ℝ, ∀ x ∈ Icc a b, B≤horizontalHadamardReading t x := by
  have hnull := (xi_zeroSet_countable.image Complex.im).measure_zero (μ:=volume)
  have hae : ∀ᵐ t : ℝ, t ∉ Complex.im '' {z : ℂ | xi z=0} :=
    ae_iff.mpr (by simpa only [not_not,Set.setOf_mem_eq] using hnull)
  filter_upwards [hae] with t ht
  intro a b
  apply (horizontal_lower_bound_iff a b t).mpr
  intro x _ hz
  exact ht ⟨pt x t,hz,rfl⟩

/-- Even a dense countable schedule of observation heights misses
every unbounded row after almost every common translation. -/
theorem almost_every_translate_misses_all_bad_rows (heights : ℕ → ℝ) :
    ∀ᵐ u : ℝ, ∀ n : ℕ, ∀ a b : ℝ, ∃ B : ℝ,
      ∀ x ∈ Icc a b, B≤horizontalHadamardReading (u+heights n) x := by
  let Z := Complex.im '' {z : ℂ | xi z=0}
  let bad := ⋃ n : ℕ, (fun t : ℝ => t-heights n) '' Z
  have hn : bad.Countable := countable_iUnion fun n =>
    (xi_zeroSet_countable.image Complex.im).image (fun t => t-heights n)
  have hae : ∀ᵐ u : ℝ, u∉bad := ae_iff.mpr (by
    simpa only [not_not,Set.setOf_mem_eq] using hn.measure_zero (μ:=volume))
  filter_upwards [hae] with u hu
  intro n a b
  apply (horizontal_lower_bound_iff a b _).mpr
  intro x _ hz
  exact hu (mem_iUnion.mpr ⟨n,u+heights n,⟨pt x (u+heights n),hz,rfl⟩,add_sub_cancel_right ..⟩)

/-- Zero approach is equivalent to a finite lower bound on each late
horizontal rational segment. The bound may vary arbitrarily with its
height and need only hold on the finite abscissa interval [σ,1]. -/
theorem zero_approach_iff_horizontal_rational_bounds :
    ZerosApproachLine ↔ ∀ σ : ℝ, 1/2<σ → ∃ T : ℝ, ∀ t : ℝ, T≤|t| →
      ∃ B : ℝ, ∀ q : ℚ, (q:ℝ)∈Icc σ 1 → B≤horizontalHadamardReading t q := by
  constructor
  · intro hZ σ hσ
    obtain ⟨T,hT⟩ := eventualHadamardPositivity_of_zerosApproachLine hZ σ hσ
    exact ⟨T,fun t ht => ⟨0,fun q hq => hT (pt q t) hq.1 ht⟩⟩
  · intro h h₀ hpos
    obtain ⟨T,hT⟩ := h (1/2+h₀) (by linarith only [hpos])
    have hbound (q : XiZeroCopy) (hq : q∈deepCopies h₀) : |((q.1:ℂ)).im|<T := by
      by_contra! ht
      let ρ : ℂ := 1-(q.1:ℂ)
      have hz : xi ρ=0 := by simpa only [ρ,xi_one_sub] using xi_xiZeroCopy_eq_zero q
      have hd : h₀<(xiSpectralPoint q).im := hq
      rw [spectral_im_eq] at hd
      have hr : 1/2+h₀<ρ.re := by
        dsimp only [ρ,Complex.sub_re,Complex.one_re]; linarith only [hd]
      have hr' : ρ.re≤1 := le_of_not_gt (fun hgt => xi_ne_zero_of_one_le_re hgt.le hz)
      have hheight : T≤|ρ.im| := by simpa [ρ] using ht
      exact (rational_horizontal_lower_bound_iff _ 1 _).mp (hT ρ.im hheight)
        ρ.re ⟨hr,hr'⟩ hz
    refine (xiZeroBall (⌈|T|+1⌉₊)).finite_toSet.subset fun q hq => ?_
    simp only [Finset.mem_coe,mem_xiZeroBall]
    have h₁ := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    have h₂ := abs_spectral_im_lt_half q
    have h₃ : |T|+1≤(⌈|T|+1⌉₊:ℝ) := Nat.le_ceil _
    have h₄ : |(xiSpectralPoint q).re|≤|T| := by
      rw [spectral_re_eq]; exact (hbound q hq).le.trans (le_abs_self T)
    linarith only [h₁,h₂,h₃,h₄]

#print axioms horizontal_lower_bound_iff
#print axioms rational_horizontal_lower_bound_iff
#print axioms almost_every_height_all_horizontal_bounds
#print axioms almost_every_translate_misses_all_bad_rows
#print axioms zero_approach_iff_horizontal_rational_bounds
end GaloisForLFunctions.ExceptionalLayerTheory
