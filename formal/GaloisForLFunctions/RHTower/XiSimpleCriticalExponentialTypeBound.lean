import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging
import GaloisForLFunctions.RHTower.SuzukiCompactL2Fourier

/-!
# Simple critical ordinates versus finite exponential type

The actual simple critical Xi zeros are reindexed by their positive ordinates.  Jensen's linear
zero-density bound then shows that a nonzero finite-exponential-type function cannot annihilate all
of those ordinates, apart from a fixed finite set, unless their counting function is only linear.
The compactly supported `L²` Fourier transform receives this conclusion through the existing
Paley--Wiener bound.
-/

noncomputable section

open Complex Metric Set

namespace RHTower

/-- Actual simple critical Xi zeros with ordinate in `(0,T]`. -/
def xiSimpleCriticalZeroFinset (T : ℝ) : Finset ℂ :=
  (stripFinsetPos T).filter
    (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)

@[simp] theorem card_xiSimpleCriticalZeroFinset (T : ℝ) :
    (xiSimpleCriticalZeroFinset T).card = xiSimpleCriticalZeroCount T := rfl

theorem mem_xiSimpleCriticalZeroFinset {T : ℝ} {z : ℂ} :
    z ∈ xiSimpleCriticalZeroFinset T ↔
      0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im ≤ T ∧ xi z = 0 ∧
        z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1 := by
  rw [xiSimpleCriticalZeroFinset, Finset.mem_filter, mem_stripFinsetPos]
  tauto

/-- Distinct simple critical Xi zeros have distinct ordinates. -/
theorem injOn_im_xiSimpleCriticalZeroFinset (T : ℝ) :
    Set.InjOn Complex.im (xiSimpleCriticalZeroFinset T : Set ℂ) := by
  intro z hz w hw hzw
  rcases mem_xiSimpleCriticalZeroFinset.mp hz with ⟨-, -, -, -, -, hzre, -⟩
  rcases mem_xiSimpleCriticalZeroFinset.mp hw with ⟨-, -, -, -, -, hwre, -⟩
  exact Complex.ext (by rw [hzre, hwre]) hzw

/-- Positive ordinates of the actual simple critical Xi zeros up to height `T`. -/
def xiSimpleCriticalOrdinateFinset (T : ℝ) : Finset ℝ :=
  (xiSimpleCriticalZeroFinset T).image Complex.im

@[simp] theorem card_xiSimpleCriticalOrdinateFinset (T : ℝ) :
    (xiSimpleCriticalOrdinateFinset T).card = xiSimpleCriticalZeroCount T := by
  rw [xiSimpleCriticalOrdinateFinset,
    Finset.card_image_iff.mpr (injOn_im_xiSimpleCriticalZeroFinset T)]
  rfl

theorem mem_xiSimpleCriticalOrdinateFinset {T t : ℝ} :
    t ∈ xiSimpleCriticalOrdinateFinset T ↔
      0 < t ∧ t ≤ T ∧ xi (linePt t) = 0 ∧
        (analyticOrderAt xi (linePt t)).toNat = 1 := by
  constructor
  · intro ht
    obtain ⟨z, hz, hzim⟩ := Finset.mem_image.mp ht
    rcases mem_xiSimpleCriticalZeroFinset.mp hz with
      ⟨-, -, hzimpos, hzimT, hxizero, hzre, hsimple⟩
    have hzline : z = linePt t := by
      apply Complex.ext
      · simpa [linePt] using hzre
      · simpa [linePt] using hzim
    rw [← hzline]
    exact ⟨by simpa [hzim] using hzimpos,
      by simpa [hzim] using hzimT, hxizero, hsimple⟩
  · rintro ⟨ht0, htT, hxi, hsimple⟩
    rw [xiSimpleCriticalOrdinateFinset, Finset.mem_image]
    refine ⟨linePt t, ?_, by simp [linePt]⟩
    rw [mem_xiSimpleCriticalZeroFinset]
    simpa [linePt] using
      (show (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧ 0 < t ∧ t ≤ T ∧
          xi (linePt t) = 0 ∧ (1 / 2 : ℝ) = 1 / 2 ∧
            (analyticOrderAt xi (linePt t)).toNat = 1 by
        exact ⟨by norm_num, by norm_num, ht0, htT, hxi, rfl, hsimple⟩)

/-- If an entire finite-exponential-type function annihilates all simple critical ordinates except
a fixed finite set, then the actual simple-critical-zero count has a linear envelope. -/
theorem exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hFne : F ≠ 0)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖))
    (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 → F (t : ℂ) = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 1 ≤ T →
      (xiSimpleCriticalZeroCount T : ℝ) ≤ K * (1 + T) + E.card := by
  have hanchor : ∃ c : ℂ, F c ≠ 0 := by
    by_contra h
    push Not at h
    exact hFne (funext h)
  obtain ⟨c, hFc⟩ := hanchor
  obtain ⟨K₀, hK₀, hlinear⟩ :=
    exponentialType_zeroCount_linear hF hFc hA hC hgrow
  let K : ℝ := K₀ * (1 + ‖c‖)
  have hK : 0 < K := mul_pos hK₀ (by positivity)
  refine ⟨K, hK, ?_⟩
  intro T hT
  let O : Finset ℝ := xiSimpleCriticalOrdinateFinset T
  let S : Finset ℝ := O \ E
  have hOS : O ⊆ S ∪ E := by
    intro t ht
    by_cases htE : t ∈ E
    · exact Finset.mem_union_right S htE
    · exact Finset.mem_union_left E (Finset.mem_sdiff.mpr ⟨ht, htE⟩)
  have hcardNat : O.card ≤ S.card + E.card :=
    (Finset.card_le_card hOS).trans (Finset.card_union_le S E)
  let r : ℝ := ‖c‖ + T
  have hr : 1 ≤ r := by
    dsimp only [r]
    linarith [norm_nonneg c]
  have hdivInt : (S.card : ℤ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor F (closedBall c r)) u := by
    apply card_le_sum_divisor_of_finite_zeros hF hFc S (fun t : ℝ => (t : ℂ))
    · intro t ht u hu htu
      exact Complex.ofReal_injective htu
    · intro t ht
      have htO : t ∈ O := (Finset.mem_sdiff.mp ht).1
      have htdata : 0 < t ∧ t ≤ T ∧ xi (linePt t) = 0 ∧
          (analyticOrderAt xi (linePt t)).toNat = 1 := by
        exact mem_xiSimpleCriticalOrdinateFinset.mp htO
      rw [mem_closedBall_iff_norm]
      calc
        ‖(t : ℂ) - c‖ ≤ ‖(t : ℂ)‖ + ‖c‖ := norm_sub_le _ _
        _ = t + ‖c‖ := by
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htdata.1]
        _ ≤ r := by dsimp only [r]; linarith
    · intro t ht
      have htdata := mem_xiSimpleCriticalOrdinateFinset.mp (Finset.mem_sdiff.mp ht).1
      exact hvanish t (Finset.mem_sdiff.mp ht).2 htdata.1 htdata.2.2.1 htdata.2.2.2
  have hdivReal : (S.card : ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor F (closedBall c r)) u) : ℝ) := by
    exact_mod_cast hdivInt
  have hSlinear : (S.card : ℝ) ≤ K₀ * (1 + r) :=
    hdivReal.trans (hlinear r hr)
  have hgeom : K₀ * (1 + r) ≤ K * (1 + T) := by
    have hbase : 1 + r ≤ (1 + ‖c‖) * (1 + T) := by
      dsimp only [r]
      nlinarith [norm_nonneg c]
    dsimp only [K]
    nlinarith [hK₀.le]
  have hcardReal : (O.card : ℝ) ≤ (S.card : ℝ) + E.card := by
    exact_mod_cast hcardNat
  have hOcount : O.card = xiSimpleCriticalZeroCount T := by
    exact card_xiSimpleCriticalOrdinateFinset T
  rw [← hOcount]
  linarith

/-- Paley--Wiener specialization for arbitrary compactly supported `L²` data. -/
theorem exists_xiSimpleCriticalZeroCount_linear_of_cofinite_suzukiFourier_zeros
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2)
    (hFne : suzukiCompactL2Fourier a f ≠ 0)
    (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        suzukiCompactL2Fourier a f (t : ℂ) = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 1 ≤ T →
      (xiSimpleCriticalZeroCount T : ℝ) ≤ K * (1 + T) + E.card := by
  obtain ⟨C, hC, hgrow⟩ := suzukiCompactL2Fourier_exponentialType ha f
  exact exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros
    (differentiable_suzukiCompactL2Fourier ha f) hFne ha hC hgrow E hvanish

/-- Identical vanishing of the compact Fourier transform forces the compact source to vanish. -/
theorem suzukiCutoff_eq_zero_of_compactFourier_eq_zero
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2)
    (hzero : suzukiCompactL2Fourier a f = 0) :
    suzukiCutoff a f = 0 := by
  apply suzukiCutoff_eq_zero_of_fourier_constant_on_xiZeros ha f (c := 0)
  intro z hz
  exact congrFun hzero z

end RHTower
