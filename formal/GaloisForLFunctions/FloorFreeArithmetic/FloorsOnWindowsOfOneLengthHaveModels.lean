import GaloisForLFunctions.FloorFreeArithmetic.TheFloorOfAMechanism
import GaloisForLFunctions.FloorFreeArithmetic.MomentsOnWindowsAmplifyTheDepth

/-!
# Floors on windows of one length have models

A one-sided floor on arbitrarily late windows of a single fixed length `L` is not a receiver for
the abscissa law: a top layer with one slow ordinate keeps its trace positive on a window of
length `L` in every period. The model is the isolated pair at the ordinate `γ₀ = 2π/(3L)`: its
top trace is `2|e| cos(γ₀ u + φ)`, at least `|e|` on a window of length `L` in each period.

This is the difference between the two forms of non-attainment. Two-sided smallness on windows
of one length excludes every finite top layer; one-sided floors exclude it only on the family of
all lengths.

* `WindowFloor L`: the mechanism "floors on arbitrarily late windows of length `L`".
* `topTrace_isolatedPair`: the top trace of the isolated pair is a single cosine.
* `hasFiniteStratumModel_windowFloor`: every `WindowFloor L` admits a finite stratum.
* `not_forall_abscissaLaw_of_windowFloor`: it does not force the abscissa law.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-- The mechanism "floors on arbitrarily late windows of length `L`": the spline trace of a
tempered configuration is bounded below on a window `[T, T + L]` beyond every point. -/
def WindowFloor (L : ℝ) : Mechanism := fun Z =>
  TemperedConfig Z ∧ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u ∈ Icc T (T + L),
    -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re

section IsolatedPair

variable {δ γ₀ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)

/-- An active exponent of real part `δ` of the isolated pair is `δ ± iγ₀`. -/
theorem isolatedPair_active_top {z : ℂ}
    (hz : evenCoeff (isolatedPairConfig one_pos hδ hδ' γ₀) (boxSpline 1 3) z ≠ 0)
    (hre : z.re = δ) : z = ⟨δ, γ₀⟩ ∨ z = ⟨δ, -γ₀⟩ := by
  have key : ∀ w : ℂ, w.re = δ → (1 / 2 + w) ∈ (isolatedPairConfig one_pos hδ hδ' γ₀).carrier →
      w.im = γ₀ := by
    intro w hw hmem
    have he : ((1 / 2 : ℂ) + w).re = 1 / 2 + w.re := by norm_num
    have him : ((1 / 2 : ℂ) + w).im = w.im := by norm_num
    have hm : (1 / 2 + w) ∈ rightOf (isolatedPairConfig one_pos hδ hδ' γ₀) 0 :=
      ⟨hmem, by rw [he, hw]; linarith only [hδ]⟩
    rw [rightOf_isolatedPairConfig] at hm
    have h1 := congrArg Complex.im (Set.mem_singleton_iff.mp hm)
    rw [him] at h1
    exact h1
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · exact Or.inl (Complex.ext hre (key z hre h))
  · have h1 := key (conj z) (by simpa using hre) h
    refine Or.inr (Complex.ext hre ?_)
    simp only [Complex.conj_im] at h1
    show z.im = -γ₀
    linarith only [h1]

/-- The isolated pair has depth `δ`. -/
theorem topDepth_isolatedPair : TopDepth (isolatedPairConfig one_pos hδ hδ' γ₀) δ := by
  have hle : ∀ ρ ∈ (isolatedPairConfig one_pos hδ hδ' γ₀).carrier, ρ.re ≤ 1 / 2 + δ := by
    intro ρ hρ
    by_cases h : 1 / 2 + 0 < ρ.re
    · have hm : ρ ∈ rightOf (isolatedPairConfig one_pos hδ hδ' γ₀) 0 := ⟨hρ, h⟩
      rw [rightOf_isolatedPairConfig] at hm
      rw [Set.mem_singleton_iff.mp hm]
      exact le_of_eq rfl
    · linarith only [not_lt.mp h, hδ]
  intro z hz
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · have h1 := hle _ h
    have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
    rw [he] at h1
    linarith only [h1]
  · have h1 := hle _ h
    have he : ((1 / 2 : ℂ) + conj z).re = 1 / 2 + z.re := by simp
    rw [he] at h1
    linarith only [h1]

/-- The spline sees the off-line point of the isolated pair. -/
theorem evenCoeff_isolatedPair_ne_zero :
    evenCoeff (isolatedPairConfig one_pos hδ hδ' γ₀) (boxSpline 1 3) ⟨δ, γ₀⟩ ≠ 0 := by
  have hmem : offLinePoint δ γ₀ ∈ (isolatedPairConfig one_pos hδ hδ' γ₀).carrier :=
    Or.inl (Or.inr rfl)
  have hre : 1 / 2 < (offLinePoint δ γ₀).re := by
    show 1 / 2 < 1 / 2 + δ
    linarith only [hδ]
  have hsee := evenCoeff_sub_half_ne_zero_of_conj_symm
    (isolatedPairConfig one_pos hδ hδ' γ₀) (contDiff_boxSpline one_pos 2).continuous
    (hasCompactSupport_of_support_subset_abs (boxSpline_support one_pos 3))
    (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hmem
    (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith only [hre])))
  have hpt : offLinePoint δ γ₀ - 1 / 2 = (⟨δ, γ₀⟩ : ℂ) := by
    apply Complex.ext
    · show (offLinePoint δ γ₀ - 1 / 2).re = δ
      have h : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
      rw [Complex.sub_re, h]
      show 1 / 2 + δ - 1 / 2 = δ
      ring
    · show (offLinePoint δ γ₀ - 1 / 2).im = γ₀
      have h : ((1 : ℂ) / 2).im = 0 := by norm_num
      rw [Complex.sub_im, h, sub_zero]
      rfl
  rwa [hpt] at hsee

variable (hγ : 0 < γ₀)
include hγ

/-- The positive top support of the isolated pair is the one point `δ + iγ₀`. -/
theorem mem_singleton_iff_positiveTopSupport_isolatedPair (z : ℂ) :
    z ∈ ({(⟨δ, γ₀⟩ : ℂ)} : Finset ℂ) ↔
      z ∈ positiveTopSupport (isolatedPairConfig one_pos hδ hδ' γ₀) δ := by
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨rfl, hγ, evenCoeff_isolatedPair_ne_zero hδ hδ'⟩
  · rintro ⟨hre, him, he⟩
    rcases isolatedPair_active_top hδ hδ' he hre with h | h
    · exact h
    · rw [h] at him
      have him' : (0 : ℝ) < -γ₀ := him
      linarith only [him', hγ]

/-- The active exponents on the top line of the isolated pair are not real. -/
theorem isolatedPair_top_im_ne_zero (z : ℂ)
    (hz : evenCoeff (isolatedPairConfig one_pos hδ hδ' γ₀) (boxSpline 1 3) z ≠ 0)
    (hre : z.re = δ) : z.im ≠ 0 := by
  rcases isolatedPair_active_top hδ hδ' hz hre with h | h
  · rw [h]
    exact hγ.ne'
  · rw [h]
    show -γ₀ ≠ 0
    exact neg_ne_zero.mpr hγ.ne'

/-- **The top trace of the isolated pair is one cosine**: `2|e| cos(γ₀ u + arg e)`, with `e` the
spline coefficient of the off-line point. -/
theorem topTrace_isolatedPair (u : ℝ) :
    topTrace (isolatedPairConfig one_pos hδ hδ' γ₀) δ u =
      2 * ‖evenCoeff (isolatedPairConfig one_pos hδ hδ' γ₀) (boxSpline 1 3) ⟨δ, γ₀⟩‖ *
        Real.cos (γ₀ * u +
          (evenCoeff (isolatedPairConfig one_pos hδ hδ' γ₀) (boxSpline 1 3) ⟨δ, γ₀⟩).arg) := by
  rw [topTrace_eq_positive_sum {(⟨δ, γ₀⟩ : ℂ)}
    (mem_singleton_iff_positiveTopSupport_isolatedPair hδ hδ' hγ)
    (isolatedPair_top_im_ne_zero hδ hδ' hγ) u, Finset.sum_singleton]
  set e := evenCoeff (isolatedPairConfig one_pos hδ hδ' γ₀) (boxSpline 1 3) ⟨δ, γ₀⟩ with he
  have hpolar : (‖e‖ : ℂ) * cexp ((e.arg : ℂ) * I) = e := Complex.norm_mul_exp_arg_mul_I e
  have hprod : (2 * e) * cexp (((γ₀ * u : ℝ) : ℂ) * I) =
      ((2 * ‖e‖ : ℝ) : ℂ) * cexp (((γ₀ * u + e.arg : ℝ) : ℂ) * I) := by
    have hexp : cexp (((γ₀ * u + e.arg : ℝ) : ℂ) * I) =
        cexp ((e.arg : ℂ) * I) * cexp (((γ₀ * u : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    conv_lhs => rw [← hpolar]
    push_cast
    ring
  show ((2 * e) * cexp ((((⟨δ, γ₀⟩ : ℂ).im * u : ℝ) : ℂ) * I)).re = _
  rw [show ((⟨δ, γ₀⟩ : ℂ).im * u : ℝ) = γ₀ * u from rfl, hprod, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

end IsolatedPair

/-- The cosine is at least `½` within `π/3` of a multiple of `2π`. -/
theorem half_le_cos_of_abs_sub_le {x : ℝ} {n : ℕ} (h : |x - n * (2 * Real.pi)| ≤ Real.pi / 3) :
    1 / 2 ≤ Real.cos x := by
  have hx : x = (x - n * (2 * Real.pi)) + n * (2 * Real.pi) := by ring
  rw [hx, Real.cos_add_nat_mul_two_pi, ← Real.cos_abs, ← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    (by linarith only [Real.pi_pos]) h

/-- **Floors on windows of one length admit a finite stratum.** For every `L > 0` the isolated
pair of depth `¼` at the ordinate `2π/(3L)` has a nonnegative spline trace on arbitrarily late
windows of length `L`. -/
theorem hasFiniteStratumModel_windowFloor {L : ℝ} (hL : 0 < L) :
    HasFiniteStratumModel (WindowFloor L) := by
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have hδ' : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hπ := Real.pi_pos
  set γ₀ : ℝ := 2 * Real.pi / (3 * L) with hγ₀
  have hγ : 0 < γ₀ := by positivity
  have hγL : γ₀ * L = 2 * Real.pi / 3 := by
    rw [hγ₀, div_mul_eq_mul_div, mul_div_mul_right _ _ hL.ne']
  have hZ := temperedConfig_isolatedPairConfig one_pos hδ hδ' γ₀
  set e := evenCoeff (isolatedPairConfig one_pos hδ hδ' γ₀) (boxSpline 1 3) ⟨1 / 4, γ₀⟩ with he
  have he0 : 0 < ‖e‖ := norm_pos_iff.mpr (evenCoeff_isolatedPair_ne_zero hδ hδ')
  have hrem := tendsto_normTrace_sub_topTrace hZ (topDepth_isolatedPair hδ hδ' (γ₀ := γ₀))
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    ((tendsto_order.mp hrem).1 (-(‖e‖ / 2)) (by linarith only [he0]))
  refine ⟨isolatedPairConfig one_pos hδ hδ' γ₀, ⟨hZ, 0, fun U => ?_⟩, ?_, ?_⟩
  · -- a window of length `L` on which the cosine is at least `½`, beyond `U` and `V`
    obtain ⟨n, hn⟩ := exists_nat_gt ((max U V * γ₀ + Real.pi / 3 + e.arg) / (2 * Real.pi))
    have hn' := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hn
    set T : ℝ := ((n : ℝ) * (2 * Real.pi) - Real.pi / 3 - e.arg) / γ₀ with hT
    have hTγ : γ₀ * T = (n : ℝ) * (2 * Real.pi) - Real.pi / 3 - e.arg := by
      rw [hT, mul_div_cancel₀ _ hγ.ne']
    have hTge : max U V ≤ T := by
      rw [hT, le_div_iff₀ hγ]
      linarith only [hn']
    refine ⟨T, (le_max_left U V).trans hTge, fun u hu => ?_⟩
    have h1 : γ₀ * T ≤ γ₀ * u := mul_le_mul_of_nonneg_left hu.1 hγ.le
    have h2 : γ₀ * u ≤ γ₀ * T + γ₀ * L := by
      have := mul_le_mul_of_nonneg_left hu.2 hγ.le
      linarith only [this, mul_add γ₀ T L]
    have hcos : 1 / 2 ≤ Real.cos (γ₀ * u + e.arg) :=
      half_le_cos_of_abs_sub_le (n := n)
        (abs_le.mpr ⟨by linarith only [h1, hTγ], by linarith only [h2, hTγ, hγL]⟩)
    have htt : topTrace (isolatedPairConfig one_pos hδ hδ' γ₀) (1 / 4) u =
        2 * ‖e‖ * Real.cos (γ₀ * u + e.arg) := topTrace_isolatedPair hδ hδ' hγ u
    have htop : ‖e‖ ≤ topTrace (isolatedPairConfig one_pos hδ hδ' γ₀) (1 / 4) u := by
      rw [htt]
      nlinarith only [hcos, he0]
    have hlo := hV u (((le_max_right U V).trans hTge).trans hu.1)
    have hnorm : 0 ≤ normTrace (isolatedPairConfig one_pos hδ hδ' γ₀) (1 / 4) u := by
      linarith only [htop, hlo, he0]
    rw [two_re_lagStructure_eq_normTrace_mul _ (1 / 4) u, neg_zero]
    exact mul_nonneg hnorm (Real.exp_pos _).le
  · rw [rightOf_isolatedPairConfig]
    exact Set.finite_singleton _
  · rw [rightOf_isolatedPairConfig]
    exact Set.singleton_nonempty _

/-- **A floor on windows of one length does not give the abscissa law.** -/
theorem not_forall_abscissaLaw_of_windowFloor {L : ℝ} (hL : 0 < L) :
    ¬ ∀ Z : ZeroConfig, WindowFloor L Z → AbscissaLaw Z :=
  not_forall_abscissaLaw_of_hasFiniteStratumModel (hasFiniteStratumModel_windowFloor hL)

end GaloisForLFunctions.FloorFreeArithmetic
