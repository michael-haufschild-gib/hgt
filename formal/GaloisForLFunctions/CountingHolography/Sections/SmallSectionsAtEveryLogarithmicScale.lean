import GaloisForLFunctions.CountingHolography.Sections.PrimeTraceWindows
import GaloisForLFunctions.CountingHolography.Sections.TheTotalDualHeightInPrimeWindows
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.UpperLogarithmicWindows

/-!
# Small rational sections at every large logarithmic scale

For every δ < 1, the number of effective prime pairs in every sufficiently
large logarithmic window exceeds any fixed multiple of exp(δT). The same
multiplicity tail works for all the selected primes in a window.
-/

noncomputable section

namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticScatteringHolography ArithmeticCastelnuovoSeveri
open ArithmeticOrientationGeometry RenormalizedIntersectionTheory SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open SquareRootThreshold Zeta23

private abbrev traceAt (u : ℝ) := 2*(lagStructure zetaZeroConfig (boxSpline 1 3) u).re

private theorem inner_radius (T : ℝ) :
    primeLogarithmicRadius T / 2 = 16 * Real.log (T+2) := by
  unfold primeLogarithmicRadius
  ring

/-- Below the zero width, every late window contains a positive peak. -/
private theorem peaks_at_every_scale {a : ℝ} (ha : 0 ≤ a) (haw : a < zetaZeroWidth) (B : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∃ u : ℝ, |u-T| ≤ primeLogarithmicRadius T / 2 ∧
      B*Real.exp (a*u) < traceAt u := by
  rw [eventually_atTop]
  by_contra! hn
  apply haw.not_ge
  apply (zetaZeroWidth_le_iff_re_le ha).mpr
  apply zeta_re_le_of_upper_logarithmic_windows (K := B) ha
  intro U
  obtain ⟨T,hT,hbound⟩ := hn U
  exact ⟨T,hT,fun u hu => hbound u (by rwa [inner_radius])⟩

/-- After deleting a power-saving number of primes, each point of the
inner half-window still has a nearby prime in the outer window. -/
private theorem near_surviving_prime {δ γ β C : ℝ} (hγ : 0 < γ) (hδγ : δ < γ)
    (hγβ : γ < β) (hβ : 7/12 < β) (hβ1 : β < 1) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, |u-T| ≤ primeLogarithmicRadius T / 2 →
      ∀ E : Finset ℕ, (E.card : ℝ) ≤ C*Real.exp (δ*T) →
        ∃ p : ℕ, p.Prime ∧ p ∉ E ∧ |Real.log p-T| ≤ primeLogarithmicRadius T ∧
          0 ≤ Real.log p ∧ Real.log p ≤ u ∧ u - Real.log p ≤ 2*Real.exp ((β-1)*u) := by
  obtain ⟨U,_,hnear⟩ := exists_log_prime_avoiding_small_finset hγ.le hγβ hβ hβ1 hC
  have hlim : Tendsto (fun u : ℝ => 2*Real.exp ((β-1)*u)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hβ1))
    simpa only [Function.comp_def, id_eq, mul_zero] using h.const_mul 2
  obtain ⟨V,hV⟩ := eventually_atTop.mp (hlim.eventually_le_const zero_lt_one)
  filter_upwards [eventually_ge_atTop (2*max U V), primeLogarithmicRadius_exception_margin hδγ]
    with T hlarge hshape
  intro u hu E hE
  obtain ⟨hR,hRT,hmargin⟩ := hshape
  have hlu := (abs_le.mp hu).1
  have huv : max U V ≤ u := by linarith only [hlu,hRT,hlarge]
  have hsmall := hV u ((le_max_right _ _).trans huv)
  have hcard : (E.card : ℝ) ≤ C*Real.exp (γ*u) := by
    apply hE.trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.exp_le_exp.mpr (hmargin.trans (mul_le_mul_of_nonneg_left (by linarith only [hlu]) hγ.le))
  obtain ⟨p,hp,hout,hs,hsu,hgap⟩ := hnear u ((le_max_left _ _).trans huv) E hcard
  refine ⟨p,hp,hout,?_,hs,hsu,hgap⟩
  have htri : |Real.log p-T| ≤ |u-T| + |u-Real.log p| := by
    calc _ = |(u-T) - (u-Real.log p)| := by congr 1; ring
         _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_sub_le (u-T) (u-Real.log p)
  rw [abs_of_nonneg (sub_nonneg.mpr hsu)] at htri
  linarith only [htri,hu,hgap,hsmall,hR]

/-- The loss in moving a peak to a surviving prime is controlled at the
actual zero width, whether or not any zero attains that width. -/
private theorem trace_loss {a β : ℝ} (hle : zetaZeroWidth + β - 1 ≤ a) :
    ∃ L : ℝ, ∀ u v : ℝ, 0 ≤ v → v ≤ u → u-v ≤ 2*Real.exp ((β-1)*u) →
      |traceAt u - traceAt v| ≤ L * Real.exp (a*u) := by
  let D := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ * ‖z‖
  have hd : 0 ≤ D := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨4*D,fun u v hv hvu hgap => ?_⟩
  have hw := zetaZeroWidth_nonneg
  have h := abs_two_re_lagStructure_sub_le_of_width temperedConfig_zetaZeroConfig hw
    ((zetaZeroWidth_le_iff_re_le hw).mp le_rfl) hv hvu
  calc
    _ ≤ 2*D*(u-v)*Real.exp (zetaZeroWidth*u) := h
    _ ≤ 2*D*(2*Real.exp ((β-1)*u))*Real.exp (zetaZeroWidth*u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by positivity)) (Real.exp_pos _).le
    _ = 4*D*Real.exp ((zetaZeroWidth+β-1)*u) := by
      rw [show (zetaZeroWidth+β-1)*u = (β-1)*u + zetaZeroWidth*u by ring, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle (hv.trans hvu))) (by positivity)

private theorem positive_primes_escape {δ C : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ E : Finset ℕ, (E.card : ℝ) ≤ C*Real.exp (δ*T) →
      ∃ p ∈ primeWindow T, p ∉ E ∧ 0 < integerProbe (p+1) (primePair p) := by
  let γ := (δ+1)/2
  let β := max ((γ+1)/2) (2/3)
  have hδγ : δ < γ := by dsimp [γ]; linarith only [hδ1]
  have hγ := hδ.trans_lt hδγ
  have hγ1 : γ < 1 := by dsimp [γ]; linarith only [hδ1]
  have hγβ : γ < β := lt_of_lt_of_le (by linarith only [hγ1] : γ < (γ+1)/2) (le_max_left _ _)
  have hβ : 7/12 < β := lt_of_lt_of_le (by norm_num : (7:ℝ)/12 < 2/3) (le_max_right _ _)
  have hβ1 : β < 1 := max_lt (by linarith only [hγ1]) (by norm_num)
  have hnear := near_surviving_prime hγ hδγ hγβ hβ hβ1 hC
  by_cases hRH : RiemannHypothesis
  · filter_upwards [hnear,primeLogarithmicRadius_shape] with T hn hshape
    intro E hE
    obtain ⟨p,hp,hout,hwin,_⟩ := hn T (by rw [sub_self,abs_zero]; linarith only [hshape.1]) E hE
    refine ⟨p,mem_primeWindow.mpr ⟨hp,hwin⟩,hout,integerProbe_pos_of_rh hRH ?_⟩
    intro hz
    have hh := congrFun hz 0
    simp only [primePair, Pi.add_apply, Pi.single_apply, Pi.zero_apply, if_true] at hh
    split_ifs at hh <;> omega
  have hw := lt_of_le_of_ne zetaZeroWidth_nonneg
    (Ne.symm (fun hz => hRH (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr hz)))
  let a := max 0 (zetaZeroWidth+β-1)
  have ha : 0 ≤ a := le_max_left _ _
  have haw : a < zetaZeroWidth := max_lt hw (by linarith only [hβ1])
  obtain ⟨L,hloss⟩ := trace_loss (le_max_right 0 (zetaZeroWidth+β-1))
  let s := 2*(splineSeries 0).re
  filter_upwards [hnear,peaks_at_every_scale ha haw (|s| + L)] with T hn hpk
  obtain ⟨u,hu,hpeak⟩ := hpk
  intro E hE
  obtain ⟨p,hp,hout,hwin,hv,hvu,hgap⟩ := hn u hu E hE
  refine ⟨p,mem_primeWindow.mpr ⟨hp,hwin⟩,hout,?_⟩
  have he : 1 ≤ Real.exp (a*u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg ha (hv.trans hvu))
  have hdiag := le_mul_of_one_le_right (abs_nonneg s) he
  have hvar := (abs_le.mp (hloss u (Real.log p) hv hvu hgap)).2
  rw [integerProbe_primePair hp.pos, ← orbitCorr_splineCycle_eq (Real.log p),
    orbitCorr_eq_re_lagStructure_spline]
  change 0 < s + traceAt (Real.log p)
  change traceAt u - traceAt (Real.log p) ≤ L*Real.exp (a*u) at hvar
  linarith only [hdiag,neg_le_abs s,hvar,hpeak]

/-- At every sufficiently large logarithmic scale the number of prime
pairs fitting the original radius, at every sufficiently large common
multiplicity, exceeds any fixed multiple of `exp(δT)` for `δ < 1`. -/
theorem eventually_many_prime_moduli_fit_at_every_scale {δ C : ℝ} (hδ1 : δ < 1)
    (hC : 0 ≤ C) : ∀ᶠ T : ℝ in atTop, ∃ S : Finset ℕ, S ⊆ primeWindow T ∧
      C*Real.exp (δ*T) < S.card ∧ ∀ᶠ m : ℕ in atTop, ∀ p ∈ S,
        Real.log (contactModulus (m • primePair p)) < radius (m • primePair p) := by
  classical
  have hmax : max 0 δ < 1 := max_lt zero_lt_one hδ1
  filter_upwards [positive_primes_escape (le_max_left 0 δ) hmax hC, eventually_ge_atTop (0 : ℝ)] with T hesc hT
  let S := (primeWindow T).filter (fun p : ℕ => 0 < integerProbe (p+1) (primePair p))
  refine ⟨S,filter_subset _ _,?_,?_⟩
  · by_contra! hs
    have hbound := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right 0 δ) hT)) hC
    obtain ⟨p,hp,hout,hpos⟩ := hesc S (hs.trans hbound)
    exact hout (mem_filter.mpr ⟨hp,hpos⟩)
  apply (Finset.eventually_all S).mpr
  intro p hp
  have hpos : 0 < integerProbe (p+1) (primePair p) := (mem_filter.mp hp).2
  apply (eventually_log_generator_lt_radius (a := primePair p) hpos).mono
  intro m hm
  have hn (i : Fin (p+1)) : 0 ≤ (m • primePair p) i := by
    simp only [primePair, Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Pi.single_apply]
    split_ifs <;> positivity
  have he : (generator (m • primePair p) : ℝ) = contactModulus (m • primePair p) := by
    exact_mod_cast generator_eq_contactModulus _ hn
  rwa [he] at hm

#print axioms eventually_many_prime_moduli_fit_at_every_scale

end GaloisForLFunctions.CountingHolography.Sections
