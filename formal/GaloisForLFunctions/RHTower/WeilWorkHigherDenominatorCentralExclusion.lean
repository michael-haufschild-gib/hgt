import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCentralTest
import GaloisForLFunctions.RHTower.WeilZetaPowerForward

/-!
# Central nonvanishing and positive sign for degree-three Weil data

The exact degree-three correspondence turns every completion zero into a spectral atom of mass
at least `1/3`. The universal central atom bound is strictly below `1/4`; hence the completion
cannot vanish at `1/2`. Its functional equation therefore has positive sign.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section

namespace RHTower.WeilHigherDenominator

open WeilZetaPower WeilSpectral

private theorem exists_copy_of_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : F 0 ≠ 0) {z : ℂ} (hz : F z = 0) :
    ∃ q : ZeroCopy F, zeroCopyPoint F q = z := by
  have ha : AnalyticOnNhd ℂ F univ := fun w _ => hF.analyticAt w
  have htop : analyticOrderAt F z ≠ ⊤ :=
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ z)
      (by rw [(hF.analyticAt 0).analyticOrderAt_eq_zero.mpr hF0]; exact ENat.zero_ne_top)
  have hnz : analyticOrderAt F z ≠ 0 := (hF.analyticAt z).analyticOrderAt_ne_zero.mpr hz
  have hpos : 0 < (MeromorphicOn.divisor F univ) z := by
    rw [MeromorphicOn.divisor_apply (fun w _ => (hF.analyticAt w).meromorphicAt)
      (mem_univ z), (hF.analyticAt z).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hn] at hnz ⊢
    have hn0 : n ≠ 0 := by rintro rfl; exact hnz rfl
    rw [ENat.map_coe, WithTop.untop₀_coe]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  exact ⟨⟨⟨z, hpos.ne'⟩, ⟨0, Int.lt_toNat.mpr (by simpa using hpos)⟩⟩, rfl⟩

/-- Every degree-three datum satisfying the full Weil correspondence is nonzero at the center. -/
theorem degreeThree_central_ne_zero {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : ZetaPowerDatum 3 g E) (hRH : ∀ s, E s = 0 → s.re = 1 / 2)
    {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s) :
    E (1 / 2) ≠ 0 := by
  intro hzero
  have hE2 : E 2 ≠ 0 := fun h => by have := hRH 2 h; norm_num at this
  have hF : Differentiable ℂ (fun z => E (z + 2)) :=
    hD.entire.comp (differentiable_id.add_const 2)
  obtain ⟨q, hq⟩ := exists_copy_of_zero hF (by simpa using hE2)
    (z := -(3 / 2)) (by convert hzero using 1 <;> norm_num)
  have hqim : (zeroCopyPoint (fun z => E (z + 2)) q + 2).im = 0 := by rw [hq]; norm_num
  let hW : WeilPositiveFull lam := weilPositiveFull_of_zetaPowerDatum (by norm_num) hD hRH hsl hΛ
  have hlower : (1 / 3 : ℝ≥0∞) ≤ boundaryMeasure hW {0} := by
    rw [boundaryMeasure_eq_zeroMeasure (by norm_num) hD hRH hsl hΛ]
    have h := Measure.le_sum (fun p : ZeroCopy (fun z => E (z + 2)) =>
      ENNReal.ofReal (1 / 3) • Measure.dirac
        (zeroCopyPoint (fun z => E (z + 2)) p + 2).im) q
    have hs := h ({0} : Set ℝ)
    rw [Measure.smul_apply, hqim, Measure.dirac_apply' _ (measurableSet_singleton 0)] at hs
    have hthird : ENNReal.ofReal (1 / 3 : ℝ) = (3 : ℝ≥0∞)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < 3 by norm_num),
        ENNReal.ofReal_ofNat]
    rw [hthird] at hs
    norm_num [smul_eq_mul] at hs ⊢
    simpa only [hthird] using hs
  have hbad := hlower.trans_lt (boundaryMeasure_zero_lt_quarter hW)
  norm_num at hbad

/-- The negative functional-equation sign is excluded by the complete degree-three datum. -/
theorem degreeThree_functional_equation {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : ZetaPowerDatum 3 g E) (hRH : ∀ s, E s = 0 → s.re = 1 / 2)
    {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s) :
    ∀ s, E (1 - s) = E s := by
  rcases hD.functional_equation with h | h
  · exact h
  · have hn := degreeThree_central_ne_zero hD hRH hsl hΛ
    have hc := h (1 / 2)
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring] at hc
    exact (hn (by linear_combination hc / 2)).elim

end RHTower.WeilHigherDenominator
