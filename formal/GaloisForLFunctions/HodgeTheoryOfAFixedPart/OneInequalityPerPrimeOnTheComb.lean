import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ExceptionalLogarithmicWindows
import GaloisForLFunctions.SquareRootThreshold.EvenAndOddTwoBumpTestsDecideTheCriticalLine

/-!
# One inequality per prime on the comb

The Riemann hypothesis is one inequality per prime, on arbitrarily late logarithmic windows, off
power-thin exceptional sets of primes. This file states it for the pairing of the normal form.

Let `B` be the cubic spline and `D_v` the two-bump divisor of the lag `v`: the samples of
`B(u − a) + B(u − a − v)`, the spline and its translate by `v`. For `v = log p` it is the class
`Γ_1 + Γ_p` of the diagonal and the graph of `F_p`, smeared by the spline.

* **Weil's form of the two-bump divisor** (`tendsto_combForm_twoBumpPacket`): it tends to
  `2 Re S(0) + 2 Re S(v)`, with `S` the lag structure of the spline on the zeros; `Re S(0)` is
  the limit for the spline alone, and `2 Re S(v)` the limit of twice the form of the spline and
  its translate.
* **Locality in scale with exceptions** (`riemannHypothesis_iff_twoBump_windows_off_finset`): for
  `0 ≤ δ < 1` the Riemann hypothesis holds iff there are `K` and `C` such that on arbitrarily
  late logarithmic windows `|log p − T| ≤ 32 log(T + 2)`, outside at most `C e^{δT}` primes of
  the window, the limit of Weil's form of `D_{log p}` is at least `2 Re S(0) − K`: the pairing of
  the spline divisor with its image under `F_p` exceeds its pole term by at most `K/2`.
-/

open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.SquareRootThreshold Zeta23
open scoped ComplexConjugate ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ SurfaceOfSpecZ.ScaleLocality

/-! ### The spline -/

/-- The cubic spline as a real function. -/
def spline (u : ℝ) : ℝ := (boxSpline 1 3 u).re

theorem ofReal_spline (u : ℝ) : ((spline u : ℝ) : ℂ) = boxSpline 1 3 u := by
  simp [spline, boxSpline]

theorem contDiff_boxSpline_three : ContDiff ℝ 2 (boxSpline 1 3) := by
  exact_mod_cast contDiff_boxSpline one_pos 2

theorem contDiff_spline : ContDiff ℝ 2 spline :=
  Complex.reCLM.contDiff.comp contDiff_boxSpline_three

theorem spline_eq_zero {u : ℝ} (h : 4 < |u|) : spline u = 0 := by
  by_contra h0
  have hb := boxSpline_support one_pos 3 u fun hb => h0 (by rw [spline, hb, Complex.zero_re])
  norm_num at hb
  linarith

theorem hasCompactSupport_spline : HasCompactSupport spline :=
  HasCompactSupport.intro (isCompact_Icc (a := (-4 : ℝ)) (b := 4)) fun u hu => by
    refine spline_eq_zero ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact h

/-! ### The two-bump packet -/

/-- The spline at `5 + log 3` and its translate by `v`. -/
def twoBumpPacket (v : ℝ) (u : ℝ) : ℝ :=
  spline (u - (5 + Real.log 3)) + spline (u - (5 + Real.log 3 + v))

/-- The ratio of a window that contains the two-bump packet of the lag `v`. -/
def twoBumpWindow (v : ℝ) : ℕ := ⌈Real.exp (10 + Real.log 3 + v)⌉₊

theorem one_le_twoBumpWindow (v : ℝ) : 1 ≤ twoBumpWindow v :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem contDiff_twoBumpPacket (v : ℝ) : ContDiff ℝ 2 (twoBumpPacket v) :=
  (contDiff_spline.comp (contDiff_id.sub contDiff_const)).add
    (contDiff_spline.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_twoBumpPacket (v : ℝ) : HasCompactSupport (twoBumpPacket v) :=
  (hasCompactSupport_spline.comp_homeomorph (Homeomorph.subRight (5 + Real.log 3))).add
    (hasCompactSupport_spline.comp_homeomorph (Homeomorph.subRight (5 + Real.log 3 + v)))

theorem twoBumpPacket_eq_zero {v : ℝ} (hv : 0 ≤ v) :
    ∀ u, u ≤ Real.log 3 ∨ Real.log (twoBumpWindow v) ≤ u → twoBumpPacket v u = 0 := by
  have hK : 10 + Real.log 3 + v ≤ Real.log (twoBumpWindow v) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast one_le_twoBumpWindow v)]
    exact Nat.le_ceil _
  rintro u (hu | hu)
  · rw [twoBumpPacket, spline_eq_zero, spline_eq_zero, add_zero]
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_neg (by linarith)]
      linarith
  · rw [twoBumpPacket, spline_eq_zero, spline_eq_zero, add_zero]
    · rw [abs_of_pos (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith

/-! ### The sum over the zeros of the two-bump packet -/

/-- The sum over the zeros does not change under a translation of the packet. -/
theorem zeroSum_translate_packet {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (s : ℝ) : zeroSum (fun u => f (u - s)) = zeroSum f := by
  have hg : ContDiff ℝ 2 fun u => f (u - s) := hf.comp (contDiff_id.sub contDiff_const)
  have hgc : HasCompactSupport fun u => f (u - s) :=
    hfc.comp_homeomorph (Homeomorph.subRight s)
  rw [zeroSum_eq_weilFullFunctional hg hgc, zeroSum_eq_weilFullFunctional hf hfc]
  exact congrArg (fun k => (_root_.RHTower.weilFullFunctional (fun n => (Λ n : ℝ)) k).re)
    (weilTest_packet_translate f s)

/-- The two-bump packet centred at the origin. -/
def centredTwoBump (v : ℝ) (t : ℝ) : ℝ :=
  spline (t - lagPoint 2 v 0) + spline (t - lagPoint 2 v 1)

theorem lagPoint_two_zero (v : ℝ) : lagPoint 2 v 0 = -(v / 2) := by
  simp only [lagPoint, Fin.val_zero, Nat.cast_zero, Nat.cast_ofNat]
  ring

theorem lagPoint_two_one (v : ℝ) : lagPoint 2 v 1 = v / 2 := by
  simp only [lagPoint, Fin.val_one, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem twoBumpPacket_eq_translate (v : ℝ) :
    twoBumpPacket v = fun u => centredTwoBump v (u - (5 + Real.log 3 + v / 2)) := by
  funext u
  rw [twoBumpPacket, centredTwoBump, lagPoint_two_zero, lagPoint_two_one]
  congr 2 <;> ring

theorem ofReal_centredTwoBump (v : ℝ) :
    (fun t => ((centredTwoBump v t : ℝ) : ℂ)) = twoBump (boxSpline 1 3) v 1 := by
  funext t
  rw [twoBump, bumpTest, Fin.sum_univ_two, centredTwoBump]
  push_cast
  rw [ofReal_spline, ofReal_spline]
  simp

/-- **The sum over the zeros of the two-bump packet**: `2 Re S(0) + 2 Re S(v)`. -/
theorem zeroSum_twoBumpPacket (v : ℝ) :
    zeroSum (twoBumpPacket v) = 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re +
      2 * (lagStructure zetaZeroConfig (boxSpline 1 3) v).re := by
  have hZ := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have hβs := boxSpline_support one_pos 3
  have hc : ContDiff ℝ 2 (centredTwoBump v) :=
    (contDiff_spline.comp (contDiff_id.sub contDiff_const)).add
      (contDiff_spline.comp (contDiff_id.sub contDiff_const))
  have hcc : HasCompactSupport (centredTwoBump v) :=
    (hasCompactSupport_spline.comp_homeomorph (Homeomorph.subRight (lagPoint 2 v 0))).add
      (hasCompactSupport_spline.comp_homeomorph (Homeomorph.subRight (lagPoint 2 v 1)))
  have hW := W_twoBump zetaZeroConfig hZ contDiff_boxSpline_three hβs v 1
  have hconj := conj_lagStructure_neg zetaZeroConfig hZ contDiff_boxSpline_three hβs v
  have hre : (lagStructure zetaZeroConfig (boxSpline 1 3) (-v)).re =
      (lagStructure zetaZeroConfig (boxSpline 1 3) v).re := by
    rw [← hconj, Complex.conj_re]
  have hW' : zetaZeroConfig.W (twoBump (boxSpline 1 3) v 1) (twoBump (boxSpline 1 3) v 1) =
      ((2 : ℝ) : ℂ) * lagStructure zetaZeroConfig (boxSpline 1 3) 0 +
        (lagStructure zetaZeroConfig (boxSpline 1 3) v +
          lagStructure zetaZeroConfig (boxSpline 1 3) (-v)) := by
    rw [hW, norm_one, Complex.ofReal_one, one_pow, map_one, one_mul, one_mul]
    push_cast
    ring
  rw [twoBumpPacket_eq_translate, zeroSum_translate_packet hc hcc, zeroSum,
    ofReal_centredTwoBump, hW', Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, hre]
  ring

/-! ### Weil's form of the two-bump divisor -/

/-- **Weil's form of the two-bump divisor** tends to `2 Re S(0) + 2 Re S(v)`. -/
theorem tendsto_combForm_twoBumpPacket {v : ℝ} (hv : 0 ≤ v) :
    Tendsto (fun N : ℕ => combForm (Ioc N (N + 3 * twoBumpWindow v * N))
        (sampleCoord (twoBumpPacket v) N)) atTop
      (𝓝 (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re +
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) v).re)) := by
  rw [← zeroSum_twoBumpPacket]
  exact tendsto_combForm_sample (contDiff_twoBumpPacket v) (hasCompactSupport_twoBumpPacket v)
    (one_le_twoBumpWindow v) (twoBumpPacket_eq_zero hv)

/-- **One inequality per prime on logarithmic windows, off power-thin exceptions, on the comb.**
For `0 ≤ δ < 1` the Riemann hypothesis holds iff there are `K` and `C` such that for arbitrarily
large `T`, outside a set of at most `C e^{δT}` primes, every prime `p` of the window
`|log p − T| ≤ 32 log(T + 2)` has: Weil's form of the two-bump divisor of the lag `log p` has a
limit at least `2 Re S(0) − K`. -/
theorem riemannHypothesis_iff_twoBump_windows_off_finset {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    RiemannHypothesis ↔ ∃ K C : ℝ, 0 ≤ C ∧ ∀ U : ℝ,
      ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧ (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
        ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ primeLogarithmicRadius T →
          ∃ l : ℝ, Tendsto (fun N : ℕ =>
              combForm (Ioc N (N + 3 * twoBumpWindow (Real.log p) * N))
                (sampleCoord (twoBumpPacket (Real.log p)) N)) atTop (𝓝 l) ∧
            2 * (lagStructure zetaZeroConfig (boxSpline 1 3) 0).re - K ≤ l := by
  rw [riemannHypothesis_iff_prime_logarithmic_windows_off_finset hδ hδ1]
  refine exists_congr fun K => exists_congr fun C => and_congr_right fun _ =>
    forall_congr' fun U => exists_congr fun T => exists_congr fun E => and_congr_right fun _ =>
      and_congr_right fun _ => forall_congr' fun p => imp_congr_right fun hp =>
        imp_congr_right fun _ => imp_congr_right fun _ => ?_
  have hv : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlim := tendsto_combForm_twoBumpPacket hv
  constructor
  · intro h
    exact ⟨_, hlim, by linarith⟩
  · rintro ⟨l, hl, hle⟩
    rw [tendsto_nhds_unique hl hlim] at hle
    linarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
