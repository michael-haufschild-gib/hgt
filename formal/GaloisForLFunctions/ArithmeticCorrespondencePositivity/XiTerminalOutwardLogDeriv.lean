import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalPairRay
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiZerosSupplyLogarithmicBand
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import GaloisForLFunctions.RHTower.XiLogDerivRePositiveRightOfStrip

/-!
# Outward Xi logarithmic derivative at a terminal zero

The two reflected copies of the terminal fibre supply the principal terms.
A separated band of zero copies supplies a positive logarithmic reserve.
-/

open Finset RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Three disjoint finite blocks contribute at least their separate floors. -/
theorem finite_three_block_sum_lower {ι : Type*} [DecidableEq ι] (f : ι → ℝ)
    (A B D : Finset ι) (hAB : Disjoint A B) (hD : Disjoint D (A ∪ B))
    (a b d : ℝ) (ha : ∀ q ∈ A, a ≤ f q)
    (hb : ∀ q ∈ B, b ≤ f q) (hd : ∀ q ∈ D, d ≤ f q) :
    (A.card : ℝ) * a + (B.card : ℝ) * b + (D.card : ℝ) * d ≤
      ∑ q ∈ D ∪ (A ∪ B), f q := by
  have hA : (A.card : ℝ) * a ≤ ∑ q ∈ A, f q := by
    calc
      _ = ∑ _q ∈ A, a := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum ha
  have hB : (B.card : ℝ) * b ≤ ∑ q ∈ B, f q := by
    calc
      _ = ∑ _q ∈ B, b := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hb
  have hD' : (D.card : ℝ) * d ≤ ∑ q ∈ D, f q := by
    calc
      _ = ∑ _q ∈ D, d := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hd
  rw [Finset.sum_union hD, Finset.sum_union hAB]
  linarith only [hA, hB, hD']

/-- Interchanging the two members of a reflected pair leaves its real sum fixed. -/
theorem xiLinePairRe_neg_depth (x b y : ℝ) :
    xiLinePairRe x (-b) y = xiLinePairRe x b y := by
  unfold xiLinePairRe
  simp only [sub_eq_add_neg, neg_neg]
  ring

/-- Reflection reverses depth and preserves ordinate. -/
theorem xiLineConj_coordinates (q : XiZeroCopy) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re ∧
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).im = (q.1 : ℂ).im := by
  constructor <;> rw [xiZero_lineConj_eq] <;> simp

/-- Every copy in a fibre has the same underlying zero. -/
theorem xiZeroCopyFiber_point (p q : XiZeroCopy) (hq : q ∈ xiZeroCopyFiber p.1) :
    (q.1 : ℂ) = (p.1 : ℂ) := by
  have hq' : q.1 = p.1 := mem_xiZeroCopyFiber.mp hq
  rw [hq']

/-- The reflected fibre has the reflected abscissa and the original ordinate. -/
theorem xiReflectedFiber_coordinates (p q : XiZeroCopy)
    (hq : q ∈ (xiZeroCopyFiber p.1).map xiZeroCopyLineConjEquiv.toEmbedding) :
    (q.1 : ℂ).re = 1 - (p.1 : ℂ).re ∧ (q.1 : ℂ).im = (p.1 : ℂ).im := by
  obtain ⟨r, hr, hrq⟩ := Finset.mem_map.mp hq
  change xiZeroCopyLineConjEquiv r = q at hrq
  subst q
  have hrpoint := xiZeroCopyFiber_point p r hr
  have hrcoords := xiLineConj_coordinates r
  rw [hrpoint] at hrcoords
  exact hrcoords

/-- The two fibres over an off-line zero and its reflection are disjoint. -/
theorem xiFiber_disjoint_reflection (p : XiZeroCopy) (hp : 1 / 2 < (p.1 : ℂ).re) :
    Disjoint (xiZeroCopyFiber p.1)
      ((xiZeroCopyFiber p.1).map xiZeroCopyLineConjEquiv.toEmbedding) := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  have hpoint := xiZeroCopyFiber_point p q hq
  have hcoords := xiReflectedFiber_coordinates p q hq'
  rw [hpoint] at hcoords
  linarith only [hp, hcoords.1]

/-- A band separated in ordinate is disjoint from both terminal fibres. -/
theorem xiSeparatedBand_disjoint_terminalFibers (p : XiZeroCopy) (D : Finset XiZeroCopy)
    (hD : ∀ q ∈ D, 1 ≤ |(q.1 : ℂ).im - (p.1 : ℂ).im|) :
    Disjoint D (xiZeroCopyFiber p.1 ∪
      (xiZeroCopyFiber p.1).map xiZeroCopyLineConjEquiv.toEmbedding) := by
  apply Finset.disjoint_left.mpr
  intro q hq hq'
  have hsep := hD q hq
  rcases Finset.mem_union.mp hq' with hqfiber | hqreflect
  · have hpoint := xiZeroCopyFiber_point p q hqfiber
    rw [hpoint] at hsep
    norm_num at hsep
  · have him := (xiReflectedFiber_coordinates p q hqreflect).2
    rw [him] at hsep
    norm_num at hsep

/-- A right-hand quadratic terminal has a positive logarithmic-derivative
reserve on its outward ray, in addition to both reflected principal terms. -/
theorem exists_xiTerminal_logDeriv_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ p : XiZeroCopy, 1 / 2 < (p.1 : ℂ).re →
      (∀ r : XiZeroCopy, xiZeroDepth r ^ 2 ≤
        xiZeroDepth p ^ 2 + (xiZeroHeight r - xiZeroHeight p) ^ 2) →
      ∀ h : ℝ, 0 < h → h < 1 / 2 - xiZeroDepth p →
        ((xiZeroCopyFiber p.1).card : ℝ) / h +
          ((xiZeroCopyFiber p.1).card : ℝ) / (2 * xiZeroDepth p + h) +
          c * xiZeroDepth p * Real.log (|xiZeroHeight p| + 4) ≤
            (logDeriv xi ((p.1 : ℂ) + (h : ℂ))).re := by
  classical
  obtain ⟨H, hH, hBand⟩ := exists_xi_zero_logarithmic_band
  let k : ℝ := (3 / 2) / (1 + H ^ 2) ^ 2
  have hk : 0 < k := by dsimp only [k]; positivity
  let c : ℝ := k / 2
  refine ⟨c, by dsimp only [c]; positivity, ?_⟩
  intro p hp hcone h hh hhbound
  let a : ℝ := xiZeroDepth p
  have haeq : a = (p.1 : ℂ).re - 1 / 2 := by
    dsimp only [a, xiZeroDepth]
    rw [abs_of_pos (by linarith)]
  have ha : 0 < a := by rw [haeq]; linarith
  have hbound : h < 1 / 2 - a := hhbound
  have hmax : a + h ≤ 1 / 2 := by linarith only [hbound]
  obtain ⟨D, hD, hcard⟩ := hBand (xiZeroHeight p)
  let A : Finset XiZeroCopy := xiZeroCopyFiber p.1
  let B : Finset XiZeroCopy := A.map xiZeroCopyLineConjEquiv.toEmbedding
  let s : ℂ := (p.1 : ℂ) + (h : ℂ)
  let f : XiZeroCopy → ℝ := fun q =>
    xiLinePairRe (s.re - 1 / 2) ((q.1 : ℂ).re - 1 / 2) (s.im - (q.1 : ℂ).im)
  let u : ℝ := 1 / h + 1 / (2 * a + h)
  have hsre : s.re - 1 / 2 = a + h := by
    dsimp only [s]
    rw [haeq]
    simp; ring
  have hsim : s.im = xiZeroHeight p := by
    dsimp only [s, xiZeroHeight]
    simp
  have hAB : Disjoint A B := by
    dsimp only [A, B]
    exact xiFiber_disjoint_reflection p hp
  have hDA : Disjoint D (A ∪ B) := by
    dsimp only [A, B]
    apply xiSeparatedBand_disjoint_terminalFibers p D
    intro q hq
    simpa only [xiZeroHeight] using (hD q hq).1
  -- The terminal fibre and its reflection each supply both principal terms.
  have hA : ∀ q ∈ A, u ≤ f q := by
    intro q hq
    have hpoint := xiZeroCopyFiber_point p q (by simpa only [A] using hq)
    have heq : f q = u := by
      dsimp only [f, u]
      rw [hsre, hsim, hpoint, haeq.symm]
      simpa only [xiZeroHeight, sub_self] using (xiLinePairRe_at_zero ha hh)
    exact heq.ge
  have hB : ∀ q ∈ B, u ≤ f q := by
    intro q hq
    have hcoords := xiReflectedFiber_coordinates p q (by simpa only [A, B] using hq)
    have hb : (q.1 : ℂ).re - 1 / 2 = -a := by rw [hcoords.1, haeq]; ring
    have hy : xiZeroHeight p - (q.1 : ℂ).im = 0 := by
      rw [hcoords.2]
      simp only [xiZeroHeight, sub_self]
    have heq : f q = u := by
      dsimp only [f, u]
      rw [hsre, hsim, hb, hy, xiLinePairRe_neg_depth]
      exact xiLinePairRe_at_zero ha hh
    exact heq.ge
  -- The separated band contributes a uniform positive amount per copy.
  have hDreserve : ∀ q ∈ D, k * a ≤ f q := by
    intro q hq
    have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := (xiZeroDepth_bounds q).2
    have hy : |s.im - (q.1 : ℂ).im| = |(q.1 : ℂ).im - xiZeroHeight p| := by
      rw [hsim, abs_sub_comm]
    have hy1 : 1 ≤ |s.im - (q.1 : ℂ).im| := by rw [hy]; exact (hD q hq).1
    have hy2 : |s.im - (q.1 : ℂ).im| ≤ H := by rw [hy]; exact (hD q hq).2
    have hqbound := xiLinePairRe_height_reserve ha (show a ≤ a + h by linarith)
      hmax hb hy1 hy2
    have heq : ((3 / 2) * a) / (1 + H ^ 2) ^ 2 = k * a := by
      dsimp only [k]
      ring
    rw [heq] at hqbound
    dsimp only [f]
    rw [hsre]
    exact hqbound
  have hdepth : xiZeroDepth p < a + h := by dsimp only [a]; linarith only [hh]
  have hpair : ∀ q : XiZeroCopy, 0 ≤
      xiLinePairRe (s.re - 1 / 2) ((q.1 : ℂ).re - 1 / 2) (s.im - (q.1 : ℂ).im) := by
    intro q
    rw [hsre, hsim]
    exact xiTerminal_pair_nonneg p hcone hdepth q
  have hxi : xi s ≠ 0 := by
    dsimp only [s]
    exact xi_ne_zero_on_terminal_ray p hp hcone hh
  have hwhole := sum_pair_le_two_mul_re_logDeriv_xi hxi hpair (D ∪ (A ∪ B))
  have hthree := finite_three_block_sum_lower f A B D hAB hDA u u (k * a) hA hB hDreserve
  have hBcard : B.card = A.card := by
    dsimp only [B]
    exact Finset.card_map _
  rw [hBcard] at hthree
  have hbudget : (A.card : ℝ) * u + (A.card : ℝ) * u +
      (D.card : ℝ) * (k * a) ≤ 2 * (logDeriv xi s).re := by
    exact hthree.trans hwhole
  have hcard' : Real.log (|xiZeroHeight p| + 4) * (k * a) ≤
      (D.card : ℝ) * (k * a) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hbudget' : (A.card : ℝ) * u + (A.card : ℝ) * u +
      Real.log (|xiZeroHeight p| + 4) * (k * a) ≤ 2 * (logDeriv xi s).re := by
    linarith only [hbudget, hcard']
  change (A.card : ℝ) / h + (A.card : ℝ) / (2 * a + h) +
    c * a * Real.log (|xiZeroHeight p| + 4) ≤ (logDeriv xi s).re
  have hidentity : 2 * ((A.card : ℝ) / h + (A.card : ℝ) / (2 * a + h) +
      c * a * Real.log (|xiZeroHeight p| + 4)) =
      (A.card : ℝ) * u + (A.card : ℝ) * u +
        Real.log (|xiZeroHeight p| + 4) * (k * a) := by
    dsimp only [c, u]
    ring
  rw [← hidentity] at hbudget'
  linarith only [hbudget']

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
