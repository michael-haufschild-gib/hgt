import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Dyadic depth projection of the continuous Möbius aperture metric

The normalized kernel `K(h*a,h*b)/h` is the Gram obtained by averaging the continuous exponential
features over valuation-depth bins of width `h`.  This file formalizes the exact innovation created
by refining every bin into two halves.

The refinement difference is not merely entrywise nonnegative: it is an actual `ell^2` Gram, both
at one prime and after the all-prime completion.  Thus the true aperture metrics increase in
Loewner order under dyadic refinement.  This is the first genuinely noninvertible infinite-level
map exposed by the continuous aperture construction; no Xi positivity or RH hypothesis is used.
-/

namespace RHTower

noncomputable section

open scoped BigOperators
open Filter Matrix

/-- The unnormalized innovation produced by halving the common aperture mesh. -/
def xiMobiusPrimeContinuousApertureDyadicInnovation
    (h a b : ℝ) (p : Nat.Primes) : ℝ :=
  2 * xiMobiusPrimeContinuousApertureSzegoMetric ((h / 2) * a) ((h / 2) * b) p -
    xiMobiusPrimeContinuousApertureSzegoMetric (h * a) (h * b) p

/-- Doubling the aperture squares the corresponding disk node. -/
theorem xiMobiusContinuousApertureDiskNode_mul_eq_half_sq
    (h a : ℝ) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode (h * a) p =
      xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ 2 := by
  rw [xiMobiusContinuousApertureDiskNode, xiMobiusContinuousApertureDiskNode,
    pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Exact positive Szegő form of the dyadic innovation. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovation_eq_szego
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDyadicInnovation h a b p =
      let q := xiTransversePrimeApertureDiskNode 1 p
      let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
      let s := xiMobiusContinuousApertureDiskNode ((h / 2) * b) p
      (q / (1 + q)) ^ 2 * (1 - r) ^ 2 * (1 - s) ^ 2 /
        (1 - (r * s) ^ 2) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  let s := xiMobiusContinuousApertureDiskNode ((h / 2) * b) p
  have hha : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hhb : 0 < (h / 2) * b := mul_pos (half_pos hh) hb
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos _ p
  have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos _ p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hhb p
  have hrs1 : r * s < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
  have hden1 : 1 - r * s ≠ 0 := by linarith
  have hden2 : 1 - (r * s) ^ 2 ≠ 0 := by
    have hsq : (r * s) ^ 2 < 1 := pow_lt_one₀ (mul_nonneg hr0.le hs0.le) hrs1 (by norm_num)
    linarith
  have hden3 : 1 - r ^ 2 * s ^ 2 ≠ 0 := by
    rw [show r ^ 2 * s ^ 2 = (r * s) ^ 2 by ring]
    exact hden2
  have hqden : 1 + q ≠ 0 := by linarith
  simp only [xiMobiusPrimeContinuousApertureDyadicInnovation,
    xiMobiusPrimeContinuousApertureSzegoMetric]
  rw [xiMobiusContinuousApertureDiskNode_mul_eq_half_sq h a p,
    xiMobiusContinuousApertureDiskNode_mul_eq_half_sq h b p]
  change 2 * ((q / (1 + q)) ^ 2 * (1 - r) * (1 - s) / (1 - r * s)) -
      (q / (1 + q)) ^ 2 * (1 - r ^ 2) * (1 - s ^ 2) /
        (1 - r ^ 2 * s ^ 2) =
    (q / (1 + q)) ^ 2 * (1 - r) ^ 2 * (1 - s) ^ 2 /
      (1 - (r * s) ^ 2)
  field_simp [hden1, hden2, hden3, hqden]
  ring

/-- The explicit depth feature carrying one dyadic innovation channel. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationFeature
    (h a : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  (q / (1 + q)) * (1 - r) ^ 2 * (r ^ 2) ^ e

private theorem summable_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    Summable (fun e : ℕ =>
      xiMobiusPrimeContinuousApertureDyadicInnovationFeature h a p e *
        xiMobiusPrimeContinuousApertureDyadicInnovationFeature h b p e) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  let s := xiMobiusContinuousApertureDiskNode ((h / 2) * b) p
  have hha : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hhb : 0 < (h / 2) * b := mul_pos (half_pos hh) hb
  have hr0 : 0 ≤ r := (xiMobiusContinuousApertureDiskNode_pos _ p).le
  have hs0 : 0 ≤ s := (xiMobiusContinuousApertureDiskNode_pos _ p).le
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hhb p
  have hrs0 : 0 ≤ (r * s) ^ 2 := sq_nonneg _
  have hrs1 : (r * s) ^ 2 < 1 :=
    pow_lt_one₀ (mul_nonneg hr0 hs0)
      (mul_lt_one_of_nonneg_of_lt_one_left hr0 hr1 hs1.le) (by norm_num)
  refine ((summable_geometric_of_lt_one hrs0 hrs1).mul_left
    ((q / (1 + q)) ^ 2 * (1 - r) ^ 2 * (1 - s) ^ 2)).congr ?_
  intro e
  simp only [xiMobiusPrimeContinuousApertureDyadicInnovationFeature, q, r, s]
  rw [show (r * s) ^ 2 = r ^ 2 * s ^ 2 by ring, mul_pow]
  ring

/-- The dyadic innovation is exactly the completed Gram of its explicit depth features. -/
theorem tsum_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul_eq
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    (∑' e : ℕ,
      xiMobiusPrimeContinuousApertureDyadicInnovationFeature h a p e *
        xiMobiusPrimeContinuousApertureDyadicInnovationFeature h b p e) =
      xiMobiusPrimeContinuousApertureDyadicInnovation h a b p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode ((h / 2) * a) p
  let s := xiMobiusContinuousApertureDiskNode ((h / 2) * b) p
  have hha : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hhb : 0 < (h / 2) * b := mul_pos (half_pos hh) hb
  have hr0 : 0 ≤ r := (xiMobiusContinuousApertureDiskNode_pos _ p).le
  have hs0 : 0 ≤ s := (xiMobiusContinuousApertureDiskNode_pos _ p).le
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hhb p
  have hrs0 : 0 ≤ (r * s) ^ 2 := sq_nonneg _
  have hrs1 : (r * s) ^ 2 < 1 :=
    pow_lt_one₀ (mul_nonneg hr0 hs0)
      (mul_lt_one_of_nonneg_of_lt_one_left hr0 hr1 hs1.le) (by norm_num)
  calc
    (∑' e : ℕ,
      xiMobiusPrimeContinuousApertureDyadicInnovationFeature h a p e *
        xiMobiusPrimeContinuousApertureDyadicInnovationFeature h b p e) =
        ((q / (1 + q)) ^ 2 * (1 - r) ^ 2 * (1 - s) ^ 2) *
          ∑' e : ℕ, ((r * s) ^ 2) ^ e := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro e
      simp only [xiMobiusPrimeContinuousApertureDyadicInnovationFeature, q, r, s]
      rw [show (r * s) ^ 2 = r ^ 2 * s ^ 2 by ring, mul_pow]
      ring
    _ = ((q / (1 + q)) ^ 2 * (1 - r) ^ 2 * (1 - s) ^ 2) *
        (1 - (r * s) ^ 2)⁻¹ := by
      rw [tsum_geometric_of_lt_one hrs0 hrs1]
    _ = xiMobiusPrimeContinuousApertureDyadicInnovation h a b p := by
      rw [xiMobiusPrimeContinuousApertureDyadicInnovation_eq_szego hh ha hb p]
      simp only [q, r, s, div_eq_mul_inv]

/-- **Cubic birth of the refinement channel.**  The dyadic innovation has no linear or quadratic
part.  Its first nonzero common-aperture germ is cubic, with an explicit positive Cauchy coefficient
at every prime. -/
theorem tendsto_xiMobiusPrimeContinuousApertureDyadicInnovation_div_cube
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    Tendsto
      (fun h : ℝ =>
        xiMobiusPrimeContinuousApertureDyadicInnovation h a b p / h ^ 3)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((xiTransversePrimeApertureDiskNode 1 p /
            (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
          (((a / 2) * Real.log (p : ℝ)) ^ 2 *
              ((b / 2) * Real.log (p : ℝ)) ^ 2 /
            ((a + b) * Real.log (p : ℝ))))) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let L := Real.log (p : ℝ)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp
  have hab : 0 < a + b := add_pos ha hb
  have hA :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
      (a / 2) p
  have hB :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
      (b / 2) p
  have hAB :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
      (a + b) p
  have hratio : Tendsto
      (fun h : ℝ =>
        ((1 - xiMobiusContinuousApertureDiskNode (h * (a / 2)) p) / h) ^ 2 *
          ((1 - xiMobiusContinuousApertureDiskNode (h * (b / 2)) p) / h) ^ 2 /
            ((1 - xiMobiusContinuousApertureDiskNode (h * (a + b)) p) / h))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        ((((a / 2) * L) ^ 2 * ((b / 2) * L) ^ 2) / ((a + b) * L))) := by
    exact ((hA.pow 2).mul (hB.pow 2)).div hAB (mul_ne_zero hab.ne' hL.ne')
  have hlimit : Tendsto
      (fun h : ℝ =>
        (q / (1 + q)) ^ 2 *
          (((1 - xiMobiusContinuousApertureDiskNode (h * (a / 2)) p) / h) ^ 2 *
            ((1 - xiMobiusContinuousApertureDiskNode (h * (b / 2)) p) / h) ^ 2 /
              ((1 - xiMobiusContinuousApertureDiskNode (h * (a + b)) p) / h)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((q / (1 + q)) ^ 2 *
        ((((a / 2) * L) ^ 2 * ((b / 2) * L) ^ 2) / ((a + b) * L)))) :=
    tendsto_const_nhds.mul hratio
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhalfA : (h / 2) * a = h * (a / 2) := by ring
  have hhalfB : (h / 2) * b = h * (b / 2) := by ring
  have hnode :
      (xiMobiusContinuousApertureDiskNode (h * (a / 2)) p *
          xiMobiusContinuousApertureDiskNode (h * (b / 2)) p) ^ 2 =
        xiMobiusContinuousApertureDiskNode (h * (a + b)) p := by
    rw [← xiMobiusContinuousApertureDiskNode_add,
      xiMobiusContinuousApertureDiskNode_mul_eq_half_sq h (a + b) p]
    congr 2
    ring
  have hsumPos : 0 < h * (a + b) := mul_pos hh hab
  have hden :
      1 - xiMobiusContinuousApertureDiskNode (h * (a + b)) p ≠ 0 := by
    have hlt := xiMobiusContinuousApertureDiskNode_lt_one hsumPos p
    linarith
  have hh0 : h ≠ 0 := ne_of_gt hh
  rw [xiMobiusPrimeContinuousApertureDyadicInnovation_eq_szego hh ha hb p]
  simp only [q]
  rw [hhalfA, hhalfB, hnode]
  field_simp [hh0, hden]

/-- Finite Cauchy tangent Gram before the global positive prime constant is inserted. -/
def xiMobiusContinuousApertureCauchyTangentGram
    {N : ℕ} (a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => a i * a j / (a i + a j)

/-- The positive kernel selected by the first cubic aperture-curvature coefficient. -/
def xiMobiusContinuousApertureCubicCurvatureGram
    {N : ℕ} (a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (a i) ^ 2 * (a j) ^ 2 / (a i + a j)

/-- The cubic curvature is an exact diagonal congruence of the Cauchy tangent. -/
theorem xiMobiusContinuousApertureCubicCurvatureGram_eq_congruence
    {N : ℕ} (a : Fin N → ℝ) :
    xiMobiusContinuousApertureCubicCurvatureGram a =
      (Matrix.diagonal a)ᴴ * xiMobiusContinuousApertureCauchyTangentGram a *
        Matrix.diagonal a := by
  classical
  ext i j
  simp only [xiMobiusContinuousApertureCubicCurvatureGram,
    xiMobiusContinuousApertureCauchyTangentGram, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, star_trivial]
  simp
  ring

/-- **Finite cubic-curvature no-go and positive survivor.**  On every positive aperture packet,
the cubic curvature and the first-order Cauchy tangent have exactly the same positive-semidefinite
status.  The curvature is therefore an invertible finite coordinate dressing, not the missing
noninvertible Xi amplifier. -/
theorem xiMobiusContinuousApertureCubicCurvatureGram_posSemidef_iff
    {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) :
    (xiMobiusContinuousApertureCubicCurvatureGram a).PosSemidef ↔
      (xiMobiusContinuousApertureCauchyTangentGram a).PosSemidef := by
  classical
  rw [xiMobiusContinuousApertureCubicCurvatureGram_eq_congruence]
  have hunit : IsUnit (Matrix.diagonal a) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero,
      Finset.prod_ne_zero_iff]
    exact fun i _ => (ha i).ne'
  simpa only [star_eq_conjTranspose] using
    hunit.posSemidef_star_left_conjugate_iff
      (x := xiMobiusContinuousApertureCauchyTangentGram a)

private theorem memℓp_two_of_sq_summable_real {f : ℕ → ℝ}
    (hf : Summable fun e => f e ^ 2) : Memℓp f 2 := by
  apply memℓp_gen
  refine hf.congr fun e => ?_
  rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) by simp,
    Real.rpow_natCast, Real.norm_eq_abs, sq_abs]

/-- The local dyadic innovation feature is an actual depth `ell^2` vector. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp
    (h a : ℝ) (p : Nat.Primes) (hh : 0 < h) (ha : 0 < a) :
    lp (fun _ : ℕ => ℝ) 2 :=
  ⟨xiMobiusPrimeContinuousApertureDyadicInnovationFeature h a p,
    memℓp_two_of_sq_summable_real (by
      simpa only [pow_two] using
        summable_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul
          hh ha ha p)⟩

/-- The local innovation is the Hilbert inner product of the genuine innovation vectors. -/
theorem inner_xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_eq
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    inner ℝ
      (xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp h a p hh ha)
      (xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp h b p hh hb) =
        xiMobiusPrimeContinuousApertureDyadicInnovation h a b p := by
  rw [lp.inner_eq_tsum]
  change (∑' i : ℕ,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature h b p i *
      xiMobiusPrimeContinuousApertureDyadicInnovationFeature h a p i) = _
  simpa only [mul_comm] using
    tsum_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul_eq hh ha hb p

/-- Finite aperture Gram of one prime's dyadic refinement innovation. -/
def xiMobiusPrimeContinuousApertureDyadicInnovationGram
    {N : ℕ} (h : ℝ) (a : Fin N → ℝ) (p : Nat.Primes) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiMobiusPrimeContinuousApertureDyadicInnovation h (a i) (a j) p

/-- Every one-prime dyadic innovation Gram is positive semidefinite. -/
theorem xiMobiusPrimeContinuousApertureDyadicInnovationGram_posSemidef
    {N : ℕ} {h : ℝ} (hh : 0 < h) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureDyadicInnovationGram h a p).PosSemidef := by
  have hgram : xiMobiusPrimeContinuousApertureDyadicInnovationGram h a p =
      Matrix.gram ℝ (fun i =>
        xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp h (a i) p hh (ha i)) := by
    ext i j
    simp only [xiMobiusPrimeContinuousApertureDyadicInnovationGram, Matrix.gram]
    simpa only [Matrix.of_apply] using
      (inner_xiMobiusPrimeContinuousApertureDyadicInnovationFeatureLp_eq
        hh (ha i) (ha j) p).symm
  rw [hgram]
  exact Matrix.posSemidef_gram ℝ _

/-- The all-prime dyadic innovation kernel. -/
def xiMobiusContinuousApertureDyadicInnovation (h a b : ℝ) : ℝ :=
  ∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureDyadicInnovation h a b p

private theorem summable_xiMobiusPrimeContinuousApertureDyadicInnovation_self
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureDyadicInnovation h a a p) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  have hnodes : Summable
      (fun p : Nat.Primes => xiTransversePrimeApertureDiskNode 1 p ^ 2) := by
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] using hprime
  refine Summable.of_nonneg_of_le ?_ ?_ (hnodes.mul_left 2)
  · intro p
    rw [← tsum_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul_eq hh ha ha p]
    exact tsum_nonneg fun e => mul_self_nonneg _
  · intro p
    rw [xiMobiusPrimeContinuousApertureDyadicInnovation]
    have hfull : 0 ≤ xiMobiusPrimeContinuousApertureSzegoMetric (h * a) (h * a) p :=
      xiMobiusPrimeContinuousApertureSzegoMetric_self_nonneg (mul_pos hh ha) p
    have hhalf := xiMobiusPrimeContinuousApertureSzegoMetric_self_le_invSq
      (mul_pos (half_pos hh) ha) p
    linarith

/-- All-prime innovation feature, indexed by prime and residual depth. -/
def xiMobiusContinuousApertureDyadicInnovationFeature
    (h a : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  xiMobiusPrimeContinuousApertureDyadicInnovationFeature h a pe.1 pe.2

private theorem summable_xiMobiusContinuousApertureDyadicInnovationFeature_sq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Summable (fun pe : Nat.Primes × ℕ =>
      xiMobiusContinuousApertureDyadicInnovationFeature h a pe ^ 2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro p
    simpa only [xiMobiusContinuousApertureDyadicInnovationFeature, pow_two] using
      summable_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul hh ha ha p
  · simpa only [xiMobiusContinuousApertureDyadicInnovationFeature, pow_two,
      tsum_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul_eq hh ha ha] using
        summable_xiMobiusPrimeContinuousApertureDyadicInnovation_self hh ha

private theorem memℓp_two_of_sq_summable_real_prod
    {f : Nat.Primes × ℕ → ℝ} (hf : Summable fun pe => f pe ^ 2) :
    Memℓp f 2 := by
  apply memℓp_gen
  refine hf.congr fun pe => ?_
  rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) by simp,
    Real.rpow_natCast, Real.norm_eq_abs, sq_abs]

/-- The completed all-prime dyadic innovation is a genuine direct-sum `ell^2` vector. -/
def xiMobiusContinuousApertureDyadicInnovationFeatureLp
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    lp (fun _ : Nat.Primes × ℕ => ℝ) 2 :=
  ⟨xiMobiusContinuousApertureDyadicInnovationFeature h a,
    memℓp_two_of_sq_summable_real_prod
      (summable_xiMobiusContinuousApertureDyadicInnovationFeature_sq hh ha)⟩

/-- The completed innovation is the inner product of the actual all-prime innovation vectors. -/
theorem inner_xiMobiusContinuousApertureDyadicInnovationFeatureLp_eq
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) :
    inner ℝ
      (xiMobiusContinuousApertureDyadicInnovationFeatureLp h a hh ha)
      (xiMobiusContinuousApertureDyadicInnovationFeatureLp h b hh hb) =
        xiMobiusContinuousApertureDyadicInnovation h a b := by
  have hsqA := summable_xiMobiusContinuousApertureDyadicInnovationFeature_sq hh ha
  have hsqB := summable_xiMobiusContinuousApertureDyadicInnovationFeature_sq hh hb
  have hsum : Summable (fun pe : Nat.Primes × ℕ =>
      xiMobiusContinuousApertureDyadicInnovationFeature h b pe *
        xiMobiusContinuousApertureDyadicInnovationFeature h a pe) := by
    apply Summable.of_norm_bounded (hsqB.add hsqA)
    intro pe
    let x := xiMobiusContinuousApertureDyadicInnovationFeature h b pe
    let y := xiMobiusContinuousApertureDyadicInnovationFeature h a pe
    change ‖x * y‖ ≤ x ^ 2 + y ^ 2
    rw [Real.norm_eq_abs, abs_mul]
    have hxy := two_mul_le_add_sq |x| |y|
    rw [sq_abs, sq_abs] at hxy
    nlinarith [abs_nonneg x, abs_nonneg y]
  rw [lp.inner_eq_tsum]
  change (∑' pe : Nat.Primes × ℕ,
    xiMobiusContinuousApertureDyadicInnovationFeature h b pe *
      xiMobiusContinuousApertureDyadicInnovationFeature h a pe) = _
  rw [hsum.tsum_prod]
  apply tsum_congr
  intro p
  simpa only [xiMobiusContinuousApertureDyadicInnovationFeature, mul_comm] using
    tsum_xiMobiusPrimeContinuousApertureDyadicInnovationFeature_mul_eq hh ha hb p

/-- Finite aperture Gram of the completed all-prime dyadic innovation. -/
def xiMobiusContinuousApertureDyadicInnovationGram
    {N : ℕ} (h : ℝ) (a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiMobiusContinuousApertureDyadicInnovation h (a i) (a j)

/-- The completed all-prime dyadic innovation is positive semidefinite on every finite packet. -/
theorem xiMobiusContinuousApertureDyadicInnovationGram_posSemidef
    {N : ℕ} {h : ℝ} (hh : 0 < h) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) :
    (xiMobiusContinuousApertureDyadicInnovationGram h a).PosSemidef := by
  have hgram : xiMobiusContinuousApertureDyadicInnovationGram h a =
      Matrix.gram ℝ (fun i =>
        xiMobiusContinuousApertureDyadicInnovationFeatureLp h (a i) hh (ha i)) := by
    ext i j
    simp only [xiMobiusContinuousApertureDyadicInnovationGram, Matrix.gram]
    simpa only [Matrix.of_apply] using
      (inner_xiMobiusContinuousApertureDyadicInnovationFeatureLp_eq
        hh (ha i) (ha j)).symm
  rw [hgram]
  exact Matrix.posSemidef_gram ℝ _

private theorem summable_xiMobiusPrimeContinuousApertureSzegoMetric_mul
    {t a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p) := by
  have hdiv : Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t) := by
    apply Summable.of_norm_bounded
      (summable_xiMobiusPrimeContinuousApertureSlopeTerm.mul_left a)
    intro p
    exact norm_xiMobiusPrimeContinuousApertureSzegoMetric_mul_div_le ht ha hb p
  exact (hdiv.mul_left t).congr fun p => by field_simp [ht.ne']

/-- The completed innovation is exactly the difference between two successive normalized meshes,
before division by the coarse width. -/
theorem xiMobiusContinuousApertureDyadicInnovation_eq_kernel
    {h a b : ℝ} (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) :
    xiMobiusContinuousApertureDyadicInnovation h a b =
      2 * xiMobiusContinuousApertureKernel ((h / 2) * a) ((h / 2) * b) -
        xiMobiusContinuousApertureKernel (h * a) (h * b) := by
  have hhalf := summable_xiMobiusPrimeContinuousApertureSzegoMetric_mul
    (half_pos hh) ha hb
  have hfull := summable_xiMobiusPrimeContinuousApertureSzegoMetric_mul hh ha hb
  rw [xiMobiusContinuousApertureDyadicInnovation]
  simp only [xiMobiusPrimeContinuousApertureDyadicInnovation]
  simp only [xiMobiusContinuousApertureKernel]
  rw [(hhalf.mul_left 2).tsum_sub hfull, tsum_mul_left]

/-- The normalized completed aperture Gram at mesh width `h`. -/
def xiMobiusContinuousApertureNormalizedMeshGram
    {N : ℕ} (h : ℝ) (a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiMobiusContinuousApertureKernel (h * a i) (h * a j) / h

/-- **Dyadic Loewner refinement.**  Halving the common valuation-depth mesh adds a positive
semidefinite all-prime innovation Gram. -/
theorem xiMobiusContinuousApertureNormalizedMeshGram_dyadic_sub_posSemidef
    {N : ℕ} {h : ℝ} (hh : 0 < h) (a : Fin N → ℝ) (ha : ∀ i, 0 < a i) :
    (xiMobiusContinuousApertureNormalizedMeshGram (h / 2) a -
      xiMobiusContinuousApertureNormalizedMeshGram h a).PosSemidef := by
  have heq :
      xiMobiusContinuousApertureNormalizedMeshGram (h / 2) a -
          xiMobiusContinuousApertureNormalizedMeshGram h a =
        (1 / h) • xiMobiusContinuousApertureDyadicInnovationGram h a := by
    ext i j
    simp only [xiMobiusContinuousApertureNormalizedMeshGram,
      xiMobiusContinuousApertureDyadicInnovationGram, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [xiMobiusContinuousApertureDyadicInnovation_eq_kernel hh (ha i) (ha j)]
    field_simp [hh.ne']
  rw [heq]
  exact (xiMobiusContinuousApertureDyadicInnovationGram_posSemidef hh a ha).smul
    (by positivity)

end

end RHTower
