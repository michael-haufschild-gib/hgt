import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy

/-!
# The dilation Hardy inequality on the pronic measure

The pronic measure is exactly self-similar under integer dilation: the fibre of a level carries
`1/j` of its mass.  That one identity turns the whole pronic energy into a *boundary-value problem
on the dilation tree*: with the Dirichlet condition `v 0 = 0` at the root, the energy of a row is
controlled by the energy of its **single dilation step** alone.

For every integer `q ≥ 2`, every horizon and every row vanishing at `0`,

`Σ_{n ≤ T} v(n)²/(n(n+1)) ≤ q/(√q − 1)² · Σ_{n ≤ T} (v(n) − v(n/q))²/(n(n+1))`
(`pronicNorm_sq_le_dilationStepEnergy`),

with the reverse comparison `Σ (v(n) − v(n/q))² w(n) ≤ 2(1 + 1/q) Σ v(n)² w(n)`
(`dilationStepEnergy_le`).  So the pronic energy and the one-step dilation energy are *uniformly
comparable*, with explicit two-sided constants and no arithmetic input whatever.  The constant
`q/(√q − 1)²` is the optimum of the elementary Peter–Paul split against the self-similarity ratio;
at `q = 2` it is `6 + 4√2`.

The consequence for the continuation layer is a reduction of its receiver.  The dilation step of
the centred source is a **block sum**: `A_ε(n) − A_ε(n/q)` is the centred divisor sum over the top
block `(n/q, n]` (`pmPowerDampedCenteredDivisorPrefix_sub_eq_blockSum`), so

`dampedMobiusEnergy ε T ≤ q/(√q − 1)² · Σ_{n ≤ T} (Σ_{n/q < j ≤ n} centred coeff)²/(n(n+1))`
(`dampedMobiusEnergy_le_blockEnergy`),

and admission at a damping — hence, cofinally, the Riemann hypothesis — follows from a
horizon-uniform bound on the pronic mean square of the centred divisor sums over *blocks* rather
than over prefixes (`riemannHypothesis_of_cofinal_bounded_blockEnergy`).  The long prefix, whose
cancellation is the open obligation, is replaced by one localized block at every scale; the two
quantities are comparable, so nothing is lost, and the localized object is the one the window laws
of the finite programmes speak about.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The one-step dilation energy -/

/-- The **dilation step energy** at scale `q`: the pronic Dirichlet energy of a row along the single
dilation `n ↦ n / q`, with the Dirichlet condition at the root read through `v 0`. -/
def dilationStepEnergy (q T : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, (v n - v (n / q)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

theorem dilationStepEnergy_nonneg (q T : ℕ) (v : ℕ → ℝ) : 0 ≤ dilationStepEnergy q T v := by
  refine Finset.sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  positivity

/-- The squared form of the sharp pronic dilation contraction. -/
theorem pronicNorm_rowDilate_sq_le {q : ℕ} (hq : 1 ≤ q) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    pronicNorm T (rowDilate q v) ^ 2 ≤ (1 / (q : ℝ)) * pronicNorm T v ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h := pronicNorm_rowDilate_le_sharp hq T v hv0
  have hnn : 0 ≤ pronicNorm T (rowDilate q v) := pronicNorm_nonneg T _
  have hsq : pronicNorm T (rowDilate q v) ^ 2 ≤
      ((1 / Real.sqrt (q : ℝ)) * pronicNorm T v) ^ 2 := by
    have hrhs : 0 ≤ (1 / Real.sqrt (q : ℝ)) * pronicNorm T v :=
      mul_nonneg (by positivity) (pronicNorm_nonneg T v)
    exact pow_le_pow_left hnn h 2
  have hroot : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0.le
  calc pronicNorm T (rowDilate q v) ^ 2
      ≤ ((1 / Real.sqrt (q : ℝ)) * pronicNorm T v) ^ 2 := hsq
    _ = (1 / (q : ℝ)) * pronicNorm T v ^ 2 := by
        rw [mul_pow, div_pow, one_pow, hroot]

/-! ## §2. The Hardy inequality -/

/-- The Peter–Paul split at the self-similarity ratio: for `s > 1`,
`(a + b)² ≤ s/(s−1) · a² + s · b²`, with equality direction `a = (s−1)b`. -/
private theorem peterPaul_sq {s a b : ℝ} (hs : 1 < s) :
    (a + b) ^ 2 ≤ (s / (s - 1)) * a ^ 2 + s * b ^ 2 := by
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  rw [div_mul_eq_mul_div, ← sub_nonneg, ← sub_div_eq_sub_div_iff_of_pos hs1] <;>
    nlinarith [sq_nonneg (a - (s - 1) * b), hs1]

/-- **The dilation Hardy inequality.**  With the Dirichlet condition at the root, the pronic energy
of a row is controlled by the energy of its single dilation step, with the explicit constant
`q/(√q − 1)²` coming from the self-similarity ratio `1/q` of the pronic measure. -/
theorem pronicNorm_sq_le_dilationStepEnergy {q : ℕ} (hq : 2 ≤ q) (T : ℕ) (v : ℕ → ℝ)
    (hv0 : v 0 = 0) :
    pronicNorm T v ^ 2 ≤
      ((q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2) * dilationStepEnergy q T v := by
  set s := Real.sqrt (q : ℝ) with hs_def
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsq : s ^ 2 = (q : ℝ) := Real.sq_sqrt hq0.le
  have hs1 : 1 < s := by
    have : Real.sqrt 1 < Real.sqrt (q : ℝ) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      linarith
    simpa [hs_def] using this
  have hs1' : (0 : ℝ) < s - 1 := by linarith
  have hspos : (0 : ℝ) < s := by linarith
  -- pointwise Peter–Paul split, summed against the pronic weight
  have hstep : pronicNorm T v ^ 2 ≤
      (s / (s - 1)) * dilationStepEnergy q T v +
        s * pronicNorm T (rowDilate q v) ^ 2 := by
    rw [pronicNorm_sq, dilationStepEnergy, pronicNorm_sq, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hw : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    have hpp := peterPaul_sq (s := s) (a := v n - v (n / q)) (b := v (n / q)) hs1
    have hvn : v n = (v n - v (n / q)) + v (n / q) := by ring
    rw [hvn]
    rw [div_add_div_same] at *
    rw [div_le_div_iff_of_pos_right hw] at *
    · nlinarith [hpp, hw]
  -- the fibre bound closes the inequality
  have hcontr := pronicNorm_rowDilate_sq_le (q := q) (by omega) T v hv0
  have hqs : (1 / (q : ℝ)) = 1 / s ^ 2 := by rw [hsq]
  have hX : (0 : ℝ) ≤ pronicNorm T v ^ 2 := sq_nonneg _
  have hD : (0 : ℝ) ≤ dilationStepEnergy q T v := dilationStepEnergy_nonneg q T v
  have hkey : pronicNorm T v ^ 2 ≤
      (s / (s - 1)) * dilationStepEnergy q T v + (1 / s) * pronicNorm T v ^ 2 := by
    refine hstep.trans ?_
    have : s * pronicNorm T (rowDilate q v) ^ 2 ≤ s * ((1 / (q : ℝ)) * pronicNorm T v ^ 2) :=
      mul_le_mul_of_nonneg_left hcontr hspos.le
    have hred : s * ((1 / (q : ℝ)) * pronicNorm T v ^ 2) = (1 / s) * pronicNorm T v ^ 2 := by
      rw [← hsq]; field_simp; ring
    linarith [this, hred.le, hred.ge]
  have hqdiv : (q : ℝ) / (s - 1) ^ 2 = s ^ 2 / (s - 1) ^ 2 := by rw [hsq]
  rw [hqdiv]
  have hfinal : (1 - 1 / s) * pronicNorm T v ^ 2 ≤ (s / (s - 1)) * dilationStepEnergy q T v := by
    linarith
  have hfac : (1 - 1 / s) = (s - 1) / s := by field_simp
  rw [hfac] at hfinal
  have hmul : ((s - 1) / s) * pronicNorm T v ^ 2 ≤ (s / (s - 1)) * dilationStepEnergy q T v :=
    hfinal
  have hpos : (0 : ℝ) < (s - 1) / s := by positivity
  have := (div_le_div_iff_of_pos_right hpos).mpr
  calc pronicNorm T v ^ 2
      = (((s - 1) / s) * pronicNorm T v ^ 2) / ((s - 1) / s) := by
        field_simp
    _ ≤ ((s / (s - 1)) * dilationStepEnergy q T v) / ((s - 1) / s) := by
        exact div_le_div_of_nonneg_right hmul hpos
    _ = (s ^ 2 / (s - 1) ^ 2) * dilationStepEnergy q T v := by
        field_simp; ring

/-- The reverse comparison: the dilation step energy is bounded by the pronic energy. -/
theorem dilationStepEnergy_le {q : ℕ} (hq : 1 ≤ q) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    dilationStepEnergy q T v ≤ (2 * (1 + 1 / (q : ℝ))) * pronicNorm T v ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hcontr := pronicNorm_rowDilate_sq_le hq T v hv0
  have hsplit : dilationStepEnergy q T v ≤
      2 * pronicNorm T v ^ 2 + 2 * pronicNorm T (rowDilate q v) ^ 2 := by
    rw [dilationStepEnergy, pronicNorm_sq, pronicNorm_sq, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hw : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
    rw [div_add_div_same, div_le_div_iff_of_pos_right hw]
    have : (v n - v (n / q)) ^ 2 ≤ 2 * v n ^ 2 + 2 * v (n / q) ^ 2 := by
      nlinarith [sq_nonneg (v n + v (n / q))]
    simpa [rowDilate] using this
  have : 2 * pronicNorm T (rowDilate q v) ^ 2 ≤
      2 * ((1 / (q : ℝ)) * pronicNorm T v ^ 2) := by linarith
  nlinarith [hsplit, this]

/-! ## §3. The receiver as a block energy -/

/-- The dilation step of a centred prefix is the centred sum over the top block. -/
theorem pmPowerDampedCenteredDivisorPrefix_sub_eq_blockSum (ε : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    pmPowerDampedCenteredDivisorPrefix ε n - pmPowerDampedCenteredDivisorPrefix ε m =
      ∑ j ∈ Ioc m n, pmPowerDampedCenteredDivisorCoeff ε j := by
  have h := Finset.sum_Ioc_consecutive (fun j => pmPowerDampedCenteredDivisorCoeff ε j)
    (Nat.zero_le m) hmn
  have hIcc : ∀ k : ℕ, (Icc 1 k : Finset ℕ) = Ioc 0 k := by
    intro k; ext x; rw [mem_Icc, mem_Ioc]; omega
  rw [pmPowerDampedCenteredDivisorPrefix, pmPowerDampedCenteredDivisorPrefix, hIcc, hIcc]
  linarith [h]

/-- The **block energy** of the source: the pronic mean square of the centred divisor sums over the
top blocks `(n/q, n]`. -/
def dampedBlockEnergy (q : ℕ) (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T,
    (∑ j ∈ Ioc (n / q) n, pmPowerDampedCenteredDivisorCoeff ε j) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))

theorem dampedBlockEnergy_eq_dilationStepEnergy (q : ℕ) (ε : ℝ) (T : ℕ) :
    dampedBlockEnergy q ε T =
      dilationStepEnergy q T (pmPowerDampedCenteredDivisorPrefix ε) := by
  rw [dampedBlockEnergy, dilationStepEnergy]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← pmPowerDampedCenteredDivisorPrefix_sub_eq_blockSum ε (Nat.div_le_self n q)]

theorem dampedMobiusEnergy_eq_pronicNorm_sq (ε : ℝ) (T : ℕ) :
    dampedMobiusEnergy ε T = pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) ^ 2 := by
  rw [pronicNorm_sq]
  rfl

/-- **The receiver is bounded by the block energy.**  The long prefix of the open obligation is
replaced by one localized block at every scale, at the explicit cost `q/(√q − 1)²`. -/
theorem dampedMobiusEnergy_le_blockEnergy {q : ℕ} (hq : 2 ≤ q) (ε : ℝ) (T : ℕ) :
    dampedMobiusEnergy ε T ≤
      ((q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2) * dampedBlockEnergy q ε T := by
  rw [dampedMobiusEnergy_eq_pronicNorm_sq, dampedBlockEnergy_eq_dilationStepEnergy]
  exact pronicNorm_sq_le_dilationStepEnergy hq T _ (pmPowerDampedCenteredDivisorPrefix_zero ε)

/-- The reverse comparison for the source: the block energy never exceeds the receiver. -/
theorem dampedBlockEnergy_le {q : ℕ} (hq : 1 ≤ q) (ε : ℝ) (T : ℕ) :
    dampedBlockEnergy q ε T ≤ (2 * (1 + 1 / (q : ℝ))) * dampedMobiusEnergy ε T := by
  rw [dampedBlockEnergy_eq_dilationStepEnergy, dampedMobiusEnergy_eq_pronicNorm_sq]
  exact dilationStepEnergy_le hq T _ (pmPowerDampedCenteredDivisorPrefix_zero ε)

/-- **Admission from the block energy.** -/
theorem admits_of_bounded_blockEnergy {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} {B : ℝ}
    (h : ∀ T : ℕ, dampedBlockEnergy q ε T ≤ B) :
    Admits dampedMobiusEnergy ε := by
  refine ⟨((q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2) * B, fun T => ?_⟩
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hs1 : 1 < Real.sqrt (q : ℝ) := by
    have : Real.sqrt 1 < Real.sqrt (q : ℝ) := by
      apply Real.sqrt_lt_sqrt (by norm_num); linarith
    simpa using this
  have hcpos : (0 : ℝ) ≤ (q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2 := by
    have : (0 : ℝ) < Real.sqrt (q : ℝ) - 1 := by linarith
    positivity
  exact (dampedMobiusEnergy_le_blockEnergy hq ε T).trans
    (mul_le_mul_of_nonneg_left (h T) hcpos)

/-- **The Riemann hypothesis from block cancellation.**  A horizon-uniform bound on the pronic mean
square of the centred divisor sums over the top blocks, at dampings accumulating at zero, is the
Riemann hypothesis. -/
theorem riemannHypothesis_of_cofinal_bounded_blockEnergy {q : ℕ} (hq : 2 ≤ q)
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, dampedBlockEnergy q ε T ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  obtain ⟨ε, hε, hεδ, B, hB⟩ := h δ hδ
  exact ⟨ε, hε, hεδ, admits_of_bounded_blockEnergy hq hB⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
