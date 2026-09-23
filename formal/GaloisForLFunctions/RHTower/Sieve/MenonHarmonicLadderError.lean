import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderOnHM
import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect

/-!
# Global support error for Menon's harmonic Ramaré ladder

The moving cofactor support must be replaced once for the whole geometric ladder, not once in
every block after Cauchy--Schwarz.  The resulting defect is a single prime-shifted Dirichlet
polynomial.  Its coefficients retain both reciprocal factors, `1 / p` and `1 / m`, and therefore
have size at most `(1 + eta) / A₀` on the dyadic source shell.

This is the harmonic analogue of `ramareLadderError`.  It reuses the exact two-sided gap geometry
from `LadderProductDefect` and pays one divisor-overlap count and one total gap cardinality.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-! ## A varying-coefficient overlap bound -/

/-- The prime-shift family mean square with a coefficient bound required only on each displayed
support.  This is the varying-coefficient version needed when the harmonic factor `1 / p` depends
on the outer prime. -/
theorem integral_Icc_normSq_sum_logPoly_le_support_bound
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (a : ι → ℕ → ℂ) (S : ι → Finset ℕ) {N : ℕ}
    (hSN : ∀ i ∈ I, S i ⊆ Finset.Icc 1 N) {K W Omega : ℝ}
    (hOmega : 0 < Omega)
    (ha : ∀ i ∈ I, ∀ n ∈ S i, ‖a i n‖ ≤ Omega)
    (hK0 : 0 ≤ K)
    (hK : ∀ n ∈ Finset.Icc 1 N,
      ((I.filter (fun i => n ∈ S i)).card : ℝ) ≤ K)
    (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, logPoly (a i) (S i) w‖ ^ (2 : ℕ))
      ≤ Omega ^ (2 : ℕ) *
          ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) *
            (K * ∑ i ∈ I, ((S i).card : ℝ))) := by
  classical
  let b : ι → ℕ → ℂ := fun i n =>
    if i ∈ I ∧ n ∈ S i then a i n / (Omega : ℂ) else 0
  have hb : ∀ i n, ‖b i n‖ ≤ 1 := by
    intro i n
    by_cases hi : i ∈ I
    · by_cases hn : n ∈ S i
      · simp only [b, hi, hn, and_self, if_true]
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hOmega, div_le_one hOmega]
        exact ha i hi n hn
      · simp only [b, hi, hn, and_false, if_false, norm_zero]
        norm_num
    · simp only [b, hi, false_and, if_false, norm_zero]
      norm_num
  have hbase := integral_Icc_normSq_sum_logPoly_le I b S hSN hb hK0 hK hW
  have hpoly : ∀ i ∈ I, ∀ w : ℝ,
      logPoly (b i) (S i) w = logPoly (a i) (S i) w / (Omega : ℂ) := by
    intro i hi w
    rw [logPoly, logPoly, Finset.sum_div]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [b, hi, hn, and_self, if_true]
    ring
  have hrep : ∀ w : ℝ,
      ‖∑ i ∈ I, logPoly (b i) (S i) w‖ ^ (2 : ℕ) =
        ‖∑ i ∈ I, logPoly (a i) (S i) w‖ ^ (2 : ℕ) / Omega ^ (2 : ℕ) := by
    intro w
    have hsum : (∑ i ∈ I, logPoly (b i) (S i) w) =
        (∑ i ∈ I, logPoly (a i) (S i) w) / (Omega : ℂ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i hi => hpoly i hi w
    rw [hsum, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hOmega, div_pow]
  have hint :
      (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, logPoly (b i) (S i) w‖ ^ (2 : ℕ)) =
        (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, logPoly (a i) (S i) w‖ ^ (2 : ℕ)) /
          Omega ^ (2 : ℕ) := by
    rw [← MeasureTheory.integral_div]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => hrep w
  rw [hint, div_le_iff₀ (by positivity)] at hbase
  have hcards :
      (∑ i ∈ I, (((S i) ∩ Finset.Icc 1 N).card : ℝ)) =
        ∑ i ∈ I, ((S i).card : ℝ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.inter_eq_left.2 (hSN i hi)]
  rw [hcards] at hbase
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hbase

/-! ## Harmonic prime shifting -/

/-- Coefficients obtained by multiplying a polynomial by the harmonic Möbius phase of `p`. -/
def harmonicPrimeShiftCoeff (p : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  primeShiftCoeff p (fun m => c m / (p : ℂ)) n

/-- Multiplication by a harmonic prime phase shifts the support and retains the factor `1 / p`. -/
theorem harmonicMoebiusPhase_mul_logPoly {p : ℕ} (hp : 0 < p)
    (c : ℕ → ℂ) {S : Finset ℕ} (hS : ∀ m ∈ S, 0 < m) (w : ℝ) :
    harmonicMoebiusPhase w p * logPoly c S w =
      logPoly (harmonicPrimeShiftCoeff p c) (S.image (fun m => p * m)) w := by
  have hshift := moebiusPhase_mul_logPoly hp (fun m => c m / (p : ℂ)) hS w
  rw [harmonicMoebiusPhase]
  change moebiusPhase w p / (p : ℂ) * logPoly c S w =
    logPoly (primeShiftCoeff p (fun m => c m / (p : ℂ)))
      (S.image (fun m => p * m)) w
  calc
    moebiusPhase w p / (p : ℂ) * logPoly c S w =
        moebiusPhase w p * logPoly (fun m => c m / (p : ℂ)) S w := by
          have hscale : logPoly (fun m => c m / (p : ℂ)) S w =
              logPoly c S w / (p : ℂ) := by
            rw [logPoly, logPoly, Finset.sum_div]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
          rw [hscale]
          ring
    _ = logPoly (primeShiftCoeff p (fun m => c m / (p : ℂ)))
          (S.image (fun m => p * m)) w := hshift

/-! ## Exact global harmonic defect -/

/-- Ladder of genuine harmonic prime/cofactor products. -/
def harmonicLadderProductPoly
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ j ∈ Finset.range L,
    harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
      logPoly (harmonicRamareCofactorCoeff P) (geomCofactorBlockAt A₀ B₀ Q eta j) w

/-- Single global discrepancy between moving harmonic cofactor supports and common block supports. -/
def harmonicLadderProductDefect
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ x ∈ ladderIndex P Q eta L,
    harmonicMoebiusPhase w x.2 *
      logPoly (harmonicRamareCofactorCoeff P) (ladderGapSetAt A₀ B₀ Q eta x) w

theorem continuous_harmonicLadderProductPoly
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (L : ℕ) :
    Continuous (harmonicLadderProductPoly P A₀ B₀ Q eta L) := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact (continuous_harmonicPrimeBlockPoly _).mul (continuous_logPoly _ _)

theorem continuous_harmonicLadderProductDefect
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (L : ℕ) :
    Continuous (harmonicLadderProductDefect P A₀ B₀ Q eta L) := by
  refine continuous_finsetSum _ fun x _ => ?_
  exact ((continuous_moebiusPhase x.2).div_const _).mul (continuous_logPoly _ _)

/-- Exact global replacement identity.  The moving-support discrepancy is formed before any
Cauchy--Schwarz over ladder steps. -/
theorem harmonicLadderProductPoly_sub_harmonicRamareBilinear_eq
    {P : Finset ℕ} (A₀ B₀ : ℕ) {Q eta : ℝ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (w : ℝ) :
    harmonicLadderProductPoly P A₀ B₀ Q eta L w -
        harmonicRamareBilinear P (Finset.Icc A₀ B₀) w =
      harmonicLadderProductDefect P A₀ B₀ Q eta L w := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + eta := by linarith
  have hbil : harmonicRamareBilinear P (Finset.Icc A₀ B₀) w =
      ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + eta) j,
        harmonicMoebiusPhase w p *
          logPoly (harmonicRamareCofactorCoeff P)
            {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w := by
    rw [harmonicRamareBilinear_eq_sum_blocks w (Finset.range L)
      (geomBlock P Q (1 + eta))
      (geomBlock_pairwiseDisjoint P hQ hr1 L)
      (geomBlock_biUnion_eq P Q (1 + eta) hL hP)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [harmonicRamareBlock, harmonicRamareCofactorPoly]
  have hprod : harmonicLadderProductPoly P A₀ B₀ Q eta L w =
      ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + eta) j,
        harmonicMoebiusPhase w p *
          logPoly (harmonicRamareCofactorCoeff P) (geomCofactorBlockAt A₀ B₀ Q eta j) w := by
    rw [harmonicLadderProductPoly]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [harmonicPrimeBlockPoly, Finset.sum_mul]
  rw [hprod, hbil, ← Finset.sum_sub_distrib, harmonicLadderProductDefect,
    ladderIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  set Qj : ℝ := Q * (1 + eta) ^ j with hQj
  have hQj0 : (0 : ℝ) < Qj := by
    rw [hQj]
    have : (0 : ℝ) < (1 + eta) ^ j := by positivity
    positivity
  have hprime := hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hrange : Qj < (p : ℝ) ∧ (p : ℝ) ≤ Qj * (1 + eta) := by
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    refine ⟨hlo, ?_⟩
    have hpow : Q * (1 + eta) ^ (j + 1) = Qj * (1 + eta) := by
      rw [hQj, pow_succ]
      ring
    rwa [hpow] at hhi
  have hsub := cofactorFilter_subset_common_at (Q := Qj) (η := eta)
    A₀ B₀ hQj0 heta hprime.pos hrange.1 hrange.2
  have hUC : {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} \
      geomCofactorBlockAt A₀ B₀ Q eta j = ∅ := by
    rw [geomCofactorBlockAt, ← hQj]
    exact Finset.sdiff_eq_empty_iff_subset.2 hsub
  have hdiff :
      logPoly (harmonicRamareCofactorCoeff P) (geomCofactorBlockAt A₀ B₀ Q eta j) w -
          logPoly (harmonicRamareCofactorCoeff P)
            {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w =
        logPoly (harmonicRamareCofactorCoeff P) (ladderGapSetAt A₀ B₀ Q eta ⟨j, p⟩) w := by
    rw [logPoly_sub_eq_sdiff, hUC, ladderGapSetAt]
    simp [logPoly]
  rw [← mul_sub, hdiff]

/-! ## Closed mean-square budget for the global defect -/

/-- Explicit harmonic global-defect budget. -/
def menonHarmonicLadderErrorBudget
    (A₀ B₀ : ℕ) (Q eta W : ℝ) (L : ℕ) : ℝ :=
  ((1 + eta) / (A₀ : ℝ)) ^ (2 : ℕ) *
    ((5 * Real.pi / 2 * W +
        5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ)) *
      (Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) / Real.log Q *
        ∑ j ∈ Finset.range L, (Q * (1 + eta) ^ j * eta + 1) *
          (((A₀ : ℝ) + (B₀ : ℝ)) * eta / (Q * (1 + eta) ^ j) + 5 +
            (B₀ : ℝ) / (Q * (1 + eta) ^ j) ^ (2 : ℕ))))

/-- Reciprocal coefficient bound on every shifted gap support. -/
theorem norm_harmonicPrimeShiftCoeff_ladderGap_le
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime)
    {x : (_ : ℕ) × ℕ} (hx : x ∈ ladderIndex P Q eta L)
    {n : ℕ}
    (hn : n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) :
    ‖harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P) n‖ ≤
      (1 + eta) / (A₀ : ℝ) := by
  classical
  rw [Finset.mem_image] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  have hxmem := hx
  rw [ladderIndex, Finset.mem_sigma] at hxmem
  have hp := hPprime x.2 (geomBlock_subset P Q (1 + eta) x.1 hxmem.2)
  rw [harmonicPrimeShiftCoeff, primeShiftCoeff, if_pos ⟨m, rfl⟩]
  rw [Nat.mul_div_cancel_left m hp.pos]
  have hp0R : (0 : ℝ) < (x.2 : ℝ) := by exact_mod_cast hp.pos
  have hmC : m ∈ geomCofactorBlockAt A₀ B₀ Q eta x.1 :=
    (Finset.mem_sdiff.1 hm).1
  have hm0 := ladderGapSetAt_pos hA hQ heta x.1 hmC
  have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  set Qj : ℝ := Q * (1 + eta) ^ x.1 with hQj
  have hQj0 : (0 : ℝ) < Qj := by
    rw [hQj]
    have : (0 : ℝ) < (1 + eta) ^ x.1 := by positivity
    positivity
  have hpQ : Qj < (x.2 : ℝ) := by
    rw [geomBlock, Finset.mem_filter] at hxmem
    simpa [Qj] using hxmem.2.2.1
  have hmlo : (A₀ : ℝ) / (Qj * (1 + eta)) ≤ (m : ℝ) := by
    rw [geomCofactorBlockAt, Finset.mem_Icc] at hmC
    exact Nat.ceil_le.1 hmC.1
  have hAprod : (A₀ : ℝ) ≤ (x.2 : ℝ) * (m : ℝ) * (1 + eta) := by
    have hbase : (A₀ : ℝ) ≤ (m : ℝ) * (Qj * (1 + eta)) := by
      rwa [div_le_iff₀ (by positivity)] at hmlo
    have hgrow : (m : ℝ) * (Qj * (1 + eta)) ≤
        (x.2 : ℝ) * (m : ℝ) * (1 + eta) := by
      calc
        (m : ℝ) * (Qj * (1 + eta)) = Qj * (m : ℝ) * (1 + eta) := by ring
        _ ≤ (x.2 : ℝ) * (m : ℝ) * (1 + eta) := by gcongr
    exact hbase.trans hgrow
  have hmu : ‖((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)‖ ≤ 1 := by
    have hnorm : ‖((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)‖ =
        |((ArithmeticFunction.moebius x.2 : ℤ) : ℝ)| := by
      rw [show (((ArithmeticFunction.moebius x.2 : ℤ)) : ℂ) =
          ((((ArithmeticFunction.moebius x.2 : ℤ) : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    exact abs_moebius_real_le_one x.2
  have hcof := norm_harmonicRamareCofactorCoeff_le_inv P m
  have hdiv : ‖harmonicRamareCofactorCoeff P m / (x.2 : ℂ)‖ ≤
      1 / ((m : ℝ) * (x.2 : ℝ)) := by
    rw [norm_div, Complex.norm_natCast]
    calc
      ‖harmonicRamareCofactorCoeff P m‖ / (x.2 : ℝ) ≤
          (1 / (m : ℝ)) / (x.2 : ℝ) :=
        div_le_div_of_nonneg_right hcof hp0R.le
      _ = 1 / ((m : ℝ) * (x.2 : ℝ)) := by field_simp
  have hrecip : 1 / ((m : ℝ) * (x.2 : ℝ)) ≤ (1 + eta) / (A₀ : ℝ) := by
    have hA0R : (0 : ℝ) < (A₀ : ℝ) := by exact_mod_cast hA
    rw [div_le_div_iff₀ (mul_pos hm0R hp0R) hA0R]
    nlinarith [hAprod]
  rw [norm_mul]
  have hright := hdiv.trans hrecip
  nlinarith [norm_nonneg (((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)),
    norm_nonneg (harmonicRamareCofactorCoeff P m / (x.2 : ℂ)),
    show (0 : ℝ) ≤ (1 + eta) / (A₀ : ℝ) by positivity]

/-- Mean square of the global harmonic support defect.  One overlap count and one gap budget are
paid, while the dyadic harmonic normalization contributes `((1 + eta) / A₀)^(2 : ℕ)`. -/
theorem integral_Icc_normSq_harmonicLadderProductDefect_le_closed
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta W : ℝ} (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ)) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ)) ≤
        menonHarmonicLadderErrorBudget A₀ B₀ Q eta W L := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  set N : ℕ := ⌊(B₀ : ℝ) * (1 + eta)⌋₊ with hN
  set K : ℝ := Real.log (N : ℝ) / Real.log Q with hK
  set Omega : ℝ := (1 + eta) / (A₀ : ℝ) with hOmega
  have hOmega0 : 0 < Omega := by
    rw [hOmega]
    have hA0R : (0 : ℝ) < (A₀ : ℝ) := by exact_mod_cast hA
    positivity
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact div_nonneg (Real.log_natCast_nonneg N) hlogQ.le
  have hpos : ∀ x ∈ ladderIndex P Q eta L, 0 < x.2 := by
    intro x hx
    rw [ladderIndex, Finset.mem_sigma] at hx
    exact (hPprime x.2 (geomBlock_subset P Q (1 + eta) x.1 hx.2)).pos
  have hDpos : ∀ x ∈ ladderIndex P Q eta L,
      ∀ m ∈ ladderGapSetAt A₀ B₀ Q eta x, 0 < m := by
    intro x _ m hm
    exact ladderGapSetAt_pos hA hQ0 heta x.1 (Finset.mem_sdiff.1 hm).1
  have hDN : ∀ x ∈ ladderIndex P Q eta L,
      (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m) ⊆ Finset.Icc 1 N := by
    intro x hx n hn
    have hupper := ladderGapSetAt_image_subset A₀ B₀ hQ.le heta L x hx hn
    rw [Finset.mem_Icc] at hupper ⊢
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    exact ⟨Nat.mul_pos (hpos x hx) (hDpos x hx m hm), hupper.2⟩
  have hOverlap : ∀ n ∈ Finset.Icc 1 N,
      (((ladderIndex P Q eta L).filter (fun x =>
        n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))).card : ℝ) ≤ K := by
    intro n hn
    have hfirst := ladderIndex_filter_card_le_gen (P := P) hQ0 heta L
      (ladderGapSetAt A₀ B₀ Q eta) n
    have hsecond := card_designatedPrimes_dvd_le hQ hPprime hPge
      (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2
    exact hfirst.trans (by simpa [K, N] using hsecond)
  have hcoeff : ∀ x ∈ ladderIndex P Q eta L,
      ∀ n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m),
        ‖harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P) n‖ ≤ Omega := by
    intro x hx n hn
    simpa [Omega] using
      norm_harmonicPrimeShiftCoeff_ladderGap_le hA hQ0 heta hPprime hx hn
  have hrep : ∀ w : ℝ,
      harmonicLadderProductDefect P A₀ B₀ Q eta L w =
        ∑ x ∈ ladderIndex P Q eta L,
          logPoly (harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P))
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w := by
    intro w
    rw [harmonicLadderProductDefect]
    refine Finset.sum_congr rfl fun x hx => ?_
    exact harmonicMoebiusPhase_mul_logPoly (hpos x hx)
      (harmonicRamareCofactorCoeff P) (hDpos x hx) w
  have hcongr :
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ)) =
      ∫ w in Set.Icc (-W) W,
        ‖∑ x ∈ ladderIndex P Q eta L,
          logPoly (harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P))
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w‖ ^ (2 : ℕ) := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => by rw [hrep w]
  rw [hcongr]
  have hmain := integral_Icc_normSq_sum_logPoly_le_support_bound
    (ladderIndex P Q eta L)
    (fun x => harmonicPrimeShiftCoeff x.2 (harmonicRamareCofactorCoeff P))
    (fun x => (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))
    hDN hOmega0 hcoeff hK0 hOverlap hW
  refine hmain.trans ?_
  rw [menonHarmonicLadderErrorBudget]
  have hgap := sum_card_ladderGapSetAt_le (P := P) A₀ B₀ hQ0 heta L hPprime
  have himageCard : ∀ x ∈ ladderIndex P Q eta L,
      (((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)).card : ℝ) =
        ((ladderGapSetAt A₀ B₀ Q eta x).card : ℝ) := by
    intro x hx
    have hinj : Set.InjOn (fun m => x.2 * m)
        ((ladderGapSetAt A₀ B₀ Q eta x : Finset ℕ) : Set ℕ) := by
      intro m₁ _ m₂ _ heq
      exact Nat.eq_of_mul_eq_mul_left (hpos x hx) heq
    exact_mod_cast Finset.card_image_of_injOn hinj
  have hcards :
      (∑ x ∈ ladderIndex P Q eta L,
          (((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)).card : ℝ)) =
        ∑ x ∈ ladderIndex P Q eta L,
          ((ladderGapSetAt A₀ B₀ Q eta x).card : ℝ) := by
    exact Finset.sum_congr rfl himageCard
  rw [hcards]
  dsimp only [Omega, K, N] at hmain ⊢
  have hmean0 : 0 ≤ 5 * Real.pi / 2 * W +
      5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) := by positivity
  have hscale0 : 0 ≤ ((1 + eta) / (A₀ : ℝ)) ^ (2 : ℕ) := sq_nonneg _
  have hKnonneg : 0 ≤ Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) /
      Real.log Q := div_nonneg (Real.log_natCast_nonneg _) hlogQ.le
  have hgapK := mul_le_mul_of_nonneg_left hgap hKnonneg
  have hmean := mul_le_mul_of_nonneg_left hgapK hmean0
  exact mul_le_mul_of_nonneg_left hmean hscale0

/-! ## Global ladder assembly on a frequency set -/

/-- Harmonic Ramaré bilinear mean square with product blocks and one global support defect. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_ladder_error
    {P : Finset ℕ} (A₀ B₀ : ℕ) {Q eta W : ℝ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ)) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (∫ w in E,
          ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
            logPoly (harmonicRamareCofactorCoeff P)
              (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ (2 : ℕ)) +
      2 * ∫ w in E, ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ) := by
  classical
  set F : ℕ → ℝ → ℂ := fun j w =>
    harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
      logPoly (harmonicRamareCofactorCoeff P) (geomCofactorBlockAt A₀ B₀ Q eta j) w
  have hcontF : ∀ j : ℕ, Continuous fun w : ℝ => ‖F j w‖ ^ (2 : ℕ) := fun j =>
    (((continuous_harmonicPrimeBlockPoly _).mul (continuous_logPoly _ _)).norm).pow 2
  have hcontD : Continuous fun w : ℝ =>
      ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ) :=
    (continuous_harmonicLadderProductDefect P A₀ B₀ Q eta L).norm.pow 2
  have hdec : ∀ w : ℝ, harmonicRamareBilinear P (Finset.Icc A₀ B₀) w =
      (∑ j ∈ Finset.range L, F j w) +
        (-(harmonicLadderProductDefect P A₀ B₀ Q eta L w)) := by
    intro w
    have h := harmonicLadderProductPoly_sub_harmonicRamareBilinear_eq
      A₀ B₀ hQ heta hL hPprime hP w
    dsimp only [F]
    rw [← harmonicLadderProductPoly]
    linear_combination -h
  have hpt : ∀ w : ℝ,
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ) ≤
        2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ)) +
          2 * ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ) := by
    intro w
    rw [hdec w]
    have hsum : ‖∑ j ∈ Finset.range L, F j w‖ ^ (2 : ℕ) ≤
        (L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ) := by
      have h1 : ‖∑ j ∈ Finset.range L, F j w‖ ≤
          ∑ j ∈ Finset.range L, ‖F j w‖ := norm_sum_le _ _
      have h2 : (∑ j ∈ Finset.range L, ‖F j w‖) ^ (2 : ℕ) ≤
          ((Finset.range L).card : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ) :=
        sq_sum_le_card_mul_sum_sq
      rw [Finset.card_range] at h2
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    have htri := norm_add_le (∑ j ∈ Finset.range L, F j w)
      (-(harmonicLadderProductDefect P A₀ B₀ Q eta L w))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    rw [norm_neg] at hsq
    nlinarith [hsq, hsum,
      sq_nonneg (‖∑ j ∈ Finset.range L, F j w‖ -
        ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖)]
  have hcontZ : Continuous fun w : ℝ =>
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ) := by
    refine (continuous_finsetSum P fun p _ => ?_).norm.pow 2
    exact (((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _))
  have hcontR : Continuous fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ)) +
        2 * ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ) :=
    (((continuous_finsetSum _ fun j _ => hcontF j).const_mul _).const_mul 2).add
      (hcontD.const_mul 2)
  have hintZ : IntegrableOn (fun w : ℝ =>
      ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ)) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn (fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ)) +
        2 * ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ)) E volume :=
    (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintF : ∀ j ∈ Finset.range L,
      IntegrableOn (fun w : ℝ => ‖F j w‖ ^ (2 : ℕ)) E volume := fun j _ =>
    ((hcontF j).integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintSum : IntegrableOn (fun w : ℝ =>
      ∑ j ∈ Finset.range L, ‖F j w‖ ^ (2 : ℕ)) E volume :=
    ((continuous_finsetSum _ fun j _ => hcontF j).integrableOn_Icc
      (a := -W) (b := W)).mono_set hEs
  have hintD : IntegrableOn (fun w : ℝ =>
      ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ)) E volume :=
    (hcontD.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hintZ hintR hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add ((hintSum.const_mul _).const_mul 2) (hintD.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul,
    MeasureTheory.integral_finsetSum _ hintF]
  ring

/-- Same global ladder bound with the harmonic support defect replaced by its closed budget. -/
theorem setIntegral_normSq_harmonicRamareBilinear_le_ladder_closed
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta W : ℝ} (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖harmonicRamareBilinear P (Finset.Icc A₀ B₀) w‖ ^ (2 : ℕ)) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (∫ w in E,
          ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
            logPoly (harmonicRamareCofactorCoeff P)
              (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ (2 : ℕ)) +
      2 * menonHarmonicLadderErrorBudget A₀ B₀ Q eta W L := by
  have hbase := setIntegral_normSq_harmonicRamareBilinear_le_ladder_error
    (P := P) A₀ B₀ (lt_trans zero_lt_one hQ) heta hL hPprime hP hEm hEs
  have hcont : Continuous fun w : ℝ =>
      ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ) :=
    (continuous_harmonicLadderProductDefect P A₀ B₀ Q eta L).norm.pow 2
  have hmono : (∫ w in E,
      ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ)) ≤
      ∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefect P A₀ B₀ Q eta L w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_mono_set
      (hcont.integrableOn_Icc (a := -W) (b := W))
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall hEs)
  have herr := hmono.trans
    (integral_Icc_normSq_harmonicLadderProductDefect_le_closed
      hA hQ heta hW hPprime (fun p hp => (hP p hp).1.le))
  exact hbase.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left herr (by norm_num)))

end

end RHTower.Sieve
