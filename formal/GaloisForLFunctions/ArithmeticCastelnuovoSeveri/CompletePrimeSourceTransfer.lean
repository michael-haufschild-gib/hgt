import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogarithmicCellSourceTransfer
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothLogarithmicCellRefinement
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# Complete prime-source transfer through logarithmic cells

Every signed real compact `C²` profile is recovered by complete logarithmic cell sections.
The full prime series of their actual quadratic `L²` energies converges to the prime term
of the Weil form at order `1/N`. Arithmetic divisibility forms have the same limit.
For mixed profiles, the proof pays both the signed successor contribution and the
logarithmic quadrature error; compact support derives one common finite prime horizon.
-/

noncomputable section
open Finset MeasureTheory Filter Topology
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

/-- The full directed prime pairing of two real source profiles. Symmetrization gives the
mixed prime form; on the diagonal the two directions agree. -/
def smoothPrimePair (f g : ℝ → ℝ) : ℝ :=
  ∑' m : ℕ, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    ∫ u, f u * g (u + Real.log m)

/-- The quadratic prime pairing of one actual cell-section vector. -/
def cellPrimeEnergy (c : ℕ → ℝ) (A X : ℕ) : ℝ :=
  ∑' m : ℕ, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    (inner ℂ (_root_.RHTower.halfLineRightShift (Real.log m) (cellSection c A X))
      (cellSection c A X)).re

/-- Clipping introduces no extra section below the first occupied cell. -/
theorem cellSection_logSamples_eq (f : ℝ → ℝ) (R : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (X : ℕ) (hf0 : f (-R) = 0) :
    cellSection (logSamples f R N) 1 X = cellSection (logSamples f R N) N X := by
  unfold cellSection
  symm
  apply sum_subset (Icc_subset_Icc_left hN)
  intro a ha hnot
  have haN : a < N := by simp only [mem_Icc] at ha hnot; omega
  simp only [logSamples, max_eq_right haN.le, sub_self, zero_sub, hf0,
    Complex.ofReal_zero, zero_smul]

theorem fullPrimeSectionPair_self_logSamples (f : ℝ → ℝ) (R : ℝ) {N : ℕ}
    (hN : 1 ≤ N) (X : ℕ) (hf0 : f (-R) = 0) :
    fullPrimeSectionPair (logSamples f R N) (logSamples f R N) N X =
      cellPrimeEnergy (logSamples f R N) N X := by
  unfold fullPrimeSectionPair cellPrimeEnergy
  rw [cellSection_logSamples_eq f R hN X hf0]

/-- On the diagonal the directed source is precisely the prime term of the Weil form. -/
theorem smoothPrimePair_self_eq_primeSum (f : ℝ → ℝ) :
    smoothPrimePair f f = _root_.RHTower.primeSum f := by
  unfold smoothPrimePair _root_.RHTower.primeSum
  apply tsum_congr
  intro m
  have hshift : (∫ u, f u * f (u - Real.log m)) = ∫ u, f u * f (u + Real.log m) := by
    have h : (∫ u : ℝ, f (u - Real.log m) * f ((u - Real.log m) + Real.log m)) =
        ∫ u : ℝ, f u * f (u + Real.log m) :=
      integral_sub_right_eq_self (fun u => f u * f (u + Real.log m)) (Real.log m)
    simpa only [sub_add_cancel, mul_comm] using h
  rw [hshift, _root_.RHTower.vonMangoldtAtom]
  by_cases hm : 2 ≤ m
  · rw [if_pos hm]
    ring
  · rw [if_neg hm]
    have h01 : m = 0 ∨ m = 1 := by omega
    rcases h01 with rfl | rfl <;> simp

/-- Compact source support removes every prime lag beyond its multiplicative span. -/
theorem smoothPrimePair_eq_sum (f g : ℝ → ℝ) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0 ∧ g u = 0) :
    smoothPrimePair f g = ∑ m ∈ Icc 1 B,
      (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) * ∫ u, f u * g (u + Real.log m) := by
  unfold smoothPrimePair
  apply tsum_eq_sum
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hBm : B < m := by simp only [mem_Icc] at hm; omega
    have hlog : Real.log B < Real.log m :=
      Real.log_lt_log (by exact_mod_cast (by omega : 0 < B)) (by exact_mod_cast hBm)
    have hz : ∀ u, f u * g (u + Real.log m) = 0 := by
      intro u
      by_cases hu : u ≤ -R
      · rw [(hs u (Or.inl hu)).1, zero_mul]
      · rw [(hs (u + Real.log m) (Or.inr (by linarith only [hu, hlog]))).2, mul_zero]
    simp only [hz, integral_zero, mul_zero]

/-- The divisibility spine samples the literal smooth mixed correlation at cell endpoints. -/
theorem cellSpine_logSamples_eq (f g : ℝ → ℝ) (R : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (B : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    cellSpine (logSamples f R N) (logSamples g R N) N (N * B) m =
      ∑ a ∈ Icc N (N * B), logCellWidth a *
        (f (logEndpoint R N a) * g (logEndpoint R N a + Real.log m)) := by
  unfold cellSpine
  apply sum_congr rfl
  intro a ha
  have hNa := (mem_Icc.mp ha).1
  have ha1 := hN.trans hNa
  have hNam : N ≤ a * m := hNa.trans (by simpa using Nat.mul_le_mul_left a hm)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  simp only [logSamples, max_eq_left hNa, max_eq_left hNam, logEndpoint, Nat.cast_mul,
    Real.log_mul ha0.ne' hm0.ne']
  rw [show Real.log a + Real.log m - Real.log N - R =
    (Real.log a - Real.log N - R) + Real.log m by ring]
  ring

/-- The signed prime divisibility sums converge to the full smooth-source pairing. -/
theorem exists_primeSpine_source_rate {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f)
    (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0 ∧ g u = 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      |primeCellSpine (logSamples f R N) (logSamples g R N) N (N * B) B -
        smoothPrimePair f g| ≤ D / N := by
  have hmod : ∀ m : ℕ, ∃ K : NNReal,
      LipschitzWith K (fun u => f u * g (u + Real.log m)) := by
    intro m
    apply _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz
    · exact hf.mul (hg.comp (contDiff_id.add contDiff_const))
    · exact hfc.mul_right
  choose K hK using hmod
  let w : ℕ → ℝ := fun m => 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m
  have hw : ∀ m, 0 ≤ w m := fun m => div_nonneg
    (mul_nonneg (by norm_num) (ArithmeticFunction.vonMangoldt_nonneg (n := m))) (Real.sqrt_nonneg m)
  refine ⟨∑ m ∈ Icc 1 B, w m * ((B : ℝ) * (K m : ℝ)),
    sum_nonneg (fun m _ => mul_nonneg (hw m) (by positivity)), fun N hN => ?_⟩
  rw [smoothPrimePair_eq_sum f g R hB hs]
  unfold primeCellSpine
  rw [← sum_sub_distrib, sum_div]
  calc _ ≤ ∑ m ∈ Icc 1 B,
        |w m * cellSpine (logSamples f R N) (logSamples g R N) N (N * B) m -
          w m * ∫ u, f u * g (u + Real.log m)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Icc 1 B, w m * ((B : ℝ) * (K m : ℝ)) / N := by
      apply sum_le_sum
      intro m hm
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw m),
        cellSpine_logSamples_eq f g R hN B (mem_Icc.mp hm).1]
      have hq := abs_logQuadrature_sub_integral_le (hK m) R hN hB
        (fun u hu => by rw [(hs u hu).1, zero_mul])
      have hb := mul_le_mul_of_nonneg_left hq (hw m)
      simpa only [← mul_div_assoc] using hb

/-- Every compact `C²` pair is recovered by complete logarithmic cell sections. The rate
pays both the signed successor terms and the smooth-source quadrature error. -/
theorem exists_complete_primeSource_rate {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧ ∃ D : ℝ, 0 ≤ D ∧
      (f (-R) = 0 ∧ g (-R) = 0) ∧ ∀ N : ℕ, 1 ≤ N →
        |fullPrimeSectionPair (logSamples f R N) (logSamples g R N) N (N * B) -
          smoothPrimePair f g| ≤ D / N := by
  obtain ⟨R, hR, B, hB, C, hC, hs, hc⟩ := exists_compact_logSamples_rate hf hg hfc hgc
  obtain ⟨D, hD, hd⟩ := exists_primeSpine_source_rate hf hg hfc R hB hs
  refine ⟨R, hR, B, hB, C + D, add_nonneg hC hD, hs (-R) (Or.inl le_rfl), fun N hN => ?_⟩
  rw [fullPrimeSectionPair_eq _ _ hN (N * B) hB le_rfl
    (logSamples_eq_zero_above R hN hB (fun u hu => (hs u (Or.inr hu.le)).2))]
  have hsplit := abs_add_le
    (primeSectionPair (logSamples f R N) (logSamples g R N) N (N * B) B -
      primeCellSpine (logSamples f R N) (logSamples g R N) N (N * B) B)
    (primeCellSpine (logSamples f R N) (logSamples g R N) N (N * B) B - smoothPrimePair f g)
  rw [sub_add_sub_cancel, primeSectionPair_sub_spine _ _ hN (N * B) B
    (logSamples_eq_zero_above R hN hB (fun u hu => (hs u (Or.inr hu.le)).2))] at hsplit
  calc _ ≤ |primeCellRemainder (logSamples f R N) (logSamples g R N) N (N * B) B| +
        |primeCellSpine (logSamples f R N) (logSamples g R N) N (N * B) B - smoothPrimePair f g| := hsplit
    _ ≤ C / N + D / N := add_le_add (hc N hN) (hd N hN)
    _ = (C + D) / N := by ring

private theorem tendsto_of_div_rate {F : ℕ → ℝ} {a D : ℝ}
    (hbound : ∀ N : ℕ, 1 ≤ N → |F N - a| ≤ D / N) : Tendsto F atTop (𝓝 a) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    _ (tendsto_const_div_atTop_nhds_zero_nat D)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact hbound N hN

/-- The arithmetic divisibility forms themselves recover every compact smooth prime source. -/
theorem exists_tendsto_primeSpine {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun N : ℕ => primeCellSpine (logSamples f R N) (logSamples g R N) N (N * B) B)
        atTop (𝓝 (smoothPrimePair f g)) := by
  obtain ⟨R, hR, B, hB, _C, _hC, hs, _hc⟩ := exists_compact_logSamples_rate hf hg hfc hgc
  obtain ⟨_D, _hD, hd⟩ := exists_primeSpine_source_rate hf hg hfc R hB hs
  exact ⟨R, hR, B, hB, tendsto_of_div_rate hd⟩

/-- Full prime source transfer holds for arbitrary signed compact `C²` profiles. -/
theorem exists_tendsto_complete_primeSource {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun N : ℕ => fullPrimeSectionPair (logSamples f R N) (logSamples g R N) N (N * B))
        atTop (𝓝 (smoothPrimePair f g)) := by
  obtain ⟨R, hR, B, hB, _D, _hD, _hzero, hbound⟩ := exists_complete_primeSource_rate hf hg hfc hgc
  exact ⟨R, hR, B, hB, tendsto_of_div_rate hbound⟩

/-- The exact Weil prime term is a limit of arithmetic divisibility forms. -/
theorem exists_tendsto_divisibility_primeSum {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun N : ℕ => primeCellSpine (logSamples f R N) (logSamples f R N) N (N * B) B)
        atTop (𝓝 (_root_.RHTower.primeSum f)) := by
  simpa only [smoothPrimePair_self_eq_primeSum] using
    exists_tendsto_primeSpine hf hf hfc hfc

/-- The actual quadratic cell prime energy recovers the original Weil prime term at
order `1/N`, with its complete prime series retained. -/
theorem exists_complete_primeSum_rate {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ N : ℕ, 1 ≤ N →
        |cellPrimeEnergy (logSamples f R N) N (N * B) - _root_.RHTower.primeSum f| ≤ D / N := by
  obtain ⟨R, hR, B, hB, D, hD, hzero, hbound⟩ := exists_complete_primeSource_rate hf hf hfc hfc
  refine ⟨R, hR, B, hB, D, hD, fun N hN => ?_⟩
  have h := hbound N hN
  rwa [fullPrimeSectionPair_self_logSamples f R hN (N * B) hzero.1,
    smoothPrimePair_self_eq_primeSum] at h

/-- Complete quadratic cell sections recover the exact prime term in the Weil form. -/
theorem exists_tendsto_complete_primeSum {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧
      Tendsto (fun N : ℕ => cellPrimeEnergy (logSamples f R N) N (N * B))
        atTop (𝓝 (_root_.RHTower.primeSum f)) := by
  obtain ⟨R, hR, B, hB, _D, _hD, hbound⟩ := exists_complete_primeSum_rate hf hfc
  exact ⟨R, hR, B, hB, tendsto_of_div_rate hbound⟩

#print axioms exists_tendsto_primeSpine
#print axioms exists_complete_primeSource_rate
#print axioms exists_complete_primeSum_rate
#print axioms exists_tendsto_divisibility_primeSum
#print axioms exists_tendsto_complete_primeSum
#print axioms exists_tendsto_complete_primeSource
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
