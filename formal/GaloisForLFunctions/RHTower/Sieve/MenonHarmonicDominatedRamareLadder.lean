import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicMaskedRamare
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicExternalFrequencyAssembly
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFullLadderError

/-!
# Harmonic Ramaré ladders with a dominated cofactor coefficient

The final Ramaré range in Menon's two-range argument acts on a coefficient already projected by
the initial range.  Its cofactor coefficient is not definitionally the unmasked harmonic cofactor,
but it is pointwise bounded by the same reciprocal envelope.  This module makes the ladder,
global support defect, reciprocal Halász--Montgomery product estimate, and external threshold
assembly uniform in any cofactor coefficient satisfying `‖c m‖ ≤ 1/m`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Harmonic Ramaré bilinear form with an arbitrary damped cofactor coefficient. -/
def harmonicRamareBilinearWithCoeff
    (P s : Finset ℕ) (c : ℕ → ℂ) (w : ℝ) : ℂ :=
  ∑ p ∈ P, harmonicMoebiusPhase w p *
    logPoly c {m ∈ ramareCofactorSet s p | ¬ p ∣ m} w

/-- Geometric ladder of harmonic prime products with an arbitrary cofactor coefficient. -/
def harmonicLadderProductPolyWithCoeff
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (L : ℕ)
    (c : ℕ → ℂ) (w : ℝ) : ℂ :=
  ∑ j ∈ Finset.range L,
    harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
      logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w

/-- One global moving-support defect for an arbitrary cofactor coefficient. -/
def harmonicLadderProductDefectWithCoeff
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (L : ℕ)
    (c : ℕ → ℂ) (w : ℝ) : ℂ :=
  ∑ x ∈ ladderIndex P Q eta L,
    harmonicMoebiusPhase w x.2 * logPoly c (ladderGapSetAt A₀ B₀ Q eta x) w

theorem continuous_harmonicRamareBilinearWithCoeff
    (P s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (harmonicRamareBilinearWithCoeff P s c) := by
  refine continuous_finsetSum _ fun p _ => ?_
  exact ((continuous_moebiusPhase p).div_const _).mul (continuous_logPoly _ _)

theorem continuous_harmonicLadderProductDefectWithCoeff
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (L : ℕ) (c : ℕ → ℂ) :
    Continuous (harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c) := by
  refine continuous_finsetSum _ fun x _ => ?_
  exact ((continuous_moebiusPhase x.2).div_const _).mul (continuous_logPoly _ _)

/-- The masked final bilinear is the coefficient-parametric bilinear. -/
theorem harmonicNonRoughRamareBilinear_eq_withCoeff
    (P₀ P s : Finset ℕ) (w : ℝ) :
    harmonicNonRoughRamareBilinear P₀ P s w =
      harmonicRamareBilinearWithCoeff P s
        (harmonicNonRoughRamareCofactorCoeff P₀ P) w := rfl

/-- Exact global support replacement before any ladder Cauchy--Schwarz step. -/
theorem harmonicLadderProductPolyWithCoeff_sub_bilinear_eq
    {P : Finset ℕ} (A₀ B₀ : ℕ) {Q eta : ℝ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (c : ℕ → ℂ) (w : ℝ) :
    harmonicLadderProductPolyWithCoeff P A₀ B₀ Q eta L c w -
        harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w =
      harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + eta := by linarith
  have hbil : harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w =
      ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + eta) j,
        harmonicMoebiusPhase w p *
          logPoly c {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w := by
    rw [harmonicRamareBilinearWithCoeff, ← Finset.sum_biUnion
      (geomBlock_pairwiseDisjoint P hQ hr1 L),
      geomBlock_biUnion_eq P Q (1 + eta) hL hP]
  have hprod : harmonicLadderProductPolyWithCoeff P A₀ B₀ Q eta L c w =
      ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + eta) j,
        harmonicMoebiusPhase w p *
          logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w := by
    rw [harmonicLadderProductPolyWithCoeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [harmonicPrimeBlockPoly, Finset.sum_mul]
  rw [hprod, hbil, ← Finset.sum_sub_distrib, harmonicLadderProductDefectWithCoeff,
    ladderIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  set Qj : ℝ := Q * (1 + eta) ^ j with hQj
  have hQj0 : (0 : ℝ) < Qj := by
    rw [hQj]
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
      logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w -
          logPoly c {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w =
        logPoly c (ladderGapSetAt A₀ B₀ Q eta ⟨j, p⟩) w := by
    rw [logPoly_sub_eq_sdiff, hUC, ladderGapSetAt]
    simp [logPoly]
  rw [← mul_sub, hdiff]

/-- Reciprocal envelope for every prime-shifted gap coefficient. -/
theorem norm_harmonicPrimeShiftCoeff_ladderGap_le_of_dominated
    {c : ℕ → ℂ} (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime)
    {x : (_ : ℕ) × ℕ} (hx : x ∈ ladderIndex P Q eta L)
    {n : ℕ}
    (hn : n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) :
    ‖harmonicPrimeShiftCoeff x.2 c n‖ ≤ (1 + eta) / (A₀ : ℝ) := by
  classical
  rw [Finset.mem_image] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  have hxmem := hx
  rw [ladderIndex, Finset.mem_sigma] at hxmem
  have hp := hPprime x.2 (geomBlock_subset P Q (1 + eta) x.1 hxmem.2)
  rw [harmonicPrimeShiftCoeff, primeShiftCoeff, if_pos ⟨m, rfl⟩,
    Nat.mul_div_cancel_left m hp.pos, norm_mul, norm_div, Complex.norm_natCast]
  have hmC : m ∈ geomCofactorBlockAt A₀ B₀ Q eta x.1 :=
    (Finset.mem_sdiff.1 hm).1
  have hm0 := ladderGapSetAt_pos hA hQ heta x.1 hmC
  have hp0R : (0 : ℝ) < (x.2 : ℝ) := by exact_mod_cast hp.pos
  have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  set Qj : ℝ := Q * (1 + eta) ^ x.1 with hQj
  have hQj0 : (0 : ℝ) < Qj := by rw [hQj]; positivity
  have hpQ : Qj < (x.2 : ℝ) := by
    rw [geomBlock, Finset.mem_filter] at hxmem
    simpa [Qj] using hxmem.2.2.1
  have hmlo : (A₀ : ℝ) / (Qj * (1 + eta)) ≤ (m : ℝ) := by
    rw [geomCofactorBlockAt, Finset.mem_Icc] at hmC
    exact Nat.ceil_le.1 hmC.1
  have hAprod : (A₀ : ℝ) ≤ (x.2 : ℝ) * (m : ℝ) * (1 + eta) := by
    have hbase : (A₀ : ℝ) ≤ (m : ℝ) * (Qj * (1 + eta)) := by
      rwa [div_le_iff₀ (by positivity)] at hmlo
    calc
      (A₀ : ℝ) ≤ (m : ℝ) * (Qj * (1 + eta)) := hbase
      _ = Qj * (m : ℝ) * (1 + eta) := by ring
      _ ≤ (x.2 : ℝ) * (m : ℝ) * (1 + eta) := by gcongr
  have hmu : ‖((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)‖ ≤ 1 := by
    have hnorm : ‖((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)‖ =
        |((ArithmeticFunction.moebius x.2 : ℤ) : ℝ)| := by
      rw [show (((ArithmeticFunction.moebius x.2 : ℤ)) : ℂ) =
          ((((ArithmeticFunction.moebius x.2 : ℤ) : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    exact abs_moebius_real_le_one x.2
  have hc' := hc hm0
  have hdiv : ‖c m‖ / (x.2 : ℝ) ≤ 1 / ((m : ℝ) * (x.2 : ℝ)) := by
    calc
      ‖c m‖ / (x.2 : ℝ) ≤ (1 / (m : ℝ)) / (x.2 : ℝ) :=
        div_le_div_of_nonneg_right hc' hp0R.le
      _ = 1 / ((m : ℝ) * (x.2 : ℝ)) := by field_simp
  have hrecip : 1 / ((m : ℝ) * (x.2 : ℝ)) ≤ (1 + eta) / (A₀ : ℝ) := by
    have hA0R : (0 : ℝ) < (A₀ : ℝ) := by exact_mod_cast hA
    rw [div_le_div_iff₀ (mul_pos hm0R hp0R) hA0R]
    nlinarith [hAprod]
  have hright := hdiv.trans hrecip
  have htarget0 : 0 ≤ (1 + eta) / (A₀ : ℝ) := by positivity
  nlinarith [norm_nonneg (((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)),
    norm_nonneg (c m), htarget0]

/-- The global moving-support defect has exactly the existing harmonic error budget for every
cofactor coefficient dominated by `1/m`. -/
theorem integral_Icc_normSq_harmonicLadderProductDefectWithCoeff_le_closed
    {c : ℕ → ℂ} (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta W : ℝ} (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ)) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w‖ ^ 2) ≤
        menonHarmonicLadderErrorBudget A₀ B₀ Q eta W L := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  set N : ℕ := ⌊(B₀ : ℝ) * (1 + eta)⌋₊ with hN
  set K : ℝ := Real.log (N : ℝ) / Real.log Q with hK
  set Omega : ℝ := (1 + eta) / (A₀ : ℝ) with hOmega
  have hOmega0 : 0 < Omega := by rw [hOmega]; positivity
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
        ‖harmonicPrimeShiftCoeff x.2 c n‖ ≤ Omega := by
    intro x hx n hn
    simpa [Omega] using norm_harmonicPrimeShiftCoeff_ladderGap_le_of_dominated
      hc hA hQ0 heta hPprime hx hn
  have hrep : ∀ w : ℝ,
      harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w =
        ∑ x ∈ ladderIndex P Q eta L,
          logPoly (harmonicPrimeShiftCoeff x.2 c)
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w := by
    intro w
    rw [harmonicLadderProductDefectWithCoeff]
    refine Finset.sum_congr rfl fun x hx => ?_
    exact harmonicMoebiusPhase_mul_logPoly (hpos x hx) c (hDpos x hx) w
  have hcongr :
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w‖ ^ 2) =
      ∫ w in Set.Icc (-W) W,
        ‖∑ x ∈ ladderIndex P Q eta L,
          logPoly (harmonicPrimeShiftCoeff x.2 c)
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w‖ ^ 2 := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => by rw [hrep w]
  rw [hcongr]
  have hmain := integral_Icc_normSq_sum_logPoly_le_support_bound
    (ladderIndex P Q eta L) (fun x => harmonicPrimeShiftCoeff x.2 c)
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
  have hscale0 : 0 ≤ ((1 + eta) / (A₀ : ℝ)) ^ 2 := sq_nonneg _
  have hKnonneg : 0 ≤ Real.log ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) /
      Real.log Q := div_nonneg (Real.log_natCast_nonneg _) hlogQ.le
  have hgapK := mul_le_mul_of_nonneg_left hgap hKnonneg
  have hmean := mul_le_mul_of_nonneg_left hgapK hmean0
  exact mul_le_mul_of_nonneg_left hmean hscale0

/-! ## Injective high suffix -/

/-- Coefficient-parametric support defect on ladder steps `J, ..., L - 1`. -/
def harmonicLadderProductDefectIcoWithCoeff
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (J L : ℕ)
    (c : ℕ → ℂ) (w : ℝ) : ℂ :=
  ∑ x ∈ ladderIndexIco P Q eta J L,
    harmonicMoebiusPhase w x.2 * logPoly c (ladderGapSetAt A₀ B₀ Q eta x) w

theorem continuous_harmonicLadderProductDefectIcoWithCoeff
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) (J L : ℕ) (c : ℕ → ℂ) :
    Continuous (harmonicLadderProductDefectIcoWithCoeff P A₀ B₀ Q eta J L c) := by
  refine continuous_finsetSum _ fun x _ => ?_
  exact ((continuous_moebiusPhase x.2).div_const _).mul (continuous_logPoly _ _)

/-- Exact prefix/suffix decomposition for every cofactor coefficient. -/
theorem harmonicLadderProductDefectWithCoeff_eq_add_Ico
    (P : Finset ℕ) (A₀ B₀ : ℕ) (Q eta : ℝ) {J L : ℕ}
    (hJL : J ≤ L) (c : ℕ → ℂ) (w : ℝ) :
    harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w =
      harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta J c w +
        harmonicLadderProductDefectIcoWithCoeff P A₀ B₀ Q eta J L c w := by
  rw [harmonicLadderProductDefectWithCoeff, harmonicLadderProductDefectWithCoeff,
    harmonicLadderProductDefectIcoWithCoeff, ladderIndex, ladderIndex, ladderIndexIco,
    Finset.sum_sigma, Finset.sum_sigma, Finset.sum_sigma]
  exact (Finset.sum_range_add_sum_Ico (fun j =>
    ∑ p ∈ geomBlock P Q (1 + eta) j,
      harmonicMoebiusPhase w p * logPoly c
        (ladderGapSetAt A₀ B₀ Q eta ⟨j, p⟩) w) hJL).symm

set_option maxHeartbeats 300000 in
/-- The injective high suffix obeys the unchanged harmonic budget for every reciprocal-dominated
cofactor coefficient. -/
theorem integral_Icc_normSq_harmonicLadderProductDefectIcoWithCoeff_le_closed
    {c : ℕ → ℂ} (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta U W : ℝ} (hQ : 1 ≤ Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    {J L : ℕ} (hPprime : ∀ p ∈ P, p.Prime)
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ 2) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicLadderProductDefectIcoWithCoeff P A₀ B₀ Q eta J L c w‖ ^ 2) ≤
        menonHarmonicHighLadderErrorBudget A₀ B₀ eta U W := by
  classical
  set N : ℕ := ⌊(B₀ : ℝ) * (1 + eta)⌋₊ with hN
  set Omega : ℝ := (1 + eta) / (A₀ : ℝ) with hOmega
  have hOmega0 : 0 < Omega := by rw [hOmega]; positivity
  have hfull : ∀ x ∈ ladderIndexIco P Q eta J L,
      x ∈ ladderIndex P Q eta L := by
    intro x hx
    rw [ladderIndexIco, Finset.mem_sigma] at hx
    rw [ladderIndex, Finset.mem_sigma]
    have hj := hx.1
    rw [Finset.mem_Ico] at hj
    exact ⟨Finset.mem_range.2 hj.2, hx.2⟩
  have hpos : ∀ x ∈ ladderIndexIco P Q eta J L, 0 < x.2 := by
    intro x hx
    have hx' := hx
    rw [ladderIndexIco, Finset.mem_sigma] at hx'
    exact (hPprime x.2 (geomBlock_subset P Q (1 + eta) x.1 hx'.2)).pos
  have hDpos : ∀ x ∈ ladderIndexIco P Q eta J L,
      ∀ m ∈ ladderGapSetAt A₀ B₀ Q eta x, 0 < m := by
    intro x _ m hm
    exact ladderGapSetAt_pos hA (lt_of_lt_of_le zero_lt_one hQ) heta x.1
      (Finset.mem_sdiff.1 hm).1
  have hDN : ∀ x ∈ ladderIndexIco P Q eta J L,
      (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m) ⊆
        Finset.Icc 1 N := by
    intro x hx n hn
    have hupper := ladderGapSetAt_image_subset A₀ B₀ hQ heta L x (hfull x hx) hn
    rw [Finset.mem_Icc] at hupper ⊢
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    exact ⟨Nat.mul_pos (hpos x hx) (hDpos x hx m hm), by simpa [N] using hupper.2⟩
  have hinj := ladderGapPairsIco_product_injective
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (U := U)
    (J := J) (L := L) hA (lt_of_lt_of_le zero_lt_one hQ) heta hPprime hJU hU hU2
  have hOverlap : ∀ n ∈ Finset.Icc 1 N,
      (((ladderIndexIco P Q eta J L).filter (fun x =>
        n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))).card : ℝ) ≤ 1 := by
    intro n _
    have hcard : ((ladderIndexIco P Q eta J L).filter (fun x =>
        n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' := Finset.mem_filter.1 hx
      have hy' := Finset.mem_filter.1 hy
      rw [Finset.mem_image] at hx' hy'
      obtain ⟨mx, hmx, hnx⟩ := hx'.2
      obtain ⟨my, hmy, hny⟩ := hy'.2
      have hzx : (⟨x, mx⟩ : ((_ : ((_ : ℕ) × ℕ)) × ℕ)) ∈
          ladderGapPairsIco P A₀ B₀ Q eta J L := by
        rw [ladderGapPairsIco, Finset.mem_sigma]
        exact ⟨hx'.1, hmx⟩
      have hzy : (⟨y, my⟩ : ((_ : ((_ : ℕ) × ℕ)) × ℕ)) ∈
          ladderGapPairsIco P A₀ B₀ Q eta J L := by
        rw [ladderGapPairsIco, Finset.mem_sigma]
        exact ⟨hy'.1, hmy⟩
      have hpair := hinj hzx hzy (hnx.trans hny.symm)
      exact congrArg Sigma.fst hpair
    exact_mod_cast hcard
  have hcoeff : ∀ x ∈ ladderIndexIco P Q eta J L,
      ∀ n ∈ (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m),
        ‖harmonicPrimeShiftCoeff x.2 c n‖ ≤ Omega := by
    intro x hx n hn
    simpa [Omega] using norm_harmonicPrimeShiftCoeff_ladderGap_le_of_dominated
      hc hA (lt_of_lt_of_le zero_lt_one hQ) heta hPprime (hfull x hx) hn
  have hrep : ∀ w : ℝ,
      harmonicLadderProductDefectIcoWithCoeff P A₀ B₀ Q eta J L c w =
        ∑ x ∈ ladderIndexIco P Q eta J L,
          logPoly (harmonicPrimeShiftCoeff x.2 c)
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w := by
    intro w
    rw [harmonicLadderProductDefectIcoWithCoeff]
    refine Finset.sum_congr rfl fun x hx => ?_
    exact harmonicMoebiusPhase_mul_logPoly (hpos x hx) c (hDpos x hx) w
  have hcongr :
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefectIcoWithCoeff P A₀ B₀ Q eta J L c w‖ ^ 2) =
      ∫ w in Set.Icc (-W) W,
        ‖∑ x ∈ ladderIndexIco P Q eta J L,
          logPoly (harmonicPrimeShiftCoeff x.2 c)
            ((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)) w‖ ^ 2 := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => by rw [hrep w]
  rw [hcongr]
  have hmain := integral_Icc_normSq_sum_logPoly_le_support_bound
    (ladderIndexIco P Q eta J L) (fun x => harmonicPrimeShiftCoeff x.2 c)
    (fun x => (ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m))
    hDN hOmega0 hcoeff (by norm_num : (0 : ℝ) ≤ 1) hOverlap hW
  have himageCard : ∀ x ∈ ladderIndexIco P Q eta J L,
      (((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)).card : ℝ) =
        ((ladderGapSetAt A₀ B₀ Q eta x).card : ℝ) := by
    intro x hx
    have hmul : Set.InjOn (fun m => x.2 * m)
        (ladderGapSetAt A₀ B₀ Q eta x : Set ℕ) := by
      intro m₁ _ m₂ _ heq
      exact Nat.eq_of_mul_eq_mul_left (hpos x hx) heq
    exact_mod_cast Finset.card_image_of_injOn hmul
  have hcards :
      (∑ x ∈ ladderIndexIco P Q eta J L,
          (((ladderGapSetAt A₀ B₀ Q eta x).image (fun m => x.2 * m)).card : ℝ)) =
        ((ladderGapPairsIco P A₀ B₀ Q eta J L).card : ℝ) := by
    rw [ladderGapPairsIco, Finset.card_sigma, Nat.cast_sum]
    exact Finset.sum_congr rfl himageCard
  rw [hcards] at hmain
  have hgap := card_ladderGapPairsIco_le_harmonic
    (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (U := U)
    (J := J) (L := L) hA (lt_of_lt_of_le zero_lt_one hQ) heta hPprime hJU hU hU2
  refine hmain.trans ?_
  rw [menonHarmonicHighLadderErrorBudget]
  dsimp only [Omega, N] at hmain ⊢
  have hmean0 : 0 ≤ 5 * Real.pi / 2 * W +
      5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) := by positivity
  have hscale0 : 0 ≤ ((1 + eta) / (A₀ : ℝ)) ^ 2 := sq_nonneg _
  have hmean := mul_le_mul_of_nonneg_left hgap hmean0
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hmean hscale0

/-- Full coefficient-parametric defect controlled by the prefix and injective suffix budgets. -/
theorem integral_Icc_normSq_harmonicLadderProductDefectWithCoeff_le_prefix_add_high
    {c : ℕ → ℂ} (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q eta U W : ℝ} (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    {J L : ℕ} (hJL : J ≤ L) (hPprime : ∀ p ∈ P, p.Prime)
    (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    (hJU : U ≤ Q * (1 + eta) ^ J) (hU : 0 < U)
    (hU2 : (B₀ : ℝ) < U ^ 2) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w‖ ^ 2) ≤
      2 * menonHarmonicLadderErrorBudget A₀ B₀ Q eta W J +
        2 * menonHarmonicHighLadderErrorBudget A₀ B₀ eta U W := by
  have hsplit := setIntegral_normSq_add_le
    (continuous_harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta J c)
    (continuous_harmonicLadderProductDefectIcoWithCoeff P A₀ B₀ Q eta J L c)
    measurableSet_Icc (Set.Subset.rfl : Set.Icc (-W) W ⊆ Set.Icc (-W) W)
  have hrewrite :
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w‖ ^ 2) =
      ∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta J c w +
          harmonicLadderProductDefectIcoWithCoeff P A₀ B₀ Q eta J L c w‖ ^ 2 := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => by
      rw [harmonicLadderProductDefectWithCoeff_eq_add_Ico P A₀ B₀ Q eta hJL c w]
  rw [hrewrite]
  have hlo := integral_Icc_normSq_harmonicLadderProductDefectWithCoeff_le_closed
    hc (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    hA hQ heta hW hPprime hPge (L := J)
  have hhi := integral_Icc_normSq_harmonicLadderProductDefectIcoWithCoeff_le_closed
    hc (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (U := U) (W := W)
    (J := J) (L := L) hA hQ.le heta hW hPprime hJU hU hU2
  exact hsplit.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlo (by norm_num))
    (mul_le_mul_of_nonneg_left hhi (by norm_num)))

/-- Menon's final schedule controls every reciprocal-dominated full-ladder defect by the same
four-log-power budget as the unmasked coefficient. -/
theorem eventually_integral_menonFinalRange_fullLadderDefectWithCoeff_le_four_log_rpow_neg_eight
    : ∀ᶠ x : ℝ in Filter.atTop,
      ∀ (c : ℕ → ℂ), (∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ)) →
      ∀ W : ℝ, 1 ≤ W → W ≤ x →
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefectWithCoeff (menonFinalRangePrimes x) ⌈x⌉₊
          (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
          (menonFinalRangeLadderEta x) (menonFinalRangeLadderSteps x) c w‖ ^ 2) ≤
        4 * (Real.log x) ^ (-(8 : ℝ)) := by
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_menonFinalRangeLadder_basic,
    eventually_menonTruncatedRangeLadderSteps_le_finalRangeLadderSteps,
    eventually_menonTruncatedRangeLadder_cover,
    eventually_menonFinalRangeTopNat_lt_truncatedPrimeTopNat_sq,
    eventually_menonTruncatedRange_ladderErrorBudget_le_log_rpow_neg_eight,
    eventually_menonFinalRange_highLadderErrorBudget_le_log_rpow_neg_eight] with
      x htrunc hfull hJL hcover hsep hlo hhi
  intro c hc
  intro W hW hWx
  rcases htrunc with ⟨hxone, _, _, hQ, _, heta, _⟩
  rcases hsep with ⟨hU, hU2⟩
  have hA : 0 < ⌈x⌉₊ := Nat.one_le_ceil_iff.2 (lt_trans zero_lt_one hxone)
  have hPprime : ∀ p ∈ menonFinalRangePrimes x, p.Prime :=
    fun p hp => menonFinalRangePrimes_prime x hp
  have hPge : ∀ p ∈ menonFinalRangePrimes x,
      menonFinalRangeLadderBase x ≤ (p : ℝ) := by
    intro p hp
    have hpRange := mem_primesRange.1 hp
    rw [menonFinalRangeLadderBase]
    exact_mod_cast hpRange.2.1.le
  have hbase := integral_Icc_normSq_harmonicLadderProductDefectWithCoeff_le_prefix_add_high
    hc (P := menonFinalRangePrimes x) (A₀ := ⌈x⌉₊)
    (B₀ := menonFinalRangeTopNat x) (Q := menonFinalRangeLadderBase x)
    (eta := menonFinalRangeLadderEta x) (U := (menonTruncatedPrimeTopNat x : ℝ))
    (W := W) (J := menonTruncatedRangeLadderSteps x)
    (L := menonFinalRangeLadderSteps x) hA hQ heta hW hJL hPprime hPge hcover
    (by exact_mod_cast hU) hU2
  calc
    _ ≤ 2 * menonHarmonicLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
          (menonTruncatedRangeLadderSteps x) +
        2 * menonHarmonicHighLadderErrorBudget ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderEta x) (menonTruncatedPrimeTopNat x : ℝ) W := hbase
    _ ≤ 2 * (Real.log x) ^ (-(8 : ℝ)) + 2 * (Real.log x) ^ (-(8 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hlo W (by linarith) hWx) (by norm_num))
        (mul_le_mul_of_nonneg_left (hhi W (by linarith) hWx) (by norm_num))
    _ = 4 * (Real.log x) ^ (-(8 : ℝ)) := by ring

/-! ## Frequency-set ladder and product receivers -/

/-- Harmonic Ramaré energy with a coefficient-parametric ladder and one exact global defect. -/
theorem setIntegral_normSq_harmonicRamareBilinearWithCoeff_le_ladder_error
    {P : Finset ℕ} (A₀ B₀ : ℕ) {Q eta W : ℝ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (c : ℕ → ℂ) {E : Set ℝ} (hEm : MeasurableSet E)
    (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E,
      ‖harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (∫ w in E,
          ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
            logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) +
      2 * ∫ w in E,
        ‖harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w‖ ^ 2 := by
  classical
  let F : ℕ → ℝ → ℂ := fun j w =>
    harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
      logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w
  let D : ℝ → ℂ := harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c
  have hcontF : ∀ j : ℕ, Continuous fun w : ℝ => ‖F j w‖ ^ 2 := fun j =>
    (((continuous_harmonicPrimeBlockPoly _).mul (continuous_logPoly _ _)).norm).pow 2
  have hcontD : Continuous fun w : ℝ => ‖D w‖ ^ 2 :=
    (continuous_harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c).norm.pow 2
  have hdec : ∀ w : ℝ,
      harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w =
        (∑ j ∈ Finset.range L, F j w) + (-D w) := by
    intro w
    have h := harmonicLadderProductPolyWithCoeff_sub_bilinear_eq
      A₀ B₀ hQ heta hL hPprime hP c w
    dsimp only [F, D]
    rw [← harmonicLadderProductPolyWithCoeff]
    linear_combination -h
  have hpt : ∀ w : ℝ,
      ‖harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w‖ ^ 2 ≤
        2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2) +
          2 * ‖D w‖ ^ 2 := by
    intro w
    rw [hdec w]
    have hsum : ‖∑ j ∈ Finset.range L, F j w‖ ^ 2 ≤
        (L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2 := by
      have h1 : ‖∑ j ∈ Finset.range L, F j w‖ ≤
          ∑ j ∈ Finset.range L, ‖F j w‖ := norm_sum_le _ _
      have h2 : (∑ j ∈ Finset.range L, ‖F j w‖) ^ 2 ≤
          ((Finset.range L).card : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      rw [Finset.card_range] at h2
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    have htri := norm_add_le (∑ j ∈ Finset.range L, F j w) (-D w)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    rw [norm_neg] at hsq
    nlinarith [hsq, hsum, sq_nonneg (‖∑ j ∈ Finset.range L, F j w‖ - ‖D w‖)]
  have hcontZ : Continuous fun w : ℝ =>
      ‖harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w‖ ^ 2 :=
    (continuous_harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c).norm.pow 2
  have hcontR : Continuous fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2) + 2 * ‖D w‖ ^ 2 :=
    (((continuous_finsetSum _ fun j _ => hcontF j).const_mul _).const_mul 2).add
      (hcontD.const_mul 2)
  have hintZ : IntegrableOn (fun w : ℝ =>
      ‖harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w‖ ^ 2) E volume :=
    (hcontZ.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintR : IntegrableOn (fun w : ℝ =>
      2 * ((L : ℝ) * ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2) + 2 * ‖D w‖ ^ 2)
      E volume := (hcontR.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintF : ∀ j ∈ Finset.range L,
      IntegrableOn (fun w : ℝ => ‖F j w‖ ^ 2) E volume := fun j _ =>
    ((hcontF j).integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hintSum : IntegrableOn (fun w : ℝ =>
      ∑ j ∈ Finset.range L, ‖F j w‖ ^ 2) E volume :=
    ((continuous_finsetSum _ fun j _ => hcontF j).integrableOn_Icc
      (a := -W) (b := W)).mono_set hEs
  have hintD : IntegrableOn (fun w : ℝ => ‖D w‖ ^ 2) E volume :=
    (hcontD.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hmono := setIntegral_mono_on hintZ hintR hEm (fun w _ => hpt w)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add ((hintSum.const_mul _).const_mul 2) (hintD.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul,
    MeasureTheory.integral_finsetSum _ hintF]
  ring

/-- Reciprocal Halász--Montgomery estimate for any cofactor coefficient dominated by `1/m`. -/
theorem setIntegral_normSq_dominatedCofactor_le_HM_recip
    (c : ℕ → ℂ) (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {D : Finset ℕ} {L N : ℕ} (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hD : D ⊆ Finset.Icc L N) {E : Set ℝ} (hE : MeasurableSet E)
    {W : ℝ} (hW : 1 ≤ W) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly c D w‖ ^ 2) ≤
      (2 * Real.pi)⁻¹ *
        (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E) *
          ((1 / (L : ℝ)) ^ 2 * (D.card : ℝ))) := by
  have hDI : D ⊆ Finset.Icc 1 N := by
    intro n hn
    have hn' := Finset.mem_Icc.1 (hD hn)
    exact Finset.mem_Icc.2 ⟨le_trans hL hn'.1, hn'.2⟩
  refine setIntegral_normSq_logPoly_le_HM_window_recip_on c hN hDI hE hW hEs
    (by positivity) ?_
  intro n hn
  have hn' := Finset.mem_Icc.1 (hD hn)
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans hL hn'.1)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hL
  have hLn : (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
  exact (hc hn0).trans (one_div_le_one_div_of_le hLR hLn)

/-- One harmonic prime product with a reciprocal-dominated cofactor has the unchanged product
cost. -/
theorem setIntegral_normSq_harmonicProductWithCoeff_geom_le_HM
    (c : ℕ → ℂ) (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W V : ℝ}
    (hW : 1 ≤ W) (j : ℕ)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : 1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hprime : ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤ V) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) ≤
      menonHarmonicProductCostVolume P A₀ B₀ Q eta W V (volume.real E) j := by
  let D : Finset ℕ := geomCofactorBlockAt A₀ B₀ Q eta j
  let L₀ : ℕ := ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊
  let N : ℕ := ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊
  have hD : D ⊆ Finset.Icc L₀ N := by
    intro n hn
    simpa [D, L₀, N, geomCofactorBlockAt] using hn
  have hcof := setIntegral_normSq_dominatedCofactor_le_HM_recip
    c hc (D := D) (L := L₀) (N := N) hleft hright hD hEm hW hEs
  have hprod := setIntegral_normSq_harmonicBlockProduct_le_supMeanSquare
    c (geomBlock P Q (1 + eta) j) D hEm hEs hprime hcof
  dsimp only [D, L₀, N] at hprod
  simpa [menonHarmonicProductCostVolume] using hprod

/-- Threshold partition of one product, uniform in a reciprocal-dominated cofactor. -/
theorem setIntegral_normSq_harmonicProductWithCoeff_geom_le_threshold_largeMeasure
    (c : ℕ → ℂ) (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W V M : ℝ}
    (hW : 1 ≤ W) (j : ℕ) (hPprime : ∀ p ∈ P, p.Prime)
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : 1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hlargeVolume : volume.real (menonHarmonicPrimeBlockLargeOn E
      (geomBlock P Q (1 + eta) j) V) ≤ M) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) ≤
      menonHarmonicProductCostVolume P A₀ B₀ Q eta W V (volume.real E) j +
        menonHarmonicProductCostVolume P A₀ B₀ Q eta W
          (harmonicPrimeMass (geomBlock P Q (1 + eta) j)) M j := by
  let B : Finset ℕ := geomBlock P Q (1 + eta) j
  let Esmall : Set ℝ := menonHarmonicPrimeBlockSmallOn E B V
  let Elarge : Set ℝ := menonHarmonicPrimeBlockLargeOn E B V
  let f : ℝ → ℝ := fun w =>
    ‖harmonicPrimeBlockPoly B w * logPoly c
      (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2
  have hcont : Continuous f :=
    (((continuous_harmonicPrimeBlockPoly B).mul (continuous_logPoly _ _)).norm).pow 2
  have hsmallm : MeasurableSet Esmall :=
    measurableSet_menonHarmonicPrimeBlockSmallOn hEm B V
  have hlargem : MeasurableSet Elarge :=
    measurableSet_menonHarmonicPrimeBlockLargeOn hEm B V
  have hsmalls : Esmall ⊆ Set.Icc (-W) W := fun _ hw => hEs hw.1
  have hlarges : Elarge ⊆ Set.Icc (-W) W := fun _ hw => hEs hw.1
  have hsmall := setIntegral_normSq_harmonicProductWithCoeff_geom_le_HM
    c hc (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := V) hW j hleft hright hsmallm hsmalls
      (fun _ hw => norm_harmonicPrimeBlockPoly_le_of_mem_smallOn hw)
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hlarge := setIntegral_normSq_harmonicProductWithCoeff_geom_le_HM
    c hc (P := P) (A₀ := A₀) (B₀ := B₀) (Q := Q) (eta := eta) (W := W)
    (V := harmonicPrimeMass B) hW j hleft hright hlargem hlarges
      (fun w _ => norm_harmonicPrimeBlockPoly_le_mass hBprime w)
  have hEtop : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hEs)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hsmallVolume : volume.real Esmall ≤ volume.real E :=
    measureReal_mono (fun _ hw => hw.1) hEtop
  have hsmall' := (menonHarmonicProductCostVolume_mono
    P A₀ B₀ Q eta W V j hW hsmallVolume).trans'
      (by simpa only [B, Esmall] using hsmall)
  have hlarge' := (menonHarmonicProductCostVolume_mono
    P A₀ B₀ Q eta W (harmonicPrimeMass B) j hW
      (by simpa only [B, Elarge] using hlargeVolume)).trans'
      (by simpa only [B, Elarge] using hlarge)
  have hsplit := setIntegral_menonHarmonicPrimeBlock_thresholdPartition
    hEm B V f (hcont.integrableOn_Icc.mono_set hEs)
  calc
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w *
        logPoly c (geomCofactorBlockAt A₀ B₀ Q eta j) w‖ ^ 2) =
        (∫ w in Esmall, f w) + ∫ w in Elarge, f w := by
          simpa only [B, Esmall, Elarge, f] using hsplit
    _ ≤ _ := add_le_add hsmall' hlarge'

/-- Complete external-threshold ladder assembly for a reciprocal-dominated cofactor. -/
theorem setIntegral_normSq_harmonicRamareBilinearWithCoeff_le_external_thresholds_exactDefect
    (c : ℕ → ℂ) (hc : ∀ {m : ℕ}, 0 < m → ‖c m‖ ≤ 1 / (m : ℝ))
    {P : Finset ℕ} {A₀ B₀ L : ℕ} {Q eta W : ℝ}
    (hQ : 1 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPrange : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta) ^ L)
    (V M : ℕ → ℝ)
    (hleft : ∀ j ∈ Finset.range L,
      1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊)
    (hright : ∀ j ∈ Finset.range L,
      1 ≤ ⌊(B₀ : ℝ) / (Q * (1 + eta) ^ j)⌋₊)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hlargeVolume : ∀ j ∈ Finset.range L,
      volume.real (menonHarmonicPrimeBlockLargeOn E
        (geomBlock P Q (1 + eta) j) (V j)) ≤ M j) :
    (∫ w in E,
      ‖harmonicRamareBilinearWithCoeff P (Finset.Icc A₀ B₀) c w‖ ^ 2) ≤
      2 * (L : ℝ) * ∑ j ∈ Finset.range L,
        (menonHarmonicProductCostVolume P A₀ B₀ Q eta W
            (V j) (volume.real E) j +
          menonHarmonicProductCostVolume P A₀ B₀ Q eta W
            (harmonicPrimeMass (geomBlock P Q (1 + eta) j)) (M j) j) +
        2 * ∫ w in E,
          ‖harmonicLadderProductDefectWithCoeff P A₀ B₀ Q eta L c w‖ ^ 2 := by
  have hbase := setIntegral_normSq_harmonicRamareBilinearWithCoeff_le_ladder_error
    (P := P) A₀ B₀ (lt_trans zero_lt_one hQ) heta hL hPprime hPrange c hEm hEs
  refine hbase.trans (add_le_add ?_ le_rfl)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg L))
  exact setIntegral_normSq_harmonicProductWithCoeff_geom_le_threshold_largeMeasure
    c hc hW j hPprime (hleft j hj) (hright j hj) hEm hEs (hlargeVolume j hj)

end

end RHTower.Sieve
