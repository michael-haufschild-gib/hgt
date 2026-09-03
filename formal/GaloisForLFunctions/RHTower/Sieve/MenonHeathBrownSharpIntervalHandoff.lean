import GaloisForLFunctions.RHTower.Sieve.MenonPrimeTwistRangeReverseAbel
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownTwistedSmoothHandoff
import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalObservationCone
import GaloisForLFunctions.RHTower.Sieve.MaynardNormalizedReferenceTargetPerron
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateCellExtraction

/-!
# Exact sharp-interval twisted Heath--Brown handoff

Subtracting two half-width smooth prefix cutoffs is exactly the indicator of a natural interval.
This gives an absolutely convergent Mellin representation of a sharp twisted von Mangoldt range
while retaining the window-relevant full Heath--Brown products.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

/-- Difference of half-width smooth prefix cutoffs used to encode `(a,b]` exactly on `ℕ`. -/
def menonSharpIntervalWeight (a b : ℕ) (x : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.smoothWeight (b : ℝ) (1 / 2 : ℝ) x -
    GaloisForLFunctions.HTGeometry.smoothWeight (a : ℝ) (1 / 2 : ℝ) x

/-- At natural arguments the half-width cutoff difference is the literal sharp interval
indicator, with no transition error. -/
theorem menonSharpIntervalWeight_nat (a b n : ℕ) (hab : a ≤ b) :
    menonSharpIntervalWeight a b n = if a < n ∧ n ≤ b then 1 else 0 := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  by_cases han : a < n
  · by_cases hnb : n ≤ b
    · have hupper := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one
        hhalf (show (n : ℝ) ≤ (b : ℝ) by exact_mod_cast hnb)
      have hlower := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero
        hhalf (show (a : ℝ) + 1 / 2 ≤ (n : ℝ) by
          have : (a : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast han
          linarith)
      rw [menonSharpIntervalWeight, hupper, hlower, if_pos ⟨han, hnb⟩]
      norm_num
    · have hbn : b < n := Nat.lt_of_not_ge hnb
      have hupper := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero
        hhalf (show (b : ℝ) + 1 / 2 ≤ (n : ℝ) by
          have : (b : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hbn
          linarith)
      have han' : a < n := hab.trans_lt hbn
      have hlower := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero
        hhalf (show (a : ℝ) + 1 / 2 ≤ (n : ℝ) by
          have : (a : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast han'
          linarith)
      rw [menonSharpIntervalWeight, hupper, hlower, if_neg (by tauto)]
      norm_num
  · have hna : n ≤ a := Nat.le_of_not_gt han
    have hnb : n ≤ b := hna.trans hab
    have hlower := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one
      hhalf (show (n : ℝ) ≤ (a : ℝ) by exact_mod_cast hna)
    have hupper := GaloisForLFunctions.HTGeometry.smoothWeight_eq_one
      hhalf (show (n : ℝ) ≤ (b : ℝ) by exact_mod_cast hnb)
    rw [menonSharpIntervalWeight, hupper, hlower, if_neg (by tauto)]
    norm_num

/-- Twisted smooth Perron identity for the exact window-relevant packet.  The physical twist
translates only the full aggregate ordinate. -/
theorem tsum_windowRelevantPacket_twist_smoothWeight_eq_integral
    (L X k : ℕ) (T0 t N0 tau : ℝ) {N H sigma : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
      complexCoeff (heathBrownWindowRelevantEligiblePacket L X k T0 t N0) n *
        (n : ℂ) ^ (-((tau : ℂ) * Complex.I)) *
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N0
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) *
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((sigma : ℂ) + (y : ℝ) * Complex.I) := by
  let F := heathBrownWindowRelevantEligiblePacket L X k T0 t N0
  let c : ℕ → ℂ := fun n =>
    complexCoeff F n * (n : ℂ) ^ (-((tau : ℂ) * Complex.I))
  have hc0 : c 0 = 0 := by simp [c]
  have hsumF : Summable fun n : ℕ => ‖complexCoeff F n‖ * (n : ℝ) ^ (-sigma) :=
    summable_norm_mul_rpow_of_LSeriesSummable (by linarith)
      (LSeriesSummable_heathBrownWindowRelevantEligiblePacket
        L X k T0 t N0 (sigma : ℂ))
  have hnorm : ∀ n : ℕ, ‖c n‖ = ‖complexCoeff F n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [c]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
      have hphase : ‖((n : ℕ) : ℂ) ^ (-((tau : ℂ) * Complex.I))‖ = 1 := by
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnR]
        simp
      simp [c, hphase]
  have hsum : Summable fun n : ℕ => ‖c n‖ * (n : ℝ) ^ (-sigma) := by
    refine hsumF.congr fun n => ?_
    rw [hnorm]
  have hperron := tsum_mul_smoothWeight_eq_integral_summable
    (a := c) hc0 hN hH hsigma hsum
  change (2 * Real.pi : ℝ) • (∑' n : ℕ, c n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ)) = _
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change (∑' n : ℕ, c n *
      (n : ℂ) ^ (-((sigma : ℂ) + (y : ℝ) * Complex.I))) * _ = _ * _
  congr 1
  change (∑' n : ℕ, complexCoeff F n *
      (n : ℂ) ^ (-((tau : ℂ) * Complex.I)) *
      (n : ℂ) ^ (-((sigma : ℂ) + (y : ℝ) * Complex.I))) = _
  rw [tsum_complexCoeff_twist_cpow_eq_LSeries,
    LSeries_heathBrownWindowRelevantEligiblePacket]
  congr 1
  push_cast
  ring

/-- The shifted window-relevant aggregate times a smooth Mellin kernel is absolutely
integrable.  This is the exact integrability input needed to subtract two cutoff identities. -/
theorem integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
    (L X k : ℕ) (hX : 1 ≤ X) (T0 t N0 tau : ℝ)
    {N H sigma : ℝ} (hN0 : 0 < N0) (hN : 0 < N) (hH : 0 < H)
    (hsigma : 0 < sigma) :
    Integrable (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N0
          ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) *
        mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)) := by
  let A : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N0
      ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I)
  let K : ℝ → ℂ := fun y =>
    mellin (fun x : ℝ =>
      ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
      ((sigma : ℂ) + (y : ℝ) * Complex.I)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k N0 sigma
  have hshift : Continuous (fun y : ℝ => y + tau) := continuous_id.add continuous_const
  have hA : Continuous A :=
    (continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t N0 sigma).comp hshift
  have hAbound : ∀ y : ℝ, ‖A y‖ ≤ P := fun y =>
    norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t N0 sigma (y + tau) hN0 hsigma.le
  have hP : 0 ≤ P := (norm_nonneg (A 0)).trans (hAbound 0)
  have hK : Integrable K := verticalIntegrable_mellin_smoothWeight hN hH hsigma
  exact Integrable.bdd_mul (c := P) hK hA.aestronglyMeasurable
    (Filter.Eventually.of_forall hAbound)

/-- Exact twisted von Mangoldt interval as one absolutely convergent vertical integral of the
window-relevant full Heath--Brown aggregate. -/
theorem sum_Ioc_vonMangoldtTwist_eq_integral_windowRelevantAggregate
    (L X k a b : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b) (hbX : b ≤ X)
    (T0 t tau : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) •
        (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n) =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) *
          (mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight (b : ℝ)
                (1 / 2 : ℝ) x : ℝ) : ℂ))
                ((sigma : ℂ) + (y : ℝ) * Complex.I) -
            mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight (a : ℝ)
                (1 / 2 : ℝ) x : ℝ) : ℂ))
                ((sigma : ℂ) + (y : ℝ) * Complex.I)) := by
  let F := heathBrownWindowRelevantEligiblePacket L X k T0 t (a : ℝ)
  let phase : ℕ → ℂ := fun n => (n : ℂ) ^ (-((tau : ℂ) * Complex.I))
  let WB : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight (b : ℝ)
      (1 / 2 : ℝ) (n : ℝ) : ℝ) : ℂ)
  let WA : ℕ → ℂ := fun n =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight (a : ℝ)
      (1 / 2 : ℝ) (n : ℝ) : ℝ) : ℂ)
  have hsharp : (∑' n : ℕ, complexCoeff F n * phase n * (WB n - WA n)) =
      ∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n := by
    rw [tsum_eq_sum (s := Finset.Ioc a b)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnI := Finset.mem_Ioc.mp hn
      have hcoeff := complexCoeff_heathBrownWindowRelevantEligiblePacket_eq_vonMangoldt
        L X k hXL hT0 hscale (n := n)
          (by exact_mod_cast hnI.1) (hnI.2.trans hbX)
      have hw := menonSharpIntervalWeight_nat a b n hab
      rw [if_pos hnI] at hw
      have hweight : WB n - WA n = 1 := by
        dsimp [WB, WA]
        exact_mod_cast hw
      rw [hweight, mul_one, hcoeff]
      simp only [phase, vonMangoldtTwist]
    · intro n hn
      have hw := menonSharpIntervalWeight_nat a b n hab
      have hn' : ¬ (a < n ∧ n ≤ b) := by
        simpa only [Finset.mem_Ioc] using hn
      rw [if_neg hn'] at hw
      have hweight : WB n - WA n = 0 := by
        dsimp [WB, WA]
        exact_mod_cast hw
      rw [hweight, mul_zero]
  have hsumB : Summable fun n : ℕ => complexCoeff F n * phase n * WB n :=
    summable_of_ne_finset_zero (s := Finset.range (⌈(b : ℝ) + 1 / 2⌉₊ + 1))
      (fun n hn => by
        have hnB : (b : ℝ) + 1 / 2 ≤ (n : ℝ) := by
          have hceil := Nat.le_ceil ((b : ℝ) + 1 / 2)
          have hn' : ¬n < ⌈(b : ℝ) + 1 / 2⌉₊ + 1 := by
            simpa only [Finset.mem_range] using hn
          have hncast : ((⌈(b : ℝ) + 1 / 2⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.le_of_not_lt hn'
          push_cast at hncast
          linarith
        have hz := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero
          (by norm_num : (0 : ℝ) < 1 / 2) hnB
        change complexCoeff F n * phase n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight (b : ℝ)
            (1 / 2 : ℝ) (n : ℝ) : ℝ) : ℂ) = 0
        rw [hz]
        simp)
  have hsumA : Summable fun n : ℕ => complexCoeff F n * phase n * WA n :=
    summable_of_ne_finset_zero (s := Finset.range (⌈(a : ℝ) + 1 / 2⌉₊ + 1))
      (fun n hn => by
        have hnA : (a : ℝ) + 1 / 2 ≤ (n : ℝ) := by
          have hceil := Nat.le_ceil ((a : ℝ) + 1 / 2)
          have hn' : ¬n < ⌈(a : ℝ) + 1 / 2⌉₊ + 1 := by
            simpa only [Finset.mem_range] using hn
          have hncast : ((⌈(a : ℝ) + 1 / 2⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.le_of_not_lt hn'
          push_cast at hncast
          linarith
        have hz := GaloisForLFunctions.HTGeometry.smoothWeight_eq_zero
          (by norm_num : (0 : ℝ) < 1 / 2) hnA
        change complexCoeff F n * phase n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight (a : ℝ)
            (1 / 2 : ℝ) (n : ℝ) : ℝ) : ℂ) = 0
        rw [hz]
        simp)
  have htsumSub :
      (∑' n : ℕ, complexCoeff F n * phase n * WB n) -
          (∑' n : ℕ, complexCoeff F n * phase n * WA n) =
        ∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n := by
    rw [← hsumB.tsum_sub hsumA]
    simpa only [mul_sub] using hsharp
  have haR : (0 : ℝ) < (a : ℝ) := by
    have hleft : (0 : ℝ) < ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t := by
      exact mul_pos (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
    exact hleft.trans_le hscale
  have haPos : 0 < a := by exact_mod_cast haR
  have hbPos : 0 < b := haPos.trans_le hab
  have hXNat : 1 ≤ X :=
    (Nat.succ_le_iff.mpr haPos).trans (hab.trans hbX)
  have hB := tsum_windowRelevantPacket_twist_smoothWeight_eq_integral
    L X k T0 t (a : ℝ) tau (N := (b : ℝ)) (H := (1 / 2 : ℝ))
      (by exact_mod_cast hbPos)
      (by norm_num) hsigma
  have hA := tsum_windowRelevantPacket_twist_smoothWeight_eq_integral
    L X k T0 t (a : ℝ) tau (N := (a : ℝ)) (H := (1 / 2 : ℝ))
      haR
      (by norm_num) hsigma
  rw [← htsumSub, smul_sub, hB, hA]
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with y
    ring
  · simpa only using
      integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
        L X k hXNat T0 t (a : ℝ) tau haR (by exact_mod_cast hbPos)
          (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 0 < sigma)
  · simpa only using
      integrable_heathBrownWindowRelevantAggregate_shift_mul_mellin_smoothWeight
        L X k hXNat T0 t (a : ℝ) tau haR haR
          (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 0 < sigma)

end RHTower.Sieve
