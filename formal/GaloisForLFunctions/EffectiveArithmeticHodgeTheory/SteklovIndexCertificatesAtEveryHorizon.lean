import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.FiniteWeilFamiliesHaveExplicitIndexHorizonTests
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheSteklovScheduleReachesTheIndex

/-!
# Finite index certificates on the exact Steklov schedule

Logarithmic Denjoy–Carleman witnesses carry every finite part of the Weil index.
Their explicit synthesis errors give a compressed-entry test at every integer
horizon; zero extension handles the incomplete last block.
-/

noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate
namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory
open HTGeometry SpacingScaleHarmonicAnalysis TransMetzlerWeilPositivity
open ArithmeticCastelnuovoSeveri (weilGram cx)
open ArithmeticElectrostatics (atomicTest)

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The full entry error of logarithmic synthesis by the fixed Steklov profile. -/
def steklovWeilEntryBudget {n : ℕ} (F : Fin n → ℝ → ℝ)
    (R M b : ℝ) (m : ℕ) (k : ℝ) (j : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  weilGramEntryBudget F (R + 1)
    (dcSynthErr M b (2 * steklovBaseSup) 12 k
      (∫ u, |steklovDCProfile u|) m j)
    (emLip (fun l => M * b ^ l * dcLogWeight l)
      (fun l => ∫ u, |iteratedDeriv l steklovDCProfile u|) k j) k

/-- Every finite part of the actual Weil index has explicit Steklov certificates,
valid at all integer horizons and all inverse widths. -/
theorem exists_steklov_index_horizon_test {d : ℕ}
    (hd : (d : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel) :
    ∃ (n : ℕ) (F : Fin n → ℝ → ℝ) (R M b : ℝ) (r : ℕ)
      (S : Matrix (Fin n) (Fin r) ℂ) (δ : ℝ),
      0 ≤ R ∧ 0 ≤ M ∧ 0 ≤ b ∧
      (∀ i, ContDiff ℝ ∞ (F i)) ∧ (∀ i, SupportedIn R (F i)) ∧
      (∀ i l u, |iteratedDeriv l (F i) u| ≤ M * b ^ l * dcLogWeight l) ∧
      d ≤ r ∧ r = hermNegIndex (weilGram Λw (fun i => cx (F i))) ∧ 0 < δ ∧
      ∀ (N m : ℕ) (k : ℝ), 2 ≤ N / blockSize R → 1 ≤ k →
      (∀ i j, compressedEntryBudget S
        (steklovWeilEntryBudget F R M b m k (N / blockSize R)) i j ≤
          δ / (2 * ((r : ℝ) ^ 2 + 1))) →
      d ≤ hermNegIndex (atomicGram (dilate k steklovDCProfile) N) := by
  obtain ⟨n, F, R, M, b, hR, hM, hb, hF, hFR, hFM, hdF⟩ :=
    exists_dcLog_family contDiff_steklovDCProfile steklovDCProfile_vanishesOff
      integral_steklovDCProfile (by norm_num) integral_abs_iteratedDeriv_steklovDCProfile_le hd
  have hF2 (i : Fin n) : ContDiff ℝ 2 (F i) := (hF i).of_le (natCast_le_infty 2)
  have hFc (i : Fin n) := hasCompactSupport_of_vanishes (hFR i)
  obtain ⟨r, S, c, δ, hr, hδ, hc, hdiag⟩ := exists_complete_negative_compression
    (weilGram Λw (fun i => cx (F i))) (weilGram_cx_isHermitian hF2 hFc)
  have hdr : d ≤ r := hr.symm ▸ hdF
  refine ⟨n, F, R, M, b, r, S, δ, hR, hM, hb, hF, hFR, hFM, hdr, hr, hδ, ?_⟩
  intro N m k hN hk hsmall
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  choose x D hx hD hDR he hL using
    (fun i => exists_dcLogSynthesis contDiff_steklovDCProfile steklovDCProfile_vanishesOff
      integral_steklovDCProfile (hF i) (hFR i) hM hb (by norm_num)
      (hFM i) integral_abs_iteratedDeriv_steklovDCProfile_le hN hk m)
  have hGD (i : Fin n) : ContDiff ℝ 2 (fun u => F i u + D i u) := (hF2 i).add (hD i)
  have hGDc (i : Fin n) : HasCompactSupport (fun u => F i u + D i u) :=
    (hFc i).add (hasCompactSupport_of_vanishes (hDR i))
  have hGram : weilGram Λw (fun i => cx
      (atomicTest ((N / blockSize R) * blockSize R) (x i) (dilate k steklovDCProfile))) =
      weilGram Λw (fun i => cx (fun u => F i u + D i u)) := by
    simp_rw [hx]
    exact weilGram_cx_common_translate (fun i u => F i u + D i u) hGD hGDc _
  have hentry (i j : Fin n) :
      ‖weilGram Λw (fun i => cx (fun u => F i u + D i u)) i j -
        weilGram Λw (fun i => cx (F i)) i j‖ ≤
          steklovWeilEntryBudget F R M b m k (N / blockSize R) i j := by
    exact norm_weilGram_add_sub_le_explicit F D hF2 hFc
      (fun i => supportedIn_mono (hFR i) (by linarith only)) hD hDR
      (by linarith only [hR]) he hL hk i j
  have hindex := le_index_of_compressed_entry_test _ _ S c hδ hc hdiag _ hentry hsmall
  rw [← hGram] at hindex
  have hext : (fun i => cx
      (atomicTest ((N / blockSize R) * blockSize R) (x i) (dilate k steklovDCProfile))) =
      fun i => cx (atomicTest N
        (fun l => if l ≤ (N / blockSize R) * blockSize R then x i l else 0)
        (dilate k steklovDCProfile)) := by
    funext i
    rw [atomicTest_extend (Nat.div_mul_le_self N (blockSize R))]
  rw [hext] at hindex
  exact hdr.trans (hindex.trans (hermNegIndex_le_atomicGram
    (contDiff_steklovDCProfile.of_le (natCast_le_infty 2)) steklovDCProfile_vanishesOff hk0 _))

/-- The finite test on the exact super-Gevrey schedule, with its prescribed order. -/
theorem exists_steklov_schedule_index_horizon_test {d : ℕ}
    (hd : (d : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel) :
    ∃ (n : ℕ) (F : Fin n → ℝ → ℝ) (R M b : ℝ) (r : ℕ)
      (S : Matrix (Fin n) (Fin r) ℂ) (δ : ℝ),
      0 ≤ R ∧ 0 ≤ M ∧ 0 ≤ b ∧ d ≤ r ∧ 0 < δ ∧
      ∀ (β : ℝ) (N : ℕ),
      let k := (N : ℝ) / superGevreyRatio β N
      2 ≤ N / blockSize R → 1 ≤ k →
      (∀ i j, compressedEntryBudget S
        (steklovWeilEntryBudget F R M b (gevOrder k) k (N / blockSize R)) i j ≤
          δ / (2 * ((r : ℝ) ^ 2 + 1))) →
      d ≤ hermNegIndex (atomicGram (dilate k steklovDCProfile) N) := by
  obtain ⟨n, F, R, M, b, r, S, δ, hR, hM, hb, _, _, _, hdr, _, hδ, htest⟩ :=
    exists_steklov_index_horizon_test hd
  exact ⟨n, F, R, M, b, r, S, δ, hR, hM, hb, hdr, hδ,
    fun β N => htest N (gevOrder ((N : ℝ) / superGevreyRatio β N))
      ((N : ℝ) / superGevreyRatio β N)⟩

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory

#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.exists_steklov_index_horizon_test
#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.exists_steklov_schedule_index_horizon_test
