import GaloisForLFunctions.BiScaleUncertainty.PrimeClockGraphCompactness
import GaloisForLFunctions.BiScaleUncertainty.PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer
import GaloisForLFunctions.RHTower.CHMDPrimitiveCuspEscape

/-!
# Escape by actual prime-clock packets

Positive packets of distinct deep primes can have bounded complete graph norm,
vanishing diagonal cost and signed energy, yet no Cauchy subsequence. The
construction quantitatively transfers the primitive cusp escape through the
actual-prime synthesis theorem.
-/

open Finset Set Filter Topology RHTower RHTower.CHMDDoobGraph
open scoped InnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.PrimeClock
noncomputable section
set_option autoImplicit false

def escapeTolerance (n : ℕ) : ℝ := 1 / (16 * ((n : ℝ) + 1))

theorem escapeTolerance_pos (n : ℕ) : 0 < escapeTolerance n := by
  unfold escapeTolerance
  positivity

theorem escapeTolerance_le (n : ℕ) : escapeTolerance n ≤ 1 / 16 := by
  unfold escapeTolerance
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * ((n : ℝ) + 1))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem escapeTolerance_zero : Tendsto escapeTolerance atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) / 16) atTop (𝓝 0) := by
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 16
  convert h using 1
  funext n
  simp only [escapeTolerance, div_div]
  ring

/-- The scalar bounds include every prime edge of the original graph. -/
theorem exists_deep_prime_escape :
    ∃ k N : ℕ → ℕ, ∃ S : ℕ → Finset ℕ,
      (∀ n, n ≤ N n) ∧
      (∀ n p, p ∈ S n → p.Prime ∧ Real.sqrt (N n) < p ∧
        (n : ℝ) < Real.log ((N n : ℝ) / p)) ∧
      (∀ n, ‖packet (k n) (N n) (S n)‖ ≤ 3) ∧
      (∀ n, (∑ p ∈ S n, ‖canonicalPrimeGraphClockAtom (k n) (N n) p‖ ^ 2) <
        escapeTolerance n) ∧
      (∀ n m, n ≠ m → 1 < ‖packet (k n) (N n) (S n) - packet (k m) (N m) (S m)‖) ∧
      Tendsto (fun n => sourceEnergy (packet (k n) (N n) (S n))) atTop (𝓝 0) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ →
        ¬ CauchySeq (fun n => packet (k (φ n)) (N (φ n)) (S (φ n)))) := by
  classical
  obtain ⟨u, _hcore, _hprim, hunit, hbound, horth, henergy, _hedge, _hgraph⟩ :=
    CHMDEscape.exists_primitive_escape
  have ha (n : ℕ) : ∃ k N : ℕ, ∃ S : Finset ℕ,
      n ≤ N ∧
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ (n : ℝ) < Real.log ((N : ℝ) / p)) ∧
      ‖packet k N S - u n‖ < escapeTolerance n ∧
      (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < escapeTolerance n := by
    obtain ⟨k, hk⟩ := exists_cutoff_eventually_criticalPrimeGraphClock_realization
      (u n) n (escapeTolerance_pos n)
    obtain ⟨N, hN, S, hS, he, hd⟩ := ((eventually_ge_atTop n).and hk).exists
    exact ⟨k, N, S, hN, hS, he, hd⟩
  choose k N S hN hprime herr hdiag using ha
  let P : ℕ → SourceGraph := fun n => packet (k n) (N n) (S n)
  have hP (n : ℕ) : ‖P n‖ ≤ 3 := by
    have h := norm_add_le (P n - u n) (u n)
    rw [sub_add_cancel] at h
    have he := herr n
    have hb := hbound n
    have hd := escapeTolerance_le n
    dsimp only [P]
    dsimp only [P] at h
    linarith
  have hsep (n m : ℕ) (hnm : n ≠ m) : 1 < ‖P n - P m‖ := by
    have hg := norm_fst_sq_le_norm_sq (u n - u m)
    change ‖CHMDEscape.source (u n) - CHMDEscape.source (u m)‖ ^ 2 ≤ ‖u n - u m‖ ^ 2 at hg
    rw [norm_sub_sq_real, hunit n, hunit m, horth n m hnm] at hg
    have hbase : (5 : ℝ) / 4 ≤ ‖u n - u m‖ := by
      nlinarith [norm_nonneg (u n - u m)]
    have ht : ‖u n - u m‖ ≤ ‖P n - u n‖ + ‖P n - P m‖ + ‖P m - u m‖ := by
      calc
        _ = ‖((u n - P n) + (P n - P m)) + (P m - u m)‖ := by congr 1; abel
        _ ≤ ‖u n - P n‖ + ‖P n - P m‖ + ‖P m - u m‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ = _ := by rw [norm_sub_rev (u n) (P n)]
    have hn := herr n
    have hm := herr m
    have hdn := escapeTolerance_le n
    have hdm := escapeTolerance_le m
    change ‖P n - u n‖ < escapeTolerance n at hn
    change ‖P m - u m‖ < escapeTolerance m at hm
    linarith
  have herrlim : Tendsto (fun n => ‖P n - u n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (herr n).le) escapeTolerance_zero
  have hlimbound : Tendsto (fun n => ‖P n - u n‖ ^ 2 + 4 * ‖P n - u n‖)
      atTop (𝓝 0) := by
    simpa using (herrlim.pow 2).add (herrlim.const_mul 4)
  have hdiff : Tendsto (fun n => sourceEnergy (P n) - sourceEnergy (u n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hlimbound
    intro n
    rw [Real.norm_eq_abs]
    have he := abs_sourceEnergy_sub_le (P n) (u n)
    have hb := mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg (P n - u n))
    nlinarith
  refine ⟨k, N, S, hN, hprime, hP, hdiag, hsep, ?_, ?_⟩
  · simpa only [sub_add_cancel, zero_add] using hdiff.add henergy
  · intro φ hφ hC
    obtain ⟨j, hj⟩ := Metric.cauchySeq_iff.mp hC 1 (by norm_num)
    have hd := hj j le_rfl (j + 1) (by omega)
    rw [dist_eq_norm] at hd
    have hs := hsep (φ j) (φ (j + 1)) (hφ (by omega : j < j + 1)).ne
    linarith

end
end GaloisForLFunctions.BiScaleUncertainty.PrimeClock
