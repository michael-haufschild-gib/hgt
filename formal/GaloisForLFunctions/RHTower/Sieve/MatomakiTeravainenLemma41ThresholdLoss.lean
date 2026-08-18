import GaloisForLFunctions.RHTower.Sieve.HuxleyDensityThreshold

/-!
# Matomäki--Teräväinen Lemma 4.1 with finite threshold loss

Pigeonholing a raised Dirichlet polynomial over finitely many dyadic blocks weakens a threshold by
a factor `L`. This module transfers that loss exactly into the exponent
`sigma + log L / log N` and applies the corpus's closed Lemma 4.1 theorem. No factor is discarded as
an implicit polylogarithm.
-/

namespace RHTower.Sieve

/-- Exponent after weakening a Huxley threshold by a factor `L`. -/
noncomputable def huxleyThresholdLossSigma (N : ℕ) (sigma L : ℝ) : ℝ :=
  sigma + Real.log L / Real.log N

theorem rpow_neg_huxleyThresholdLossSigma
    {N : ℕ} (hN : 2 ≤ N) {sigma L : ℝ} (hL : 0 < L) :
    (N : ℝ) ^ (-huxleyThresholdLossSigma N sigma L) =
      (N : ℝ) ^ (-sigma) / L := by
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hNR
  have hlogN : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNR)
  rw [huxleyThresholdLossSigma]
  rw [show -(sigma + Real.log L / Real.log N) =
      (-sigma) + (-(Real.log L / Real.log N)) by ring,
    Real.rpow_add hN0]
  have hpow : (N : ℝ) ^ (Real.log L / Real.log N) = L := by
    rw [Real.rpow_def_of_pos hN0]
    rw [show Real.log (N : ℝ) * (Real.log L / Real.log N) = Real.log L by
      field_simp]
    exact Real.exp_log hL
  have hpowneg : (N : ℝ) ^ (-(Real.log L / Real.log N)) = L⁻¹ := by
    rw [Real.rpow_neg hN0.le, hpow]
  rw [hpowneg]
  ring

/-- Lemma 4.1 with an explicit finite threshold loss. The loss is transferred exactly into the
amplitude exponent, so no constant or polylog factor is hidden. -/
theorem exists_lemma41_huxley_threshold_loss
    {eps D : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) (hD1 : 1 ≤ D) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T : ℝ) (N : ℕ) (sigma L : ℝ)
      (c : ℕ → ℂ) (S : Finset ℝ),
      T₀ ≤ T → 2 ≤ N → 1 ≤ L →
      T ^ ((9 : ℝ) / 11) ≤ (N : ℝ) → (N : ℝ) ≤ T ^ (1 - eps) →
      5 * eps ≤ huxleyThresholdLossSigma N sigma L →
      huxleyThresholdLossSigma N sigma L ≤ 7 / 32 - 5 * eps →
      2400 * D ^ 2 ≤
        (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma N sigma L) →
      (∀ n ∈ Finset.Ico N (2 * N), ‖c n‖ ≤ D) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ x ∈ S, (N : ℝ) ^ (-sigma) / L ≤ ‖blockPoly N c 1 x‖) →
      (S.card : ℝ) ≤
        T ^ (2 * huxleyThresholdLossSigma N sigma L - eps ^ 2 / 5) := by
  obtain ⟨T₀, hT₀1, hbase⟩ := exists_lemma41_huxley heps hepss hD1
  refine ⟨T₀, hT₀1, ?_⟩
  intro T N sigma L c S hT hN hL hNlo hNhi hsl hsh hthr hc hsep hspread hbig
  apply hbase T N (huxleyThresholdLossSigma N sigma L) c S hT (by omega)
    hNlo hNhi hsl hsh hthr hc hsep hspread
  intro x hx
  rw [rpow_neg_huxleyThresholdLossSigma hN (lt_of_lt_of_le zero_lt_one hL)]
  exact hbig x hx

end RHTower.Sieve
