import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard
import GaloisForLFunctions.HTGeometry.QuotientProximityBound
import GaloisForLFunctions.HTGeometry.NevanlinnaMaxModulusBridge
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationEntire

noncomputable section

open Complex Metric Set ValueDistribution

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.QuotientProximity

/-- **Finite order descends to removable quotients.**  If `G = H F`, all three functions are
entire, `H` is zero-free, and `F,G` have finite-order envelopes, then `H` has one too.  The proof
uses the quotient characteristic inequality followed by the Poisson bound for zero-free entire
functions; no minimum-modulus hypothesis is used. -/
theorem FiniteOrderEnvelope.of_entire_quotient
    {F G H : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (hG : AnalyticOnNhd ℂ G Set.univ)
    (hH : AnalyticOnNhd ℂ H Set.univ)
    (hFne : ∃ z, F z ≠ 0) (hGne : ∃ z, G z ≠ 0)
    (hHzero : ∀ z, H z ≠ 0) (hfac : ∀ z, G z = H z * F z)
    (hFfinite : FiniteOrderEnvelope F) (hGfinite : FiniteOrderEnvelope G) :
    FiniteOrderEnvelope H := by
  obtain ⟨CF, dF, hCF, hFbound⟩ := hFfinite
  obtain ⟨CG, dG, hCG, hGbound⟩ := hGfinite
  obtain ⟨zF, hzF⟩ := hFne
  obtain ⟨zG, hzG⟩ := hGne
  have hFdiff : Differentiable ℂ F := by
    rw [← Complex.analyticOnNhd_univ_iff_differentiable]
    exact hF
  have hGdiff : Differentiable ℂ G := by
    rw [← Complex.analyticOnNhd_univ_iff_differentiable]
    exact hG
  have hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤ := by
    intro z
    rw [(hF z (Set.mem_univ z)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_ne_top_of_entire hFdiff hzF z]
  have hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤ := by
    intro z
    rw [(hG z (Set.mem_univ z)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_ne_top_of_entire hGdiff hzG z]
  obtain ⟨K, hK⟩ := proximity_quotient_le hF hG hH hFord hGord hfac
  let d : ℕ := max dF dG
  let C : ℝ := 3 * (CG * 3 ^ dG + CF * 3 ^ dF + |K|)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, d, hC, fun z => ?_⟩
  let R : ℝ := 2 * (1 + ‖z‖)
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hR0 : (0 : ℝ) ≤ R := by dsimp [R]; linarith
  have hR1 : (1 : ℝ) ≤ R := by dsimp [R]; linarith
  have hmerF : MeromorphicOn F (sphere (0 : ℂ) R) :=
    fun w _ => (hF w (Set.mem_univ w)).meromorphicAt
  have hmerG : MeromorphicOn G (sphere (0 : ℂ) R) :=
    fun w _ => (hG w (Set.mem_univ w)).meromorphicAt
  have hpF : proximity F ⊤ R ≤ CF * (1 + R) ^ dF := by
    refine le_trans (proximity_top_le_posLog_of_norm
      (M := Real.exp (CF * (1 + R) ^ dF)) hR0 hmerF ?_) ?_
    · intro w hw
      simpa [hw] using hFbound w
    · rw [Real.posLog, Real.log_exp]
      exact max_le (mul_nonneg hCF (by positivity)) le_rfl
  have hpG : proximity G ⊤ R ≤ CG * (1 + R) ^ dG := by
    refine le_trans (proximity_top_le_posLog_of_norm
      (M := Real.exp (CG * (1 + R) ^ dG)) hR0 hmerG ?_) ?_
    · intro w hw
      simpa [hw] using hGbound w
    · rw [Real.posLog, Real.log_exp]
      exact max_le (mul_nonneg hCG (by positivity)) le_rfl
  have hshape : 1 + R ≤ 3 * (1 + ‖z‖) := by
    dsimp [R]
    linarith
  have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith
  have hpowF : (1 + R) ^ dF ≤ 3 ^ dF * (1 + ‖z‖) ^ d := by
    calc
      (1 + R) ^ dF ≤ (3 * (1 + ‖z‖)) ^ dF :=
        pow_le_pow_left₀ (by positivity) hshape dF
      _ = 3 ^ dF * (1 + ‖z‖) ^ dF := by rw [mul_pow]
      _ ≤ 3 ^ dF * (1 + ‖z‖) ^ d := by
        gcongr
        exact le_max_left _ _
  have hpowG : (1 + R) ^ dG ≤ 3 ^ dG * (1 + ‖z‖) ^ d := by
    calc
      (1 + R) ^ dG ≤ (3 * (1 + ‖z‖)) ^ dG :=
        pow_le_pow_left₀ (by positivity) hshape dG
      _ = 3 ^ dG * (1 + ‖z‖) ^ dG := by rw [mul_pow]
      _ ≤ 3 ^ dG * (1 + ‖z‖) ^ d := by
        gcongr
        exact le_max_right _ _
  have hpF' : proximity F ⊤ R ≤
      (CF * 3 ^ dF) * (1 + ‖z‖) ^ d := by
    calc
      proximity F ⊤ R ≤ CF * (1 + R) ^ dF := hpF
      _ ≤ CF * (3 ^ dF * (1 + ‖z‖) ^ d) :=
        mul_le_mul_of_nonneg_left hpowF hCF
      _ = _ := by ring
  have hpG' : proximity G ⊤ R ≤
      (CG * 3 ^ dG) * (1 + ‖z‖) ^ d := by
    calc
      proximity G ⊤ R ≤ CG * (1 + R) ^ dG := hpG
      _ ≤ CG * (3 ^ dG * (1 + ‖z‖) ^ d) :=
        mul_le_mul_of_nonneg_left hpowG hCG
      _ = _ := by ring
  have hpow1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ hbase
  have hK' : K ≤ |K| * (1 + ‖z‖) ^ d := by
    exact (le_abs_self K).trans (by nlinarith [abs_nonneg K])
  have hpH : proximity H ⊤ R ≤
      (CG * 3 ^ dG + CF * 3 ^ dF + |K|) * (1 + ‖z‖) ^ d := by
    have hq := hK R hR1
    nlinarith
  have hlog := log_norm_le_three_mul_proximity hH hHzero z
  change Real.log ‖H z‖ ≤ 3 * proximity H ⊤ R at hlog
  have hlog' : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ d := by
    dsimp [C]
    nlinarith
  rw [← Real.exp_log (norm_pos_iff.mpr (hHzero z))]
  exact Real.exp_le_exp.mpr hlog'

end GaloisForLFunctions.HTGeometry
