import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentDirichletSeriesIsAConstituent
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawOnAStripSurvivesSummablePoles
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentExpansionIsAConstituentInAStrip
import GaloisForLFunctions.HTGeometry.SummableLogarithmicPrincipalParts
import GaloisForLFunctions.Bottcher.ZeroSet

/-!
# A pure expansion has nonsummable zeta residues

For a nonzero real-scale Wiener expansion whose strip zeros lie on the critical line,
any zero forces divergence of the sum of `|mρ ζ(ρ)/ρ|`. Summably small failures to share
zeros with zeta cannot preserve the expansion. The proof removes all principal parts,
then identifies the left and right logarithmic derivatives by the jump law.
-/

open Complex Filter Topology Set Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

/-- The zeros of an expansion on the critical line. -/
def criticalExpansionZeros (c : Scale → ℂ) : Set ℂ :=
  {p | p.re = 1 / 2 ∧ expansion c p = 0}

/-- The multiplicity residue of `−ζ F'/(s F)`. -/
def expansionZetaResidue (c : Scale → ℂ) (p : ℂ) : ℂ :=
  HTGeometry.weightedLogResidue (expansion c) (fun z => -(riemannZeta z / z)) p

/-- Summable residue errors identify the logarithmic derivatives on both sides of the line. -/
theorem logDeriv_expansion_eq_of_summable_residues {c gL gR : Scale → ℂ} {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 4) (hc : WSummable (1 / 2 - 2 * η) (1 / 2 + 2 * η) c)
    (hAP : IsStripAlmostPeriodicOn (expansion c) (1 / 2) (η / 2))
    (hoff : ∀ s : ℂ, |s.re - 1 / 2| < 2 * η → s.re ≠ 1 / 2 → expansion c s ≠ 0)
    (hr : Summable fun p : criticalExpansionZeros c => ‖expansionZetaResidue c p‖)
    (hne : c ≠ 0)
    (hgL : ∀ σ₁ σ₂ : ℝ, 1 / 2 - 2 * η < σ₁ → σ₁ ≤ σ₂ → σ₂ < 1 / 2 → WSummable σ₁ σ₂ gL)
    (hGL : ∀ s : ℂ, 1 / 2 - 2 * η < s.re → s.re < 1 / 2 →
      deriv (expansion c) s / expansion c s = expansion gL s)
    (hgR : ∀ σ₁ σ₂ : ℝ, 1 / 2 < σ₁ → σ₁ ≤ σ₂ → σ₂ < 1 / 2 + 2 * η → WSummable σ₁ σ₂ gR)
    (hGR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + 2 * η →
      deriv (expansion c) s / expansion c s = expansion gR s) : gL = gR := by
  have hV : ∀ z : ℂ, 1 / 2 - 2 * η < z.re → z.re < 1 / 2 + 2 * η → |z.re - 1 / 2| < 2 * η :=
    fun z h1 h2 => abs_lt.mpr ⟨by linarith, by linarith⟩
  have hFd : DifferentiableOn ℂ (expansion c)
      {z : ℂ | 1 / 2 - 2 * η < z.re ∧ z.re < 1 / 2 + 2 * η} := differentiableOn_expansion hc
  have hsumR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η →
      Summable fun q : Scale => ‖gR q‖ * q.toReal ^ σ := fun σ h1 h2 => by
    refine (hgR σ σ h1 le_rfl (by linarith)).congr fun q => ?_
    rw [stripWeight_self]
  have hsumL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 →
      Summable fun q : Scale => ‖gL q‖ * q.toReal ^ σ := fun σ h1 h2 => by
    refine (hgL σ σ (by linarith) le_rfl h2).congr fun q => ?_
    rw [stripWeight_self]
  -- the quotient `−ζ F'/(sF)` on the strip of half-width `η`
  set U : Set ℂ := {z : ℂ | 1 / 2 - η < z.re ∧ z.re < 1 / 2 + η} with hU
  have hUo : IsOpen U := isOpen_openStrip _ _
  have hUV : ∀ z ∈ U, z ∈ {z : ℂ | 1 / 2 - 2 * η < z.re ∧ z.re < 1 / 2 + 2 * η} := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hfd : DifferentiableOn ℂ (expansion c) U := hFd.mono hUV
  have hgd : DifferentiableOn ℂ (fun z : ℂ => -(riemannZeta z / z)) U :=
    differentiableOn_neg_riemannZeta_div (by linarith) (by linarith)
  -- a real point right of the line, where `F` does not vanish
  set s₀ : ℂ := ((1 / 2 + η / 2 : ℝ) : ℂ) with hs₀
  have hs₀re : s₀.re = 1 / 2 + η / 2 := by rw [hs₀, ofReal_re]
  have hs₀U : s₀ ∈ U := ⟨by rw [hs₀re]; linarith, by rw [hs₀re]; linarith⟩
  have hp : expansion c s₀ ≠ 0 :=
    hoff s₀ (by rw [hs₀re, abs_lt]; constructor <;> linarith) (by rw [hs₀re]; linarith)
  have hfin : ∀ z ∈ U, analyticOrderAt (expansion c) z ≠ ⊤ := by
    intro z hz htop
    have hall := (hFd.analyticOnNhd (isOpen_openStrip _ _)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_openStrip _ _) (hUV z hz) (analyticOrderAt_eq_top.mp htop)
    exact hp (hall (hUV s₀ hs₀U))
  let E := criticalExpansionZeros c
  let r := expansionZetaResidue c
  have hPre : ∀ p ∈ E, p.re = 1 / 2 := fun p hp => hp.1
  have hPzero : ∀ p ∈ E, expansion c p = 0 := fun p hp => hp.2
  have hPU : ∀ p ∈ E, p ∈ U := fun p hp =>
    ⟨by rw [hPre p hp]; linarith, by rw [hPre p hp]; linarith⟩
  have hcount : E.Countable :=
    (Bottcher.analyticOnNhd_zeros_countable (hfd.analyticOnNhd hUo)
      (isPreconnected_openStrip _ _) hs₀U hp).mono fun p hp => ⟨hPU p hp, hPzero p hp⟩
  letI : Countable E := hcount.to_subtype
  obtain ⟨Φ, hΦd, hΦ⟩ := HTGeometry.exists_holomorphic_sub_residueCauchySum hUo hfd hgd
    hfin hPzero (fun z hz hz0 => ⟨by
      by_contra hn
      exact hoff z (hV z (hUV z hz).1 (hUV z hz).2) hn hz0, hz0⟩) hr
  change ∀ z ∈ U, expansion c z ≠ 0 →
    Φ z = deriv (expansion c) z * -(riemannZeta z / z) / expansion c z -
      ∑' p : E, r p / (z - p) at hΦ
  have hΦR : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 / 2 + η →
      Φ z = -(riemannZeta z / z) * (∑' q : Scale, gR q * (q.toReal : ℂ) ^ z) -
        ∑' p : E, r p / (z - p) := by
    intro z h1 h2
    have hz0 : expansion c z ≠ 0 := hoff z (hV z (by linarith) (by linarith)) (ne_of_gt h1)
    have hG : deriv (expansion c) z / expansion c z = ∑' q : Scale, gR q * (q.toReal : ℂ) ^ z :=
      hGR z h1 (by linarith)
    rw [hΦ z ⟨by linarith, h2⟩ hz0, ← hG]
    ring
  have hΦL : ∀ z : ℂ, 1 / 2 - η < z.re → z.re < 1 / 2 →
      Φ z = -(riemannZeta z / z) * (∑' q : Scale, gL q * (q.toReal : ℂ) ^ z) -
        ∑' p : E, r p / (z - p) := by
    intro z h1 h2
    have hz0 : expansion c z ≠ 0 := hoff z (hV z (by linarith) (by linarith)) (ne_of_lt h2)
    have hG : deriv (expansion c) z / expansion c z = ∑' q : Scale, gL q * (q.toReal : ℂ) ^ z :=
      hGL z (by linarith) h2
    rw [hΦ z ⟨h1, by linarith⟩ hz0, ← hG]
    ring
  -- bounds on the two boundary lines and at good heights
  have hx : (1 / 2 - η / 2 : ℝ) < 1 / 2 + η / 2 := by linarith
  have hWR : WSummable (1 / 2 + η / 2) (1 / 2 + η / 2) gR :=
    hgR _ _ (by linarith) le_rfl (by linarith)
  have hWL : WSummable (1 / 2 - η / 2) (1 / 2 - η / 2) gL :=
    hgL _ _ (by linarith) le_rfl (by linarith)
  have hWD : WSummable (1 / 2 - η / 2) (1 / 2 + η / 2) fun q => c q * ((q.log : ℝ) : ℂ) :=
    hc.log_mul (by linarith) hx.le (by linarith)
  have hζ : ∀ z : ℂ, 1 / 2 - η / 2 ≤ z.re → z.re ≤ 1 / 2 + η / 2 →
      ‖-(riemannZeta z / z)‖ ≤ 8 := fun z h1 h2 => by
    rw [norm_neg]
    exact norm_riemannZeta_div_le_eight (by linarith) (by linarith)
  have hcontF : ContinuousOn (expansion c) {z : ℂ | |z.re - 1 / 2| ≤ η / 2} :=
    hFd.continuousOn.mono fun z hz => by
      have h := abs_le.mp (show |z.re - 1 / 2| ≤ η / 2 from hz)
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℝ, expansion c (((1 / 2 : ℝ) : ℂ) + (T₀ : ℂ) * I) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (eq_zero_of_expansion_eq_zero (le_refl (1 / 2 : ℝ))
      (hc.mono (by linarith) le_rfl (by linarith)) fun z h1 h2 => ?_)
    have hre : z.re = 1 / 2 := le_antisymm h2 h1
    have hz : z = ((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hre]
    rw [hz]
    exact hcon z.im
  have hseg : ∀ x : ℝ, |x - 1 / 2| ≤ η / 2 → expansion c ((x : ℂ) + (T₀ : ℂ) * I) ≠ 0 := by
    intro x hx'
    have hre : ((x : ℂ) + (T₀ : ℂ) * I).re = x := by simp
    by_cases hx2 : x = 1 / 2
    · rw [hx2]
      exact hT₀
    · exact hoff _ (by rw [hre]; exact lt_of_le_of_lt hx' (by linarith)) (by rw [hre]; exact hx2)
  obtain ⟨μ, hμ, L, hgoodF⟩ := exists_good_heights (by positivity) hcontF hAP hseg
  set NR : ℝ := ∑' q, ‖gR q‖ * stripWeight (1 / 2 + η / 2) (1 / 2 + η / 2) q with hNR
  set NL : ℝ := ∑' q, ‖gL q‖ * stripWeight (1 / 2 - η / 2) (1 / 2 - η / 2) q with hNL
  set MD : ℝ := ∑' q, ‖c q * ((q.log : ℝ) : ℂ)‖ *
    stripWeight (1 / 2 - η / 2) (1 / 2 + η / 2) q with hMD
  have hNR0 : 0 ≤ NR := tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le
  have hNL0 : 0 ≤ NL := tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le
  have hMD0 : 0 ≤ MD := tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le
  have hquot0 : 0 ≤ MD * 8 / μ := by positivity
  have hFdiff : ∀ w : ℂ, 1 / 2 - η / 2 ≤ w.re → w.re ≤ 1 / 2 + η / 2 →
      DifferentiableAt ℂ (expansion c) w := fun w hw1 hw2 =>
    (hfd w ⟨by linarith, by linarith⟩).differentiableAt (hUo.mem_nhds ⟨by linarith, by linarith⟩)
  have hFder : ∀ w : ℂ, 1 / 2 - η / 2 ≤ w.re → w.re ≤ 1 / 2 + η / 2 →
      ‖deriv (expansion c) w‖ ≤ MD := fun w hw1 hw2 => by
    rw [deriv_expansion hc (by linarith) (by linarith)]
    exact hWD.norm_expansion_le hw1 hw2
  set ρ : ℝ := ∑' p : E, ‖r p‖ with hρ
  have hρ0 : 0 ≤ ρ := tsum_nonneg fun _ => norm_nonneg _
  set C : ℝ := 8 * NR + 8 * NL + MD * 8 / μ + ρ / (η / 2) + ρ / (μ / (MD + 1)) with hC
  have hC1 : 0 ≤ ρ / (η / 2) := by positivity
  have hC2 : 0 ≤ ρ / (μ / (MD + 1)) := by positivity
  have hlineB : ∀ z : ℂ, z.re = 1 / 2 - η / 2 ∨ z.re = 1 / 2 + η / 2 → ‖Φ z‖ ≤ C := by
    rintro z (hz | hz)
    · have hdist : ∀ p ∈ E, η / 2 ≤ ‖z - p‖ := fun p hp => by
        have h := Complex.abs_re_le_norm (z - p)
        rw [Complex.sub_re, hz, hPre p hp, show (1 / 2 - η / 2 - 1 / 2 : ℝ) = -(η / 2) by ring,
          abs_neg, abs_of_pos (by positivity)] at h
        exact h
      rw [hΦL z (by rw [hz]; linarith) (by rw [hz]; linarith)]
      have h1 := hζ z (by rw [hz]) (by rw [hz]; linarith)
      have h2 : ‖∑' q : Scale, gL q * (q.toReal : ℂ) ^ z‖ ≤ NL :=
        hWL.norm_expansion_le (le_of_eq hz.symm) (le_of_eq hz)
      have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
      have h4 := HTGeometry.norm_residueCauchySum_le hr (by positivity : (0 : ℝ) < η / 2) hdist
      have h5 := norm_sub_le (-(riemannZeta z / z) * ∑' q : Scale, gL q * (q.toReal : ℂ) ^ z)
        (∑' p : E, r p / (z - p))
      rw [norm_mul] at h5
      rw [hC]
      linarith
    · have hdist : ∀ p ∈ E, η / 2 ≤ ‖z - p‖ := fun p hp => by
        have h := Complex.abs_re_le_norm (z - p)
        rw [Complex.sub_re, hz, hPre p hp, show (1 / 2 + η / 2 - 1 / 2 : ℝ) = η / 2 by ring,
          abs_of_pos (by positivity)] at h
        exact h
      rw [hΦR z (by rw [hz]; linarith) (by rw [hz]; linarith)]
      have h1 := hζ z (by rw [hz]; linarith) (by rw [hz])
      have h2 : ‖∑' q : Scale, gR q * (q.toReal : ℂ) ^ z‖ ≤ NR :=
        hWR.norm_expansion_le (le_of_eq hz.symm) (le_of_eq hz)
      have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
      have h4 := HTGeometry.norm_residueCauchySum_le hr (by positivity : (0 : ℝ) < η / 2) hdist
      have h5 := norm_sub_le (-(riemannZeta z / z) * ∑' q : Scale, gR q * (q.toReal : ℂ) ^ z)
        (∑' p : E, r p / (z - p))
      rw [norm_mul] at h5
      rw [hC]
      linarith
  have hgoodB : ∀ y : ℝ, ∃ T ∈ Icc y (y + L), ∀ z : ℂ, 1 / 2 - η / 2 ≤ z.re →
      z.re ≤ 1 / 2 + η / 2 → z.im = T → ‖Φ z‖ ≤ C := by
    intro y
    obtain ⟨T, hT, hTF⟩ := hgoodF y
    refine ⟨T, hT, fun z h1 h2 hzT => ?_⟩
    have hμz := hTF z (abs_le.mpr ⟨by linarith, by linarith⟩) hzT
    have hz0 : expansion c z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hμ hμz)
    -- where `F` is bounded below, the exceptional zeros are at distance at least `μ/(MD + 1)`
    have hdist : ∀ p ∈ E, μ / (MD + 1) ≤ ‖z - p‖ := fun p hp =>
      div_le_norm_sub_of_zero hMD0 hFdiff hFder (by rw [hPre p hp]; linarith)
        (by rw [hPre p hp]; linarith) h1 h2 (hPzero p hp) hμz
    rw [hΦ z ⟨by linarith, by linarith⟩ hz0]
    have h8 := hζ z h1 h2
    have e1 : ‖deriv (expansion c) z * -(riemannZeta z / z) / expansion c z‖ ≤ MD * 8 / μ := by
      rw [norm_div, norm_mul]
      exact (div_le_div_of_nonneg_right (mul_le_mul (hFder z h1 h2) h8 (norm_nonneg _) hMD0)
        (norm_nonneg _)).trans (div_le_div_of_nonneg_left (by positivity) hμ hμz)
    have e2 := HTGeometry.norm_residueCauchySum_le hr (by positivity : (0 : ℝ) < μ / (MD + 1)) hdist
    have e3 := norm_sub_le (deriv (expansion c) z * -(riemannZeta z / z) / expansion c z)
      (∑' p : E, r p / (z - p))
    rw [hC]
    linarith
  have hΦb : ∀ w : ℂ, 1 / 2 - η / 2 ≤ w.re → w.re ≤ 1 / 2 + η / 2 → ‖Φ w‖ ≤ C :=
    fun w h1 h2 =>
      norm_le_of_good_heights hx (fun z h1 h2 => (⟨by linarith, by linarith⟩ : z ∈ U)) hΦd
        hlineB hgoodB h1 h2
  -- Summable poles contribute a continuous polar part, hence no fractional-part jump.
  exact (eq_of_strip_of_summable_poles (a := Scale.toReal) Scale.toReal_pos Scale.toReal_injective hη0
    (by linarith) hsumR hsumL hPre hr hΦd hΦb hΦR hΦL).symm

/-- A pure Wiener expansion with summable zeta residues has no zero in its strip. -/
theorem expansion_ne_zero_of_summable_residues {c : Scale → ℂ} {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ 1 / 4) (hc : WSummable (1 / 2 - 2 * η) (1 / 2 + 2 * η) c)
    (hAP : IsStripAlmostPeriodicOn (expansion c) (1 / 2) (η / 2))
    (hoff : ∀ s : ℂ, |s.re - 1 / 2| < 2 * η → s.re ≠ 1 / 2 → expansion c s ≠ 0)
    (hr : Summable fun p : criticalExpansionZeros c => ‖expansionZetaResidue c p‖)
    (hne : c ≠ 0) {s : ℂ} (hs : |s.re - 1 / 2| < 2 * η) : expansion c s ≠ 0 := by
  by_cases hsre : s.re = 1 / 2
  swap
  · exact hoff s hs hsre
  have hV : ∀ z : ℂ, 1 / 2 - 2 * η < z.re → z.re < 1 / 2 + 2 * η → |z.re - 1 / 2| < 2 * η :=
    fun z h1 h2 => abs_lt.mpr ⟨by linarith, by linarith⟩
  have hFd : DifferentiableOn ℂ (expansion c)
      {z : ℂ | 1 / 2 - 2 * η < z.re ∧ z.re < 1 / 2 + 2 * η} := differentiableOn_expansion hc
  -- the logarithmic derivative on the two sides of the line
  obtain ⟨gL, hgL, hGL⟩ := exists_logDeriv_expansion (τ₁ := 1 / 2 - 2 * η) (τ₂ := 1 / 2)
    (by linarith) (hc.mono le_rfl (by linarith) (by linarith))
    (fun z h1 h2 => hoff z (hV z h1 (by linarith)) (ne_of_lt h2))
  obtain ⟨gR, hgR, hGR⟩ := exists_logDeriv_expansion (τ₁ := 1 / 2) (τ₂ := 1 / 2 + 2 * η)
    (by linarith) (hc.mono (by linarith) (by linarith) le_rfl)
    (fun z h1 h2 => hoff z (hV z (by linarith) h2) (ne_of_gt h1))
  have hbc : gL = gR := logDeriv_expansion_eq_of_summable_residues hη0 hη hc hAP hoff hr
    hne hgL hGL hgR hGR
  rw [hbc] at hgL
  -- one expansion on the closed strip of half-width `η`
  have hsumL : Summable fun q : Scale => ‖gR q‖ * q.toReal ^ (1 / 2 - η) := by
    refine (hgL (1 / 2 - η) (1 / 2 - η) (by linarith) le_rfl (by linarith)).congr fun q => ?_
    rw [stripWeight_self]
  have hsumR : Summable fun q : Scale => ‖gR q‖ * q.toReal ^ (1 / 2 + η) := by
    refine (hgR (1 / 2 + η) (1 / 2 + η) (by linarith) le_rfl (by linarith)).congr fun q => ?_
    rw [stripWeight_self]
  have hWg : WSummable (1 / 2 - η) (1 / 2 + η) gR := by
    refine Summable.of_nonneg_of_le
      (fun q => mul_nonneg (norm_nonneg _) (stripWeight_pos _ _ q).le) (fun q => ?_)
      (hsumL.add hsumR)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (Real.rpow_nonneg q.toReal_pos.le _)
      (Real.rpow_nonneg q.toReal_pos.le _)) (norm_nonneg _)
  set U : Set ℂ := {z : ℂ | 1 / 2 - η < z.re ∧ z.re < 1 / 2 + η} with hU
  have hUo : IsOpen U := isOpen_openStrip _ _
  have hUV : ∀ z ∈ U, z ∈ {z : ℂ | 1 / 2 - 2 * η < z.re ∧ z.re < 1 / 2 + 2 * η} := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hfd : DifferentiableOn ℂ (expansion c) U := hFd.mono hUV
  have hHd : DifferentiableOn ℂ (expansion gR) U := differentiableOn_expansion hWg
  -- `F' = H F` right of the line
  set s₀ : ℂ := ((1 / 2 + η / 2 : ℝ) : ℂ) with hs₀
  have hs₀re : s₀.re = 1 / 2 + η / 2 := by rw [hs₀, ofReal_re]
  have hs₀U : s₀ ∈ U := ⟨by rw [hs₀re]; linarith, by rw [hs₀re]; linarith⟩
  have hp : expansion c s₀ ≠ 0 :=
    hoff s₀ (by rw [hs₀re, abs_lt]; constructor <;> linarith) (by rw [hs₀re]; linarith)
  have hev : (fun z => deriv (expansion c) z - expansion gR z * expansion c z) =ᶠ[𝓝 s₀] 0 := by
    have h2 : ∀ᶠ z in 𝓝 s₀, expansion c z ≠ 0 :=
      (hfd.continuousOn.continuousAt (hUo.mem_nhds hs₀U)).eventually_ne hp
    have h3 : ∀ᶠ z : ℂ in 𝓝 s₀, 1 / 2 < z.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        show 1 / 2 < s₀.re
        rw [hs₀re]
        linarith)
    filter_upwards [h2, h3, hUo.mem_nhds hs₀U] with z hz2 hz3 hz4
    show deriv (expansion c) z - expansion gR z * expansion c z = 0
    rw [← hGR z hz3 (by linarith [hz4.2]), div_mul_cancel₀ _ hz2, sub_self]
  have hsU : s ∈ U := ⟨by rw [hsre]; linarith, by rw [hsre]; linarith⟩
  have hfin : analyticOrderAt (expansion c) s ≠ ⊤ := by
    intro htop
    have hall := (hFd.analyticOnNhd (isOpen_openStrip _ _)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isPreconnected_openStrip _ _) (hUV s hsU) (analyticOrderAt_eq_top.mp htop)
    exact hp (hall (hUV s₀ hs₀U))
  exact ne_zero_of_deriv_eq_mul hUo (isPreconnected_openStrip _ _) hfd hHd hs₀U hev hsU hfin


/-- A zero of a Wiener expansion forces either an off-line zero or nonsummable
multiplicity-weighted zeta residues on the critical line. -/
theorem expansion_zero_forces_offLine_or_nonsummable_residues {c : Scale → ℂ} {ω : ℝ}
    (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (hc : WSummable (1 / 2 - ω) (1 / 2 + ω) c) (hne : c ≠ 0)
    {s : ℂ} (hs : |s.re - 1 / 2| < ω) (hs0 : expansion c s = 0) :
    (∃ z : ℂ, |z.re - 1 / 2| < ω ∧ expansion c z = 0 ∧ z.re ≠ 1 / 2) ∨
      ¬ Summable (fun p : criticalExpansionZeros c => ‖expansionZetaResidue c p‖) := by
  classical
  by_cases hoff : ∃ z : ℂ, |z.re - 1 / 2| < ω ∧ expansion c z = 0 ∧ z.re ≠ 1 / 2
  · exact Or.inl hoff
  · refine Or.inr fun hr => ?_
    have hω2 : 2 * (ω / 2) = ω := by ring
    exact expansion_ne_zero_of_summable_residues (η := ω / 2) (by positivity)
      (by linarith only [hω]) (by rwa [hω2])
      (isStripAlmostPeriodicOn_expansion (hc.mono (by linarith only [hω0])
        (by linarith only [hω0]) (by linarith only [hω0])))
      (fun z hz hzre hz0 => hoff ⟨z, by rwa [hω2] at hz, hz0, hzre⟩)
      hr hne (by rwa [hω2]) hs0

#print axioms expansion_zero_forces_offLine_or_nonsummable_residues

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
