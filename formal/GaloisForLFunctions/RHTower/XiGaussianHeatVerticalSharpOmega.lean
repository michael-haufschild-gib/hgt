import GaloisForLFunctions.RHTower.XiGaussianHeatVerticalOmegaLaw
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# The sharp Ω-constant of the vertical heat trace

On the vertical line `Re τ = a` the heat trace satisfies `‖ν(a+ib)‖ ≤ ν(a)` for all `b` iff RH holds
(`riemannHypothesis_iff_forall_norm_xiGaussianHeatTraceC_le_real`).  This module shows that the
constant `ν(a)` is attained in the limsup, unconditionally.

**Theorem** (`frequently_le_norm_xiGaussianHeatTraceC`).  For every `a > 0` and `ε > 0` there are
arbitrarily large `b` with `‖ν(a+ib)‖ ≥ ν(a) - ε`.

So `limsup_{b→∞} ‖ν(a+ib)‖ ≥ ν(a)` always, and RH is exactly the statement that this limsup is not
exceeded.  In prime terms (`frequently_le_norm_gaussianPrimeChirpSum_sub_main`):
`‖S(a+ib) - M(a+ib)‖ ≥ (ν(a) - ε) √(π|a+ib|)` for arbitrarily large `b`.  The O-constant `√π ν(a)` of
the RH bound is therefore also the Ω-constant.

Mechanism.  Under RH, `ν(a+ib) = Σ_q e^{-aλ_q} e^{-ibλ_q}` with real `λ_q`.  Truncate to a finite
set carrying all but `ε/4` of the mass.  Simultaneous Dirichlet approximation
(`HTGeometry.exists_simultaneous_dirichlet`) gives arbitrarily large `b`
with every `bλ_q` within `2π/N` of `2πℤ`, so `Re ν(a+ib) ≥ ν(a) - ε`.  Without RH the trace is
unbounded on `[0, ∞)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Boundedness of the vertical trace on a half-line already gives RH. -/
theorem riemannHypothesis_of_xiGaussianHeatTraceC_bounded_eventually {a : ℝ} (ha : 0 < a)
    {B C : ℝ} (h : ∀ b : ℝ, B ≤ b → ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ ≤ C) :
    RiemannHypothesis := by
  have hcont := continuous_xiGaussianHeatTraceC_vertical ha
  rw [riemannHypothesis_iff_xiGaussianHeatTraceC_bounded_on_vertical_line ha]
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -|B|) (b := |B|)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K C, fun b => ?_⟩
  rcases le_or_gt |B| |b| with hbig | hsmall
  · rcases le_or_gt 0 b with hb | hb
    · exact le_max_of_le_right (h b (by rw [abs_of_nonneg hb] at hbig; linarith [le_abs_self B]))
    · have hsym : xiGaussianHeatTraceC ((a : ℂ) + b * I) =
          (starRingEnd ℂ) (xiGaussianHeatTraceC ((a : ℂ) + (-b : ℝ) * I)) := by
        rw [← xiGaussianHeatTraceC_conj]
        congr 1
        apply Complex.ext <;> simp
      rw [hsym, Complex.norm_conj]
      exact le_max_of_le_right (h (-b) (by rw [abs_of_neg hb] at hbig; linarith [le_abs_self B]))
  · exact le_max_of_le_left (hK b ⟨by linarith [neg_abs_le b, abs_nonneg b],
      by linarith [le_abs_self b]⟩)

/-- **Sharp Ω-constant.**  For every `a > 0` and `ε > 0`, `‖ν(a+ib)‖ ≥ ν(a) - ε` for arbitrarily
large `b`. -/
theorem frequently_le_norm_xiGaussianHeatTraceC {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ᶠ b : ℝ in atTop, xiGaussianHeatTraceReal a - ε ≤ ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ := by
  classical
  by_cases hRH : RiemannHypothesis
  · rw [Filter.frequently_atTop]
    intro B
    set c : XiZeroCopy → ℝ := fun q => Real.exp (-(a * xiSpectralSqRe q))
    have hc : Summable c := by
      have h := summable_norm_xiGaussianHeatTermC (τ := (a : ℂ)) (by simpa using ha)
      refine h.congr fun q => ?_
      rw [norm_xiGaussianHeatTermC]
      simp [c, xiSpectralSqRe]
    have hc0 : ∀ q, 0 < c q := fun q => Real.exp_pos _
    have hreal : xiGaussianHeatTraceReal a = ∑' q, c q := by
      rw [xiGaussianHeatTraceReal_eq_tsum_re ha]
      refine tsum_congr fun q => ?_
      have him0 : (xiSpectralPoint q ^ (2 : ℕ)).im = 0 := by
        rw [xiSpectralSq_eq_ofReal_re_of_rh hRH q, Complex.ofReal_im]
      rw [xiGaussianHeatTerm, Complex.exp_re]
      simp [c, xiSpectralSqRe, Complex.mul_re, him0]
    set V : ℝ := ∑' q, c q
    -- a finite set carrying all but `ε/4` of the mass
    obtain ⟨F, hF⟩ : ∃ F : Finset XiZeroCopy, V - ε / 4 < ∑ q ∈ F, c q := by
      have hlim := hc.hasSum
      have := (hlim.eventually (Ioi_mem_nhds (show V - ε / 4 < V by linarith)))
      obtain ⟨F, hF⟩ := Filter.eventually_atTop.1 this
      exact ⟨F, hF F le_rfl⟩
    -- Dirichlet: all `b λ_q`, `q ∈ F`, close to `2πℤ`
    set B' : ℝ := max B 1
    have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
    set SF : ℝ := ∑ q ∈ F, c q
    have hSF0 : 0 ≤ SF := Finset.sum_nonneg fun q _ => (hc0 q).le
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * Real.pi ^ 2 * SF < (N : ℝ) ^ 2 * (ε / 4) ∧ 0 < N := by
      obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt (2 * Real.pi ^ 2 * SF / (ε / 4)) + 1)
      refine ⟨N, ?_, by exact_mod_cast (lt_of_le_of_lt (by positivity) hN : (0 : ℝ) < N)⟩
      have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi ^ 2 * SF / (ε / 4) by positivity)
      have hN' : Real.sqrt (2 * Real.pi ^ 2 * SF / (ε / 4)) < N := by linarith
      have hsq := pow_lt_pow_left₀ hN' (Real.sqrt_nonneg _) two_ne_zero
      rw [hs, div_lt_iff₀ (by positivity)] at hsq
      linarith
    obtain ⟨hNbig, hNpos⟩ := hN
    obtain ⟨n, hn1, -, hn⟩ := GaloisForLFunctions.HTGeometry.exists_simultaneous_dirichlet
      (fun i : Fin F.card => B' * xiSpectralSqRe (F.equivFin.symm i : XiZeroCopy) / (2 * Real.pi))
      hNpos
    set b : ℝ := n * B'
    have hbB : B ≤ b := by
      have : B' ≤ b := by
        simp only [b]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith
      exact (le_max_left _ _).trans this
    refine ⟨b, hbB, ?_⟩
    -- the real part of the trace at `a + ib`
    have hterm : ∀ q : XiZeroCopy, (xiGaussianHeatTermC ((a : ℂ) + b * I) q).re =
        c q * Real.cos (b * xiSpectralSqRe q) := by
      intro q
      rw [xiGaussianHeatTermC, xiSpectralSq_eq_ofReal_xiSpectralSqRe_of_rh hRH, Complex.exp_re]
      have hre : (-((a : ℂ) + b * I) * (xiSpectralSqRe q : ℂ)).re = -(a * xiSpectralSqRe q) := by
        simp [Complex.mul_re]
      have him : (-((a : ℂ) + b * I) * (xiSpectralSqRe q : ℂ)).im = -(b * xiSpectralSqRe q) := by
        simp [Complex.mul_im]
      rw [hre, him, Real.cos_neg]
    have hτ : 0 < ((a : ℂ) + b * I).re := by simpa using ha
    have hsumC := summable_norm_xiGaussianHeatTermC hτ
    have hsumre : Summable (fun q => (xiGaussianHeatTermC ((a : ℂ) + b * I) q).re) :=
      (Complex.reCLM.summable (hsumC.of_norm))
    have hre_tsum : (xiGaussianHeatTraceC ((a : ℂ) + b * I)).re =
        ∑' q, c q * Real.cos (b * xiSpectralSqRe q) := by
      rw [xiGaussianHeatTraceC, Complex.re_tsum hsumC.of_norm]
      exact tsum_congr hterm
    have hsumcos : Summable (fun q => c q * Real.cos (b * xiSpectralSqRe q)) :=
      hsumre.congr hterm
    -- split off `F`
    have hsplit := hsumcos.sum_add_tsum_compl (s := F)
    have hcompl : -(V - SF) ≤ ∑' q : ↥((F : Set XiZeroCopy)ᶜ),
        c q * Real.cos (b * xiSpectralSqRe q) := by
      have hcs := hc.sum_add_tsum_compl (s := F)
      have hcsub : Summable (fun q : ↥((F : Set XiZeroCopy)ᶜ) => c q) :=
        hc.comp_injective Subtype.coe_injective
      have hle : (∑' q : ↥((F : Set XiZeroCopy)ᶜ), -(c q)) ≤
          ∑' q : ↥((F : Set XiZeroCopy)ᶜ), c q * Real.cos (b * xiSpectralSqRe q) :=
        Summable.tsum_le_tsum (fun q => by
          have := Real.neg_one_le_cos (b * xiSpectralSqRe q)
          nlinarith [hc0 q])
          hcsub.neg (hsumcos.comp_injective Subtype.coe_injective)
      rw [tsum_neg] at hle
      linarith
    -- each term in `F` is nearly `c q`
    have hF_cos : ∑ q ∈ F, c q * (1 - (2 * Real.pi / N) ^ 2 / 2) ≤
        ∑ q ∈ F, c q * Real.cos (b * xiSpectralSqRe q) := by
      refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (hc0 q).le
      obtain ⟨k, hk'⟩ := hn (F.equivFin ⟨q, hq⟩)
      simp only [Equiv.symm_apply_apply] at hk'
      have hk : |(n : ℝ) * (B' * xiSpectralSqRe q / (2 * Real.pi)) - k| ≤ 1 / N := hk'.le
      have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hdist : |b * xiSpectralSqRe q - 2 * Real.pi * k| ≤ 2 * Real.pi / N := by
        have e : b * xiSpectralSqRe q - 2 * Real.pi * k =
            2 * Real.pi * ((n : ℝ) * (B' * xiSpectralSqRe q / (2 * Real.pi)) - k) := by
          simp only [b]; field_simp
        rw [e, abs_mul, abs_of_pos (by positivity)]
        calc 2 * Real.pi * |(n : ℝ) * (B' * xiSpectralSqRe q / (2 * Real.pi)) - k|
            ≤ 2 * Real.pi * (1 / N) := mul_le_mul_of_nonneg_left hk (by positivity)
          _ = 2 * Real.pi / N := by ring
      have hcos : Real.cos (b * xiSpectralSqRe q) =
          Real.cos (b * xiSpectralSqRe q - 2 * Real.pi * k) := by
        rw [show b * xiSpectralSqRe q - 2 * Real.pi * k = b * xiSpectralSqRe q - (k : ℤ) * (2 * Real.pi)
          by ring, Real.cos_sub_int_mul_two_pi]
      rw [hcos]
      have hlow := Real.one_sub_sq_div_two_le_cos (x := b * xiSpectralSqRe q - 2 * Real.pi * k)
      have hsq : (b * xiSpectralSqRe q - 2 * Real.pi * k) ^ 2 ≤ (2 * Real.pi / N) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdist 2
      linarith
    have hF_eq : ∑ q ∈ F, c q * (1 - (2 * Real.pi / N) ^ 2 / 2) =
        SF - (2 * Real.pi ^ 2 / (N : ℝ) ^ 2) * SF := by
      rw [← Finset.sum_mul]
      have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
      have e : (2 * Real.pi / N) ^ 2 / 2 = 2 * Real.pi ^ 2 / (N : ℝ) ^ 2 := by
        field_simp
      rw [e]
      ring
    have hsmall : (2 * Real.pi ^ 2 / (N : ℝ) ^ 2) * SF ≤ ε / 4 := by
      have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      linarith
    have hre_low : V - ε ≤ (xiGaussianHeatTraceC ((a : ℂ) + b * I)).re := by
      rw [hre_tsum, ← hsplit]
      linarith
    rw [hreal]
    exact hre_low.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  · rw [Filter.frequently_atTop]
    intro B
    by_contra hcon
    push Not at hcon
    exact hRH (riemannHypothesis_of_xiGaussianHeatTraceC_bounded_eventually ha
      (C := xiGaussianHeatTraceReal a - ε) fun b hb => (hcon b hb).le)

/-- **Sharp Ω-law for the prime chirp.**  For every `a > 0` and `ε > 0`,
`‖S(a+ib) - M(a+ib)‖ ≥ (ν(a) - ε) √(π |a+ib|)` for arbitrarily large `b`.  Under RH the reverse
inequality `‖S - M‖ ≤ ν(a) √(π|τ|)` holds for all `b`, so the constant is exact. -/
theorem frequently_le_norm_gaussianPrimeChirpSum_sub_main {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ᶠ b : ℝ in atTop,
      (xiGaussianHeatTraceReal a - ε) * (Real.sqrt Real.pi * Real.sqrt ‖(a : ℂ) + b * I‖) ≤
        ‖gaussianPrimeChirpSum ((a : ℂ) + b * I) -
          (gaussianArchCriticalC ((a : ℂ) + b * I) + gaussianArchPoleC ((a : ℂ) + b * I)) /
            ((Real.pi : ℂ) / ((a : ℂ) + b * I)) ^ (1 / 2 : ℂ)‖ := by
  refine (frequently_le_norm_xiGaussianHeatTraceC ha hε).mono fun b hb => ?_
  rw [norm_gaussianPrimeChirpSum_sub_main ha b]
  have hpos : 0 ≤ Real.sqrt Real.pi * Real.sqrt ‖(a : ℂ) + b * I‖ := by positivity
  calc (xiGaussianHeatTraceReal a - ε) * (Real.sqrt Real.pi * Real.sqrt ‖(a : ℂ) + b * I‖)
      ≤ ‖xiGaussianHeatTraceC ((a : ℂ) + b * I)‖ *
          (Real.sqrt Real.pi * Real.sqrt ‖(a : ℂ) + b * I‖) :=
        mul_le_mul_of_nonneg_right hb hpos
    _ = _ := by ring

end

end RHTower
