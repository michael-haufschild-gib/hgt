import GaloisForLFunctions.RHTower.ZetaWeightedTrace
import GaloisForLFunctions.RHTower.ZetaFrobeniusSurplusSplit
import GaloisForLFunctions.RHTower.ZetaTraceWide
import GaloisForLFunctions.RHTower.SeparatedSimpleZeros
import GaloisForLFunctions.RHTower.HorizontalSimplicityDeficitThmD
import Zeta23.GammaFacts.Complete
import Zeta23.Final

/-!
# Zeta23 analytic inputs discharged in the trace and Theorem D layers

* `GammaFacts` (Stirling-type facts for the archimedean density `μ`) is `Zeta23.gammaFacts`;
  with it, `Zeta23.PrimeSide.mu_increment_bound` supplies the increment constant `K` of
  `|μ(t+r) − μ(t)| ≤ (K|r| + 10r²)/t`.
* `PaperInputs zetaZeroConfig` (explicit formula, Riemann–von Mangoldt, Chebyshev–Mertens,
  mean value, Γ-facts) is `Zeta23.paperInputs_zeta`; it turns the abstract Theorem D variants into
  statements about the zeros of `ζ` for every valid parameter family `P`.
-/

open MeasureTheory Real Finset Filter
open Zeta23 Zeta23.PrimeSide Zeta23.ThmD Zeta23.ZeroSide Zeta23.Assembly

noncomputable section

namespace RHTower

/-! ## Γ-facts and the μ-increment constant -/

/-- **The weighted μ-part of the trace**, with the increment constant supplied by Stirling. -/
theorem exists_abs_weighted_mu_part_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {cϱ : ℝ} {p : Setting} {F : LocalFun}, LocalHypsCore cϱ p F →
      2 ≤ p.T → ∀ {W : ℕ → ℝ}, (∀ k, 0 ≤ W k) → (∀ k, W k ≤ 1) →
      |∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
          - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, W k * Zeta23.mu (p.tau k)|
        ≤ p.d * ((K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / p.T) := by
  obtain ⟨K, hK0, hK⟩ := mu_increment_bound gammaFacts
  exact ⟨K, hK0, fun {_ _ _} hF hT {_} hW0 hW1 =>
    abs_weighted_mu_part_sub_le gammaFacts hF hK0 hK hT hW0 hW1⟩

/-- **The weighted trace** `Σ_k W_k G_kk` against `2πaL Σ_k W_k μ(τ_k)`, with the Γ-facts and the
increment constant discharged. -/
theorem exists_abs_weighted_trace_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {cϱ : ℝ} {p : Setting} {F : LocalFun}, LocalHypsCore cϱ p F →
      2 ≤ p.T → ∀ {W : ℕ → ℝ}, (∀ k, 0 ≤ W k) → (∀ k, W k ≤ 1) →
      |∑ k ∈ Finset.range p.d, W k * GentryA p F k k
          - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, W k * Zeta23.mu (p.tau k)|
        ≤ p.d * ((K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / p.T)
          + p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * F.a * p.L)
            + (12 * Real.sqrt p.X / p.T ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2)
          + |∑ k ∈ Finset.range p.d, W k * (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r))| := by
  obtain ⟨K, hK0, hK⟩ := mu_increment_bound gammaFacts
  exact ⟨K, hK0, fun {_ _ _} hF hT {_} hW0 hW1 =>
    abs_weighted_trace_sub_le gammaFacts hF hK0 hK hT hW0 hW1⟩

/-- Exact split of the Frobenius norm of `ν_X = μ + Π_X + P_X` at every bandwidth. -/
theorem trGt2Nu_nuX_split_unconditional {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) (hT : 0 ≤ p.T) :
    trGt2Nu (Zeta23.nuX p.X) p F
      = Mform F.Phi p.T Zeta23.mu Zeta23.mu + (1 / (2 * π ^ 2)) * ppDiag F.Phi p.T p.X
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X)
        + Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X) + frobSurplus p F :=
  trGt2Nu_nuX_split gammaFacts hF hT

/-- The same split for the bandwidth-`4/3` Gram matrix of `ζ`. -/
theorem trGtildeSq_eq_split_unconditional {cϱ T : ℝ}
    (hF : LocalHypsCoreW cϱ (params43.toSetting T) (params43.localFun T)) (hT : 0 ≤ T) :
    params43.trGtildeSq T
      = Mform (params43.PhiR T) T Zeta23.mu Zeta23.mu
        + (1 / (2 * π ^ 2)) * ppDiag (params43.PhiR T) T (params43.X T)
        + 2 * Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PX (params43.X T))
        + 2 * Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PiX (params43.X T))
        + Mform (params43.PhiR T) T (Zeta23.PiX (params43.X T)) (Zeta23.PiX (params43.X T))
        + frobSurplus (params43.toSetting T) (params43.localFun T) :=
  trGtildeSq_eq_split gammaFacts hF hT

/-- `φ̂(r)² μ(t + r)` is integrable for every `t > 0`. -/
theorem mu_part_integrable_W_unconditional {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) {t : ℝ} (ht0 : 0 < t) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) :=
  mu_part_integrable_W gammaFacts hF ht0

/-- A diagonal Gram entry splits into its `μ`, `Π_X` and `P_X` parts at any bandwidth. -/
theorem GentryA_diag_eq_W_unconditional {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) (k : ℤ) (hk : 0 < p.tau k) :
    GentryA p F k k = (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) :=
  GentryA_diag_eq_W gammaFacts hF k hk

/-! ## Theorem D at the zeros of `ζ`, for every valid parameter family -/

/-- `(HD λ − ε) N(T,2T)` simple critical zeros in `(T,2T]` are horizontally isolated at scale
`5/(2L)`. -/
theorem thmD_horizontal_lam_zeta (P : Params) (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - ε) * (zetaZeroConfig.N T (2 * T) : ℝ)
        ≤ NisoH zetaZeroConfig (5 / (2 * P.L T)) T (2 * T) :=
  thmD_horizontal_lam_abstract zetaZeroConfig paperInputs_zeta P hP hlam

/-- `(HD λ − r² − ε) N(T,2T)` simple critical zeros in `(T,2T]` are `r`-separated. -/
theorem thmD_sep_lam_zeta (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - r ^ 2 - ε) * (zetaZeroConfig.N T (2 * T) : ℝ)
        ≤ NisoSep zetaZeroConfig r (P.L T) T (2 * T) :=
  thmD_sep_lam_abstract zetaZeroConfig paperInputs_zeta P hP hlam hr0 hr1

/-- `(HD λ − ε) N(T,2T)` simple critical zeros in `(T,2T]` are lens-isolated. -/
theorem thmD_lens_lam_zeta (P : Params) (hP : P.Valid) (hlam : P.lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - ε) * (zetaZeroConfig.N T (2 * T) : ℝ)
        ≤ NisoLens zetaZeroConfig (P.L T) T (2 * T) :=
  thmD_lens_lam_abstract zetaZeroConfig paperInputs_zeta P hP hlam

/-- Theorem D with horizontal deficits at every isolation radius `δ`. -/
theorem thmD_horizontal_deficit_lam_zeta (P : Params) (hP : P.Valid) (hlam : P.lam < 1) (δ : ℝ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam - ε) * (zetaZeroConfig.N T (2 * T) : ℝ)
        ≤ NisoH zetaZeroConfig δ T (2 * T)
          + 1 / 24 * P.L T * offMoment zetaZeroConfig (T - D0 T) (2 * T + D0 T)
          + 2 * P.w / P.L T * (zetaZeroConfig.NIprime T : ℝ) :=
  thmD_horizontal_deficit_lam_abstract zetaZeroConfig paperInputs_zeta P hP hlam δ

end RHTower
