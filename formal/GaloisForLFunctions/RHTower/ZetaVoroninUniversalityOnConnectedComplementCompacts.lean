import GaloisForLFunctions.RHTower.ZetaVoroninUniversalityOnCompactSets
import GaloisForLFunctions.HTGeometry.PolynomialRungeOnConnectedComplement

/-!
# Voronin universality of `ζ` on compact sets with connected complement

Let `K` be a compact subset of the open strip `1/2 < Re s < 1` with `ℂ \ K` connected, and let
`g` be analytic and nonvanishing on a simply connected open set `U ⊇ K` (equivalently
`g = exp ∘ F` with `F` analytic on an open set containing `K`).  Then for every `ε > 0` the shifts
`τ` with `sup_K |ζ(s + iτ) − g(s)| < ε` have positive lower density
(`exists_pos_density_zetaTargetReturnSet_of_isCompact_of_isPreconnected_compl`,
`exists_pos_density_zetaTargetReturnSet_exp_of_isCompact_of_isPreconnected_compl`).

The polynomial Runge theorem approximates `F` on `K` by a polynomial `P`; `exp ∘ P` is entire and
nonvanishing, so the compact-set universality theorem for entire targets applies, and
`‖exp F − exp P‖ ≤ 2 e^{sup_K ‖F‖} sup_K ‖F − P‖` on `K` transfers the return heights.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Universality for exponential targets on compact sets with connected complement.**  For `K`
compact in the strip with `ℂ \ K` connected and `F` analytic on an open set containing `K`, the
shifts with `sup_K |ζ(s + iτ) − exp(F(s))| < ε` have positive lower density. -/
theorem exists_pos_density_zetaTargetReturnSet_exp_of_isCompact_of_isPreconnected_compl
    {K : Set ℂ} (hK : IsCompact K) (hstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1)
    (hconn : IsPreconnected Kᶜ) {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet (fun s => Complex.exp (F s)) K ε ∩ Icc 0 T) := by
  -- a bound for `F` on `K` and the polynomial approximation
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF.continuousOn.mono hKU)
  set η : ℝ := min 1 (ε / (4 * Real.exp M)) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / (4 * Real.exp M) := min_le_right _ _
  obtain ⟨P, hP⟩ := exists_polynomial_approx_of_analyticOnNhd hU hF hK hKU hconn hηpos
  -- universality for the entire nonvanishing target `exp ∘ P`
  set g : ℂ → ℂ := fun z => Complex.exp (P.eval z) with hg
  have hgd : Differentiable ℂ g := Complex.differentiable_exp.comp (Polynomial.differentiable P)
  have hg0 : ∀ z, g z ≠ 0 := fun z => Complex.exp_ne_zero _
  obtain ⟨c, hc, hT⟩ := exists_pos_density_zetaTargetReturnSet_of_differentiable_of_isCompact hK
    hstrip hgd hg0 (half_pos hε)
  refine ⟨c, hc, hT.mono fun T hT => hT.trans (measure_mono (inter_subset_inter_left _ ?_))⟩
  -- the return heights of `exp ∘ P` within `ε/2` are return heights of `exp ∘ F` within `ε`
  intro τ hτ s hs
  have h1 := hτ s hs
  have hFs := hM s hs
  have hPs := hP s hs
  have h2 : ‖Complex.exp (P.eval s) - Complex.exp (F s)‖ ≤ ε / 2 := by
    calc ‖Complex.exp (P.eval s) - Complex.exp (F s)‖
        ≤ 2 * Real.exp ‖F s‖ * ‖P.eval s - F s‖ := by
          refine norm_cexp_sub_cexp_le_of_norm_sub_le_one ?_
          rw [norm_sub_rev]
          exact hPs.trans hη1
      _ ≤ 2 * Real.exp M * η :=
          mul_le_mul (by gcongr) (by rw [norm_sub_rev]; exact hPs) (norm_nonneg _)
            (by positivity)
      _ ≤ 2 * Real.exp M * (ε / (4 * Real.exp M)) := by gcongr
      _ = ε / 2 := by
          field_simp
          ring
  calc ‖riemannZeta (s + τ * I) - Complex.exp (F s)‖
      = ‖(riemannZeta (s + τ * I) - g s) + (Complex.exp (P.eval s) - Complex.exp (F s))‖ := by
        congr 1
        rw [hg]
        ring
    _ ≤ ‖riemannZeta (s + τ * I) - g s‖ + ‖Complex.exp (P.eval s) - Complex.exp (F s)‖ :=
        norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 h2
    _ = ε := add_halves ε

/-- **Voronin universality on compact sets with connected complement.**  For `K` compact in the
strip with `ℂ \ K` connected, and `g` analytic and nonvanishing on a simply connected open set
`U ⊇ K`, the shifts with `sup_K |ζ(s + iτ) − g(s)| < ε` have positive lower density. -/
theorem exists_pos_density_zetaTargetReturnSet_of_isCompact_of_isPreconnected_compl
    {K : Set ℂ} (hK : IsCompact K) (hstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1)
    (hconn : IsPreconnected Kᶜ) {U : Set ℂ} (hU : IsOpen U) (hUsc : IsSimplyConnected U)
    (hKU : K ⊆ U) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ s ∈ U, g s ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume (zetaTargetReturnSet g K ε ∩ Icc 0 T) := by
  -- the analytic logarithm of `g` on `U`
  have hU0 : (0 : ℂ) ∉ g '' U := by
    rintro ⟨z, hz, hgz⟩
    exact hg0 z hz hgz
  obtain ⟨F, hFc, hFeq⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUsc hU hg.continuousOn hU0
  have hF : AnalyticOnNhd ℂ F U :=
    U0KummerBranch.analyticOnNhd_of_continuousOn_exp_eq hU hFc hg (fun z hz => hFeq hz)
  obtain ⟨c, hc, hT⟩ := exists_pos_density_zetaTargetReturnSet_exp_of_isCompact_of_isPreconnected_compl
    hK hstrip hconn hU hKU hF hε
  refine ⟨c, hc, hT.mono fun T hT => hT.trans (le_of_eq ?_)⟩
  congr 2
  ext τ
  simp only [zetaTargetReturnSet, Set.mem_setOf_eq]
  constructor
  · intro h s hs
    have hgs : Complex.exp (F s) = g s := hFeq (hKU hs)
    have := h s hs
    rwa [hgs] at this
  · intro h s hs
    have hgs : Complex.exp (F s) = g s := hFeq (hKU hs)
    rw [hgs]
    exact h s hs

end RHTower
