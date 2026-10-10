import GaloisForLFunctions.RHTower.GaussianCentralGapCompleteBias
import GaloisForLFunctions.RHTower.XiLogDerivReStripBound

/-!
# The sign abscissa of the Gaussian prime gaps is the zero abscissa

For real `σ > 0` let `G_σ(y) = Σ Λ(n) n^{-σ} e^{-yn²} − ∫₁^∞ u^{-σ} e^{-yu²} du`, and let
`Θ = sup {Re ρ : ξ(ρ) = 0}`.

* **Archimedean sign** (`re_gaussianArchimedeanCurrent_ofReal_le`).  The archimedean current
  `A(σ) = 1/σ + ψ(σ/2)/2 − (log π)/2` satisfies `A(σ) ≤ ½ log((σ+2)/(2π))`, by
  `ψ(σ/2) = ψ(σ/2 + 1) − 2/σ` and `ψ ≤ log`.  It is negative for `0 < σ < 2π − 2`.
* **Gaussian Mertens limit** (`tendsto_gaussianWeightedGap_of_zero_bound`).  If every zero has
  `Re ρ ≤ θ < σ < 2`, then `G_σ(y) → Re (A(σ) − ξ'/ξ(σ))` as `y → 0⁺`.
* **Negativity right of the zeros** (`eventually_gaussianWeightedGap_lt_of_zero_bound`).  Hadamard
  positivity `Re ξ'/ξ(σ) ≥ 0` (every zero lies closer to the critical line than `σ`) puts the limit
  below `½ log((σ+2)/(2π)) < 0`, so `G_σ < ¼ log((σ+2)/(2π))` for all small `y`.
* **Oscillation left of a zero** (`frequently_gaussianWeightedGap_gt_of_lt_re`).  If some zero has
  `Re ρ > σ`, then `G_σ` exceeds every `K` and falls below every `−K` arbitrarily close to `0`.
* **Sign abscissa** (`gaussianSignAbscissa_eq_xiZeroAbscissa`).  The infimum of the `σ ∈ (0, 2)`
  at which `G_σ` is eventually negative equals `Θ`.  RH holds iff this sign abscissa is `½`; at
  the centre itself the sign is also eventually negative under RH (complete archimedean bias).
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-! ## The archimedean current on the real axis -/

/-- **Archimedean sign.**  For `σ > 0`, `Re A(σ) ≤ ½ log((σ+2)/(2π))`. -/
theorem re_gaussianArchimedeanCurrent_ofReal_le {σ : ℝ} (hσ : 0 < σ) :
    (gaussianArchimedeanCurrent (σ : ℂ)).re ≤ Real.log ((σ + 2) / (2 * Real.pi)) / 2 := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  rw [gaussianArchimedeanCurrent, logDeriv_Gammaℝ_of_re_pos hs]
  have hne : ∀ m : ℕ, (σ : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m h
    have h' := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h'
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hrec := Complex.digamma_apply_add_one ((σ : ℂ) / 2) hne
  have hle := re_digamma_le_log (y := σ / 2 + 1) (by positivity)
  have hcast : ((σ / 2 + 1 : ℝ) : ℂ) = (σ : ℂ) / 2 + 1 := by push_cast; ring
  rw [hcast, hrec, Complex.add_re] at hle
  have hinv : (((σ : ℂ) / 2)⁻¹).re = 2 / σ := by
    rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      Complex.ofReal_re]
    field_simp
  rw [hinv] at hle
  have hre : ((σ : ℂ)⁻¹ + (Complex.digamma ((σ : ℂ) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)).re =
      σ⁻¹ + (Complex.digamma ((σ : ℂ) / 2)).re / 2 - Real.log Real.pi / 2 := by
    rw [← Complex.ofReal_inv]
    simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
    ring
  rw [hre]
  have hlog : Real.log ((σ + 2) / (2 * Real.pi)) = Real.log (σ / 2 + 1) - Real.log Real.pi := by
    rw [show (σ + 2) / (2 * Real.pi) = (σ / 2 + 1) / Real.pi by field_simp,
      Real.log_div (by positivity) Real.pi_ne_zero]
  rw [hlog]
  have h2 : σ⁻¹ = (2 / σ) / 2 := by field_simp
  linarith

/-- The archimedean bound is negative on `0 < σ < 2`. -/
theorem log_add_two_div_two_pi_neg {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ < 2) :
    Real.log ((σ + 2) / (2 * Real.pi)) < 0 := by
  have hpi := Real.pi_gt_three
  refine Real.log_neg (by positivity) ?_
  rw [div_lt_one (by positivity)]
  linarith

/-! ## Right of the zeros: the Gaussian Mertens limit and its sign -/

/-- **Gaussian Mertens limit.**  If every zero of `ξ` has `Re ρ ≤ θ < σ < 2` and `σ > 0`, then
`G_σ(y) → Re (A(σ) − ξ'/ξ(σ))` as `y → 0⁺`. -/
theorem tendsto_gaussianWeightedGap_of_zero_bound {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ)
    {σ : ℝ} (hσ0 : 0 < σ) (hσθ : θ < σ) (hσ2 : σ < 2) :
    Tendsto (fun y : ℝ => gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y)
      (𝓝[>] 0) (𝓝 (gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ)).re) := by
  have hs0 : 0 < (σ : ℂ).re := by simpa using hσ0
  have hT := (tendsto_logDeriv_gaussianFormation_of_zeroFree hθ hs0 (by simpa using hσθ)
    (by simpa using hσ2)).comp tendsto_div_pi_nhdsGT_zero
  have hC : Tendsto (fun y : ℝ => gaussianArchimedeanCurrent (σ : ℂ) -
      logDeriv (gaussianEulerContinuumFormation (y / Real.pi)) (σ : ℂ)) (𝓝[>] 0)
      (𝓝 (gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ))) :=
    tendsto_const_nhds.sub hT
  have hR := (Complex.continuous_re.tendsto _).comp hC
  refine hR.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : (0 : ℝ) < y := hy
  have hx : 0 < y / Real.pi := div_pos hy0 Real.pi_pos
  have hpy : Real.pi * (y / Real.pi) = y := mul_div_cancel₀ _ Real.pi_ne_zero
  have hid := logDeriv_gaussianFormation_eq_sub_gap hx hs0
  rw [hpy, gaussianPrimeContinuumGap_ofReal] at hid
  simp only [Function.comp]
  rw [hid, sub_sub_cancel, Complex.ofReal_re]

/-- Every zero of `ξ` has `Re ρ ≥ 1 − θ` when every zero has `Re ρ ≤ θ`. -/
theorem one_sub_re_le_of_zero_bound {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {ρ : ℂ}
    (hρ : xi ρ = 0) : 1 - θ ≤ ρ.re := by
  have h := hθ (1 - ρ) (by rw [xi_one_sub]; exact hρ)
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

/-- The zero bound is at least `½`. -/
theorem half_le_of_zero_bound {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) : 1 / 2 ≤ θ := by
  obtain ⟨ρ, hρ, hre⟩ := exists_xi_zero_re_eq_half
  have := hθ ρ hρ
  linarith

/-- **Hadamard positivity right of the zeros.**  If every zero has `Re ρ ≤ θ < σ`, then
`Re ξ'/ξ(σ) ≥ 0`: every zero is closer to the critical line than `σ`. -/
theorem re_logDeriv_xi_ofReal_nonneg_of_zero_bound {θ : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {σ : ℝ} (hσθ : θ < σ) :
    0 ≤ (logDeriv xi (σ : ℂ)).re := by
  have hhalf := half_le_of_zero_bound hθ
  have hs : 1 / 2 < (σ : ℂ).re := by simp; linarith
  have hxi : xi (σ : ℂ) ≠ 0 := by
    intro h
    have := hθ _ h
    simp at this
    linarith
  refine re_logDeriv_xi_nonneg_of_strip_bound hs hxi (fun q => ?_)
  have hz : xi ((q.1 : ℂ)) = 0 := xi_xiZero q
  have h1 := hθ _ hz
  have h2 := one_sub_re_le_of_zero_bound hθ hz
  have hσre : (σ : ℂ).re = σ := by simp
  rw [hσre]
  nlinarith

/-- **Negativity right of the zeros.**  If every zero has `Re ρ ≤ θ < σ < 2`, then
`G_σ(y) < ¼ log((σ+2)/(2π)) < 0` for all small `y > 0`. -/
theorem eventually_gaussianWeightedGap_lt_of_zero_bound {θ : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {σ : ℝ} (hσθ : θ < σ) (hσ2 : σ < 2) :
    ∀ᶠ y in 𝓝[>] 0, gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y <
      Real.log ((σ + 2) / (2 * Real.pi)) / 4 := by
  have hσ0 : 0 < σ := by linarith [half_le_of_zero_bound hθ]
  have hT := tendsto_gaussianWeightedGap_of_zero_bound hθ hσ0 hσθ hσ2
  have hA := re_gaussianArchimedeanCurrent_ofReal_le hσ0
  have hX := re_logDeriv_xi_ofReal_nonneg_of_zero_bound hθ hσθ
  have hneg := log_add_two_div_two_pi_neg hσ0 hσ2
  have hlim : (gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ)).re <
      Real.log ((σ + 2) / (2 * Real.pi)) / 4 := by
    rw [Complex.sub_re]
    linarith
  exact hT.eventually (gt_mem_nhds hlim)

/-! ## Left of a zero: oscillation -/

/-- Away from `0` every Gaussian gap is bounded: `|G_σ(y)| ≤ (e² + Γ(½)) δ^{-2}` on `[δ, 1]`. -/
theorem abs_gaussianWeightedGap_le_of_ge {σ : ℝ} (hσ : 0 ≤ σ) {δ : ℝ} (hδ : 0 < δ) {y : ℝ}
    (hyδ : δ ≤ y) (hy1 : y ≤ 1) :
    |gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y| ≤
      (Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ) := by
  have hb := norm_gaussianPrimeContinuumGap_le (s := (σ : ℂ)) (by simpa using hσ)
    (hδ.trans_le hyδ) hy1
  rw [gaussianPrimeContinuumGap_ofReal, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ hyδ (by norm_num))
    (by positivity))

/-- An eventual upper bound of `η G_σ` (`η = ±1`) is a bound on all of `(0, 1]`. -/
theorem exists_gaussianWeightedGap_le_of_eventually {σ : ℝ} (hσ : 0 ≤ σ) {η : ℝ}
    (hη : η = 1 ∨ η = -1) {B : ℝ}
    (h : ∀ᶠ y in 𝓝[>] 0,
      η * (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) ≤ B) :
    ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      η * (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) ≤ K := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  have hδ0 : (0 : ℝ) < δ := hδ
  refine ⟨max ((Real.exp 2 + Real.Gamma (1 / 2)) * δ ^ (-2 : ℝ)) B, fun y hy hy1 => ?_⟩
  by_cases hyδ : y < δ
  · have : η * (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) ≤ B :=
      hsub ⟨hy, hyδ⟩
    exact this.trans (le_max_right _ _)
  · push Not at hyδ
    have habs := abs_le.1 (abs_gaussianWeightedGap_le_of_ge hσ hδ0 hyδ hy1)
    refine le_trans ?_ (le_max_left _ _)
    rcases hη with rfl | rfl
    · linarith [habs.2]
    · linarith [habs.1]

/-- **Oscillation left of a zero.**  If some zero has `Re ρ > σ > 0`, then for every `K` the gap
`G_σ` exceeds `K` arbitrarily close to `0`. -/
theorem frequently_gaussianWeightedGap_gt_of_lt_re {σ : ℝ} (hσ : 0 < σ) {ρ : ℂ} (hρ : xi ρ = 0)
    (hρσ : σ < ρ.re) (K : ℝ) :
    ∃ᶠ y in 𝓝[>] 0, K < gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y := by
  by_contra hf
  rw [Filter.not_frequently] at hf
  obtain ⟨B, hB⟩ := exists_gaussianWeightedGap_le_of_eventually hσ.le (Or.inl rfl) (B := K)
    (hf.mono fun y hy => by rw [one_mul]; exact not_lt.1 hy)
  exact xi_ne_zero_of_gaussianPrimeBudget hσ (B := B)
    (fun y hy hy1 => by simpa using hB y hy hy1) hρσ hρ

/-- **Oscillation left of a zero, lower side.**  If some zero has `Re ρ > σ > 0`, then for every
`K` the gap `G_σ` falls below `−K` arbitrarily close to `0`. -/
theorem frequently_gaussianWeightedGap_lt_of_lt_re {σ : ℝ} (hσ : 0 < σ) {ρ : ℂ} (hρ : xi ρ = 0)
    (hρσ : σ < ρ.re) (K : ℝ) :
    ∃ᶠ y in 𝓝[>] 0, gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y < -K := by
  by_contra hf
  rw [Filter.not_frequently] at hf
  obtain ⟨B, hB⟩ := exists_gaussianWeightedGap_le_of_eventually hσ.le (Or.inr rfl) (B := K)
    (hf.mono fun y hy => by have := not_lt.1 hy; linarith)
  exact xi_ne_zero_of_gaussianPrimeBudget_lower hσ (B := B)
    (fun y hy hy1 => by have := hB y hy hy1; linarith) hρσ hρ

/-- **Eventual negativity bounds the zeros.**  If `G_σ < 0` for all small `y` (`σ > 0`), then every
zero of `ξ` has `Re ρ ≤ σ`. -/
theorem xi_zero_re_le_of_eventually_gaussianWeightedGap_neg {σ : ℝ} (hσ : 0 < σ)
    (h : ∀ᶠ y in 𝓝[>] 0, gaussianWeightedPrimeMass σ y < gaussianWeightedContinuumMass σ y)
    {ρ : ℂ} (hρ : xi ρ = 0) : ρ.re ≤ σ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, hy1, hy2⟩ :=
    ((frequently_gaussianWeightedGap_gt_of_lt_re hσ hρ hlt 0).and_eventually h).exists
  linarith

/-! ## The sign abscissa -/

/-- The zero abscissa `Θ = sup {Re ρ : ξ(ρ) = 0}`. -/
def xiZeroAbscissa : ℝ := sSup (Complex.re '' {ρ : ℂ | xi ρ = 0})

/-- The sign abscissa: the infimum of the `σ ∈ (0, 2)` at which the Gaussian gap `G_σ` is
eventually negative. -/
def gaussianSignAbscissa : ℝ :=
  sInf {σ : ℝ | 0 < σ ∧ σ < 2 ∧
    ∀ᶠ y in 𝓝[>] 0, gaussianWeightedPrimeMass σ y < gaussianWeightedContinuumMass σ y}

theorem bddAbove_xiZero_re : BddAbove (Complex.re '' {ρ : ℂ | xi ρ = 0}) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨ρ, hρ, rfl⟩
  by_contra h
  push Not at h
  exact xi_ne_zero_of_one_le_re h.le hρ

theorem nonempty_xiZero_re : (Complex.re '' {ρ : ℂ | xi ρ = 0}).Nonempty := by
  obtain ⟨ρ, hρ, -⟩ := exists_xi_zero_re_eq_half
  exact ⟨ρ.re, ρ, hρ, rfl⟩

theorem re_le_xiZeroAbscissa {ρ : ℂ} (hρ : xi ρ = 0) : ρ.re ≤ xiZeroAbscissa :=
  le_csSup bddAbove_xiZero_re ⟨ρ, hρ, rfl⟩

theorem xiZeroAbscissa_le_one : xiZeroAbscissa ≤ 1 := by
  refine csSup_le nonempty_xiZero_re ?_
  rintro _ ⟨ρ, hρ, rfl⟩
  by_contra h
  push Not at h
  exact xi_ne_zero_of_one_le_re h.le hρ

theorem half_le_xiZeroAbscissa : 1 / 2 ≤ xiZeroAbscissa :=
  half_le_of_zero_bound fun _ hρ => re_le_xiZeroAbscissa hρ

/-- **The sign abscissa is the zero abscissa.**  The Gaussian gap `G_σ` is eventually negative at
every `σ ∈ (Θ, 2)` and at no `σ < Θ`; hence `inf {σ : G_σ < 0 eventually} = Θ`. -/
theorem gaussianSignAbscissa_eq_xiZeroAbscissa : gaussianSignAbscissa = xiZeroAbscissa := by
  set Θ := xiZeroAbscissa with hΘ
  have hΘ1 := xiZeroAbscissa_le_one
  have hΘh := half_le_xiZeroAbscissa
  have hzero : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ Θ := fun _ hρ => re_le_xiZeroAbscissa hρ
  have hmem : ∀ σ : ℝ, Θ < σ → σ < 2 → σ ∈ {σ : ℝ | 0 < σ ∧ σ < 2 ∧
      ∀ᶠ y in 𝓝[>] 0, gaussianWeightedPrimeMass σ y < gaussianWeightedContinuumMass σ y} := by
    intro σ hσΘ hσ2
    refine ⟨by linarith, hσ2, ?_⟩
    have hneg := log_add_two_div_two_pi_neg (σ := σ) (by linarith) hσ2
    filter_upwards [eventually_gaussianWeightedGap_lt_of_zero_bound hzero hσΘ hσ2] with y hy
    linarith
  have hglb : IsGLB {σ : ℝ | 0 < σ ∧ σ < 2 ∧
      ∀ᶠ y in 𝓝[>] 0, gaussianWeightedPrimeMass σ y < gaussianWeightedContinuumMass σ y} Θ := by
    constructor
    · rintro σ ⟨hσ0, -, hσ⟩
      exact csSup_le nonempty_xiZero_re (by
        rintro _ ⟨ρ, hρ, rfl⟩
        exact xi_zero_re_le_of_eventually_gaussianWeightedGap_neg hσ0 hσ hρ)
    · intro b hb
      by_contra hlt
      push Not at hlt
      set σ : ℝ := (Θ + min b 2) / 2 with hσdef
      have hmin : Θ < min b 2 := lt_min hlt (by linarith)
      have hσ := hmem σ (by rw [hσdef]; linarith) (by
        rw [hσdef]; linarith [min_le_right b 2])
      have := hb hσ
      rw [hσdef] at this
      linarith [min_le_left b 2]
  have hne : {σ : ℝ | 0 < σ ∧ σ < 2 ∧
      ∀ᶠ y in 𝓝[>] 0, gaussianWeightedPrimeMass σ y < gaussianWeightedContinuumMass σ y}.Nonempty :=
    ⟨3 / 2, hmem (3 / 2) (by linarith) (by norm_num)⟩
  exact hglb.csInf_eq hne

/-- RH holds iff the zero abscissa is `½`. -/
theorem riemannHypothesis_iff_xiZeroAbscissa_eq_half :
    RiemannHypothesis ↔ xiZeroAbscissa = 1 / 2 := by
  constructor
  · intro hRH
    refine le_antisymm (csSup_le nonempty_xiZero_re ?_) half_le_xiZeroAbscissa
    rintro _ ⟨ρ, hρ, rfl⟩
    by_contra hlt
    push Not at hlt
    exact (rh_iff_xi_ne_zero_right.mp hRH) ρ (mem_rightHalf.mpr hlt) hρ
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hzero
    have h1 := re_le_xiZeroAbscissa hzero
    have h2 := mem_rightHalf.1 hs
    linarith

/-- **RH as a sign abscissa.**  RH holds iff the Gaussian gaps `G_σ` are eventually negative at
every `σ ∈ (½, 2)` and at no `σ < ½`, i.e. iff the sign abscissa is `½`.  At `σ = ½` itself the
sign is then also eventually negative (`riemannHypothesis_iff_eventually_gaussianCentralGap_neg`). -/
theorem riemannHypothesis_iff_gaussianSignAbscissa_eq_half :
    RiemannHypothesis ↔ gaussianSignAbscissa = 1 / 2 := by
  rw [gaussianSignAbscissa_eq_xiZeroAbscissa, riemannHypothesis_iff_xiZeroAbscissa_eq_half]

end

end RHTower
