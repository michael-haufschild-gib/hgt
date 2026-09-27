import GaloisForLFunctions.RHTower.STCPrimeHeightFiberAbel
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationCriticalBoundary
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Prime-square sign wall for the continued Euler Gram

The prime-log current `Q(s) = Σ_p (log p) p^{-s}` continues across `Re s = 1` and, through the
valuation split `Q(s) = A(s) - A(2s) + H(2s) - H_{≥3}(s)` (`A = -ζ'/ζ`), across the prime-square
wall down to `Re s > 1/3`.  Its Laurent data are

* `Q(s) = 1/(s-1) + holomorphic` near `s = 1`;
* `Q(s) = -1/(2s-1) + holomorphic` near `s = 1/2` (only the valuation-two row reaches this wall).

Hence the continued log-square series `F = -Q'` (equal to `Σ_p (log p)² p^{-s}` on `Re s > 1`)
satisfies `F(s) = -2/(2s-1)² + holomorphic` near `s = 1/2`.  On the real axis `F(σ) < 0` for
`σ ↓ 1/2`, so the continued Gram kernel `K(w,z) = F(w + z̄ - 1)` is neither positive semidefinite
nor a Gram kernel of Hilbert vectors on `Re w > 3/4`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The prime-log current continued across the prime-square wall. -/
def primeLogCriticalContinuation (s : ℂ) : ℂ :=
  infinitePrimeFlux s - xiPrimeLogHigherValuationCriticalContinuation s

theorem primeLogCriticalContinuation_eq {s : ℂ} (hs : 1 / 2 < s.re) :
    primeLogCriticalContinuation s = xiPrimeLogDirichletContinuation s := by
  rw [primeLogCriticalContinuation, xiPrimeLogHigherValuationCriticalContinuation_eq hs]
  rfl

/-- The continued prime log-square series `F = -Q'`. -/
def primeLogSquareContinuation (s : ℂ) : ℂ :=
  -deriv primeLogCriticalContinuation s

/-- On the Euler half-plane the continuation is the literal log-square prime series. -/
theorem primeLogSquareContinuation_eq {s : ℂ} (hs : 1 < s.re) :
    primeLogSquareContinuation s = primeLogSquareComplex s := by
  rw [primeLogSquareComplex_eq_neg_deriv_continuation hs, primeLogSquareContinuation]
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : primeLogCriticalContinuation =ᶠ[𝓝 s] xiPrimeLogDirichletContinuation := by
    filter_upwards [hopen.mem_nhds (show 1 / 2 < s.re by linarith)] with z hz
    exact primeLogCriticalContinuation_eq hz
  rw [heq.deriv_eq]

private theorem infinitePrimeFlux_eq_fun :
    infinitePrimeFlux = fun s => -(deriv riemannZeta s / riemannZeta s) := by
  funext s
  simp [infinitePrimeFlux, logDeriv_apply]

private theorem analyticAt_logDeriv_zetaResidueUnit_one :
    AnalyticAt ℂ (logDeriv zetaResidueUnit) 1 := by
  have h1 : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have : logDeriv zetaResidueUnit = fun s => deriv zetaResidueUnit s / zetaResidueUnit s := by
    funext s; rw [logDeriv_apply]
  rw [this]
  exact zetaResidueUnit_analyticAt.deriv.div zetaResidueUnit_analyticAt h1

/-- Pole of the prime flux at `1`: `A(s) = 1/(s-1) - (log G)'(s)` off the pole. -/
private theorem infinitePrimeFlux_eventually_eq :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ), infinitePrimeFlux s = (s - 1)⁻¹ - logDeriv zetaResidueUnit s := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds zetaResidueUnit_ne_zero_eventually]
    with s hs hG
  rw [infinitePrimeFlux, logDeriv_zeta_eq hs hG]
  ring

private theorem analyticAt_xiPrimeLogHigherValuation {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ xiPrimeLogHigherValuation s := by
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact (differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd hopen) s hs

private theorem analyticAt_threePlus {s : ℂ} (hs : 1 / 3 < s.re) :
    AnalyticAt ℂ xiPrimeLogHigherValuationThreePlus s := by
  have hopen : IsOpen {z : ℂ | 1 / 3 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ xiPrimeLogHigherValuationThreePlus {z : ℂ | 1 / 3 < z.re} :=
    fun z hz => (differentiableAt_xiPrimeLogHigherValuationThreePlus hz).differentiableWithinAt
  exact (hdiff.analyticOnNhd hopen) s hs

/-- **Pole at `s = 1`.** `Q(s) = 1/(s-1) + G(s)` with `G` holomorphic at `1`. -/
theorem primeLogCriticalContinuation_laurent_one :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 1 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ), primeLogCriticalContinuation s = (s - 1)⁻¹ + G s := by
  refine ⟨fun s => -logDeriv zetaResidueUnit s - xiPrimeLogHigherValuation s,
    analyticAt_logDeriv_zetaResidueUnit_one.neg.sub
      (analyticAt_xiPrimeLogHigherValuation (by norm_num)), ?_⟩
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [infinitePrimeFlux_eventually_eq,
    nhdsWithin_le_nhds (hopen.mem_nhds (show (1 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re} by norm_num))]
    with s hflux hre
  rw [primeLogCriticalContinuation_eq hre, xiPrimeLogDirichletContinuation, hflux]
  ring

/-- The regular part of `Q` at the prime-square wall. -/
private def primeSquareRegularPart (s : ℂ) : ℂ :=
  infinitePrimeFlux s + logDeriv zetaResidueUnit (2 * s) + xiPrimeLogHigherValuation (2 * s) -
    xiPrimeLogHigherValuationThreePlus s

private theorem analyticAt_primeSquareRegularPart :
    AnalyticAt ℂ primeSquareRegularPart (1 / 2) := by
  have hζ : riemannZeta (1 / 2 : ℂ) ≠ 0 := by
    have := riemannZeta_ne_zero_of_ofReal_mem_Ioo (σ := 1 / 2) (by norm_num) (by norm_num)
    simpa using this
  have hζan : AnalyticAt ℂ riemannZeta (1 / 2 : ℂ) := by
    have hdon : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
      fun z hz => (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
    exact (hdon.analyticOnNhd isOpen_compl_singleton) _ (by norm_num)
  have hA : AnalyticAt ℂ infinitePrimeFlux (1 / 2 : ℂ) := by
    rw [infinitePrimeFlux_eq_fun]
    exact (hζan.deriv.div hζan hζ).neg
  have htwo : AnalyticAt ℂ (fun s : ℂ => 2 * s) (1 / 2 : ℂ) := by fun_prop
  have hlogG : AnalyticAt ℂ (fun s : ℂ => logDeriv zetaResidueUnit (2 * s)) (1 / 2 : ℂ) := by
    have h := analyticAt_logDeriv_zetaResidueUnit_one
    have e : (2 : ℂ) * (1 / 2) = 1 := by norm_num
    rw [← e] at h
    exact h.comp htwo
  have hH : AnalyticAt ℂ (fun s : ℂ => xiPrimeLogHigherValuation (2 * s)) (1 / 2 : ℂ) := by
    have h := analyticAt_xiPrimeLogHigherValuation (s := 2 * (1 / 2 : ℂ)) (by norm_num)
    exact h.comp htwo
  have h3 := analyticAt_threePlus (s := (1 / 2 : ℂ)) (by norm_num)
  exact ((hA.add hlogG).add hH).sub h3

/-- **Pole at the prime-square wall.** `Q(s) = -1/(2s-1) + K(s)` with `K` holomorphic at `1/2`. -/
theorem primeLogCriticalContinuation_laurent_half :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K (1 / 2) ∧
      ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), primeLogCriticalContinuation s = -(2 * s - 1)⁻¹ + K s := by
  refine ⟨primeSquareRegularPart, analyticAt_primeSquareRegularPart, ?_⟩
  have htwo : Tendsto (fun s : ℂ => 2 * s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : ContinuousAt (fun s : ℂ => 2 * s) (1 / 2 : ℂ) := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h
      apply hs
      simp only [Set.mem_singleton_iff] at h ⊢
      linear_combination h / 2
  filter_upwards [htwo.eventually infinitePrimeFlux_eventually_eq] with s hs
  unfold primeLogCriticalContinuation xiPrimeLogHigherValuationCriticalContinuation
    primeSquareRegularPart
  rw [hs]
  ring

/-- **Laurent law of the continued log-square series.** `F(s) = -2/(2s-1)² + G(s)` near `1/2`,
with `G` holomorphic at `1/2`. -/
theorem primeLogSquareContinuation_laurent_half :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (1 / 2) ∧
      ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), primeLogSquareContinuation s = -2 / (2 * s - 1) ^ 2 + G s := by
  obtain ⟨K, hK, hQ⟩ := primeLogCriticalContinuation_laurent_half
  refine ⟨fun s => -deriv K s, hK.deriv.neg, ?_⟩
  have hQ' : ∀ᶠ s in 𝓝 (1 / 2 : ℂ), s ≠ 1 / 2 →
      primeLogCriticalContinuation s = -(2 * s - 1)⁻¹ + K s := eventually_nhdsWithin_iff.mp hQ
  have hKd : ∀ᶠ s in 𝓝 (1 / 2 : ℂ), DifferentiableAt ℂ K s :=
    hK.eventually_analyticAt.mono fun s hs => hs.differentiableAt
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hQ'.eventually_nhds,
    nhdsWithin_le_nhds hKd] with s hs hnear hdK
  have hs' : s ≠ 1 / 2 := hs
  have hs2 : 2 * s - 1 ≠ 0 := by
    intro h
    apply hs'
    linear_combination h / 2
  have hloc : primeLogCriticalContinuation =ᶠ[𝓝 s] fun z => -(2 * z - 1)⁻¹ + K z := by
    filter_upwards [hnear, isOpen_ne.mem_nhds hs'] with z hz hz'
    exact hz hz'
  have hinv : HasDerivAt (fun z : ℂ => -(2 * z - 1)⁻¹) (2 / (2 * s - 1) ^ 2) s := by
    have h1 : HasDerivAt (fun z : ℂ => 2 * z - 1) 2 s := by
      simpa using ((hasDerivAt_id s).const_mul 2).sub_const 1
    have h2 : HasDerivAt (fun z : ℂ => -(2 * z - 1)⁻¹) (-(-2 / (2 * s - 1) ^ 2)) s :=
      (h1.inv hs2).neg
    rwa [show -(-2 / (2 * s - 1) ^ 2) = 2 / (2 * s - 1) ^ 2 by ring] at h2
  have hsum : HasDerivAt (fun z => -(2 * z - 1)⁻¹ + K z) (2 / (2 * s - 1) ^ 2 + deriv K s) s :=
    hinv.add hdK.hasDerivAt
  rw [primeLogSquareContinuation, hloc.deriv_eq, hsum.deriv]
  ring

/-- `(2σ-1)² F(σ) → -2` as real `σ ↓ 1/2`. -/
theorem tendsto_primeLogSquareContinuation_real :
    Tendsto (fun σ : ℝ => ((2 * σ - 1) ^ 2 : ℂ) * primeLogSquareContinuation σ)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 (-2)) := by
  obtain ⟨G, hG, hF⟩ := primeLogSquareContinuation_laurent_half
  have hcoe : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : ContinuousAt (fun σ : ℝ => (σ : ℂ)) (1 / 2) := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro h
      simp only [Set.mem_singleton_iff] at h
      have h' : (σ : ℂ) = ((1 / 2 : ℝ) : ℂ) := by rw [h]; push_cast; ring
      exact (ne_of_gt (show (1 / 2 : ℝ) < σ from hσ)) (Complex.ofReal_injective h')
  have hGt : Tendsto (fun σ : ℝ => G σ) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (G (1 / 2))) :=
    hG.continuousAt.tendsto.comp (hcoe.mono_right nhdsWithin_le_nhds)
  have hsq : Tendsto (fun σ : ℝ => ((2 * σ - 1) ^ 2 : ℂ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun σ : ℝ => ((2 * (σ : ℂ) - 1) ^ 2 : ℂ)) (1 / 2) := by fun_prop
    have h2 := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 / 2 : ℝ)))
    convert h2 using 2
    push_cast
    ring
  have hlim := tendsto_const_nhds (x := (-2 : ℂ)) |>.add (hsq.mul hGt)
  rw [zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hcoe.eventually hF, self_mem_nhdsWithin] with σ hσ hσpos
  have hne : (2 * (σ : ℂ) - 1) ≠ 0 := by
    have : (2 * σ - 1 : ℝ) ≠ 0 := by
      have : (1 / 2 : ℝ) < σ := hσpos
      linarith
    exact_mod_cast this
  rw [hσ]
  field_simp

/-- **Negative diagonal.** `Re F(σ) < 0` for all real `σ` sufficiently close to `1/2` from above. -/
theorem eventually_re_primeLogSquareContinuation_neg :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), (primeLogSquareContinuation (σ : ℂ)).re < 0 := by
  have hre : Tendsto (fun σ : ℝ => Complex.re (((2 * σ - 1) ^ 2 : ℂ) *
      primeLogSquareContinuation σ)) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (Complex.re (-2))) :=
    (Complex.continuous_re.tendsto (-2 : ℂ)).comp tendsto_primeLogSquareContinuation_real
  filter_upwards [hre.eventually (eventually_lt_nhds (show Complex.re (-2) < 0 by norm_num)),
    self_mem_nhdsWithin] with σ hσ hσpos
  have hpos : 0 < (2 * σ - 1) ^ 2 := by
    have : (1 / 2 : ℝ) < σ := hσpos
    nlinarith
  have hcast : ((2 * (σ : ℂ) - 1) ^ 2 : ℂ) = (((2 * σ - 1) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.re_ofReal_mul] at hσ
  by_contra h
  push Not at h
  have := mul_nonneg hpos.le h
  linarith

/-- The analytically continued Euler Gram kernel `K(w,z) = F(w + z̄ - 1)`. -/
def primeSquareGramKernel (w z : ℂ) : ℂ :=
  primeLogSquareContinuation (w + (starRingEnd ℂ) z - 1)

/-- There are points `w` with `Re w > 3/4` whose diagonal kernel value has negative real part. -/
theorem exists_primeSquareGramKernel_diag_neg :
    ∃ w : ℂ, 3 / 4 < w.re ∧ (primeSquareGramKernel w w).re < 0 := by
  have hmem : ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), (1 / 2 : ℝ) < σ := self_mem_nhdsWithin
  obtain ⟨σ, hσ, hσpos⟩ := (eventually_re_primeLogSquareContinuation_neg.and hmem).exists
  have hσ' : (1 / 2 : ℝ) < σ := hσpos
  refine ⟨((σ + 1) / 2 : ℝ), by simp; linarith, ?_⟩
  unfold primeSquareGramKernel
  have : ((((σ + 1) / 2 : ℝ) : ℂ) + (starRingEnd ℂ) (((σ + 1) / 2 : ℝ) : ℂ) - 1) = (σ : ℂ) := by
    rw [Complex.conj_ofReal]
    push_cast
    ring
  rw [this]
  exact hσ

/-- **No positivity-preserving continuation.** The continued kernel is not positive semidefinite
on the half-plane `Re w > 3/4`. -/
theorem not_posSemidef_primeSquareGramKernel :
    ¬ ∀ (n : ℕ) (z c : Fin n → ℂ), (∀ i, 3 / 4 < (z i).re) →
      0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * primeSquareGramKernel (z i) (z j)).re := by
  intro h
  obtain ⟨w, hw, hneg⟩ := exists_primeSquareGramKernel_diag_neg
  have := h 1 (fun _ => w) (fun _ => 1) (fun _ => hw)
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, map_one,
    one_mul] at this
  linarith

/-- **Not a Gram kernel of Hilbert vectors.** No vectors `v_w` in a complex inner product space
satisfy `K(w,z) = ⟪v_z, v_w⟫` for all `Re w, Re z > 3/4`. -/
theorem not_gram_primeSquareGramKernel :
    ¬ ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (v : ℂ → E),
      ∀ w z : ℂ, 3 / 4 < w.re → 3 / 4 < z.re →
        primeSquareGramKernel w z = @inner ℂ E _ (v z) (v w) := by
  rintro ⟨E, _, _, v, hv⟩
  obtain ⟨w, hw, hneg⟩ := exists_primeSquareGramKernel_diag_neg
  rw [hv w w hw hw] at hneg
  have h0 : 0 ≤ RCLike.re (@inner ℂ E _ (v w) (v w)) := inner_self_nonneg
  rw [RCLike.re_to_complex] at h0
  linarith

end

end RHTower
