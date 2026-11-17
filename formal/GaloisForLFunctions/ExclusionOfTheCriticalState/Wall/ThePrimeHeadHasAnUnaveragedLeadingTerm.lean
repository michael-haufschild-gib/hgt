import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheStateHasAContinuousEdgeAtTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeHeadHasAnAveragedLeadingTerm

/-!
# The prime head of the state has an unaveraged leading term

Around an interior point `p ≤ −¼` of the half-line take the window `[p − ¾, p + ¼]` and the interior
cutoff, equal to `1` on `[p − ½, p + ⅛]`. The cut state solves the logarithmic equation on this window
with a bounded forcing, the forward prime wave having finitely many terms there, and the window edge
theorem makes it continuous on `[p − ¼, p + ¼]` (`criticalState_window_edge`). Hence:

* **Interior continuity** (`criticalState_exists_continuous_near`). For `p ≤ −¼` the state agrees almost
  everywhere on `[p − ¼, p + ⅛]` with a continuous function.
* **Right averages** (`criticalState_tendsto_rightAverage`). At every such `p` the right averages
  `h⁻¹ ∫_p^{p+h} F` converge.
* **The prime head** (`criticalState_tendsto_mul_primeHead`). With `ℓ(n)` the right limit of the state at
  `−log n`, `t · ŜF(−t) → Σ_n Λ(n) n^{−½} ℓ(n)` as `t → ∞`: the Abelian theorem of the averaged form
  (`tendsto_mul_primeHead_neg_of_average`), applied to the representative of `F` cut at `±C e^{2u}`,
  whose prime head and right averages are those of `F`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations _root_.RHTower

/-- **Interior continuity.** Around every `p ≤ −¼` the state agrees almost everywhere with a
continuous function on `[p − ¼, p + ⅛]`. -/
theorem criticalState_exists_continuous_near {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {p : ℝ} (hp : p ≤ -(1 / 4)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ᵐ y, y ∈ Icc (p - 1 / 4) (p + 1 / 8) → F y = g y := by
  have hχ : IsWindowCutoff ((p - 1 / 4) - 1 / 2) ((p - 1 / 4) + 1 / 2) 8 (interiorCutoff p) := by
    rw [show p - 1 / 4 - 1 / 2 = p - 3 / 4 by ring, show p - 1 / 4 + 1 / 2 = p + 1 / 4 by ring]
    exact isWindowCutoff_interiorCutoff p
  obtain ⟨Ψ, hΨc, hrep, -⟩ :=
    criticalState_window_edge hW ht hF (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) hχ
  refine ⟨fun y => Ψ (p + 1 / 4 - y), hΨc.comp (continuous_const.sub continuous_id), ?_⟩
  filter_upwards [hrep] with y hy hm
  have h := hy hm.1
  rw [interiorCutoff_eq_one (by linarith [hm.1]) hm.2, one_mul,
    show p - 1 / 4 + 1 / 2 - y = p + 1 / 4 - y by ring] at h
  exact h

/-- Right averages of a function that is almost everywhere continuous to the right of `p`. -/
theorem tendsto_rightAverage_of_ae_eq {F g : ℝ → ℝ} (hg : Continuous g) {p δ : ℝ} (hδ : 0 < δ)
    (hFg : ∀ᵐ y, y ∈ Ioc p (p + δ) → F y = g y) :
    Tendsto (fun h => (∫ u in p..(p + h), F u) / h) (𝓝[>] 0) (𝓝 (g p)) := by
  have hd := ((hg.integral_hasStrictDerivAt p p).hasDerivAt).tendsto_slope_zero_right
  simp only [intervalIntegral.integral_same, sub_zero] at hd
  refine hd.congr' ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with h hh hhδ
  have hh0 : (0 : ℝ) < h := hh
  have hhδ' : h < δ := hhδ
  rw [smul_eq_mul, inv_mul_eq_div]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hFg] with y hy hyI
  rw [uIoc_of_le (by linarith)] at hyI
  exact (hy ⟨hyI.1, by linarith [hyI.2]⟩).symm

/-- **Right averages of the state.** At every `p ≤ −¼` the right averages of the state converge. -/
theorem criticalState_tendsto_rightAverage {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {p : ℝ} (hp : p ≤ -(1 / 4)) :
    ∃ L : ℝ, Tendsto (fun h => (∫ u in p..(p + h), F u) / h) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨g, hg, hFg⟩ := criticalState_exists_continuous_near hW ht hF hp
  refine ⟨g p, tendsto_rightAverage_of_ae_eq hg (δ := 1 / 8) (by norm_num) ?_⟩
  filter_upwards [hFg] with y hy hm
  exact hy ⟨by linarith [hm.1], hm.2⟩

/-- The prime head sees the profile only through integrals: it is unchanged by a change of `F` on a
null set. -/
theorem primeHead_congr_ae {F G : ℝ → ℝ} (h : F =ᵐ[volume] G) (q : ℂ) :
    primeHead F q = primeHead G q := by
  unfold primeHead levyHead
  congr 1
  funext n
  congr 2
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [h] with u hu
  rw [hu]

/-- **The prime head of the state has an unaveraged leading term.** The state has right limits
`ℓ(n)` (as right averages) at every prime power point `−log n`, and
`t · ŜF(−t) → Σ_n Λ(n) n^{−½} ℓ(n)` as `t → ∞`. -/
theorem criticalState_tendsto_mul_primeHead {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ ℓ : ℕ → ℝ, (∀ n : ℕ, 2 ≤ n → Tendsto
        (fun h => (∫ u in (-Real.log n)..(-Real.log n + h), F u) / h) (𝓝[>] 0) (𝓝 (ℓ n))) ∧
      Tendsto (fun t : ℝ => (t : ℂ) * primeHead F (-(t : ℂ))) atTop
        (𝓝 (∑' n : ℕ, ((vonMangoldtAtom n * ℓ n : ℝ) : ℂ))) := by
  have hex : ∀ n : ℕ, 2 ≤ n → ∃ L : ℝ, Tendsto
      (fun h => (∫ u in (-Real.log n)..(-Real.log n + h), F u) / h) (𝓝[>] 0) (𝓝 L) := by
    intro n hn
    have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h2 := Real.log_two_gt_d9
    exact criticalState_tendsto_rightAverage hW ht hF (by norm_num at h2; linarith)
  choose! ℓ hℓ using hex
  refine ⟨ℓ, hℓ, ?_⟩
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC0, hbexp, -⟩ := criticalState_ae_abs_le hW ht hF
  -- the representative cut at ±C e^{2u}
  set Ft : ℝ → ℝ := fun u => max (-(C * Real.exp (2 * u))) (min (C * Real.exp (2 * u)) (F u))
    with hFtdef
  have hFtm : Measurable Ft := by
    rw [hFtdef]
    exact (by fun_prop : Measurable fun u : ℝ => -(C * Real.exp (2 * u))).max
      ((by fun_prop : Measurable fun u : ℝ => C * Real.exp (2 * u)).min hdF.meas)
  have hbd : ∀ u, |Ft u| ≤ C * Real.exp (2 * u) := fun u => by
    have he : 0 ≤ C * Real.exp (2 * u) := mul_nonneg hC0 (Real.exp_pos _).le
    rw [hFtdef, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hae : Ft =ᵐ[volume] F := by
    filter_upwards [hbexp] with u hu
    rw [hFtdef]
    simp only
    rw [min_eq_right (abs_le.mp hu).2, max_eq_right (abs_le.mp hu).1]
  have hav : ∀ n : ℕ, vonMangoldtAtom n ≠ 0 → Tendsto
      (fun h => (∫ u in (-Real.log n)..(-Real.log n + h), Ft u) / h) (𝓝[>] 0) (𝓝 (ℓ n)) := by
    intro n hn
    have hn2 : 2 ≤ n := by
      by_contra h
      exact hn (vonMangoldtAtom_eq_zero_of_lt_two (by omega))
    refine (hℓ n hn2).congr fun h => ?_
    congr 1
    exact intervalIntegral.integral_congr_ae (hae.mono fun u hu _ => hu.symm)
  have hmain := tendsto_mul_primeHead_neg_of_average hFtm (c := 2) (by norm_num) hbd hav
  refine hmain.congr fun t => ?_
  rw [primeHead_congr_ae hae]

#print axioms criticalState_tendsto_mul_primeHead

end GaloisForLFunctions.ExclusionOfTheCriticalState
