import GaloisForLFunctions.GrowingWindowsOfSpecZ.ForbiddingLatticeZeroModesIsRH

/-!
# Lattice Schur data coalesce under refinement

What survives the continuum limit `h → 0` of the lattice canonical system of a fixed bump `φ`?
Nothing at fixed scale:

* **The first reflection coefficient tends to `1`** (`tendsto_reflCoeff_zero`): `γ_0(φ, h) = c(h)/c(0)`
  and the orbit correlation is continuous, so `γ_0(φ, h) → 1` as `h → 0`, for every bump with
  `Q(φ) ≠ 0`.
* **Every fixed-index margin vanishes** (`tendsto_levinsonErr_one`, `tendsto_levinsonErr_of_rh`):
  `E_1(φ, h) → 0`, and under RH `E_n(φ, h) → 0` as `h → 0` for every `n ≥ 1`.
* **The continuum corner margin is degenerate** (`contMargin_nonpos`, `contMargin_eq_zero`): a single
  translate `φ(· − s)` with `s → 0⁻` has `Q(φ − φ(· − s)) = 2(c(0) − c(s)) → 0`, so the infimum of
  Weil's form over corner combinations is `≤ 0` for every window length `T > 0`, unconditionally,
  and `= 0` under RH. Hence the margins at fixed total length also tend to `0`
  (`tendsto_levinsonErr_dyadic_zero`).

Translates of a fixed bump coalesce: the unnormalized canonical system has a trivial continuum limit.
The surviving continuum invariants are the margins rescaled by the step: the first margin is born at
order `h²` with coefficient the zero energy of `φ'` (`tendsto_levinsonErr_one_div_sq`).
-/

noncomputable section

open Filter Topology Set

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis

variable {φ : ℝ → ℝ}

/-- The first reflection coefficient is the normalized orbit correlation: `γ_0 = c(h)/c(0)`. -/
theorem reflCoeff_zero_eq (φ : ℝ → ℝ) (h : ℝ) :
    reflCoeff (weilSeq φ h) 0 = weilOrbitCorr φ h / weilQuad φ := by
  have h0 : weilSeq φ h 0 = weilQuad φ := by rw [weilSeq, latticeTranslate_zero]; rfl
  have hs : schurParam (weilSeq φ h) 0 = weilOrbitCorr φ h := by
    simp only [schurParam, schurCoupling, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      Nat.cast_zero, zero_add]
    exact weilSeq_one φ h
  rw [reflCoeff, hs, levinsonErr_zero, h0]

/-- `c(0) = Q(φ)`. -/
theorem weilOrbitCorr_zero (φ : ℝ → ℝ) : weilOrbitCorr φ 0 = weilQuad φ := by
  show weilPair (scaleShift 0 φ) φ = weilQuad φ
  rw [scaleShift_zero]; rfl

/-- **The first reflection coefficient tends to `1` under refinement.** -/
theorem tendsto_reflCoeff_zero (hφ : φ ∈ realTests) (hQ : weilQuad φ ≠ 0) :
    Tendsto (fun h => reflCoeff (weilSeq φ h) 0) (𝓝 0) (𝓝 1) := by
  have hc := (continuous_weilOrbitCorr hφ).tendsto 0
  rw [weilOrbitCorr_zero] at hc
  have := hc.div_const (weilQuad φ)
  rw [div_self hQ] at this
  simpa only [reflCoeff_zero_eq] using this

/-- **The two-site margin vanishes under refinement**: `E_1(φ, h) → 0` as `h → 0`. -/
theorem tendsto_levinsonErr_one (hφ : φ ∈ realTests) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) 1) (𝓝 0) (𝓝 0) := by
  have hc := (continuous_weilOrbitCorr hφ).tendsto 0
  rw [weilOrbitCorr_zero] at hc
  have := (tendsto_const_nhds (x := weilQuad φ)).sub ((hc.pow 2).div_const (weilQuad φ))
  rw [show weilQuad φ - weilQuad φ ^ 2 / weilQuad φ = 0 by
    rcases eq_or_ne (weilQuad φ) 0 with h | h
    · rw [h]; ring
    · field_simp; ring] at this
  simpa only [levinsonErr_one] using this

/-- **Under RH every fixed-index margin vanishes under refinement**: `E_n(φ, h) → 0` as `h → 0⁺` for
every `n ≥ 1`. -/
theorem tendsto_levinsonErr_of_rh (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) n) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ h : ℝ, 0 < h → ∀ m, 0 < levinsonErr (weilSeq φ h) m := fun h hh m =>
    riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh m
  have h1 := (tendsto_levinsonErr_one hφ).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hpos h hh n).le
  · filter_upwards [self_mem_nhdsWithin] with h hh
    -- the margins decrease in the number of sites
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => simp
    | succ k ih =>
      exact (levinsonErr_succ_le (hpos h hh _)).trans (ih (by omega))

/-! ### The continuum corner margin is degenerate -/

/-- `Q(φ − φ(· − s)) = 2(c(0) − c(s))`. -/
theorem weilQuad_cornerCombo_single (hφ : φ ∈ realTests) (s : ℝ) :
    weilQuad (cornerCombo φ ![-1] ![s]) = 2 * weilQuad φ - 2 * weilOrbitCorr φ s := by
  rw [cornerCombo_eq_sum, weilQuad_sum_scaleShift hφ]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ,
    Matrix.cons_val_zero, sub_self, zero_sub, sub_zero, weilOrbitCorr_neg, weilOrbitCorr_zero,
    add_zero]
  ring

/-- **The continuum corner margin is nonpositive**, unconditionally, for every length `T > 0`. -/
theorem contMargin_nonpos (hφ : φ ∈ realTests) {T : ℝ} (hT : 0 < T) : contMargin φ T ≤ 0 := by
  by_cases hb : BddBelow (cornerValues φ T)
  · have hc := (continuous_weilOrbitCorr hφ).tendsto 0
    rw [weilOrbitCorr_zero] at hc
    have hlim : Tendsto (fun s => 2 * weilQuad φ - 2 * weilOrbitCorr φ s) (𝓝[<] 0) (𝓝 0) := by
      have := (tendsto_const_nhds (x := 2 * weilQuad φ)).sub (hc.const_mul 2)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨s, hs, hsT⟩ :=
      ((hlim.eventually (gt_mem_nhds hε)).and (Ioo_mem_nhdsLT (show -T < 0 by linarith))).exists
    have hmem : weilQuad (cornerCombo φ ![-1] ![s]) ∈ cornerValues φ T :=
      ⟨1, ![-1], ![s], fun i => by
        rw [Subsingleton.elim i 0, Matrix.cons_val_zero]; exact ⟨hsT.1.le, hsT.2⟩, rfl⟩
    have := csInf_le hb hmem
    rw [weilQuad_cornerCombo_single hφ] at this
    exact (this.trans hs.le).trans (by linarith)
  · exact (Real.sInf_of_not_bddBelow hb).le

/-- **Under RH the continuum corner margin vanishes** for every length `T > 0`. -/
theorem contMargin_eq_zero (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) {T : ℝ} (hT : 0 < T) :
    contMargin φ T = 0 := by
  refine le_antisymm (contMargin_nonpos hφ hT) (le_csInf ⟨_, 0, Fin.elim0, Fin.elim0,
    fun i => i.elim0, rfl⟩ ?_)
  rintro v ⟨m, a, s, -, rfl⟩
  have hmem : cornerCombo φ a s ∈ realTests := by
    rw [cornerCombo_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (scaleShift_mem _ hφ)
  exact (ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg.mp hRH)
    _ hmem.1 hmem.2

/-- **The margins at fixed total length vanish** under dyadic refinement (RH). -/
theorem tendsto_levinsonErr_dyadic_zero (hRH : RiemannHypothesis) (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun j : ℕ => levinsonErr (weilSeq φ (h / 2 ^ j)) (2 ^ j * n)) atTop (𝓝 0) := by
  have := tendsto_levinsonErr_dyadic_contMargin hRH hφ hφ0 hh hn
  rwa [contMargin_eq_zero hRH hφ (by positivity)] at this

end GaloisForLFunctions.GrowingWindowsOfSpecZ
