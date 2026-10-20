import GaloisForLFunctions.RHTower.ZetaTypicalHeightPairRecurrenceAndHeadZeroObstruction

/-!
# Isolated zeros of partial sums are tail-bad heights; uniform pair returns

Write `head_M(s) = Σ_{n ≤ M} n^{-s}` and `discTailBadSet M c r ε` for the heights `τ` at which
`|ζ − head_M| ≥ ε` somewhere on `closedBall c r + iτ`.

**Isolated partial-sum zeros are rare** (`eventually_eventually_volume_headIsolatedZeroSet_le`).
Call `τ` an *isolated-zero height* of `head_M` on the disc when `head_M(· + iτ)` vanishes in
`ball c r` and has modulus `≥ 2ε` on the boundary circle.  At such a height that is not tail-bad,
the minimum-modulus principle (at the interior zero, `exists_zero_of_exists_norm_lt_sphere_on`)
forces a zero of `ζ` in `ball c r + iτ`; zero-forcing shift sets have density zero.  Hence
isolated-zero heights are tail-bad up to density zero
(`eventually_volume_headIsolatedZeroSet_le_discTailBadSet_add`), and by the disc-uniform Carlson
tail law their density tends to zero as `M → ∞`.  This is a statement about the Dirichlet
polynomials `head_M` alone, derived from the `o(T)` count of zeros of `ζ` right of a fixed abscissa:
the head-zero obstruction to common-height alignment lives on a set of disc translates of
asymptotically vanishing density.  The obstruction itself extends from zeros at the centre to zeros
anywhere in the open disc (`eventually_volume_poleShiftedReturnSet_le_of_exists_zero`).

**Explicit density** (`eventually_volume_discTailBadSet_le_tailMass`).  For fixed `M` the bad
heights have asymptotic density at most `28 K · tailMass(M, Re c − 2r)/ε²`,
`K = (1 + r/(1 − (Re c + 2r)))²`.

**Uniform pair returns** (`exists_eventually_forall_volume_zetaPairReturnFail_le`).  The exceptional
base heights of the pair law can be bounded uniformly over all almost periods `d ∈ [0, T]`, and the
almost periods are relatively dense (`exists_relDense_headPhaseReturnSet`), so every interval of a
fixed length contains an `ε`-almost period of `ζ` valid at density-`(1 − δ)` base heights
(`exists_relDense_zetaReturn_typicalHeight`).
-/

open Complex Filter Topology MeasureTheory Set Metric
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## 1. Minimum modulus at an interior point -/

/-- If `f` is holomorphic near the closed disc and `|f(w)| < |f|` on the boundary circle for some
interior point `w`, then `f` vanishes in the disc. -/
theorem exists_zero_of_exists_norm_lt_sphere_on {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (closedBall c ρ)) {w : ℂ} (hw : w ∈ ball c ρ)
    (h : ∀ z ∈ sphere c ρ, ‖f w‖ < ‖f z‖) :
    ∃ z ∈ ball c ρ, f z = 0 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hcl : ∀ z ∈ closedBall c ρ, f z ≠ 0 := by
    intro z hz
    rcases eq_or_lt_of_le (mem_closedBall.mp hz) with h1 | h1
    · exact norm_pos_iff.mp ((norm_nonneg _).trans_lt (h z (mem_sphere.mpr h1)))
    · exact hne z (mem_ball.mpr h1)
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le)
    (hf.continuousOn.norm.mono sphere_subset_closedBall)
  have hg : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball c ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hρ.ne']
    exact hf.inv hcl
  have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
    (C := ‖f z₁‖⁻¹) (fun z hz => by
      rw [frontier_ball c hρ.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ (norm_pos_iff.mpr (hcl z₁ (sphere_subset_closedBall hz₁))) (hmin hz))
    (subset_closure hw)
  rw [norm_inv] at hbd
  have h1 := h z₁ hz₁
  have hc : 0 < ‖f w‖ := norm_pos_iff.mpr (hcl w (ball_subset_closedBall hw))
  have := (inv_le_inv₀ hc (hc.trans h1)).mp hbd
  linarith

/-! ## 2. Isolated zeros of the partial sum at tail-good heights force zeros of `ζ` -/

/-- Heights `τ` at which `head_M(· + iτ)` has a zero in `ball c r` and modulus at least `2ε` on the
boundary circle. -/
def headIsolatedZeroSet (M : ℕ) (c : ℂ) (r ε : ℝ) : Set ℝ :=
  {τ : ℝ | (∃ z ∈ ball c r, edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) = 0) ∧
    ∀ z ∈ sphere c r, 2 * ε ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I)‖}

theorem exists_zeta_zero_of_mem_headIsolatedZeroSet {M : ℕ} {c : ℂ} {r ε τ : ℝ} (hr : 0 < r)
    (h1 : c.re + r < 1) (hτ : τ ∈ headIsolatedZeroSet M c r ε)
    (hgood : τ ∉ discTailBadSet M c r ε) :
    ∃ z ∈ ball c r, riemannZeta (z + τ * I) = 0 := by
  obtain ⟨⟨w, hw, hw0⟩, hsph⟩ := hτ
  have hdiff : DifferentiableOn ℂ (fun s => riemannZeta (s + τ * I)) (closedBall c r) := by
    intro s hs
    have hne : s + τ * I ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith [re_le_of_mem_closedBall hs]
    exact ((differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have htail : ∀ y ∈ closedBall c r, ‖zetaTailFun M (y + τ * I)‖ < ε := by
    intro y hy
    by_contra hcon
    exact hgood ⟨y, hy, not_lt.mp hcon⟩
  refine exists_zero_of_exists_norm_lt_sphere_on hr hdiff hw fun z hz => ?_
  have hw' := htail w (ball_subset_closedBall hw)
  have hz' := htail z (sphere_subset_closedBall hz)
  have hsz := hsph z hz
  have ew : riemannZeta (w + τ * I) = zetaTailFun M (w + τ * I) := by
    unfold zetaTailFun
    rw [hw0, sub_zero]
  have hz3 := norm_sub_norm_le (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I))
    (riemannZeta (z + τ * I))
  have ez : ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) - riemannZeta (z + τ * I)‖ =
      ‖zetaTailFun M (z + τ * I)‖ := by
    rw [norm_sub_rev]
    rfl
  rw [ez] at hz3
  show ‖riemannZeta (w + τ * I)‖ < ‖riemannZeta (z + τ * I)‖
  rw [ew]
  linarith

/-- **Isolated partial-sum zeros are tail-bad up to density zero.** -/
theorem eventually_volume_headIsolatedZeroSet_le_discTailBadSet_add {M : ℕ} {c : ℂ} {r ε : ℝ}
    (hr : 0 < r) (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop,
      volume (headIsolatedZeroSet M c r ε ∩ Icc 0 T) ≤
        volume (discTailBadSet M c r ε ∩ Icc 0 T) + ENNReal.ofReal (κ * T) := by
  have hr2 : r ≤ (c.re - 1 / 2) / 2 := by linarith
  have hr3 : r ≤ (1 - c.re) / 2 := by linarith
  have hforce : ∀ τ ∈ headIsolatedZeroSet M c r ε \ discTailBadSet M c r ε,
      ∃ z ∈ ball c r, riemannZeta (z + τ * I) = 0 :=
    fun τ hτ => exists_zeta_zero_of_mem_headIsolatedZeroSet hr (by linarith) hτ.1 hτ.2
  filter_upwards [eventually_volume_inter_Icc_le_of_forces_zero hr hr2 hr3 hforce hκ] with T hT
  have hsplit : headIsolatedZeroSet M c r ε ∩ Icc 0 T ⊆
      (discTailBadSet M c r ε ∩ Icc 0 T) ∪
        ((headIsolatedZeroSet M c r ε \ discTailBadSet M c r ε) ∩ Icc 0 T) := by
    rintro τ ⟨hτ, hI⟩
    by_cases hb : τ ∈ discTailBadSet M c r ε
    · exact Or.inl ⟨hb, hI⟩
    · exact Or.inr ⟨⟨hτ, hb⟩, hI⟩
  calc volume (headIsolatedZeroSet M c r ε ∩ Icc 0 T)
      ≤ volume ((discTailBadSet M c r ε ∩ Icc 0 T) ∪
          ((headIsolatedZeroSet M c r ε \ discTailBadSet M c r ε) ∩ Icc 0 T)) :=
        measure_mono hsplit
    _ ≤ volume (discTailBadSet M c r ε ∩ Icc 0 T) +
          volume ((headIsolatedZeroSet M c r ε \ discTailBadSet M c r ε) ∩ Icc 0 T) :=
        measure_union_le _ _
    _ ≤ volume (discTailBadSet M c r ε ∩ Icc 0 T) + ENNReal.ofReal (κ * T) :=
        add_le_add le_rfl hT

/-- **Isolated zeros of partial sums are rare right of any abscissa `> 1/2`.**  For every disc
`closedBall c (2r) ⊂ {1/2 < Re s < 1}` and `ε, δ > 0`, for all large `M` the heights at which
`head_M(· + iτ)` has a zero in `ball c r` and modulus `≥ 2ε` on its boundary circle have density
at most `δ`. -/
theorem eventually_eventually_volume_headIsolatedZeroSet_le {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ᶠ T : ℝ in atTop,
      volume (headIsolatedZeroSet M c r ε ∩ Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  filter_upwards [eventually_eventually_volume_discTailBadSet_le hr h0 h1 hε (half_pos hδ)]
    with M hM
  filter_upwards [hM, eventually_volume_headIsolatedZeroSet_le_discTailBadSet_add (M := M)
    (ε := ε) hr h0 h1 (half_pos hδ), eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  calc volume (headIsolatedZeroSet M c r ε ∩ Icc 0 T)
      ≤ volume (discTailBadSet M c r ε ∩ Icc 0 T) + ENNReal.ofReal (δ / 2 * T) := hT2
    _ ≤ ENNReal.ofReal (δ / 2 * T) + ENNReal.ofReal (δ / 2 * T) := add_le_add hT1 le_rfl
    _ = ENNReal.ofReal (δ * T) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-! ## 3. The head-zero obstruction for zeros anywhere in the disc -/

/-- A pole-shifted return forces a zero of `ζ` in the translated disc when `head_M` vanishes
somewhere in the open disc and `|head_M| ≥ m ≥ 2ε` on the boundary circle. -/
theorem exists_zero_of_mem_poleShiftedReturnSet_of_exists_zero {M : ℕ} {ρ₀ : ℂ} {r m ε τ : ℝ}
    (hr : 0 < r) (hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1)
    (hw : ∃ w ∈ ball ρ₀ r, edPoly (fun _ => 1) (Finset.Icc 1 M) w = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) z‖) (hε : ε ≤ m / 2)
    (hτ : τ ∈ poleShiftedReturnSet M (closedBall ρ₀ r) ε) :
    ∃ z ∈ ball ρ₀ r, riemannZeta (z + τ * I) = 0 := by
  obtain ⟨w, hw, hw0⟩ := hw
  have hdiff : DifferentiableOn ℂ (fun s => riemannZeta (s + τ * I)) (closedBall ρ₀ r) := by
    intro s hs
    have hne : s + τ * I ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith [hre s hs]
    exact ((differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  refine exists_zero_of_exists_norm_lt_sphere_on hr hdiff hw fun z hz => ?_
  have h1 := hτ w (ball_subset_closedBall hw)
  rw [hw0, sub_zero] at h1
  have h2 := hτ z (sphere_subset_closedBall hz)
  have h3 := hm z hz
  have h4 := norm_sub_norm_le (edPoly (fun _ => 1) (Finset.Icc 1 M) z) (riemannZeta (z + τ * I))
  rw [norm_sub_rev] at h4
  show ‖riemannZeta (w + τ * I)‖ < ‖riemannZeta (z + τ * I)‖
  linarith

/-- The head-zero obstruction for a zero anywhere in the open disc: the pole-shifted return set has
density zero. -/
theorem eventually_volume_poleShiftedReturnSet_le_of_exists_zero {M : ℕ} {ρ₀ : ℂ} {r m ε : ℝ}
    (hr : 0 < r) (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2)
    (hw : ∃ w ∈ ball ρ₀ r, edPoly (fun _ => 1) (Finset.Icc 1 M) w = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖edPoly (fun _ => 1) (Finset.Icc 1 M) z‖) (hε : ε ≤ m / 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T in atTop, volume (poleShiftedReturnSet M (closedBall ρ₀ r) ε ∩ Icc 0 T) ≤
      ENNReal.ofReal (κ * T) := by
  have hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1 := fun s hs => by
    have := re_le_of_mem_closedBall hs
    linarith
  exact eventually_volume_inter_Icc_le_of_forces_zero hr hr2 hr3
    (fun τ hτ => exists_zero_of_mem_poleShiftedReturnSet_of_exists_zero hr hre hw hm hε hτ) hκ

/-! ## 4. Explicit density of the bad heights at fixed `M` -/

/-- For fixed `M`, the bad heights have asymptotic density at most
`28 K · tailMass(M, Re c − 2r) / ε²`, `K = (1 + r/(1 − (Re c + 2r)))²`. -/
theorem eventually_volume_discTailBadSet_le_tailMass (M : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε : ℝ} (hε : 0 < ε) {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, volume (discTailBadSet M c r ε ∩ Icc 0 T) ≤
      ENNReal.ofReal ((28 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 / ε ^ 2 *
        zetaCoefficientTailMass M (c.re - 2 * r) + κ) * T) := by
  set K : ℝ := (1 + r / (1 - (c.re + 2 * r))) ^ 2 with hK
  have hL : 0 < 1 - (c.re + 2 * r) := by linarith
  have hK0 : 0 < K := by positivity
  have hKne : K ≠ 0 := hK0.ne'
  have hεne : ε ≠ 0 := hε.ne'
  have hτ0 := zetaCoefficientTailMass_nonneg M (c.re - 2 * r)
  set η : ℝ := κ * ε ^ 2 / (28 * K) with hη
  have hη0 : 0 < η := by positivity
  set β : ℝ := 7 * K / ε ^ 2 * (2 * zetaCoefficientTailMass M (c.re - 2 * r) + η) with hβ
  have hβ0 : 0 ≤ β := mul_nonneg (by positivity) (by linarith)
  have hwin : ∀ᶠ V : ℝ in atTop,
      volume (discTailBadSet M c r ε ∩ Icc (V / 2) V) ≤ ENNReal.ofReal (β * V) := by
    filter_upwards [eventually_uniform_window_zetaDirichletTail_meanSquare_le M h0
      (by linarith) h1 hη0, eventually_ge_atTop (4 * (|c.im| + 2 * r)),
      eventually_ge_atTop (0 : ℝ)] with V hVwin hV4 hV0
    have hB0 : 0 ≤ 7 * V / 4 * (2 * zetaCoefficientTailMass M (c.re - 2 * r) + η) :=
      mul_nonneg (by positivity) (by linarith)
    refine (volume_discTailBadSet_window_le M hr h1 hε hV4 hB0 hVwin).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hβ]
    ring
  filter_upwards [eventually_volume_inter_Icc_le_of_dyadic_window hβ0 hwin (half_pos hκ),
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have hβeq : 2 * β = 28 * K / ε ^ 2 * zetaCoefficientTailMass M (c.re - 2 * r) + κ / 2 := by
    rw [hβ, hη]
    field_simp
    ring
  exact mul_le_mul_of_nonneg_right (by linarith) hT0

/-! ## 5. Uniform pair returns and relative density of the almost periods -/

/-- **Uniform pair returns.**  For all large `T`, every almost period `d ∈ [0, T]` of the head
fails to be an `ε`-return shift of `ζ` on `closedBall (c + iτ₁) r` for at most `δ T` base heights
`τ₁ ∈ [0, T]`. -/
theorem exists_eventually_forall_volume_zetaPairReturnFail_le {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M : ℕ, ∃ θ > 0, ∀ᶠ T : ℝ in atTop, ∀ d ∈ headPhaseReturnSet M θ ∩ Icc 0 T,
      volume ({τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  obtain ⟨M, hM⟩ := (eventually_eventually_volume_discTailBadSet_le hr h0 h1
    (by positivity : 0 < ε / 3) (by positivity : 0 < δ / 3)).exists
  refine ⟨M, ε / (3 * (M + 1)), by positivity, ?_⟩
  have hMθ : (M : ℝ) * (ε / (3 * (M + 1))) ≤ ε / 3 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  filter_upwards [hM, (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2)).eventually hM,
    eventually_ge_atTop (0 : ℝ)] with T hT1 hT2 hT0
  rintro d ⟨hdE, hdI⟩
  have hsub := zetaPairReturnFail_subset_discTailBadSet_union hr h0 hMθ hdE
  have hsub2 : (fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T ⊆
      (fun τ₁ : ℝ => τ₁ + d) ⁻¹' (discTailBadSet M c r (ε / 3) ∩ Icc 0 (2 * T)) := by
    rintro τ₁ ⟨hb, hI⟩
    exact ⟨hb, by linarith [hI.1, hdI.1], by linarith [hI.2, hdI.2]⟩
  calc volume ({τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ∩ Icc 0 T)
      ≤ volume ((discTailBadSet M c r (ε / 3) ∩ Icc 0 T) ∪
          ((fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T)) := by
        refine measure_mono ?_
        rintro τ₁ ⟨hτ, hI⟩
        rcases hsub hτ with h | h
        · exact Or.inl ⟨h, hI⟩
        · exact Or.inr ⟨h, hI⟩
    _ ≤ volume (discTailBadSet M c r (ε / 3) ∩ Icc 0 T) +
          volume ((fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 3 * T) + volume (discTailBadSet M c r (ε / 3) ∩ Icc 0 (2 * T)) := by
        refine add_le_add hT1 ?_
        calc volume ((fun τ₁ : ℝ => τ₁ + d) ⁻¹' discTailBadSet M c r (ε / 3) ∩ Icc 0 T)
            ≤ volume ((fun τ₁ : ℝ => τ₁ + d) ⁻¹'
                (discTailBadSet M c r (ε / 3) ∩ Icc 0 (2 * T))) := measure_mono hsub2
          _ = volume (discTailBadSet M c r (ε / 3) ∩ Icc 0 (2 * T)) :=
              measure_preimage_add_right _ _ _
    _ ≤ ENNReal.ofReal (δ / 3 * T) + ENNReal.ofReal (δ / 3 * (2 * T)) := add_le_add le_rfl hT2
    _ = ENNReal.ofReal (δ * T) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Simultaneous almost periods of the head phases are relatively dense. -/
theorem exists_relDense_headPhaseReturnSet (M : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ L > 0, ∀ a : ℝ, ∃ d ∈ Icc a (a + L), d ∈ headPhaseReturnSet M θ := by
  set u : Fin M → ℝ := fun j => Real.log ((j : ℕ) + 1) with hu
  obtain ⟨L, hL, hper⟩ := isBohrAlmostPeriodic_bohrCharVector M u (θ / 2) (half_pos hθ)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨d, hd, hdper⟩ := hper a
  refine ⟨d, hd, fun n hn => ?_⟩
  obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
  have h := hdper 0
  rw [zero_add] at h
  have h' := (pi_norm_le_iff_of_nonneg (by positivity)).mp h ⟨n - 1, by omega⟩
  rw [Pi.sub_apply, bohrCharVector_zero] at h'
  simp only [bohrCharVector, hu] at h'
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn1
  rw [hcast] at h'
  linarith

/-- Every interval of a fixed length `L` contains an `ε`-almost period of `ζ` on the disc, valid at
all base heights outside a set of density `≤ δ`. -/
theorem exists_relDense_zetaReturn_typicalHeight {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ L > 0, ∀ a : ℝ, ∃ d ∈ Icc a (a + L), ∀ᶠ T : ℝ in atTop,
      volume ({τ₁ : ℝ | d ∉ zetaReturnSet (closedBall (c + τ₁ * I) r) ε} ∩ Icc 0 T) ≤
        ENNReal.ofReal (δ * T) := by
  obtain ⟨M, θ, hθ, hd⟩ := exists_headPhaseReturnSet_zetaReturn_typicalHeight hr h0 h1 hε hδ
  obtain ⟨L, hL, hrel⟩ := exists_relDense_headPhaseReturnSet M hθ
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨d, hdI, hdE⟩ := hrel a
  exact ⟨d, hdI, hd d hdE⟩

end RHTower
