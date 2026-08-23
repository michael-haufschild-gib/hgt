import GaloisForLFunctions.RHTower.BurnolContourLimits
import GaloisForLFunctions.RHTower.SoninMellinMultiplier

/-!
# Burnol's Theorem 5.2: the series of residues

Putting the contour together.  For a fixed abscissa `A` the rectangle identity of
`BurnolRectangleSum` and the edge limits of `BurnolContourLimits` give

`∑_{|Im ρ| < T_k} Res_ρ  →  M(f)(Z) + (1/2π)·ζ(Z)·(∫_{Re s = 1/2+A} − ∫_{Re s = 1/2−A})`,

and the right-hand correction tends to `0` as `A → ∞`: on the right by the Hardy `L²` bound paired
against the Cauchy kernel, on the left by the functional equation, which turns the left line into
the right line of the Fourier-transformed datum.

## Main results

* `riemannZeta_ne_zero_of_abs_im_ne` — the selected heights carry no zero.
* `tendsto_residueSum_of_abscissa` — the limit at a fixed abscissa.
* `tendsto_residueSum_extendedMellin` — **Theorem 5.2, pointwise convergence.**
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Conjugate symmetry of the height selection -/

theorem line_conj (σ t : ℝ) :
    ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * I) := by
  apply Complex.ext <;> simp

theorem norm_zeta_inv_neg_height (σ t : ℝ) :
    ‖(riemannZeta ((σ : ℂ) + ((-t : ℝ) : ℂ) * I))⁻¹‖
      = ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ := by
  rw [line_conj, riemannZeta_conj, ← map_inv₀, Complex.norm_conj]

theorem riemannZeta_ne_zero_neg_height {σ t : ℝ}
    (h : riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0) :
    riemannZeta ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) ≠ 0 := by
  rw [line_conj, riemannZeta_conj]
  simpa using h

/-- **No zero of `ζ` at a selected height.** -/
theorem riemannZeta_ne_zero_of_abs_im_ne {T : ℝ} (hT : 0 < T)
    (hne : ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 → riemannZeta ((σ : ℂ) + (T : ℂ) * I) ≠ 0) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≠ T := by
  intro ρ hzero h1 h2 habs
  have hre1 : -1 ≤ ρ.re := by linarith
  have hre2 : ρ.re ≤ 2 := by linarith
  rcases abs_eq (le_of_lt hT) |>.1 habs with him | him
  · refine hne ρ.re hre1 hre2 ?_
    have : ((ρ.re : ℝ) : ℂ) + (T : ℂ) * I = ρ := by
      apply Complex.ext <;> simp [him]
    rw [this]
    exact hzero
  · refine hne ρ.re hre1 hre2 ?_
    have hconj : (starRingEnd ℂ) ρ = ((ρ.re : ℝ) : ℂ) + (T : ℂ) * I := by
      apply Complex.ext <;> simp [him]
    have := riemannZeta_conj ρ
    rw [hconj, hzero] at this
    simpa using this

/-! ## The limit at a fixed abscissa -/

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

theorem tendsto_residueSum_of_abscissa (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    (hTne : ∀ k : ℕ, ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I) ≠ 0)
    (hzeta : ∀ b : ℝ, 2 ≤ b → ∃ (C Aexp : ℝ) (k₀ : ℕ), 0 < C ∧ 0 < Aexp ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
        ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ Aexp)
    {Z : ℂ} (hZζ : riemannZeta Z ≠ 0) (hZ1 : Z ≠ 1) (hZ0 : Z ≠ 0)
    {A : ℝ} (hA : 3 / 2 ≤ A)
    (hAint : ∀ k : ℕ, (1 / 2 - A : ℝ) ≠ -(2 * ((k : ℝ) + 1)))
    (hZr1 : 1 / 2 - A < Z.re) (hZr2 : Z.re < 1 / 2 + A) (hZr3 : (1 - Z).re < 1 / 2 + A) :
    Tendsto (fun k : ℕ => ∑ ρ ∈ nontrivialZeroFinset (T k),
        laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1)) atTop
      (𝓝 (extendedMellinContinuation a c d f Z
        + (1 / (2 * (Real.pi : ℂ))) * riemannZeta Z *
          ((∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
              (((1 / 2 + A : ℝ) : ℂ) + (y : ℂ) * I))
            - ∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
              (((1 / 2 - A : ℝ) : ℂ) + (y : ℂ) * I)))) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨C, Aexp, k₀, hC, hAexp, hbound⟩ := hzeta (A + 1) (by linarith)
  have hposb : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -(A + 1) ≤ σ → σ ≤ A + 1 →
      ‖(riemannZeta ((σ : ℂ) + (((1 : ℝ) * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ Aexp := by
    intro k hk σ h1 h2
    simpa using hbound k hk σ h1 h2
  have hnegb : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -(A + 1) ≤ σ → σ ≤ A + 1 →
      ‖(riemannZeta ((σ : ℂ) + (((-1 : ℝ) * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ Aexp := by
    intro k hk σ h1 h2
    have h := hbound k hk σ h1 h2
    rw [show ((-1 : ℝ) * T k) = -(T k) by ring, norm_zeta_inv_neg_height]
    exact h
  have hσ2 : (2 : ℝ) ≤ 1 / 2 + A := by linarith
  have hintR : Integrable (fun y : ℝ =>
      burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 / 2 + A : ℝ) : ℂ) + (y : ℂ) * I)) volume :=
    integrable_burnolEdgeIntegrand_right ha hev hc hd hσ2 hZr2
  have hintL : Integrable (fun y : ℝ =>
      burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 / 2 - A : ℝ) : ℂ) + (y : ℂ) * I)) volume := by
    have h := integrable_burnolEdgeIntegrand_left ha hev hc hd hσ2 hZr3
    rw [show (1 - (1 / 2 + A) : ℝ) = 1 / 2 - A by ring] at h
    exact h
  have hrect := tendsto_rectangleIntegral'_burnolIntegrand
    (G := extendedMellinContinuation a c d f) hrapid htop hT1 hC hAexp
    (b := A + 1) (by linarith) hposb hnegb (A := A) (by linarith) (by linarith) (by linarith)
    hintR hintL
  have heq : ∀ᶠ k : ℕ in atTop,
      RectangleIntegral' (burnolIntegrand (extendedMellinContinuation a c d f) Z)
          (burnolRectLow A (T k)) (burnolRectHigh A (T k))
        = -extendedMellinContinuation a c d f Z
          + ∑ ρ ∈ nontrivialZeroFinset (T k),
              laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1) := by
    filter_upwards [htop.eventually_gt_atTop |Z.im|] with k hk
    have hTk : (0 : ℝ) < T k := lt_of_lt_of_le zero_lt_one (hT1 k)
    exact rectangleIntegral'_burnolIntegrand_extendedMellin ha0 hev hc hd hZζ hZ1 hZ0
      (by linarith) hTk hAint hZr1 hZr2 hk
      (riemannZeta_ne_zero_of_abs_im_ne hTk (hTne k))
  have hlim := hrect.congr' heq
  have hadd := (tendsto_const_nhds (x := extendedMellinContinuation a c d f Z)
    (f := (atTop : Filter ℕ))).add hlim
  refine Tendsto.congr (fun k => ?_) hadd
  ring

/-! ## The vertical lines vanish as the abscissa grows -/

theorem tendsto_lineIntegral_right_zero (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (Z : ℂ) :
    Tendsto (fun σ : ℝ => ∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
      ((σ : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
  have h := tendsto_vertical_edge_zero ha hev hc hd Z
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h.congr fun σ => ?_
  simp only [burnolEdgeIntegrand]

theorem tendsto_lineIntegral_left_zero (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (Z : ℂ) :
    Tendsto (fun σ : ℝ => ∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
      (((1 - σ : ℝ) : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
  have hrefl := tendsto_lineIntegral_right_zero (a := a) (c := d) (d := c)
    (f := fourierUnitary f) ha (fourierUnitary_mem_evenSubspace hev)
    (fourierUnitary_band_of_reflect hev hd) hc (1 - Z)
  have hneg : Tendsto (fun σ : ℝ =>
      -∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f)) (1 - Z)
        ((σ : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    simpa using hrefl.neg
  refine hneg.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with σ hσ
  exact (integral_burnolEdgeIntegrand_left a c d f hσ Z).symm

/-! ## Theorem 5.2, pointwise -/

/-- **Burnol's Theorem 5.2 (pointwise convergence).**  For a fixed `Z` which is neither `0`, nor
`1`, nor a zero of `ζ`, the series of residues of `M(f)(s)ζ(Z)/(ζ(s)(Z−s))` over the nontrivial
zeros, summed in Burnol's grouping by the selected heights, converges to `M(f)(Z)`.

The residue at a zero `ρ` is its Laurent coefficient, so no hypothesis whatsoever is made on the
multiplicities — exactly the convention of Note 13 of the paper. -/
theorem tendsto_residueSum_extendedMellin (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    (hTne : ∀ k : ℕ, ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I) ≠ 0)
    (hzeta : ∀ b : ℝ, 2 ≤ b → ∃ (C Aexp : ℝ) (k₀ : ℕ), 0 < C ∧ 0 < Aexp ∧
      ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
        ‖(riemannZeta ((σ : ℂ) + ((T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ Aexp)
    {Z : ℂ} (hZζ : riemannZeta Z ≠ 0) (hZ1 : Z ≠ 1) (hZ0 : Z ≠ 0) :
    Tendsto (fun k : ℕ => ∑ ρ ∈ nontrivialZeroFinset (T k),
        laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1)) atTop
      (𝓝 (extendedMellinContinuation a c d f Z)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (|Z.re| + |(1 - Z).re| + 4 : ℝ)
  set A : ℕ → ℝ := fun j => (j : ℝ) + (N₀ : ℝ) + 3 / 4 with hAdef
  have hZre : Z.re ≤ |Z.re| := le_abs_self _
  have hZre' : -Z.re ≤ |Z.re| := neg_le_abs _
  have hWre : (1 - Z).re ≤ |(1 - Z).re| := le_abs_self _
  have habs0 : (0 : ℝ) ≤ |Z.re| := abs_nonneg _
  have habs1 : (0 : ℝ) ≤ |(1 - Z).re| := abs_nonneg _
  have hAj : ∀ j : ℕ, |Z.re| + |(1 - Z).re| + 4 ≤ A j := by
    intro j
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [hAdef]
    simp only
    linarith
  have hint : ∀ j : ℕ, ∀ k : ℕ, (1 / 2 - A j : ℝ) ≠ -(2 * ((k : ℝ) + 1)) := by
    intro j k hcon
    rw [hAdef] at hcon
    simp only at hcon
    have hcast : ((4 * (j + N₀) : ℕ) : ℝ) = 8 * (k : ℝ) + 7 := by
      push_cast
      linarith
    have hZint : (4 * (j + N₀) : ℤ) = 8 * (k : ℤ) + 7 := by exact_mod_cast hcast
    omega
  have hkey : ∀ j : ℕ, Tendsto (fun k : ℕ => ∑ ρ ∈ nontrivialZeroFinset (T k),
      laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1)) atTop
      (𝓝 (extendedMellinContinuation a c d f Z
        + (1 / (2 * (Real.pi : ℂ))) * riemannZeta Z *
          ((∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
              (((1 / 2 + A j : ℝ) : ℂ) + (y : ℂ) * I))
            - ∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
              (((1 / 2 - A j : ℝ) : ℂ) + (y : ℂ) * I)))) := by
    intro j
    have hbig := hAj j
    exact tendsto_residueSum_of_abscissa ha hev hc hd hrapid htop hT1 hTne hzeta hZζ hZ1 hZ0
      (by linarith) (hint j) (by linarith) (by linarith) (by linarith)
  -- the correction term is independent of `j`
  set L : ℕ → ℂ := fun j => (1 / (2 * (Real.pi : ℂ))) * riemannZeta Z *
    ((∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 / 2 + A j : ℝ) : ℂ) + (y : ℂ) * I))
      - ∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 / 2 - A j : ℝ) : ℂ) + (y : ℂ) * I)) with hLdef
  have hconst : ∀ j : ℕ, L j = L 0 := by
    intro j
    have h := tendsto_nhds_unique (hkey j) (hkey 0)
    exact add_left_cancel h
  -- and it tends to zero
  have hAtop : Tendsto A atTop atTop := by
    rw [hAdef]
    refine tendsto_atTop_add_const_right _ _ ?_
    exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R := ℝ))
  have hRtop : Tendsto (fun j : ℕ => 1 / 2 + A j) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hAtop
  have hR0 : Tendsto (fun j : ℕ => ∫ y : ℝ,
      burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 / 2 + A j : ℝ) : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) :=
    (tendsto_lineIntegral_right_zero ha hev hc hd Z).comp hRtop
  have hL0 : Tendsto (fun j : ℕ => ∫ y : ℝ,
      burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
        (((1 / 2 - A j : ℝ) : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    have h := (tendsto_lineIntegral_left_zero ha hev hc hd Z).comp hRtop
    refine h.congr fun j => ?_
    simp only [Function.comp_apply]
    rw [show (1 - (1 / 2 + A j) : ℝ) = 1 / 2 - A j by ring]
  have hLzero : Tendsto L atTop (𝓝 0) := by
    have := ((hR0.sub hL0).const_mul ((1 / (2 * (Real.pi : ℂ))) * riemannZeta Z))
    simpa [hLdef] using this
  have hLval : L 0 = 0 := by
    have hcongr : Tendsto (fun _ : ℕ => L 0) atTop (𝓝 0) := by
      refine hLzero.congr fun j => ?_
      exact hconst j
    exact tendsto_nhds_unique tendsto_const_nhds hcongr
  have hfin := hkey 0
  rw [show (1 / (2 * (Real.pi : ℂ))) * riemannZeta Z *
      ((∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
          (((1 / 2 + A 0 : ℝ) : ℂ) + (y : ℂ) * I))
        - ∫ y : ℝ, burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z
          (((1 / 2 - A 0 : ℝ) : ℂ) + (y : ℂ) * I)) = L 0 from rfl, hLval, add_zero] at hfin
  exact hfin

/-! ## The packaged statement -/

/-- **Theorem 5.2, with the heights supplied by Proposition 5.1.**  One sequence of heights works
for every `Z` at once, exactly as in Note 13. -/
theorem exists_seq_tendsto_residueSum_extendedMellin (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f)) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧ (∀ k : ℕ, 1 ≤ T k) ∧
      ∀ Z : ℂ, riemannZeta Z ≠ 0 → Z ≠ 1 → Z ≠ 0 →
        Tendsto (fun k : ℕ => ∑ ρ ∈ nontrivialZeroFinset (T k),
            laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1)) atTop
          (𝓝 (extendedMellinContinuation a c d f Z)) := by
  obtain ⟨T, hmono, htop, hT1, hspace, hTne, hzeta⟩ := exists_seq_zeta_inv_horizontal
  refine ⟨T, hmono, htop, hT1, fun Z hZζ hZ1 hZ0 => ?_⟩
  refine tendsto_residueSum_extendedMellin ha hev hc hd hrapid htop hT1 hTne ?_ hZζ hZ1 hZ0
  intro b hb
  obtain ⟨C, Aexp, k₀, hC, hAexp, hbound⟩ := hzeta b hb
  exact ⟨C, Aexp, k₀, hC, hAexp, hbound⟩

/-- **Theorem 5.2 for a vector of Definition 12.** -/
theorem exists_tendsto_residueSum_of_hasRapidMellin (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hrm : HasRapidMellin a f) :
    ∃ (c d : ℂ) (T : ℕ → ℝ), StrictMono T ∧ Tendsto T atTop atTop ∧ (∀ k : ℕ, 1 ≤ T k) ∧
      ∀ Z : ℂ, riemannZeta Z ≠ 0 → Z ≠ 1 → Z ≠ 0 →
        Tendsto (fun k : ℕ => ∑ ρ ∈ nontrivialZeroFinset (T k),
            laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1)) atTop
          (𝓝 (extendedMellinContinuation a c d f Z)) := by
  obtain ⟨c, d, hc, hd, hrapid⟩ := hrm
  obtain ⟨T, hmono, htop, hT1, hconv⟩ :=
    exists_seq_tendsto_residueSum_extendedMellin ha hev hc hd hrapid
  exact ⟨c, d, T, hmono, htop, hT1, hconv⟩

/-! ## Corollary 5.3: completeness of the evaluators -/

/-- **Corollary 5.3.**  If the Mellin transform of a vector of the dense subspace vanishes at every
nontrivial zero of `ζ` to at least the order of `ζ` there — i.e. if `ζ` divides it, which is exactly
the statement that the vector is orthogonal to all the evaluators `ζ(s)/(s−ρ)^l` — then the
transform vanishes identically off `{0, 1}`.  The system of evaluators is therefore complete. -/
theorem extendedMellinContinuation_eq_zero_of_dvd (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    (hdvd : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      meromorphicOrderAt riemannZeta ρ
        ≤ meromorphicOrderAt (extendedMellinContinuation a c d f) ρ)
    {Z : ℂ} (hZζ : riemannZeta Z ≠ 0) (hZ1 : Z ≠ 1) (hZ0 : Z ≠ 0) :
    extendedMellinContinuation a c d f Z = 0 := by
  obtain ⟨T, hmono, htop, hT1, hconv⟩ :=
    exists_seq_tendsto_residueSum_extendedMellin ha hev hc hd hrapid
  have hlim := hconv Z hZζ hZ1 hZ0
  have hzero : ∀ k : ℕ, ∑ ρ ∈ nontrivialZeroFinset (T k),
      laurentCoeff (burnolIntegrand (extendedMellinContinuation a c d f) Z) ρ (-1) = 0 := by
    intro k
    refine Finset.sum_eq_zero fun ρ hρ => ?_
    obtain ⟨hzero, h1, h2, -⟩ := mem_nontrivialZeroFinset.1 hρ
    have hρZ : ρ ≠ Z := by
      intro hcon
      rw [hcon] at hzero
      exact hZζ hzero
    have hmero : MeromorphicAt (extendedMellinContinuation a c d f) ρ :=
      meromorphicAt_extendedMellinContinuation (lt_of_lt_of_le zero_lt_one ha) hev hc hd ρ
    refine laurentCoeff_burnolIntegrand_eq_zero_of_le hmero ?_
    rw [meromorphicOrderAt_burnolIntegrand hmero hZζ hρZ]
    -- the order of the numerator dominates the order of `ζ`
    have hle := hdvd ρ hzero h1 h2
    induction hx : meromorphicOrderAt riemannZeta ρ with
    | top =>
        rw [hx] at hle
        have htop' : meromorphicOrderAt (extendedMellinContinuation a c d f) ρ = ⊤ :=
          top_le_iff.1 hle
        rw [htop']
        simp
    | coe n =>
        rw [hx] at hle
        exact withTop_sub_nonneg_of_le hle
  have hconst : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop
      (𝓝 (extendedMellinContinuation a c d f Z)) := by
    refine hlim.congr fun k => ?_
    exact hzero k
  exact (tendsto_nhds_unique tendsto_const_nhds hconst).symm

end

end RHTower
