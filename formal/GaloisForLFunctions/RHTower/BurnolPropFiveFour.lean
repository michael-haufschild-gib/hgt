import GaloisForLFunctions.RHTower.BurnolQuotientContour

/-!
# Burnol's Proposition 5.4

`0 = Σ_ρ M(f)(ρ)/ζ'(ρ)`: the series of residues of `M(f)/ζ` over the nontrivial zeros, grouped by
the selected heights of Proposition 5.1, converges to zero.

Both vertical sides of the contour vanish: the one on `Re s = 2` by the Möbius expansion
(`BurnolMoebiusLine`), the one on `Re s = −1` by the functional equation, which turns it into the
right-hand side of the Fourier-transformed datum — this is where Lemma 4.10 is needed.

## Main results

* `burnolQuotient_reflect_line`, `integral_burnolQuotient_neg_one_eq_zero`
* `exists_seq_tendsto_residueSum_quotient` — **Proposition 5.4**.
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-! ## The left line through the functional equation -/

theorem burnolQuotient_reflect_line (a : ℝ) (c d : ℂ) (f : SoninL2) {τ : ℝ} (hτ : τ ≠ 0) :
    burnolQuotient (extendedMellinContinuation a c d f) ((-1 : ℂ) + (τ : ℂ) * I)
      = burnolQuotient (extendedMellinContinuation a d c (fourierUnitary f))
          ((2 : ℂ) + ((-τ : ℝ) : ℂ) * I) := by
  set s : ℂ := (-1 : ℂ) + (τ : ℂ) * I with hsdef
  have hsre : s.re = -1 := by rw [hsdef]; simp
  have hsim : s.im = τ := by rw [hsdef]; simp
  have hint : ∀ m : ℤ, s ≠ (m : ℂ) := by
    intro m hm
    have := congrArg Complex.im hm
    rw [hsim] at this
    simp at this
    exact hτ this
  have hchi : burnolChiFactor s ≠ 0 := burnolChiFactor_ne_zero hint
  have hzeta : riemannZeta s = burnolChiFactor s * riemannZeta (1 - s) :=
    riemannZeta_eq_burnolChiFactor_mul_one_sub hint
  have hmel : extendedMellinContinuation a c d f s
      = burnolChiFactor s * extendedMellinContinuation a d c (fourierUnitary f) (1 - s) :=
    extendedMellinContinuation_reflect a c d f (by rw [hsre]; norm_num)
  have harg : (1 : ℂ) - s = (2 : ℂ) + ((-τ : ℝ) : ℂ) * I := by
    rw [hsdef]
    push_cast
    ring
  rw [burnolQuotient, burnolQuotient, hmel, hzeta, ← harg, mul_inv]
  field_simp

/-! ## Integrability and vanishing on the two lines -/

theorem integrable_burnolQuotient_two (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f)) :
    Integrable (fun τ : ℝ =>
      burnolQuotient (extendedMellinContinuation a c d f) ((2 : ℂ) + (τ : ℂ) * I)) volume := by
  have hcontG : Continuous fun τ : ℝ =>
      extendedMellinContinuation a c d f ((2 : ℂ) + (τ : ℂ) * I) := by
    have h := continuous_extendedMellinContinuation_line ha hev hc hd
      (σ := (2 : ℝ)) (by norm_num) (by norm_num)
    simpa using h
  have hintG : Integrable (fun τ : ℝ =>
      extendedMellinContinuation a c d f ((2 : ℂ) + (τ : ℂ) * I)) volume :=
    integrable_line_of_stripRapidDecrease hrapid hcontG
  have hζne : ∀ τ : ℝ, riemannZeta ((2 : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    intro τ
    have hre : ((2 : ℂ) + (τ : ℂ) * I).re = 2 := by simp
    have h := norm_riemannZeta_ge_of_two_le_re (s := (2 : ℂ) + (τ : ℂ) * I) (by rw [hre])
    intro hzero
    rw [hzero] at h
    simp at h
    linarith
  have hcontζ : Continuous fun τ : ℝ => (riemannZeta ((2 : ℂ) + (τ : ℂ) * I))⁻¹ := by
    have h := continuous_riemannZeta_inv_line (σ := (2 : ℝ)) (by norm_num) ?_
    · simpa using h
    · intro t
      have := hζne t
      simpa using this
  refine Integrable.mono' (hintG.norm.const_mul 4) ((hcontG.mul hcontζ).aestronglyMeasurable) ?_
  filter_upwards with τ
  have hζ4 : ‖(riemannZeta ((2 : ℂ) + (τ : ℂ) * I))⁻¹‖ ≤ 4 := by
    refine norm_zeta_inv_le_of_two_le_re ?_
    simp
  rw [burnolQuotient, norm_mul]
  have hG0 : (0:ℝ) ≤ ‖extendedMellinContinuation a c d f ((2 : ℂ) + (τ : ℂ) * I)‖ := norm_nonneg _
  nlinarith [hζ4, hG0]

theorem integrable_burnolQuotient_neg_one (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f)) :
    Integrable (fun τ : ℝ =>
      burnolQuotient (extendedMellinContinuation a c d f) ((-1 : ℂ) + (τ : ℂ) * I)) volume := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hrapid' := hasStripRapidDecrease_reflect ha0 hev hc hd hrapid
  have hright := integrable_burnolQuotient_two (a := a) (c := d) (d := c)
    (f := fourierUnitary f) ha0 (fourierUnitary_mem_evenSubspace hev)
    (fourierUnitary_band_of_reflect hev hd) hc hrapid'
  have h1 : Integrable (fun τ : ℝ =>
      burnolQuotient (extendedMellinContinuation a d c (fourierUnitary f))
        ((2 : ℂ) + ((-τ : ℝ) : ℂ) * I)) volume := by
    have h := hright.comp_neg
    refine h.congr ?_
    filter_upwards with τ
    norm_num
  refine h1.congr ?_
  have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
  filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hnull] with τ hτ
  have hτ0 : τ ≠ 0 := by simpa using hτ
  exact (burnolQuotient_reflect_line a c d f hτ0).symm

/-- **The left line integral vanishes**, by the functional equation and Lemma 4.10. -/
theorem integral_burnolQuotient_neg_one_eq_zero (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f)) :
    (∫ τ : ℝ, burnolQuotient (extendedMellinContinuation a c d f)
      ((-1 : ℂ) + (τ : ℂ) * I)) = 0 := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hrapid' := hasStripRapidDecrease_reflect ha0 hev hc hd hrapid
  have hright := integral_extendedMellin_zeta_inv_two_eq_zero (a := a) (c := d) (d := c)
    (f := fourierUnitary f) ha (fourierUnitary_mem_evenSubspace hev)
    (fourierUnitary_band_of_reflect hev hd) hc hrapid'
  have hae : (fun τ : ℝ => burnolQuotient (extendedMellinContinuation a c d f)
      ((-1 : ℂ) + (τ : ℂ) * I))
      =ᵐ[volume] fun τ : ℝ => burnolQuotient (extendedMellinContinuation a d c (fourierUnitary f))
        ((2 : ℂ) + ((-τ : ℝ) : ℂ) * I) := by
    have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
    filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hnull] with τ hτ
    have hτ0 : τ ≠ 0 := by simpa using hτ
    exact burnolQuotient_reflect_line a c d f hτ0
  rw [integral_congr_ae hae]
  have hswap : (∫ τ : ℝ, burnolQuotient (extendedMellinContinuation a d c (fourierUnitary f))
      ((2 : ℂ) + ((-τ : ℝ) : ℂ) * I))
      = ∫ τ : ℝ, burnolQuotient (extendedMellinContinuation a d c (fourierUnitary f))
        ((2 : ℂ) + (τ : ℂ) * I) := by
    have h := integral_neg_eq_self
      (fun τ : ℝ => burnolQuotient (extendedMellinContinuation a d c (fourierUnitary f))
        ((2 : ℂ) + (τ : ℂ) * I)) volume
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    norm_num
  rw [hswap]
  exact hright

/-! ## Proposition 5.4 -/

/-- **Burnol's Proposition 5.4.**  The residue series of `M(f)/ζ` over the nontrivial zeros,
grouped by the selected heights, converges to `0`. -/
theorem exists_seq_tendsto_residueSum_quotient (ha : 1 ≤ a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f)) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧ (∀ k : ℕ, 1 ≤ T k) ∧
      Tendsto (fun n : ℕ => ∑ ρ ∈ nontrivialZeroFinset (T n),
          laurentCoeff (burnolQuotient (extendedMellinContinuation a c d f)) ρ (-1)) atTop
        (𝓝 0) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨T, hmono, htop, hT1, hspace, hTne, hzeta⟩ := exists_seq_zeta_inv_horizontal
  refine ⟨T, hmono, htop, hT1, ?_⟩
  obtain ⟨C, A, k₀, hC, hA, hbound⟩ := hzeta 2 (le_refl 2)
  set G : ℂ → ℂ := extendedMellinContinuation a c d f with hGdef
  -- the two horizontal edges
  have hposb : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -(2:ℝ) ≤ σ → σ ≤ 2 →
      ‖(riemannZeta ((σ : ℂ) + (((1 : ℝ) * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A := by
    intro k hk σ h1 h2
    simpa using hbound k hk σ h1 h2
  have hnegb : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -(2:ℝ) ≤ σ → σ ≤ 2 →
      ‖(riemannZeta ((σ : ℂ) + (((-1 : ℝ) * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A := by
    intro k hk σ h1 h2
    have h := hbound k hk σ h1 h2
    rw [show ((-1 : ℝ) * T k) = -(T k) by ring, norm_zeta_inv_neg_height]
    exact h
  have hH2 : Tendsto (fun k : ℕ => HIntegral (burnolQuotient G) (-1) 2 (T k)) atTop (𝓝 0) := by
    have h := tendsto_hIntegral_burnolQuotient (G := G) hrapid htop hT1 hC hA (le_refl 2)
      (by norm_num : |(1:ℝ)| = 1) hposb (x₁ := (-1:ℝ)) (x₂ := (2:ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine Tendsto.congr (fun k => ?_) h
    rw [one_mul]
  have hH1 : Tendsto (fun k : ℕ => HIntegral (burnolQuotient G) (-1) 2 (-T k)) atTop (𝓝 0) := by
    have h := tendsto_hIntegral_burnolQuotient (G := G) hrapid htop hT1 hC hA (le_refl 2)
      (by norm_num : |(-1:ℝ)| = 1) hnegb (x₁ := (-1:ℝ)) (x₂ := (2:ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine Tendsto.congr (fun k => ?_) h
    rw [neg_one_mul]
  -- the two vertical edges
  have hint2 : Integrable (fun τ : ℝ =>
      burnolQuotient G (((2 : ℝ) : ℂ) + (τ : ℂ) * I)) volume := by
    rw [hGdef]
    have h := integrable_burnolQuotient_two ha0 hev hc hd hrapid
    simpa using h
  have hint1 : Integrable (fun τ : ℝ =>
      burnolQuotient G (((-1 : ℝ) : ℂ) + (τ : ℂ) * I)) volume := by
    rw [hGdef]
    have h := integrable_burnolQuotient_neg_one ha hev hc hd hrapid
    simpa using h
  have hV2 := tendsto_vIntegral_of_integrable hint2 htop
  have hV1 := tendsto_vIntegral_of_integrable hint1 htop
  have hzero2 : (∫ τ : ℝ, burnolQuotient G (((2 : ℝ) : ℂ) + (τ : ℂ) * I)) = 0 := by
    rw [hGdef]
    have h := integral_extendedMellin_zeta_inv_two_eq_zero ha hev hc hd hrapid
    simpa [burnolQuotient] using h
  have hzero1 : (∫ τ : ℝ, burnolQuotient G (((-1 : ℝ) : ℂ) + (τ : ℂ) * I)) = 0 := by
    rw [hGdef]
    have h := integral_burnolQuotient_neg_one_eq_zero ha hev hc hd hrapid
    simpa using h
  -- the rectangle
  have hrect : ∀ n : ℕ, RectangleIntegral (burnolQuotient G)
      ((-1 : ℂ) + ((-T n : ℝ) : ℂ) * I) ((2 : ℂ) + ((T n : ℝ) : ℂ) * I)
      = HIntegral (burnolQuotient G) (-1) 2 (-T n) - HIntegral (burnolQuotient G) (-1) 2 (T n)
        + VIntegral (burnolQuotient G) 2 (-T n) (T n)
        - VIntegral (burnolQuotient G) (-1) (-T n) (T n) := by
    intro n
    rw [RectangleIntegral]
    congr 1 <;> simp
  have hlim : Tendsto (fun n : ℕ => RectangleIntegral (burnolQuotient G)
      ((-1 : ℂ) + ((-T n : ℝ) : ℂ) * I) ((2 : ℂ) + ((T n : ℝ) : ℂ) * I)) atTop
      (𝓝 (0 - 0 + I • (∫ τ : ℝ, burnolQuotient G (((2 : ℝ) : ℂ) + (τ : ℂ) * I))
        - I • ∫ τ : ℝ, burnolQuotient G (((-1 : ℝ) : ℂ) + (τ : ℂ) * I))) := by
    refine Tendsto.congr (fun n => (hrect n).symm) (((hH1.sub hH2).add hV2).sub hV1)
  rw [hzero1, hzero2] at hlim
  have hlim' : Tendsto (fun n : ℕ => RectangleIntegral' (burnolQuotient G)
      ((-1 : ℂ) + ((-T n : ℝ) : ℂ) * I) ((2 : ℂ) + ((T n : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    have h := hlim.const_smul (1 / (2 * (Real.pi : ℂ) * I))
    simpa using h
  refine hlim'.congr fun n => ?_
  have hTn : (0 : ℝ) < T n := lt_of_lt_of_le zero_lt_one (hT1 n)
  rw [hGdef]
  exact rectangleIntegral'_burnolQuotient_extendedMellin ha0 hev hc hd hTn
    (riemannZeta_ne_zero_of_abs_im_ne hTn (hTne n))

end

end RHTower
