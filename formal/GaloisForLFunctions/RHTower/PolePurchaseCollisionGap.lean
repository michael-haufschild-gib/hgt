import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.RHTower.Sieve.CoefficientFreeCap

/-!
# The collision gap and its price

The corpus's cap laws say that a bound depending on a completely multiplicative sequence only
through its moduli can never certify a gap between a unimodular sequence and the constant sequence.
The gap nevertheless exists.  The functional

`Φ_σ(g) = (σ − 1) ‖∑ g(n) n^{-σ}‖`

separates the Liouville sequence from the constant sequence: `Φ_σ(1) → 1` because `ζ` has a simple
pole at `1` with residue `1`, while `Φ_σ(λ) → 0` because `∑ λ(n)n^{-σ} = ζ(2σ)/ζ(σ)` and the same
pole now sits in the denominator.  The two sequences are modulus-collided — `‖λ(n)‖ = ‖1‖` for every
`n ≥ 1` — so no modulus-only majorant sees the gap.  What `Φ` consumes is exactly one invariant
beyond the moduli: the pole of the Dirichlet series at `σ = 1`.

The `t ≠ 0` extension of the same purchase is de la Vallée Poussin's coupled positivity, whose
positive input is the trigonometric inequality `3 + 4cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0` and whose
purchasing power is again the pole.
-/

open ArithmeticFunction Filter Topology Complex

namespace RHTower

/-! ## The pole functional -/

/-- The pole functional at the constant sequence. -/
noncomputable def poleFunctionalZeta (σ : ℝ) : ℝ := (σ - 1) * ‖riemannZeta (σ : ℂ)‖

/-- The pole functional at the Liouville sequence. -/
noncomputable def poleFunctionalLiouville (σ : ℝ) : ℝ :=
  (σ - 1) * ‖LSeries (fun n => liouvilleC n) (σ : ℂ)‖

/-- On the half-plane of absolute convergence the constant sequence's functional is the one the
card writes as `Φ_σ(1)`. -/
theorem poleFunctionalZeta_eq_lseries {σ : ℝ} (hσ : 1 < σ) :
    poleFunctionalZeta σ = (σ - 1) * ‖LSeries 1 (σ : ℂ)‖ := by
  rw [poleFunctionalZeta, LSeries_one_eq_riemannZeta (by simpa using hσ)]

private theorem tendsto_ofReal_nhdsGT_one_ne :
    Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hcont : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (((1 : ℝ) : ℂ))) :=
      (Complex.continuous_ofReal.tendsto 1)
    have h2 : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (((1 : ℝ) : ℂ))) :=
      hcont.mono_left nhdsWithin_le_nhds
    simpa using h2
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have hr : σ = 1 := by exact_mod_cast h
    exact absurd hr (ne_of_gt hσ)

/-- **The constant sequence's pole functional tends to one.**  This is the simple pole of `ζ`. -/
theorem tendsto_poleFunctionalZeta :
    Tendsto poleFunctionalZeta (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have h := riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_one_ne
  have hnorm : Tendsto (fun σ : ℝ => ‖((σ : ℂ) - 1) * riemannZeta (σ : ℂ)‖)
      (𝓝[>] (1 : ℝ)) (𝓝 1) := by
    have := h.norm
    simpa [Function.comp] using this
  refine hnorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [Set.mem_Ioi] at hσ
  rw [poleFunctionalZeta, norm_mul]
  congr 1
  rw [show ((σ : ℂ) - 1) = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith)]

theorem tendsto_norm_riemannZeta_two_mul :
    Tendsto (fun σ : ℝ => ‖riemannZeta (2 * (σ : ℂ))‖) (𝓝[>] (1 : ℝ)) (𝓝 ‖riemannZeta 2‖) := by
  have hmap : Tendsto (fun σ : ℝ => 2 * (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (2 : ℂ)) := by
    have : Tendsto (fun σ : ℝ => 2 * (σ : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (2 * ((1 : ℝ) : ℂ))) :=
      (Complex.continuous_ofReal.tendsto 1).const_mul 2
    simpa using this
  have hzeta : ContinuousAt riemannZeta 2 :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have := (hzeta.tendsto.comp hmap).norm
  exact this.mono_left nhdsWithin_le_nhds

/-- **The Liouville sequence's pole functional tends to zero.**  The pole of `ζ` now sits in the
denominator of `∑ λ(n)n^{-σ} = ζ(2σ)/ζ(σ)`. -/
theorem tendsto_poleFunctionalLiouville :
    Tendsto poleFunctionalLiouville (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hsq : Tendsto (fun σ : ℝ => (σ - 1) ^ (2 : ℕ)) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun σ : ℝ => (σ - 1) ^ (2 : ℕ)) :=
      (continuous_id.sub continuous_const).pow 2
    have h0 : Tendsto (fun σ : ℝ => (σ - 1) ^ (2 : ℕ)) (𝓝[>] (1 : ℝ)) (𝓝 ((1 - 1 : ℝ) ^ (2 : ℕ))) :=
      (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa using h0
  have hnum : Tendsto (fun σ : ℝ => (σ - 1) ^ (2 : ℕ) * ‖riemannZeta (2 * (σ : ℂ))‖)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have := hsq.mul tendsto_norm_riemannZeta_two_mul
    simpa using this
  have hquot := hnum.div tendsto_poleFunctionalZeta one_ne_zero
  rw [zero_div] at hquot
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [Set.mem_Ioi] at hσ
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hzne : riemannZeta (σ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hre)
  have hznorm : ‖riemannZeta (σ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hzne
  have hs1 : (σ : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hσ)
  have hid := LSeries_liouvilleC_mul_riemannZeta hre
  have hnorms : ‖LSeries (fun n => liouvilleC n) (σ : ℂ)‖ * ‖riemannZeta (σ : ℂ)‖
      = ‖riemannZeta (2 * (σ : ℂ))‖ := by
    rw [← norm_mul, hid]
  simp only [Pi.div_apply, poleFunctionalZeta, poleFunctionalLiouville]
  rw [← hnorms]
  field_simp

/-! ## The certified modulus-collided gap -/

theorem norm_liouvilleC {n : ℕ} (hn : n ≠ 0) : ‖liouvilleC n‖ = 1 := by
  rw [liouvilleC_apply, ArithmeticFunction.liouville_apply hn]
  push_cast
  simp

/-- The Liouville sequence is modulus-collided with the constant sequence. -/
theorem norm_liouvilleC_eq_norm_one {n : ℕ} (hn : n ≠ 0) :
    ‖liouvilleC n‖ = ‖(1 : ℕ → ℂ) n‖ := by
  rw [norm_liouvilleC hn]
  simp

/-- **The collision gap is real.**  Below some aperture the pole functional strictly separates the
Liouville sequence from the constant sequence, even though the two are modulus-collided. -/
theorem exists_collision_gap :
    ∃ σ₀ : ℝ, 1 < σ₀ ∧ ∀ σ : ℝ, 1 < σ → σ < σ₀ →
      poleFunctionalLiouville σ < poleFunctionalZeta σ := by
  have hL := tendsto_poleFunctionalLiouville.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hZ := tendsto_poleFunctionalZeta.eventually
    (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  obtain ⟨u, huGT, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hL.and hZ)
  refine ⟨u, huGT, fun σ hσ1 hσu => ?_⟩
  obtain ⟨h1, h2⟩ := hu ⟨hσ1, hσu⟩
  linarith

/-- **The strengthened cap is false.**  There is an aperture at which the pole functional certifies
a gap between two modulus-collided completely multiplicative sequences.  So no cap of the form "no
functional separates a modulus-collided pair" can hold: the escape invariant is the pole. -/
theorem exists_modulusCollided_gap :
    ∃ σ : ℝ, 1 < σ ∧ (∀ n : ℕ, n ≠ 0 → ‖liouvilleC n‖ = ‖(1 : ℕ → ℂ) n‖)
      ∧ poleFunctionalLiouville σ < poleFunctionalZeta σ := by
  obtain ⟨σ₀, hσ₀, hgap⟩ := exists_collision_gap
  refine ⟨(1 + σ₀) / 2, by linarith, fun n hn => norm_liouvilleC_eq_norm_one hn, ?_⟩
  exact hgap _ (by linarith) (by linarith)

/-! ## The coupled purchase at nonzero height -/

/-- **The de la Vallée Poussin positivity.**  `3 + 4cos θ + cos 2θ = 2(1 + cos θ)²`. -/
theorem vallee_poussin_identity (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ (2 : ℕ) := by
  rw [Real.cos_two_mul]
  ring

/-- The source cone's positive input at nonzero height. -/
theorem vallee_poussin_nonneg (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [vallee_poussin_identity]
  positivity

/-- **No zero on the line `Re s = 1`.**  The conclusion the coupled purchase buys. -/
theorem riemannZeta_ne_zero_one_add_I_mul (t : ℝ) :
    riemannZeta (1 + (t : ℂ) * Complex.I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp

end RHTower
