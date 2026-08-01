import GaloisForLFunctions.HTGeometry.GammaJetRatioFamily

/-!
# The Gamma-jet datum and its residue are unique

A Gamma-field element on a vertical line is described by a datum — a power of `Γ`, a power of the
argument, a power of the vertical logarithm — together with the residue against that shape.  The
description is unique: two shapes whose ratio has a nonzero limit carry the same Gamma exponent, the
same logarithmic degree and the same argument degree, and the limit is then `1`.

The three-level dominance supplies both directions.  If the data differ, one of the two ratios
vanishes; but the two ratios multiply to `1`, so neither can vanish while the other has a nonzero
limit.

Consequently the residue of an element against its own shape is unique as well: this is the
uniqueness clause of the projective boundary law.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- The two shape ratios multiply to `1` on a vertical line. -/
theorem gammaJetShape_ratio_mul_symm (hσ : 0 < σ) (u₁ a₁ dP₁ b₁ u₂ a₂ dP₂ b₂ : ℕ) :
    (fun _ : ℝ => (1 : ℂ)) =ᶠ[atTop] fun t : ℝ =>
      (gammaJetShape σ u₁ a₁ dP₁ b₁ t / gammaJetShape σ u₂ a₂ dP₂ b₂ t)
        * (gammaJetShape σ u₂ a₂ dP₂ b₂ t / gammaJetShape σ u₁ a₁ dP₁ b₁ t) := by
  filter_upwards [eventually_gammaJetShape_ne_zero hσ u₁ a₁ dP₁ b₁,
    eventually_gammaJetShape_ne_zero hσ u₂ a₂ dP₂ b₂] with t h1 h2
  field_simp

/-- **Uniqueness of the Gamma-jet datum.**  If the ratio of two Gamma-jet shapes has a nonzero
limit, the two data agree at all three levels and the limit is `1`. -/
theorem gammaJetShape_datum_unique (hσ : 0 < σ) {u₁ a₁ dP₁ b₁ u₂ a₂ dP₂ b₂ : ℕ} {c : ℂ}
    (hc : c ≠ 0)
    (h : Tendsto (fun t : ℝ => gammaJetShape σ u₁ a₁ dP₁ b₁ t / gammaJetShape σ u₂ a₂ dP₂ b₂ t)
      atTop (nhds c)) :
    u₁ = u₂ ∧ a₁ = a₂ ∧ dP₁ + b₂ = dP₂ + b₁ ∧ c = 1 := by
  -- the forward ratio cannot vanish, since its limit is nonzero
  have hfwd : ¬ Tendsto (fun t : ℝ =>
      gammaJetShape σ u₁ a₁ dP₁ b₁ t / gammaJetShape σ u₂ a₂ dP₂ b₂ t) atTop (nhds 0) := by
    intro h0
    exact hc (tendsto_nhds_unique h h0)
  -- neither can the reverse ratio, since the two multiply to `1`
  have hrev : ¬ Tendsto (fun t : ℝ =>
      gammaJetShape σ u₂ a₂ dP₂ b₂ t / gammaJetShape σ u₁ a₁ dP₁ b₁ t) atTop (nhds 0) := by
    intro h0
    have hprod := h.mul h0
    rw [mul_zero] at hprod
    have hone : Tendsto (fun t : ℝ =>
        (gammaJetShape σ u₁ a₁ dP₁ b₁ t / gammaJetShape σ u₂ a₂ dP₂ b₂ t)
          * (gammaJetShape σ u₂ a₂ dP₂ b₂ t / gammaJetShape σ u₁ a₁ dP₁ b₁ t))
        atTop (nhds 1) :=
      tendsto_const_nhds.congr' (gammaJetShape_ratio_mul_symm hσ u₁ a₁ dP₁ b₁ u₂ a₂ dP₂ b₂)
    exact one_ne_zero (tendsto_nhds_unique hone hprod)
  rcases lt_trichotomy u₁ u₂ with hu | rfl | hu
  · exact absurd (tendsto_gammaJetShape_ratio_of_gamma_lt hσ hu) hrev
  · rcases lt_trichotomy (dP₁ + b₂) (dP₂ + b₁) with hd | hd | hd
    · exact absurd (tendsto_gammaJetShape_ratio_of_gamma_eq hσ
        (tendsto_polyJetShape_ratio_zero_of_deg hσ hd)) hfwd
    · rcases lt_trichotomy a₁ a₂ with ha | rfl | ha
      · exact absurd (tendsto_gammaJetShape_ratio_of_gamma_eq hσ
          (tendsto_polyJetShape_ratio_zero_of_log hσ hd ha)) hfwd
      · refine ⟨rfl, rfl, hd, ?_⟩
        exact tendsto_nhds_unique h (tendsto_gammaJetShape_ratio_of_gamma_eq hσ
          (tendsto_polyJetShape_ratio_one hσ hd rfl))
      · exact absurd (tendsto_gammaJetShape_ratio_of_gamma_eq hσ
          (tendsto_polyJetShape_ratio_zero_of_log hσ hd.symm ha)) hrev
    · exact absurd (tendsto_gammaJetShape_ratio_of_gamma_eq hσ
        (tendsto_polyJetShape_ratio_zero_of_deg hσ hd)) hrev
  · exact absurd (tendsto_gammaJetShape_ratio_of_gamma_lt hσ hu) hfwd

/-- **Uniqueness of the datum and the residue of an element.**  A function on a vertical line
determines its Gamma-jet datum and its residue: two presentations with nonzero residues agree. -/
theorem gammaJet_datum_residue_unique (hσ : 0 < σ) {F : ℝ → ℂ} {u₁ a₁ dP₁ b₁ u₂ a₂ dP₂ b₂ : ℕ}
    {c₁ c₂ : ℂ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (h₁ : Tendsto (fun t : ℝ => F t / gammaJetShape σ u₁ a₁ dP₁ b₁ t) atTop (nhds c₁))
    (h₂ : Tendsto (fun t : ℝ => F t / gammaJetShape σ u₂ a₂ dP₂ b₂ t) atTop (nhds c₂)) :
    u₁ = u₂ ∧ a₁ = a₂ ∧ dP₁ + b₂ = dP₂ + b₁ ∧ c₁ = c₂ := by
  have hFne : ∀ᶠ t : ℝ in atTop, F t / gammaJetShape σ u₁ a₁ dP₁ b₁ t ≠ 0 :=
    h₁.eventually (eventually_ne_nhds hc₁)
  have hratio : Tendsto (fun t : ℝ =>
      gammaJetShape σ u₁ a₁ dP₁ b₁ t / gammaJetShape σ u₂ a₂ dP₂ b₂ t) atTop (nhds (c₂ / c₁)) := by
    refine (h₂.div h₁ hc₁).congr' ?_
    filter_upwards [hFne, eventually_gammaJetShape_ne_zero hσ u₁ a₁ dP₁ b₁,
      eventually_gammaJetShape_ne_zero hσ u₂ a₂ dP₂ b₂] with t hF h1 h2
    have hFt : F t ≠ 0 := by
      intro hzero
      exact hF (by rw [hzero, zero_div])
    show (F t / gammaJetShape σ u₂ a₂ dP₂ b₂ t) / (F t / gammaJetShape σ u₁ a₁ dP₁ b₁ t)
      = gammaJetShape σ u₁ a₁ dP₁ b₁ t / gammaJetShape σ u₂ a₂ dP₂ b₂ t
    field_simp
  obtain ⟨hu, ha, hd, hone⟩ := gammaJetShape_datum_unique hσ (div_ne_zero hc₂ hc₁) hratio
  exact ⟨hu, ha, hd, ((div_eq_one_iff_eq hc₁).mp hone).symm⟩

/-- A trivial Gamma exponent leaves the jet shape of the coefficient. -/
theorem gammaJetShape_gamma_zero (σ : ℝ) (a dP b : ℕ) (t : ℝ) :
    gammaJetShape σ 0 a dP b t = polyJetShape σ a dP b t := by
  rw [gammaJetShape, pow_zero, one_mul]

/-- **Uniqueness of the digamma-field datum.**  Inside the digamma field the Gamma exponent is
`0`, and the remaining two levels of the datum — the argument degree and the logarithmic degree —
are determined, with limit `1`. -/
theorem polyJetShape_datum_unique (hσ : 0 < σ) {a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ} {c : ℂ} (hc : c ≠ 0)
    (h : Tendsto (fun t : ℝ => polyJetShape σ a₁ dP₁ b₁ t / polyJetShape σ a₂ dP₂ b₂ t)
      atTop (nhds c)) :
    a₁ = a₂ ∧ dP₁ + b₂ = dP₂ + b₁ ∧ c = 1 := by
  have h' : Tendsto (fun t : ℝ =>
      gammaJetShape σ 0 a₁ dP₁ b₁ t / gammaJetShape σ 0 a₂ dP₂ b₂ t) atTop (nhds c) := by
    refine h.congr fun t => ?_
    rw [gammaJetShape_gamma_zero, gammaJetShape_gamma_zero]
  obtain ⟨-, ha, hd, hone⟩ := gammaJetShape_datum_unique hσ hc h'
  exact ⟨ha, hd, hone⟩

/-- **Uniqueness of the datum and the residue in the digamma field.**  This is the uniqueness
clause of the algebraic-logarithmic residue law. -/
theorem polyJet_datum_residue_unique (hσ : 0 < σ) {A : ℝ → ℂ} {a₁ dP₁ b₁ a₂ dP₂ b₂ : ℕ}
    {c₁ c₂ : ℂ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (h₁ : Tendsto (fun t : ℝ => A t / polyJetShape σ a₁ dP₁ b₁ t) atTop (nhds c₁))
    (h₂ : Tendsto (fun t : ℝ => A t / polyJetShape σ a₂ dP₂ b₂ t) atTop (nhds c₂)) :
    a₁ = a₂ ∧ dP₁ + b₂ = dP₂ + b₁ ∧ c₁ = c₂ := by
  have h₁' : Tendsto (fun t : ℝ => A t / gammaJetShape σ 0 a₁ dP₁ b₁ t) atTop (nhds c₁) := by
    refine h₁.congr fun t => ?_
    rw [gammaJetShape_gamma_zero]
  have h₂' : Tendsto (fun t : ℝ => A t / gammaJetShape σ 0 a₂ dP₂ b₂ t) atTop (nhds c₂) := by
    refine h₂.congr fun t => ?_
    rw [gammaJetShape_gamma_zero]
  obtain ⟨-, ha, hd, hcc⟩ := gammaJet_datum_residue_unique hσ hc₁ hc₂ h₁' h₂'
  exact ⟨ha, hd, hcc⟩

end GaloisForLFunctions
