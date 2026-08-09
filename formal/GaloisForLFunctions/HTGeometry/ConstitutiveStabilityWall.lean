import Mathlib

/-!
# A₂ law-stability wall and positive chamber erasure

The quiver `1 → 2` over `ℂ` has the nonsplit extension `E = (ℂ →id ℂ)` of `S₁ = (ℂ,0)` by
`S₂ = (0,ℂ)`.  Its subrepresentations are pairs of subspaces `U₁ ≤ U₂` of `ℂ`, so `E` has exactly
one nonzero proper subobject, namely `S₂`, and stability of `E` for a central charge with
`z₁ = Z(S₁)`, `z₂ = Z(S₂)` in the open upper half-plane is exactly `arg z₂ < arg (z₁ + z₂)`.

* `subrep_classification` — the three subrepresentations of `E`;
* `arg_lt_arg_iff_cross_pos` — in the open upper half-plane the phase order is the sign of the
  cross product, so `stability_iff` gives `E` stable `↔ arg z₂ < arg z₁`, and
  `arg_eq_of_arg_eq` gives strict semistability on the wall;
* `wallFamily_stable_iff_pos` and `wallFamily_modulus_packet` — on the explicit family
  `z₁ = exp(i(π/2+θ))`, `z₂ = exp(i(π/2−θ))` the law is stable exactly for `θ > 0`, while the
  modulus packet `(|z₁|, |z₂|, |z₁+z₂|) = (1, 1, 2|cos θ|)` is the same at `θ` and `−θ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

section Subobjects

/-- **The subrepresentations of the nonsplit extension.**  A subrepresentation of `(ℂ →id ℂ)` is a
pair of subspaces with `U₁ ≤ U₂`, and there are exactly three. -/
theorem subrep_classification (U₁ U₂ : Submodule ℂ ℂ) (h : U₁ ≤ U₂) :
    (U₁ = ⊥ ∧ U₂ = ⊥) ∨ (U₁ = ⊥ ∧ U₂ = ⊤) ∨ (U₁ = ⊤ ∧ U₂ = ⊤) := by
  rcases Ideal.eq_bot_or_top U₁ with h1 | h1 <;> rcases Ideal.eq_bot_or_top U₂ with h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exfalso
    rw [h1, h2] at h
    have : (1 : ℂ) ∈ (⊥ : Submodule ℂ ℂ) := h Submodule.mem_top
    rw [Submodule.mem_bot] at this
    exact one_ne_zero this
  · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- The unique nonzero proper subrepresentation is `S₂ = (0, ℂ)`. -/
theorem subrep_proper_nonzero (U₁ U₂ : Submodule ℂ ℂ) (h : U₁ ≤ U₂)
    (hne : ¬ (U₁ = ⊥ ∧ U₂ = ⊥)) (hnt : ¬ (U₁ = ⊤ ∧ U₂ = ⊤)) :
    U₁ = ⊥ ∧ U₂ = ⊤ := by
  rcases subrep_classification U₁ U₂ h with h' | h' | h'
  · exact absurd h' hne
  · exact h'
  · exact absurd h' hnt

end Subobjects

section PhaseOrder

theorem arg_pos_of_im_pos {t : ℂ} (h : 0 < t.im) : 0 < t.arg := by
  have h1 : 0 ≤ t.arg := Complex.arg_nonneg_iff.mpr h.le
  rcases lt_or_eq_of_le h1 with h2 | h2
  · exact h2
  · exfalso
    have h3 := Complex.arg_eq_zero_iff.mp h2.symm
    exact absurd h3.2 (ne_of_gt h)

theorem arg_lt_pi_of_im_pos {t : ℂ} (h : 0 < t.im) : t.arg < Real.pi :=
  Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt h))

theorem im_ne_zero_of_im_pos {t : ℂ} (h : 0 < t.im) : t ≠ 0 := by
  intro hcon
  rw [hcon] at h
  simp at h

theorem arg_div_eq_sub {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    (z / w).arg = z.arg - w.arg := by
  have hz0 : z ≠ 0 := im_ne_zero_of_im_pos hz
  have hw0 : w ≠ 0 := im_ne_zero_of_im_pos hw
  have hzp : 0 < z.arg := arg_pos_of_im_pos hz
  have hzp' : z.arg < Real.pi := arg_lt_pi_of_im_pos hz
  have hwp : 0 < w.arg := arg_pos_of_im_pos hw
  have hwp' : w.arg < Real.pi := arg_lt_pi_of_im_pos hw
  have hinv : (w⁻¹).arg = -w.arg := by
    rw [Complex.arg_inv, if_neg (ne_of_lt hwp')]
  rw [div_eq_mul_inv]
  rw [(Complex.arg_mul_eq_add_arg_iff hz0 (inv_ne_zero hw0)).mpr ?_, hinv]
  · ring
  · rw [hinv]
    constructor
    · linarith
    · linarith

/-- **The phase order in the upper half-plane is the sign of the cross product.** -/
theorem arg_lt_arg_iff_cross_pos {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    w.arg < z.arg ↔ 0 < (z * (starRingEnd ℂ) w).im := by
  have hw0 : w ≠ 0 := im_ne_zero_of_im_pos hw
  have hnormsq : (0 : ℝ) < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have hdivim : (z / w).im = (z * (starRingEnd ℂ) w).im / Complex.normSq w := by
    rw [Complex.div_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    field_simp
    ring
  have hsub : (z / w).arg = z.arg - w.arg := arg_div_eq_sub hz hw
  constructor
  · intro hlt
    have hargpos : 0 < (z / w).arg := by rw [hsub]; linarith
    have him : 0 ≤ (z / w).im := Complex.arg_nonneg_iff.mp hargpos.le
    have hne : (z / w).im ≠ 0 := by
      intro hzero
      have hargz : (z / w).arg = 0 ∨ (z / w).arg = Real.pi := by
        rcases lt_trichotomy (z / w).re 0 with hre | hre | hre
        · right
          exact Complex.arg_eq_pi_iff.mpr ⟨hre, hzero⟩
        · exfalso
          have hz0 : z / w = 0 := by
            apply Complex.ext <;> simp [hre, hzero]
          rw [hz0] at hargpos
          simp at hargpos
        · left
          exact Complex.arg_eq_zero_iff.mpr ⟨hre.le, hzero⟩
      rcases hargz with h | h
      · rw [h] at hargpos; exact lt_irrefl 0 hargpos
      · have hzp' : z.arg < Real.pi := arg_lt_pi_of_im_pos hz
        have hwp : 0 < w.arg := arg_pos_of_im_pos hw
        rw [hsub] at h
        linarith
    have hpos : 0 < (z / w).im := lt_of_le_of_ne him (Ne.symm hne)
    rw [hdivim] at hpos
    exact (div_pos_iff.mp hpos).resolve_right (fun h => absurd h.2 (not_lt.mpr hnormsq.le))
      |>.1
  · intro hcross
    have hpos : 0 < (z / w).im := by
      rw [hdivim]
      exact div_pos hcross hnormsq
    have hargpos : 0 < (z / w).arg := arg_pos_of_im_pos hpos
    rw [hsub] at hargpos
    linarith

end PhaseOrder

section StabilityWall

/-- **Stability of the extension is the phase order of the two simples.**  `E` is stable exactly
when the unique nonzero proper subobject `S₂` has strictly smaller phase, and that happens exactly
when `arg z₂ < arg z₁`. -/
theorem stability_iff {z₁ z₂ : ℂ} (h₁ : 0 < z₁.im) (h₂ : 0 < z₂.im) :
    z₂.arg < (z₁ + z₂).arg ↔ z₂.arg < z₁.arg := by
  have hsum : 0 < (z₁ + z₂).im := by
    rw [Complex.add_im]
    linarith
  rw [arg_lt_arg_iff_cross_pos hsum h₂, arg_lt_arg_iff_cross_pos h₁ h₂]
  have hexp : ((z₁ + z₂) * (starRingEnd ℂ) z₂).im
      = (z₁ * (starRingEnd ℂ) z₂).im + (z₂ * (starRingEnd ℂ) z₂).im := by
    rw [add_mul, Complex.add_im]
  have hself : (z₂ * (starRingEnd ℂ) z₂).im = 0 := by
    rw [Complex.mul_conj]
    simp
  rw [hexp, hself, add_zero]

/-- **On the wall the extension is strictly semistable.** -/
theorem arg_eq_of_arg_eq {z₁ z₂ : ℂ} (h₁ : 0 < z₁.im) (h₂ : 0 < z₂.im) (heq : z₁.arg = z₂.arg) :
    (z₁ + z₂).arg = z₂.arg := by
  have hsum : 0 < (z₁ + z₂).im := by
    rw [Complex.add_im]
    linarith
  have hnot1 : ¬ z₂.arg < (z₁ + z₂).arg := by
    rw [stability_iff h₁ h₂, heq]
    exact lt_irrefl _
  have hnot2 : ¬ (z₁ + z₂).arg < z₂.arg := by
    rw [arg_lt_arg_iff_cross_pos h₂ hsum]
    intro hcon
    have hexp : (z₂ * (starRingEnd ℂ) (z₁ + z₂)).im
        = (z₂ * (starRingEnd ℂ) z₁).im + (z₂ * (starRingEnd ℂ) z₂).im := by
      rw [map_add, mul_add, Complex.add_im]
    have hself : (z₂ * (starRingEnd ℂ) z₂).im = 0 := by
      rw [Complex.mul_conj]
      simp
    rw [hexp, hself, add_zero] at hcon
    have hlt : z₁.arg < z₂.arg := (arg_lt_arg_iff_cross_pos h₂ h₁).mpr hcon
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  linarith [lt_trichotomy z₂.arg (z₁ + z₂).arg]

end StabilityWall

section ChamberErasure

/-- The explicit wall family of central charges. -/
noncomputable def wallCharge₁ (θ : ℝ) : ℂ := Complex.exp (((Real.pi / 2 + θ : ℝ) : ℂ) * Complex.I)

/-- The second charge of the wall family. -/
noncomputable def wallCharge₂ (θ : ℝ) : ℂ := Complex.exp (((Real.pi / 2 - θ : ℝ) : ℂ) * Complex.I)

theorem wallCharge₁_im (θ : ℝ) : (wallCharge₁ θ).im = Real.cos θ := by
  rw [wallCharge₁, Complex.exp_ofReal_mul_I_im]
  simp [Real.sin_add]

theorem wallCharge₂_im (θ : ℝ) : (wallCharge₂ θ).im = Real.cos θ := by
  rw [wallCharge₂, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two_sub]

theorem wallCharge_im_pos {θ : ℝ} (h : |θ| < Real.pi / 2) :
    0 < (wallCharge₁ θ).im ∧ 0 < (wallCharge₂ θ).im := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by
    have := abs_lt.mp h
    linarith [this.1], (abs_lt.mp h).2⟩
  exact ⟨by rw [wallCharge₁_im]; exact hcos, by rw [wallCharge₂_im]; exact hcos⟩

theorem wallCharge_cross (θ : ℝ) :
    (wallCharge₁ θ * (starRingEnd ℂ) (wallCharge₂ θ)).im = Real.sin (2 * θ) := by
  rw [wallCharge₁, wallCharge₂, ← Complex.exp_conj, ← Complex.exp_add]
  have hc : (starRingEnd ℂ) (((Real.pi / 2 - θ : ℝ) : ℂ) * Complex.I)
      = -(((Real.pi / 2 - θ : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc]
  have hsum : ((Real.pi / 2 + θ : ℝ) : ℂ) * Complex.I + -(((Real.pi / 2 - θ : ℝ) : ℂ) * Complex.I)
      = ((2 * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsum, Complex.exp_ofReal_mul_I_im]

/-- **The wall family is stable exactly on the positive side.** -/
theorem wallFamily_stable_iff_pos {θ : ℝ} (h : |θ| < Real.pi / 2) :
    ((wallCharge₂ θ).arg < (wallCharge₁ θ + wallCharge₂ θ).arg) ↔ 0 < θ := by
  obtain ⟨h₁, h₂⟩ := wallCharge_im_pos h
  rw [stability_iff h₁ h₂, arg_lt_arg_iff_cross_pos h₁ h₂, wallCharge_cross]
  constructor
  · intro hsin
    by_contra hcon
    rw [not_lt] at hcon
    have hle : Real.sin (2 * θ) ≤ 0 := by
      rcases lt_or_eq_of_le hcon with hlt | heq
      · have hb := abs_lt.mp h
        exact le_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith))
      · rw [heq]
        simp
    linarith
  · intro hpos
    have hb := abs_lt.mp h
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

theorem wallCharge_sum (θ : ℝ) :
    wallCharge₁ θ + wallCharge₂ θ = (2 * Real.cos θ : ℝ) * Complex.I := by
  rw [wallCharge₁, wallCharge₂]
  have h1 : ((Real.pi / 2 + θ : ℝ) : ℂ) * Complex.I
      = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I + (θ : ℂ) * Complex.I := by
    push_cast; ring
  have h2 : ((Real.pi / 2 - θ : ℝ) : ℂ) * Complex.I
      = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I + (-(θ : ℂ)) * Complex.I := by
    push_cast; ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add, ← mul_add]
  have hI : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I]
    push_cast
    simp
  have hcos : Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp ((-(θ : ℂ)) * Complex.I)
      = 2 * Complex.cos (θ : ℂ) := by
    rw [Complex.cos]
    ring_nf
  rw [hI, hcos]
  push_cast
  ring

/-- **The modulus packet cannot see the chamber.**  It is the same at `θ` and `−θ`. -/
theorem wallFamily_modulus_packet (θ : ℝ) :
    ‖wallCharge₁ θ‖ = 1 ∧ ‖wallCharge₂ θ‖ = 1 ∧
      ‖wallCharge₁ θ + wallCharge₂ θ‖ = 2 * |Real.cos θ| := by
  refine ⟨?_, ?_, ?_⟩
  · rw [wallCharge₁, Complex.norm_exp_ofReal_mul_I]
  · rw [wallCharge₂, Complex.norm_exp_ofReal_mul_I]
  · rw [wallCharge_sum, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    norm_num

theorem wallFamily_modulus_packet_symm (θ : ℝ) :
    (‖wallCharge₁ θ‖, ‖wallCharge₂ θ‖, ‖wallCharge₁ θ + wallCharge₂ θ‖)
      = (‖wallCharge₁ (-θ)‖, ‖wallCharge₂ (-θ)‖, ‖wallCharge₁ (-θ) + wallCharge₂ (-θ)‖) := by
  obtain ⟨a1, a2, a3⟩ := wallFamily_modulus_packet θ
  obtain ⟨b1, b2, b3⟩ := wallFamily_modulus_packet (-θ)
  rw [a1, a2, a3, b1, b2, b3, Real.cos_neg]

/-- **Positivity identifies opposite law chambers.**  The wall family is stable at `θ > 0` and
unstable at `−θ`, while the three positive moduli agree. -/
theorem positive_chamber_erasure {θ : ℝ} (h : |θ| < Real.pi / 2) (hpos : 0 < θ) :
    ((wallCharge₂ θ).arg < (wallCharge₁ θ + wallCharge₂ θ).arg) ∧
      ¬ ((wallCharge₂ (-θ)).arg < (wallCharge₁ (-θ) + wallCharge₂ (-θ)).arg) ∧
      (‖wallCharge₁ θ‖, ‖wallCharge₂ θ‖, ‖wallCharge₁ θ + wallCharge₂ θ‖)
        = (‖wallCharge₁ (-θ)‖, ‖wallCharge₂ (-θ)‖, ‖wallCharge₁ (-θ) + wallCharge₂ (-θ)‖) := by
  have hneg : |(-θ)| < Real.pi / 2 := by rwa [abs_neg]
  refine ⟨(wallFamily_stable_iff_pos h).mpr hpos, ?_, wallFamily_modulus_packet_symm θ⟩
  rw [wallFamily_stable_iff_pos hneg]
  linarith

end ChamberErasure

end GaloisForLFunctions.HTGeometry
