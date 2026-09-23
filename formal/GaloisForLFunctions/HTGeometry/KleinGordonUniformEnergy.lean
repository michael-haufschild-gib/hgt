import GaloisForLFunctions.HTGeometry.KleinGordonExactConservation

/-!
# A real potential removes the exponential

The estimate for a general bounded perturbation grows like `e^{2‖W‖|t|}`, and the ill-posedness
witness shows the exponential is not an artefact of the proof — for a general `W` the energy really
can grow. For a **self-adjoint** perturbation it cannot: exact conservation turns the differential
inequality into an algebraic one, and the energy is bounded uniformly in time.

Two forms. If the potential is small, `‖W‖ = b < 1`, the potential term is at most `b` times the
energy itself, so conservation gives

`‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖² ≤ (1+b)/(1−b) · (‖⟨D⟩u(0)‖² + ‖∂ₜu(0)‖²)`

for **every** time — no growth at all, only a fixed loss. If instead the potential is confining,
`re⟪Wx,x⟫ ≤ 0`, no smallness is needed: the potential term has the right sign and the energy is
bounded by its initial value outright.

The mechanism in both cases is that `‖u‖ ≤ ‖⟨D⟩u‖`, so the potential term is controlled by the very
quantity it is being subtracted from. That is the operator form of the mass gap: the frequency is
bounded below by one.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Uniform

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The potential term is controlled by the norm of the perturbation. -/
theorem abs_re_inner_potential_le (hW : ‖W‖ ≤ b) (x : Lp ℂ 2 (volume : Measure E)) :
    |RCLike.re (inner ℂ (W x) x : ℂ)| ≤ b * ‖x‖ ^ (2 : ℕ) := by
  have h1 : |RCLike.re (inner ℂ (W x) x : ℂ)| ≤ ‖(inner ℂ (W x) x : ℂ)‖ :=
    RCLike.abs_re_le_norm _
  have h2 : ‖(inner ℂ (W x) x : ℂ)‖ ≤ ‖W x‖ * ‖x‖ := norm_inner_le_norm _ _
  have h3 : ‖W x‖ ≤ b * ‖x‖ := W.le_of_opNorm_le hW x
  have h4 : ‖W x‖ * ‖x‖ ≤ b * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg x)
  calc |RCLike.re (inner ℂ (W x) x : ℂ)| ≤ ‖(inner ℂ (W x) x : ℂ)‖ := h1
    _ ≤ ‖W x‖ * ‖x‖ := h2
    _ ≤ b * ‖x‖ * ‖x‖ := h4
    _ = b * ‖x‖ ^ (2 : ℕ) := by ring

/-- **The field is bounded by the energy**: the operator form of the mass gap. -/
theorem norm_kgFieldMild_sq_le_energy (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W (kgFreqInvOp g) h t‖ ^ (2 : ℕ)
      ≤ ‖kgFieldGrad W g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W g h t‖ ^ (2 : ℕ) := by
  have hu : kgFieldMild W (kgFreqInvOp g) h t = kgFreqInvOp (kgFieldGrad W g h t) :=
    (kgFreqInvOp_kgFieldGrad hb0 hW g h t).symm
  have hle : ‖kgFieldMild W (kgFreqInvOp g) h t‖ ≤ ‖kgFieldGrad W g h t‖ := by
    rw [hu]
    have hc := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le (kgFieldGrad W g h t)
    rwa [one_mul] at hc
  have hsq : ‖kgFieldMild W (kgFreqInvOp g) h t‖ ^ (2 : ℕ) ≤ ‖kgFieldGrad W g h t‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hvel : (0 : ℝ) ≤ ‖kgFieldVel W g h t‖ ^ (2 : ℕ) := sq_nonneg _
  linarith

/-- **A small real potential gives an energy bounded uniformly in time.** The exponential of the
general estimate disappears completely: what is left is a fixed loss `(1+b)/(1−b)`, independent of the
time. -/
theorem kgFieldEnergy_uniform (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W x) y : ℂ) = inner ℂ x (W y))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad W g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W g h t‖ ^ (2 : ℕ)
      ≤ (1 + b) / (1 - b) * (‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ)) := by
  have hb1' : (0 : ℝ) < 1 - b := by linarith
  have hcons := kgFieldEnergy_conserved hb0 hW hsa g h t
  have hPt := abs_re_inner_potential_le hW (kgFieldMild W (kgFreqInvOp g) h t)
  have hP0 := abs_re_inner_potential_le hW (kgFreqInvOp (E := E) g)
  have hut := norm_kgFieldMild_sq_le_energy hb0 hW g h t
  have hfg : ‖kgFreqInvOp (E := E) g‖ ≤ ‖g‖ := by
    have hc := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le g
    rwa [one_mul] at hc
  have hfg2 : ‖kgFreqInvOp (E := E) g‖ ^ (2 : ℕ) ≤ ‖g‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hfg 2
  have hPtle : RCLike.re (inner ℂ (W (kgFieldMild W (kgFreqInvOp g) h t))
      (kgFieldMild W (kgFreqInvOp g) h t) : ℂ)
      ≤ b * (‖kgFieldGrad W g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W g h t‖ ^ (2 : ℕ)) := by
    have h1 := (abs_le.mp hPt).2
    have h2 : b * ‖kgFieldMild W (kgFreqInvOp g) h t‖ ^ (2 : ℕ)
        ≤ b * (‖kgFieldGrad W g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W g h t‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hut hb0
    linarith
  have hP0le : -RCLike.re (inner ℂ (W (kgFreqInvOp g)) (kgFreqInvOp g) : ℂ) ≤ b * ‖g‖ ^ (2 : ℕ) := by
    have h1 := (abs_le.mp hP0).1
    have h2 : b * ‖kgFreqInvOp (E := E) g‖ ^ (2 : ℕ) ≤ b * ‖g‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hfg2 hb0
    linarith
  have hsum : (1 - b) * (‖kgFieldGrad W g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W g h t‖ ^ (2 : ℕ))
      ≤ (1 + b) * (‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ)) := by
    have hh : (0 : ℝ) ≤ ‖h‖ ^ (2 : ℕ) := sq_nonneg _
    nlinarith [hcons, hPtle, hP0le]
  rw [div_mul_eq_mul_div, le_div_iff₀ hb1']
  linarith [hsum]

/-- **A confining real potential needs no smallness at all**: the energy never exceeds its initial
value. -/
theorem kgFieldEnergy_le_of_nonpos (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W x) y : ℂ) = inner ℂ x (W y))
    (hneg : ∀ x : Lp ℂ 2 (volume : Measure E), RCLike.re (inner ℂ (W x) x : ℂ) ≤ 0)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad W g h t‖ ^ (2 : ℕ) + ‖kgFieldVel W g h t‖ ^ (2 : ℕ)
      ≤ ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) - RCLike.re (inner ℂ (W (kgFreqInvOp g)) (kgFreqInvOp g) : ℂ) := by
  have hcons := kgFieldEnergy_conserved hb0 hW hsa g h t
  have hPt := hneg (kgFieldMild W (kgFreqInvOp g) h t)
  linarith

/-- **A confining real potential keeps the field itself bounded for all time.** -/
theorem norm_kgFieldMild_le_of_nonpos (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W x) y : ℂ) = inner ℂ x (W y))
    (hneg : ∀ x : Lp ℂ 2 (volume : Measure E), RCLike.re (inner ℂ (W x) x : ℂ) ≤ 0)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W (kgFreqInvOp g) h t‖ ^ (2 : ℕ)
      ≤ ‖g‖ ^ (2 : ℕ) + ‖h‖ ^ (2 : ℕ) - RCLike.re (inner ℂ (W (kgFreqInvOp g)) (kgFreqInvOp g) : ℂ) :=
  (norm_kgFieldMild_sq_le_energy hb0 hW g h t).trans
    (kgFieldEnergy_le_of_nonpos hb0 hW hsa hneg g h t)

end Uniform

end GaloisForLFunctions.HTGeometry
