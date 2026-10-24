import GaloisForLFunctions.RHTower.CCM.CCMApertureRemainderFamilyContinuity
import GaloisForLFunctions.HTGeometry.CapocasaCatanesePositivity

/-!
# The aperture flow is a shell flux

For every aperture-compatible family of bounded remainders `a ↦ B_a` (`CCMRemainderFamily`: the
literal restricted Weil operator and its prime-deleted, prime-inserted, countably perturbed and
prime-free variants) the ground energy `μ(a)` flows down as the aperture grows. This module gives
the exact law of one step `a → b` of the flow.

* **Euler–Lagrange.** A ground form state `u_a` annihilates the shifted form:
  `form_a(u_a, w) = μ(a) ⟨J u_a, J w⟩` for every form vector `w`
  (`shiftedForm_eq_zero_of_isGround`).
* **Polarized compatibility.** Extending both arguments to a larger aperture leaves the
  sesquilinear form unchanged (`apertureForm_ext`).
* **The shell flux.** The residual `Φ_{a,b}(v) = form_b(ext u_a, v) − μ(a) ⟨J ext u_a, J v⟩` of the
  smaller ground state vanishes on every form vector supported in the smaller aperture
  (`shellFlux_ext_eq_zero`): it is a functional of the shell `a ≤ |x| ≤ b`.
* **The flux law.** `Φ_{a,b}(u_b) = (μ(b) − μ(a)) ⟨J ext u_a, J u_b⟩` (`shellFlux_ground_eq`): a
  step of the flow is the shell flux of the smaller ground state read by the larger one.
* **The sign-definite jump.** `μ(a) − μ(b) = Re h_b(ext u_a − c u_b)` for every `c ∈ ℂ`, where
  `h_b ≥ 0` is the shifted form at `b` (`energy_sub_energy_eq_shiftedForm`). A flat step means that
  the smaller ground state stays a ground state, and then its shell flux vanishes identically
  (`isGround_ext_iff_energy_eq`, `shellFlux_eq_zero_of_energy_eq`).

None of this uses the arithmetic content of `B_a`: the identities hold verbatim for every perturbed
family, so they cannot by themselves decide the sign of the flow.
-/

open Complex
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.RHTower GaloisForLFunctions.HTGeometry

/-! ## Extension of form vectors to a larger aperture -/

/-- A form vector at aperture `a`, viewed at a larger aperture `b` with the same weighted Fourier
data. -/
def apertureExt {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain a) : CCMArchimedeanFormDomain b :=
  ⟨u.1, by
    obtain ⟨v, hv⟩ := exists_ccmArchimedeanFormDomain_extension hab u
    exact hv ▸ v.2⟩

section Ext

variable {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)

theorem apertureExt_val (u : CCMArchimedeanFormDomain a) :
    (apertureExt hab u).1 = u.1 := by
  unfold apertureExt
  rfl

theorem apertureExt_add (u v : CCMArchimedeanFormDomain a) :
    apertureExt hab (u + v) = apertureExt hab u + apertureExt hab v := by
  apply Subtype.ext
  rw [Submodule.coe_add, apertureExt_val, apertureExt_val, apertureExt_val, Submodule.coe_add]

theorem apertureExt_smul (c : ℂ) (u : CCMArchimedeanFormDomain a) :
    apertureExt hab (c • u) = c • apertureExt hab u := by
  apply Subtype.ext
  rw [Submodule.coe_smul, apertureExt_val, apertureExt_val, Submodule.coe_smul]

theorem inner_embedding_apertureExt (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmArchimedeanFormToAperture b (apertureExt hab u))
        (ccmArchimedeanFormToAperture b (apertureExt hab v)) =
      inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  rw [Submodule.coe_inner, Submodule.coe_inner,
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val hab u),
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val hab v)]

theorem norm_embedding_apertureExt (u : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture b (apertureExt hab u)‖ = ‖ccmArchimedeanFormToAperture a u‖ :=
  norm_ccmArchimedeanFormToAperture_eq_of_val_eq (apertureExt_val hab u)

end Ext

/-! ## The sesquilinear form of a family and its Euler–Lagrange equation -/

variable (F : CCMRemainderFamily)

/-- The sesquilinear form `⟨u, v⟩ + ⟨B_a J u, J v⟩` of the family at aperture `a`; its real
diagonal is `F.Q a`. -/
def apertureForm (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) : ℂ :=
  inner ℂ u v +
    inner ℂ (F.B a (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a v)

/-- The form shifted by the mass `E ⟨J u, J v⟩`. -/
def shiftedForm (a : SuzukiPositiveAperture) (E : ℝ) (u v : CCMArchimedeanFormDomain a) : ℂ :=
  apertureForm F a u v -
    (E : ℂ) * inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)

/-- A ground form state of the family at aperture `a`. -/
def IsGround (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : Prop :=
  F.Q a u = F.energy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2

section Form

variable (a : SuzukiPositiveAperture)

theorem apertureForm_self_re (u : CCMArchimedeanFormDomain a) :
    (apertureForm F a u u).re = F.Q a u :=
  (F.Q_eq_form_re a u).symm

theorem apertureForm_add_left (u v w : CCMArchimedeanFormDomain a) :
    apertureForm F a (u + v) w = apertureForm F a u w + apertureForm F a v w := by
  rw [apertureForm, apertureForm, apertureForm, map_add, map_add, inner_add_left u v w,
    inner_add_left (F.B a (ccmArchimedeanFormToAperture a u))
      (F.B a (ccmArchimedeanFormToAperture a v)) (ccmArchimedeanFormToAperture a w)]
  ring

theorem apertureForm_add_right (u v w : CCMArchimedeanFormDomain a) :
    apertureForm F a u (v + w) = apertureForm F a u v + apertureForm F a u w := by
  rw [apertureForm, apertureForm, apertureForm, map_add, inner_add_right u v w,
    inner_add_right (F.B a (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a v)
      (ccmArchimedeanFormToAperture a w)]
  ring

theorem apertureForm_smul_left (c : ℂ) (u v : CCMArchimedeanFormDomain a) :
    apertureForm F a (c • u) v = (starRingEnd ℂ) c * apertureForm F a u v := by
  rw [apertureForm, apertureForm, map_smul, map_smul, inner_smul_left u v c,
    inner_smul_left (F.B a (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a v) c]
  ring

theorem apertureForm_smul_right (c : ℂ) (u v : CCMArchimedeanFormDomain a) :
    apertureForm F a u (c • v) = c * apertureForm F a u v := by
  rw [apertureForm, apertureForm, map_smul, inner_smul_right u v c,
    inner_smul_right (F.B a (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a v) c]
  ring

/-- The form is Hermitian because `B_a` is self-adjoint. -/
theorem apertureForm_conj (u v : CCMArchimedeanFormDomain a) :
    apertureForm F a v u = (starRingEnd ℂ) (apertureForm F a u v) := by
  have hB := (F.selfAdjoint a).isSymmetric (ccmArchimedeanFormToAperture a v)
    (ccmArchimedeanFormToAperture a u)
  change inner ℂ (F.B a (ccmArchimedeanFormToAperture a v)) (ccmArchimedeanFormToAperture a u) =
    inner ℂ (ccmArchimedeanFormToAperture a v) (F.B a (ccmArchimedeanFormToAperture a u)) at hB
  rw [apertureForm, apertureForm, map_add, hB, inner_conj_symm v u,
    inner_conj_symm (ccmArchimedeanFormToAperture a v) (F.B a (ccmArchimedeanFormToAperture a u))]

theorem inner_embedding_self_re (u : CCMArchimedeanFormDomain a) :
    (inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a u)).re =
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ccmArchimedeanFormToAperture a u)]
  norm_cast

theorem shiftedForm_self_re (E : ℝ) (u : CCMArchimedeanFormDomain a) :
    (shiftedForm F a E u u).re = F.Q a u - E * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [shiftedForm, sub_re, apertureForm_self_re, re_ofReal_mul, inner_embedding_self_re]

theorem shiftedForm_conj (E : ℝ) (u v : CCMArchimedeanFormDomain a) :
    shiftedForm F a E v u = (starRingEnd ℂ) (shiftedForm F a E u v) := by
  rw [shiftedForm, shiftedForm, map_sub, map_mul, Complex.conj_ofReal, apertureForm_conj F a u v,
    inner_conj_symm (ccmArchimedeanFormToAperture a v) (ccmArchimedeanFormToAperture a u)]

theorem shiftedForm_add_right (E : ℝ) (u v w : CCMArchimedeanFormDomain a) :
    shiftedForm F a E u (v + w) = shiftedForm F a E u v + shiftedForm F a E u w := by
  rw [shiftedForm, shiftedForm, shiftedForm, apertureForm_add_right, map_add,
    inner_add_right (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)
      (ccmArchimedeanFormToAperture a w)]
  ring

theorem shiftedForm_smul_right (E : ℝ) (c : ℂ) (u v : CCMArchimedeanFormDomain a) :
    shiftedForm F a E u (c • v) = c * shiftedForm F a E u v := by
  rw [shiftedForm, shiftedForm, apertureForm_smul_right, map_smul,
    inner_smul_right (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) c]
  ring

theorem shiftedForm_sub_right (E : ℝ) (u v w : CCMArchimedeanFormDomain a) :
    shiftedForm F a E u (v - w) = shiftedForm F a E u v - shiftedForm F a E u w := by
  rw [sub_eq_add_neg, shiftedForm_add_right, ← neg_one_smul ℂ w, shiftedForm_smul_right]
  ring

theorem shiftedForm_sub_left (E : ℝ) (u v w : CCMArchimedeanFormDomain a) :
    shiftedForm F a E (u - v) w = shiftedForm F a E u w - shiftedForm F a E v w := by
  rw [shiftedForm_conj F a E w (u - v), shiftedForm_sub_right, map_sub, ← shiftedForm_conj,
    ← shiftedForm_conj]

theorem shiftedForm_smul_left (E : ℝ) (c : ℂ) (u v : CCMArchimedeanFormDomain a) :
    shiftedForm F a E (c • u) v = (starRingEnd ℂ) c * shiftedForm F a E u v := by
  rw [shiftedForm_conj F a E v (c • u), shiftedForm_smul_right, map_mul, ← shiftedForm_conj]

/-- The shifted form, with its arguments swapped, is a Hermitian form in the sense of
`IsHermitianForm` (linear in the first slot). -/
theorem isHermitianForm_shiftedForm (E : ℝ) :
    IsHermitianForm (fun x y : CCMArchimedeanFormDomain a => shiftedForm F a E y x) where
  add_left x y z := shiftedForm_add_right F a E z x y
  smul_left c x y := shiftedForm_smul_right F a E c y x
  symm x y := by
    rw [shiftedForm_conj F a E x y, Complex.star_def, Complex.conj_conj]

/-- **Euler–Lagrange equation.** A ground form state annihilates the shifted form at the ground
energy: the shifted form is nonnegative and Hermitian and vanishes on the diagonal at `u`. -/
theorem shiftedForm_eq_zero_of_isGround {u : CCMArchimedeanFormDomain a} (hu : IsGround F a u)
    (v : CCMArchimedeanFormDomain a) : shiftedForm F a (F.energy a) u v = 0 := by
  have hpsd : ∀ x : CCMArchimedeanFormDomain a,
      0 ≤ ((fun x y => shiftedForm F a (F.energy a) y x) x x).re := fun x => by
    change 0 ≤ (shiftedForm F a (F.energy a) x x).re
    rw [shiftedForm_self_re]
    linarith [F.energy_mul_formNorm_sq_le a x]
  have hu0 : ((fun x y => shiftedForm F a (F.energy a) y x) u u).re = 0 := by
    change (shiftedForm F a (F.energy a) u u).re = 0
    rw [shiftedForm_self_re, hu, sub_self]
  have h : shiftedForm F a (F.energy a) v u = 0 :=
    (isHermitianForm_shiftedForm F a (F.energy a)).eq_zero_of_self_re_eq_zero hpsd hu0 v
  rw [shiftedForm_conj F a _ v u, h, map_zero]

/-- The normalized ground state of the family is a ground form state. -/
theorem isGround_normalizedGround : IsGround F a (F.normalizedGround a) := by
  rw [IsGround, F.normalizedGround_Q, F.norm_normalizedGround_embedding, one_pow, mul_one]

end Form

/-! ## Polarized aperture compatibility -/

/-- The defect of a form under extension, written with swapped arguments so that it is linear in
the first slot. -/
private def extDefect {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (x y : CCMArchimedeanFormDomain a) : ℂ :=
  apertureForm F b (apertureExt hab y) (apertureExt hab x) - apertureForm F a y x

private theorem isHermitianForm_extDefect {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    IsHermitianForm (extDefect F hab) where
  add_left x x' z := by
    rw [extDefect, extDefect, extDefect, apertureExt_add, apertureForm_add_right,
      apertureForm_add_right]
    ring
  smul_left c x z := by
    rw [extDefect, extDefect, apertureExt_smul, apertureForm_smul_right, apertureForm_smul_right]
    ring
  symm x z := by
    rw [extDefect, extDefect, Complex.star_def, map_sub, ← apertureForm_conj, ← apertureForm_conj]

/-- **Polarized compatibility.** The sesquilinear form is unchanged when both arguments are
extended to a larger aperture; the diagonal law of `CCMRemainderFamily` polarizes. -/
theorem apertureForm_ext {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (x y : CCMArchimedeanFormDomain a) :
    apertureForm F b (apertureExt hab x) (apertureExt hab y) = apertureForm F a x y := by
  have hdiag : ∀ z, (extDefect F hab z z).re = 0 := fun z => by
    rw [extDefect, sub_re, apertureForm_self_re, apertureForm_self_re,
      F.Q_eq_of_val_eq hab (apertureExt_val hab z), sub_self]
  have h := (isHermitianForm_extDefect F hab).eq_zero_of_self_re_eq_zero
    (fun z => (hdiag z).ge) (hdiag y) x
  rw [extDefect] at h
  exact sub_eq_zero.mp h

/-! ## The shell flux and the flux law -/

/-- The **shell flux** of the normalized ground state at `a`, read on the form domain at `b ≥ a`:
`Φ_{a,b}(v) = form_b(ext u_a, v) − μ(a) ⟨J ext u_a, J v⟩`. -/
def shellFlux {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (v : CCMArchimedeanFormDomain b) : ℂ :=
  shiftedForm F b (F.energy a) (apertureExt hab (F.normalizedGround a)) v

/-- **The shell flux lives on the shell.** It vanishes on every form vector supported in the
smaller aperture. -/
theorem shellFlux_ext_eq_zero {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (w : CCMArchimedeanFormDomain a) : shellFlux F hab (apertureExt hab w) = 0 := by
  rw [shellFlux, shiftedForm, apertureForm_ext, inner_embedding_apertureExt]
  exact shiftedForm_eq_zero_of_isGround F a (isGround_normalizedGround F a) w

/-- **The flux law.** One step of the aperture flow is the shell flux of the smaller ground state
read by the larger one: `Φ_{a,b}(u_b) = (μ(b) − μ(a)) ⟨J ext u_a, J u_b⟩`. -/
theorem shellFlux_ground_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    shellFlux F hab (F.normalizedGround b) =
      ((F.energy b - F.energy a : ℝ) : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture b (apertureExt hab (F.normalizedGround a)))
          (ccmArchimedeanFormToAperture b (F.normalizedGround b)) := by
  set e := apertureExt hab (F.normalizedGround a)
  have hEL : shiftedForm F b (F.energy b) e (F.normalizedGround b) = 0 := by
    rw [shiftedForm_conj F b _ (F.normalizedGround b) e,
      shiftedForm_eq_zero_of_isGround F b (isGround_normalizedGround F b) e, map_zero]
  rw [shiftedForm, sub_eq_zero] at hEL
  rw [shellFlux, shiftedForm, hEL]
  push_cast
  ring

/-- When the two ground states overlap, the jump of the flow is the normalized shell flux. -/
theorem energy_sub_eq_shellFlux_div {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (hov : inner ℂ (ccmArchimedeanFormToAperture b (apertureExt hab (F.normalizedGround a)))
      (ccmArchimedeanFormToAperture b (F.normalizedGround b)) ≠ 0) :
    ((F.energy b - F.energy a : ℝ) : ℂ) =
      shellFlux F hab (F.normalizedGround b) /
        inner ℂ (ccmArchimedeanFormToAperture b (apertureExt hab (F.normalizedGround a)))
          (ccmArchimedeanFormToAperture b (F.normalizedGround b)) := by
  rw [shellFlux_ground_eq, mul_div_cancel_right₀ _ hov]

/-! ## The sign-definite jump -/

/-- **The jump is a relaxation energy.** For every `c ∈ ℂ`,
`μ(a) − μ(b) = Re h_b(ext u_a − c u_b)` with `h_b = form_b − μ(b) ⟨J·, J·⟩ ≥ 0`. -/
theorem energy_sub_energy_eq_shiftedForm {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (c : ℂ) :
    F.energy a - F.energy b =
      (shiftedForm F b (F.energy b)
        (apertureExt hab (F.normalizedGround a) - c • F.normalizedGround b)
        (apertureExt hab (F.normalizedGround a) - c • F.normalizedGround b)).re := by
  set e := apertureExt hab (F.normalizedGround a)
  set u := F.normalizedGround b
  have hR : ∀ v, shiftedForm F b (F.energy b) u v = 0 :=
    shiftedForm_eq_zero_of_isGround F b (isGround_normalizedGround F b)
  have hL : ∀ v, shiftedForm F b (F.energy b) v u = 0 := fun v => by
    rw [shiftedForm_conj, hR, map_zero]
  have hexp : shiftedForm F b (F.energy b) (e - c • u) (e - c • u) =
      shiftedForm F b (F.energy b) e e := by
    rw [shiftedForm_sub_left, shiftedForm_sub_right, shiftedForm_sub_right,
      shiftedForm_smul_left, shiftedForm_smul_left, shiftedForm_smul_right, shiftedForm_smul_right]
    simp only [hR, hL, mul_zero, sub_zero]
  rw [hexp, shiftedForm_self_re, F.Q_eq_of_val_eq hab (apertureExt_val hab _),
    norm_embedding_apertureExt, F.normalizedGround_Q, F.norm_normalizedGround_embedding]
  ring

/-- A step of the flow is flat exactly when the extended smaller ground state is a ground state at
the larger aperture. -/
theorem isGround_ext_iff_energy_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    IsGround F b (apertureExt hab (F.normalizedGround a)) ↔ F.energy b = F.energy a := by
  rw [IsGround, F.Q_eq_of_val_eq hab (apertureExt_val hab _), norm_embedding_apertureExt,
    F.normalizedGround_Q, F.norm_normalizedGround_embedding, one_pow, mul_one]
  exact eq_comm

/-- On a flat step the smaller ground state radiates no shell flux at all. -/
theorem shellFlux_eq_zero_of_energy_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (h : F.energy b = F.energy a) (v : CCMArchimedeanFormDomain b) : shellFlux F hab v = 0 := by
  rw [shellFlux, ← h]
  exact shiftedForm_eq_zero_of_isGround F b ((isGround_ext_iff_energy_eq F hab).mpr h) v

/-- **The aperture flow is a shell flux.** For every aperture family and `a ≤ b`: the shell flux
vanishes on the smaller form domain, it equals the jump times the overlap on the larger ground
state, and the jump is the nonnegative relaxation energy of the extended smaller ground state. -/
theorem apertureFlow_isShellFlux {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    (∀ w : CCMArchimedeanFormDomain a, shellFlux F hab (apertureExt hab w) = 0) ∧
      shellFlux F hab (F.normalizedGround b) =
        ((F.energy b - F.energy a : ℝ) : ℂ) *
          inner ℂ (ccmArchimedeanFormToAperture b (apertureExt hab (F.normalizedGround a)))
            (ccmArchimedeanFormToAperture b (F.normalizedGround b)) ∧
      (∀ c : ℂ, F.energy a - F.energy b =
        (shiftedForm F b (F.energy b)
          (apertureExt hab (F.normalizedGround a) - c • F.normalizedGround b)
          (apertureExt hab (F.normalizedGround a) - c • F.normalizedGround b)).re) ∧
      (IsGround F b (apertureExt hab (F.normalizedGround a)) ↔ F.energy b = F.energy a) :=
  ⟨shellFlux_ext_eq_zero F hab, shellFlux_ground_eq F hab,
    energy_sub_energy_eq_shiftedForm F hab, isGround_ext_iff_energy_eq F hab⟩

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
