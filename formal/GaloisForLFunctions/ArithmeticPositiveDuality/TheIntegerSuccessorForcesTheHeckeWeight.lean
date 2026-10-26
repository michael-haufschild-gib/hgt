import GaloisForLFunctions.ArithmeticPositiveDuality.AffinePositivityIsInducedFromTheDilations

/-!
# The integer successor forces the Hecke weight

The affine group `x ↦ ax + b` of `ℚ` carries the successor and the dilations. Restriction–induction
(`exists_isPosDefOnGroup_extension_iff`) says the successor part of a positive-definite function is
free; a forcing law on the affine group must prescribe it from the arithmetic source. The most
arithmetic prescription is the **integer successor state**: `φ(x ↦ x + b) = 1_ℤ(b)`, the state of
the additive structure of `ℤ` inside `ℚ`. This file computes exactly what it forces on the
dilations.

* **Hecke–Bessel law** (`heckeBessel`). If `φ` is positive definite with integer successor and
  `u = ±n/d` in lowest terms, then for representatives `b` of distinct classes of `ℚ/(1/d)ℤ`,
  `n d Σ_b |φ(x ↦ ux + b)|² ≤ 1`; in particular `|φ(x ↦ ux)| ≤ (nd)^{−1/2}`
  (`normSq_dilation_le`). Proof: `φ` is `ℤ`-bi-invariant, so `φ(ux + ·)` is `(ℤ + uℤ) = (1/d)ℤ`
  periodic; the averages `X = d⁻¹Σ_{j<d}[x + j/d]` and `Y_b = n⁻¹Σ_{k<n}[ux + b + k/d]` have Gram
  entries `⟨X,X⟩ = 1/d`, `⟨Y_b, Y_{b'}⟩ = n⁻¹δ_{bb'}`, `⟨X, Y_b⟩ = φ(ux + b)`, and the Gram form of
  `X − Σ_b nφ̄(ux+b) Y_b` is `1/d − nΣ_b|φ(ux+b)|² ≥ 0`.
* **Sharpness: the Haar state** (`isPosDefOnGroup_haarState`, `integer_successor_hecke_weight`). The function
  `φ_*(x ↦ ax + b) = (nd)^{−1/2}·1[db ∈ ℤ]` (`a = ±n/d`) is positive definite, has integer successor
  and equality in the law. It is the coefficient `⟨π(g)1_Ẑ, 1_Ẑ⟩` of the finite adeles: in the
  ball picture `φ_*(g⁻¹h) = |a_g a_h|^{1/2} dens(gℤ ∩ hℤ)`, realized here on a finite period of
  `ℤ` by the Chinese remainder count of two residue classes.
* **No archimedean dilation part** (`successor_scale_eq_zero_of_continuousAt`). If the successor
  part is `c·1_ℤ` and `r ↦ φ(x ↦ rx)` on `ℚ_{>0}` is the restriction of a function continuous at
  `1`, then `c = 0`: along `u = (m+2)/(m+1) → 1` the bound `(nd)^{−1/2} → 0` contradicts continuity.
  So the spline correlation, or any Weil dilation correlation, never meets the integer successor
  (`splineCorr_zero_of_integer_successor`).

The integer successor sees the dilations only `p`-adically, with the weight `p^{−|k|/2}` of the
critical line: `(nd)^{−1/2} = Π_p p^{−|v_p(u)|/2}`. A successor-prescribed carrier for Weil's
archimedean correlation must therefore split into an archimedean and a finite-adelic factor.
-/

open Complex Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### Positive-definite functions on groups: hermitian symmetry and bi-invariance -/

section Group

variable {G : Type*} [Group G] {φ : G → ℂ}

/-- The two-point Gram form. -/
theorem IsPosDefOnGroup.two_point (hφ : IsPosDefOnGroup φ) (x y : G) (c e : ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ star c * φ 1 * c + star c * φ (x⁻¹ * y) * e +
      star e * φ (y⁻¹ * x) * c + star e * φ 1 * e = r := by
  obtain ⟨r, hr, h⟩ := hφ 2 ![x, y] ![c, e]
  refine ⟨r, hr, ?_⟩
  rw [← h]
  simp [Fin.sum_univ_two]
  ring

/-- `φ(1)` is real and nonnegative. -/
theorem IsPosDefOnGroup.map_one_eq (hφ : IsPosDefOnGroup φ) : ∃ r : ℝ, 0 ≤ r ∧ φ 1 = r := by
  obtain ⟨r, hr, h⟩ := hφ 1 ![1] ![1]
  exact ⟨r, hr, by simpa using h⟩

/-- Hermitian symmetry `φ(x⁻¹) = conj φ(x)`. -/
theorem IsPosDefOnGroup.map_inv (hφ : IsPosDefOnGroup φ) (x : G) : φ x⁻¹ = star (φ x) := by
  obtain ⟨r0, -, h0⟩ := hφ.map_one_eq
  obtain ⟨r1, -, h1⟩ := hφ.two_point 1 x 1 1
  obtain ⟨r2, -, h2⟩ := hφ.two_point 1 x 1 I
  simp only [inv_one, one_mul, mul_one, star_one, h0] at h1 h2
  have i1 := congrArg Complex.im h1
  have i2 := congrArg Complex.im h2
  simp at i1 i2
  apply Complex.ext <;> simp <;> linarith

/-- A real quadratic `a + 2 Re(tD)` that is nonnegative for every `t` forces `D = 0`. -/
theorem eq_zero_of_forall_quadratic {a : ℝ} {D : ℂ}
    (h : ∀ t : ℂ, ∃ r : ℝ, 0 ≤ r ∧ (a : ℂ) + t * D + star (t * D) = r) : D = 0 := by
  by_contra hD
  have hn : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD
  set s : ℝ := (|a| + 1) / Complex.normSq D
  obtain ⟨r, hr, hrr⟩ := h (-(s : ℂ) * star D)
  have htD : -(s : ℂ) * star D * D = ((-(|a| + 1) : ℝ) : ℂ) := by
    rw [mul_assoc, show star D * D = (Complex.normSq D : ℂ) from
      (Complex.normSq_eq_conj_mul_self).symm]
    simp only [s]
    push_cast
    have : (Complex.normSq D : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [htD] at hrr
  have := congrArg Complex.re hrr
  simp at this
  have := abs_nonneg a
  linarith [le_abs_self a]

/-- **Bi-invariance.** If `φ(h) = φ(1)` then `φ(gh) = φ(g)`: the three-point Gram form on
`1, g, gh` with coefficients `1, t, −t` is `φ(1) + 2 Re(t(φ(g) − φ(gh)))`. -/
theorem IsPosDefOnGroup.mul_right_eq (hφ : IsPosDefOnGroup φ) {h : G} (hh : φ h = φ 1) (g : G) :
    φ (g * h) = φ g := by
  obtain ⟨r0, -, h0⟩ := hφ.map_one_eq
  have hinv : ∀ x, φ x⁻¹ = star (φ x) := hφ.map_inv
  have hhinv : φ h⁻¹ = r0 := by rw [hinv, hh, h0]; simp
  suffices hD : φ g - φ (g * h) = 0 from (sub_eq_zero.mp hD).symm
  refine eq_zero_of_forall_quadratic (a := r0) fun t => ?_
  obtain ⟨r, hr, hs⟩ := hφ 3 ![1, g, g * h] ![1, t, -t]
  refine ⟨r, hr, ?_⟩
  rw [← hs]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, inv_one, one_mul, inv_mul_cancel, mul_inv_rev,
    mul_assoc, inv_mul_cancel_left, star_one, mul_one, star_neg]
  have e : φ (h⁻¹ * g⁻¹) = star (φ (g * h)) := by rw [← mul_inv_rev, hinv]
  rw [e, hinv g, hhinv, hh, h0, star_mul, star_sub]
  ring

/-- Left bi-invariance. -/
theorem IsPosDefOnGroup.mul_left_eq (hφ : IsPosDefOnGroup φ) {h : G} (hh : φ h = φ 1) (g : G) :
    φ (h * g) = φ g := by
  obtain ⟨r0, -, h0⟩ := hφ.map_one_eq
  have hinv : ∀ x, φ x⁻¹ = star (φ x) := hφ.map_inv
  have hh' : φ h⁻¹ = φ 1 := by rw [hinv, hh, h0]; simp
  have := hφ.mul_right_eq hh' g⁻¹
  rw [← mul_inv_rev, hinv, hinv] at this
  simpa using congrArg star this

end Group

/-! ### Affine coordinates -/

/-- The slope `a` of `x ↦ ax + b`. -/
def affSlope (g : AffineGroupQ) : ℚ := g.linear 1
/-- The shift `b` of `x ↦ ax + b`. -/
def affShift (g : AffineGroupQ) : ℚ := g 0

theorem affine_apply_eq (g : AffineGroupQ) (x : ℚ) : g x = affSlope g * x + affShift g := by
  have h := congrFun g.toAffineMap.decomp x
  simp only [Pi.add_apply] at h
  have h2 : g.toAffineMap.linear x = x * g.linear 1 := by
    change g.linear x = _
    rw [← smul_eq_mul, ← g.linear.map_smul, smul_eq_mul, mul_one]
  rw [show g x = g.toAffineMap x from rfl, h, h2, affSlope, affShift, mul_comm]
  rfl

theorem affSlope_ne_zero (g : AffineGroupQ) : affSlope g ≠ 0 := by
  intro h
  have : g.linear 1 = g.linear 0 := by rw [map_zero]; exact h
  exact one_ne_zero (g.linear.injective this)

theorem affine_ext {g h : AffineGroupQ} (h1 : affSlope g = affSlope h) (h2 : affShift g = affShift h) :
    g = h := by
  ext x; rw [affine_apply_eq g, affine_apply_eq h, h1, h2]

theorem affSlope_mul (g h : AffineGroupQ) : affSlope (g * h) = affSlope g * affSlope h := by
  have e1 := affine_apply_eq (g * h) 1
  have e0 := affine_apply_eq (g * h) 0
  rw [AffineEquiv.coe_mul, Function.comp_apply, affine_apply_eq h, affine_apply_eq g] at e1 e0
  linear_combination -(e1 - e0)

theorem affShift_mul (g h : AffineGroupQ) : affShift (g * h) = affSlope g * affShift h + affShift g := by
  have e0 := affine_apply_eq (g * h) 0
  rw [AffineEquiv.coe_mul, Function.comp_apply, affine_apply_eq h, affine_apply_eq g] at e0
  linear_combination -e0

theorem affSlope_one : affSlope 1 = 1 := by
  have := affine_apply_eq 1 1
  have h0 := affine_apply_eq 1 0
  simp only [AffineEquiv.coe_one, id] at this h0
  linear_combination -this + h0
theorem affShift_one : affShift 1 = 0 := by simp [affShift]

theorem affSlope_inv (g : AffineGroupQ) : affSlope g⁻¹ = (affSlope g)⁻¹ := by
  have := affSlope_mul g g⁻¹
  rw [mul_inv_cancel, affSlope_one] at this
  have hs := affSlope_ne_zero g
  field_simp
  linear_combination -this

theorem affShift_inv (g : AffineGroupQ) : affShift g⁻¹ = -affShift g / affSlope g := by
  have h := affShift_mul g g⁻¹
  rw [mul_inv_cancel, affShift_one] at h
  have hs := affSlope_ne_zero g
  field_simp
  linear_combination -h

/-- The translation `x ↦ x + b`. -/
def translation (b : ℚ) : AffineGroupQ := AffineEquiv.constVAdd ℚ ℚ b

theorem affSlope_translation (b : ℚ) : affSlope (translation b) = 1 := by
  simp [affSlope, translation]
theorem affShift_translation (b : ℚ) : affShift (translation b) = b := by
  simp [affShift, translation]
theorem affSlope_dilation (u : ℚˣ) : affSlope (dilation u) = u := by
  have := affine_apply_eq (dilation u) 1
  rw [dilation_apply] at this
  have h0 := affine_apply_eq (dilation u) 0
  rw [dilation_apply] at h0
  linear_combination -this + h0
theorem affShift_dilation (u : ℚˣ) : affShift (dilation u) = 0 := by
  simp [affShift, dilation_apply]


theorem translation_zero : translation 0 = 1 :=
  affine_ext (by rw [affSlope_translation, affSlope_one]) (by rw [affShift_translation, affShift_one])

theorem translation_inv_mul (a b : ℚ) :
    (translation a)⁻¹ * translation b = translation (b - a) := by
  refine affine_ext ?_ ?_
  · simp [affSlope_mul, affSlope_inv, affSlope_translation]
  · simp [affShift_mul, affShift_inv, affSlope_inv, affSlope_translation, affShift_translation]
    ring

theorem translation_inv_mul_tdil (a b : ℚ) (u : ℚˣ) :
    (translation a)⁻¹ * (translation b * dilation u) = translation (b - a) * dilation u := by
  rw [← mul_assoc, translation_inv_mul]

theorem tdil_inv_mul_tdil (b b' : ℚ) (u : ℚˣ) :
    (translation b * dilation u)⁻¹ * (translation b' * dilation u) =
      translation ((b' - b) / u) := by
  have hu : (u : ℚ) ≠ 0 := u.ne_zero
  refine affine_ext ?_ ?_
  · simp only [affSlope_mul, affSlope_inv, affSlope_translation, affSlope_dilation]
    field_simp
  · simp only [affShift_mul, affShift_inv, affSlope_mul, affSlope_inv, affSlope_translation,
      affSlope_dilation, affShift_translation, affShift_dilation]
    field_simp
    ring

theorem translation_add_mul_dil (b : ℚ) (m m' : ℤ) (u : ℚˣ) :
    translation (b + m + u * m') * dilation u =
      translation m * (translation b * dilation u) * translation m' := by
  refine affine_ext ?_ ?_
  · simp only [affSlope_mul, affSlope_translation, affSlope_dilation]; ring
  · simp only [affShift_mul, affSlope_mul, affSlope_translation, affSlope_dilation,
      affShift_translation, affShift_dilation]
    ring

/-! ### The integer successor state and the Hecke–Bessel law -/

/-- The **integer successor state**: `φ` restricted to translations is the indicator of `ℤ`. -/
def HasIntegerSuccessor (φ : AffineGroupQ → ℂ) : Prop :=
  ∀ b : ℚ, φ (translation b) = if b.den = 1 then 1 else 0

theorem den_eq_one_iff_exists (q : ℚ) : q.den = 1 ↔ ∃ m : ℤ, (m : ℚ) = q := by
  constructor
  · intro h; exact ⟨q.num, (Rat.den_eq_one_iff q).mp h⟩
  · rintro ⟨m, rfl⟩; exact Rat.den_intCast m

/-- `ℤ`-bi-invariance of a positive-definite function with integer successor. -/
theorem hasIntegerSuccessor_one {φ : AffineGroupQ → ℂ} (hs : HasIntegerSuccessor φ) : φ 1 = 1 := by
  have := hs 0; rwa [translation_zero, Rat.den_zero, if_pos rfl] at this

theorem hasIntegerSuccessor_int {φ : AffineGroupQ → ℂ} (hs : HasIntegerSuccessor φ) (m : ℤ) :
    φ (translation m) = φ 1 := by
  rw [hs, hasIntegerSuccessor_one hs, Rat.den_intCast, if_pos rfl]

/-- Period of the successor-twisted dilation coefficients. -/
theorem tdil_periodic {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (hs : HasIntegerSuccessor φ)
    (u : ℚˣ) (b : ℚ) (q : ℤ) :
    φ (translation (b + q / (u : ℚ).den) * dilation u) = φ (translation b * dilation u) := by
  have hcop : Int.gcd (u : ℚ).num ((u : ℚ).den : ℤ) = 1 := (u : ℚ).reduced
  have hbez := Int.gcd_eq_gcd_ab (u : ℚ).num ((u : ℚ).den : ℤ)
  rw [hcop] at hbez
  set x := Int.gcdA (u : ℚ).num ((u : ℚ).den : ℤ)
  set y := Int.gcdB (u : ℚ).num ((u : ℚ).den : ℤ)
  have hd : ((u : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (u : ℚ).den_ne_zero
  have hnum : ((u : ℚ).num : ℚ) = u * (u : ℚ).den := (Rat.mul_den_eq_num (u : ℚ)).symm
  have key : b + q / (u : ℚ).den = b + ((q * y : ℤ) : ℚ) + u * ((q * x : ℤ) : ℚ) := by
    have hb' : (1 : ℚ) = (u : ℚ).num * x + (u : ℚ).den * y := by exact_mod_cast hbez
    rw [hnum] at hb'
    have h1 : (q : ℚ) / (u : ℚ).den = q * y + u * (q * x) := by
      rw [div_eq_iff hd]; linear_combination (q : ℚ) * hb'
    push_cast
    rw [h1]; ring
  rw [key, translation_add_mul_dil, hφ.mul_right_eq (hasIntegerSuccessor_int hs _),
    hφ.mul_left_eq (hasIntegerSuccessor_int hs _)]

theorem int_eq_zero_of_mul_lt {m : ℤ} {D : ℕ} {t : ℤ} (hD : 0 < D) (ht : |t| < D)
    (h : m * D = t) : m = 0 := by
  by_contra hm
  have h1 : (D : ℤ) ≤ |m * D| := by
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (by positivity) (Int.one_le_abs hm)
  rw [h] at h1
  omega

theorem int_eq_zero_of_mul_lt' {m N t : ℤ} (ht : |t| < |N|) (h : m * N = t) : m = 0 := by
  by_contra hm
  have h1 : |N| ≤ |m * N| := by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs hm)
  rw [h] at h1
  omega

theorem fin_eq_of_den_eq_one {D : ℕ} (hD : 0 < D) (j j' : Fin D)
    (h : (((j' : ℕ) : ℚ) / D - ((j : ℕ) : ℚ) / D).den = 1) : j = j' := by
  obtain ⟨m, hm⟩ := (den_eq_one_iff_exists _).mp h
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : m * (D : ℤ) = (j' : ℤ) - j := by
    have : (m : ℚ) * D = (j' : ℕ) - (j : ℕ) := by rw [hm]; field_simp
    exact_mod_cast this
  have := int_eq_zero_of_mul_lt hD (by have := j.2; have := j'.2; rw [abs_lt]; constructor <;> omega) hz
  rw [this, zero_mul] at hz
  exact Fin.ext (by omega)

/-- **The integer successor forces the Hecke weight (Bessel form).** For a positive-definite `φ`
on `Aff(ℚ)` with successor part `1_ℤ`, and `u = ±n/d` in lowest terms, the successor-twisted
dilation coefficients over classes of `ℚ/(1/d)ℤ` carry total square mass at most `1/(nd)`. -/
theorem heckeBessel {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (hs : HasIntegerSuccessor φ)
    (u : ℚˣ) {r : ℕ} (b : Fin r → ℚ)
    (hb : ∀ i j, i ≠ j → (((u : ℚ).den : ℚ) * (b i - b j)).den ≠ 1) :
    ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) *
      ∑ i, Complex.normSq (φ (translation (b i) * dilation u)) ≤ 1 := by
  set n := (u : ℚ).num.natAbs with hn_def
  set d := (u : ℚ).den with hd_def
  have hd : 0 < d := (u : ℚ).den_pos
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hn : 0 < n := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)
  have hu0 : (u : ℚ) ≠ 0 := u.ne_zero
  have hnum : ((u : ℚ).num : ℚ) = u * d := (Rat.mul_den_eq_num (u : ℚ)).symm
  set F : Fin r → ℂ := fun i => φ (translation (b i) * dilation u) with hF
  set P : Fin d ⊕ (Fin r × Fin n) → AffineGroupQ :=
    Sum.elim (fun j => translation (((j : ℕ) : ℚ) / d))
      (fun ik => translation (b ik.1 + ((ik.2 : ℕ) : ℚ) / d) * dilation u) with hP
  set C : Fin d ⊕ (Fin r × Fin n) → ℂ :=
    Sum.elim (fun _ => (((1 : ℝ) / d : ℝ) : ℂ)) (fun ik => -star (F ik.1)) with hC
  obtain ⟨R, hR, hsum⟩ := hφ.form P C
  have hinv : ∀ x, φ x⁻¹ = star (φ x) := hφ.map_inv
  -- the four blocks of Gram values
  have v1 : ∀ j j' : Fin d, φ ((P (Sum.inl j))⁻¹ * P (Sum.inl j')) = if j = j' then 1 else 0 := by
    intro j j'
    simp only [hP, Sum.elim_inl, translation_inv_mul]
    rw [hs]
    by_cases hjj : j = j'
    · subst hjj; simp
    · rw [if_neg hjj, if_neg fun h => hjj (fin_eq_of_den_eq_one hd j j' h)]
  have v2 : ∀ (j : Fin d) (ik : Fin r × Fin n),
      φ ((P (Sum.inl j))⁻¹ * P (Sum.inr ik)) = F ik.1 := by
    intro j ik
    simp only [hP, Sum.elim_inl, Sum.elim_inr, translation_inv_mul_tdil]
    have := tdil_periodic hφ hs u (b ik.1) ((ik.2 : ℕ) - (j : ℕ) : ℤ)
    rw [show b ik.1 + ((ik.2 : ℕ) : ℚ) / d - ((j : ℕ) : ℚ) / d =
      b ik.1 + (((ik.2 : ℕ) - (j : ℕ) : ℤ) : ℚ) / d by push_cast; ring]
    exact this
  have v3 : ∀ (ik : Fin r × Fin n) (j : Fin d),
      φ ((P (Sum.inr ik))⁻¹ * P (Sum.inl j)) = star (F ik.1) := by
    intro ik j
    rw [← v2 j ik, ← hinv, mul_inv_rev, inv_inv]
  have v4 : ∀ ik ik' : Fin r × Fin n, φ ((P (Sum.inr ik))⁻¹ * P (Sum.inr ik')) =
      if ik = ik' then 1 else 0 := by
    rintro ⟨i, k⟩ ⟨i', k'⟩
    simp only [hP, Sum.elim_inr, tdil_inv_mul_tdil]
    rw [hs]
    by_cases hik : (i, k) = (i', k')
    · rw [if_pos hik]; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hik; simp
    · rw [if_neg hik, if_neg]
      intro hden
      obtain ⟨m, hm⟩ := (den_eq_one_iff_exists _).mp hden
      have hmu : (m : ℚ) * u = b i' - b i + (((k' : ℕ) : ℚ) - (k : ℕ)) / d := by
        rw [hm]; field_simp; ring
      -- `d (b i' − b i)` is an integer
      have hint : ((d : ℚ) * (b i' - b i)) = ((m * (u : ℚ).num - ((k' : ℕ) - (k : ℕ)) : ℤ) : ℚ) := by
        push_cast
        rw [hnum]
        have : (d : ℚ) * (b i' - b i) = d * ((m : ℚ) * u) - ((k' : ℕ) - (k : ℕ)) := by
          rw [hmu]; field_simp; ring
        rw [this]; ring
      have hii : i' = i := by
        by_contra hne
        exact hb i' i hne (by rw [hint]; exact Rat.den_intCast _)
      subst hii
      have hkk : m * (u : ℚ).num = (k' : ℕ) - (k : ℕ) := by
        have : (m : ℚ) * (u : ℚ).num = (k' : ℕ) - (k : ℕ) := by
          rw [hnum]
          have h2 := hmu
          rw [sub_self, zero_add] at h2
          field_simp at h2 ⊢
          linear_combination h2
        exact_mod_cast this
      have habs : |(u : ℚ).num| = (n : ℤ) := by rw [hn_def, Int.natCast_natAbs]
      have hm0 := int_eq_zero_of_mul_lt' (by
        rw [habs]; have := k.2; have := k'.2; rw [abs_lt]; constructor <;> omega) hkk
      rw [hm0, zero_mul] at hkk
      exact hik (by congr 1; exact Fin.ext (by omega))
  -- evaluate the Gram form block by block
  have hstar : star ((((1 : ℝ) / d : ℝ)) : ℂ) = (((1 : ℝ) / d : ℝ) : ℂ) := Complex.conj_ofReal _
  have hnorm : ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) := fun z => Complex.mul_conj z
  rw [Fintype.sum_sum_type] at hsum
  simp only [Fintype.sum_sum_type, hC, Sum.elim_inl, Sum.elim_inr, v1, v2, v3, v4, hstar,
    star_neg, star_star] at hsum
  have hA : ∑ j : Fin d, ∑ j' : Fin d, (((1 : ℝ) / d : ℝ) : ℂ) * (if j = j' then 1 else 0) *
      (((1 : ℝ) / d : ℝ) : ℂ) = (((1 : ℝ) / d : ℝ) : ℂ) := by
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  set S : ℝ := ∑ i, Complex.normSq (F i) with hS
  have hprod : ∑ ik : Fin r × Fin n, (Complex.normSq (F ik.1) : ℂ) = (n : ℂ) * (S : ℂ) := by
    rw [Fintype.sum_prod_type, hS]
    push_cast
    rw [Finset.mul_sum]
    simp
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hB : ∑ _j : Fin d, ∑ ik : Fin r × Fin n, (((1 : ℝ) / d : ℝ) : ℂ) * F ik.1 * -star (F ik.1) =
      -((n : ℂ) * (S : ℂ)) := by
    have e : ∀ ik : Fin r × Fin n, (((1 : ℝ) / d : ℝ) : ℂ) * F ik.1 * -star (F ik.1) =
        -((((1 : ℝ) / d : ℝ) : ℂ) * (Complex.normSq (F ik.1) : ℂ)) := by
      intro ik; rw [mul_neg, mul_assoc, hnorm]
    simp_rw [e]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_neg_distrib,
      ← Finset.mul_sum, hprod]
    push_cast
    field_simp
  have hC' : ∑ ik : Fin r × Fin n, ∑ _j : Fin d, -F ik.1 * star (F ik.1) *
      (((1 : ℝ) / d : ℝ) : ℂ) = -((n : ℂ) * (S : ℂ)) := by
    have e : ∀ ik : Fin r × Fin n, ∑ _j : Fin d, -F ik.1 * star (F ik.1) * (((1 : ℝ) / d : ℝ) : ℂ) =
        -(Complex.normSq (F ik.1) : ℂ) := by
      intro ik
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, neg_mul, hnorm]
      push_cast
      rw [mul_one_div, mul_div_cancel₀ _ hdC]
    simp_rw [e]
    rw [Finset.sum_neg_distrib, hprod]
  have hD : ∑ ik : Fin r × Fin n, ∑ ik' : Fin r × Fin n, -F ik.1 * (if ik = ik' then 1 else 0) *
      -star (F ik'.1) = (n : ℂ) * (S : ℂ) := by
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, neg_mul_neg, hnorm]
    rw [hprod]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA, hB, hC', hD] at hsum
  have hR' : R = 1 / d - n * S := by
    have e : (((1 : ℝ) / d : ℝ) : ℂ) + -((n : ℂ) * (S : ℂ)) + (-((n : ℂ) * (S : ℂ)) +
        (n : ℂ) * (S : ℂ)) = ((1 / d - n * S : ℝ) : ℂ) := by push_cast; ring
    rw [e] at hsum
    exact (Complex.ofReal_injective hsum).symm
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hR'] at hR
  have : (n : ℝ) * S ≤ 1 / d := by linarith
  calc (n * d : ℝ) * S = d * (n * S) := by ring
    _ ≤ d * (1 / d) := by gcongr
    _ = 1 := by field_simp

/-- **The integer successor forces the Hecke weight**: `|φ(x ↦ ux)|² ≤ 1/(nd)`. -/
theorem normSq_dilation_le {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hs : HasIntegerSuccessor φ) (u : ℚˣ) :
    ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) * Complex.normSq (φ (dilation u)) ≤ 1 := by
  have := heckeBessel hφ hs u (r := 1) (fun _ => 0) fun i j hij => absurd (Subsingleton.elim i j) hij
  simpa [translation_zero] using this

/-! ### No archimedean dilation part meets the integer successor -/

theorem natAbs_num_mul_den_ge (m : ℕ) :
    ((m : ℝ) + 1) ≤ (((m + 2 : ℕ) : ℚ) / ((m + 1 : ℕ) : ℚ)).num.natAbs *
      (((m + 2 : ℕ) : ℚ) / ((m + 1 : ℕ) : ℚ)).den := by
  have hcop : Nat.Coprime ((m + 2 : ℕ) : ℤ).natAbs ((m + 1 : ℕ) : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    rw [show m + 2 = 1 + (m + 1) by ring]
    exact Nat.coprime_add_self_left.mpr (Nat.coprime_one_left _)
  have hden := Rat.den_div_eq_of_coprime (by positivity : (0 : ℤ) < ((m + 1 : ℕ) : ℤ)) hcop
  have hnum := Rat.num_div_eq_of_coprime (by positivity : (0 : ℤ) < ((m + 1 : ℕ) : ℤ)) hcop
  push_cast at hden hnum
  have e : ((((m : ℚ) + 2) / ((m : ℚ) + 1)).den : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hden
  have e' : ((((m : ℚ) + 2) / ((m : ℚ) + 1)).num.natAbs : ℝ) = (m : ℝ) + 2 := by
    rw [hnum]; norm_cast
  push_cast
  rw [e, e']
  nlinarith

/-- **No archimedean dilation part.** If `φ` is positive definite on `Aff(ℚ)` with successor part
`c·1_ℤ` and its dilation part on `ℚ_{>0}` is the restriction of a function continuous at `1`, then
`c = 0`. -/
theorem successor_scale_eq_zero_of_continuousAt {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    {c : ℂ} (hc : ∀ b : ℚ, φ (translation b) = c * if b.den = 1 then 1 else 0)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hfφ : ∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = f (u : ℚ)) : c = 0 := by
  have hc1 : φ 1 = c := by
    have := hc 0; rwa [translation_zero, Rat.den_zero, if_pos rfl, mul_one] at this
  obtain ⟨r0, hr0, h0⟩ := hφ.map_one_eq
  by_contra hc0
  have hr0pos : 0 < r0 := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← hc1, h0, ← h]; simp) hc0
  have hr0C : (r0 : ℂ) ≠ 0 := by exact_mod_cast hr0pos.ne'
  set ψ : AffineGroupQ → ℂ := fun g => φ g / r0 with hψ_def
  have hψ : IsPosDefOnGroup ψ := by
    intro N x e
    obtain ⟨r, hr, h⟩ := hφ N x e
    refine ⟨r / r0, div_nonneg hr hr0pos.le, ?_⟩
    push_cast
    rw [← h, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hψ_def]
    ring
  have hsψ : HasIntegerSuccessor ψ := by
    intro b
    simp only [hψ_def, hc, ← hc1, h0]
    split_ifs <;> field_simp
  -- the dilations `u_m = (m+2)/(m+1) → 1`
  have hu : ∀ m : ℕ, ((m + 2 : ℕ) : ℚ) / ((m + 1 : ℕ) : ℚ) ≠ 0 := fun m => by positivity
  set u : ℕ → ℚˣ := fun m => Units.mk0 _ (hu m) with hu_def
  have hupos : ∀ m, 0 < ((u m : ℚˣ) : ℚ) := fun m => by simp only [hu_def, Units.val_mk0]; positivity
  have hbound : ∀ m : ℕ, Complex.normSq (ψ (dilation (u m))) ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    have h1 := normSq_dilation_le hψ hsψ (u m)
    have h2 := natAbs_num_mul_den_ge m
    simp only [hu_def, Units.val_mk0] at h1
    rw [le_div_iff₀ (by positivity)]
    have := Complex.normSq_nonneg (ψ (dilation (u m)))
    nlinarith
  have hlim_u : Tendsto (fun m : ℕ => (((u m : ℚˣ) : ℚ) : ℝ)) atTop (𝓝 1) := by
    have e : ∀ m : ℕ, (((u m : ℚˣ) : ℚ) : ℝ) = 1 + 1 / ((m : ℝ) + 1) := by
      intro m
      simp only [hu_def, Units.val_mk0]
      push_cast
      field_simp
      ring
    simp_rw [e]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
  have hf1 : f 1 = r0 := by
    have := hfφ 1 (by norm_num)
    rw [map_one, h0] at this
    simpa using this.symm
  have hlim_ψ : Tendsto (fun m : ℕ => ψ (dilation (u m))) atTop (𝓝 1) := by
    have e : ∀ m, ψ (dilation (u m)) = f (((u m : ℚˣ) : ℚ) : ℝ) / r0 := fun m => by
      simp only [hψ_def]; rw [hfφ _ (hupos m)]
    simp_rw [e]
    have := (hf.tendsto.comp hlim_u).div_const (r0 : ℂ)
    rwa [hf1, div_self hr0C] at this
  have h1 : Tendsto (fun m : ℕ => Complex.normSq (ψ (dilation (u m)))) atTop (𝓝 1) := by
    have := (Complex.continuous_normSq.tendsto 1).comp hlim_ψ
    rwa [Complex.normSq_one] at this
  have h2 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := le_of_tendsto_of_tendsto' h1 h2 hbound
  norm_num at this

open ArithmeticCastelnuovoSeveri GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge in
/-- The spline correlation is continuous: it is the Weil functional of the translates of one
admissible kernel. -/
theorem continuous_splineCorr : Continuous splineCorr := by
  have hk := RHTower.WeilSpectral.admissible_weilTest (cx_contDiff contDiff_cubicSpline)
    (cx_hasCompactSupport hasCompactSupport_cubicSpline)
  have e : splineCorr = fun y => RHTower.weilFullFunctional vonMangoldtWeight
      (RHTower.WeilSpectral.transl y (Zeta23.EF.weilTest (cx cubicSpline) (cx cubicSpline))) := by
    funext y
    unfold splineCorr
    congr 1
    funext x
    have := weilTest_translate y 0 (cx cubicSpline) (cx cubicSpline) x
    have h0 : ArithmeticCastelnuovoSeveri.translate 0 (cx cubicSpline) = cx cubicSpline := by
      funext t; simp [ArithmeticCastelnuovoSeveri.translate]
    rw [h0, sub_zero] at this
    rw [this]; rfl
  rw [e]
  exact RHTower.WeilSpectral.continuous_spectralKernel _ hk

/-- **The spline correlation never meets the integer successor.** A positive-definite function on
`Aff(ℚ)` that restricts to the spline correlation on the dilations and to `c·1_ℤ` on the
translations has `c = 0`; then `C(0) = 0`. -/
theorem splineCorr_zero_of_integer_successor {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hdil : ∀ u : posUnits, φ (dilation u) = ratCorr u) {c : ℂ}
    (hc : ∀ b : ℚ, φ (translation b) = c * if b.den = 1 then 1 else 0) :
    c = 0 ∧ splineCorr 0 = 0 := by
  have hcont : ContinuousAt (fun x : ℝ => splineCorr (-Real.log x)) 1 :=
    (continuous_splineCorr.continuousAt).comp
      ((Real.continuousAt_log one_ne_zero).neg)
  have hc0 := successor_scale_eq_zero_of_continuousAt hφ hc hcont fun u hu => by
    rw [hdil ⟨u, hu⟩]; rfl
  refine ⟨hc0, ?_⟩
  have h1 := hdil 1
  rw [OneMemClass.coe_one, map_one] at h1
  have := hc 0
  rw [translation_zero, Rat.den_zero, if_pos rfl, mul_one, hc0] at this
  rw [this] at h1
  have e : ratCorr 1 = splineCorr 0 := by simp [ratCorr, logPos]
  rw [← e, ← h1]

/-! ### Sharpness: the adelic Haar state -/

/-- Residues of one class modulo `L` in a window of `P` consecutive integers, `L ∣ P`. -/
theorem card_Ico_filter_modEq_of_dvd {L P : ℤ} (hL : 0 < L) (hLP : L ∣ P) (hP : 0 ≤ P) (v : ℤ) :
    (#{x ∈ Ico 0 P | x ≡ v [ZMOD L]} : ℤ) = P / L := by
  rw [Int.Ico_filter_modEq_card _ _ hL]
  obtain ⟨t, rfl⟩ := hLP
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have e : (((L * t : ℤ) : ℚ) - v) / L = (t : ℚ) + (-(v : ℚ)) / L := by
    push_cast; field_simp; ring
  have e0 : (((0 : ℤ) : ℚ) - v) / L = (-(v : ℚ)) / L := by push_cast; ring
  rw [e, e0, Int.ceil_intCast_add, add_sub_cancel_right, Int.mul_ediv_cancel_left _ hL.ne']
  have : 0 ≤ t := by
    by_contra h; have h' := not_le.mp h; nlinarith
  exact max_eq_left this

/-- **Counting the intersection of two residue classes** (Chinese remainder with arbitrary
moduli). -/
theorem card_Ico_filter_modEq_and_modEq {m m' P : ℤ} (hm : 0 < m) (hm' : 0 < m') (hP : 0 ≤ P)
    (hdvd : (m.lcm m' : ℤ) ∣ P) (c c' : ℤ) :
    (#{x ∈ Ico 0 P | x ≡ c [ZMOD m] ∧ x ≡ c' [ZMOD m']} : ℤ) =
      if (m.gcd m' : ℤ) ∣ c' - c then P / m.lcm m' else 0 := by
  split_ifs with h
  · obtain ⟨q, hq⟩ := h
    have hbez := Int.gcd_eq_gcd_ab m m'
    set k₀ := c + m * Int.gcdA m m' * q
    have h1 : k₀ ≡ c [ZMOD m] := by
      rw [Int.modEq_iff_dvd]; exact ⟨-(Int.gcdA m m' * q), by simp only [k₀]; ring⟩
    have h2 : k₀ ≡ c' [ZMOD m'] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨Int.gcdB m m' * q, ?_⟩
      have : c' - c = (m * Int.gcdA m m' + m' * Int.gcdB m m') * q := by rw [← hbez]; exact hq
      simp only [k₀]; linear_combination this
    have hset : ({x ∈ Ico 0 P | x ≡ c [ZMOD m] ∧ x ≡ c' [ZMOD m']} : Finset ℤ) =
        {x ∈ Ico 0 P | x ≡ k₀ [ZMOD m.lcm m']} := by
      refine Finset.filter_congr fun x _ => ?_
      rw [← Int.modEq_and_modEq_iff_modEq_lcm]
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨ha.trans h1.symm, hb.trans h2.symm⟩
      · rintro ⟨ha, hb⟩; exact ⟨ha.trans h1, hb.trans h2⟩
    rw [hset]
    exact card_Ico_filter_modEq_of_dvd (by
      have := Int.lcm_pos hm.ne' hm'.ne'; exact_mod_cast this) hdvd hP k₀
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨ha, hb⟩
    apply h
    have g1 : (m.gcd m' : ℤ) ∣ m := Int.gcd_dvd_left m m'
    have g2 : (m.gcd m' : ℤ) ∣ m' := Int.gcd_dvd_right m m'
    have := (Int.ModEq.of_dvd g1 ha).symm.trans (Int.ModEq.of_dvd g2 hb)
    exact (Int.modEq_iff_dvd.mp this)
/-- The **commensurability kernel** of residue classes: `gcd(A,A')/√|AA'|` if the classes
`C + Aℤ`, `C' + A'ℤ` meet, else `0`. -/
noncomputable def commKernel (A C A' C' : ℤ) : ℝ :=
  if (A.gcd A' : ℤ) ∣ C' - C then (A.gcd A' : ℝ) / Real.sqrt (|(A : ℝ)| * |(A' : ℝ)|) else 0

/-- The residue class `C + Aℤ`, weighted by `√|A|`. -/
noncomputable def classVec (A C k : ℤ) : ℝ :=
  if k ≡ C [ZMOD |A|] then Real.sqrt |(A : ℝ)| else 0

theorem classVec_mul (A C A' C' k : ℤ) :
    classVec A C k * classVec A' C' k = Real.sqrt |(A : ℝ)| * Real.sqrt |(A' : ℝ)| *
      (if k ≡ C [ZMOD |A|] ∧ k ≡ C' [ZMOD |A'|] then 1 else 0) := by
  unfold classVec
  by_cases h1 : k ≡ C [ZMOD |A|] <;> by_cases h2 : k ≡ C' [ZMOD |A'|] <;> simp [h1, h2]

/-- The model inner product of two weighted residue classes over a common period is `P` times the
commensurability kernel. -/
theorem sum_classVec_mul {A A' C C' P : ℤ} (hA : A ≠ 0) (hA' : A' ≠ 0) (hP : 0 < P)
    (hdvdA : |A| ∣ P) (hdvdA' : |A'| ∣ P) :
    ∑ k ∈ Ico 0 P, classVec A C k * classVec A' C' k = P * commKernel A C A' C' := by
  have hg : (|A|).gcd |A'| = A.gcd A' := by
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_abs, Int.natAbs_abs]
  have hl : (|A|).lcm |A'| = A.lcm A' := by
    show Nat.lcm (|A|).natAbs (|A'|).natAbs = Nat.lcm A.natAbs A'.natAbs
    rw [Int.natAbs_abs, Int.natAbs_abs]
  have hdvd : ((|A|).lcm |A'| : ℤ) ∣ P := Int.coe_lcm_dvd_iff.mpr ⟨hdvdA, hdvdA'⟩
  have hcount := card_Ico_filter_modEq_and_modEq (abs_pos.mpr hA) (abs_pos.mpr hA') hP.le hdvd C C'
  rw [hg, hl] at hcount
  rw [hl] at hdvd
  simp_rw [classVec_mul]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hc : ((#{k ∈ Ico 0 P | k ≡ C [ZMOD |A|] ∧ k ≡ C' [ZMOD |A'|]} : ℕ) : ℝ) =
      (((#{k ∈ Ico 0 P | k ≡ C [ZMOD |A|] ∧ k ≡ C' [ZMOD |A'|]} : ℕ) : ℤ) : ℝ) := rfl
  rw [hc, hcount]
  unfold commKernel
  have hX : 0 < |(A : ℝ)| * |(A' : ℝ)| := by
    have : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    have : (A' : ℝ) ≠ 0 := by exact_mod_cast hA'
    positivity
  by_cases hdiv : ((A.gcd A' : ℕ) : ℤ) ∣ C' - C
  · rw [if_pos hdiv, if_pos hdiv]
    have hlpos : 0 < A.lcm A' := Int.lcm_pos hA hA'
    rw [Int.cast_div hdvd (by exact_mod_cast hlpos.ne')]
    have hgl : ((A.gcd A' : ℕ) : ℝ) * ((A.lcm A' : ℕ) : ℝ) = |(A : ℝ)| * |(A' : ℝ)| := by
      have h := Int.gcd_mul_lcm A A'
      have h' := congrArg (fun n : ℕ => (n : ℝ)) h
      simp only [Nat.cast_mul] at h'
      rw [h', Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    rw [← Real.sqrt_mul (abs_nonneg _)]
    set s := Real.sqrt (|(A : ℝ)| * |(A' : ℝ)|) with hs_def
    have hs0 : 0 < s := Real.sqrt_pos.mpr hX
    have hss : s * s = |(A : ℝ)| * |(A' : ℝ)| := Real.mul_self_sqrt hX.le
    have hlR : (0 : ℝ) < ((A.lcm A' : ℕ) : ℝ) := by exact_mod_cast hlpos
    simp only [Int.cast_natCast]
    have hsgl : s * s = ((A.gcd A' : ℕ) : ℝ) * ((A.lcm A' : ℕ) : ℝ) := hss.trans hgl.symm
    rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff hlR.ne' hs0.ne']
    linear_combination (P : ℝ) * hsgl
  · rw [if_neg hdiv, if_neg hdiv]; simp

/-- **The commensurability kernel is positive definite**: its Gram form over any family of residue
classes is `P⁻¹ Σ_k |Σ_j c_j w_j(k)|²` on a common period. -/
theorem commKernel_gram {N : ℕ} (A C : Fin N → ℤ) (hA : ∀ i, A i ≠ 0) (c : Fin N → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∑ i, ∑ j, star (c i) * (commKernel (A i) (C i) (A j) (C j) : ℂ) * c j = r := by
  classical
  set P : ℤ := ∏ i, |A i| with hP_def
  have hP0 : 0 < P := Finset.prod_pos fun i _ => abs_pos.mpr (hA i)
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP0
  have hdvd : ∀ i, |A i| ∣ P := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set S : ℤ → ℂ := fun k => ∑ j, c j * (classVec (A j) (C j) k : ℂ) with hS_def
  refine ⟨(1 / P : ℝ) * ∑ k ∈ Ico 0 P, Complex.normSq (S k),
    mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _), ?_⟩
  have hK : ∀ i j, (commKernel (A i) (C i) (A j) (C j) : ℂ) =
      ((1 / P : ℝ) : ℂ) * ∑ k ∈ Ico 0 P,
        ((classVec (A i) (C i) k : ℝ) : ℂ) * ((classVec (A j) (C j) k : ℝ) : ℂ) := by
    intro i j
    have h := sum_classVec_mul (C := C i) (C' := C j) (hA i) (hA j) hP0 (hdvd i) (hdvd j)
    have h' : commKernel (A i) (C i) (A j) (C j) =
        (1 / P : ℝ) * ∑ k ∈ Ico 0 P, classVec (A i) (C i) k * classVec (A j) (C j) k := by
      rw [h]; field_simp
    rw [h']; push_cast; rfl
  simp_rw [hK]
  have hR : ∀ k, (Complex.normSq (S k) : ℂ) = ∑ i, ∑ j,
      star (c i) * ((classVec (A i) (C i) k : ℝ) : ℂ) *
        (((classVec (A j) (C j) k : ℝ) : ℂ) * c j) := by
    intro k
    have hstar : star (S k) = ∑ i, star (c i) * ((classVec (A i) (C i) k : ℝ) : ℂ) := by
      simp only [hS_def, star_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, hstar, hS_def, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  calc ∑ i, ∑ j, star (c i) * (((1 / P : ℝ) : ℂ) * ∑ k ∈ Ico 0 P,
          ((classVec (A i) (C i) k : ℝ) : ℂ) * ((classVec (A j) (C j) k : ℝ) : ℂ)) * c j
      = ∑ i, ∑ j, ∑ k ∈ Ico 0 P, ((1 / P : ℝ) : ℂ) * (star (c i) *
          ((classVec (A i) (C i) k : ℝ) : ℂ) * (((classVec (A j) (C j) k : ℝ) : ℂ) * c j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i, ∑ k ∈ Ico 0 P, ∑ j, ((1 / P : ℝ) : ℂ) * (star (c i) *
          ((classVec (A i) (C i) k : ℝ) : ℂ) * (((classVec (A j) (C j) k : ℝ) : ℂ) * c j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ Ico 0 P, ∑ i, ∑ j, ((1 / P : ℝ) : ℂ) * (star (c i) *
          ((classVec (A i) (C i) k : ℝ) : ℂ) * (((classVec (A j) (C j) k : ℝ) : ℂ) * c j)) :=
        Finset.sum_comm
    _ = (((1 / P : ℝ) * ∑ k ∈ Ico 0 P, Complex.normSq (S k) : ℝ) : ℂ) := by
        push_cast
        simp_rw [hR, Finset.mul_sum]

/-- Lowest terms of `A'/A` for nonzero integers: `A = gμ`, `A' = gμ'`, `g = gcd`, and
`A'/A = (sμ')/|μ|` with `s = sign μ`. -/
theorem lowest_terms_div {A A' : ℤ} (hA : A ≠ 0) :
    ((A' : ℚ) / A).den = (A.natAbs / A.gcd A') ∧
      ((A' : ℚ) / A).num.natAbs = A'.natAbs / A.gcd A' := by
  have hg : 0 < A.gcd A' := Int.gcd_pos_of_ne_zero_left A' hA
  obtain ⟨g, μ, μ', hg0, hcop, rfl, rfl⟩ := Int.exists_gcd_one' hg
  have hgg : (μ * g).gcd (μ' * g) = g := by
    rw [Int.gcd_mul_right, hcop, one_mul, Int.natAbs_natCast]
  have hμ : μ ≠ 0 := by rintro rfl; simp at hA
  have hgq : ((g : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hdiv : ((μ' * g : ℤ) : ℚ) / ((μ * g : ℤ) : ℚ) = ((μ.sign * μ' : ℤ) : ℚ) / ((|μ| : ℤ) : ℚ) := by
    have hμq : (μ : ℚ) ≠ 0 := by exact_mod_cast hμ
    rcases lt_or_gt_of_ne hμ with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg h]; push_cast; field_simp
    · rw [Int.sign_eq_one_of_pos h, abs_of_pos h]; push_cast; field_simp
  have hcop' : Nat.Coprime (μ.sign * μ').natAbs (|μ|).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hμ, one_mul, Int.natAbs_abs]
    exact Nat.Coprime.symm hcop
  have hpos : 0 < |μ| := abs_pos.mpr hμ
  refine ⟨?_, ?_⟩
  · have := Rat.den_div_eq_of_coprime hpos hcop'
    rw [hdiv, hgg, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel _ hg0]
    have h2 : ((((μ.sign * μ' : ℤ) : ℚ) / ((|μ| : ℤ) : ℚ)).den : ℤ) = (μ.natAbs : ℤ) := by
      rw [this, Int.abs_eq_natAbs]
    exact_mod_cast h2
  · have := Rat.num_div_eq_of_coprime hpos hcop'
    rw [hdiv, hgg, this, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hμ, one_mul, Int.natAbs_mul,
      Int.natAbs_natCast, Nat.mul_div_cancel _ hg0]

/-- The shift condition `den(A'/A)·(E/A) ∈ ℤ` is divisibility of `E` by `gcd(A, A')`. -/
theorem den_mul_div_eq_one_iff {A A' : ℤ} (hA : A ≠ 0) (E : ℤ) :
    ((((A' : ℚ) / A).den : ℚ) * ((E : ℚ) / A)).den = 1 ↔ (A.gcd A' : ℤ) ∣ E := by
  have hg : 0 < A.gcd A' := Int.gcd_pos_of_ne_zero_left A' hA
  have hgA : (A.gcd A' : ℤ) ∣ A := Int.gcd_dvd_left A A'
  rw [(lowest_terms_div (A' := A') hA).1]
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hgq : ((A.gcd A' : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have e : (((A.natAbs / A.gcd A' : ℕ) : ℚ)) * ((E : ℚ) / A) =
      ((A.sign * E : ℤ) : ℚ) / ((A.gcd A' : ℤ) : ℚ) := by
    have hnat : ((A.natAbs / A.gcd A' : ℕ) : ℚ) = (A.natAbs : ℚ) / (A.gcd A' : ℕ) := by
      rw [Nat.cast_div (Int.natCast_dvd.mp (by simpa using hgA)) (by exact_mod_cast hg.ne')]
    rw [hnat]
    have habs : (A.natAbs : ℚ) = (A.sign : ℚ) * A := by
      rcases lt_or_gt_of_ne hA with h | h
      · rw [Int.sign_eq_neg_one_of_neg h]; push_cast
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]; ring
      · rw [Int.sign_eq_one_of_pos h]; push_cast
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast h)]; ring
    rw [habs]; push_cast; field_simp
  rw [e, Rat.den_div_intCast_eq_one_iff _ _ (by exact_mod_cast hg.ne')]
  constructor
  · intro h
    have hs : A.sign * A.sign = 1 := by
      rcases lt_or_gt_of_ne hA with h | h
      · rw [Int.sign_eq_neg_one_of_neg h]; rfl
      · rw [Int.sign_eq_one_of_pos h]; rfl
    have := dvd_mul_of_dvd_right h A.sign
    rwa [← mul_assoc, hs, one_mul] at this
  · exact fun h => dvd_mul_of_dvd_right h _

/-- The weight of the **adelic Haar state** `⟨π(g)1_Ẑ, 1_Ẑ⟩`: for `g = (x ↦ ax + b)` with
`a = ±n/d` in lowest terms it is `(nd)^{−1/2}` if `db ∈ ℤ` and `0` otherwise. -/
def haarWeight (g : AffineGroupQ) : ℝ :=
  if (((affSlope g).den : ℚ) * affShift g).den = 1 then
    1 / Real.sqrt ((affSlope g).num.natAbs * (affSlope g).den) else 0

/-- The adelic Haar state. -/
def haarState (g : AffineGroupQ) : ℂ := (haarWeight g : ℂ)

/-- The Haar weight in integer coordinates `a = A'/A`, `b = E/A`:
`gcd(A,A')/√|AA'|` if `gcd(A,A') ∣ E`. -/
theorem haarWeight_of_int {g : AffineGroupQ} {A A' E : ℤ} (hA : A ≠ 0) (hA' : A' ≠ 0)
    (hsl : affSlope g = (A' : ℚ) / A) (hsh : affShift g = (E : ℚ) / A) :
    haarWeight g = if (A.gcd A' : ℤ) ∣ E then
      (A.gcd A' : ℝ) / Real.sqrt (|(A : ℝ)| * |(A' : ℝ)|) else 0 := by
  unfold haarWeight
  rw [hsl, hsh]
  simp only [den_mul_div_eq_one_iff hA E]
  split_ifs with h
  · obtain ⟨hden, hnum⟩ := lowest_terms_div (A' := A') hA
    rw [hden, hnum]
    have hg : 0 < A.gcd A' := Int.gcd_pos_of_ne_zero_left A' hA
    have hgR : (0 : ℝ) < A.gcd A' := by exact_mod_cast hg
    have h1 : ((A.gcd A' : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A A'
    have h2 : ((A.gcd A' : ℕ) : ℤ) ∣ A' := Int.gcd_dvd_right A A'
    have c1 : ((A'.natAbs / A.gcd A' : ℕ) : ℝ) = |(A' : ℝ)| / A.gcd A' := by
      rw [Nat.cast_div (Int.natCast_dvd.mp h2) (by exact_mod_cast hg.ne'), Nat.cast_natAbs,
        Int.cast_abs]
    have c2 : ((A.natAbs / A.gcd A' : ℕ) : ℝ) = |(A : ℝ)| / A.gcd A' := by
      rw [Nat.cast_div (Int.natCast_dvd.mp h1) (by exact_mod_cast hg.ne'), Nat.cast_natAbs,
        Int.cast_abs]
    rw [c1, c2]
    have hX : 0 < |(A : ℝ)| * |(A' : ℝ)| := by
      have : (A : ℝ) ≠ 0 := by exact_mod_cast hA
      have : (A' : ℝ) ≠ 0 := by exact_mod_cast hA'
      positivity
    rw [show |(A' : ℝ)| / A.gcd A' * (|(A : ℝ)| / A.gcd A') =
        (|(A : ℝ)| * |(A' : ℝ)|) / (A.gcd A' : ℝ) ^ 2 by ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hgR.le]
    have : 0 < Real.sqrt (|(A : ℝ)| * |(A' : ℝ)|) := Real.sqrt_pos.mpr hX
    field_simp
  · rfl

/-- **The Haar state is positive definite.** Over a common denominator `D` write
`g_i = (x ↦ (A_i x + C_i)/D)`; then `φ_*(g_i⁻¹g_j)` is the commensurability kernel of the residue
classes `C_i + A_iℤ`, which is a Gram matrix on a common period (`commKernel_gram`). -/
theorem isPosDefOnGroup_haarState : IsPosDefOnGroup haarState := by
  intro N x c
  classical
  set a : Fin N → ℚ := fun i => affSlope (x i) with ha_def
  set b : Fin N → ℚ := fun i => affShift (x i) with hb_def
  set D : ℕ := ∏ i, ((a i).den * (b i).den) with hD_def
  have hD : 0 < D := Finset.prod_pos fun i _ => Nat.mul_pos (a i).den_pos (b i).den_pos
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hint : ∀ q : ℚ, q.den ∣ D → ∃ z : ℤ, (z : ℚ) = D * q := by
    rintro q ⟨t, ht⟩
    refine ⟨t * q.num, ?_⟩
    rw [ht]; push_cast
    rw [mul_comm (q.den : ℚ) t, mul_assoc, Rat.den_mul_eq_num]
  have hdvd_a : ∀ i, (a i).den ∣ D := fun i =>
    (Nat.dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hdvd_b : ∀ i, (b i).den ∣ D := fun i =>
    (Nat.dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  choose A hA using fun i => hint (a i) (hdvd_a i)
  choose C hC using fun i => hint (b i) (hdvd_b i)
  have hA0 : ∀ i, A i ≠ 0 := fun i h => by
    have e := hA i
    rw [h, Int.cast_zero] at e
    rcases mul_eq_zero.mp e.symm with h' | h'
    · exact hDq h'
    · exact affSlope_ne_zero (x i) h'
  have ea : ∀ i, a i = A i / D := fun i => by rw [hA i]; field_simp
  have eb : ∀ i, b i = C i / D := fun i => by rw [hC i]; field_simp
  have key : ∀ i j, haarWeight ((x i)⁻¹ * x j) = commKernel (A i) (C i) (A j) (C j) := by
    intro i j
    have hAi : (A i : ℚ) ≠ 0 := by exact_mod_cast hA0 i
    have hsl : affSlope ((x i)⁻¹ * x j) = (A j : ℚ) / A i := by
      rw [affSlope_mul, affSlope_inv]
      change (a i)⁻¹ * a j = _
      rw [ea i, ea j]
      field_simp
    have hsh : affShift ((x i)⁻¹ * x j) = ((C j - C i : ℤ) : ℚ) / A i := by
      rw [affShift_mul, affShift_inv, affSlope_inv]
      change (a i)⁻¹ * b j + -b i / a i = _
      rw [ea i, eb i, eb j]
      push_cast
      field_simp
      ring
    rw [haarWeight_of_int (hA0 i) (hA0 j) hsl hsh]
    rfl
  obtain ⟨r, hr, h⟩ := commKernel_gram A C hA0 c
  exact ⟨r, hr, by simp only [haarState, key]; exact h⟩

/-- The Haar state has the integer successor. -/
theorem haarState_hasIntegerSuccessor : HasIntegerSuccessor haarState := by
  intro b
  simp only [haarState, haarWeight, affSlope_translation, affShift_translation, Rat.num_one,
    Rat.den_one, Int.natAbs_one, Nat.cast_one, one_mul, mul_one, Real.sqrt_one, div_one]
  split_ifs <;> simp

/-- The Haar state on the dilations is the Hecke weight `(nd)^{−1/2}`. -/
theorem haarState_dilation (u : ℚˣ) :
    haarState (dilation u) =
      ((1 / Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℝ) : ℂ) := by
  simp only [haarState, haarWeight, affSlope_dilation, affShift_dilation, mul_zero, Rat.den_zero,
    ite_true]

/-- **Sharpness**: the Haar state attains the Hecke weight at every dilation. -/
theorem normSq_haarState_dilation (u : ℚˣ) :
    ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) * Complex.normSq (haarState (dilation u)) = 1 := by
  rw [haarState_dilation, Complex.normSq_ofReal]
  have hpos : (0 : ℝ) < (u : ℚ).num.natAbs * (u : ℚ).den := by
    have h1 : 0 < (u : ℚ).num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)
    have h2 : 0 < (u : ℚ).den := (u : ℚ).den_pos
    positivity
  have hs := Real.mul_self_sqrt hpos.le
  have hs0 := Real.sqrt_pos.mpr hpos
  field_simp
  linarith

/-- **The integer successor forces exactly the Hecke weight.** Every positive-definite function on
`Aff(ℚ)` with integer successor satisfies `nd·|φ(x ↦ ux)|² ≤ 1` at `u = ±n/d`, and the adelic
Haar state attains equality at every dilation. -/
theorem integer_successor_hecke_weight :
    (∀ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ → HasIntegerSuccessor φ → ∀ u : ℚˣ,
      ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) * Complex.normSq (φ (dilation u)) ≤ 1) ∧
    ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧ HasIntegerSuccessor φ ∧ ∀ u : ℚˣ,
      ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) * Complex.normSq (φ (dilation u)) = 1 :=
  ⟨fun _ hφ hs u => normSq_dilation_le hφ hs u,
    ⟨haarState, isPosDefOnGroup_haarState, haarState_hasIntegerSuccessor,
      normSq_haarState_dilation⟩⟩

end GaloisForLFunctions.ArithmeticPositiveDuality
