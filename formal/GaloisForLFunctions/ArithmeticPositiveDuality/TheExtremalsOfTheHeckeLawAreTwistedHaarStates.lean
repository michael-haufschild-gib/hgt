import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesTheHeckeWeight

/-!
# The extremals of the Hecke law are twisted Haar states

A positive-definite `φ` on `Aff(ℚ)` with integer successor obeys the Hecke law
`nd·|φ(x ↦ ux)|² ≤ 1` (`normSq_dilation_le`). Call `φ` **Hecke-extremal** if equality holds at
every dilation. Equality is rigid:

* **Classification** (`heckeExtremal_iff`). `φ` is Hecke-extremal iff
  `φ(g) = φ_*(g)·χ(slope g)` for the adelic Haar state `φ_*` and a unitary character `χ` of `ℚ^×`.
* **Mechanism.** Equality kills every successor class `b ∉ (1/d)ℤ` (Parseval form of the law) and
  turns the averages into a **two-scale relation**: the Gram form of
  `[x ↦ x/m] − m⁻¹λ_m Σ_{j<m}[x ↦ x + j/m]`, `λ_m = m·conj φ(x ↦ mx)`, vanishes, so this vector is
  orthogonal to every group element (`IsPosDefOnGroup.null_orth`). Pairing it with dilations gives
  `φ(x ↦ x/(mm')) = φ(x ↦ x/m)φ(x ↦ x/m')` and `φ(x ↦ (n/d)x) = φ(x ↦ nx)φ(x ↦ x/d)` for coprime
  `n, d`: the normalized dilation coefficients form a character.

So the Hecke law has, up to characters, a unique extremal: the integer successor and the critical
weight determine the state.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

section Null

variable {G : Type*} [Group G] {φ : G → ℂ}

/-- A quadratic `r|t|² + 2 Re(t̄D)` nonnegative for every `t` forces `D = 0`. -/
theorem eq_zero_of_forall_quadratic' {r : ℝ} (hr : 0 ≤ r) {D : ℂ}
    (h : ∀ t : ℂ, ∃ q : ℝ, 0 ≤ q ∧ star t * (r : ℂ) * t + star t * D + star D * t = q) : D = 0 := by
  by_contra hD
  have hn : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD
  set s : ℝ := 1 / (r + 1)
  have hs : 0 < s := by positivity
  obtain ⟨q, hq, hqq⟩ := h (-(s : ℂ) * D)
  have e : star (-(s : ℂ) * D) * (r : ℂ) * (-(s : ℂ) * D) + star (-(s : ℂ) * D) * D +
      star D * (-(s : ℂ) * D) = ((s * Complex.normSq D * (s * r - 2) : ℝ) : ℂ) := by
    have hDD : star D * D = (Complex.normSq D : ℂ) := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    have hss : star (s : ℂ) = s := Complex.conj_ofReal s
    rw [star_mul', star_neg, hss]
    push_cast
    linear_combination (s * (s * r - 2) : ℂ) * hDD
  rw [e] at hqq
  have := Complex.ofReal_injective hqq
  have hsr : s * r < 1 := by
    simp only [s]; rw [div_mul_eq_mul_div, one_mul, div_lt_one (by linarith)]; linarith
  nlinarith [mul_pos hs hn]

/-- **Null vectors are orthogonal to everything.** If the Gram form of `Σ c_b [x_b]` vanishes, then
`Σ_b φ(y⁻¹x_b) c_b = 0` for every group element `y`. -/
theorem IsPosDefOnGroup.null_orth (hφ : IsPosDefOnGroup φ) {ι : Type*} [Fintype ι] (x : ι → G)
    (c : ι → ℂ) (hQ : ∑ a, ∑ b, star (c a) * φ ((x a)⁻¹ * x b) * c b = 0) (y : G) :
    ∑ b, φ (y⁻¹ * x b) * c b = 0 := by
  obtain ⟨r0, hr0, h0⟩ := hφ.map_one_eq
  refine eq_zero_of_forall_quadratic' hr0 fun t => ?_
  obtain ⟨q, hq, hqq⟩ := hφ.form (Option.elim · y x) (Option.elim · t c)
  refine ⟨q, hq, ?_⟩
  rw [← hqq, Fintype.sum_option]
  simp only [Fintype.sum_option, Option.elim, inv_mul_cancel, h0, Finset.sum_add_distrib, hQ,
    add_zero]
  have hconj : ∑ a, star (c a) * φ ((x a)⁻¹ * y) * t = star (∑ b, φ (y⁻¹ * x b) * c b) * t := by
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_mul', ← hφ.map_inv, mul_inv_rev, inv_inv]; ring
  rw [hconj, Finset.mul_sum]
  ring_nf

end Null

/-- **Hecke-extremal**: equality in the Hecke law at every dilation. -/
def IsHeckeExtremal (φ : AffineGroupQ → ℂ) : Prop :=
  ∀ u : ℚˣ, ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) * Complex.normSq (φ (dilation u)) = 1

/-- Every affine map is a translation after a dilation. -/
theorem eq_translation_mul_dilation (g : AffineGroupQ) :
    g = translation (affShift g) * dilation (Units.mk0 (affSlope g) (affSlope_ne_zero g)) :=
  affine_ext (by rw [affSlope_mul, affSlope_translation, affSlope_dilation, one_mul]; rfl)
    (by rw [affShift_mul, affSlope_translation, affShift_dilation, affShift_translation]; ring)

section Extremal

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (hs : HasIntegerSuccessor φ)
  (he : IsHeckeExtremal φ)
include hφ hs he

/-- Extremality empties every successor class off `(1/d)ℤ`. -/
theorem extremal_off_class (u : ℚˣ) (b : ℚ) (hb : (((u : ℚ).den : ℚ) * b).den ≠ 1) :
    φ (translation b * dilation u) = 0 := by
  have hbes := heckeBessel hφ hs u (r := 2) ![0, b] (by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [Rat.neg_den, mul_neg] using hb
    · simpa using hb
    · exact absurd rfl hij)
  have h1 := he u
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    translation_zero, one_mul, mul_add] at hbes
  have hpos : (0 : ℝ) < ((u : ℚ).num.natAbs * (u : ℚ).den : ℝ) := by
    have := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)
    have := (u : ℚ).den_pos
    positivity
  have h2 : Complex.normSq (φ (translation b * dilation u)) ≤ 0 := by
    have := Complex.normSq_nonneg (φ (translation b * dilation u))
    nlinarith
  exact Complex.normSq_eq_zero.mp (le_antisymm h2 (Complex.normSq_nonneg _))

omit he in
/-- On the class `(1/d)ℤ` the coefficient is the dilation coefficient. -/
theorem extremal_on_class (u : ℚˣ) (b : ℚ) (hb : (((u : ℚ).den : ℚ) * b).den = 1) :
    φ (translation b * dilation u) = φ (dilation u) := by
  obtain ⟨q, hq⟩ := (den_eq_one_iff_exists _).mp hb
  have hd : ((u : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (u : ℚ).den_ne_zero
  have := tdil_periodic hφ hs u 0 q
  rw [zero_add, translation_zero, one_mul] at this
  rw [show b = (q : ℚ) / (u : ℚ).den by rw [hq]; field_simp]
  exact this

/-- The structure of an extremal: `φ(x ↦ ax + b) = 1[db ∈ ℤ]·φ(x ↦ ax)`. -/
theorem extremal_eq (g : AffineGroupQ) :
    φ g = if (((affSlope g).den : ℚ) * affShift g).den = 1 then
      φ (dilation (Units.mk0 (affSlope g) (affSlope_ne_zero g))) else 0 := by
  conv_lhs => rw [eq_translation_mul_dilation g]
  split_ifs with h
  · exact extremal_on_class hφ hs _ _ h
  · exact extremal_off_class hφ hs he _ _ h

end Extremal

/-! ### The two-scale relations and the character -/

/-- The unit `m ∈ ℚˣ` of a positive integer. -/
def natUnit (m : ℕ) (hm : 0 < m) : ℚˣ := Units.mk0 (m : ℚ) (by exact_mod_cast hm.ne')

section Character

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (hs : HasIntegerSuccessor φ)
  (he : IsHeckeExtremal φ)
include hφ hs he

omit he in
theorem extremal_value (g : AffineGroupQ) (u : ℚˣ) (hsl : affSlope g = u)
    (hsh : (((u : ℚ).den : ℚ) * affShift g).den = 1) : φ g = φ (dilation u) := by
  have hg : g = translation (affShift g) * dilation u := affine_ext
    (by rw [affSlope_mul, affSlope_translation, affSlope_dilation, one_mul, hsl])
    (by rw [affShift_mul, affSlope_translation, affShift_dilation, affShift_translation]; ring)
  rw [hg]
  exact extremal_on_class hφ hs u _ hsh

theorem extremal_value_zero (g : AffineGroupQ) (u : ℚˣ) (hsl : affSlope g = u)
    (hsh : (((u : ℚ).den : ℚ) * affShift g).den ≠ 1) : φ g = 0 := by
  have hg : g = translation (affShift g) * dilation u := affine_ext
    (by rw [affSlope_mul, affSlope_translation, affSlope_dilation, one_mul, hsl])
    (by rw [affShift_mul, affSlope_translation, affShift_dilation, affShift_translation]; ring)
  rw [hg]
  exact extremal_off_class hφ hs he u _ hsh

omit hφ hs in
theorem normSq_natUnit (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * Complex.normSq (φ (dilation (natUnit m hm))) = 1 := by
  have := he (natUnit m hm)
  simpa [natUnit] using this

/-- **The two-scale relation.** For every `y`,
`φ(y⁻¹(x ↦ x/m)) = conj φ(x ↦ mx)·Σ_{j<m} φ(y⁻¹(x ↦ x + j/m))`. -/
theorem two_scale (m : ℕ) (hm : 0 < m) (y : AffineGroupQ) :
    φ (y⁻¹ * dilation (natUnit m hm)⁻¹) =
      star (φ (dilation (natUnit m hm))) * ∑ j : Fin m, φ (y⁻¹ * translation (((j : ℕ) : ℚ) / m)) := by
  set F := φ (dilation (natUnit m hm)) with hF
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  set x : Option (Fin m) → AffineGroupQ :=
    fun o => o.elim (dilation (natUnit m hm)⁻¹) fun j => translation (((j : ℕ) : ℚ) / m) with hx
  set c : Option (Fin m) → ℂ := fun o => o.elim 1 fun _ => -star F with hc
  -- the four kinds of Gram entries
  have e00 : φ ((dilation (natUnit m hm)⁻¹)⁻¹ * dilation (natUnit m hm)⁻¹) = 1 := by
    rw [inv_mul_cancel, hasIntegerSuccessor_one hs]
  have e0j : ∀ j : Fin m, φ ((dilation (natUnit m hm)⁻¹)⁻¹ * translation (((j : ℕ) : ℚ) / m)) = F := by
    intro j
    refine extremal_value hφ hs _ _ ?_ ?_
    · rw [affSlope_mul, affSlope_inv, affSlope_dilation, affSlope_translation]; simp
    · rw [affShift_mul, affShift_inv, affSlope_dilation, affShift_dilation, affShift_translation,
        affSlope_inv, affSlope_dilation]
      simp only [natUnit, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv, neg_zero, zero_div,
        add_zero]
      rw [show (m : ℚ) * (((j : ℕ) : ℚ) / m) = (((j : ℕ) : ℤ) : ℚ) by push_cast; field_simp]
      simp
  have hFinv : φ (dilation (natUnit m hm)⁻¹) = star F := by rw [map_inv, hφ.map_inv]
  have ej0 : ∀ j : Fin m, φ ((translation (((j : ℕ) : ℚ) / m))⁻¹ * dilation (natUnit m hm)⁻¹) =
      star F := by
    intro j
    rw [← hFinv]
    refine extremal_value hφ hs _ _ ?_ ?_
    · rw [affSlope_mul, affSlope_inv, affSlope_translation, affSlope_dilation]; simp
    · rw [affShift_mul, affShift_inv, affSlope_translation, affShift_translation, affShift_dilation]
      simp only [natUnit, Units.val_inv_eq_inv_val, Units.val_mk0, div_one, mul_zero,
        zero_add, Rat.inv_natCast_den, if_neg hm.ne']
      rw [show ((m : ℕ) : ℚ) * -(((j : ℕ) : ℚ) / m) = ((-(j : ℕ) : ℤ) : ℚ) by push_cast; field_simp]
      simp
  have ejj : ∀ j j' : Fin m, φ ((translation (((j : ℕ) : ℚ) / m))⁻¹ * translation (((j' : ℕ) : ℚ) / m)) =
      if j = j' then 1 else 0 := by
    intro j j'
    rw [translation_inv_mul, hs]
    by_cases hjj : j = j'
    · subst hjj; simp
    · rw [if_neg hjj, if_neg fun h => hjj (fin_eq_of_den_eq_one hm j j' h)]
  -- the Gram form of the two-scale vector vanishes
  have hQ : ∑ a, ∑ b, star (c a) * φ ((x a)⁻¹ * x b) * c b = 0 := by
    have hnorm : (m : ℝ) * Complex.normSq F = 1 := normSq_natUnit he m hm
    have hFF : F * star F = (Complex.normSq F : ℂ) := by rw [Complex.star_def, Complex.mul_conj]
    have hn' : (m : ℂ) * (Complex.normSq F : ℂ) = 1 := by exact_mod_cast hnorm
    simp only [Fintype.sum_option, hx, hc, Option.elim, e00, e0j, ej0, ejj, Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      star_neg, star_star, star_one, one_mul]
    linear_combination (-(m : ℂ)) * hFF - hn'
  have hnull := hφ.null_orth x c hQ y
  simp only [Fintype.sum_option, hx, hc, Option.elim, mul_one, mul_neg, Finset.sum_neg_distrib,
    ← Finset.sum_mul] at hnull
  linear_combination hnull

/-- Unit-dilation multiplicativity: `φ(x ↦ x/(mm')) = φ(x ↦ x/m)·φ(x ↦ x/m')`. -/
theorem dil_inv_nat_mul (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') :
    φ (dilation (natUnit (m * m') (Nat.mul_pos hm hm'))⁻¹) =
      φ (dilation (natUnit m hm)⁻¹) * φ (dilation (natUnit m' hm')⁻¹) := by
  have h := two_scale hφ hs he m hm (dilation (natUnit m' hm'))
  have hu : (dilation (natUnit m' hm'))⁻¹ * dilation (natUnit m hm)⁻¹ =
      dilation (natUnit (m * m') (Nat.mul_pos hm hm'))⁻¹ := by
    rw [← map_inv, ← map_mul]; congr 1; ext; simp [natUnit, mul_comm]
  rw [hu] at h
  have hst : star (φ (dilation (natUnit m hm))) = φ (dilation (natUnit m hm)⁻¹) := by
    rw [map_inv, hφ.map_inv]
  rw [h, hst]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmq' : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · congr 1
    rw [show ((0 : ℕ) : ℚ) / m = 0 by simp, translation_zero, mul_one, map_inv]
  · intro j _ hj
    refine extremal_value_zero hφ hs he _ (natUnit m' hm')⁻¹ ?_ ?_
    · rw [affSlope_mul, ← map_inv, affSlope_dilation, affSlope_translation, mul_one]
    · rw [affShift_mul, ← map_inv, affSlope_dilation, affShift_translation, affShift_dilation,
        add_zero]
      simp only [natUnit, Units.val_inv_eq_inv_val, Units.val_mk0, Rat.inv_natCast_den,
        if_neg hm'.ne']
      rw [show (m' : ℚ) * ((m' : ℚ)⁻¹ * (((j : ℕ) : ℚ) / m)) = ((j : ℕ) : ℚ) / m by field_simp,
        Ne, Rat.den_div_natCast_eq_one_iff _ _ hm.ne']
      intro hdvd
      apply hj
      exact Fin.ext (Nat.eq_zero_of_dvd_of_lt hdvd j.2)
  · intro h0; exact absurd (Finset.mem_univ _) h0

/-- Coprime factorization: `φ(x ↦ (n/d)x) = φ(x ↦ nx)·φ(x ↦ x/d)` for coprime `n, d`. -/
theorem dil_coprime (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hcop : n.Coprime d) :
    φ (dilation (natUnit n hn * (natUnit d hd)⁻¹)) =
      φ (dilation (natUnit n hn)) * φ (dilation (natUnit d hd)⁻¹) := by
  have h := two_scale hφ hs he d hd (dilation (natUnit n hn))⁻¹
  rw [inv_inv, ← map_mul] at h
  have hst : star (φ (dilation (natUnit d hd))) = φ (dilation (natUnit d hd)⁻¹) := by
    rw [map_inv, hφ.map_inv]
  rw [h, hst]
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · rw [mul_comm]
    congr 1
    rw [show ((0 : ℕ) : ℚ) / d = 0 by simp, translation_zero, mul_one]
  · intro j _ hj
    refine extremal_value_zero hφ hs he _ (natUnit n hn) ?_ ?_
    · rw [affSlope_mul, affSlope_dilation, affSlope_translation, mul_one]
    · rw [affShift_mul, affSlope_dilation, affShift_translation, affShift_dilation, add_zero]
      simp only [natUnit, Units.val_mk0, Rat.den_natCast, Nat.cast_one, one_mul]
      rw [show (n : ℚ) * (((j : ℕ) : ℚ) / d) = ((n * (j : ℕ) : ℕ) : ℚ) / d by push_cast; ring,
        Ne, Rat.den_div_natCast_eq_one_iff _ _ hd.ne']
      intro hdvd
      apply hj
      exact Fin.ext (Nat.eq_zero_of_dvd_of_lt (hcop.symm.dvd_of_dvd_mul_left hdvd) j.2)
  · intro h0; exact absurd (Finset.mem_univ _) h0

/-- The sign: `φ(x ↦ −ux) = φ(x ↦ −x)·φ(x ↦ ux)`. -/
theorem dil_neg (u : ℚˣ) : φ (dilation (-u)) = φ (dilation (-1)) * φ (dilation u) := by
  set f := φ (dilation (-1)) with hf
  have hinv1 : (dilation (-1 : ℚˣ))⁻¹ = dilation (-1) := by rw [← map_inv, inv_neg, inv_one]
  have hreal : star f = f := by rw [hf, ← hφ.map_inv, hinv1]
  have hsq1 : dilation (-1 : ℚˣ) * dilation (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hnorm : f * f = 1 := by
    have h := he (-1)
    simp only [Units.val_neg, Units.val_one, Rat.neg_num, Rat.num_one, Int.natAbs_neg,
      Int.natAbs_one, Rat.neg_den, Rat.den_one, Nat.cast_one, one_mul] at h
    have hFF : f * star f = (Complex.normSq f : ℂ) := by rw [Complex.star_def, Complex.mul_conj]
    rw [hreal] at hFF
    rw [hFF, h, Complex.ofReal_one]
  have hQ : ∑ a, ∑ b, star (![1, -f] a) * φ ((![dilation (-1), 1] a)⁻¹ * ![dilation (-1), 1] b) *
      ![1, -f] b = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      inv_one, one_mul, mul_one, hinv1, hsq1, hasIntegerSuccessor_one hs, star_one,
      star_neg, hreal]
    linear_combination (-1 : ℂ) * hnorm
  have h := hφ.null_orth ![dilation (-1), 1] ![1, -f] hQ (dilation u)⁻¹
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_inv, mul_one] at h
  rw [← map_mul, show u * -1 = -u by simp] at h
  linear_combination h

end Character

/-! ### The character of an extremal -/

/-- The normalized dilation coefficient `χ(u) = φ(x ↦ ux)·√(nd)`. -/
def heckeChar (φ : AffineGroupQ → ℂ) (u : ℚˣ) : ℂ :=
  φ (dilation u) * (Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℂ)

/-- `nd` of a unit, as a positive real. -/
theorem heckeIndex_pos (u : ℚˣ) : (0 : ℝ) < (u : ℚ).num.natAbs * (u : ℚ).den := by
  have := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)
  have := (u : ℚ).den_pos
  positivity

theorem heckeIndex_inv (u : ℚˣ) :
    (((u⁻¹ : ℚˣ) : ℚ).num.natAbs * ((u⁻¹ : ℚˣ) : ℚ).den : ℝ) =
      (u : ℚ).num.natAbs * (u : ℚ).den := by
  simp only [Units.val_inv_eq_inv_val, Rat.num_inv, Rat.den_inv, Int.natAbs_mul,
    Int.natAbs_sign_of_ne_zero (Rat.num_ne_zero.mpr u.ne_zero), one_mul, Int.natAbs_natCast,
    if_neg (Rat.num_ne_zero.mpr u.ne_zero)]
  ring

theorem heckeIndex_neg (u : ℚˣ) :
    ((((-u : ℚˣ) : ℚ)).num.natAbs * (((-u : ℚˣ) : ℚ)).den : ℝ) =
      (u : ℚ).num.natAbs * (u : ℚ).den := by
  simp [Rat.neg_den]

theorem heckeIndex_natUnit (m : ℕ) (hm : 0 < m) :
    (((natUnit m hm : ℚˣ) : ℚ).num.natAbs * ((natUnit m hm : ℚˣ) : ℚ).den : ℝ) = m := by
  simp [natUnit]

theorem heckeIndex_natUnit_inv (m : ℕ) (hm : 0 < m) :
    ((((natUnit m hm)⁻¹ : ℚˣ) : ℚ).num.natAbs * (((natUnit m hm)⁻¹ : ℚˣ) : ℚ).den : ℝ) = m := by
  rw [heckeIndex_inv, heckeIndex_natUnit]

/-- A positive unit is `|num|/den`. -/
theorem eq_natUnit_div (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    u = natUnit (u : ℚ).num.natAbs (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)) *
      (natUnit (u : ℚ).den (u : ℚ).den_pos)⁻¹ := by
  ext
  simp only [natUnit, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hnum : ((u : ℚ).num.natAbs : ℚ) = (u : ℚ).num := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast Rat.num_pos.mpr hu)]
  rw [hnum, ← div_eq_mul_inv, Rat.num_div_den]

section CharacterLaws

variable {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) (hs : HasIntegerSuccessor φ)
  (he : IsHeckeExtremal φ)
include hφ hs he

omit hφ hs in
theorem heckeChar_mul_star (u : ℚˣ) : heckeChar φ u * star (heckeChar φ u) = 1 := by
  have h := he u
  unfold heckeChar
  rw [star_mul', show star ((Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℝ) : ℂ) =
    (Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℂ) from Complex.conj_ofReal _]
  have hFF : φ (dilation u) * star (φ (dilation u)) = (Complex.normSq (φ (dilation u)) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have hsq := Real.mul_self_sqrt (heckeIndex_pos u).le
  calc φ (dilation u) * (Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℂ) *
        (star (φ (dilation u)) * (Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℂ))
      = (φ (dilation u) * star (φ (dilation u))) *
        ((Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) *
          Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℝ) : ℂ) := by push_cast; ring
    _ = 1 := by rw [hFF, hsq, ← Complex.ofReal_mul, mul_comm, h, Complex.ofReal_one]

omit hs he in
theorem heckeChar_inv (u : ℚˣ) : heckeChar φ u⁻¹ = star (heckeChar φ u) := by
  unfold heckeChar
  rw [map_inv, hφ.map_inv, heckeIndex_inv, star_mul', show star ((Real.sqrt
    ((u : ℚ).num.natAbs * (u : ℚ).den) : ℝ) : ℂ) =
    (Real.sqrt ((u : ℚ).num.natAbs * (u : ℚ).den) : ℂ) from Complex.conj_ofReal _]

theorem heckeChar_natUnit_mul (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') :
    heckeChar φ (natUnit (m * m') (Nat.mul_pos hm hm')) =
      heckeChar φ (natUnit m hm) * heckeChar φ (natUnit m' hm') := by
  have hinv : ∀ (k : ℕ) (hk : 0 < k), heckeChar φ (natUnit k hk) =
      star (heckeChar φ (natUnit k hk)⁻¹) := fun k hk => by
    rw [heckeChar_inv hφ, star_star]
  rw [hinv, hinv m hm, hinv m' hm', ← star_mul]
  congr 1
  unfold heckeChar
  rw [dil_inv_nat_mul hφ hs he m m' hm hm', heckeIndex_natUnit_inv, heckeIndex_natUnit_inv,
    heckeIndex_natUnit_inv]
  push_cast
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  push_cast; ring

theorem heckeChar_coprime (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hcop : n.Coprime d) :
    heckeChar φ (natUnit n hn * (natUnit d hd)⁻¹) =
      heckeChar φ (natUnit n hn) * heckeChar φ (natUnit d hd)⁻¹ := by
  unfold heckeChar
  rw [dil_coprime hφ hs he n d hn hd hcop, heckeIndex_natUnit, heckeIndex_natUnit_inv]
  have hidx : ((((natUnit n hn * (natUnit d hd)⁻¹ : ℚˣ)) : ℚ).num.natAbs *
      (((natUnit n hn * (natUnit d hd)⁻¹ : ℚˣ)) : ℚ).den : ℝ) = n * d := by
    have hval : (((natUnit n hn * (natUnit d hd)⁻¹ : ℚˣ)) : ℚ) = ((n : ℤ) : ℚ) / ((d : ℤ) : ℚ) := by
      simp [natUnit, div_eq_mul_inv]
    have hc : Nat.Coprime (n : ℤ).natAbs (d : ℤ).natAbs := by simpa using hcop
    have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
    rw [hval, Rat.num_div_eq_of_coprime hdpos hc]
    have := Rat.den_div_eq_of_coprime hdpos hc
    have hden : ((((n : ℤ) : ℚ) / ((d : ℤ) : ℚ)).den : ℝ) = d := by exact_mod_cast this
    rw [hden]; simp
  rw [hidx, Real.sqrt_mul (Nat.cast_nonneg _)]
  push_cast; ring

theorem heckeChar_neg (u : ℚˣ) : heckeChar φ (-u) = heckeChar φ (-1) * heckeChar φ u := by
  unfold heckeChar
  rw [dil_neg hφ hs he u, heckeIndex_neg, show ((((-1 : ℚˣ)) : ℚ).num.natAbs *
    ((((-1 : ℚˣ)) : ℚ)).den : ℝ) = 1 by simp, Real.sqrt_one, Complex.ofReal_one, mul_one]
  ring

omit hs in
theorem heckeChar_neg_one_sq : heckeChar φ (-1) * heckeChar φ (-1) = 1 := by
  have h := heckeChar_mul_star he (-1)
  rwa [← heckeChar_inv hφ, inv_neg, inv_one] at h

/-- Representation independence: `χ(a/b) = χ(a)·χ(1/b)` for all positive integers `a, b`. -/
theorem heckeChar_div (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    heckeChar φ (natUnit a ha * (natUnit b hb)⁻¹) =
      heckeChar φ (natUnit a ha) * heckeChar φ (natUnit b hb)⁻¹ := by
  obtain ⟨g, n, d, hg, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left b ha)
  have hn : 0 < n := Nat.pos_of_mul_pos_right ha
  have hd : 0 < d := Nat.pos_of_mul_pos_right hb
  have hu : natUnit (n * g) ha * (natUnit (d * g) hb)⁻¹ = natUnit n hn * (natUnit d hd)⁻¹ := by
    ext; simp only [natUnit, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    push_cast
    have : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    field_simp
  rw [hu, heckeChar_coprime hφ hs he n d hn hd hcop]
  rw [show natUnit (n * g) ha = natUnit (n * g) (Nat.mul_pos hn hg) from rfl,
    heckeChar_natUnit_mul hφ hs he n g hn hg]
  have hdg := heckeChar_natUnit_mul hφ hs he d g hd hg
  have hinv' : heckeChar φ (natUnit (d * g) hb)⁻¹ =
      heckeChar φ (natUnit d hd)⁻¹ * heckeChar φ (natUnit g hg)⁻¹ := by
    rw [heckeChar_inv hφ, heckeChar_inv hφ, heckeChar_inv hφ, ← star_mul]
    congr 1
    rw [show natUnit (d * g) hb = natUnit (d * g) (Nat.mul_pos hd hg) from rfl, hdg, mul_comm]
  rw [hinv']
  have hg1 : heckeChar φ (natUnit g hg) * heckeChar φ (natUnit g hg)⁻¹ = 1 := by
    rw [heckeChar_inv hφ]; exact heckeChar_mul_star he _
  linear_combination (-(heckeChar φ (natUnit n hn) * heckeChar φ (natUnit d hd)⁻¹)) * hg1

theorem heckeChar_mul_pos (u v : ℚˣ) (hu : 0 < (u : ℚ)) (hv : 0 < (v : ℚ)) :
    heckeChar φ (u * v) = heckeChar φ u * heckeChar φ v := by
  set a := (u : ℚ).num.natAbs
  set b := (u : ℚ).den
  set a' := (v : ℚ).num.natAbs
  set b' := (v : ℚ).den
  have ha : 0 < a := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr u.ne_zero)
  have ha' : 0 < a' := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr v.ne_zero)
  have hb : 0 < b := (u : ℚ).den_pos
  have hb' : 0 < b' := (v : ℚ).den_pos
  have huv : u * v = natUnit (a * a') (Nat.mul_pos ha ha') * (natUnit (b * b') (Nat.mul_pos hb hb'))⁻¹ := by
    conv_lhs => rw [eq_natUnit_div u hu, eq_natUnit_div v hv]
    ext; simp only [natUnit, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]; push_cast
    ring
  rw [huv, heckeChar_div hφ hs he, heckeChar_natUnit_mul hφ hs he a a' ha ha']
  have hinvbb : heckeChar φ (natUnit (b * b') (Nat.mul_pos hb hb'))⁻¹ =
      heckeChar φ (natUnit b hb)⁻¹ * heckeChar φ (natUnit b' hb')⁻¹ := by
    rw [heckeChar_inv hφ, heckeChar_inv hφ, heckeChar_inv hφ, ← star_mul,
      heckeChar_natUnit_mul hφ hs he b b' hb hb', mul_comm]
  rw [hinvbb]
  conv_rhs => rw [eq_natUnit_div u hu, eq_natUnit_div v hv, heckeChar_div hφ hs he,
    heckeChar_div hφ hs he]
  ring

theorem heckeChar_mul (u v : ℚˣ) : heckeChar φ (u * v) = heckeChar φ u * heckeChar φ v := by
  have hsq := heckeChar_neg_one_sq hφ he
  have hneg := heckeChar_neg hφ hs he
  have flip : ∀ w, heckeChar φ w = heckeChar φ (-1) * heckeChar φ (-w) := fun w => by
    rw [← hneg, neg_neg]
  have key : ∀ w : ℚˣ, 0 < (w : ℚ) ∨ 0 < ((-w : ℚˣ) : ℚ) := fun w => by
    rcases lt_or_gt_of_ne w.ne_zero with h | h
    · right; simpa using h
    · left; exact h
  rcases key u with hu | hu <;> rcases key v with hv | hv
  · exact heckeChar_mul_pos hφ hs he u v hu hv
  · rw [flip (u * v), flip v, show -(u * v) = u * -v by simp,
      heckeChar_mul_pos hφ hs he u (-v) hu hv]
    ring
  · rw [flip (u * v), flip u, show -(u * v) = -u * v by simp,
      heckeChar_mul_pos hφ hs he (-u) v hu hv]
    ring
  · rw [show u * v = -u * -v by simp, heckeChar_mul_pos hφ hs he (-u) (-v) hu hv, flip u, flip v]
    linear_combination (-(heckeChar φ (-u) * heckeChar φ (-v))) * hsq

end CharacterLaws

/-! ### The classification -/

/-- The Haar state twisted by a character of `ℚ^×`. -/
def twistedHaar (χ : ℚˣ →* ℂ) (g : AffineGroupQ) : ℂ :=
  haarState g * χ (Units.mk0 (affSlope g) (affSlope_ne_zero g))

theorem twistedHaar_posDef (χ : ℚˣ →* ℂ) (hχ : ∀ u, χ u * star (χ u) = 1) :
    IsPosDefOnGroup (twistedHaar χ) := by
  intro N x c
  obtain ⟨r, hr, h⟩ := isPosDefOnGroup_haarState N x
    fun b => c b * χ (Units.mk0 (affSlope (x b)) (affSlope_ne_zero _))
  refine ⟨r, hr, ?_⟩
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hsl : Units.mk0 (affSlope ((x a)⁻¹ * x b)) (affSlope_ne_zero _) =
      (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))⁻¹ *
        Units.mk0 (affSlope (x b)) (affSlope_ne_zero _) := by
    ext; simp [affSlope_mul, affSlope_inv]
  have hinvχ : χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))⁻¹ =
      star (χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))) := by
    have h1 := hχ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))
    have h2 : χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))⁻¹ *
        χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _)) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))⁻¹
        = χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))⁻¹ *
            (χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _)) *
              star (χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _)))) := by rw [h1, mul_one]
      _ = (χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))⁻¹ *
            χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))) *
              star (χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))) := by ring
      _ = star (χ (Units.mk0 (affSlope (x a)) (affSlope_ne_zero _))) := by rw [h2, one_mul]
  unfold twistedHaar
  rw [hsl, map_mul, hinvχ, star_mul']
  ring

/-- **Classification of the Hecke extremals.** A positive-definite function on `Aff(ℚ)` with
integer successor attains the Hecke law at every dilation iff it is the adelic Haar state twisted by
a unitary character of `ℚ^×`. -/
theorem heckeExtremal_iff {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ)
    (hs : HasIntegerSuccessor φ) :
    IsHeckeExtremal φ ↔
      ∃ χ : ℚˣ →* ℂ, (∀ u, χ u * star (χ u) = 1) ∧ ∀ g, φ g = twistedHaar χ g := by
  constructor
  · intro he
    refine ⟨⟨⟨heckeChar φ, ?_⟩, heckeChar_mul hφ hs he⟩, heckeChar_mul_star he, fun g => ?_⟩
    · simp [heckeChar, hasIntegerSuccessor_one hs]
    · simp only [twistedHaar, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [extremal_eq hφ hs he g]
      unfold haarState haarWeight heckeChar
      split_ifs with h
      · set u := Units.mk0 (affSlope g) (affSlope_ne_zero g)
        have hu : (u : ℚ) = affSlope g := rfl
        rw [← hu]
        have hs0 := Real.sqrt_pos.mpr (heckeIndex_pos u)
        push_cast
        field_simp
      · simp
  · rintro ⟨χ, hχ, hφχ⟩ u
    have hu : Units.mk0 (affSlope (dilation u)) (affSlope_ne_zero _) = u := by
      ext; simp [affSlope_dilation]
    have hnorm : Complex.normSq (χ u) = 1 := by
      have := hχ u
      rw [Complex.star_def, Complex.mul_conj] at this
      exact_mod_cast this
    rw [hφχ, twistedHaar, Complex.normSq_mul, hu, hnorm, mul_one]
    exact normSq_haarState_dilation u

end GaloisForLFunctions.ArithmeticPositiveDuality
