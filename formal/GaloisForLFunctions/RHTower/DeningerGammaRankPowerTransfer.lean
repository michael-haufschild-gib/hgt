import GaloisForLFunctions.RHTower.DeningerArithmeticGammaRankRegular

/-!
# Framed power transfers on the Gamma-rank regular coefficient

On the completed Gamma-rank coefficient `ℓ²(G ⊔ G, ℂ)` the left regular translations `U_a` form
a genuine unitary representation of the group `G`, with `U_a† = U_{a⁻¹}`.  Scaling by the square
root of a degree gives the uncentered framed power pullback and pushforward
`V_n = √n U_a`, `F_n = √n U_{a⁻¹}`.  These satisfy the Milnor--Witt push--pull degree law
`F_n V_n = n·id`, the metric dilation `⟨V_n x, V_n y⟩ = n⟨x,y⟩`, and the cup dilation
`ω(V_n x, V_n y) = n ω(x,y)`; the centered transfer `n^{-1/2} V_n` is the unitary `U_a`.

The invertibility of every `U_a` is a property of the group of rational powers, not of the
multiplicative monoid of positive integers: `deningerPosRat` is the group `ℚ_{>0}^×`, and
`deningerPosRatNat` is the multiplicative embedding of the degrees into it.

* `deningerGammaRankHilbertPowerShift_mul`, `_one`, `_inv` : the representation law.
* `inner_deningerGammaRankHilbertPowerShift_left` : `U_a† = U_{a⁻¹}`.
* `deningerGammaRankCotransfer_transfer` : `F_n V_n = n·id`.
* `inner_deningerGammaRankTransfer` : `⟨V_n x, V_n y⟩ = n⟨x,y⟩`.
* `deningerGammaRankTransfer_centered` : `n^{-1/2} V_n = U_a`.
-/

namespace RHTower

noncomputable section

section HilbertRepresentation

variable {G : Type*}

theorem deningerGammaRankHilbertShift_apply (e : (G ⊕ G) ≃ (G ⊕ G))
    (x : DeningerGammaRankHilbert G) (s : G ⊕ G) :
    deningerGammaRankHilbertShift e x s = x (e.symm s) := rfl

theorem deningerGammaRankHilbertShift_add (e : (G ⊕ G) ≃ (G ⊕ G))
    (x y : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertShift e (x + y) =
      deningerGammaRankHilbertShift e x + deningerGammaRankHilbertShift e y := by
  ext s
  simp [deningerGammaRankHilbertShift_apply]

theorem deningerGammaRankHilbertShift_smul (e : (G ⊕ G) ≃ (G ⊕ G)) (c : ℂ)
    (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertShift e (c • x) = c • deningerGammaRankHilbertShift e x := by
  ext s
  simp [deningerGammaRankHilbertShift_apply]

variable [Group G]

theorem deningerGammaRankHilbertPowerShift_add (a : G) (x y : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertPowerShift a (x + y) =
      deningerGammaRankHilbertPowerShift a x + deningerGammaRankHilbertPowerShift a y :=
  deningerGammaRankHilbertShift_add _ x y

theorem deningerGammaRankHilbertPowerShift_smul (a : G) (c : ℂ)
    (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertPowerShift a (c • x) =
      c • deningerGammaRankHilbertPowerShift a x :=
  deningerGammaRankHilbertShift_smul _ c x

/-- The identity rational power acts trivially on the completed coefficient. -/
@[simp]
theorem deningerGammaRankHilbertPowerShift_one (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertPowerShift (1 : G) x = x := by
  ext s
  cases s <;>
    simp [deningerGammaRankHilbertPowerShift, deningerGammaRankHilbertShift,
      deningerGammaRankHilbertPowerEquiv]

/-- **The completed left regular translations form a representation.** -/
theorem deningerGammaRankHilbertPowerShift_mul (a b : G) (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertPowerShift a (deningerGammaRankHilbertPowerShift b x) =
      deningerGammaRankHilbertPowerShift (a * b : G) x := by
  ext s
  cases s <;>
    simp [deningerGammaRankHilbertPowerShift, deningerGammaRankHilbertShift,
      deningerGammaRankHilbertPowerEquiv, mul_inv_rev, mul_assoc]

/-- Every completed regular translation is invertible: this is where the group of rational
powers, rather than the monoid of positive integers, is essential. -/
@[simp]
theorem deningerGammaRankHilbertPowerShift_inv (a : G) (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertPowerShift a⁻¹ (deningerGammaRankHilbertPowerShift a x) = x := by
  rw [deningerGammaRankHilbertPowerShift_mul, inv_mul_cancel,
    deningerGammaRankHilbertPowerShift_one]

theorem deningerGammaRankHilbertPowerShift_bijective (a : G) :
    Function.Bijective (deningerGammaRankHilbertPowerShift (G := G) a) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨deningerGammaRankHilbertPowerShift a⁻¹,
      deningerGammaRankHilbertPowerShift_inv a,
      fun x => by
        rw [deningerGammaRankHilbertPowerShift_mul, mul_inv_cancel,
          deningerGammaRankHilbertPowerShift_one]⟩

/-- Completed regular translations preserve the Hilbert inner product. -/
theorem inner_deningerGammaRankHilbertPowerShift (a : G)
    (x y : DeningerGammaRankHilbert G) :
    inner ℂ (deningerGammaRankHilbertPowerShift a x)
        (deningerGammaRankHilbertPowerShift a y) = inner ℂ x y :=
  inner_deningerGammaRankHilbertShift _ x y

/-- **The adjoint of a translation is the inverse translation**, `U_a† = U_{a⁻¹}`. -/
theorem inner_deningerGammaRankHilbertPowerShift_left (a : G)
    (x y : DeningerGammaRankHilbert G) :
    inner ℂ (deningerGammaRankHilbertPowerShift a x) y =
      inner ℂ x (deningerGammaRankHilbertPowerShift a⁻¹ y) := by
  have h := inner_deningerGammaRankHilbertPowerShift a⁻¹
    (deningerGammaRankHilbertPowerShift a x) y
  rw [deningerGammaRankHilbertPowerShift_inv] at h
  exact h.symm

end HilbertRepresentation

section PowerTransfer

variable {G : Type*} [Group G]

/-- The uncentered framed power pullback `V_n = √n · U_a`. -/
def deningerGammaRankTransfer (n : ℕ) (a : G) (x : DeningerGammaRankHilbert G) :
    DeningerGammaRankHilbert G :=
  ((Real.sqrt n : ℝ) : ℂ) • deningerGammaRankHilbertPowerShift a x

/-- The uncentered framed power pushforward `F_n = √n · U_{a⁻¹}`. -/
def deningerGammaRankCotransfer (n : ℕ) (a : G) (x : DeningerGammaRankHilbert G) :
    DeningerGammaRankHilbert G :=
  ((Real.sqrt n : ℝ) : ℂ) • deningerGammaRankHilbertPowerShift a⁻¹ x

theorem deningerGammaRankSqrt_mul_self (n : ℕ) :
    ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
  have h : (Real.sqrt n : ℝ) * (Real.sqrt n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg n)
  calc ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ)
      = (((Real.sqrt n : ℝ) * (Real.sqrt n : ℝ) : ℝ) : ℂ) := by push_cast; ring
    _ = ((n : ℝ) : ℂ) := by rw [h]
    _ = (n : ℂ) := by push_cast; ring

/-- **The Milnor--Witt push--pull degree law** `F_n V_n = n·id` on the completed coefficient. -/
theorem deningerGammaRankCotransfer_transfer (n : ℕ) (a : G)
    (x : DeningerGammaRankHilbert G) :
    deningerGammaRankCotransfer n a (deningerGammaRankTransfer n a x) = (n : ℂ) • x := by
  rw [deningerGammaRankCotransfer, deningerGammaRankTransfer,
    deningerGammaRankHilbertPowerShift_smul, smul_smul,
    deningerGammaRankHilbertPowerShift_inv, deningerGammaRankSqrt_mul_self]

/-- **The metric dilation** `⟨V_n x, V_n y⟩ = n⟨x,y⟩`. -/
theorem inner_deningerGammaRankTransfer (n : ℕ) (a : G)
    (x y : DeningerGammaRankHilbert G) :
    inner ℂ (deningerGammaRankTransfer n a x) (deningerGammaRankTransfer n a y) =
      (n : ℂ) * inner ℂ x y := by
  rw [deningerGammaRankTransfer, deningerGammaRankTransfer, inner_smul_left, inner_smul_right,
    inner_deningerGammaRankHilbertPowerShift]
  rw [Complex.conj_ofReal, ← mul_assoc, deningerGammaRankSqrt_mul_self]

/-- **The pushforward is the adjoint of the pullback**, `F_n = V_n†`. -/
theorem deningerGammaRankTransfer_adjoint (n : ℕ) (a : G)
    (x y : DeningerGammaRankHilbert G) :
    inner ℂ (deningerGammaRankTransfer n a x) y =
      inner ℂ x (deningerGammaRankCotransfer n a y) := by
  rw [deningerGammaRankTransfer, deningerGammaRankCotransfer, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_deningerGammaRankHilbertPowerShift_left]

/-- The norm dilation `‖V_n x‖ = √n ‖x‖`. -/
theorem norm_deningerGammaRankTransfer (n : ℕ) (a : G) (x : DeningerGammaRankHilbert G) :
    ‖deningerGammaRankTransfer n a x‖ = Real.sqrt n * ‖x‖ := by
  rw [deningerGammaRankTransfer, norm_smul, deningerGammaRankHilbertPowerShift,
    norm_deningerGammaRankHilbertShift, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **The centered transfer is the unitary translation**, `n^{-1/2} V_n = U_a`. -/
theorem deningerGammaRankTransfer_centered {n : ℕ} (hn : 0 < n) (a : G)
    (x : DeningerGammaRankHilbert G) :
    ((Real.sqrt n : ℝ) : ℂ)⁻¹ • deningerGammaRankTransfer n a x =
      deningerGammaRankHilbertPowerShift a x := by
  have hpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hne : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr hpos.ne')
  rw [deningerGammaRankTransfer, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The framed power transfer commutes with the positive odd Hodge operator. -/
theorem deningerGammaRankHilbertHodge_transfer (n : ℕ) (a : G)
    (x : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertHodge (deningerGammaRankTransfer n a x) =
      deningerGammaRankTransfer n a (deningerGammaRankHilbertHodge x) := by
  have hJ := map_smulₛₗ (deningerGammaRankHilbertHodgeSigma (G := G))
    ((Real.sqrt n : ℝ) : ℂ) (deningerGammaRankHilbertPowerShift a x)
  have hJ' : deningerGammaRankHilbertHodge
      (((Real.sqrt n : ℝ) : ℂ) • deningerGammaRankHilbertPowerShift a x) =
      (starRingEnd ℂ) ((Real.sqrt n : ℝ) : ℂ) •
        deningerGammaRankHilbertHodge (deningerGammaRankHilbertPowerShift a x) := hJ
  rw [deningerGammaRankTransfer, deningerGammaRankTransfer, hJ', Complex.conj_ofReal,
    deningerGammaRankHilbertPowerShift_hodge]

/-- **The cup dilation** `ω(V_n x, V_n y) = n ω(x,y)`. -/
theorem deningerGammaRankHilbertCup_transfer (n : ℕ) (a : G)
    (x y : DeningerGammaRankHilbert G) :
    deningerGammaRankHilbertCup (deningerGammaRankTransfer n a x)
        (deningerGammaRankTransfer n a y) =
      (n : ℂ) * deningerGammaRankHilbertCup x y := by
  simp only [deningerGammaRankTransfer, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [deningerGammaRankHilbertCup_powerShift, ← mul_assoc, deningerGammaRankSqrt_mul_self]

end PowerTransfer

section PositiveRationals

/-- **The Frobenius colimit group** `ℚ_{>0}^×` of positive rational powers. -/
def deningerPosRat : Subgroup ℚˣ where
  carrier := {u : ℚˣ | 0 < (u : ℚ)}
  mul_mem' := by
    intro a b ha hb
    have ha' : 0 < (a : ℚ) := ha
    have hb' : 0 < (b : ℚ) := hb
    show 0 < ((a * b : ℚˣ) : ℚ)
    rw [Units.val_mul]
    exact mul_pos ha' hb'
  one_mem' := by
    show 0 < ((1 : ℚˣ) : ℚ)
    rw [Units.val_one]
    norm_num
  inv_mem' := by
    intro u hu
    have hu' : 0 < (u : ℚ) := hu
    show 0 < ((u⁻¹ : ℚˣ) : ℚ)
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hu'

/-- A positive degree, viewed as a positive rational power. -/
def deningerPosRatNat (n : ℕ) (hn : 0 < n) : deningerPosRat :=
  ⟨Units.mk0 (n : ℚ) (by exact_mod_cast hn.ne'), by
    show 0 < ((Units.mk0 (n : ℚ) (by exact_mod_cast hn.ne') : ℚˣ) : ℚ)
    rw [Units.val_mk0]
    exact_mod_cast hn⟩

@[simp] theorem deningerPosRatNat_val (n : ℕ) (hn : 0 < n) :
    ((((deningerPosRatNat n hn : deningerPosRat) : ℚˣ)) : ℚ) = (n : ℚ) := rfl

/-- **The degrees embed multiplicatively** into the group of rational powers. -/
theorem deningerPosRatNat_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    deningerPosRatNat m hm * deningerPosRatNat n hn
      = deningerPosRatNat (m * n) (Nat.mul_pos hm hn) := by
  refine Subtype.ext (Units.ext ?_)
  show ((((deningerPosRatNat m hm : deningerPosRat) : ℚˣ)) : ℚ)
      * ((((deningerPosRatNat n hn : deningerPosRat) : ℚˣ)) : ℚ) = ((m * n : ℕ) : ℚ)
  rw [deningerPosRatNat_val, deningerPosRatNat_val]
  push_cast
  ring

theorem deningerPosRatNat_one : deningerPosRatNat 1 Nat.one_pos = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show ((((deningerPosRatNat 1 Nat.one_pos : deningerPosRat) : ℚˣ)) : ℚ) = 1
  rw [deningerPosRatNat_val]
  norm_num

/-- **The push--pull degree law over the rational power group.**  On `ℓ²(ℚ_{>0}^× ⊔ ℚ_{>0}^×)`
the framed pushforward composed with the framed pullback of a degree `n` is multiplication by
`n`, with no signature contribution. -/
theorem deningerGammaRankPosRat_pushPull {n : ℕ} (hn : 0 < n)
    (x : DeningerGammaRankHilbert deningerPosRat) :
    deningerGammaRankCotransfer n (deningerPosRatNat n hn)
        (deningerGammaRankTransfer n (deningerPosRatNat n hn) x) = (n : ℂ) • x :=
  deningerGammaRankCotransfer_transfer n _ x

/-- **The metric dilation over the rational power group.** -/
theorem deningerGammaRankPosRat_inner_transfer {n : ℕ} (hn : 0 < n)
    (x y : DeningerGammaRankHilbert deningerPosRat) :
    inner ℂ (deningerGammaRankTransfer n (deningerPosRatNat n hn) x)
        (deningerGammaRankTransfer n (deningerPosRatNat n hn) y) = (n : ℂ) * inner ℂ x y :=
  inner_deningerGammaRankTransfer n _ x y

/-- **The centered transfer over the rational power group is unitary.** -/
theorem deningerGammaRankPosRat_centered_norm {n : ℕ} (hn : 0 < n)
    (x : DeningerGammaRankHilbert deningerPosRat) :
    ‖deningerGammaRankHilbertPowerShift (deningerPosRatNat n hn) x‖ = ‖x‖ :=
  norm_deningerGammaRankHilbertShift _ x

end PositiveRationals

end

end RHTower
