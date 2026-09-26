import GaloisForLFunctions.RHTower.HalfWeightTwistedForcedZero

/-!
# Inversion of the twisted theta series

For a Dirichlet character `ψ ≠ 1` modulo a prime `q` and `Im z > 0`,
`Σ_n ψ(n) e(n²z) = τ(ψ) (-2iq²z)^{-1/2} Σ_n ψ̄(n) e(-n²/(4q²z))`,
where `τ(ψ)` is the Gauss sum. The proof splits `n = mq + r`, applies Poisson summation in each
residue class, and evaluates `Σ_r ψ(r) e(rn/q) = ψ̄(n) τ(ψ)` by primitivity.

For the twisted theta function `θ_χ(z) = Σ_a χ̄(a) θ(z + a/q) = τ(χ̄) Σ_n χ²(n) e(n²z)` with
`χ² ≠ 1`, this gives the Fricke inversion
`τ(χ) θ_χ(z) = τ(χ̄) τ(χ²) (-2iq²z)^{-1/2} θ_χ̄(-1/(4q²z))`, the source of the root number in the
functional equation of the twisted symmetric-square family.
-/

open Complex
open scoped Real

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

section Inversion

variable {q : ℕ} [hq : Fact q.Prime] (ψ : DirichletCharacter ℂ q)

omit hq in
theorem poisson_exponent {q r : ℕ} (n : ℤ) {z : ℂ} (hq0 : (q : ℂ) ≠ 0) (hz0 : z ≠ 0) :
    2 * π * I * (r : ℂ) ^ 2 * z + -π / (-2 * I * (q : ℂ) ^ 2 * z) * ((n : ℂ) + I * (2 * I * q * r * z)) ^ 2 =
      2 * π * I * (n : ℂ) ^ 2 * (-1 / (4 * (q : ℂ) ^ 2 * z)) + 2 * π * I * (r : ℂ) * n / q := by
  have hI : I * (2 * I * q * r * z) = -(2 * q * r * z) := by
    ring_nf; rw [I_sq]; ring
  rw [hI]
  have hI0 : I ≠ 0 := I_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring_nf

/-- One residue class `n ≡ r (mod q)` of `Σ_n e(n²z)`, by Poisson summation:
`Σ_m e((mq + r)² z) = (-2iq²z)^{-1/2} Σ_n e(-n²/(4q²z)) e(rn/q)`. -/
theorem residue_class_poisson {z : ℂ} (hz : 0 < z.im) (r : ℕ) :
    ∑' m : ℤ, cexp (2 * π * I * (((m * q + r : ℤ)) : ℂ) ^ 2 * z) =
      1 / (-2 * I * (q : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) ^ 2 * (-1 / (4 * (q : ℂ) ^ 2 * z))) *
          cexp (2 * π * I * (r : ℂ) * n / q) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  set a : ℂ := -2 * I * (q : ℂ) ^ 2 * z with ha
  have hare : 0 < a.re := by
    have ha' : a = (((2 * (q : ℝ) ^ 2) : ℝ) : ℂ) * (-I * z) := by rw [ha]; push_cast; ring
    rw [ha', Complex.re_ofReal_mul]
    have : (-I * z).re = z.im := by simp
    rw [this]; have : (0 : ℝ) < q := by exact_mod_cast hq.out.pos
    positivity
  have ha0 : a ≠ 0 := fun h => by rw [h] at hare; simp at hare
  have key := Complex.tsum_exp_neg_quadratic hare (2 * I * q * r * z)
  have e1 : ∀ m : ℤ, cexp (2 * π * I * (((m * q + r : ℤ)) : ℂ) ^ 2 * z) =
      cexp (2 * π * I * (r : ℂ) ^ 2 * z) *
        cexp (-π * a * (m : ℂ) ^ 2 + 2 * π * (2 * I * q * r * z) * m) := by
    intro m
    rw [← Complex.exp_add]; congr 1; simp only [ha]; push_cast; ring_nf
  simp_rw [e1]
  rw [tsum_mul_left, key, mul_left_comm, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun n => ?_
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [ha]
  exact poisson_exponent n hq0 hz0

theorem im_neg_inv_pos {q : ℕ} (hq0 : 0 < q) {z : ℂ} (hz : 0 < z.im) :
    0 < (-1 / (4 * (q : ℂ) ^ 2 * z)).im := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have e : -1 / (4 * (q : ℂ) ^ 2 * z) = (((1 / (4 * (q : ℝ) ^ 2)) : ℝ) : ℂ) * (-1 / z) := by
    push_cast; field_simp
  rw [e, Complex.im_ofReal_mul]
  have : (-1 / z).im = z.im / Complex.normSq z := by
    rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_re, Complex.inv_im]; simp; ring
  rw [this]
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  positivity

theorem sum_char_cexp (hψ : ψ ≠ 1) (n : ℤ) :
    ∑ r : Fin q, ψ ((r : ℕ) : ZMod q) * cexp (2 * π * I * ((r : ℕ) : ℂ) * n / q) =
      ψ⁻¹ (n : ZMod q) * gaussSum ψ ZMod.stdAddChar := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  rw [← gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar (isPrimitive_of_ne_one ψ hψ) (n : ZMod q)]
  unfold gaussSum
  let e : Fin q ≃ ZMod q :=
    { toFun := fun r => ((r : ℕ) : ZMod q)
      invFun := fun a => ⟨a.val, ZMod.val_lt a⟩
      left_inv := fun r => Fin.ext (ZMod.val_natCast_of_lt r.2)
      right_inv := fun a => ZMod.natCast_zmod_val a }
  refine Fintype.sum_equiv e _ _ fun r => ?_
  simp only [e, Equiv.coe_fn_mk, AddChar.mulShift_apply]
  rw [stdAddChar_mul_val, ← cexp_val_intCast ((r : ℕ) : ZMod q) n, ZMod.val_natCast_of_lt r.2]

theorem char_residue_class {z : ℂ} (hz : 0 < z.im) (r : ℕ) :
    ∑' m : ℤ, ψ (((m * q + r : ℤ)) : ZMod q) * cexp (2 * π * I * (((m * q + r : ℤ)) : ℂ) ^ 2 * z) =
      ψ (r : ZMod q) * (1 / (-2 * I * (q : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) ^ 2 * (-1 / (4 * (q : ℂ) ^ 2 * z))) *
          cexp (2 * π * I * (r : ℂ) * n / q)) := by
  have hψr : ∀ m : ℤ, ψ (((m * q + r : ℤ)) : ZMod q) = ψ (r : ZMod q) := by
    intro m
    congr 1
    push_cast
    rw [ZMod.natCast_self]
    ring
  simp_rw [hψr]
  rw [tsum_mul_left, residue_class_poisson hz r]

theorem tsum_int_split_residue {f : ℤ → ℂ} (hsum : Summable f) :
    ∑' n : ℤ, f n = ∑ r : Fin q, ∑' m : ℤ, f (m * q + (r : ℕ)) := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  rw [← (Int.divModEquiv q).symm.tsum_eq]
  have hsum' : Summable fun p : ℤ × Fin q => f ((Int.divModEquiv q).symm p) :=
    (Int.divModEquiv q).symm.summable_iff.2 hsum
  rw [hsum'.tsum_prod' (fun m => (hasSum_fintype _).summable)]
  simp_rw [tsum_fintype]
  have hsr : ∀ r : Fin q, Summable fun m : ℤ => f ((Int.divModEquiv q).symm (m, r)) := by
    intro r
    refine hsum.comp_injective ?_
    intro m m' h
    simp only [Int.divModEquiv_symm_apply] at h
    have : (m : ℤ) * q = m' * q := by linarith
    exact mul_right_cancel₀ (by exact_mod_cast (NeZero.ne q)) this
  rw [Summable.tsum_finsetSum (fun r _ => hsr r)]
  simp only [Int.divModEquiv_symm_apply]

/-- **Inversion of the twisted theta series**: for a nontrivial `ψ` mod a prime `q` and `Im z > 0`,
`Σ_n ψ(n) e(n²z) = τ(ψ) (-2iq²z)^{-1/2} Σ_n ψ̄(n) e(-n²/(4q²z))`. -/
theorem thetaChar_inversion (hψ : ψ ≠ 1) {z : ℂ} (hz : 0 < z.im) :
    ∑' n : ℤ, ψ (n : ZMod q) * cexp (2 * π * I * (n : ℂ) ^ 2 * z) =
      gaussSum ψ ZMod.stdAddChar / (-2 * I * (q : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, ψ⁻¹ (n : ZMod q) * cexp (2 * π * I * (n : ℂ) ^ 2 * (-1 / (4 * (q : ℂ) ^ 2 * z))) := by
  have hsum : Summable fun n : ℤ => ψ (n : ZMod q) * cexp (2 * π * I * (n : ℂ) ^ 2 * z) :=
    Summable.of_norm_bounded (summable_theta_terms hz).norm fun n => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  rw [tsum_int_split_residue (q := q) hsum]
  simp_rw [char_residue_class ψ hz]
  have hv := im_neg_inv_pos hq.out.pos hz
  set v : ℂ := -1 / (4 * (q : ℂ) ^ 2 * z) with hvdef
  set c : ℂ := 1 / (-2 * I * (q : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ) with hc
  have hsv := summable_theta_terms hv
  have hsd : ∀ r : Fin q, Summable fun n : ℤ => ψ ((r : ℕ) : ZMod q) *
      (c * (cexp (2 * π * I * (n : ℂ) ^ 2 * v) * cexp (2 * π * I * ((r : ℕ) : ℂ) * n / q))) := by
    intro r
    refine (((summable_theta_terms hv).norm.mul_left (‖ψ ((r : ℕ) : ZMod q)‖ * ‖c‖))).of_norm_bounded
      fun n => ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖cexp (2 * π * I * ((r : ℕ) : ℂ) * n / q)‖ = 1 := by
      rw [Complex.norm_exp]
      have : (2 * π * I * ((r : ℕ) : ℂ) * n / q).re = 0 := by
        rw [show (2 * π * I * ((r : ℕ) : ℂ) * n / q) = ((2 * π * (r : ℕ) * n / q : ℝ) : ℂ) * I by
          push_cast; ring]
        simp
      rw [this, Real.exp_zero]
    rw [h1]
    apply le_of_eq
    ring
  have e1 : ∀ r : Fin q, ψ ((r : ℕ) : ZMod q) * (c *
      ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) ^ 2 * v) * cexp (2 * π * I * ((r : ℕ) : ℂ) * n / q)) =
      ∑' n : ℤ, ψ ((r : ℕ) : ZMod q) *
        (c * (cexp (2 * π * I * (n : ℂ) ^ 2 * v) * cexp (2 * π * I * ((r : ℕ) : ℂ) * n / q))) := by
    intro r
    rw [tsum_mul_left, tsum_mul_left]
  simp_rw [e1]
  rw [← Summable.tsum_finsetSum (fun r _ => hsd r)]
  rw [div_eq_mul_inv, ← one_div, ← hc, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hg := sum_char_cexp ψ hψ n
  calc ∑ r : Fin q, ψ ((r : ℕ) : ZMod q) *
        (c * (cexp (2 * π * I * (n : ℂ) ^ 2 * v) * cexp (2 * π * I * ((r : ℕ) : ℂ) * n / q)))
      = c * cexp (2 * π * I * (n : ℂ) ^ 2 * v) *
          ∑ r : Fin q, ψ ((r : ℕ) : ZMod q) * cexp (2 * π * I * ((r : ℕ) : ℂ) * n / q) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
    _ = _ := by rw [hg]; ring

/-- `θ_χ = τ(χ̄) Σ_n χ²(n) e(n²z)`: the twisted theta series is a Gauss sum times the theta series of
the square character. -/
theorem thetaTw_eq_char_sq (h1 : ψ ≠ 1) {v : ℂ} (hv : 0 < v.im) :
    thetaTw ψ v = tauG ψ⁻¹ * ∑' n : ℤ, (ψ ^ 2) (n : ZMod q) * cexp (2 * π * I * (n : ℂ) ^ 2 * v) := by
  rw [← (thetaTw_hasSum ψ hv).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [gTw_eq ψ h1, MulChar.pow_apply' _ two_ne_zero]
  push_cast
  rw [map_pow]
  ring

/-- **Inversion of `θ_χ`** for `χ² ≠ 1` mod a prime `q`:
`τ(χ) θ_χ(z) = τ(χ̄) τ(χ²) (-2iq²z)^{-1/2} θ_χ̄(-1/(4q²z))`. -/
theorem thetaTw_inversion (h2 : ψ ^ 2 ≠ 1) {z : ℂ} (hz : 0 < z.im) :
    tauG ψ * thetaTw ψ z =
      tauG ψ⁻¹ * tauG (ψ ^ 2) / (-2 * I * (q : ℂ) ^ 2 * z) ^ (1 / 2 : ℂ) *
        thetaTw ψ⁻¹ (-1 / (4 * (q : ℂ) ^ 2 * z)) := by
  have h1 : ψ ≠ 1 := fun h => h2 (by rw [h, one_pow])
  have h1' : ψ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.1 h)
  have hv := im_neg_inv_pos hq.out.pos hz
  rw [thetaTw_eq_char_sq ψ h1 hz, thetaTw_eq_char_sq ψ⁻¹ h1' hv, thetaChar_inversion (ψ ^ 2) h2 hz,
    inv_inv, inv_pow]
  unfold tauG
  ring

end Inversion

end

end GaloisForLFunctions.RHTower.HalfWeight
