import GaloisForLFunctions.RHTower.HalfWeightTwistedKernel

/-!
# The forced zero of the twisted Shimura transform

For a Maass cusp form `f` on `Γ₀(N+1)` with exceptional eigenvalue `1/4 - τ²`, `0 < τ < 1/2`, and a
character `χ` of odd prime conductor `q ∤ N+1` with `χ⁴ ≠ 1`:

* `gTw_eq`, `conj_gTw_sq`: `g_χ(n) = χ(n) τ(χ̄)`, so the weights of the twisted series are
  `\overline{g_χ(4j²)} = \overline{χ(4) τ(χ̄)} χ̄(j)²`.
* `YTw`: `Y_χ(w) = I_χ(w) Mel_τ(w - 1/4)⁻¹ / 2`, with `I_χ` the folded Rankin–Selberg integral of
  `G_χ = f(4z) \overline{θ_χ(z)} y^{1/4}` against `E*_{χ²}` at level `4(N+1)q²`.
* **`shimura_forced_zero_tw`**: `Z_χ(w) = Σ_j \overline{g_χ(4j²)} ρ_{j²}(8πj²)^{3/4-w}` converges absolutely on
  `Re w > 5/4`; `Y_χ = L(4w-1, χ̄⁴) Z_χ` on `Re w > 7/4`; `Y_χ` is holomorphic on `Re w > 1/4`; and
  `Y_χ(1/4 + τ) = 0`, because `1/Γ(w - 1/4 - τ)` vanishes there.

Up to the constant `\overline{χ(4) τ(χ̄)}`, `L(4w-1, χ̄⁴) Z_χ(w)` is the Dirichlet series of
`L(s, sym² f ⊗ χ̄²)` at `s = 2w - 1/2` in the normalisation of the Whittaker coefficients.
-/

open Real Complex Filter Topology MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

section TwistedForcedZero

open SelbergMaassFourier SelbergMaassMean
open _root_.RHTower GaloisForLFunctions.RHTower

variable (N : ℕ) {τ : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma0 (N + 1))) (1 / 4 - τ ^ (2 : ℕ)))
  {q : ℕ} [hq : Fact q.Prime] (χ : DirichletCharacter ℂ q)

theorem char_sq_neg_one : (χ ^ 2) (-1) = 1 := by
  rw [MulChar.pow_apply' _ two_ne_zero, ← map_pow]; simp

theorem cexp_val_intCast (a : ZMod q) (n : ℤ) :
    cexp (2 * π * Complex.I * ((a.val : ℕ) : ℂ) * n / q) =
      cexp (2 * π * Complex.I * ((((n : ZMod q)).val : ℕ) : ℂ) * ((a.val : ℕ) : ℂ) / q) := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.out.ne_zero
  have hv : ((((n : ZMod q)).val : ℕ) : ℤ) = n - q * (n / q) := by
    rw [ZMod.val_intCast, Int.emod_def]
  have hvC : ((((n : ZMod q)).val : ℕ) : ℂ) = (n : ℂ) - q * ((n / q : ℤ) : ℂ) := by exact_mod_cast hv
  rw [hvC, show 2 * π * Complex.I * ((n : ℂ) - q * ((n / q : ℤ) : ℂ)) * ((a.val : ℕ) : ℂ) / q =
      2 * π * Complex.I * ((a.val : ℕ) : ℂ) * n / q + ((-((n / q) * a.val) : ℤ) : ℂ) * (2 * π * Complex.I) by
    push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **`g_χ(n) = χ(n) τ(χ̄)`** for `χ ≠ 1` of prime conductor. -/
theorem gTw_eq (h1 : χ ≠ 1) (n : ℤ) : gTw χ n = χ (n : ZMod q) * tauG χ⁻¹ := by
  have h1' : χ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.1 h)
  have hg := conj_char_eq_gauss χ⁻¹ h1' (n : ZMod q)
  have hl : starRingEnd ℂ (χ⁻¹ (n : ZMod q)) = χ (n : ZMod q) := by
    rw [← MulChar.star_apply' χ, show star (χ (n : ZMod q)) = starRingEnd ℂ (χ (n : ZMod q)) from rfl,
      Complex.conj_conj]
  rw [hl] at hg
  rw [hg, mul_comm ((tauG χ⁻¹)⁻¹), mul_assoc, inv_mul_cancel₀ (tauG_ne_zero χ⁻¹ h1'), mul_one, gTw]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cexp_val_intCast, ← MulChar.star_apply' χ]
  rfl

/-- The weights of the twisted series: `\overline{g_χ(4j²)} = \overline{χ(4) τ(χ̄)} χ̄(j)²`. -/
theorem conj_gTw_sq (h1 : χ ≠ 1) (j : ℤ) :
    starRingEnd ℂ (gTw χ (4 * j ^ 2)) = starRingEnd ℂ (χ 4 * tauG χ⁻¹) * (χ⁻¹ ^ 2) (j : ZMod q) := by
  rw [gTw_eq χ h1, MulChar.pow_apply' _ two_ne_zero, ← MulChar.star_apply' χ]
  push_cast
  rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow]
  simp only [show ∀ x : ℂ, star x = starRingEnd ℂ x from fun x => rfl]
  ring

/-- The twisted Shimura transform `Y_χ(w) = I_χ(w) Mel_τ(w - 1/4)⁻¹ / 2`, where `I_χ` is the folded
Rankin–Selberg integral of `G_χ` against `E*_{χ²}` at level `4(N+1)q²`. -/
def YTw (w : ℂ) : ℂ := rsFoldTw (χ ^ 2) (N + 1) (Gtw N f χ) w * invMel τ (w - 1 / 4) / 2

variable {N f χ}

theorem differentiableAt_YTw (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (h4 : (χ ^ 2) ^ 2 ≠ 1) {w : ℂ}
    (hw : 1 / 4 < w.re) : DifferentiableAt ℂ (YTw N f χ) w := by
  have hI := differentiableAt_rsFoldTw (χ ^ 2) (N + 1) h4 (continuous_Gtw N f χ)
    (fun B c => Gtw_hdec χ hτ0 hτ1 B (Quotient.out c)) hw
  have hM : DifferentiableAt ℂ (fun w : ℂ => invMel τ (w - 1 / 4)) w :=
    (differentiableAt_invMel τ (by simp; linarith)).comp w (differentiableAt_id.sub_const _)
  exact (hI.mul hM).div_const 2

theorem YTw_eq (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (hq2 : q ≠ 2) (hcop : q.Coprime (4 * (N + 1)))
    (h2 : χ ^ 2 ≠ 1) (h4 : (χ ^ 2) ^ 2 ≠ 1) {w : ℂ} (hw : 7 / 4 < w.re) :
    YTw N f χ w = RTw (χ ^ 2) w * ∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * zCoef f hτ0 hτ1 w j := by
  unfold YTw
  rw [rsFoldTw_eq (χ ^ 2) (N + 1) h2 h4 hcop (char_sq_neg_one χ) (fun γ hγ z => Gtw_smul N f χ hq2 hγ z)
    (by linarith) (integrableOn_Gtw_strip χ hτ0 hτ1 hw), strip_integral_Gtw χ hτ0 hτ1 hw]
  have hmel := melK_mul_invMel (τ := τ) (μ := w - 1 / 4) (by rw [abs_of_pos hτ0]; simp; linarith)
  set S := ∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * zCoef f hτ0 hτ1 w j
  set m := melK τ (w - 1 / 4)
  set v := invMel τ (w - 1 / 4)
  rw [show 2 * RTw (χ ^ 2) w * (S * m) * v / 2 = RTw (χ ^ 2) w * S * (m * v) by ring, hmel, mul_one]

theorem summable_zCoef_tw (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) {w : ℂ} (hw : 5 / 4 < w.re) :
    Summable fun j : ℤ => starRingEnd ℂ (gTw χ (4 * j ^ 2)) * zCoef f hτ0 hτ1 w j := by
  obtain ⟨R, -, hR⟩ := rhoW_bounded (N := N) (f := f) hτ0 hτ1
  refine Summable.of_norm_bounded
    ((Real.summable_abs_int_rpow (b := 2 * w.re - 3 / 2) (by linarith)).mul_left
      (q * (R * (8 * π) ^ (3 / 4 - w.re)))) fun j => ?_
  rw [norm_mul, Complex.norm_conj]
  have h1 := norm_gTw_le χ (4 * j ^ 2)
  have h2 := norm_zCoef_le hτ0 hτ1 hR w j
  calc ‖gTw χ (4 * j ^ 2)‖ * ‖zCoef f hτ0 hτ1 w j‖
      ≤ q * (R * (8 * π) ^ (3 / 4 - w.re) * |(j : ℝ)| ^ (-(2 * w.re - 3 / 2))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- **The forced zero of the twisted Shimura transform.**  Let `f` be a Maass cusp eigenform on `Γ₀(N+1)`
with exceptional eigenvalue `1/4 - τ²`, `0 < τ < 1/2`, and `χ` a Dirichlet character of odd prime
conductor `q ∤ N+1` with `χ⁴ ≠ 1`.  The series `Z_χ(w) = Σ_j \overline{g_χ(4j²)} ρ_{j²}(8πj²)^{3/4-w}`
converges absolutely on `Re w > 5/4`; `L(4w-1, χ̄⁴) Z_χ(w)` continues to the holomorphic function `Y_χ` on
`Re w > 1/4`, and `Y_χ(1/4 + τ) = 0`. -/
theorem shimura_forced_zero_tw (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (hq2 : q ≠ 2)
    (hcop : q.Coprime (4 * (N + 1))) (h2 : χ ^ 2 ≠ 1) (h4 : (χ ^ 2) ^ 2 ≠ 1) :
    (∀ w : ℂ, 5 / 4 < w.re →
      Summable fun j : ℤ => starRingEnd ℂ (gTw χ (4 * j ^ 2)) * zCoef f hτ0 hτ1 w j) ∧
    (∀ w : ℂ, 7 / 4 < w.re → YTw N f χ w =
      DirichletCharacter.LFunction ((χ ^ 2)⁻¹ ^ 2) (4 * w - 1) *
        ∑' j : ℤ, starRingEnd ℂ (gTw χ (4 * j ^ 2)) * zCoef f hτ0 hτ1 w j) ∧
    (∀ w : ℂ, 1 / 4 < w.re → DifferentiableAt ℂ (YTw N f χ) w) ∧
    YTw N f χ (1 / 4 + τ) = 0 := by
  refine ⟨fun w hw => summable_zCoef_tw hτ0 hτ1 hw, fun w hw => YTw_eq hτ0 hτ1 hq2 hcop h2 h4 hw,
    fun w hw => differentiableAt_YTw hτ0 hτ1 h4 hw, ?_⟩
  unfold YTw
  rw [show (1 / 4 + (τ : ℂ)) - 1 / 4 = τ by ring, invMel_self]
  simp

end TwistedForcedZero

end

end GaloisForLFunctions.RHTower.HalfWeight
