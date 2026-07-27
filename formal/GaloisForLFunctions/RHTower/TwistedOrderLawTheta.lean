import GaloisForLFunctions.RHTower.DirichletZeroAbscissa
import GaloisForLFunctions.RHTower.TwistedMertensOrderLowerBound

/-!
# The order laws at the zero abscissa

Upgrading the per-zero order bounds to the zero frontier `Θ_χ` gives the order law `(R3)` and the
lower half of its Mertens companion `(R15)` in the form the card states them:

```
2k Θ_χ - 1 ≤ Ψ_{χ,k} ≤ 2k - 1,        2k(1 + Θ_χ) - 1 ≤ Ψ^C_{χ,k}.
```

The matching upper bound for the companion is not an order-law statement at all: it is the
classical Littlewood-type estimate `M_χ(N) = O(N^{Θ_χ + ε})` on the twisted Mertens function.  Here
that estimate appears as the interface `TwistedMertensSubpowerBound`, and the reduction of the upper
half of `(R15)` to it is proved unconditionally.
-/

open Complex Filter
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- **The order law `(R3)` at the zero frontier.**  `2k Θ_χ - 1 ≤ Ψ_{χ,k}`. -/
theorem two_mul_zeroAbscissa_sub_one_le_limsup
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {j : ℕ} :
    2 * ((j : ℝ) + 1) * zeroAbscissa χ - 1 ≤ Filter.limsup
      (fun M => Real.log (1 + max (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop := by
  have hcoeff : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := norm_twistedMobiusCoeff_le_one χ
  have hkR : (0 : ℝ) < 2 * (((j + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  refine le_limsup_of_no_subpower_below (D := 2 * j + 1) (fun M => ?_) fun α C hα hC hlt => ?_
  · exact (Complex.re_le_norm _).trans (norm_mixedAdditiveConvolutionPower_le_pow hcoeff j M)
  · have hb : (α + 1) / (2 * (((j + 1 : ℕ) : ℝ))) < zeroAbscissa χ := by
      rw [div_lt_iff₀ hkR]
      push_cast at hlt ⊢
      nlinarith [hlt]
    obtain ⟨ρ, hzero, hρre⟩ := exists_zero_lt_re hχ hprim hb
    exact not_twistedMixedSubpower_of_LFunction_eq_zero hχ (Nat.succ_pos j) hα hC hzero hρre

/-- **The companion law `(R15)` from below at the zero frontier.**
`2k(1 + Θ_χ) - 1 ≤ Ψ^C_{χ,k}`. -/
theorem two_mul_one_add_zeroAbscissa_sub_one_le_limsup_mertens
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {j : ℕ} :
    2 * ((j : ℝ) + 1) * (1 + zeroAbscissa χ) - 1 ≤ Filter.limsup
      (fun M => Real.log
          (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop := by
  have hcoeff : ∀ n : ℕ, ‖(↗χ * ↗μ) n‖ ≤ 1 := norm_twistedMobiusCoeff_le_one χ
  have hkR : (0 : ℝ) < 2 * (((j + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  refine le_limsup_of_no_subpower_below (D := 4 * j + 3) (fun M => ?_) fun α C hα hC hlt => ?_
  · exact (Complex.re_le_norm _).trans
      (norm_mixedAdditiveConvolutionPower_partialSumSeq_le_pow hcoeff j M)
  · have hb : (α + 1) / (2 * (((j + 1 : ℕ) : ℝ))) - 1 < zeroAbscissa χ := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hkR]
      push_cast at hlt ⊢
      nlinarith [hlt]
    have hbmax : max ((α + 1) / (2 * (((j + 1 : ℕ) : ℝ))) - 1) 0 < zeroAbscissa χ :=
      max_lt hb (zeroAbscissa_pos hχ hprim)
    obtain ⟨ρ, hzero, hρre⟩ := exists_zero_lt_re hχ hprim hbmax
    have hpos : 0 < ρ.re := lt_of_le_of_lt (le_max_right _ _) hρre
    have hshift : (α + 1) / (2 * (((j + 1 : ℕ) : ℝ))) - 1 < ρ.re :=
      lt_of_le_of_lt (le_max_left _ _) hρre
    exact not_mertensSubpower_of_LFunction_eq_zero hχ (Nat.succ_pos j) hα hC hzero hpos hshift

/-- **The classical Littlewood-type estimate for the twisted Mertens function**, as an interface:
for every `ε > 0` the partial sums of `χ μ` are `O(N^{θ+ε})`.  This is the analytic input the
companion law `(R15)` needs for its upper half; it is a Perron/contour estimate on `1/L(·,χ)` in
the half-plane right of `θ`, with no counterpart in mathlib. -/
def TwistedMertensSubpowerBound (χ : DirichletCharacter ℂ N) (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ M : ℕ,
    ‖partialSumSeq (↗χ * ↗μ) M‖ ≤ A * ((M : ℝ) + 1) ^ (θ + ε)

omit [NeZero N] in
/-- Polynomial domination of the Hermitian mixed convolution from a subpower bound on the
coefficients. -/
theorem norm_mixedAdditiveConvolutionPower_le_of_subpower {a : ℕ → ℂ} {A α : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α) (ha : ∀ n : ℕ, ‖a n‖ ≤ A * ((n : ℝ) + 1) ^ α) (j M : ℕ) :
    ‖mixedAdditiveConvolutionPower a (j + 1) M‖
      ≤ A ^ (2 * (j + 1)) * ((M : ℝ) + 1) ^ (2 * ((j : ℝ) + 1) * α + 2 * (j : ℝ) + 1) := by
  have hconv : ∀ n : ℕ, ‖additiveConvolutionPower a (j + 1) n‖
      ≤ A ^ (j + 1) * ((n : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ)) := by
    intro n
    have h := norm_additiveConvolutionPower_succ_le a hA hα ha j n
    refine h.trans (le_of_eq ?_)
    congr 2
    push_cast
    ring
  show ‖∑ ab ∈ Finset.antidiagonal M, additiveConvolutionPower a (j + 1) ab.1 *
    (starRingEnd ℂ) (additiveConvolutionPower a (j + 1) ab.2)‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  have hAp : (0 : ℝ) ≤ A ^ (j + 1) := by positivity
  have hstep : ∀ ab ∈ Finset.antidiagonal M,
      ‖additiveConvolutionPower a (j + 1) ab.1 *
          (starRingEnd ℂ) (additiveConvolutionPower a (j + 1) ab.2)‖
        ≤ A ^ (2 * (j + 1)) * ((M : ℝ) + 1) ^ (2 * (((j : ℝ) + 1) * α + (j : ℝ))) := by
    intro ab hab
    rw [Finset.mem_antidiagonal] at hab
    rw [norm_mul, RCLike.norm_conj]
    have hb1 : ((ab.1 : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ))
        ≤ ((M : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have h : (ab.1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : ab.1 ≤ M)
      linarith
    have hb2 : ((ab.2 : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ))
        ≤ ((M : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      have h : (ab.2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : ab.2 ≤ M)
      linarith
    calc ‖additiveConvolutionPower a (j + 1) ab.1‖ * ‖additiveConvolutionPower a (j + 1) ab.2‖
        ≤ (A ^ (j + 1) * ((M : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ))) *
            (A ^ (j + 1) * ((M : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ))) :=
          mul_le_mul ((hconv ab.1).trans (mul_le_mul_of_nonneg_left hb1 hAp))
            ((hconv ab.2).trans (mul_le_mul_of_nonneg_left hb2 hAp)) (norm_nonneg _)
            (by positivity)
      _ = A ^ (2 * (j + 1)) * ((M : ℝ) + 1) ^ (2 * (((j : ℝ) + 1) * α + (j : ℝ))) := by
          have h1 : ((M : ℝ) + 1) ^ (2 * (((j : ℝ) + 1) * α + (j : ℝ)))
              = ((M : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ))
                * ((M : ℝ) + 1) ^ (((j : ℝ) + 1) * α + (j : ℝ)) := by
            rw [← Real.rpow_add (by positivity)]
            congr 1
            ring
          have h2 : A ^ (2 * (j + 1)) = A ^ (j + 1) * A ^ (j + 1) := by
            rw [← pow_add]
            congr 1
            omega
          rw [h1, h2]
          ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hsplit : ((M : ℝ) + 1) ^ (2 * ((j : ℝ) + 1) * α + 2 * (j : ℝ) + 1)
      = ((M : ℝ) + 1) * ((M : ℝ) + 1) ^ (2 * (((j : ℝ) + 1) * α + (j : ℝ))) := by
    rw [show (2 * ((j : ℝ) + 1) * α + 2 * (j : ℝ) + 1)
        = 1 + 2 * (((j : ℝ) + 1) * α + (j : ℝ)) by ring,
      Real.rpow_add (by positivity), Real.rpow_one]
  rw [hsplit]
  exact le_of_eq (by ring)

omit [NeZero N] in
/-- **Reduction of the upper half of `(R15)`.**  A Littlewood-type subpower bound at exponent `θ`
on the twisted Mertens function caps the companion order exponent at `2k(1 + θ) - 1`. -/
theorem limsup_mertens_le_of_subpowerBound {χ : DirichletCharacter ℂ N} {θ : ℝ} (hθ : 0 ≤ θ)
    (hLit : TwistedMertensSubpowerBound χ θ) {j : ℕ} :
    Filter.limsup
      (fun M => Real.log
          (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop
      ≤ 2 * ((j : ℝ) + 1) * (1 + θ) - 1 := by
  refine le_of_forall_pos_le_add fun dlt hdlt => ?_
  set c : ℝ := 2 * ((j : ℝ) + 1) with hc
  have hc0 : 0 < c := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [hc]; linarith
  obtain ⟨A, hA, hbound⟩ := hLit (dlt / c) (by positivity)
  have hdeg : 0 ≤ 2 * ((j : ℝ) + 1) * (θ + dlt / c) + 2 * (j : ℝ) + 1 := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have : 0 ≤ θ + dlt / c := by positivity
    nlinarith
  refine le_trans (GaloisForLFunctions.HTGeometry.limsup_log_one_add_div_log_le_rpow
    (C := A ^ (2 * (j + 1))) (d := 2 * ((j : ℝ) + 1) * (θ + dlt / c) + 2 * (j : ℝ) + 1)
    (by positivity) hdeg (fun M => le_max_right _ _) (fun M => ?_)) ?_
  · refine max_le ?_ (by positivity)
    exact (Complex.re_le_norm _).trans
      (norm_mixedAdditiveConvolutionPower_le_of_subpower (le_of_lt hA)
        (by positivity) hbound j M)
  · have hcancel : c * (dlt / c) = dlt := by field_simp
    rw [hc] at hcancel ⊢
    nlinarith [hcancel]

/-- **The companion law `(R15)`.**  Granted the classical Littlewood estimate at the zero frontier,
the companion order exponent is exactly `2k(1 + Θ_χ) - 1`. -/
theorem limsup_mertens_eq_of_subpowerBound {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (hLit : TwistedMertensSubpowerBound χ (zeroAbscissa χ)) {j : ℕ} :
    Filter.limsup
      (fun M => Real.log
          (1 + max (mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) (j + 1) M).re 0)
        / Real.log ((M : ℝ) + 1)) atTop
      = 2 * ((j : ℝ) + 1) * (1 + zeroAbscissa χ) - 1 :=
  le_antisymm (limsup_mertens_le_of_subpowerBound (le_of_lt (zeroAbscissa_pos hχ hprim)) hLit)
    (two_mul_one_add_zeroAbscissa_sub_one_le_limsup_mertens hχ hprim)

end RHTower
