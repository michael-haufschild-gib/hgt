import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeStrictStability

/-!
# Hurwitz stability of the Jensen polynomials of `ξ` at real points

At a real point `σ` the Jensen polynomials of `ξ` in the real direction are

`J_d(ξ; σ)(t) = Σ_{k≤d} C(d,k) ξ^{(k)}(σ) t^k`.

They are the reversed Jensen polynomials of `w ↦ ξ(σ + iw)` read through `X = i/t`:
`R_d(ξ(σ + i·))(i/t) = i^d t^{−d} J_d(ξ; σ)(t)`, and `Im(i/t) = Re t/|t|²`. So Hermite–Biehler
stability of `R_d` (roots in `Im < 0`) is exactly Hurwitz stability of `J_d(ξ; σ)` (roots in
`Re t < 0`).

**Theorem.** For every `σ ≥ 1` and `d ≥ 1`, every root of `J_d(ξ; σ)` has negative real part
(unconditionally). For `σ > 1/2`: `ξ ≠ 0` on `Re s > σ` iff all `J_d(ξ; σ)`, `d ≥ 1`, are Hurwitz
stable. For every `σ`: `ξ ≠ 0` on `Re s > σ` iff all roots of all `J_d(ξ; σ)` have `Re t ≤ 0`.
-/

open Polynomial Filter Topology Complex
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- The Jensen polynomial `Σ_{k≤d} C(d,k) ξ^{(k)}(σ) t^k` of `ξ` at the real point `σ`. -/
def xiRealJensen (σ : ℝ) (d : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (d + 1), C ((d.choose k : ℂ) * iteratedDeriv k xi (σ : ℂ)) * X ^ k

theorem xiShiftCoeff_eq (σ : ℝ) (k : ℕ) :
    xiShiftCoeff σ k = I ^ k * iteratedDeriv k xi (σ : ℂ) / (k.factorial : ℂ) := by
  have hg : ContDiff ℂ k fun z : ℂ => xi ((σ : ℂ) + z) :=
    (xi_differentiable.comp (by fun_prop)).contDiff
  have h := iteratedDeriv_comp_const_mul hg I
  have h2 : iteratedDeriv k (fun z : ℂ => xi ((σ : ℂ) + z)) = fun t =>
      iteratedDeriv k xi ((σ : ℂ) + t) := iteratedDeriv_comp_const_add k xi (σ : ℂ)
  rw [xiShiftCoeff, show (fun w : ℂ => xi ((σ : ℂ) + I * w)) =
    fun x => (fun z => xi ((σ : ℂ) + z)) (I * x) from rfl, h, h2]
  simp

theorem eval_xiRealJensen_zero (σ : ℝ) (d : ℕ) : (xiRealJensen σ d).eval 0 = xi (σ : ℂ) := by
  rw [xiRealJensen, eval_finsetSum, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos d)) h

/-- `R_d(ξ(σ + i·))(i/t) = i^d t^{−d} J_d(ξ; σ)(t)`. -/
theorem eval_jensenRev_I_div (σ : ℝ) (d : ℕ) {t : ℂ} (ht : t ≠ 0) :
    (jensenRev d (PowerSeries.mk (xiShiftCoeff σ))).eval (I / t) =
      I ^ d / t ^ d * (xiRealJensen σ d).eval t := by
  rw [jensenRev_eq_sum, eval_finsetSum, xiRealJensen, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [eval_mul, eval_C, eval_pow, eval_X, eval_mul, eval_C, eval_pow, eval_X,
    PowerSeries.coeff_mk, xiShiftCoeff_eq]
  have hdesc : (d.descFactorial k : ℂ) = (d.choose k : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hId : I ^ d = I ^ k * I ^ (d - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  have htd : t ^ d = t ^ k * t ^ (d - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [hdesc, hId, htd, div_pow]
  field_simp

theorem im_I_div (t : ℂ) : (I / t).im = t.re / Complex.normSq t := by
  rw [div_eq_mul_inv, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, inv_re]

/-- **Hurwitz stability from a zero-free half-plane.** For `σ > 1/2`, if `ξ ≠ 0` on `Re s > σ`, every
root of every `J_d(ξ; σ)`, `d ≥ 1`, has negative real part. -/
theorem re_neg_of_isRoot_xiRealJensen {σ : ℝ} (hσ : 1 / 2 < σ)
    (hzf : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ) {d : ℕ} (hd : 1 ≤ d) {t : ℂ}
    (ht : (xiRealJensen σ d).IsRoot t) : t.re < 0 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [IsRoot, eval_xiRealJensen_zero] at ht
    exact xi_ne_zero_of_real σ ht
  have hx := im_neg_of_zeroFree hσ hzf hd (x := I / t)
    (by rw [IsRoot, eval_jensenRev_I_div σ d ht0, ht.eq_zero, mul_zero])
  rw [im_I_div] at hx
  have hns : 0 < Complex.normSq t := Complex.normSq_pos.2 ht0
  by_contra h; push Not at h
  exact absurd hx (not_lt.2 (div_nonneg h hns.le))

/-- **Unconditional Hurwitz stability at `σ ≥ 1`.** For `σ ≥ 1` and `d ≥ 1`, every root of the
Jensen polynomial `Σ_k C(d,k) ξ^{(k)}(σ) t^k` has negative real part. -/
theorem re_neg_of_isRoot_xiRealJensen_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) {d : ℕ} (hd : 1 ≤ d)
    {t : ℂ} (ht : (xiRealJensen σ d).IsRoot t) : t.re < 0 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [IsRoot, eval_xiRealJensen_zero] at ht
    exact xi_ne_zero_of_real σ ht
  have hx := im_neg_of_one_le hσ hd (x := I / t)
    (by rw [IsRoot, eval_jensenRev_I_div σ d ht0, ht.eq_zero, mul_zero])
  rw [im_I_div] at hx
  have hns : 0 < Complex.normSq t := Complex.normSq_pos.2 ht0
  by_contra h; push Not at h
  exact absurd hx (not_lt.2 (div_nonneg h hns.le))

/-- Weak Hurwitz stability of all `J_d(ξ; σ)` forces the zero-free half-plane `Re s > σ`. -/
theorem zeroFree_of_forall_re_nonpos {σ : ℝ}
    (h : ∀ d : ℕ, 1 ≤ d → ∀ t, (xiRealJensen σ d).IsRoot t → t.re ≤ 0) :
    ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ := by
  refine (zeroFree_iff_exists_frequently_im_le σ).2 ⟨0, ?_⟩
  refine (eventually_ge_atTop 1).frequently.mono fun d hd x hx => ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have ht0 : I / x ≠ 0 := div_ne_zero I_ne_zero hx0
  have hroot : (xiRealJensen σ d).IsRoot (I / x) := by
    have := eval_jensenRev_I_div σ d ht0
    rw [show I / (I / x) = x by field_simp, hx.eq_zero] at this
    rw [IsRoot]
    exact (mul_eq_zero.1 this.symm).resolve_left (div_ne_zero (pow_ne_zero _ I_ne_zero)
      (pow_ne_zero _ ht0))
  have hre := h d hd _ hroot
  have : x = I / (I / x) := by field_simp
  rw [this, im_I_div]
  exact div_nonpos_of_nonpos_of_nonneg hre (Complex.normSq_nonneg _)

/-- **The real Jensen form of the half-plane theorem.** For `σ > 1/2`: `ξ` has no zero with
`Re ρ > σ` iff every `J_d(ξ; σ)`, `d ≥ 1`, is Hurwitz stable. -/
theorem zeroFree_iff_xiRealJensen_hurwitz {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ) ↔
      ∀ d : ℕ, 1 ≤ d → ∀ t, (xiRealJensen σ d).IsRoot t → t.re < 0 :=
  ⟨fun h _ hd _ ht => re_neg_of_isRoot_xiRealJensen hσ h hd ht,
    fun h => zeroFree_of_forall_re_nonpos fun d hd t ht => (h d hd t ht).le⟩

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.re_neg_of_isRoot_xiRealJensen_of_one_le
#print axioms FiniteFreeProbability.zeroFree_iff_xiRealJensen_hurwitz
