import GaloisForLFunctions.RHTower.DeningerTwoSidedSchwartzBound

/-!
# The inverse weight and its derivatives decay like the weight

Strengthening the bound on the derivatives of `u = 1/(2\cosh(Kt))`: each one is bounded by a
constant multiple of `u` itself, not merely by a constant.  Since `e^{K|t|}u(t) \le 1`, this is the
decay needed to read the Meyer weight off the derivatives of `w_K h`.

* `deningerSechWeight_pos` : `u > 0`.
* `deningerSechWeight_iteratedFDeriv_le_mul` : **`‖u^{(j)}‖ ≤ C_j u`.**
* `deningerExpWeight_mul_sech_le_one` : `e^{K|t|}u(t) ≤ 1`.
-/

namespace RHTower

open scoped ContDiff

noncomputable section

theorem deningerSechWeight_pos (K t : ℝ) : 0 < deningerSechWeight K t := by
  have := Real.cosh_pos (K * t)
  rw [deningerSechWeight]
  positivity

/-- **Every derivative of the inverse weight is bounded by a multiple of the weight itself.** -/
theorem deningerSechWeight_iteratedFDeriv_le_mul (K : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (deningerSechWeight K) t‖ ≤ C * deningerSechWeight K t := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 =>
      refine ⟨1, zero_le_one, fun t => ?_⟩
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
        abs_of_pos (deningerSechWeight_pos K t), one_mul]
    | (n + 1) =>
      have hu : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, i ≤ n →
          ‖iteratedFDeriv ℝ i (deningerSechWeight K) t‖ ≤ C * deningerSechWeight K t := by
        intro i
        by_cases hi : i ≤ n
        · obtain ⟨C, hC0, hC⟩ := ih i (Nat.lt_succ_of_le hi)
          exact ⟨C, hC0, fun t _ => hC t⟩
        · exact ⟨0, le_refl 0, fun _ hcon => absurd hcon hi⟩
      choose Cu hCu0 hCu using hu
      choose Cv hCv0 hCv using deningerSechLog_iteratedFDeriv_bounded K
      have hnegv : ContDiff ℝ ∞ (fun s : ℝ => -(deningerSechLog K s)) :=
        (deningerSechLog_contDiff K).neg
      refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cv i * Cu (n - i),
        Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCv0 i)) (hCu0 (n - i)), fun t => ?_⟩
      have hderiv : deriv (deningerSechWeight K)
          = fun s => -(deningerSechLog K s) * deningerSechWeight K s :=
        funext fun s => (deningerSechWeight_hasDerivAt K s).deriv
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ', hderiv,
        ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      refine le_trans (norm_iteratedFDeriv_mul_le hnegv (deningerSechWeight_contDiff K) t
        (by exact_mod_cast le_top)) ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hfun : (fun s : ℝ => -(deningerSechLog K s)) = -(deningerSechLog K) := rfl
      have hvi : ‖iteratedFDeriv ℝ i (fun s : ℝ => -(deningerSechLog K s)) t‖ ≤ Cv i := by
        rw [hfun, iteratedFDeriv_neg_apply, norm_neg]
        exact hCv i t
      have hui : ‖iteratedFDeriv ℝ (n - i) (deningerSechWeight K) t‖
          ≤ Cu (n - i) * deningerSechWeight K t := hCu (n - i) t (Nat.sub_le _ _)
      calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun s : ℝ => -(deningerSechLog K s)) t‖
              * ‖iteratedFDeriv ℝ (n - i) (deningerSechWeight K) t‖
          ≤ (n.choose i : ℝ) * Cv i * (Cu (n - i) * deningerSechWeight K t) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hvi (Nat.cast_nonneg _)) hui
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCv0 i))
        _ = (n.choose i : ℝ) * Cv i * Cu (n - i) * deningerSechWeight K t := by ring

/-- **The Meyer weight is absorbed by the inverse two-sided weight.** -/
theorem deningerExpWeight_mul_sech_le_one {K : ℝ} (hK : 0 ≤ K) (t : ℝ) :
    Real.exp (K * |t|) * deningerSechWeight K t ≤ 1 := by
  have hge : Real.exp (K * |t|) ≤ Real.exp (K * t) + Real.exp (-(K * t)) :=
    deningerTwoSidedWeight_ge K t hK
  have hcosh : Real.exp (K * t) + Real.exp (-(K * t)) = 2 * Real.cosh (K * t) := by
    rw [Real.cosh_eq]; ring
  have hpos : (0 : ℝ) < 2 * Real.cosh (K * t) := by
    have := Real.cosh_pos (K * t); positivity
  rw [deningerSechWeight, mul_one_div, div_le_one hpos]
  rw [hcosh] at hge
  exact hge

end

end RHTower
