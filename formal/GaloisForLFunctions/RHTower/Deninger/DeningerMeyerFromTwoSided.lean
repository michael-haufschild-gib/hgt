import GaloisForLFunctions.RHTower.Deninger.DeningerSechDecay

/-!
# The Meyer weights are read off the two-sided weighted function

Writing `h = u\,(w_K h)` with `u = 1/w_K` and expanding by Leibniz, every Meyer weight of `h` is
bounded by the derivatives of `w_K h`: the factors `u^{(j)}` are bounded by multiples of `u`, and
`e^{K|t|}u(t) \le 1` absorbs the Meyer weight exactly.

* `deningerSech_mul_twoSided` : `h = u\,(w_K h)` pointwise.
* `deningerMeyerWeight_le_twoSidedDeriv` : **`e^{K|t|}‖h^{(n)}(t)‖ ≤ C ∑_{m ≤ n} ‖(w_K h)^{(m)}(t)‖`.**
-/

namespace RHTower

open SchwartzMap
open scoped ContDiff

noncomputable section

/-- **The cochain is the inverse weight times the weighted cochain.** -/
theorem deningerSech_mul_twoSided (K : ℝ) (h : DeningerExpSchwartz) :
    (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun t => ((deningerSechWeight K t : ℝ) : ℂ)
        * (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t := by
  funext t
  rw [deningerTwoSidedMul_apply, ← mul_assoc, ← Complex.ofReal_mul]
  have hcosh : Real.exp (K * t) + Real.exp (-(K * t)) = 2 * Real.cosh (K * t) := by
    rw [Real.cosh_eq]; ring
  have hone : deningerSechWeight K t * (Real.exp (K * t) + Real.exp (-(K * t))) = 1 := by
    rw [hcosh, deningerSechWeight]
    have := Real.cosh_pos (K * t)
    field_simp
  rw [hone, Complex.ofReal_one, one_mul]

/-- **Every Meyer weight of the cochain is bounded by the derivatives of the weighted cochain.** -/
theorem deningerMeyerWeight_le_twoSidedDeriv {K : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : DeningerExpSchwartz) (t : ℝ),
      Real.exp (K * |t|)
          * ‖iteratedFDeriv ℝ n (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖
        ≤ C * ∑ m ∈ Finset.range (n + 1),
            ‖iteratedFDeriv ℝ m
              (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ := by
  choose Cu hCu0 hCu using deningerSechWeight_iteratedFDeriv_le_mul K
  set D : ℝ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * Cu j with hD
  refine ⟨D, Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hCu0 j),
    fun h t => ?_⟩
  have hsechC : ContDiff ℝ ∞ (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (deningerSechWeight_contDiff K)
  have hwC : ContDiff ℝ ∞ (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    ((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)
  have hleib : ‖iteratedFDeriv ℝ n (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖
      ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
          * ‖iteratedFDeriv ℝ j (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ)) t‖
          * ‖iteratedFDeriv ℝ (n - j)
              (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ := by
    rw [deningerSech_mul_twoSided K h]
    exact norm_iteratedFDeriv_mul_le hsechC hwC t (by exact_mod_cast le_top)
  have hstep : Real.exp (K * |t|)
      * ‖iteratedFDeriv ℝ n (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖
      ≤ Real.exp (K * |t|) * ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
          * ‖iteratedFDeriv ℝ j (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ)) t‖
          * ‖iteratedFDeriv ℝ (n - j)
              (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ :=
    mul_le_mul_of_nonneg_left hleib (Real.exp_pos _).le
  refine le_trans hstep ?_
  rw [Finset.mul_sum, hD, Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  -- the inverse weight cancels the Meyer weight
  have hsechNorm : ‖iteratedFDeriv ℝ j (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ)) t‖
      = ‖iteratedFDeriv ℝ j (deningerSechWeight K) t‖ := by
    have hcomp : (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ))
        = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ deningerSechWeight K := rfl
    rw [hcomp]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      ((deningerSechWeight_contDiff K).contDiffAt) (i := j) (by exact_mod_cast le_top)
  have habsorb : Real.exp (K * |t|)
      * ‖iteratedFDeriv ℝ j (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ)) t‖ ≤ Cu j := by
    rw [hsechNorm]
    have h1 := hCu j t
    have h2 : Real.exp (K * |t|) * (Cu j * deningerSechWeight K t) ≤ Cu j := by
      have habs := deningerExpWeight_mul_sech_le_one hK t
      calc Real.exp (K * |t|) * (Cu j * deningerSechWeight K t)
          = Cu j * (Real.exp (K * |t|) * deningerSechWeight K t) := by ring
        _ ≤ Cu j * 1 := mul_le_mul_of_nonneg_left habs (hCu0 j)
        _ = Cu j := by ring
    calc Real.exp (K * |t|) * ‖iteratedFDeriv ℝ j (deningerSechWeight K) t‖
        ≤ Real.exp (K * |t|) * (Cu j * deningerSechWeight K t) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ ≤ Cu j := h2
  have hmem : ‖iteratedFDeriv ℝ (n - j)
      (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖
      ≤ ∑ m ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ m
          (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ :=
    Finset.single_le_sum
      (f := fun m => ‖iteratedFDeriv ℝ m
        (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖)
      (fun m _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.sub_le _ _)))
  calc Real.exp (K * |t|) * ((n.choose j : ℝ)
          * ‖iteratedFDeriv ℝ j (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ)) t‖
          * ‖iteratedFDeriv ℝ (n - j)
              (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖)
      = (n.choose j : ℝ) * (Real.exp (K * |t|)
          * ‖iteratedFDeriv ℝ j (fun s : ℝ => ((deningerSechWeight K s : ℝ) : ℂ)) t‖)
        * ‖iteratedFDeriv ℝ (n - j)
            (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ := by ring
    _ ≤ (n.choose j : ℝ) * Cu j * ∑ m ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ m
          (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left habsorb (Nat.cast_nonneg _)) hmem
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hCu0 j))

end

end RHTower
