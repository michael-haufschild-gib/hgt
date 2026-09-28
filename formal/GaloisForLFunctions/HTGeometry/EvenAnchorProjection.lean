import Mathlib
import GaloisForLFunctions.HTGeometry.LagrangeRemainder

/-!
# Projection off the even anchors `1, x², …, x^{2N}, cosh(x/2)`

The even anchors are linearly independent on every neighbourhood of `0`. For a continuous
nonnegative weight `ψ` positive near `0`, the Gram matrix `G_ij = ∫ ψ A_i A_j` is therefore
invertible, and the projection `Π b = b - Σ_i (G⁻¹ r(b))_i ψ A_i`, `r_j(b) = ∫ A_j b`, annihilates
every anchor functional. It preserves evenness, and its coefficients vanish with the data `r(b)`.
-/

open Filter Topology MeasureTheory Set Polynomial Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The even anchors `1, x², …, x^{2N}, cosh(x/2)` -/

/-- The even anchors: `x^{2i}` for `i ≤ N` and `cosh(x/2)` for `i = N + 1`. -/
def evenAnchor (N : ℕ) (i : Fin (N + 2)) (x : ℝ) : ℝ :=
  if (i : ℕ) ≤ N then x ^ (2 * (i : ℕ)) else Real.cosh (x / 2)

theorem continuous_evenAnchor (N : ℕ) (i : Fin (N + 2)) : Continuous (evenAnchor N i) := by
  unfold evenAnchor; split_ifs <;> fun_prop

theorem evenAnchor_neg (N : ℕ) (i : Fin (N + 2)) (x : ℝ) :
    evenAnchor N i (-x) = evenAnchor N i x := by
  unfold evenAnchor
  split_ifs
  · rw [pow_mul, pow_mul, neg_sq]
  · rw [neg_div, Real.cosh_neg]

theorem evenAnchor_castSucc (N : ℕ) (i : Fin (N + 1)) (x : ℝ) :
    evenAnchor N i.castSucc x = x ^ (2 * (i : ℕ)) := by
  rw [evenAnchor, if_pos (by simpa using Nat.lt_succ_iff.mp i.2)]; rfl

theorem evenAnchor_last (N : ℕ) (x : ℝ) : evenAnchor N (Fin.last (N + 1)) x = Real.cosh (x / 2) := by
  rw [evenAnchor, if_neg (by simp)]

theorem iteratedDeriv_two_mul_cosh_half (n : ℕ) :
    iteratedDeriv (2 * n) (fun x : ℝ => Real.cosh (x / 2)) =
      fun x => (1 / 4 : ℝ) ^ n * Real.cosh (x / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd1 : ∀ x, HasDerivAt (fun x : ℝ => (1 / 4 : ℝ) ^ n * Real.cosh (x / 2))
        ((1 / 4 : ℝ) ^ n * (Real.sinh (x / 2) * (1 / 2))) x := fun x =>
      (((hasDerivAt_id x).div_const 2).cosh.congr_deriv (by simp)).const_mul _
    have hd2 : ∀ x, HasDerivAt (fun x : ℝ => (1 / 4 : ℝ) ^ n * (Real.sinh (x / 2) * (1 / 2)))
        ((1 / 4 : ℝ) ^ (n + 1) * Real.cosh (x / 2)) x := fun x => by
      have h := ((((hasDerivAt_id x).div_const 2).sinh.mul_const (1 / 2 : ℝ)).const_mul
        ((1 / 4 : ℝ) ^ n))
      refine h.congr_deriv ?_
      simp only [id]; ring
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, iteratedDeriv_succ, iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun x : ℝ => (1 / 4 : ℝ) ^ n * Real.cosh (x / 2)) =
      fun x => (1 / 4 : ℝ) ^ n * (Real.sinh (x / 2) * (1 / 2)) from funext fun y => (hd1 y).deriv]
    exact (hd2 x).deriv

/-- **Independence.** A combination of the even anchors vanishing on a neighbourhood of `0` is
trivial. -/
theorem evenAnchor_combination_eq_zero {N : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {c : Fin (N + 2) → ℝ}
    (h : ∀ x ∈ Ioo (-ρ) ρ, ∑ i, c i * evenAnchor N i x = 0) : c = 0 := by
  set p : ℝ[X] := ∑ i : Fin (N + 1), Polynomial.C (c i.castSucc) * X ^ (2 * (i : ℕ))
  set c' := c (Fin.last (N + 1))
  have hsplit : ∀ x, ∑ i, c i * evenAnchor N i x = p.eval x + c' * Real.cosh (x / 2) := by
    intro x
    rw [Fin.sum_univ_castSucc]
    simp only [evenAnchor_castSucc, evenAnchor_last, p, eval_finsetSum, eval_mul, eval_C,
      eval_pow, eval_X, c']
  have hdeg : p.natDegree ≤ 2 * N := by
    refine (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]
    have := i.2; omega
  have hloc : (fun x : ℝ => p.eval x + c' * Real.cosh (x / 2)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ρ < 0) hρ] with x hx
    rw [← hsplit, h x hx]
  have hc' : c' = 0 := by
    have h0 := hloc.iteratedDeriv_eq (2 * (N + 1))
    have hcosh : ContDiff ℝ ⊤ (fun x : ℝ => Real.cosh (x / 2)) := by fun_prop
    have hpc : ContDiff ℝ ⊤ (fun x : ℝ => p.eval x) := by
      simpa [Polynomial.coe_aeval_eq_eval] using Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) p ⊤
    have hp : ContDiffAt ℝ (↑(2 * (N + 1))) (fun x : ℝ => p.eval x) 0 :=
      hpc.contDiffAt.of_le le_top
    have hq : ContDiffAt ℝ (↑(2 * (N + 1))) (fun x : ℝ => c' * Real.cosh (x / 2)) 0 :=
      (contDiff_const.mul hcosh).contDiffAt.of_le le_top
    have e1 : iteratedDeriv (2 * (N + 1)) (fun x : ℝ => p.eval x) 0 = 0 := by
      rw [_root_.HTGeometry.iteratedDeriv_polynomial_eval, iterate_derivative_eq_zero (by omega)]; simp
    have e2 : iteratedDeriv (2 * (N + 1)) (fun x : ℝ => c' * Real.cosh (x / 2)) 0 =
        c' * (1 / 4 : ℝ) ^ (N + 1) := by
      rw [iteratedDeriv_const_mul (f := fun x : ℝ => Real.cosh (x / 2)) c'
        (hcosh.contDiffAt.of_le le_top), iteratedDeriv_two_mul_cosh_half]
      simp
    rw [show (fun x : ℝ => p.eval x + c' * Real.cosh (x / 2)) =
      (fun x : ℝ => p.eval x) + fun x => c' * Real.cosh (x / 2) from rfl,
      iteratedDeriv_add hp hq, e1, e2, iteratedDeriv_const] at h0
    simp only [zero_add, if_neg (by omega : 2 * (N + 1) ≠ 0)] at h0
    have h4 : (1 / 4 : ℝ) ^ (N + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h0).resolve_right h4
  have hp0 : p = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (fun x hx => ?_) (Set.Ioo_infinite (by linarith : -ρ < ρ))
    have := h x hx
    rw [hsplit, hc', zero_mul, add_zero] at this
    exact this
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hc'
  · have hcoeff := congrArg (fun q : ℝ[X] => q.coeff (2 * (j : ℕ))) hp0
    simp only [p, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hcoeff
    rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [if_neg (fun h => hk (Fin.ext (by omega))), mul_zero]) (by simp), if_pos rfl,
      mul_one] at hcoeff
    exact hcoeff

/-! ## Gram matrix and anchor projection -/

/-- An admissible anchor weight: continuous, nonnegative, positive near `0`, integrable against
all anchor products. -/
structure AnchorWeight (N : ℕ) (ψ : ℝ → ℝ) : Prop where
  continuous : Continuous ψ
  nonneg : ∀ x, 0 ≤ ψ x
  pos : ∃ ρ > 0, ∀ x ∈ Ioo (-ρ) ρ, 0 < ψ x
  integrable : ∀ i j : Fin (N + 2), Integrable fun x => ψ x * evenAnchor N i x * evenAnchor N j x

/-- The Gram matrix `G_ij = ∫ ψ A_i A_j`. -/
def anchorGram (N : ℕ) (ψ : ℝ → ℝ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ :=
  fun i j => ∫ x, ψ x * evenAnchor N i x * evenAnchor N j x

/-- The anchor functionals `r_j(b) = ∫ A_j b`. -/
def anchorMoments (N : ℕ) (b : ℝ → ℝ) : Fin (N + 2) → ℝ :=
  fun j => ∫ x, evenAnchor N j x * b x

/-- The correction coefficients `c(b) = G⁻¹ r(b)`. -/
def anchorCoef (N : ℕ) (ψ b : ℝ → ℝ) : Fin (N + 2) → ℝ :=
  (anchorGram N ψ)⁻¹ *ᵥ anchorMoments N b

/-- The anchor projection `Π b = b - Σ c_i(b) ψ A_i`. -/
def anchorProj (N : ℕ) (ψ b : ℝ → ℝ) (x : ℝ) : ℝ :=
  b x - ∑ i, anchorCoef N ψ b i * (ψ x * evenAnchor N i x)

theorem anchorGram_symm (N : ℕ) (ψ : ℝ → ℝ) (i j : Fin (N + 2)) :
    anchorGram N ψ i j = anchorGram N ψ j i := by
  simp only [anchorGram]; congr 1; ext x; ring

/-- `vᵀ G v = ∫ ψ (Σ v_i A_i)²`. -/
theorem dotProduct_anchorGram_mulVec {N : ℕ} {ψ : ℝ → ℝ} (hw : AnchorWeight N ψ)
    (v : Fin (N + 2) → ℝ) :
    v ⬝ᵥ (anchorGram N ψ *ᵥ v) = ∫ x, ψ x * (∑ i, v i * evenAnchor N i x) ^ 2 := by
  have hint : ∀ i j : Fin (N + 2), Integrable fun x =>
      v i * v j * (ψ x * evenAnchor N i x * evenAnchor N j x) :=
    fun i j => (hw.integrable i j).const_mul _
  have hpt : ∀ x, ψ x * (∑ i, v i * evenAnchor N i x) ^ 2 =
      ∑ i, ∑ j, v i * v j * (ψ x * evenAnchor N i x * evenAnchor N j x) := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp only [dotProduct, mulVec, anchorGram]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; ring

/-- **The Gram matrix is invertible.** -/
theorem AnchorWeight.isUnit_det {N : ℕ} {ψ : ℝ → ℝ} (hw : AnchorWeight N ψ) :
    IsUnit (anchorGram N ψ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hq := dotProduct_anchorGram_mulVec hw v
  rw [hGv, dotProduct_zero] at hq
  set F : ℝ → ℝ := fun x => ψ x * (∑ i, v i * evenAnchor N i x) ^ 2
  have hFc : Continuous F := hw.continuous.mul
    ((continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_evenAnchor N i)).pow 2)
  have hF0 : 0 ≤ F := fun x => mul_nonneg (hw.nonneg x) (sq_nonneg _)
  have hFi : Integrable F := by
    have : F = fun x => ∑ i, ∑ j, v i * v j * (ψ x * evenAnchor N i x * evenAnchor N j x) := by
      funext x
      simp only [F]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hw.integrable i j).const_mul _
  have hae := (integral_eq_zero_iff_of_nonneg hF0 hFi).mp hq.symm
  have hzero : F = 0 := (Continuous.ae_eq_iff_eq volume hFc continuous_const).mp hae
  obtain ⟨ρ, hρ, hpos⟩ := hw.pos
  apply hv
  refine evenAnchor_combination_eq_zero hρ fun x hx => ?_
  have h := congrFun hzero x
  simp only [F, Pi.zero_apply] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (hpos x hx).ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

/-- **The projection kills every anchor.** `∫ A_j Π b = 0`. -/
theorem integral_evenAnchor_mul_anchorProj {N : ℕ} {ψ b : ℝ → ℝ} (hw : AnchorWeight N ψ)
    (hb : ∀ j, Integrable fun x => evenAnchor N j x * b x) (j : Fin (N + 2)) :
    ∫ x, evenAnchor N j x * anchorProj N ψ b x = 0 := by
  have hint : ∀ i, Integrable fun x =>
      evenAnchor N j x * (anchorCoef N ψ b i * (ψ x * evenAnchor N i x)) := fun i => by
    refine ((hw.integrable i j).const_mul (anchorCoef N ψ b i)).congr
      (Eventually.of_forall fun x => ?_)
    ring
  have hsum : (fun x => evenAnchor N j x * anchorProj N ψ b x) =
      fun x => evenAnchor N j x * b x -
        ∑ i, evenAnchor N j x * (anchorCoef N ψ b i * (ψ x * evenAnchor N i x)) := by
    funext x; rw [anchorProj, mul_sub, Finset.mul_sum]
  rw [hsum, integral_sub (hb j) (integrable_finsetSum _ fun i _ => hint i),
    integral_finsetSum _ fun i _ => hint i]
  have hGc : anchorGram N ψ *ᵥ anchorCoef N ψ b = anchorMoments N b := by
    rw [anchorCoef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hw.isUnit_det,
      Matrix.one_mulVec]
  have hj := congrFun hGc j
  simp only [mulVec, dotProduct, anchorMoments] at hj
  rw [← hj, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [anchorGram_symm, anchorGram, ← integral_mul_const]
  congr 1; ext x; ring

theorem anchorProj_neg {N : ℕ} {ψ b : ℝ → ℝ} (hψ : ∀ x, ψ (-x) = ψ x) (hb : ∀ x, b (-x) = b x)
    (x : ℝ) : anchorProj N ψ b (-x) = anchorProj N ψ b x := by
  simp only [anchorProj, hψ, hb, evenAnchor_neg]

/-- Vanishing anchor data give vanishing correction coefficients. -/
theorem tendsto_anchorCoef {α : Type*} {l : Filter α} {N : ℕ} {ψ : ℝ → ℝ} {b : α → ℝ → ℝ}
    (hb : ∀ j, Tendsto (fun u => anchorMoments N (b u) j) l (𝓝 0)) (i : Fin (N + 2)) :
    Tendsto (fun u => anchorCoef N ψ (b u) i) l (𝓝 0) := by
  simp only [anchorCoef, mulVec, dotProduct]
  have := tendsto_finsetSum (Finset.univ : Finset (Fin (N + 2)))
    (fun j _ => (hb j).const_mul ((anchorGram N ψ)⁻¹ i j))
  simpa using this

end

end GaloisForLFunctions.HTGeometry
