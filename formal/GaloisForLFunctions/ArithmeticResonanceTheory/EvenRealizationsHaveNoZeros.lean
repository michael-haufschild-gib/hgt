import GaloisForLFunctions.HTGeometry.FiniteDeterminantLogSeries
import GaloisForLFunctions.RHTower.ZetaResidueFactorDerivative

/-!
# Even realizations have no zeros

A finite weighted graph — vertices `Fin n`, edges `e` from `src e` to `tgt e` with length `r e > 0`
and coefficient `c e` — has transfer matrix `M(s)_{ij} = Σ_{e : i → j} c_e e^{−s r_e}`
(`graphMatrix`). Its closed walks of length `k` are counted by `tr M(s)^k`, and its dynamical zeta
function is `Z(s) = exp Σ_{k ≥ 1} tr M(s)^k / k` (`graphZeta`).

**Theorem** (`graphZeta_mul_det_eq_one`). Far enough to the right, `Z(s) · det(1 − M(s)) = 1`.
The determinant is entire (`differentiable_det_one_sub_graphMatrix`), so `Z` continues to the
reciprocal of an entire function: an *even* realization has poles and no zeros. Zeros of a
dynamical zeta function need an *odd* part, `det(1 − L⁻_s)/det(1 − L⁺_s)`; over `𝔽_q` this is
`H¹` of the curve.

**Corollary** (`riemannZeta_ne_graphZeta`). `ζ` is the dynamical zeta function of no finite
weighted graph: `(s − 1) ζ(s) · det(1 − M(s)) = s − 1` would hold on `ℂ` by the identity theorem,
and the trivial zero `ζ(−2) = 0` breaks it.

The matrix identity `det(1 − A) = exp(−Σ_k tr Aᵏ/k)` is the corpus's Schur-triangulation formula
(`exp_neg_traceSeries_eq_finiteDet2_neg`), with the trace bound `|tr A^{k+1}| ≤ (n a)^{k+1}` for
entries bounded by `a` (`norm_trace_pow_succ_le`).
-/

open Matrix Finset Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-! ## Trace bounds and the determinant identity -/

/-- Entries of powers: `n |(A^{k+1})ᵢⱼ| ≤ (n a)^{k+1}` when every entry of `A` is bounded by `a`. -/
theorem mul_norm_pow_succ_apply_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ i j, ‖A i j‖ ≤ a) (k : ℕ) (i j : Fin n) :
    (n : ℝ) * ‖(A ^ (k + 1)) i j‖ ≤ ((n : ℝ) * a) ^ (k + 1) := by
  induction k generalizing i j with
  | zero =>
    rw [zero_add, pow_one, pow_one]
    exact mul_le_mul_of_nonneg_left (ha i j) (Nat.cast_nonneg n)
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    have hsum : ‖∑ l, (A ^ (k + 1)) i l * A l j‖ ≤ ∑ _l : Fin n, ((n : ℝ) * a) ^ (k + 1) / n * a := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_mul]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact absurd l.2 (by omega)
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have h1 : ‖(A ^ (k + 1)) i l‖ ≤ ((n : ℝ) * a) ^ (k + 1) / n := by
          rw [le_div_iff₀ hn', mul_comm]; exact ih i l
        exact mul_le_mul h1 (ha l j) (norm_nonneg _) (by positivity)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      calc (n : ℝ) * ‖∑ l, (A ^ (k + 1)) i l * A l j‖
          ≤ n * (n * (((n : ℝ) * a) ^ (k + 1) / n * a)) := mul_le_mul_of_nonneg_left hsum hn'.le
        _ = ((n : ℝ) * a) ^ (k + 1 + 1) := by field_simp; ring

/-- `|tr A^{k+1}| ≤ (n a)^{k+1}` when every entry of `A` is bounded by `a`. -/
theorem norm_trace_pow_succ_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ i j, ‖A i j‖ ≤ a) (k : ℕ) : ‖(A ^ (k + 1)).trace‖ ≤ ((n : ℝ) * a) ^ (k + 1) := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc ∑ i, ‖Matrix.diag (A ^ (k + 1)) i‖ ≤ ∑ _i : Fin n, ((n : ℝ) * a) ^ (k + 1) / n :=
          Finset.sum_le_sum fun i _ => by
            rw [Matrix.diag, le_div_iff₀ hn', mul_comm]
            exact mul_norm_pow_succ_apply_le A ha0 ha k i i
      _ = ((n : ℝ) * a) ^ (k + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

/-- **The determinant identity.** If every entry of `A` is bounded by `a` with `n a < 1`, then
`det(1 − A) = exp(−Σ_{k ≥ 1} tr Aᵏ/k)`. -/
theorem det_one_sub_eq_exp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ i j, ‖A i j‖ ≤ a) (hna : (n : ℝ) * a < 1) :
    (1 - A).det = Complex.exp (-∑' k : ℕ, (A ^ (k + 1)).trace / ((k + 1 : ℕ) : ℂ)) := by
  -- the Hilbert–Schmidt norm is at most `n a`
  have hHS : Real.sqrt (matHSNormSq A) ≤ (n : ℝ) * a := by
    rw [Real.sqrt_le_left (by positivity), matHSNormSq]
    calc ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℕ) ≤ ∑ _i : Fin n, ∑ _j : Fin n, a ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2
      _ = ((n : ℝ) * a) ^ 2 := by simp; ring
  have hz : ‖(1 : ℂ)‖ * Real.sqrt (matHSNormSq A) < 1 := by rw [norm_one, one_mul]; linarith
  have h := exp_neg_traceSeries_eq_finiteDet2_neg A hz
  have hdet : finiteDet2 (-A) 1 = (1 - A).det * Complex.exp A.trace := by
    simp only [finiteDet2, one_smul, Matrix.trace_neg, one_mul, neg_neg, ← sub_eq_add_neg]
  -- summability of the trace series
  have hsum : Summable fun k : ℕ => (A ^ (k + 1)).trace / ((k + 1 : ℕ) : ℂ) := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (by positivity) hna)
      fun k => ?_
    rw [norm_div, Complex.norm_natCast]
    have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    calc ‖(A ^ (k + 1)).trace‖ / ((k + 1 : ℕ) : ℝ) ≤ ‖(A ^ (k + 1)).trace‖ :=
          div_le_self (norm_nonneg _) h1
      _ ≤ ((n : ℝ) * a) ^ (k + 1) := norm_trace_pow_succ_le A ha0 ha k
      _ ≤ ((n : ℝ) * a) ^ k := pow_le_pow_of_le_one (by positivity) hna.le (by omega)
  have hsplit : ∑' k : ℕ, (A ^ (k + 1)).trace / ((k + 1 : ℕ) : ℂ) =
      A.trace + ∑' k : ℕ, (1 : ℂ) ^ (k + 2) / ((k + 2 : ℕ) : ℂ) * (A ^ (k + 2)).trace := by
    rw [hsum.tsum_eq_zero_add]
    simp only [zero_add, pow_one, Nat.cast_one, div_one, one_pow, one_div]
    congr 1
    exact tsum_congr fun k => by rw [div_eq_inv_mul]
  rw [hsplit, neg_add, Complex.exp_add, h, hdet, mul_comm (Complex.exp _), mul_assoc,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-! ## Finite weighted graphs -/

variable {n : ℕ} {E : Type*} [Fintype E]

/-- The transfer matrix `M(s)_{ij} = Σ_{e : i → j} c_e e^{−s r_e}` of a finite weighted graph. -/
noncomputable def graphMatrix (src tgt : E → Fin n) (r : E → ℝ) (c : E → ℂ) (s : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ e, if src e = i ∧ tgt e = j then c e * Complex.exp (-(s * r e)) else 0

/-- The dynamical zeta function `exp Σ_{k ≥ 1} tr M(s)^k / k` of a finite weighted graph. -/
noncomputable def graphZeta (src tgt : E → Fin n) (r : E → ℝ) (c : E → ℂ) (s : ℂ) : ℂ :=
  Complex.exp (∑' k : ℕ, (graphMatrix src tgt r c s ^ (k + 1)).trace / ((k + 1 : ℕ) : ℂ))

theorem differentiable_det_one_sub_graphMatrix (src tgt : E → Fin n) (r : E → ℝ) (c : E → ℂ) :
    Differentiable ℂ fun s => (1 - graphMatrix src tgt r c s).det := by
  have hrw : (fun s => (1 - graphMatrix src tgt r c s).det) = fun s =>
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∏ i,
        ((if σ i = i then (1 : ℂ) else 0) -
          ∑ e, if src e = σ i ∧ tgt e = i then c e * Complex.exp (-(s * r e)) else 0) := by
    funext s
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    simp [graphMatrix, Matrix.one_apply]
  rw [hrw]
  refine Differentiable.fun_sum fun σ _ => (differentiable_const _).mul ?_
  refine Differentiable.fun_finsetProd fun i _ => (differentiable_const _).sub ?_
  refine Differentiable.fun_sum fun e _ => ?_
  split_ifs
  · exact (differentiable_const _).mul (Complex.differentiable_exp.comp (by fun_prop))
  · exact differentiable_const _

/-- **Even realizations are pole-only.** If all lengths are positive, then far to the right
`Z(s) · det(1 − M(s)) = 1`. -/
theorem graphZeta_mul_det_eq_one (src tgt : E → Fin n) {r : E → ℝ} (hr : ∀ e, 0 < r e)
    (c : E → ℂ) : ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
      graphZeta src tgt r c s * (1 - graphMatrix src tgt r c s).det = 1 := by
  classical
  -- a uniform rate: every entry is at most `C e^{−ρ σ}` with `ρ = min r`
  obtain ⟨ρ, hρ, hρr⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ e, ρ ≤ r e := by
    rcases isEmpty_or_nonempty E with hE | hE
    · exact ⟨1, one_pos, fun e => isEmptyElim e⟩
    · obtain ⟨e₀, -, he₀⟩ := Finset.exists_min_image Finset.univ r Finset.univ_nonempty
      exact ⟨r e₀, hr e₀, fun e => he₀ e (Finset.mem_univ e)⟩
  set C : ℝ := ∑ e, ‖c e‖ with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun e _ => norm_nonneg _
  -- choose `σ₁ ≥ 0` with `n C e^{−ρ σ₁} < 1`
  obtain ⟨σ₁, hσ₁0, hσ₁⟩ : ∃ σ₁ : ℝ, 0 ≤ σ₁ ∧ (n : ℝ) * (C * Real.exp (-(ρ * σ₁))) < 1 := by
    have ht : Tendsto (fun σ : ℝ => (n : ℝ) * (C * Real.exp (-(ρ * σ)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun σ : ℝ => -(ρ * σ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hρ)
      simpa using ((Real.tendsto_exp_atBot.comp h1).const_mul C).const_mul (n : ℝ)
    obtain ⟨σ, hσ⟩ := ((ht.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop 0)).exists
    exact ⟨σ, hσ.2, hσ.1⟩
  refine ⟨σ₁, fun s hs => ?_⟩
  set a : ℝ := C * Real.exp (-(ρ * σ₁)) with ha
  have hentry : ∀ i j, ‖graphMatrix src tgt r c s i j‖ ≤ a := by
    intro i j
    refine (norm_sum_le _ _).trans ?_
    rw [ha, hC, Finset.sum_mul]
    refine Finset.sum_le_sum fun e _ => ?_
    split_ifs
    · rw [norm_mul, Complex.norm_exp]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      have hre : (-(s * (r e : ℂ))).re = -(s.re * r e) := by simp
      rw [hre]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.le) (hr e).le,
        mul_nonneg hσ₁0 (sub_nonneg.mpr (hρr e))]
    · rw [norm_zero]; positivity
  have hdet := det_one_sub_eq_exp (graphMatrix src tgt r c s) (by positivity) hentry hσ₁
  rw [hdet, graphZeta, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- **`ζ` is not the dynamical zeta function of a finite weighted graph.** -/
theorem riemannZeta_ne_graphZeta (src tgt : E → Fin n) {r : E → ℝ} (hr : ∀ e, 0 < r e)
    (c : E → ℂ) : ¬ ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → riemannZeta s = graphZeta src tgt r c s := by
  rintro ⟨σ₀, hσ₀⟩
  obtain ⟨σ₁, hσ₁⟩ := graphZeta_mul_det_eq_one src tgt hr c
  set D : ℂ → ℂ := fun s => (1 - graphMatrix src tgt r c s).det with hD
  -- `(s − 1) ζ(s) D(s) = s − 1` to the right, hence everywhere
  set σ₂ : ℝ := max (max σ₀ σ₁) 1 with hσ₂
  have hright : ∀ s : ℂ, σ₂ < s.re → RHTower.zetaResidueFactor s * D s = s - 1 := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by
      rw [h, Complex.one_re] at hs; linarith [le_max_right (max σ₀ σ₁) 1]
    rw [RHTower.zetaResidueFactor_of_ne hs1, mul_assoc,
      hσ₀ s (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs),
      hσ₁ s (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs), mul_one]
  have hent : Differentiable ℂ fun s => RHTower.zetaResidueFactor s * D s :=
    RHTower.differentiable_zetaResidueFactor.mul (differentiable_det_one_sub_graphMatrix src tgt r c)
  have hlin : Differentiable ℂ fun s : ℂ => s - 1 := by fun_prop
  set z₀ : ℂ := ((σ₂ + 1 : ℝ) : ℂ) with hz₀
  have hev : (fun s => RHTower.zetaResidueFactor s * D s) =ᶠ[𝓝 z₀] fun s => s - 1 := by
    have hopen : IsOpen {s : ℂ | σ₂ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show σ₂ < z₀.re by simp [hz₀])] with s hs
    exact hright s hs
  have heq := (hent.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hlin.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ z₀) hev
    (Set.mem_univ (-2))
  -- the trivial zero `ζ(−2) = 0`
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  have hne : (-2 : ℂ) ≠ 1 := by norm_num
  simp only [RHTower.zetaResidueFactor_of_ne hne, hz, mul_zero, zero_mul] at heq
  norm_num at heq

end GaloisForLFunctions.ArithmeticResonanceTheory
