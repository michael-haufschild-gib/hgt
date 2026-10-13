import GaloisForLFunctions.RHTower.JointAncestryTypicalCapExpansion

/-!
# The coherent exponential model for one zero

Fix coefficients `A_i, B_i` with `½(|A_i| + |B_i|) ≤ ½`, and consider the shifted product
`∏_i g_i(k_i + j)`, `g_i(x) = 1 + ½(ω^x A_i + ω^{−x} B_i)`.  Let `Z(k) = Σ_i a_i ω^{−k_i}`.

**Theorem** (`norm_prod_phaseFactor_shift_sub_exp_le`).  For complex numbers `X, Y`, put
`m = ω^{−j} X Z(k) + ω^j Y Z̄(k)` and
`Δ = |S − XZ| + |T − YZ̄| + ½|Q| + ½|Q'| + ¼|Σ A_iB_i| + (2/3)Σ(½(|A_i| + |B_i|))³`,
where `S = Σ ½B_i ω^{−k_i}`, `T = Σ ½A_i ω^{k_i}`, `Q = Σ (½B_i)² ω^{−2k_i}` and
`Q' = Σ (½A_i)² ω^{2k_i}`.  If `Δ ≤ 1` then `|∏_i g_i(k_i + j) − e^m| ≤ 2 e^{|m|} Δ` for every `j`.

Proof.  With `u_i = ω^j·½A_iω^{k_i} + ω^{−j}·½B_iω^{−k_i}`, the second-order expansion gives
`∏(1 + u_i) = exp(Σu_i − ½Σu_i² + E)`.  Here `Σu_i = ω^jT + ω^{−j}S`,
`Σu_i² = ω^{2j}Q' + ω^{−2j}Q + ½ΣA_iB_i` (the cross terms carry `|ω|² = 1`), and
`|E| ≤ (2/3)Σ|u_i|³`.  So the exponent differs from `m` by at most `Δ`, uniformly in `j`.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The coherent exponential model.** -/
theorem norm_prod_phaseFactor_shift_sub_exp_le {N : ℕ} (hN : 0 < N) (A B : ι → ℂ)
    (a₀ : ι → ℝ) (Xc Yc : ℂ) (k : ι → Fin N) (j : Fin N)
    (hAB : ∀ i, 1 / 2 * (‖A i‖ + ‖B i‖) ≤ 1 / 2)
    (hΔ : ‖∑ i, 1 / 2 * B i * conj (unitRoot N ^ ((k i : Fin N) : ℕ)) -
        Xc * ∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ))‖ +
      ‖∑ i, 1 / 2 * A i * unitRoot N ^ ((k i : Fin N) : ℕ) -
        Yc * conj (∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ)))‖ +
      1 / 2 * ‖∑ i, (1 / 2 * B i) ^ 2 * conj (unitRoot N ^ ((k i : Fin N) : ℕ)) ^ 2‖ +
      1 / 2 * ‖∑ i, (1 / 2 * A i) ^ 2 * (unitRoot N ^ ((k i : Fin N) : ℕ)) ^ 2‖ +
      1 / 4 * ‖∑ i, A i * B i‖ + 2 / 3 * ∑ i, (1 / 2 * (‖A i‖ + ‖B i‖)) ^ 3 ≤ 1) :
    ‖∏ i, phaseFactor N (1 / 2) (A i) (B i) (phaseShift j k i) -
        Complex.exp (conj (unitRoot N ^ (j : ℕ)) *
          (Xc * ∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ))) +
          unitRoot N ^ (j : ℕ) *
            (Yc * conj (∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ)))))‖ ≤
      2 * Real.exp ‖conj (unitRoot N ^ (j : ℕ)) *
          (Xc * ∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ))) +
          unitRoot N ^ (j : ℕ) *
            (Yc * conj (∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ))))‖ *
        (‖∑ i, 1 / 2 * B i * conj (unitRoot N ^ ((k i : Fin N) : ℕ)) -
          Xc * ∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ))‖ +
        ‖∑ i, 1 / 2 * A i * unitRoot N ^ ((k i : Fin N) : ℕ) -
          Yc * conj (∑ i, (a₀ i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ)))‖ +
        1 / 2 * ‖∑ i, (1 / 2 * B i) ^ 2 * conj (unitRoot N ^ ((k i : Fin N) : ℕ)) ^ 2‖ +
        1 / 2 * ‖∑ i, (1 / 2 * A i) ^ 2 * (unitRoot N ^ ((k i : Fin N) : ℕ)) ^ 2‖ +
        1 / 4 * ‖∑ i, A i * B i‖ + 2 / 3 * ∑ i, (1 / 2 * (‖A i‖ + ‖B i‖)) ^ 3) := by
  set w := unitRoot N ^ (j : ℕ) with hw
  set e : ι → ℂ := fun i => unitRoot N ^ ((k i : Fin N) : ℕ) with he
  have hww : w * conj w = 1 := unitRoot_pow_mul_conj N (j : ℕ)
  have hee : ∀ i, e i * conj (e i) = 1 := fun i => unitRoot_pow_mul_conj N _
  have hnw : ‖w‖ = 1 := norm_unitRoot_pow N _
  have hne : ∀ i, ‖e i‖ = 1 := fun i => norm_unitRoot_pow N _
  set u : ι → ℂ := fun i => w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i)) with hu
  have hfac : ∀ i, phaseFactor N (1 / 2) (A i) (B i) (phaseShift j k i) = 1 + u i := by
    intro i
    unfold phaseFactor phaseShift
    rw [unitRoot_pow_add_fin hN, map_mul]
    simp only [hu, he, hw]
    push_cast; ring
  rw [Finset.prod_congr rfl fun i _ => hfac i]
  have he' : ∀ i, unitRoot N ^ ((k i : Fin N) : ℕ) = e i := fun i => rfl
  simp only [he'] at hΔ ⊢
  clear_value w e u
  subst hu
  have hn1 : ‖conj w‖ = 1 := by rw [Complex.norm_conj, hnw]
  have hnu : ∀ i, ‖w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))‖ ≤
      1 / 2 * (‖A i‖ + ‖B i‖) := by
    intro i
    have h1 : ‖w * (1 / 2 * A i * e i)‖ = 1 / 2 * ‖A i‖ := by
      rw [norm_mul, norm_mul, norm_mul, hnw, hne]; norm_num
    have h2 : ‖conj w * (1 / 2 * B i * conj (e i))‖ = 1 / 2 * ‖B i‖ := by
      rw [norm_mul, norm_mul, norm_mul, hn1, Complex.norm_conj, hne]; norm_num
    have := norm_add_le (w * (1 / 2 * A i * e i)) (conj w * (1 / 2 * B i * conj (e i)))
    linarith
  obtain ⟨E, hE, hprod⟩ := exists_prod_one_add_eq_exp_second_order
    (fun i => w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i)))
    (fun i => (hnu i).trans (hAB i))
  rw [hprod]
  have hsum1 : ∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) =
      w * ∑ i, 1 / 2 * A i * e i + conj w * ∑ i, 1 / 2 * B i * conj (e i) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hsum2 : ∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) ^ 2 =
      w ^ 2 * ∑ i, (1 / 2 * A i) ^ 2 * e i ^ 2 +
      conj w ^ 2 * ∑ i, (1 / 2 * B i) ^ 2 * conj (e i) ^ 2 + 1 / 2 * ∑ i, A i * B i := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : (w * conj w) * (e i * conj (e i)) = 1 := by rw [hww, hee i, one_mul]
    linear_combination (1 / 2 * A i * B i) * h3
  set Z := ∑ i, (a₀ i : ℂ) * conj (e i) with hZ
  set m := conj w * (Xc * Z) + w * (Yc * conj Z) with hm
  set X1 := ∑ i, 1 / 2 * B i * conj (e i) - Xc * Z with hX1
  set X2 := ∑ i, 1 / 2 * A i * e i - Yc * conj Z with hX2
  set X3 := ∑ i, (1 / 2 * B i) ^ 2 * conj (e i) ^ 2 with hX3
  set X4 := ∑ i, (1 / 2 * A i) ^ 2 * e i ^ 2 with hX4
  set X5 := ∑ i, A i * B i with hX5
  set Δ := ‖X1‖ + ‖X2‖ + 1 / 2 * ‖X3‖ + 1 / 2 * ‖X4‖ + 1 / 4 * ‖X5‖ +
      2 / 3 * ∑ i, (1 / 2 * (‖A i‖ + ‖B i‖)) ^ 3 with hΔdef
  have hid : (∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) -
      (∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) ^ 2) / 2 + E) - m =
      conj w * X1 + w * X2 + (-(1 / 2) * conj w ^ 2) * X3 + (-(1 / 2) * w ^ 2) * X4 +
        (-(1 / 4)) * X5 + E := by
    rw [hsum1, hsum2, hm, hX1, hX2, hX3, hX4, hX5]; ring
  have hEle : ‖E‖ ≤ 2 / 3 * ∑ i, (1 / 2 * (‖A i‖ + ‖B i‖)) ^ 3 := by
    refine hE.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num))
    exact pow_le_pow_left₀ (norm_nonneg _) (hnu i) 3
  have t1 : ‖conj w * X1‖ = ‖X1‖ := by rw [norm_mul, hn1, one_mul]
  have t2 : ‖w * X2‖ = ‖X2‖ := by rw [norm_mul, hnw, one_mul]
  have t3 : ‖(-(1 / 2) * conj w ^ 2) * X3‖ = 1 / 2 * ‖X3‖ := by
    rw [norm_mul, norm_mul, norm_pow, hn1]; norm_num
  have t4 : ‖(-(1 / 2) * w ^ 2) * X4‖ = 1 / 2 * ‖X4‖ := by
    rw [norm_mul, norm_mul, norm_pow, hnw]; norm_num
  have t5 : ‖(-(1 / 4) : ℂ) * X5‖ = 1 / 4 * ‖X5‖ := by rw [norm_mul]; norm_num
  have hdiff : ‖(∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) -
      (∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) ^ 2) / 2 + E) - m‖
      ≤ Δ := by
    rw [hid]
    have a1 := norm_add_le (conj w * X1 + w * X2 + (-(1 / 2) * conj w ^ 2) * X3 +
      (-(1 / 2) * w ^ 2) * X4 + (-(1 / 4)) * X5) E
    have a2 := norm_add_le (conj w * X1 + w * X2 + (-(1 / 2) * conj w ^ 2) * X3 +
      (-(1 / 2) * w ^ 2) * X4) ((-(1 / 4)) * X5)
    have a3 := norm_add_le (conj w * X1 + w * X2 + (-(1 / 2) * conj w ^ 2) * X3)
      ((-(1 / 2) * w ^ 2) * X4)
    have a4 := norm_add_le (conj w * X1 + w * X2) ((-(1 / 2) * conj w ^ 2) * X3)
    have a5 := norm_add_le (conj w * X1) (w * X2)
    rw [hΔdef]
    linarith
  have hΔ1 : Δ ≤ 1 := hΔ
  refine (norm_cexp_sub_cexp_le_two_mul (hdiff.trans hΔ1)).trans ?_
  have hre : Real.exp m.re ≤ Real.exp ‖m‖ := Real.exp_le_exp.mpr (Complex.re_le_norm m)
  have := Real.exp_pos m.re
  have hd0 := norm_nonneg ((∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) -
      (∑ i, (w * (1 / 2 * A i * e i) + conj w * (1 / 2 * B i * conj (e i))) ^ 2) / 2 + E) - m)
  nlinarith [hdiff]

end

end RHTower
