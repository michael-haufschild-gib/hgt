import GaloisForLFunctions.HTGeometry.KleinbockMargulis.PolynomialGood


/-!
# Lagrange extrapolation and a Remez inequality without factorial loss

For nodes `v_0, …, v_k` with `|v_i - v_j| ≥ |i - j| δ` the Lagrange basis satisfies
`∑_i |ℓ_i(x)| ≤ (2b/δ)^k / k!` wherever `|x - v_i| ≤ b`, because `∏_{j ≠ i} |i - j| = i!(k-i)!` and
`∑_i 1/(i!(k-i)!) = 2^k/k!`.  Consequences, all with losses exponential (not factorial) in `k`:

* `abs_eval_le_extrapolate`, `abs_eval_derivative_le_extrapolate`: a polynomial bounded by `M`
  on `[α, β]` satisfies `|P(y)| ≤ M (2e(y-α)/(β-α))^k` and
  `|P'(y)| ≤ M (k/(y-α)) (2e(y-α)/(β-α))^k` for `y ≥ β`;
* `volume_sublevel_comp_le`: a Remez inequality in a monotone chart `g` expanding distances by
  `λ`: `|{u : |P(g u)| ≤ ε}| ≤ 4e b/(λ q)` whenever `ε q^k < |P(z)|` and `|z - g u| ≤ b`.
-/

open Finset Polynomial MeasureTheory Set
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- `∏_{j ≠ i} |i - j| = i! (k - i)!` over the nodes `0, …, k`. -/
theorem prod_erase_abs_sub_fin (k : ℕ) (i : Fin (k + 1)) :
    ∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| = ((i : ℕ)! : ℝ) * ((k - i)! : ℝ) := by
  classical
  set g : ℕ → ℝ := fun j => if j = (i : ℕ) then 1 else |((i : ℕ) : ℝ) - (j : ℝ)| with hg
  have h1 : ∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| =
      ∏ j : Fin (k + 1), g j := by
    rw [← Finset.prod_erase_mul _ _ (mem_univ i)]
    have hgi : g i = 1 := by simp [hg]
    rw [hgi, mul_one]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ (i : ℕ) := fun h => (Finset.ne_of_mem_erase hj) (Fin.ext h)
    simp [hg, hne]
  rw [h1, Fin.prod_univ_eq_prod_range (fun j => g j) (k + 1)]
  have hi : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.2
  rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive _ (Nat.zero_le (i : ℕ))
    (by omega : (i : ℕ) ≤ k + 1)]
  rw [Finset.prod_eq_prod_Ico_succ_bot (by omega : (i : ℕ) < k + 1)]
  have hgi : g i = 1 := by simp [hg]
  rw [hgi, one_mul]
  congr 1
  · rw [← Finset.range_eq_Ico]
    rw [← Finset.prod_range_reflect]
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : j < (i : ℕ) := Finset.mem_range.mp hj
    have hne : (i : ℕ) - 1 - j ≠ (i : ℕ) := by omega
    simp only [hg, hne, if_false]
    rw [abs_of_nonneg (by
      have : (((i : ℕ) - 1 - j : ℕ) : ℝ) ≤ (i : ℕ) := by exact_mod_cast (by omega : (i:ℕ) - 1 - j ≤ i)
      linarith)]
    rw [Nat.cast_sub (by omega : j ≤ (i : ℕ) - 1), Nat.cast_sub (by omega : 1 ≤ (i : ℕ))]
    ring
  · rw [Finset.prod_Ico_eq_prod_range]
    rw [show k + 1 - ((i : ℕ) + 1) = k - (i : ℕ) by omega]
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    refine Finset.prod_congr rfl fun m _ => ?_
    have hne : (i : ℕ) + 1 + m ≠ (i : ℕ) := by omega
    simp only [hg, hne, if_false]
    push_cast
    rw [abs_of_nonpos (by linarith)]
    ring

/-- `∑_i 1/(i!(k-i)!) = 2^k / k!`. -/
theorem sum_inv_prod_erase_abs_sub_fin (k : ℕ) :
    ∑ i : Fin (k + 1), (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ =
      2 ^ k / (k ! : ℝ) := by
  simp_rw [prod_erase_abs_sub_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => (((i)! : ℝ) * ((k - i)! : ℝ))⁻¹) (k + 1)]
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hk, Finset.sum_mul]
  have hc := congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_range_choose k)
  push_cast at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.choose_eq_factorial_div_factorial hik]
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hik) (by positivity)]
  push_cast
  field_simp


/-- Nodes separated in proportion to their index distance are injective. -/
theorem injective_of_index_sep {k : ℕ} {v : Fin (k + 1) → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j|) :
    Function.Injective v := by
  intro i j hij
  by_contra hne
  have hne' : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := fun h => hne (Fin.ext (by exact_mod_cast h))
  have h1 : 1 ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne hne' with h | h
    · have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
        have : (i : ℕ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
        exact_mod_cast this
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
        have : (j : ℕ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
        exact_mod_cast this
      rw [abs_of_pos (by linarith)]; linarith
  have := hsep i j
  rw [hij, sub_self, abs_zero] at this
  nlinarith

/-- Bound on one Lagrange basis polynomial at nodes separated in proportion to index distance. -/
theorem abs_eval_lagrangeBasis_le {k : ℕ} (v : Fin (k + 1) → ℝ) {δ b : ℝ} (hδ : 0 < δ)
    (hb : 0 ≤ b)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j|)
    {x : ℝ} (hx : ∀ i, |x - v i| ≤ b) (i : Fin (k + 1)) :
    |(Lagrange.basis univ v i).eval x| ≤
      (b / δ) ^ k * (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
  classical
  have hprod : (Lagrange.basis univ v i).eval x
      = ∏ j ∈ univ.erase i, (v i - v j)⁻¹ * (x - v j) := by
    simp [Lagrange.basis, eval_prod, Lagrange.basisDivisor]
  rw [hprod, Finset.abs_prod]
  have hcard : (univ.erase i).card = k := by
    rw [Finset.card_erase_of_mem (mem_univ i)]; simp
  have hle : ∀ j ∈ univ.erase i, |(v i - v j)⁻¹ * (x - v j)| ≤
      (b / δ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹ := by
    intro j hj
    have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hij : 0 < |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rw [abs_pos, sub_ne_zero]
      exact fun h => hne (Fin.ext (by exact_mod_cast h))
    have h1 := hsep i j
    rw [abs_mul, abs_inv]
    have hvpos : 0 < |v i - v j| := lt_of_lt_of_le (mul_pos hij hδ) h1
    rw [show (b / δ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹ =
      b / (|((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ) by field_simp]
    rw [inv_mul_eq_div]
    exact div_le_div₀ hb (hx j) (mul_pos hij hδ) h1
  calc ∏ j ∈ univ.erase i, |(v i - v j)⁻¹ * (x - v j)|
      ≤ ∏ j ∈ univ.erase i, ((b / δ) * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹) :=
        Finset.prod_le_prod (fun j _ => abs_nonneg _) hle
    _ = (b / δ) ^ k * (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, Finset.prod_inv_distrib]

/-- Lagrange expansion of a polynomial of degree at most `k` at `k+1` distinct nodes. -/
theorem eval_eq_sum_lagrangeBasis {k : ℕ} (P : ℝ[X]) (hdeg : P.natDegree ≤ k)
    (v : Fin (k + 1) → ℝ) (hinj : Function.Injective v) (x : ℝ) :
    P.eval x = ∑ i : Fin (k + 1), P.eval (v i) * (Lagrange.basis univ v i).eval x := by
  classical
  have hcard : (univ : Finset (Fin (k + 1))).card = k + 1 := by simp
  have hdlt : P.degree < ((univ : Finset (Fin (k + 1))).card : ℕ) := by
    rw [hcard]
    rcases eq_or_ne P 0 with rfl | hP
    · simp
    · exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hP := Lagrange.eq_interpolate hinj.injOn hdlt
  conv_lhs => rw [hP]
  simp [Lagrange.interpolate_apply, eval_finsetSum]

/-- **Lagrange bound without factorial loss.**  If `|P| ≤ ε` at `k+1` nodes with
`|v_i - v_j| ≥ |i - j| δ`, then `|P(x)| ≤ ε (2b/δ)^k / k!` wherever `|x - v_i| ≤ b` for all `i`. -/
theorem abs_eval_le_of_lagrange_indexSep {k : ℕ} (P : ℝ[X]) (hdeg : P.natDegree ≤ k)
    (v : Fin (k + 1) → ℝ) {ε δ b : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b)
    (hbound : ∀ i, |P.eval (v i)| ≤ ε)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j|)
    {x : ℝ} (hx : ∀ i, |x - v i| ≤ b) :
    |P.eval x| ≤ ε * (2 * b / δ) ^ k / (k ! : ℝ) := by
  classical
  have hinj := injective_of_index_sep hδ hsep
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hbound 0)
  rw [eval_eq_sum_lagrangeBasis P hdeg v hinj x]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin (k + 1), |P.eval (v i) * (Lagrange.basis univ v i).eval x|
      ≤ ∑ i : Fin (k + 1), ε * ((b / δ) ^ k *
          (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hbound i) (abs_eval_lagrangeBasis_le v hδ hb hsep hx i)
          (abs_nonneg _) hε
    _ = ε * (b / δ) ^ k * (2 ^ k / (k ! : ℝ)) := by
        rw [← sum_inv_prod_erase_abs_sub_fin k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ = ε * (2 * b / δ) ^ k / (k ! : ℝ) := by
        rw [mul_div_assoc, div_pow, div_pow, mul_pow]; ring


/-- Bound on the derivative of one Lagrange basis polynomial. -/
theorem abs_eval_derivative_lagrangeBasis_le {k : ℕ} (v : Fin (k + 1) → ℝ) {δ b : ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ b)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j|)
    {x : ℝ} (hx : ∀ i, |x - v i| ≤ b) (i : Fin (k + 1)) :
    |(derivative (Lagrange.basis univ v i)).eval x| ≤
      k * b ^ (k - 1) / δ ^ k * (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
  classical
  set s := univ.erase i with hs
  set c : Fin (k + 1) → ℝ := fun j => (v i - v j)⁻¹ with hc
  have hcard : s.card = k := by
    rw [hs, Finset.card_erase_of_mem (mem_univ i)]; simp
  have hbasis : Lagrange.basis univ v i = ∏ j ∈ s, (C (c j) * (X - C (v j))) := by
    simp [Lagrange.basis, Lagrange.basisDivisor, hs, hc]
  have hc_le : ∀ j ∈ s, |c j| ≤ δ⁻¹ * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹ := by
    intro j hj
    have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hij : 0 < |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rw [abs_pos, sub_ne_zero]
      exact fun h => hne (Fin.ext (by exact_mod_cast h))
    have h1 := hsep i j
    simp only [hc, abs_inv]
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) (by linarith [h1])
  rw [hbasis, derivative_prod_finset, eval_finsetSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ m ∈ s, |((∏ j ∈ s.erase m, (C (c j) * (X - C (v j)))) *
      derivative (C (c m) * (X - C (v m)))).eval x| ≤
      b ^ (k - 1) * ∏ j ∈ s, |c j| := by
    intro m hm
    rw [eval_mul, eval_prod, abs_mul, Finset.abs_prod]
    have hd : (derivative (C (c m) * (X - C (v m)))).eval x = c m := by simp
    rw [hd]
    have hle : ∀ j ∈ s.erase m, |(C (c j) * (X - C (v j))).eval x| ≤ |c j| * b := by
      intro j _
      simp only [eval_mul, eval_C, eval_sub, eval_X, abs_mul]
      exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
    have hcard' : (s.erase m).card = k - 1 := by rw [Finset.card_erase_of_mem hm, hcard]
    calc (∏ j ∈ s.erase m, |(C (c j) * (X - C (v j))).eval x|) * |c m|
        ≤ (∏ j ∈ s.erase m, (|c j| * b)) * |c m| :=
          mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => abs_nonneg _) hle)
            (abs_nonneg _)
      _ = b ^ (k - 1) * ((∏ j ∈ s.erase m, |c j|) * |c m|) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard']; ring
      _ = b ^ (k - 1) * ∏ j ∈ s, |c j| := by rw [Finset.prod_erase_mul _ _ hm]
  have hprodc : ∏ j ∈ s, |c j| ≤ (δ ^ k)⁻¹ *
      (∏ j ∈ s, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
    calc ∏ j ∈ s, |c j| ≤ ∏ j ∈ s, (δ⁻¹ * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) hc_le
      _ = (δ ^ k)⁻¹ * (∏ j ∈ s, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, Finset.prod_inv_distrib, inv_pow]
  calc ∑ m ∈ s, |((∏ j ∈ s.erase m, (C (c j) * (X - C (v j)))) *
        derivative (C (c m) * (X - C (v m)))).eval x|
      ≤ ∑ _m ∈ s, b ^ (k - 1) * ∏ j ∈ s, |c j| := Finset.sum_le_sum hterm
    _ = k * (b ^ (k - 1) * ∏ j ∈ s, |c j|) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ k * (b ^ (k - 1) * ((δ ^ k)⁻¹ * (∏ j ∈ s, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹)) := by
        gcongr
    _ = k * b ^ (k - 1) / δ ^ k * (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
        rw [hs]; field_simp

/-- **Derivative extrapolation.**  Under the hypotheses of `abs_eval_le_of_lagrange_indexSep`,
`|P'(x)| ≤ ε k b^{k-1} (2/δ)^k / k!`. -/
theorem abs_eval_derivative_le_of_lagrange_indexSep {k : ℕ} (P : ℝ[X]) (hdeg : P.natDegree ≤ k)
    (v : Fin (k + 1) → ℝ) {ε δ b : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b)
    (hbound : ∀ i, |P.eval (v i)| ≤ ε)
    (hsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j|)
    {x : ℝ} (hx : ∀ i, |x - v i| ≤ b) :
    |(derivative P).eval x| ≤ ε * k * b ^ (k - 1) * (2 / δ) ^ k / (k ! : ℝ) := by
  classical
  have hinj := injective_of_index_sep hδ hsep
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hbound 0)
  have hcard : (univ : Finset (Fin (k + 1))).card = k + 1 := by simp
  have hdlt : P.degree < ((univ : Finset (Fin (k + 1))).card : ℕ) := by
    rw [hcard]
    rcases eq_or_ne P 0 with rfl | hP
    · simp
    · exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hP := Lagrange.eq_interpolate hinj.injOn hdlt
  have hder : (derivative P).eval x =
      ∑ i : Fin (k + 1), P.eval (v i) * (derivative (Lagrange.basis univ v i)).eval x := by
    conv_lhs => rw [hP]
    simp [Lagrange.interpolate_apply, eval_finsetSum]
  rw [hder]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin (k + 1), |P.eval (v i) * (derivative (Lagrange.basis univ v i)).eval x|
      ≤ ∑ i : Fin (k + 1), ε * (k * b ^ (k - 1) / δ ^ k *
          (∏ j ∈ univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hbound i) (abs_eval_derivative_lagrangeBasis_le v hδ hb hsep hx i)
          (abs_nonneg _) hε
    _ = ε * (k * b ^ (k - 1) / δ ^ k) * (2 ^ k / (k ! : ℝ)) := by
        rw [← sum_inv_prod_erase_abs_sub_fin k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ = ε * k * b ^ (k - 1) * (2 / δ) ^ k / (k ! : ℝ) := by
        rw [div_pow]; field_simp


/-- Sorted points of a pairwise `δ`-separated finite set are separated in proportion to their
index distance. -/
theorem orderEmbOfFin_index_sep {k : ℕ} (T : Finset ℝ) (hT : T.card = k + 1) {δ : ℝ}
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ ≤ |a - b|) (i j : Fin (k + 1)) (hij : i ≤ j) :
    (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * δ ≤ T.orderEmbOfFin hT j - T.orderEmbOfFin hT i := by
  set w := T.orderEmbOfFin hT with hw
  have hstep : ∀ n : ℕ, ∀ i j : Fin (k + 1), (j : ℕ) = (i : ℕ) + n →
      (n : ℝ) * δ ≤ w j - w i := by
    intro n
    induction n with
    | zero =>
      intro i j h
      have : i = j := Fin.ext (by omega)
      subst this; simp
    | succ n ih =>
      intro i j h
      set j' : Fin (k + 1) := ⟨(i : ℕ) + n, by omega⟩ with hj'
      have h1 := ih i j' rfl
      have hlt : j' < j := by rw [Fin.lt_def]; simp [hj']; omega
      have hwlt : w j' < w j := w.strictMono hlt
      have hmem : ∀ l, w l ∈ T := fun l => Finset.orderEmbOfFin_mem T hT l
      have h2 : δ ≤ |w j - w j'| := hsep _ (hmem j) _ (hmem j') (ne_of_gt hwlt)
      rw [abs_of_pos (by linarith)] at h2
      push_cast
      linarith
  have h := hstep ((j : ℕ) - (i : ℕ)) i j (by
    have : (i : ℕ) ≤ (j : ℕ) := hij
    omega)
  have hcast : (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) = ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) :=
    Nat.cast_sub (show (i : ℕ) ≤ (j : ℕ) from hij)
  rwa [hcast] at h

theorem pow_div_factorial_le_one {k : ℕ} :
    ((max (k : ℝ) 1) / Real.exp 1) ^ k / (k ! : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [max_eq_left hkR, div_pow, div_div, div_le_one (by positivity)]
    have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (by positivity) k
    rw [div_le_iff₀ (by positivity)] at h
    calc (k : ℝ) ^ k ≤ Real.exp k * (k ! : ℝ) := h
      _ = Real.exp 1 ^ k * (k ! : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf

/-- **Remez-type sublevel bound in a monotone chart.**  Let `P` have degree at most `k` and let
`g` expand distances on `(a, c)` by at least `λ`, with `|z - g u| ≤ b` there.  If
`ε q^k < |P(z)|`, then `{u ∈ (a,c) : |P(g u)| ≤ ε}` has measure at most `4e b/(λ q)`.
The loss is exponential in `k`, not factorial. -/
theorem volume_sublevel_comp_le {k : ℕ} (P : ℝ[X]) (hdeg : P.natDegree ≤ k)
    {g : ℝ → ℝ} {a c lam b ε q : ℝ} (hlam : 0 < lam) (hb : 0 < b) (hq : 0 < q)
    (hg : ∀ u ∈ Ioo a c, ∀ w ∈ Ioo a c, u ≤ w → lam * (w - u) ≤ g w - g u)
    {z : ℝ} (hz : ∀ u ∈ Ioo a c, |z - g u| ≤ b)
    (hε : ε * q ^ k < |P.eval z|) :
    (volume {u ∈ Ioo a c | |P.eval (g u)| ≤ ε}).toReal ≤ 4 * Real.exp 1 * b / (lam * q) := by
  classical
  set S := {u ∈ Ioo a c | |P.eval (g u)| ≤ ε} with hS
  by_contra hcon
  push Not at hcon
  set K : ℝ := max (k : ℝ) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  set δ : ℝ := 2 * Real.exp 1 * b / (lam * q * K) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hsepm : 2 * (k : ℝ) * δ < (volume S).toReal := by
    have hkK : (k : ℝ) ≤ K := le_max_left _ _
    have : 2 * (k : ℝ) * δ ≤ 4 * Real.exp 1 * b / (lam * q) := by
      rw [hδ]
      rw [show 2 * (k : ℝ) * (2 * Real.exp 1 * b / (lam * q * K)) =
        (4 * Real.exp 1 * b / (lam * q)) * ((k : ℝ) / K) by field_simp; ring]
      have hr : (k : ℝ) / K ≤ 1 := (div_le_one (by linarith)).mpr hkK
      have hpos : 0 ≤ 4 * Real.exp 1 * b / (lam * q) := by positivity
      nlinarith
    linarith
  obtain ⟨T, hTS, hTcard, hTsep⟩ :=
    GaloisForLFunctions.HTGeometry.KleinbockMargulis.exists_finset_separated hδ0 k hsepm
  set w := T.orderEmbOfFin hTcard with hw
  have hwS : ∀ i, w i ∈ S := fun i => hTS (by exact_mod_cast Finset.orderEmbOfFin_mem T hTcard i)
  set v : Fin (k + 1) → ℝ := fun i => g (w i) with hv
  have hvsep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (lam * δ) ≤
      |v i - v j| := by
    have key : ∀ i j : Fin (k + 1), i ≤ j →
        |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (lam * δ) ≤ |v i - v j| := by
      intro i j hij
      have h1 := orderEmbOfFin_index_sep T hTcard hTsep i j hij
      have hwle : w i ≤ w j := w.monotone hij
      have h2 := hg (w i) (hwS i).1 (w j) (hwS j).1 hwle
      have hij' : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (show (i:ℕ) ≤ j from hij)
      rw [abs_of_nonpos (by linarith), abs_sub_comm, abs_of_nonneg (by
        have : 0 ≤ w j - w i := by linarith
        nlinarith)]
      simp only [hv]
      nlinarith
    intro i j
    rcases le_total i j with h | h
    · exact key i j h
    · rw [abs_sub_comm, abs_sub_comm (v i)]; exact key j i h
  have hbound : ∀ i, |P.eval (v i)| ≤ ε := fun i => (hwS i).2
  have hzv : ∀ i, |z - v i| ≤ b := fun i => hz _ (hwS i).1
  have hlag := abs_eval_le_of_lagrange_indexSep P hdeg v (mul_pos hlam hδ0) hb.le hbound hvsep hzv
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hbound 0)
  have hratio : 2 * b / (lam * δ) = q * K / Real.exp 1 := by
    rw [hδ]; field_simp
  rw [hratio] at hlag
  have hfac := pow_div_factorial_le_one (k := k)
  rw [← hK] at hfac
  have : ε * (q * K / Real.exp 1) ^ k / (k ! : ℝ) ≤ ε * q ^ k := by
    rw [mul_div_assoc, show (q * K / Real.exp 1) ^ k = q ^ k * (K / Real.exp 1) ^ k by
      rw [mul_div_assoc, mul_pow]]
    rw [mul_div_assoc]
    have hq0 : 0 ≤ q ^ k := by positivity
    calc ε * (q ^ k * ((K / Real.exp 1) ^ k / (k ! : ℝ))) ≤ ε * (q ^ k * 1) := by gcongr
      _ = ε * q ^ k := by ring
  linarith


/-- Equispaced nodes on `[α, β]`. -/
theorem equispaced_nodes {k : ℕ} {α β : ℝ} (hαβ : α < β) :
    ∃ v : Fin (k + 1) → ℝ, (∀ i, v i ∈ Icc α β) ∧
      ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * ((β - α) / max (k : ℝ) 1) ≤
        |v i - v j| := by
  set K : ℝ := max (k : ℝ) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  refine ⟨fun i => α + ((i : ℕ) : ℝ) * ((β - α) / K), fun i => ⟨?_, ?_⟩, fun i j => ?_⟩
  · have : 0 ≤ ((i : ℕ) : ℝ) * ((β - α) / K) := by
      have : 0 < (β - α) / K := div_pos (by linarith) (by linarith)
      positivity
    linarith
  · have hi : ((i : ℕ) : ℝ) ≤ K := by
      have : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp i.2
      linarith [le_max_left (k : ℝ) 1]
    have : ((i : ℕ) : ℝ) * ((β - α) / K) ≤ K * ((β - α) / K) :=
      mul_le_mul_of_nonneg_right hi (div_pos (by linarith) (by linarith)).le
    rw [mul_div_cancel₀ _ (by linarith)] at this
    linarith
  · have : α + ((i : ℕ) : ℝ) * ((β - α) / K) - (α + ((j : ℕ) : ℝ) * ((β - α) / K)) =
        (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * ((β - α) / K) := by ring
    rw [this, abs_mul, abs_of_pos (div_pos (sub_pos.mpr hαβ) (by linarith : (0:ℝ) < K))]

/-- **Extrapolation beyond an interval.**  If `|P| ≤ M` on `[α, β]` and `deg P ≤ k`, then for
`y ≥ β`: `|P(y)| ≤ M (2e(y-α)/(β-α))^k`. -/
theorem abs_eval_le_extrapolate {k : ℕ} (P : ℝ[X]) (hdeg : P.natDegree ≤ k) {α β M : ℝ}
    (hαβ : α < β) (hM : ∀ t ∈ Icc α β, |P.eval t| ≤ M) {y : ℝ} (hy : β ≤ y) :
    |P.eval y| ≤ M * (2 * Real.exp 1 * (y - α) / (β - α)) ^ k := by
  obtain ⟨v, hvI, hvsep⟩ := equispaced_nodes (k := k) hαβ
  set K : ℝ := max (k : ℝ) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hδ : 0 < (β - α) / K := div_pos (by linarith) (by linarith)
  have hxv : ∀ i, |y - v i| ≤ y - α := by
    intro i
    rw [abs_of_nonneg (by linarith [(hvI i).2])]; linarith [(hvI i).1]
  have h := abs_eval_le_of_lagrange_indexSep P hdeg v hδ (by linarith) (fun i => hM _ (hvI i))
    hvsep hxv
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM α ⟨le_rfl, hαβ.le⟩)
  refine h.trans ?_
  have hr : 2 * (y - α) / ((β - α) / K) =
      (2 * Real.exp 1 * (y - α) / (β - α)) * (K / Real.exp 1) := by
    field_simp
  rw [hr, mul_pow, mul_div_assoc, mul_div_assoc]
  have hfac := pow_div_factorial_le_one (k := k)
  rw [← hK] at hfac
  have h0 : 0 ≤ (2 * Real.exp 1 * (y - α) / (β - α)) ^ k := by
    apply pow_nonneg; apply div_nonneg _ (by linarith); nlinarith [Real.exp_pos 1]
  calc M * ((2 * Real.exp 1 * (y - α) / (β - α)) ^ k * ((K / Real.exp 1) ^ k / (k ! : ℝ)))
      ≤ M * ((2 * Real.exp 1 * (y - α) / (β - α)) ^ k * 1) := by gcongr
    _ = M * (2 * Real.exp 1 * (y - α) / (β - α)) ^ k := by ring

/-- **Derivative extrapolation beyond an interval.**  Under the hypotheses of
`abs_eval_le_extrapolate`, `|P'(y)| ≤ M (k/(y-α)) (2e(y-α)/(β-α))^k`. -/
theorem abs_eval_derivative_le_extrapolate {k : ℕ} (P : ℝ[X]) (hdeg : P.natDegree ≤ k)
    {α β M : ℝ} (hαβ : α < β) (hM : ∀ t ∈ Icc α β, |P.eval t| ≤ M) {y : ℝ} (hy : β ≤ y) :
    |(derivative P).eval y| ≤
      M * (k / (y - α)) * (2 * Real.exp 1 * (y - α) / (β - α)) ^ k := by
  obtain ⟨v, hvI, hvsep⟩ := equispaced_nodes (k := k) hαβ
  set K : ℝ := max (k : ℝ) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hδ : 0 < (β - α) / K := div_pos (by linarith) (by linarith)
  have hya : 0 < y - α := by linarith
  have hxv : ∀ i, |y - v i| ≤ y - α := by
    intro i
    rw [abs_of_nonneg (by linarith [(hvI i).2])]; linarith [(hvI i).1]
  have h := abs_eval_derivative_le_of_lagrange_indexSep P hdeg v hδ hya.le
    (fun i => hM _ (hvI i)) hvsep hxv
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM α ⟨le_rfl, hαβ.le⟩)
  refine h.trans ?_
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0; simp
  have hpow : (y - α) ^ (k - 1) = (y - α) ^ k / (y - α) := by
    rw [eq_div_iff hya.ne', ← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow]
  have hr : (2 / ((β - α) / K)) ^ k * (y - α) ^ k =
      (2 * Real.exp 1 * (y - α) / (β - α)) ^ k * (K / Real.exp 1) ^ k := by
    rw [← mul_pow, ← mul_pow]; congr 1; field_simp
  have hfac := pow_div_factorial_le_one (k := k)
  rw [← hK] at hfac
  have h0 : 0 ≤ (2 * Real.exp 1 * (y - α) / (β - α)) ^ k := by
    apply pow_nonneg; apply div_nonneg _ (by linarith); nlinarith [Real.exp_pos 1]
  calc M * k * ((y - α) ^ k / (y - α)) * (2 / ((β - α) / K)) ^ k / (k ! : ℝ)
      = M * (k / (y - α)) * ((2 / ((β - α) / K)) ^ k * (y - α) ^ k / (k ! : ℝ)) := by
        field_simp
    _ = M * (k / (y - α)) * ((2 * Real.exp 1 * (y - α) / (β - α)) ^ k *
          ((K / Real.exp 1) ^ k / (k ! : ℝ))) := by rw [hr]; ring
    _ ≤ M * (k / (y - α)) * ((2 * Real.exp 1 * (y - α) / (β - α)) ^ k * 1) := by gcongr
    _ = M * (k / (y - α)) * (2 * Real.exp 1 * (y - α) / (β - α)) ^ k := by ring

end GaloisForLFunctions.HTGeometry
