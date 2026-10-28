import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheEulerProductOfLorentzianLocalFactorsIsLorentzian

/-!
# The support of a mixed-Lorentzian polynomial is M-convex

A mixed-Lorentzian polynomial (`IsMixedLorentzian`) is defined by signature alone: nonnegative
coefficients, homogeneity, and one positive square for every mixed quadratic derivative along
nonnegative directions. Its support is M-convex. Hence the mixed class equals the class of
Lorentzian polynomials in coefficient form, and the coefficient class inherits the closure
operations of the mixed class.

* **Exchange in a Lorentzian form** (`IsHyperbolic.exchange`): for `Q ≥ 0` with one positive
  square, `Q_{ai} > 0` and `Q_{jk} > 0` force `Q_{aj} > 0` or `Q_{ak} > 0`. Otherwise
  `e_a + t e_i` and `e_j + e_k` span a positive definite plane for small `t > 0`. For a quadratic
  this is the exchange property of its support (`IsMixedLorentzian.quadratic_exchange`).
* **A common variable** (`exchange_of_common`): if `x^α` and `x^β` share a variable `x_k`, the
  exchange passes to `∂_k p`, which has lower degree.
* **Coprime monomials** (`exchange_disjoint`): write `x^α = x^μ x_a x_i` and `x^β = x^ν x_k`, and
  differentiate along `e_a + e_k`. The exchange in `∂_{e_a+e_k} p` either lands on `α − e_i + e_j`,
  or produces the monomial `α' = μ + e_j + e_k`, which shares `x^μ` with `x^α`. The exchange of
  `α` with `α'` at `i` then lands on `α − e_i + e_j` or `α − e_i + e_k`.
* **The support is M-convex** (`IsMixedLorentzian.isMConvex`), by induction on the degree. The
  quadratic derivatives `∂^α p` are mixed derivatives along coordinate directions
  (`exists_unitList`), so **the two classes coincide**
  (`isMixedLorentzian_iff_isLorentzianPolynomial`).
* **Closure in coefficient form**: products (`IsLorentzianPolynomial.mul`), nonnegative
  substitutions (`IsLorentzianPolynomial.subst`) and directional derivatives
  (`IsLorentzianPolynomial.differentiate`) of Lorentzian polynomials are Lorentzian, and so is the
  Euler product of Lorentzian local factors composed with the scale map
  (`isLorentzianPolynomial_prod_subst`). In particular the support of a product of Lorentzian
  polynomials is M-convex (`isMConvex_support_mul`).
-/

noncomputable section

open Matrix Finset MvPolynomial

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Exchange in a Lorentzian form -/

/-- **Exchange in a Lorentzian form.** If `Q ≥ 0` is hyperbolic with `Q_{ai} > 0` and `Q_{jk} > 0`,
then `Q_{aj} > 0` or `Q_{ak} > 0`: otherwise `x = e_a + t e_i`, `y = e_j + e_k` have
`Q[x] Q[y] ≥ 4t Q_{ai} Q_{jk} > t² (Q_{ij} + Q_{ik})² = (xᵀQy)²` for small `t > 0`. -/
theorem IsHyperbolic.exchange {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hnn : ∀ r s, 0 ≤ Q r s)
    (hh : IsHyperbolic Q) {a i j k : ι} (hai : 0 < Q a i) (hjk : 0 < Q j k) :
    0 < Q a j ∨ 0 < Q a k := by
  by_contra hcon
  push Not at hcon
  have haj : Q a j = 0 := le_antisymm hcon.1 (hnn a j)
  have hak : Q a k = 0 := le_antisymm hcon.2 (hnn a k)
  have hS : 0 ≤ Q i j + Q i k := add_nonneg (hnn i j) (hnn i k)
  -- a small `t > 0` with `t S² < 4 Q_{ai} Q_{jk}`
  obtain ⟨t, ht, htS⟩ : ∃ t : ℝ, 0 < t ∧ t * (Q i j + Q i k) ^ 2 < 4 * (Q a i * Q j k) := by
    have hP : 0 < Q a i * Q j k := mul_pos hai hjk
    refine ⟨Q a i * Q j k / ((Q i j + Q i k) ^ 2 + 1), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Q i j + Q i k)]
  have hqx : qf Q (Pi.single a 1 + t • Pi.single i 1) = Q a a + 2 * t * Q a i + t ^ 2 * Q i i := by
    have h := qf_add_smul hQ 1 t (Pi.single a 1) (Pi.single i 1)
    simp only [one_smul] at h
    rw [h]
    simp only [qf, bil_single_single]
    ring
  have hqy : qf Q (Pi.single j 1 + Pi.single k 1) = Q j j + 2 * Q j k + Q k k := by
    have h := qf_add_smul hQ 1 1 (Pi.single j 1) (Pi.single k 1)
    simp only [one_smul] at h
    rw [h]
    simp only [qf, bil_single_single]
    ring
  have hb : bil Q (Pi.single a 1 + t • Pi.single i 1) (Pi.single j 1 + Pi.single k 1) =
      t * (Q i j + Q i k) := by
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_single_single, haj, hak]
    ring
  have hx : 0 < qf Q (Pi.single a 1 + t • Pi.single i 1) := by
    rw [hqx]
    nlinarith [hnn a a, mul_nonneg (sq_nonneg t) (hnn i i), mul_pos ht hai]
  have h := hh _ (Pi.single j 1 + Pi.single k 1) hx
  rw [hqx, hqy, hb] at h
  have h1 : 2 * t * Q a i ≤ Q a a + 2 * t * Q a i + t ^ 2 * Q i i := by
    nlinarith [hnn a a, mul_nonneg (sq_nonneg t) (hnn i i)]
  have h2 : 2 * Q j k ≤ Q j j + 2 * Q j k + Q k k := by nlinarith [hnn j j, hnn k k]
  have h3 := mul_le_mul h1 h2 (by positivity) (by linarith [mul_pos ht hai])
  have key : 4 * t * (Q a i * Q j k) ≤ t * (t * (Q i j + Q i k) ^ 2) := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left htS ht]

/-! ### Quadratics -/

theorem hess0_isSymm (q : MvPolynomial ι ℝ) : (hess0 q).IsSymm :=
  Matrix.IsSymm.ext fun j k => by rw [hess0_apply_eq, hess0_apply_eq, add_right_comm]

theorem hess0_nonneg {q : MvPolynomial ι ℝ} (hq : ∀ β, 0 ≤ coeff β q) (j k : ι) :
    0 ≤ hess0 q j k := by
  rw [hess0_apply_eq]; exact mul_nonneg (mfact_pos _).le (hq _)

/-- An entry of the Hessian of a quadratic with nonnegative coefficients is positive iff the
monomial `x_j x_k` occurs. -/
theorem hess0_pos_iff {q : MvPolynomial ι ℝ} (hq : ∀ β, 0 ≤ coeff β q) (j k : ι) :
    0 < hess0 q j k ↔ coeff (Finsupp.single j 1 + Finsupp.single k 1) q ≠ 0 := by
  rw [hess0_apply_eq, zero_add]
  have hm := mfact_pos (Finsupp.single j 1 + Finsupp.single k 1)
  exact ⟨fun h h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h,
    fun h => mul_pos hm (lt_of_le_of_ne (hq _) (Ne.symm h))⟩

/-- **Quadratic exchange.** If a mixed-Lorentzian quadratic contains `x_a x_i` and `x_j x_k`, it
contains `x_a x_j` or `x_a x_k`. -/
theorem IsMixedLorentzian.quadratic_exchange {p : MvPolynomial ι ℝ} (hp : IsMixedLorentzian 2 p)
    {a i j k : ι} (hai : coeff (Finsupp.single a 1 + Finsupp.single i 1) p ≠ 0)
    (hjk : coeff (Finsupp.single j 1 + Finsupp.single k 1) p ≠ 0) :
    coeff (Finsupp.single a 1 + Finsupp.single j 1) p ≠ 0 ∨
      coeff (Finsupp.single a 1 + Finsupp.single k 1) p ≠ 0 := by
  have hh : IsHyperbolic (hess0 p) := hp.2.2 [] rfl (by simp)
  have h := hh.exchange (hess0_isSymm p) (hess0_nonneg hp.1) ((hess0_pos_iff hp.1 a i).mpr hai)
    ((hess0_pos_iff hp.1 j k).mpr hjk)
  rwa [hess0_pos_iff hp.1, hess0_pos_iff hp.1] at h

/-! ### Coefficients of derivatives -/

theorem coeff_dirDeriv_single (p : MvPolynomial ι ℝ) (k : ι) (γ : ι →₀ ℕ) :
    coeff γ (dirDeriv (Pi.single k 1) p) =
      coeff (γ + Finsupp.single k 1) p * ((γ k : ℝ) + 1) := by
  rw [coeff_dirDeriv, Finset.sum_eq_single k
    (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul]) (fun h => absurd (mem_univ k) h),
    Pi.single_eq_same, one_mul, coeff_pderiv]

theorem coeff_dirDeriv_single_ne_zero_iff (p : MvPolynomial ι ℝ) (k : ι) (γ : ι →₀ ℕ) :
    coeff γ (dirDeriv (Pi.single k 1) p) ≠ 0 ↔ coeff (γ + Finsupp.single k 1) p ≠ 0 := by
  rw [coeff_dirDeriv_single]
  have : ((γ k : ℝ) + 1) ≠ 0 := by positivity
  exact ⟨fun h h0 => h (by rw [h0, zero_mul]), fun h => mul_ne_zero h this⟩

theorem coeff_dirDeriv_single_nonneg {p : MvPolynomial ι ℝ} (hp : ∀ β, 0 ≤ coeff β p) (k : ι)
    (γ : ι →₀ ℕ) : 0 ≤ coeff γ (dirDeriv (Pi.single k 1) p) := by
  rw [coeff_dirDeriv_single]; exact mul_nonneg (hp _) (by positivity)

omit [DecidableEq ι] in
theorem coeff_dirDeriv_add (u v : ι → ℝ) (p : MvPolynomial ι ℝ) (γ : ι →₀ ℕ) :
    coeff γ (dirDeriv (u + v) p) = coeff γ (dirDeriv u p) + coeff γ (dirDeriv v p) := by
  simp only [coeff_dirDeriv, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- For nonnegative coefficients, `x^γ` occurs in `∂_{e_a + e_k} p` iff `x^{γ+e_a}` or `x^{γ+e_k}`
occurs in `p`. -/
theorem coeff_dirDeriv_pair_ne_zero_iff {p : MvPolynomial ι ℝ} (hp : ∀ β, 0 ≤ coeff β p)
    (a k : ι) (γ : ι →₀ ℕ) :
    coeff γ (dirDeriv (Pi.single a 1 + Pi.single k 1) p) ≠ 0 ↔
      coeff (γ + Finsupp.single a 1) p ≠ 0 ∨ coeff (γ + Finsupp.single k 1) p ≠ 0 := by
  rw [coeff_dirDeriv_add, ← coeff_dirDeriv_single_ne_zero_iff,
    ← coeff_dirDeriv_single_ne_zero_iff, Ne,
    add_eq_zero_iff_of_nonneg (coeff_dirDeriv_single_nonneg hp a γ)
      (coeff_dirDeriv_single_nonneg hp k γ), not_and_or]

omit [Fintype ι] in
theorem single_nonneg (k : ι) (r : ι) : (0 : ℝ) ≤ (Pi.single k 1 : ι → ℝ) r := by
  rw [Pi.single_apply]; split_ifs <;> norm_num

/-! ### Degrees -/

omit [Fintype ι] [DecidableEq ι] in
theorem degree_of_coeff_ne_zero {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d)
    {β : ι →₀ ℕ} (h : coeff β p ≠ 0) : Finsupp.degree β = d := by
  rw [Finsupp.degree_eq_weight_one]; exact hp h

omit [DecidableEq ι] in
theorem exists_one_le_of_degree_pos {β : ι →₀ ℕ} (h : 0 < Finsupp.degree β) : ∃ k, 1 ≤ β k := by
  rw [Finsupp.degree_eq_sum] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  exact ⟨k, Nat.one_le_iff_ne_zero.mpr hk⟩

theorem exists_other_of_degree {α : ι →₀ ℕ} {i : ι} (hi : α i ≤ 1)
    (h : 2 ≤ Finsupp.degree α) : ∃ a, a ≠ i ∧ 1 ≤ α a := by
  rw [Finsupp.degree_eq_sum, ← Finset.add_sum_erase _ _ (mem_univ i)] at h
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (s := univ.erase i) (f := fun l => α l) (by omega)
  exact ⟨a, Finset.ne_of_mem_erase ha, Nat.one_le_iff_ne_zero.mpr hne⟩

omit [DecidableEq ι] in
theorem eq_of_le_of_degree_le {α γ : ι →₀ ℕ} (hle : γ ≤ α)
    (hd : Finsupp.degree α ≤ Finsupp.degree γ) : α = γ := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum] at hd
  have hle' : ∀ l ∈ univ, γ l ≤ α l := fun l _ => Finsupp.le_def.mp hle l
  have hsum : ∑ l, γ l = ∑ l, α l := le_antisymm (Finset.sum_le_sum hle') hd
  exact Finsupp.ext fun l => ((Finset.sum_eq_sum_iff_of_le hle').mp hsum l (mem_univ l)).symm

omit [Fintype ι] [DecidableEq ι] in
/-- A monomial containing `x_k` is `x^ν x_k`. -/
theorem exists_eq_add_single {β : ι →₀ ℕ} {k : ι} (h : 1 ≤ β k) :
    ∃ ν, β = ν + Finsupp.single k 1 := by
  obtain ⟨ν, hν⟩ := exists_add_of_le (Finsupp.single_le_iff.mpr h)
  exact ⟨ν, by rw [hν, add_comm]⟩

/-! ### The exchange -/

/-- **A common variable.** If `x^α, x^β` occur in `p`, share the variable `x_k`, and `∂_k p` has
M-convex support, then the exchange for `(α, β)` holds in `p`. -/
theorem exchange_of_common {p : MvPolynomial ι ℝ} {k : ι}
    (hk : IsMConvex {γ | coeff γ (dirDeriv (Pi.single k 1) p) ≠ 0})
    {α β : ι →₀ ℕ} (hα : coeff α p ≠ 0) (hβ : coeff β p ≠ 0) (hαk : 1 ≤ α k) (hβk : 1 ≤ β k)
    {i : ι} (hi : β i < α i) :
    ∃ j, α j < β j ∧ coeff (α - Finsupp.single i 1 + Finsupp.single j 1) p ≠ 0 := by
  have hmem : ∀ {γ : ι →₀ ℕ}, 1 ≤ γ k → coeff γ p ≠ 0 →
      γ - Finsupp.single k 1 ∈ {γ | coeff γ (dirDeriv (Pi.single k 1) p) ≠ 0} :=
    fun hγk hγ => by
      show coeff _ _ ≠ 0
      rwa [coeff_dirDeriv_single_ne_zero_iff, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hγk)]
  obtain ⟨j, hj, hJ⟩ := hk _ (hmem hαk hα) _ (hmem hβk hβ) i (by
    simp only [Finsupp.tsub_apply, single_apply_eq]
    split_ifs <;> subst_vars <;> omega)
  refine ⟨j, by
    simp only [Finsupp.tsub_apply, single_apply_eq] at hj
    split_ifs at hj <;> subst_vars <;> omega, ?_⟩
  have h := (coeff_dirDeriv_single_ne_zero_iff p k _).mp hJ
  have heq : α - Finsupp.single k 1 - Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 =
      α - Finsupp.single i 1 + Finsupp.single j 1 := by
    ext l
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, single_apply_eq]
    split_ifs <;> subst_vars <;> omega
  rwa [heq] at h

/-- **Coprime monomials, degree `≥ 3`.** Let `x^α = x^μ x_a x_i` and `x^β = x^ν x_k` occur in `p`,
coprime, with `μ ≠ 0`. If `∂_{e_a+e_k} p` and every `∂_l p` have M-convex support, then some
`x_j ∣ x^β` has `x^μ x_a x_j` in `p`. -/
theorem exchange_disjoint {p : MvPolynomial ι ℝ} (hp : ∀ β, 0 ≤ coeff β p)
    {μ ν : ι →₀ ℕ} {a i k : ι}
    (hpair : IsMConvex {γ | coeff γ (dirDeriv (Pi.single a 1 + Pi.single k 1) p) ≠ 0})
    (hpart : ∀ l, IsMConvex {γ | coeff γ (dirDeriv (Pi.single l 1) p) ≠ 0}) (hμ : μ ≠ 0)
    (hα : coeff (μ + Finsupp.single a 1 + Finsupp.single i 1) p ≠ 0)
    (hβ : coeff (ν + Finsupp.single k 1) p ≠ 0)
    (hdisj : ∀ l, 1 ≤ (μ + Finsupp.single a 1 + Finsupp.single i 1 : ι →₀ ℕ) l →
      (ν + Finsupp.single k 1 : ι →₀ ℕ) l = 0) :
    ∃ j, 1 ≤ (ν + Finsupp.single k 1 : ι →₀ ℕ) j ∧
      coeff (μ + Finsupp.single a 1 + Finsupp.single j 1) p ≠ 0 := by
  have hβi : (ν + Finsupp.single k 1 : ι →₀ ℕ) i = 0 :=
    hdisj i (by simp [single_apply_eq])
  have hνi : ν i = 0 := by
    simp only [Finsupp.add_apply, single_apply_eq] at hβi; omega
  -- the two monomials in `∂_{e_a+e_k} p`
  have hA : coeff (μ + Finsupp.single i 1) (dirDeriv (Pi.single a 1 + Pi.single k 1) p) ≠ 0 := by
    rw [coeff_dirDeriv_pair_ne_zero_iff hp]
    left; rwa [add_right_comm]
  have hB : coeff ν (dirDeriv (Pi.single a 1 + Pi.single k 1) p) ≠ 0 := by
    rw [coeff_dirDeriv_pair_ne_zero_iff hp]; right; exact hβ
  obtain ⟨j, hj, hJ⟩ := hpair _ hA _ hB i (by simp [hνi])
  rw [add_tsub_cancel_right] at hJ
  have hβj : 1 ≤ (ν + Finsupp.single k 1 : ι →₀ ℕ) j := by
    simp only [Finsupp.add_apply, single_apply_eq] at hj ⊢
    split_ifs at hj ⊢ <;> omega
  rcases (coeff_dirDeriv_pair_ne_zero_iff hp a k _).mp hJ with h | h
  · exact ⟨j, hβj, by rwa [add_right_comm] at h⟩
  -- `x^{α'} = x^μ x_j x_k` shares `x^μ` with `x^α`
  obtain ⟨l, hl⟩ := exists_one_le_of_degree_pos (β := μ)
    (Nat.pos_of_ne_zero fun h0 => hμ ((Finsupp.degree_eq_zero_iff μ).mp h0))
  have hβk : 1 ≤ (ν + Finsupp.single k 1 : ι →₀ ℕ) k := by simp
  have hji : j ≠ i := fun h' => by subst h'; omega
  have hki : k ≠ i := fun h' => by subst h'; omega
  obtain ⟨j', hj', hJ'⟩ := exchange_of_common (hpart l) hα h
    (by simp only [Finsupp.add_apply]; omega) (by simp only [Finsupp.add_apply]; omega)
    (i := i) (by
      simp only [Finsupp.add_apply, single_apply_eq, if_neg hji, if_neg hki]
      split_ifs <;> omega)
  have hj'jk : j' = j ∨ j' = k := by
    by_contra hc
    push Not at hc
    have e1 : (Finsupp.single j 1 : ι →₀ ℕ) j' = 0 := by rw [single_apply_eq, if_neg (Ne.symm hc.1)]
    have e2 : (Finsupp.single k 1 : ι →₀ ℕ) j' = 0 := by rw [single_apply_eq, if_neg (Ne.symm hc.2)]
    simp only [Finsupp.add_apply, e1, e2] at hj'
    omega
  rw [add_tsub_cancel_right] at hJ'
  rcases hj'jk with rfl | rfl
  · exact ⟨j', hβj, hJ'⟩
  · exact ⟨j', hβk, hJ'⟩

/-- **The support of a mixed-Lorentzian polynomial is M-convex.** -/
theorem IsMixedLorentzian.isMConvex {d : ℕ} {p : MvPolynomial ι ℝ} (hp : IsMixedLorentzian d p) :
    IsMConvex {β | coeff β p ≠ 0} := by
  induction d generalizing p with
  | zero =>
    intro α hα β hβ i hi
    rw [(Finsupp.degree_eq_zero_iff α).mp (degree_of_coeff_ne_zero hp.2.1 hα)] at hi
    simp at hi
  | succ d IH =>
    have hpart : ∀ l, IsMConvex {γ | coeff γ (dirDeriv (Pi.single l 1) p) ≠ 0} := fun l =>
      IH (hp.differentiate (single_nonneg l))
    intro α hα β hβ i hi
    have hα' : coeff α p ≠ 0 := hα
    have hβ' : coeff β p ≠ 0 := hβ
    have hdα := degree_of_coeff_ne_zero hp.2.1 hα'
    have hdβ := degree_of_coeff_ne_zero hp.2.1 hβ'
    by_cases hcommon : ∃ k, 1 ≤ α k ∧ 1 ≤ β k
    · obtain ⟨k, hαk, hβk⟩ := hcommon
      exact exchange_of_common (hpart k) hα' hβ' hαk hβk hi
    push Not at hcommon
    -- coprime monomials: write `x^β = x^ν x_k`
    obtain ⟨k, hβk⟩ := exists_one_le_of_degree_pos (β := β) (by omega)
    obtain ⟨ν, rfl⟩ := exists_eq_add_single hβk
    have hdν : Finsupp.degree ν = d := by rw [degree_add_single] at hdβ; omega
    have hcop : ∀ l, 1 ≤ (ν + Finsupp.single k 1 : ι →₀ ℕ) l → α l = 0 := fun l hl => by
      by_contra h0
      have := hcommon l (Nat.one_le_iff_ne_zero.mpr h0)
      omega
    rcases d with _ | _ | d
    · -- degree one: `x^α = x_i`, `x^β = x_k`
      have hαe : α = Finsupp.single i 1 :=
        eq_of_le_of_degree_le (Finsupp.single_le_iff.mpr (by omega))
          (by rw [hdα, Finsupp.degree_single])
      have hν0 : ν = 0 := (Finsupp.degree_eq_zero_iff ν).mp hdν
      subst hαe hν0
      refine ⟨k, by rw [hcop k hβk]; omega, ?_⟩
      show coeff _ p ≠ 0
      rwa [tsub_self, zero_add, ← zero_add (Finsupp.single k 1)]
    all_goals
      -- write `x^α = x^μ x_a x_i`
      obtain ⟨a, ha⟩ : ∃ a, Finsupp.single a 1 + Finsupp.single i 1 ≤ α := by
        by_cases h2 : 2 ≤ α i
        · refine ⟨i, Finsupp.le_def.mpr fun l => ?_⟩
          simp only [Finsupp.add_apply, single_apply_eq]
          split_ifs <;> subst_vars <;> omega
        · obtain ⟨a, hai, ha⟩ := exists_other_of_degree (α := α) (i := i) (by omega) (by omega)
          refine ⟨a, Finsupp.le_def.mpr fun l => ?_⟩
          simp only [Finsupp.add_apply, single_apply_eq]
          split_ifs <;> subst_vars <;> first | omega | exact absurd rfl hai
      obtain ⟨μ, hμ⟩ := exists_add_of_le ha
      replace hμ : α = μ + Finsupp.single a 1 + Finsupp.single i 1 := by rw [hμ]; abel
      subst hμ
      have hdμ := hdα
      rw [degree_add_single, degree_add_single] at hdμ
      suffices h : ∃ j, 1 ≤ (ν + Finsupp.single k 1 : ι →₀ ℕ) j ∧
          coeff (μ + Finsupp.single a 1 + Finsupp.single j 1) p ≠ 0 by
        obtain ⟨j, hj, hJ⟩ := h
        refine ⟨j, by rw [hcop j hj]; omega, ?_⟩
        show coeff _ p ≠ 0
        rwa [add_tsub_cancel_right]
    · -- degree two: a quadratic exchange
      have hμ0 : μ = 0 := (Finsupp.degree_eq_zero_iff μ).mp (by omega)
      subst hμ0
      obtain ⟨k', hk'⟩ := exists_one_le_of_degree_pos (β := ν) (by omega)
      have hνe : ν = Finsupp.single k' 1 :=
        eq_of_le_of_degree_le (Finsupp.single_le_iff.mpr hk')
          (by rw [hdν, Finsupp.degree_single])
      subst hνe
      rw [zero_add] at hα' ⊢
      rcases hp.quadratic_exchange hα' hβ' with h | h
      · exact ⟨k', by simp [single_apply_eq], h⟩
      · exact ⟨k, by simp [single_apply_eq], h⟩
    · -- degree at least three
      refine exchange_disjoint hp.1 (IH (hp.differentiate fun r => add_nonneg
        (single_nonneg a r) (single_nonneg k r))) hpart
        (fun h0 => by rw [h0, map_zero] at hdμ; omega) hα' hβ' fun l hl => ?_
      have := hcommon l hl
      omega

/-! ### The two classes coincide -/

/-- Every multi-index is reached by coordinate directions: there are unit vectors `vs` with
`|vs| = |α|` and `dval c vs γ = dval c [] (γ + α)`, i.e. `∂_{vs} = ∂^α`. -/
theorem exists_unitList : ∀ (n : ℕ) (α : ι →₀ ℕ), Finsupp.degree α = n →
    ∃ vs : List (ι → ℝ), vs.length = n ∧ (∀ v ∈ vs, ∀ i, 0 ≤ v i) ∧
      ∀ (c : (ι →₀ ℕ) → ℝ) (γ : ι →₀ ℕ), dval c vs γ = dval c [] (γ + α)
  | 0, α, h => ⟨[], rfl, by simp, fun c γ => by rw [(Finsupp.degree_eq_zero_iff α).mp h, add_zero]⟩
  | n + 1, α, h => by
    obtain ⟨l, hl⟩ := exists_one_le_of_degree_pos (β := α) (by omega)
    obtain ⟨α', rfl⟩ := exists_eq_add_single hl
    obtain ⟨vs, hlen, hnn, hval⟩ := exists_unitList n α' (by rw [degree_add_single] at h; omega)
    refine ⟨Pi.single l 1 :: vs, by simp [hlen], fun v hv i => ?_, fun c γ => ?_⟩
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact single_nonneg l i
      · exact hnn v hv i
    · show (∑ i, (Pi.single l 1 : ι → ℝ) i * dval c vs (γ + Finsupp.single i 1)) = _
      rw [Finset.sum_eq_single l
        (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul]) (fun h => absurd (mem_univ l) h),
        Pi.single_eq_same, one_mul, hval, add_assoc, add_comm (Finsupp.single l 1)]

/-- The quadratic derivatives `∂^α p` of a mixed-Lorentzian polynomial are hyperbolic. -/
theorem IsMixedLorentzian.isHyperbolic_quadDeriv {d : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsMixedLorentzian d p) {α : ι →₀ ℕ} (hα : Finsupp.degree α + 2 = d) :
    IsHyperbolic (quadDeriv (fun β => coeff β p) α) := by
  obtain ⟨vs, hlen, hnn, hval⟩ := exists_unitList _ α rfl
  have h := hp.2.2 vs (by omega) hnn
  rw [hess0_dirDerivs] at h
  have e : mixHess (fun β => coeff β p) vs 0 = quadDeriv (fun β => coeff β p) α := by
    ext j k
    have hjk : (0 : ι →₀ ℕ) + Finsupp.single j 1 + Finsupp.single k 1 + α =
        α + Finsupp.single j 1 + Finsupp.single k 1 := by abel
    simp only [mixHess, quadDeriv, Matrix.of_apply, hval, dval, hjk]
  rwa [e] at h

/-- **Mixed-Lorentzian polynomials are Lorentzian in coefficient form.** -/
theorem IsMixedLorentzian.isLorentzianPolynomial {d : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsMixedLorentzian d p) : IsLorentzianPolynomial d p :=
  ⟨hp.1, fun _ hβ => degree_of_coeff_ne_zero hp.2.1 hβ, hp.isMConvex,
    fun _ hα => hp.isHyperbolic_quadDeriv hα⟩

/-- **The two Lorentzian classes coincide**: the signature conditions along all nonnegative
directions force the M-convex support. -/
theorem isMixedLorentzian_iff_isLorentzianPolynomial {d : ℕ} {p : MvPolynomial ι ℝ} :
    IsMixedLorentzian d p ↔ IsLorentzianPolynomial d p :=
  ⟨IsMixedLorentzian.isLorentzianPolynomial, IsLorentzianPolynomial.isMixedLorentzian⟩

/-! ### Closure in coefficient form -/

/-- **Products of Lorentzian polynomials are Lorentzian.** -/
theorem IsLorentzianPolynomial.mul {d e : ℕ} {f g : MvPolynomial ι ℝ}
    (hf : IsLorentzianPolynomial d f) (hg : IsLorentzianPolynomial e g) :
    IsLorentzianPolynomial (d + e) (f * g) :=
  (isMixedLorentzian_mul hf hg).isLorentzianPolynomial

/-- The support of a product of Lorentzian polynomials is M-convex. -/
theorem isMConvex_support_mul {d e : ℕ} {f g : MvPolynomial ι ℝ}
    (hf : IsLorentzianPolynomial d f) (hg : IsLorentzianPolynomial e g) :
    IsMConvex {β | coeff β (f * g) ≠ 0} :=
  (hf.mul hg).2.2.1

/-- Directional derivatives of a Lorentzian polynomial along nonnegative directions are
Lorentzian. -/
theorem IsLorentzianPolynomial.differentiate {d : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsLorentzianPolynomial (d + 1) p) {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    IsLorentzianPolynomial d (dirDeriv v p) :=
  (hp.isMixedLorentzian.differentiate hv).isLorentzianPolynomial

/-- **Nonnegative substitutions preserve the Lorentzian class.** -/
theorem IsLorentzianPolynomial.subst {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}
    {p : MvPolynomial ι ℝ} (hp : IsLorentzianPolynomial d p) {A : Matrix ι κ ℝ}
    (hA : ∀ i k, 0 ≤ A i k) : IsLorentzianPolynomial d (aeval (linSub A) p) :=
  (hp.isMixedLorentzian.subst hA).isLorentzianPolynomial

/-- **The Euler product closure in coefficient form**: the product of Lorentzian local factors,
composed with any nonnegative substitution, is Lorentzian. -/
theorem isLorentzianPolynomial_prod_subst {κ τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype τ]
    [DecidableEq τ] {d : κ → ℕ} {f : κ → MvPolynomial ι ℝ} (s : Finset κ)
    (hf : ∀ p ∈ s, IsLorentzianPolynomial (d p) (f p)) {A : Matrix ι τ ℝ}
    (hA : ∀ i k, 0 ≤ A i k) :
    IsLorentzianPolynomial (∑ p ∈ s, d p) (aeval (linSub A) (∏ p ∈ s, f p)) :=
  (isMixedLorentzian_prod_subst s hf hA).isLorentzianPolynomial

end GaloisForLFunctions.ArithmeticLorentzianGeometry
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms IsMixedLorentzian.isMConvex
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms isMixedLorentzian_iff_isLorentzianPolynomial
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms IsLorentzianPolynomial.mul
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms IsLorentzianPolynomial.subst
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms isLorentzianPolynomial_prod_subst
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms isMConvex_support_mul
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms IsLorentzianPolynomial.differentiate
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms IsHyperbolic.exchange
