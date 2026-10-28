import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianPolynomialsAndTheTuranLayer
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerDichotomy

/-!
# The Hessian of a Lorentzian polynomial trickles down

A Lorentzian polynomial `f = Σ_β c_β x^β` of degree `d = m + 2` (`IsLorentzianPoly`) is defined by
conditions on its coefficients: nonnegative, M-convex support, hyperbolic quadratic derivatives
`∂^α f`, `|α| = m`. Its Hessian at a point `x` is the weighted sum of these quadratic derivatives,

    ∇²f(x) = Σ_{|α| = m} (x^α/α!) Q_α,      Q_α = Hessian of ∂^α f       (`hess`).

* **Differentiation** (`isLorentzianPoly_coeffDeriv`): `∂_i f` is Lorentzian of degree `d − 1`; its
  quadratic derivatives are those of `f` (`quadDeriv_coeffDeriv`) and its support is a slice of an
  M-convex set.
* **Euler's identity is the link condition** (`hess_succ_smul`, `sum_hess_coeffDeriv_mul`):
  `m ∇²f(x) = Σ_i x_i ∇²(∂_i f)(x)` and `∇²(∂_i f)(x) x = m ∇²f(x) e_i`. So the Hessians of the
  partial derivatives are links of the Hessian, weighted by `x`.
* **The Hessian trickles down** (`isHyperbolic_hess`): for `x > 0` the Hessian `∇²f(x)` has one
  positive square. Reverse Cauchy–Schwarz in each link gives the weighted trickle-down
  inequality `(TD_x)`; the Hessian is entrywise nonnegative, and M-convexity of the support makes
  it connected on the variables that occur (`mconvex_path`); the weighted Metzler
  Hodge index theorem concludes. By continuity the same holds at every `x ≥ 0`
  (`isHyperbolic_hess_of_nonneg`).

This is the trickle-down theorem of the programme proving the basic analytic property of
Lorentzian polynomials (Brändén–Huh): local signature of the derivatives, glued by Euler's identity,
gives global signature of the Hessian at every positive point.
-/

noncomputable section

open Matrix Finset
open scoped Nat

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Multi-indices, monomials and factorials -/

/-- The multi-indices of degree `m`. -/
def degSet (m : ℕ) : Finset (ι →₀ ℕ) := (Finset.univ : Finset ι).finsuppAntidiag m

theorem mem_degSet {m : ℕ} {α : ι →₀ ℕ} : α ∈ degSet m ↔ Finsupp.degree α = m := by
  simp [degSet, Finsupp.degree_eq_sum]

/-- The monomial `x^α`. -/
def mono (x : ι → ℝ) (α : ι →₀ ℕ) : ℝ := ∏ i, x i ^ α i

omit [DecidableEq ι] in
theorem mfact_eq_prod (α : ι →₀ ℕ) : mfact α = ∏ i, ((α i)! : ℝ) := by
  rw [mfact, Finsupp.prod_fintype _ _ (fun _ => by simp)]

theorem mfact_pos (α : ι →₀ ℕ) : 0 < mfact α := by
  rw [mfact_eq_prod]; exact prod_pos fun i _ => by positivity

omit [Fintype ι] in
theorem single_apply_eq (i l : ι) : (Finsupp.single i 1 : ι →₀ ℕ) l = if i = l then 1 else 0 :=
  Finsupp.single_apply

theorem mfact_add_single (α : ι →₀ ℕ) (i : ι) :
    mfact (α + Finsupp.single i 1) = ((α i : ℝ) + 1) * mfact α := by
  rw [mfact_eq_prod, mfact_eq_prod, ← Finset.mul_prod_erase univ _ (mem_univ i),
    ← Finset.mul_prod_erase univ (fun l => ((α l)! : ℝ)) (mem_univ i)]
  have h1 : ∀ l ∈ univ.erase i, (((α + Finsupp.single i 1 : ι →₀ ℕ) l)! : ℝ) = ((α l)! : ℝ) :=
    fun l hl => by
      rw [Finsupp.add_apply, single_apply_eq, if_neg (Ne.symm (ne_of_mem_erase hl)), add_zero]
  rw [prod_congr rfl h1, Finsupp.add_apply, single_apply_eq, if_pos rfl, Nat.factorial_succ]
  push_cast; ring

theorem mono_add_single (x : ι → ℝ) (α : ι →₀ ℕ) (i : ι) :
    mono x (α + Finsupp.single i 1) = x i * mono x α := by
  unfold mono
  have h : ∀ l, x l ^ (α + Finsupp.single i 1 : ι →₀ ℕ) l =
      x l ^ α l * (if i = l then x l else 1) := fun l => by
    rw [Finsupp.add_apply, single_apply_eq, pow_add]; split_ifs <;> simp
  rw [prod_congr rfl fun l _ => h l, prod_mul_distrib, prod_ite_eq univ i (fun l => x l)]
  simp [mul_comm]

omit [DecidableEq ι] in
theorem mono_pos {x : ι → ℝ} (hx : ∀ i, 0 < x i) (α : ι →₀ ℕ) : 0 < mono x α :=
  prod_pos fun i _ => pow_pos (hx i) _

omit [DecidableEq ι] in
theorem mono_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (α : ι →₀ ℕ) : 0 ≤ mono x α :=
  prod_nonneg fun i _ => pow_nonneg (hx i) _

omit [Fintype ι] [DecidableEq ι] in
theorem degree_add_single (α : ι →₀ ℕ) (i : ι) :
    Finsupp.degree (α + Finsupp.single i 1) = Finsupp.degree α + 1 := by
  rw [map_add, Finsupp.degree_single]

/-! ### Derivatives and the Hessian -/

/-- The coefficients of `∂_i f`: `(∂_i c)_β = (β_i + 1) c_{β + e_i}`. -/
def coeffDeriv (i : ι) (c : (ι →₀ ℕ) → ℝ) : (ι →₀ ℕ) → ℝ :=
  fun β => ((β i : ℝ) + 1) * c (β + Finsupp.single i 1)

/-- The quadratic derivatives of `∂_i f` are those of `f`. -/
theorem quadDeriv_coeffDeriv (i : ι) (c : (ι →₀ ℕ) → ℝ) (α : ι →₀ ℕ) :
    quadDeriv (coeffDeriv i c) α = quadDeriv c (α + Finsupp.single i 1) := by
  ext j k
  simp only [quadDeriv, Matrix.of_apply, coeffDeriv]
  have e : α + Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 =
      α + Finsupp.single j 1 + Finsupp.single k 1 + Finsupp.single i 1 := by abel
  rw [e, mfact_add_single (α + Finsupp.single j 1 + Finsupp.single k 1) i]; ring

/-- The Hessian `∇²f(x) = Σ_{|α| = m} (x^α/α!) Q_α`. -/
def hess (c : (ι →₀ ℕ) → ℝ) (m : ℕ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  ∑ α ∈ degSet m, (mono x α / mfact α) • quadDeriv c α

theorem hess_apply (c : (ι →₀ ℕ) → ℝ) (m : ℕ) (x : ι → ℝ) (j k : ι) :
    hess c m x j k = ∑ α ∈ degSet m, mono x α / mfact α * quadDeriv c α j k := by
  simp [hess, Matrix.sum_apply]

theorem hess_isSymm (c : (ι →₀ ℕ) → ℝ) (m : ℕ) (x : ι → ℝ) : (hess c m x).IsSymm :=
  Matrix.IsSymm.ext fun j k => by
    rw [hess_apply, hess_apply]
    exact sum_congr rfl fun α _ => by rw [(quadDeriv_isSymm c α).apply j k]

theorem hess_zero (c : (ι →₀ ℕ) → ℝ) (x : ι → ℝ) : hess c 0 x = quadDeriv c 0 := by
  have h : degSet 0 = ({0} : Finset (ι →₀ ℕ)) := by
    ext α; rw [mem_degSet, Finsupp.degree_eq_zero_iff, mem_singleton]
  simp [hess, h, mono, mfact_eq_prod]

/-- One coordinate of Euler's identity: `Σ_{|α'| = n} x_i (x^{α'}/α'!) Q_{α' + e_i} =
Σ_{|α| = n + 1} α_i (x^α/α!) Q_α`. -/
theorem sum_degSet_shift (c : (ι →₀ ℕ) → ℝ) (n : ℕ) (x : ι → ℝ) (i : ι) :
    ∑ α ∈ degSet n, (x i * (mono x α / mfact α)) • quadDeriv c (α + Finsupp.single i 1) =
      ∑ α ∈ degSet (n + 1), ((α i : ℝ) * (mono x α / mfact α)) • quadDeriv c α := by
  have hfilt : ∑ α ∈ degSet (n + 1), ((α i : ℝ) * (mono x α / mfact α)) • quadDeriv c α =
      ∑ α ∈ (degSet (n + 1)).filter (fun α => 1 ≤ α i),
        ((α i : ℝ) * (mono x α / mfact α)) • quadDeriv c α := by
    rw [sum_filter_of_ne]
    intro α _ h
    by_contra h1
    push Not at h1
    have : α i = 0 := by omega
    simp [this] at h
  rw [hfilt]
  refine sum_nbij' (fun α => α + Finsupp.single i 1) (fun α => α - Finsupp.single i 1) ?_ ?_ ?_ ?_ ?_
  · intro α hα
    rw [mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_degSet, degree_add_single, (mem_degSet.mp hα)]
    · rw [Finsupp.add_apply, single_apply_eq, if_pos rfl]; omega
  · intro α hα
    obtain ⟨h1, h2⟩ := mem_filter.mp hα
    have hle : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.mpr h2
    have := degree_add_single (α - Finsupp.single i 1) i
    rw [tsub_add_cancel_of_le hle, mem_degSet.mp h1] at this
    rw [mem_degSet]; omega
  · intro α _
    exact add_tsub_cancel_right α _
  · intro α hα
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (mem_filter.mp hα).2)
  · intro α _
    rw [mono_add_single, mfact_add_single, Finsupp.add_apply, single_apply_eq, if_pos rfl]
    have := mfact_pos α
    congr 1
    push_cast
    field_simp

/-- **Euler's identity**: `(n + 1) ∇²f(x) = Σ_i x_i ∇²(∂_i f)(x)` for `f` of degree `n + 3`. -/
theorem hess_succ_smul (c : (ι →₀ ℕ) → ℝ) (n : ℕ) (x : ι → ℝ) :
    ((n : ℝ) + 1) • hess c (n + 1) x = ∑ i, x i • hess (coeffDeriv i c) n x := by
  have h : ∀ i, x i • hess (coeffDeriv i c) n x =
      ∑ α ∈ degSet (n + 1), ((α i : ℝ) * (mono x α / mfact α)) • quadDeriv c α := fun i => by
    rw [← sum_degSet_shift, hess, smul_sum]
    refine sum_congr rfl fun α _ => ?_
    rw [quadDeriv_coeffDeriv, smul_smul]
  simp_rw [h]
  rw [sum_comm, hess, smul_sum]
  refine sum_congr rfl fun α hα => ?_
  rw [← sum_smul, ← sum_mul, smul_smul]
  congr 1
  have hdeg : ∑ i, (α i : ℝ) = (n : ℝ) + 1 := by
    have := mem_degSet.mp hα
    rw [Finsupp.degree_eq_sum] at this
    exact_mod_cast this
  rw [hdeg]

/-- **The link condition**: `Σ_k ∇²(∂_i f)(x)_{jk} x_k = (n + 1) ∇²f(x)_{ji}`. -/
theorem sum_hess_coeffDeriv_mul (c : (ι →₀ ℕ) → ℝ) (n : ℕ) (x : ι → ℝ) (i j : ι) :
    ∑ k, hess (coeffDeriv i c) n x j k * x k = ((n : ℝ) + 1) * hess c (n + 1) x j i := by
  have hsw : ∀ (α : ι →₀ ℕ) (k : ι), quadDeriv (coeffDeriv i c) α j k =
      quadDeriv (coeffDeriv k c) α j i := fun α k => by
    rw [quadDeriv_coeffDeriv, quadDeriv_coeffDeriv]
    simp only [quadDeriv, Matrix.of_apply]
    have e : α + Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 =
        α + Finsupp.single k 1 + Finsupp.single j 1 + Finsupp.single i 1 := by abel
    rw [e]
  have h := congrArg (fun M : Matrix ι ι ℝ => M j i) (hess_succ_smul c n x)
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply] at h
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  rw [hess_apply, hess_apply, sum_mul, mul_sum]
  exact sum_congr rfl fun α _ => by rw [hsw]; ring

/-! ### Differentiation preserves the Lorentzian property -/

omit [Fintype ι] in
theorem slice_add_single_eq {α : ι →₀ ℕ} {l a j : ι} (hl : 1 ≤ α l) :
    α - Finsupp.single l 1 + Finsupp.single j 1 + Finsupp.single a 1 =
      α + Finsupp.single a 1 - Finsupp.single l 1 + Finsupp.single j 1 := by
  ext p
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> omega

omit [Fintype ι] in
/-- A slice `{β : β + e_a ∈ S}` of an M-convex set is M-convex. -/
theorem isMConvex_slice {S : Set (ι →₀ ℕ)} (hS : IsMConvex S) (a : ι) :
    IsMConvex {β | β + Finsupp.single a 1 ∈ S} := by
  intro α hα β hβ l hlt
  obtain ⟨j, hj, hmem⟩ := hS _ hα _ hβ l (by simp only [Finsupp.add_apply]; omega)
  refine ⟨j, by simp only [Finsupp.add_apply] at hj; omega, ?_⟩
  show α - Finsupp.single l 1 + Finsupp.single j 1 + Finsupp.single a 1 ∈ S
  rw [slice_add_single_eq (by omega)]
  exact hmem

/-- **Differentiation**: `∂_i f` of a Lorentzian polynomial of degree `n + 3` is Lorentzian. -/
theorem isLorentzianPoly_coeffDeriv {n : ℕ} {c : (ι →₀ ℕ) → ℝ} (hc : IsLorentzianPoly (n + 3) c)
    (i : ι) : IsLorentzianPoly (n + 2) (coeffDeriv i c) := by
  obtain ⟨h0, hdeg, hM, hQ⟩ := hc
  refine ⟨fun β => mul_nonneg (by positivity) (h0 _), fun β hβ => ?_, ?_, fun α hα => ?_⟩
  · have hne : c (β + Finsupp.single i 1) ≠ 0 := fun h => hβ (by simp [coeffDeriv, h])
    have := hdeg _ hne
    rw [degree_add_single] at this
    omega
  · have hset : {β | coeffDeriv i c β ≠ 0} = {β | β + Finsupp.single i 1 ∈ {γ | c γ ≠ 0}} := by
      ext β
      simp only [Set.mem_setOf_eq, coeffDeriv]
      constructor
      · intro h h'; exact h (by rw [h', mul_zero])
      · intro h; exact mul_ne_zero (by positivity) h
    rw [hset]
    exact isMConvex_slice hM i
  · rw [quadDeriv_coeffDeriv]
    exact hQ _ (by rw [degree_add_single]; omega)

/-! ### Sign and support of the Hessian -/

variable {c : (ι →₀ ℕ) → ℝ} {x : ι → ℝ}

theorem quadDeriv_nonneg (hc : ∀ β, 0 ≤ c β) (α : ι →₀ ℕ) (j k : ι) : 0 ≤ quadDeriv c α j k := by
  simp only [quadDeriv, Matrix.of_apply]
  exact mul_nonneg (mfact_pos _).le (hc _)

theorem hess_nonneg (hc : ∀ β, 0 ≤ c β) (m : ℕ) (hx : ∀ i, 0 ≤ x i) (j k : ι) :
    0 ≤ hess c m x j k := by
  rw [hess_apply]
  exact sum_nonneg fun α _ =>
    mul_nonneg (div_nonneg (mono_nonneg hx α) (mfact_pos α).le) (quadDeriv_nonneg hc α j k)

/-- An entry of the Hessian is positive as soon as one monomial `x^γ`, `γ ≥ e_j + e_k`, occurs. -/
theorem hess_pos (hc : ∀ β, 0 ≤ c β) {m : ℕ} (hx : ∀ i, 0 < x i) {j k : ι} {γ : ι →₀ ℕ}
    (hγ : Finsupp.degree γ = m + 2) (hle : Finsupp.single j 1 + Finsupp.single k 1 ≤ γ)
    (hcγ : c γ ≠ 0) : 0 < hess c m x j k := by
  set α := γ - (Finsupp.single j 1 + Finsupp.single k 1)
  have hαγ : α + Finsupp.single j 1 + Finsupp.single k 1 = γ := by
    rw [add_assoc]; exact tsub_add_cancel_of_le hle
  have hα : α ∈ degSet m := by
    rw [mem_degSet]
    have := congrArg Finsupp.degree hαγ
    rw [degree_add_single, degree_add_single, hγ] at this
    omega
  rw [hess_apply]
  refine sum_pos' (fun β _ => mul_nonneg (div_nonneg (mono_nonneg (fun i => (hx i).le) β)
    (mfact_pos β).le) (quadDeriv_nonneg hc β j k)) ⟨α, hα, ?_⟩
  refine mul_pos (div_pos (mono_pos hx α) (mfact_pos α)) ?_
  simp only [quadDeriv, Matrix.of_apply, hαγ]
  exact mul_pos (mfact_pos _) (lt_of_le_of_ne (hc γ) (Ne.symm hcγ))

/-- A positive Hessian entry comes from a monomial `x^γ` with `γ ≥ e_j + e_k`. -/
theorem exists_of_hess_pos {m : ℕ} {j k : ι} (h : 0 < hess c m x j k) :
    ∃ α ∈ degSet m, c (α + Finsupp.single j 1 + Finsupp.single k 1) ≠ 0 := by
  rw [hess_apply] at h
  by_contra hne
  push Not at hne
  have : ∑ α ∈ degSet m, mono x α / mfact α * quadDeriv c α j k = 0 :=
    sum_eq_zero fun α hα => by simp [quadDeriv, hne α hα]
  linarith

omit [DecidableEq ι] in
/-- A matrix with nonnegative entries vanishing on a positive vector is zero. -/
theorem eq_zero_of_qf_eq_zero {M : Matrix ι ι ℝ} (hM : ∀ j k, 0 ≤ M j k) (hx : ∀ i, 0 < x i)
    (h : qf M x = 0) (j k : ι) : M j k = 0 := by
  rw [qf_eq_sum] at h
  have hrow := (sum_eq_zero_iff_of_nonneg fun j _ => sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hx j).le (hM j k)) (hx k).le).mp h j (mem_univ j)
  have hjk := (sum_eq_zero_iff_of_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hx j).le (hM j k)) (hx k).le).mp hrow k (mem_univ k)
  rcases mul_eq_zero.mp hjk with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (hx j).ne'
    · exact h2
  · exact absurd h1 (hx k).ne'

/-! ### Connectivity from M-convexity -/

/-- **The M-convex path lemma.** If `w` is constant on the variables of each monomial of an
M-convex set of degree `D ≥ 2`, it is constant on all variables that occur. The proof walks from
one monomial to another by single exchanges, consecutive monomials sharing a variable. -/
theorem mconvex_path {S : Set (ι →₀ ℕ)} (hS : IsMConvex S) {D : ℕ}
    (hdeg : ∀ γ ∈ S, Finsupp.degree γ = D) (hD : 2 ≤ D) (w : ι → ℝ)
    (hw : ∀ γ ∈ S, ∀ p q, 1 ≤ γ p → 1 ≤ γ q → w p = w q) :
    ∀ e : ℕ, ∀ γ γ' : ι →₀ ℕ, γ ∈ S → γ' ∈ S → ∑ l, (γ l - γ' l) = e →
      ∀ p q, 1 ≤ γ p → 1 ≤ γ' q → w p = w q := by
  intro e
  induction e with
  | zero =>
    intro γ γ' hγ hγ' he p q hp hq
    have hle : ∀ l, γ l ≤ γ' l := fun l => by
      have := (sum_eq_zero_iff.mp he) l (mem_univ l); omega
    have heq : ∀ l, γ l = γ' l := by
      have h1 := hdeg γ hγ
      have h2 := hdeg γ' hγ'
      rw [Finsupp.degree_eq_sum] at h1 h2
      have := (Finset.sum_eq_sum_iff_of_le fun l _ => hle l).mp (h1.trans h2.symm)
      exact fun l => this l (mem_univ l)
    exact hw γ' hγ' p q (heq p ▸ hp) hq
  | succ e ih =>
    intro γ γ' hγ hγ' he p q hp hq
    obtain ⟨l, hl⟩ : ∃ l, γ' l < γ l := by
      by_contra h
      push Not at h
      have : ∑ l, (γ l - γ' l) = 0 := sum_eq_zero fun l _ => by have := h l; omega
      omega
    obtain ⟨k, hk, hmem⟩ := hS γ hγ γ' hγ' l hl
    set γ'' := γ - Finsupp.single l 1 + Finsupp.single k 1
    have hlk : l ≠ k := fun h => by subst h; omega
    have hcoord : ∀ t, γ'' t = γ t - (if l = t then 1 else 0) + (if k = t then 1 else 0) :=
      fun t => by simp only [γ'', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    -- one exchange lowers the excess by one
    have hex : ∑ t, (γ'' t - γ' t) = e := by
      have hpt : ∀ t, (γ'' t - γ' t) + (if l = t then 1 else 0) = γ t - γ' t := fun t => by
        rw [hcoord]
        by_cases h1 : l = t <;> by_cases h2 : k = t <;> simp only [h1, h2, if_true, if_false] <;>
          subst_vars <;> omega
      have := sum_congr rfl fun t (_ : t ∈ univ) => hpt t
      rw [sum_add_distrib, sum_ite_eq univ l (fun _ => 1), if_pos (mem_univ l)] at this
      omega
    -- `γ` and `γ''` share a variable
    obtain ⟨r, hr, hr''⟩ : ∃ r, 1 ≤ γ r ∧ 1 ≤ γ'' r := by
      by_cases h2 : 2 ≤ γ l
      · exact ⟨l, by omega, by rw [hcoord]; simp; omega⟩
      · have hsum : ∑ t ∈ univ.erase l, γ t ≠ 0 := by
          have h1 := hdeg γ hγ
          rw [Finsupp.degree_eq_sum, ← add_sum_erase univ _ (mem_univ l)] at h1
          omega
        obtain ⟨r, hr, hr0⟩ := exists_ne_zero_of_sum_ne_zero hsum
        refine ⟨r, by omega, ?_⟩
        rw [hcoord, if_neg (ne_of_mem_erase hr).symm]
        omega
    exact (hw γ hγ p r hp hr).trans (ih γ'' γ' hmem hγ' hex r q hr'' hq)

/-! ### The trickle-down step -/

section Step

variable {n : ℕ}

omit [DecidableEq ι] in
theorem qf_smul' (a : ℝ) (M : Matrix ι ι ℝ) (v : ι → ℝ) : qf (a • M) v = a * qf M v := by
  simp [qf, bil, smul_mulVec, dotProduct_smul]

omit [DecidableEq ι] in
theorem qf_sum' (M : ι → Matrix ι ι ℝ) (v : ι → ℝ) : qf (∑ i, M i) v = ∑ i, qf (M i) v := by
  simp [qf, bil, Matrix.sum_mulVec, dotProduct_sum]

/-- **The weighted trickle-down inequality of the Hessian**, from hyperbolic Hessians of the
partial derivatives: `∇²f(x)[v] ≤ Σ_i x_i (∇²f(x)v)_i² / (∇²f(x)x)_i`. -/
theorem weightedTrickleDown_hess (hc0 : ∀ β, 0 ≤ c β)
    (hH : ∀ i, IsHyperbolic (hess (coeffDeriv i c) n x)) (hx : ∀ i, 0 < x i) (v : ι → ℝ) :
    qf (hess c (n + 1) x) v ≤
      ∑ i, x i * (hess c (n + 1) x *ᵥ v) i ^ 2 / (hess c (n + 1) x *ᵥ x) i := by
  set Q := hess c (n + 1) x
  set H : ι → Matrix ι ι ℝ := fun i => hess (coeffDeriv i c) n x
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hQs := hess_isSymm c (n + 1) x
  have hsum : ((n : ℝ) + 1) * qf Q v = ∑ i, x i * qf (H i) v := by
    have := congrArg (fun M => qf M v) (hess_succ_smul c n x)
    simp only [qf_smul', qf_sum'] at this
    exact this
  -- the link identities
  have hlink : ∀ i (u : ι → ℝ), bil (H i) u x = ((n : ℝ) + 1) * (Q *ᵥ u) i := fun i u => by
    simp only [bil, dotProduct, mulVec, H]
    simp_rw [sum_hess_coeffDeriv_mul c n x i, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [hQs.apply i j]; simp only [Q]; ring
  have hxx : ∀ i, qf (H i) x = ((n : ℝ) + 1) * (Q *ᵥ x) i := fun i => hlink i x
  have hxv : ∀ i, bil (H i) x v = ((n : ℝ) + 1) * (Q *ᵥ v) i := fun i => by
    rw [bil_comm (hess_isSymm _ n x)]; exact hlink i v
  have hQx0 : ∀ i, 0 ≤ (Q *ᵥ x) i := fun i =>
    sum_nonneg fun j _ => mul_nonneg (hess_nonneg hc0 _ (fun i => (hx i).le) i j) (hx j).le
  have hHnn : ∀ i j k, 0 ≤ H i j k := fun i =>
    hess_nonneg (fun β => mul_nonneg (by positivity) (hc0 _)) n (fun i => (hx i).le)
  -- each link gives one term of the trickle-down inequality
  have hterm : ∀ i, x i * qf (H i) v ≤ ((n : ℝ) + 1) * (x i * (Q *ᵥ v) i ^ 2 / (Q *ᵥ x) i) :=
    fun i => by
      rcases (hQx0 i).lt_or_eq with hpos | hzero
      · have hq : 0 < qf (H i) x := by rw [hxx]; positivity
        have hcs := hH i x v hq
        rw [hxx, hxv] at hcs
        have : qf (H i) v ≤ ((n : ℝ) + 1) * (Q *ᵥ v) i ^ 2 / (Q *ᵥ x) i := by
          rw [le_div_iff₀ hpos]; nlinarith
        calc x i * qf (H i) v ≤ x i * (((n : ℝ) + 1) * (Q *ᵥ v) i ^ 2 / (Q *ᵥ x) i) :=
              mul_le_mul_of_nonneg_left this (hx i).le
          _ = ((n : ℝ) + 1) * (x i * (Q *ᵥ v) i ^ 2 / (Q *ᵥ x) i) := by ring
      · have h0 : qf (H i) x = 0 := by rw [hxx, ← hzero, mul_zero]
        have hz := eq_zero_of_qf_eq_zero (hHnn i) hx h0
        have : qf (H i) v = 0 := by simp [qf, bil, dotProduct, mulVec, hz]
        rw [this, ← hzero, div_zero, mul_zero, mul_zero]
  have := sum_le_sum fun i (_ : i ∈ univ) => hterm i
  rw [← hsum, ← mul_sum] at this
  exact le_of_mul_le_mul_left this hn

end Step

/-! ### The Hessian theorem -/

omit [DecidableEq ι] in
theorem bil_eq_sum (M : Matrix ι ι ℝ) (u v : ι → ℝ) :
    bil M u v = ∑ j, ∑ k, u j * M j k * v k := by
  simp only [bil, dotProduct, mulVec, mul_sum, mul_assoc]

open Classical in
/-- **Trickle-down on the active variables.** A symmetric nonnegative matrix satisfying `(TD_x)` for
some `x > 0`, and connected on the variables with `(Qx)_i > 0`, has one positive square: the
inactive variables carry zero rows, and the active block is a connected Metzler form to which the
weighted Metzler Hodge index theorem applies. -/
theorem isHyperbolic_of_weightedTrickleDown_active {Q : Matrix ι ι ℝ} (hQs : Q.IsSymm)
    (hQnn : ∀ j k, 0 ≤ Q j k) (hx : ∀ i, 0 < x i) (hTD : WeightedTrickleDown x Q)
    (hconn : ∀ w : ι → ℝ, (∀ j k, Q j k ≠ 0 → w j = w k) →
      ∀ a b, 0 < (Q *ᵥ x) a → 0 < (Q *ᵥ x) b → w a = w b) : IsHyperbolic Q := by
  have hQx0 : ∀ i, 0 ≤ (Q *ᵥ x) i := fun i =>
    sum_nonneg fun j _ => mul_nonneg (hQnn i j) (hx j).le
  have hrow0 : ∀ i, ¬ 0 < (Q *ᵥ x) i → ∀ j, Q i j = 0 := fun i hi j => by
    have h0 : (Q *ᵥ x) i = 0 := le_antisymm (not_lt.mp hi) (hQx0 i)
    have := (sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hQnn i k) (hx k).le).mp h0 j
      (mem_univ j)
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (hx j).ne'
  have hcol0 : ∀ i, ¬ 0 < (Q *ᵥ x) i → ∀ j, Q j i = 0 := fun i hi j => by
    rw [hQs.apply i j]; exact hrow0 i hi j
  let A := {i : ι // 0 < (Q *ᵥ x) i}
  have hsplit : ∀ f : ι → ℝ, (∀ i, ¬ 0 < (Q *ᵥ x) i → f i = 0) →
      ∑ i, f i = ∑ a : A, f a.1 := fun f hf => by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => 0 < (Q *ᵥ x) i) f,
      Fintype.sum_eq_zero (fun a : {a // ¬ 0 < (Q *ᵥ x) a} => f a.1) (fun a => hf a.1 a.2),
      add_zero]
  let QA : Matrix A A ℝ := fun a b => Q a.1 b.1
  have hinner : ∀ (j : ι) (v : ι → ℝ), (Q *ᵥ v) j = ∑ b : A, Q j b.1 * v b.1 := fun j v =>
    hsplit (fun k => Q j k * v k) fun k hk => by rw [hcol0 k hk j, zero_mul]
  have hbil : ∀ u v : ι → ℝ, bil Q u v = bil QA (fun a => u a.1) (fun a => v a.1) := fun u v => by
    simp only [bil, dotProduct]
    rw [hsplit (fun j => u j * (Q *ᵥ v) j) fun j hj => by
      simp [mulVec, dotProduct, hrow0 j hj]]
    refine sum_congr rfl fun a _ => ?_
    rw [hinner]; rfl
  have hQAx : ∀ a : A, (QA *ᵥ fun b => x b.1) a = (Q *ᵥ x) a.1 := fun a => by
    rw [hinner]; rfl
  have hQAs : QA.IsSymm := Matrix.IsSymm.ext fun a b => hQs.apply a.1 b.1
  have hQAM : IsMetzler QA := fun a b _ => hQnn a.1 b.1
  have hπ : ∀ a : A, 0 < x a.1 := fun a => hx a.1
  have hQAπ : ∀ a : A, 0 < (QA *ᵥ fun b => x b.1) a := fun a => by rw [hQAx]; exact a.2
  have hQATD : WeightedTrickleDown (fun a : A => x a.1) QA := by
    intro u
    let v : ι → ℝ := fun i => if h : 0 < (Q *ᵥ x) i then u ⟨i, h⟩ else 0
    have hvu : (fun a : A => v a.1) = u := funext fun a => dif_pos a.2
    have hQv : ∀ a : A, (Q *ᵥ v) a.1 = (QA *ᵥ u) a := fun a => by
      rw [hinner, ← hvu]; rfl
    have h := hTD v
    rw [show qf Q v = qf QA u by rw [qf, hbil, hvu]; rfl] at h
    rw [hsplit (fun i => x i * (Q *ᵥ v) i ^ 2 / (Q *ᵥ x) i) fun i hi => by
      rw [show (Q *ᵥ x) i = 0 from le_antisymm (not_lt.mp hi) (hQx0 i), div_zero]] at h
    refine h.trans (le_of_eq (sum_congr rfl fun a _ => ?_))
    rw [hQv, hQAx]
  have hQAc : IsConnectedSupport QA := by
    intro w hw a b
    let W : ι → ℝ := fun i => if h : 0 < (Q *ᵥ x) i then w ⟨i, h⟩ else 0
    have hact : ∀ j k, Q j k ≠ 0 → 0 < (Q *ᵥ x) j := fun j k hjk =>
      calc 0 < Q j k * x k := mul_pos (lt_of_le_of_ne (hQnn j k) (Ne.symm hjk)) (hx k)
        _ ≤ (Q *ᵥ x) j := single_le_sum (f := fun k => Q j k * x k)
            (fun k _ => mul_nonneg (hQnn j k) (hx k).le) (mem_univ k)
    have hW : ∀ j k, Q j k ≠ 0 → W j = W k := fun j k hjk => by
      have hj := hact j k hjk
      have hk := hact k j (by rw [hQs.apply j k]; exact hjk)
      simp only [W, dif_pos hj, dif_pos hk]
      exact hw ⟨j, hj⟩ ⟨k, hk⟩ hjk
    have := hconn W hW a.1 b.1 a.2 b.2
    simpa only [W, dif_pos a.2, dif_pos b.2] using this
  have hA := (isHyperbolic_iff_weightedTrickleDown hQAs hQAM hQAc hπ hQAπ).mpr hQATD
  intro u v hu
  simp only [qf, hbil] at hu ⊢
  exact hA _ _ hu

/-- **The trickle-down step**: if the Hessians of all partial derivatives at `x > 0` are
hyperbolic, so is the Hessian of a Lorentzian polynomial of degree `n + 3`. -/
theorem isHyperbolic_hess_succ {n : ℕ} (hc : IsLorentzianPoly (n + 3) c)
    (hH : ∀ i, IsHyperbolic (hess (coeffDeriv i c) n x)) (hx : ∀ i, 0 < x i) :
    IsHyperbolic (hess c (n + 1) x) := by
  obtain ⟨hc0, hdeg, hM, -⟩ := hc
  refine isHyperbolic_of_weightedTrickleDown_active (hess_isSymm c (n + 1) x)
    (hess_nonneg hc0 _ fun i => (hx i).le) hx (weightedTrickleDown_hess hc0 hH hx) ?_
  intro w hw a b ha hb
  -- every active variable occurs in a monomial
  have hmono : ∀ p, 0 < (hess c (n + 1) x *ᵥ x) p → ∃ γ : ι →₀ ℕ, c γ ≠ 0 ∧ 1 ≤ γ p :=
    fun p hp => by
      obtain ⟨k, -, hk⟩ : ∃ k ∈ univ, 0 < hess c (n + 1) x p k * x k := by
        by_contra h
        push Not at h
        have : (hess c (n + 1) x *ᵥ x) p ≤ 0 := sum_nonpos fun k hk => h k hk
        linarith
      obtain ⟨α, -, hα⟩ := exists_of_hess_pos (pos_of_mul_pos_left hk (hx k).le)
      refine ⟨_, hα, ?_⟩
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> omega
  -- the variables of one monomial are pairwise joined by nonzero Hessian entries
  have hclique : ∀ γ ∈ {γ | c γ ≠ 0}, ∀ p q, 1 ≤ γ p → 1 ≤ γ q → w p = w q := by
    intro γ hγ p q hp hq
    by_cases hpq : p = q
    · rw [hpq]
    have hle : Finsupp.single p 1 + Finsupp.single q 1 ≤ γ := by
      refine Finsupp.le_def.mpr fun t => ?_
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> subst_vars <;> first | omega | exact absurd rfl hpq
    exact hw p q (hess_pos hc0 hx (hdeg γ hγ) hle hγ).ne'
  obtain ⟨γ, hγ, hγa⟩ := hmono a ha
  obtain ⟨γ', hγ', hγb⟩ := hmono b hb
  exact mconvex_path hM (fun γ hγ => hdeg γ hγ) (by omega) w hclique _ γ γ' hγ hγ' rfl a b hγa hγb

/-- **The Hessian of a Lorentzian polynomial has one positive square at every positive point.** -/
theorem isHyperbolic_hess {n : ℕ} {c : (ι →₀ ℕ) → ℝ} (hc : IsLorentzianPoly (n + 2) c)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) : IsHyperbolic (hess c n x) := by
  induction n generalizing c with
  | zero => rw [hess_zero]; exact hc.2.2.2 0 (by simp)
  | succ n ih =>
    have hc' : IsLorentzianPoly (n + 3) c := hc
    exact isHyperbolic_hess_succ hc' (fun i => ih (isLorentzianPoly_coeffDeriv hc' i)) hx

/-- Hyperbolicity is closed: a continuous family hyperbolic for `t > 0` is hyperbolic at `0`. -/
theorem isHyperbolic_of_continuous {Q : ℝ → Matrix ι ι ℝ}
    (hcont : ∀ j k, Continuous fun t => Q t j k) (hpos : ∀ t, 0 < t → IsHyperbolic (Q t)) :
    IsHyperbolic (Q 0) := by
  intro u v hu
  have hq : ∀ w : ι → ℝ, Continuous fun t => qf (Q t) w := fun w => by
    simp only [qf_eq_sum]
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      (continuous_const.mul (hcont j k)).mul continuous_const
  have hb : Continuous fun t => bil (Q t) u v := by
    simp only [bil_eq_sum]
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      (continuous_const.mul (hcont j k)).mul continuous_const
  set F : ℝ → ℝ := fun t => bil (Q t) u v ^ 2 - qf (Q t) u * qf (Q t) v
  have hF : Continuous F := (hb.pow 2).sub ((hq u).mul (hq v))
  have hev : ∀ᶠ t in nhds (0 : ℝ), 0 < qf (Q t) u :=
    (hq u).continuousAt.eventually (lt_mem_nhds hu)
  have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ F t := by
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t ht ht0
    simp only [F, sub_nonneg]
    exact hpos t ht0 u v ht
  have := ge_of_tendsto (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev'
  simp only [F, sub_nonneg] at this
  exact this

/-- **The Hessian theorem at nonnegative points.** In particular every pure directional quadratic
derivative `∂_v^n f = n! ∇²f(v)`, `v ≥ 0`, of a Lorentzian polynomial is hyperbolic. -/
theorem isHyperbolic_hess_of_nonneg {n : ℕ} {c : (ι →₀ ℕ) → ℝ} (hc : IsLorentzianPoly (n + 2) c)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : IsHyperbolic (hess c n x) := by
  have h := isHyperbolic_of_continuous (Q := fun t => hess c n (fun i => x i + t))
    (fun j k => by
      simp only [hess_apply]
      exact continuous_finsetSum _ fun α _ => ((continuous_finsetProd _ fun i _ =>
        (continuous_const.add continuous_id).pow _).div_const _).mul continuous_const)
    (fun t ht => isHyperbolic_hess hc fun i => by linarith [hx i])
  simpa using h

end GaloisForLFunctions.ArithmeticLorentzianGeometry
