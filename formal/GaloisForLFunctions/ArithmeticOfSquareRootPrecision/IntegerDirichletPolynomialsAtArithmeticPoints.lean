import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityLatticeOfTheHorizon
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialZeroBound

/-!
# Integer Dirichlet polynomials at arithmetic points

An **integer Dirichlet polynomial** of length `N` is `D(s) = Σ_{n ≤ N} a_n n^{−s}` with `a_n ∈ ℤ`
(here indexed by `i : Fin N`, `n = i + 1`, and evaluated at real `σ`). These are the auxiliary
functions of a transcendence argument on the Hecke lattice; this module proves the three classical
ingredients for them, and locates where integrality speaks.

* **The Nair functional is the value at the pole** (`nairIntegral_eq_intDirichlet_one`):
  `∫₀¹ P = D_P(1)` with `D_P(s) = Σ_k p_k (k + 1)^{−s}`.
* **Liouville inequality at `s = m ≥ 1`, sharp** (`one_div_lcmUpto_pow_le_abs_intDirichlet`,
  `exists_intDirichlet_eq_one_div_lcmUpto_pow`). `lcm(1, …, N)^m · D(m) ∈ ℤ`, so a nonzero value is
  at least `lcm(1, …, N)^{−m} = e^{−m ψ(N)}`, and this value is attained. The values at `s = m`
  form the lattice `lcm(1, …, N)^{−m} ℤ`.
* **Integer values on the trivial lattice** (`intDirichlet_neg_natCast`): `D(−k) ∈ ℤ`.
* **Zero estimate on the real axis** (`card_lt_of_intDirichlet_eq_zero`): a nonzero `D` has fewer
  real zeros than nonzero coefficients (Rolle for exponential polynomials).
* **Zero estimate at the trivial lattice** (`exists_one_le_abs_intDirichlet_neg`): a nonzero `D` of
  length `N` has `|D(−k)| ≥ 1` at some `k < N`.
* **Siegel's lemma** (`exists_intDirichlet_vanishing_on_trivial_lattice`): for `0 < M < N` there is a
  nonzero `D` of length `N` vanishing at `s = 0, −1, …, −(M − 1)` with height
  `≤ (N^M)^{M/(N − M)}`. By the zero estimate `M = N` is impossible.

So integrality acts on integer Dirichlet polynomials at `s ∈ ℤ` only: exactly (sharp lattice) at
the pole side `s ≥ 1`, with integer values at `s ≤ 0`. At precision it speaks through `ψ(N)`, i.e.
at the zero width; it never speaks at a nontrivial zero.
-/

noncomputable section

open Real Finset Polynomial

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- An **integer Dirichlet polynomial** of length `N` at real `σ`:
`D(σ) = Σ_{i < N} a_i (i + 1)^{−σ}`. -/
def intDirichlet {N : ℕ} (a : Fin N → ℤ) (σ : ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-σ)

/-! ### The pole: Nair's functional and the Liouville inequality -/

/-- **The Nair functional is the value at the pole** of the integer Dirichlet polynomial of the
coefficients. -/
theorem nairIntegral_eq_intDirichlet_one (P : ℤ[X]) {n : ℕ} (hP : P.natDegree ≤ n) :
    nairIntegral P = intDirichlet (fun i : Fin (n + 1) => P.coeff i) 1 := by
  unfold nairIntegral intDirichlet
  have hrange : ∀ x : ℝ, aeval x P = ∑ i ∈ range (n + 1), (P.coeff i : ℝ) * x ^ i := by
    intro x
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hP)]
    simp [zsmul_eq_mul]
  simp_rw [hrange]
  rw [intervalIntegral.integral_finsetSum (f := fun i x => (P.coeff i : ℝ) * x ^ i) fun i _ =>
    (continuous_const.mul (continuous_pow i)).intervalIntegrable _ _,
    ← Fin.sum_univ_eq_sum_range (fun i => ∫ x in (0 : ℝ)..1, (P.coeff i : ℝ) * x ^ i)]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow, Real.rpow_neg (by positivity),
    Real.rpow_one]
  simp [div_eq_mul_inv]

/-- `lcm(1, …, N)^m · D(m) ∈ ℤ`. -/
theorem exists_int_eq_lcmUpto_pow_mul_intDirichlet {N : ℕ} (a : Fin N → ℤ) (m : ℕ) :
    ∃ z : ℤ, ((Nat.lcmUpto N : ℕ) : ℝ) ^ m * intDirichlet a m = z := by
  refine ⟨∑ i, a i * ((Nat.lcmUpto N / ((i : ℕ) + 1)) ^ m : ℕ), ?_⟩
  unfold intDirichlet
  rw [mul_sum, Int.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  have hdvd : (i : ℕ) + 1 ∣ Nat.lcmUpto N :=
    Finset.dvd_lcm (s := Icc 1 N) (f := id) (mem_Icc.mpr ⟨by omega, by omega⟩)
  have hi : (0 : ℝ) < ((i : ℕ) : ℝ) + 1 := by positivity
  rw [Real.rpow_neg hi.le, Real.rpow_natCast, Int.cast_mul, Int.cast_natCast, Nat.cast_pow,
    Nat.cast_div hdvd (by positivity)]
  push_cast
  field_simp
  rw [div_pow]
  field_simp

/-- **The Liouville inequality at `s = m`**: a nonzero value `D(m)` is at least
`lcm(1, …, N)^{−m}` in modulus. -/
theorem one_div_lcmUpto_pow_le_abs_intDirichlet {N : ℕ} (a : Fin N → ℤ) (m : ℕ)
    (hD : intDirichlet a m ≠ 0) :
    1 / ((Nat.lcmUpto N : ℕ) : ℝ) ^ m ≤ |intDirichlet a m| := by
  obtain ⟨z, hz⟩ := exists_int_eq_lcmUpto_pow_mul_intDirichlet a m
  have hL : (0 : ℝ) < ((Nat.lcmUpto N : ℕ) : ℝ) ^ m := by
    have := Nat.lcmUpto_pos N; positivity
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hD (by simpa [hL.ne'] using hz)
  have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
  rw [div_le_iff₀ hL, ← hz, abs_mul, abs_of_pos hL] at *
  linarith

/-- `lcm(1, …, N)^{−m} = e^{−m ψ(N)}`. -/
theorem one_div_lcmUpto_pow_eq_exp (N m : ℕ) :
    1 / ((Nat.lcmUpto N : ℕ) : ℝ) ^ m = exp (-(m * Chebyshev.psi N)) := by
  rw [Chebyshev.psi_eq_log_lcmUpto, ← Real.log_pow, Real.exp_neg,
    Real.exp_log (by have := Nat.lcmUpto_pos N; positivity), one_div]

/-- `lcm(a^m, b^m) = lcm(a, b)^m`. -/
theorem lcm_pow_pow {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (m : ℕ) :
    Nat.lcm (a ^ m) (b ^ m) = Nat.lcm a b ^ m := by
  refine Nat.eq_of_factorization_eq (Nat.lcm_ne_zero (pow_ne_zero m ha) (pow_ne_zero m hb))
    (pow_ne_zero m (Nat.lcm_ne_zero ha hb)) fun p => ?_
  rw [Nat.factorization_lcm (pow_ne_zero m ha) (pow_ne_zero m hb), Nat.factorization_pow,
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_lcm ha hb]
  simp [Finsupp.sup_apply, Nat.mul_max_mul_left]

/-- The lcm of `m`-th powers is the `m`-th power of the lcm. -/
theorem finset_lcm_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℕ}
    (hf : ∀ i ∈ s, f i ≠ 0) (m : ℕ) : s.lcm (fun i => f i ^ m) = s.lcm f ^ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b t hb ih =>
    rw [Finset.lcm_insert, Finset.lcm_insert, lcm_eq_nat_lcm, lcm_eq_nat_lcm,
      ih fun i hi => hf i (mem_insert_of_mem hi)]
    exact lcm_pow_pow (hf b (mem_insert_self b t)) (Finset.lcm_ne_zero_iff.mpr fun i hi =>
      hf i (mem_insert_of_mem hi)) m

/-- **The Liouville inequality is sharp**: some integer Dirichlet polynomial of length `N ≥ 1`
has `D(m) = lcm(1, …, N)^{−m}`. -/
theorem exists_intDirichlet_eq_one_div_lcmUpto_pow {N : ℕ} (hN : 0 < N) (m : ℕ) :
    ∃ a : Fin N → ℤ, intDirichlet a m = 1 / ((Nat.lcmUpto N : ℕ) : ℝ) ^ m := by
  have hne : (univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, mem_univ _⟩
  obtain ⟨c, hc⟩ := exists_int_sum_div_eq_inv_lcm univ hne (f := fun i : Fin N => ((i : ℕ) + 1) ^ m)
    fun i _ => by positivity
  have hlcm : (univ : Finset (Fin N)).lcm (fun i : Fin N => ((i : ℕ) + 1) ^ m) =
      Nat.lcmUpto N ^ m := by
    rw [finset_lcm_pow _ (fun i _ => by omega)]
    congr 1
    have : (univ : Finset (Fin N)).lcm (fun i : Fin N => (i : ℕ) + 1) =
        ((univ : Finset (Fin N)).image fun i : Fin N => (i : ℕ) + 1).lcm id := by
      rw [Finset.lcm_image]; rfl
    rw [this, Nat.lcmUpto]
    congr 1
    ext n
    simp only [mem_image, mem_univ, true_and, mem_Icc]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨by omega, i.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n - 1, by omega⟩, by simp; omega⟩
  refine ⟨c, ?_⟩
  rw [hlcm] at hc
  unfold intDirichlet
  have hterm : ∀ i : Fin N, ((c i : ℤ) : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-(m : ℝ)) =
      (c i : ℝ) / ((((i : ℕ) + 1) ^ m : ℕ) : ℝ) := by
    intro i
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]
    push_cast; rfl
  simp_rw [hterm]
  rw [hc]
  push_cast; rfl

/-! ### The trivial lattice -/

/-- **Integer values at `s = −k`**: `D(−k) = Σ a_i (i + 1)^k ∈ ℤ`. -/
theorem intDirichlet_neg_natCast {N : ℕ} (a : Fin N → ℤ) (k : ℕ) :
    intDirichlet a (-(k : ℝ)) = ((∑ i, a i * ((i : ℕ) + 1) ^ k : ℤ) : ℝ) := by
  unfold intDirichlet
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [neg_neg, Real.rpow_natCast]

/-- **Zero estimate on the real axis.** A nonzero integer Dirichlet polynomial has fewer real zeros
than nonzero coefficients, in particular fewer than its length. -/
theorem card_lt_of_intDirichlet_eq_zero {N : ℕ} {a : Fin N → ℤ} (ha : a ≠ 0) (S : Finset ℝ)
    (hS : ∀ σ ∈ S, intDirichlet a σ = 0) : S.card < N := by
  classical
  set s := (univ : Finset (Fin N)).filter fun i => a i ≠ 0
  have hs0 : s.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by have := hs0.card_pos; omega⟩
  set e := s.orderEmbOfFin hm
  have he : ∀ j, e j ∈ s := fun j => s.orderEmbOfFin_mem hm j
  have hsum : ∀ σ : ℝ, intDirichlet a σ = HTGeometry.ExpZeroBound.expPoly
      (fun j => -Real.log (((e j : ℕ) : ℝ) + 1)) (fun j => C ((a (e j) : ℤ) : ℝ)) σ := by
    intro σ
    unfold intDirichlet HTGeometry.ExpZeroBound.expPoly
    rw [← sum_filter_ne_zero (s := univ)]
    have hfil : (univ.filter fun i : Fin N => (a i : ℝ) * (((i : ℕ) : ℝ) + 1) ^ (-σ) ≠ 0) ⊆ s := by
      intro i hi
      refine mem_filter.mpr ⟨mem_univ _, fun h0 => ?_⟩
      simp [h0] at hi
    rw [sum_subset hfil fun i _ hi => by
      by_contra h; exact hi (mem_filter.mpr ⟨mem_univ _, h⟩)]
    rw [← s.image_orderEmbOfFin_univ hm, sum_image fun x _ y _ hxy => e.injective hxy]
    refine sum_congr rfl fun j _ => ?_
    rw [eval_C, Real.rpow_def_of_pos (by positivity)]
    ring_nf
  have hcinj : Function.Injective fun j => -Real.log (((e j : ℕ) : ℝ) + 1) := by
    intro j k hjk
    have h := neg_inj.mp hjk
    have h' := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) h
    have : ((e j : ℕ)) = (e k : ℕ) := by exact_mod_cast (add_right_cancel h')
    exact e.injective (Fin.ext this)
  have hP : ∀ j, C ((a (e j) : ℤ) : ℝ) ≠ 0 := fun j => by
    rw [Ne, C_eq_zero, Int.cast_eq_zero]
    exact (mem_filter.mp (he j)).2
  have h := HTGeometry.ExpZeroBound.card_lt_of_expPoly_eq_zero m _ _ hcinj hP S
    fun σ hσ => (hsum σ).symm.trans (hS σ hσ)
  simp only [natDegree_C, zero_add, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at h
  have hsN : s.card ≤ N := by simpa using card_filter_le univ fun i => a i ≠ 0
  omega

/-- **Zero estimate at the trivial lattice**: a nonzero integer Dirichlet polynomial of length `N`
has `|D(−k)| ≥ 1` at some `k < N`. -/
theorem exists_one_le_abs_intDirichlet_neg {N : ℕ} {a : Fin N → ℤ} (ha : a ≠ 0) :
    ∃ k < N, 1 ≤ |intDirichlet a (-(k : ℝ))| := by
  by_contra hno
  push Not at hno
  have hzero : ∀ k < N, intDirichlet a (-(k : ℝ)) = 0 := by
    intro k hk
    have h := hno k hk
    rw [intDirichlet_neg_natCast] at h ⊢
    have : |(∑ i, a i * ((i : ℕ) + 1) ^ k : ℤ)| < 1 := by exact_mod_cast h
    exact_mod_cast Int.abs_lt_one_iff.mp this
  have hcard := card_lt_of_intDirichlet_eq_zero ha ((range N).image fun k : ℕ => -(k : ℝ))
    fun σ hσ => by
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hσ
      exact hzero k (mem_range.mp hk)
  rw [card_image_of_injective _ fun x y h => by exact_mod_cast neg_inj.mp h, card_range] at hcard
  exact lt_irrefl N hcard

/-! ### Siegel's lemma -/

attribute [local instance] Matrix.seminormedAddCommGroup

/-- **Siegel's lemma for integer Dirichlet polynomials.** For `0 < M < N` there is a nonzero integer
Dirichlet polynomial of length `N` vanishing at `s = 0, −1, …, −(M − 1)`, with coefficients bounded
by `(N^M)^{M/(N − M)}`. -/
theorem exists_intDirichlet_vanishing_on_trivial_lattice {M N : ℕ} (hM : 0 < M) (hMN : M < N) :
    ∃ a : Fin N → ℤ, a ≠ 0 ∧ (∀ k < M, intDirichlet a (-(k : ℝ)) = 0) ∧
      ∀ i, |(a i : ℝ)| ≤ ((N : ℝ) ^ M) ^ ((M : ℝ) / (N - M)) := by
  set A : Matrix (Fin M) (Fin N) ℤ := fun k i => ((i : ℕ) + 1) ^ (k : ℕ)
  obtain ⟨t, ht0, hAt, hnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A
    (by simpa using hMN) (by simpa using hM)
  have hA : ‖A‖ ≤ (N : ℝ) ^ (M - 1) := by
    refine (Matrix.norm_le_iff (by positivity)).mpr fun k i => ?_
    simp only [A, Int.norm_eq_abs]
    push_cast
    rw [abs_of_nonneg (by positivity)]
    calc (((i : ℕ) : ℝ) + 1) ^ (k : ℕ) ≤ (N : ℝ) ^ (k : ℕ) :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast i.isLt) _
      _ ≤ (N : ℝ) ^ (M - 1) := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ N))
          (by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hmax : max 1 ‖A‖ ≤ (N : ℝ) ^ (M - 1) :=
    max_le (one_le_pow₀ hN1) hA
  refine ⟨t, ht0, fun k hk => ?_, fun i => ?_⟩
  · rw [intDirichlet_neg_natCast, Int.cast_eq_zero]
    have := congrFun hAt ⟨k, hk⟩
    simp only [Matrix.mulVec, dotProduct, A, Pi.zero_apply] at this
    rw [← this]
    exact sum_congr rfl fun i _ => by ring
  · have h1 : |(t i : ℝ)| ≤ ‖t‖ := by
      rw [← Int.norm_eq_abs, ← Int.norm_cast_real]
      exact norm_le_pi_norm t i
    refine h1.trans (hnorm.trans ?_)
    have hMN' : (M : ℝ) < N := by exact_mod_cast hMN
    have hexp : (0 : ℝ) ≤ (M : ℝ) / (N - M) := div_nonneg (Nat.cast_nonneg M) (by linarith)
    simp only [Fintype.card_fin]
    refine Real.rpow_le_rpow (by positivity) ?_ hexp
    calc (N : ℝ) * max 1 ‖A‖ ≤ N * (N : ℝ) ^ (M - 1) := by gcongr
      _ = (N : ℝ) ^ M := by
          rw [← pow_succ']; congr 1; omega

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision

#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.nairLattice_eq
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.isLeast_positive_nairIntegral
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.isGreatest_log_inv_nairIntegral
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.nairIntegral_eq_intDirichlet_one
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.one_div_lcmUpto_pow_le_abs_intDirichlet
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.exists_intDirichlet_eq_one_div_lcmUpto_pow
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.card_lt_of_intDirichlet_eq_zero
#print axioms GaloisForLFunctions.ArithmeticOfSquareRootPrecision.exists_intDirichlet_vanishing_on_trivial_lattice
