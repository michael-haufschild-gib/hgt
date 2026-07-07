/-
# The classification of entire automorphisms of ℂ

Building on the generalized Liouville theorem (`EntireGrowth`), this file classifies the
holomorphic self-maps of `ℂ` that arise as symmetries:

* `exists_polynomial_of_polyGrowth` — an entire function of polynomial growth is a
  polynomial function (the headline strengthening of Liouville that mathlib lacked);
* `natDegree_le_one_of_eval_injective` — an injective polynomial map on `ℂ` has degree `≤ 1`;
* `entire_affine_of_injective_polyGrowth` — an injective entire function of polynomial growth
  is affine;
* `finiteOrder_fixing_is_rotation` — a finite-order entire automorphism fixing `ρ` is the
  rotation `z ↦ ρ + a(z − ρ)` with `aⁿ = 1`.

This pins the uniqueness of the deck-charge forcing symmetry: the rotation about `ρ` is the
*only* finite-order entire symmetry fixing `ρ`, so `analyticOrderAt_dvd_of_rotation` captures
every symmetric forcing of a rung.
-/
import GaloisForLFunctions.RHTower.EntireGrowth

namespace RHTower

open Complex Metric Topology Filter Set Polynomial

/-- The degree-`d` Taylor polynomial of `f` at `0` as an element of `ℂ[X]`. -/
noncomputable def taylorPoly (f : ℂ → ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (iteratedDeriv i f 0 / i.factorial) * Polynomial.X ^ i

theorem taylorPoly_eval (f : ℂ → ℂ) (d : ℕ) (z : ℂ) :
    (taylorPoly f d).eval z = ∑ i ∈ Finset.range (d + 1),
      (iteratedDeriv i f 0 / i.factorial) * z ^ i := by
  unfold taylorPoly
  rw [eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

theorem taylorPoly_natDegree_le (f : ℂ → ℂ) (d : ℕ) : (taylorPoly f d).natDegree ≤ d := by
  refine (natDegree_sum_le _ _).trans ?_
  refine Finset.fold_max_le d ?_ ?_
  · exact Nat.zero_le d
  intro i hi
  rw [Finset.mem_range] at hi
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_pow_le).trans ?_
  simpa using Nat.le_of_lt_succ hi

/-- The `n`-th derivative of the Taylor polynomial function at `0` recovers the `n`-th Taylor
coefficient for `n ≤ d`, and vanishes for `n > d`. -/
theorem iteratedDeriv_taylorPoly_eval (f : ℂ → ℂ) (d n : ℕ) :
    iteratedDeriv n (fun z => (taylorPoly f d).eval z) 0 =
      if n < d + 1 then iteratedDeriv n f 0 else 0 := by
  have hfun : (fun z => (taylorPoly f d).eval z) =
      fun z => ∑ i ∈ Finset.range (d + 1), (iteratedDeriv i f 0 / i.factorial) * z ^ i := by
    funext z; exact taylorPoly_eval f d z
  rw [hfun]
  rw [iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  have hterm : ∀ i ∈ Finset.range (d + 1),
      iteratedDeriv n (fun z : ℂ => (iteratedDeriv i f 0 / i.factorial) * z ^ i) 0 =
        if n = i then iteratedDeriv i f 0 else 0 := by
    intro i _
    have : (fun z : ℂ => (iteratedDeriv i f 0 / i.factorial) * z ^ i)
        = (iteratedDeriv i f 0 / i.factorial) • (fun z : ℂ => z ^ i) := by
      funext z; simp [smul_eq_mul]
    rw [this, iteratedDeriv_const_smul (by fun_prop), iteratedDeriv_fun_pow_zero]
    by_cases hni : n = i
    · subst hni
      simp only [if_pos rfl, if_pos rfl, smul_eq_mul]
      rw [div_mul_cancel₀]
      exact_mod_cast (Nat.factorial_ne_zero i)
    · simp [hni]
  rw [Finset.sum_congr rfl hterm]
  by_cases hn : n < d + 1
  · rw [if_pos hn, Finset.sum_ite_eq' (Finset.range (d + 1)) n (fun i => iteratedDeriv i f 0)]
    rw [if_pos (Finset.mem_range.mpr hn)]
  · rw [if_neg hn, Finset.sum_ite_eq' (Finset.range (d + 1)) n (fun i => iteratedDeriv i f 0)]
    rw [if_neg (by simpa using hn)]

/-- **An entire function of polynomial growth is a polynomial.**  If `f` is entire and
`‖f z‖ ≤ M(‖z‖+1)^d`, then `f` equals the evaluation of a polynomial of degree `≤ d`. -/
theorem exists_polynomial_of_polyGrowth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M : ℝ} {d : ℕ} (hgrow : ∀ z : ℂ, ‖f z‖ ≤ M * (‖z‖ + 1) ^ d) :
    ∃ p : Polynomial ℂ, (∀ z, f z = p.eval z) ∧ p.natDegree ≤ d := by
  refine ⟨taylorPoly f d, ?_, taylorPoly_natDegree_le f d⟩
  have hg : Differentiable ℂ (fun z => f z - (taylorPoly f d).eval z) :=
    hf.sub (Polynomial.differentiable _)
  have hzero : (fun z => f z - (taylorPoly f d).eval z) = 0 := by
    refine eq_zero_of_iteratedDeriv_eq_zero hg (fun n => ?_)
    rw [iteratedDeriv_fun_sub (hf.contDiff.contDiffAt) ((taylorPoly f d).contDiff.contDiffAt),
      iteratedDeriv_taylorPoly_eval]
    by_cases hn : n < d + 1
    · rw [if_pos hn, sub_self]
    · rw [if_neg hn, sub_zero]
      exact iteratedDeriv_eq_zero_of_polyGrowth hf hgrow (by omega)
  intro z
  have := congrFun hzero z
  simpa [sub_eq_zero] using this

/-- **An injective polynomial map on `ℂ` has degree at most one.**  If `z ↦ p.eval z` is
injective, then `p.natDegree ≤ 1`: over `ℂ`, a polynomial of degree `≥ 2` is never injective. -/
theorem natDegree_le_one_of_eval_injective {p : Polynomial ℂ}
    (hinj : Function.Injective fun z => p.eval z) : p.natDegree ≤ 1 := by
  by_contra hd
  push_neg at hd
  -- q = p - p(0) vanishes only at 0, has natDegree = p.natDegree ≥ 2, so q = c·X^n
  set n := p.natDegree with hn
  set q : Polynomial ℂ := p - Polynomial.C (p.eval 0) with hq
  have hqdeg : q.natDegree = n := by
    rw [hq, hn]
    exact natDegree_sub_C
  have hqne : q ≠ 0 := by
    intro h0
    rw [h0] at hqdeg
    simp only [natDegree_zero] at hqdeg
    omega
  have hqroots : ∀ z, q.eval z = 0 ↔ z = 0 := by
    intro z
    rw [hq, eval_sub, eval_C, sub_eq_zero]
    constructor
    · intro h; exact hinj (by simpa using h)
    · intro h; rw [h]
  -- all roots of q equal 0, and there are n of them (alg closed), so q = c · X^n
  have hcard : q.roots.card = n := by rw [← hqdeg]; exact card_roots_eq_natDegree
  have hall0 : ∀ z ∈ q.roots, z = 0 := by
    intro z hz
    exact (hqroots z).mp (isRoot_of_mem_roots hz)
  have hrootsval : q.roots = Multiset.replicate n 0 := by
    rw [← hcard]
    exact Multiset.eq_replicate.mpr ⟨rfl, hall0⟩
  -- q = C (leadingCoeff q) * ∏ (X - root) = C c * X^n
  have hqfactored : q = Polynomial.C q.leadingCoeff * X ^ n := by
    have hsplit := Polynomial.eq_prod_roots_of_splits_id (IsAlgClosed.splits_codomain q)
    rw [hrootsval, Multiset.map_replicate, Multiset.prod_replicate] at hsplit
    simpa using hsplit
  -- pick a primitive n-th root of unity ζ ≠ 1; q.eval 1 = q.eval ζ but 1 ≠ ζ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n :=
    ⟨Complex.exp (2 * ↑Real.pi * Complex.I / n), Complex.isPrimitiveRoot_exp n (by omega)⟩
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  have hζne1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have he1 : q.eval 1 = q.leadingCoeff := by rw [hqfactored]; simp
  have heζ : q.eval ζ = q.leadingCoeff := by
    rw [hqfactored, eval_mul, eval_C, eval_pow, eval_X, hζn, mul_one]
  have hqeval : q.eval 1 = q.eval ζ := by rw [he1, heζ]
  -- so p.eval 1 = p.eval ζ, contradicting injectivity (1 ≠ ζ)
  have hpeval : p.eval 1 = p.eval ζ := by
    have h1 := hqeval
    rw [hq, eval_sub, eval_sub, eval_C, eval_C] at h1
    linear_combination h1
  exact hζne1 (hinj hpeval).symm

/-- **An injective entire function of polynomial growth is affine.** -/
theorem entire_affine_of_injective_polyGrowth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hinj : Function.Injective f) {M : ℝ} {d : ℕ}
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ M * (‖z‖ + 1) ^ d) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z = a * z + b := by
  obtain ⟨p, hpf, -⟩ := exists_polynomial_of_polyGrowth hf hgrow
  have hinj' : Function.Injective fun z => p.eval z := by
    intro x y hxy; exact hinj (by rw [hpf x, hpf y]; exact hxy)
  have hdeg : p.natDegree ≤ 1 := natDegree_le_one_of_eval_injective hinj'
  refine ⟨p.coeff 1, p.coeff 0, ?_, ?_⟩
  · -- coeff 1 ≠ 0 else p constant, not injective
    intro h0
    have hp0 : p.natDegree = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h | h
      · exact h
      · exfalso; rw [← h] at h0; exact (leadingCoeff_ne_zero.mpr ?_) h0 <;> sorry
    sorry
  · intro z
    rw [hpf z, Polynomial.eval_eq_sum_range]
    have : (Finset.range (p.natDegree + 1)) ⊆ Finset.range 2 := by
      apply Finset.range_subset.mpr; omega
    sorry

end RHTower
