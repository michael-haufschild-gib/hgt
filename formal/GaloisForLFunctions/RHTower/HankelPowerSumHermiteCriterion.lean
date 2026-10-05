import GaloisForLFunctions.RHTower.TraceHankelConverse

/-!
# Hermite's criterion: the power-sum Hankel form detects real-rootedness

Let `f` be a real polynomial of degree `d` with complex roots `x₁, …, x_d` (with multiplicity) and
power sums `P_k = Σ x_i^k`.  The quadratic form of the Hankel matrix `H_d = (P_{i+j})_{i,j<d}` is

`vᵀ H_d v = Σ_i g_v(x_i)²`,  `g_v = Σ_{k<d} v_k X^k`.

If every root is real this is a sum of squares, so `H_d ⪰ 0`.  Conversely, if `α` is a nonreal
root, a real polynomial vanishing at every other root and taking the value `i` at `α` (hence `−i` at
`ᾱ`), reduced modulo `f` to degree `< d`, gives `vᵀ H_d v ≤ −mult(α) < 0`.  So `H_d ⪰ 0` exactly when
`f` is real-rooted.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The complex roots of a real polynomial, with multiplicity. -/
def complexRoots (f : ℝ[X]) : Multiset ℂ := (f.map (algebraMap ℝ ℂ)).roots

/-- The power sum `P_k = Σ x^k` over the complex roots (its real part; the sum itself is real). -/
def rootPowerSum (f : ℝ[X]) (k : ℕ) : ℝ := ((complexRoots f).map fun x => x ^ k).sum.re

/-- The Hankel matrix `(P_{i+j})_{i,j<d}` of the root power sums. -/
def rootPowerSumHankel (f : ℝ[X]) (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => rootPowerSum f (i + j)

theorem multiset_sum_map_eq_sum_count (s : Multiset ℂ) (h : ℂ → ℂ) :
    (s.map h).sum = ∑ x ∈ s.toFinset, (s.count x : ℂ) * h x := by
  classical
  rw [Finset.sum_multiset_map_count]
  exact Finset.sum_congr rfl fun x _ => by rw [nsmul_eq_mul]

/-- **The Hankel form is a sum of squares over the roots.** -/
theorem hankel_form_eq (f : ℝ[X]) (d : ℕ) (v : Fin d → ℝ) :
    star v ⬝ᵥ (rootPowerSumHankel f d).mulVec v =
      ((complexRoots f).map fun x => (∑ i : Fin d, (v i : ℂ) * x ^ (i : ℕ)) ^ 2).sum.re := by
  classical
  set s := complexRoots f with hs
  have hcplx : ∑ i : Fin d, ∑ j : Fin d, (v i : ℂ) * (s.map fun x => x ^ ((i : ℕ) + j)).sum * v j =
      (s.map fun x => (∑ i : Fin d, (v i : ℂ) * x ^ (i : ℕ)) ^ 2).sum := by
    simp only [multiset_sum_map_eq_sum_count]
    calc ∑ i : Fin d, ∑ j : Fin d, (v i : ℂ) * (∑ x ∈ s.toFinset, (s.count x : ℂ) *
          x ^ ((i : ℕ) + j)) * v j
        = ∑ i : Fin d, ∑ j : Fin d, ∑ x ∈ s.toFinset,
            (s.count x : ℂ) * ((v i : ℂ) * x ^ (i : ℕ) * ((v j : ℂ) * x ^ (j : ℕ))) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => by rw [pow_add]; ring
      _ = ∑ i : Fin d, ∑ x ∈ s.toFinset, ∑ j : Fin d,
            (s.count x : ℂ) * ((v i : ℂ) * x ^ (i : ℕ) * ((v j : ℂ) * x ^ (j : ℕ))) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ x ∈ s.toFinset, ∑ i : Fin d, ∑ j : Fin d,
            (s.count x : ℂ) * ((v i : ℂ) * x ^ (i : ℕ) * ((v j : ℂ) * x ^ (j : ℕ))) :=
          Finset.sum_comm
      _ = ∑ x ∈ s.toFinset, (s.count x : ℂ) * (∑ i : Fin d, (v i : ℂ) * x ^ (i : ℕ)) ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [← hcplx]
  have hreal : star v ⬝ᵥ (rootPowerSumHankel f d).mulVec v =
      ∑ i : Fin d, ∑ j : Fin d, v i * rootPowerSum f ((i : ℕ) + j) * v j := by
    simp only [dotProduct, Matrix.mulVec, rootPowerSumHankel, Matrix.of_apply, star_trivial,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hreal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]
  rfl

theorem evalRealPolynomial_add (p q : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (p + q) z = evalRealPolynomial p z + evalRealPolynomial q z := by
  simp [evalRealPolynomial]

/-- **Real roots give a positive semidefinite Hankel form.** -/
theorem rootPowerSumHankel_posSemidef (f : ℝ[X]) (d : ℕ)
    (hreal : ∀ x ∈ complexRoots f, x.im = 0) : (rootPowerSumHankel f d).PosSemidef := by
  classical
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, rootPowerSumHankel, Matrix.of_apply, star_trivial]
    rw [add_comm]
  · rw [hankel_form_eq, multiset_sum_map_eq_sum_count, Complex.re_sum]
    refine Finset.sum_nonneg fun x hx => ?_
    have hxr : x.im = 0 := hreal x (Multiset.mem_toFinset.mp hx)
    have hx : x = ((x.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hxr])
    set y : ℝ := ∑ i : Fin d, v i * x.re ^ (i : ℕ) with hy
    have hsum : ∑ i : Fin d, (v i : ℂ) * x ^ (i : ℕ) = (y : ℂ) := by
      rw [hx, hy]; push_cast; rfl
    rw [hsum, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    positivity

/-- **A nonreal root makes the Hankel form indefinite.** -/
theorem roots_real_of_rootPowerSumHankel_posSemidef (f : ℝ[X]) (hf : f.Monic)
    (hpsd : (rootPowerSumHankel f f.natDegree).PosSemidef) :
    ∀ x ∈ complexRoots f, x.im = 0 := by
  classical
  intro α hα
  by_contra him
  set s := complexRoots f with hs
  set F := s.toFinset with hF
  set sep := realOrbitSeparator F α with hsepdef
  have hsep : evalRealPolynomial sep α ≠ 0 := evalRealOrbitSeparator_ne_zero
  set g₀ := sep * realLinearInterpolator α (I / evalRealPolynomial sep α) with hg₀
  have hg₀α : evalRealPolynomial g₀ α = I := by
    rw [hg₀, evalRealPolynomial_mul, evalRealLinearInterpolator him]
    field_simp
  have hg₀c : evalRealPolynomial g₀ ((starRingEnd ℂ) α) = -I := by
    rw [evalRealPolynomial_conj, hg₀α, Complex.conj_I]
  have hg₀0 : ∀ x ∈ F, x ≠ α → x ≠ (starRingEnd ℂ) α → evalRealPolynomial g₀ x = 0 := by
    intro x hx hxα hxc
    rw [hg₀, evalRealPolynomial_mul, evalRealOrbitSeparator_eq_zero hx hxα hxc, zero_mul]
  have hne : f.map (algebraMap ℝ ℂ) ≠ 0 := (hf.map _).ne_zero
  have hf1 : f ≠ 1 := by
    rintro rfl
    simp [hs, complexRoots] at hα
  set g := g₀ %ₘ f with hg
  have hgdeg : g.natDegree < f.natDegree := natDegree_modByMonic_lt _ hf hf1
  have hgval : ∀ x ∈ s, evalRealPolynomial g x = evalRealPolynomial g₀ x := by
    intro x hx
    have hfx : evalRealPolynomial f x = 0 := (mem_roots hne).mp hx
    have h := congrArg (fun p => evalRealPolynomial p x) (modByMonic_add_div g₀ f)
    simp only [evalRealPolynomial_add, evalRealPolynomial_mul, hfx, zero_mul, add_zero] at h
    exact h
  set v : Fin f.natDegree → ℝ := fun i => g.coeff i with hv
  have hsum : ∀ x : ℂ, ∑ i : Fin f.natDegree, (v i : ℂ) * x ^ (i : ℕ) = evalRealPolynomial g x := by
    intro x
    rw [evalRealPolynomial, eval_eq_sum_range' (n := f.natDegree)
      (lt_of_le_of_lt natDegree_map_le hgdeg), ← Fin.sum_univ_eq_sum_range
        (fun i => (g.map (algebraMap ℝ ℂ)).coeff i * x ^ i)]
    simp [hv, coeff_map]
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 v
  rw [hankel_form_eq] at hform
  simp_rw [hsum] at hform
  rw [multiset_sum_map_eq_sum_count, Complex.re_sum] at hform
  have hαF : α ∈ F := Multiset.mem_toFinset.mpr hα
  have hterm : ∀ x ∈ F, ((s.count x : ℂ) * evalRealPolynomial g x ^ 2).re ≤ 0 := by
    intro x hx
    rw [hgval x (Multiset.mem_toFinset.mp hx)]
    by_cases h1 : x = α
    · rw [h1, hg₀α]; simp
    · by_cases h2 : x = (starRingEnd ℂ) α
      · rw [h2, hg₀c]; simp
      · rw [hg₀0 x hx h1 h2]; simp
  have hαterm : ((s.count α : ℂ) * evalRealPolynomial g α ^ 2).re < 0 := by
    rw [hgval α hα, hg₀α]
    have hc : 0 < s.count α := Multiset.count_pos.mpr hα
    simp only [Complex.I_sq, mul_neg, mul_one, Complex.neg_re, Complex.natCast_re]
    have : (0 : ℝ) < (s.count α : ℝ) := by exact_mod_cast hc
    linarith
  have hrest : ∑ x ∈ F.erase α, ((s.count x : ℂ) * evalRealPolynomial g x ^ 2).re ≤ 0 :=
    Finset.sum_nonpos fun x hx => hterm x (Finset.mem_of_mem_erase hx)
  rw [← Finset.add_sum_erase F _ hαF] at hform
  linarith

/-- **Hermite's criterion.**  A monic real polynomial of degree `d` is real-rooted if and only if the
Hankel matrix `(P_{i+j})_{i,j<d}` of the power sums of its roots is positive semidefinite. -/
theorem rootPowerSumHankel_posSemidef_iff (f : ℝ[X]) (hf : f.Monic) :
    (rootPowerSumHankel f f.natDegree).PosSemidef ↔ ∀ x ∈ complexRoots f, x.im = 0 :=
  ⟨roots_real_of_rootPowerSumHankel_posSemidef f hf, rootPowerSumHankel_posSemidef f _⟩

end

end RHTower
