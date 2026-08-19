import GaloisForLFunctions.HTGeometry.IncongruentShiftObstruction

/-!
# The second logarithmic derivative of a signed shift product

The ratio of two Gamma monomials satisfies `R(z+1) = ρ(z) R(z)` with

`ρ(z) = ∏_k (z + λ_k)^{n_k}`,  `n_k ∈ ℤ`,

so the obstruction of `IncongruentShiftObstruction` is reached through `deriv (logDeriv ρ)`.  The
corpus has this computation for multiplicity-one products (`deriv_logDeriv_prod_sub`); this file
does it with integer exponents of either sign.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem logDeriv_shift_zpow (lam : ℂ) (n : ℤ) {w : ℂ} (h : w + lam ≠ 0) :
    logDeriv (fun u => (u + lam) ^ n) w = (n : ℂ) * (w + lam)⁻¹ := by
  have hg : DifferentiableAt ℂ (fun u : ℂ => u + lam) w :=
    (differentiable_id.add_const lam).differentiableAt
  have hf : DifferentiableAt ℂ (fun x : ℂ => x ^ n) ((fun u : ℂ => u + lam) w) :=
    differentiableAt_zpow.mpr (Or.inl h)
  have hcomp := logDeriv_comp (f := fun x : ℂ => x ^ n) (g := fun u : ℂ => u + lam)
    (x := w) hf hg
  have hrw : ((fun x : ℂ => x ^ n) ∘ (fun u : ℂ => u + lam)) = fun u : ℂ => (u + lam) ^ n := by
    funext u; rfl
  rw [hrw] at hcomp
  have hd : deriv (fun u : ℂ => u + lam) w = 1 := by
    simp
  rw [hcomp, logDeriv_zpow, hd, mul_one, div_eq_mul_inv]

theorem differentiableAt_shift_zpow (lam : ℂ) (n : ℤ) {w : ℂ} (h : w + lam ≠ 0) :
    DifferentiableAt ℂ (fun u : ℂ => (u + lam) ^ n) w := by
  have hg : DifferentiableAt ℂ (fun u : ℂ => u + lam) w :=
    (differentiable_id.add_const lam).differentiableAt
  have hf : DifferentiableAt ℂ (fun x : ℂ => x ^ n) ((fun u : ℂ => u + lam) w) :=
    differentiableAt_zpow.mpr (Or.inl h)
  have := hf.comp w hg
  have hrw : ((fun x : ℂ => x ^ n) ∘ (fun u : ℂ => u + lam)) = fun u : ℂ => (u + lam) ^ n := by
    funext u; rfl
  rwa [hrw] at this

/-- The logarithmic derivative of a signed shift product. -/
theorem logDeriv_zpowShiftProd {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ) {w : ℂ}
    (h : ∀ k, w + lam k ≠ 0) :
    logDeriv (fun u => ∏ k, (u + lam k) ^ (n k)) w = ∑ k, (n k : ℂ) * (w + lam k)⁻¹ := by
  rw [logDeriv_prod (s := (Finset.univ : Finset (Fin r)))
    (f := fun k => fun u : ℂ => (u + lam k) ^ (n k)) (x := w)
    (fun k _ => zpow_ne_zero _ (h k))
    (fun k _ => differentiableAt_shift_zpow (lam k) (n k) (h k))]
  exact Finset.sum_congr rfl fun k _ => logDeriv_shift_zpow (lam k) (n k) (h k)

/-- The derivative of a signed sum of reciprocals of shifted linear factors. -/
theorem deriv_sum_shift_inv {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ) {z : ℂ}
    (h : ∀ k, z + lam k ≠ 0) :
    deriv (fun w => ∑ k, (n k : ℂ) * (w + lam k)⁻¹) z
      = -∑ k, (n k : ℂ) * ((z + lam k) ^ 2)⁻¹ := by
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin r)),
      HasDerivAt (fun w : ℂ => (n k : ℂ) * (w + lam k)⁻¹)
        (-((n k : ℂ) * ((z + lam k) ^ 2)⁻¹)) z := by
    intro k _
    have hd : HasDerivAt (fun u : ℂ => u + lam k) 1 z := (hasDerivAt_id z).add_const (lam k)
    have hinv := hd.inv (h k)
    have hmul := hinv.const_mul ((n k : ℂ))
    have hrw : (n k : ℂ) * (-1 / (z + lam k) ^ 2) = -((n k : ℂ) * ((z + lam k) ^ 2)⁻¹) := by
      rw [neg_div, one_div]
      ring
    rwa [hrw] at hmul
  have hsum : HasDerivAt (fun w : ℂ => ∑ k, (n k : ℂ) * (w + lam k)⁻¹)
      (∑ k, -((n k : ℂ) * ((z + lam k) ^ 2)⁻¹)) z := HasDerivAt.fun_sum hterm
  rw [hsum.deriv, Finset.sum_neg_distrib]

/-- **The second logarithmic derivative of a signed shift product.** -/
theorem deriv_logDeriv_zpowShiftProd {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℤ) {z : ℂ}
    (h : ∀ k, z + lam k ≠ 0) :
    deriv (logDeriv fun u => ∏ k, (u + lam k) ^ (n k)) z
      = -∑ k, (n k : ℂ) * ((z + lam k) ^ 2)⁻¹ := by
  classical
  have hopen : IsOpen {w : ℂ | ∀ k, w + lam k ≠ 0} := by
    have hcompl : {w : ℂ | ∀ k, w + lam k ≠ 0} = (Set.range fun k : Fin r => -lam k)ᶜ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      constructor
      · intro hw k hk
        exact hw k (by linear_combination -hk)
      · intro hw k hk
        exact hw k (by linear_combination -hk)
    rw [hcompl]
    exact (Set.finite_range _).isClosed.isOpen_compl
  have hev : (logDeriv fun u => ∏ k, (u + lam k) ^ (n k))
      =ᶠ[nhds z] fun w => ∑ k, (n k : ℂ) * (w + lam k)⁻¹ := by
    filter_upwards [hopen.mem_nhds h] with w hw
    exact logDeriv_zpowShiftProd lam n hw
  rw [hev.deriv_eq, deriv_sum_shift_inv lam n h]


/-- **The signed shift obstruction, in the form the Gamma-monomial argument produces it.**  The
second logarithmic derivative of `∏_k (z+λ_k)^{n_k}` is not the unit shift difference of any
meromorphic function with finitely many poles, as soon as one exponent is nonzero and the shifts are
pairwise incongruent modulo `ℤ`. -/
theorem not_shiftDifference_deriv_logDeriv_zpowShiftProd {r : ℕ} (lam : Fin r → ℂ)
    (n : Fin r → ℤ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ))
    (k₀ : Fin r) (hn : n k₀ ≠ 0)
    {y : ℂ → ℂ} (hy : MeromorphicOn y Set.univ)
    (hpoles : {z : ℂ | ¬ AnalyticAt ℂ y z}.Finite) :
    ¬ ((fun z => y (z + 1) - y z)
        =ᶠ[Filter.cofinite] fun z =>
          deriv (logDeriv fun u => ∏ k, (u + lam k) ^ (n k)) z) := by
  classical
  intro heq
  have hfin : {z : ℂ | ¬ (∀ k, z + lam k ≠ 0)}.Finite := by
    refine Set.Finite.subset (Set.finite_range fun k : Fin r => -lam k) ?_
    intro z hz
    simp only [Set.mem_setOf_eq, not_forall, not_not] at hz
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, by linear_combination -hk⟩
  have hcof : (fun z : ℂ => deriv (logDeriv fun u => ∏ k, (u + lam k) ^ (n k)) z)
      =ᶠ[Filter.cofinite] fun z : ℂ => ∑ k, (-(n k : ℂ)) * ((z + lam k) ^ 2)⁻¹ := by
    rw [Filter.EventuallyEq, Filter.eventually_cofinite]
    refine Set.Finite.subset hfin ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    intro hall
    refine hz ?_
    rw [deriv_logDeriv_zpowShiftProd lam n hall, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact not_shiftDifference_signedInvSq_of_incongruent lam (fun k => -(n k : ℂ)) hincong k₀
    (by
      intro hcon
      apply hn
      have : (n k₀ : ℂ) = 0 := by linear_combination -hcon
      exact_mod_cast this)
    hy hpoles (heq.trans hcof)

end

end GaloisForLFunctions.HTGeometry
