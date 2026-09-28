import GaloisForLFunctions.RHTower.ChronologicalFiniteTailObstruction
import GaloisForLFunctions.RHTower.ChronologicalHalfTailGram
import Mathlib.NumberTheory.Bernoulli

/-!
# Least-coefficient-norm moment repair with a fixed moment system

Freeze `a_k = μ(k)` for `k ≤ θN` and choose the tail `θN < k ≤ N` to minimise `Σ a_k²` subject to
finitely many moment constraints `Σ_{k ≤ N} a_k k^p = b_p`, `p ∈ P`.  Minimality forces the tail
functional `v ↦ Σ a_k v_k` to vanish on every tail variation with vanishing moments, so it lies in
the span of the moment functionals: `a_k = Σ_{p ∈ P} λ_p k^p` on the tail.  The tail therefore
samples the fixed function `x ↦ Σ λ_p N^p x^p` of the finite-dimensional space
`span {x^p : p ∈ P}`, and the fixed-tail obstruction applies: for every fixed exponent set and all
right-hand sides the actual residuals stay above a positive level at arbitrarily large `N`.

For `θ = 1/2` and `P = {-1, 0, 1, 3, …, 2m - 1}` with the harmonic-charge, constant and odd-jet
constraints `Σ a_k/k = 0`, `Σ a_k = -2`, `Σ a_k k^{2j-1} = -2j/B_{2j}`, this is the statement that
least-coefficient-norm moment repair with a fixed number `m` of moments cannot converge in `L²`.
-/

open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology Moebius

noncomputable section

namespace RHTower

/-- `a` is a least-coefficient-norm moment repair: it has the Möbius prefix through `θN`, satisfies
the moment constraints `Σ_{k ≤ N} a_k k^p = b_p` (`p ∈ P`), and its tail `ℓ²` norm is minimal among
all such arrays. -/
def IsLeastNormMomentRepair (θ : ℝ) (N : ℕ) (P : Finset ℤ) (b : ℤ → ℝ) (a : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, (k : ℝ) ≤ θ * N → a k = μ k) ∧
  (∀ p ∈ P, ∑ k ∈ Finset.Ioc 0 N, a k * (k : ℝ) ^ p = b p) ∧
  ∀ a' : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) ≤ θ * N → a' k = μ k) →
    (∀ p ∈ P, ∑ k ∈ Finset.Ioc 0 N, a' k * (k : ℝ) ^ p = b p) →
      ∑ k ∈ (Finset.Ioc 0 N).filter (fun k : ℕ => θ * N < k), a k ^ 2 ≤
        ∑ k ∈ (Finset.Ioc 0 N).filter (fun k : ℕ => θ * N < k), a' k ^ 2

/-- A real number `c` with `2 s c + s² Q ≥ 0` for all `s` and `Q ≥ 0` vanishes. -/
theorem eq_zero_of_forall_quadratic_nonneg {c Q : ℝ} (hQ : 0 ≤ Q)
    (h : ∀ s : ℝ, 0 ≤ 2 * s * c + s ^ 2 * Q) : c = 0 := by
  by_contra hc
  have hs := h (-c / (Q + 1))
  have hQ1 : 0 < Q + 1 := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have key : 2 * (-c / (Q + 1)) * c + (-c / (Q + 1)) ^ 2 * Q =
      -(c ^ 2 * (Q + 2)) / (Q + 1) ^ 2 := by field_simp; ring
  rw [key] at hs
  have : 0 < c ^ 2 * (Q + 2) / (Q + 1) ^ 2 := by positivity
  linarith [neg_div ((Q + 1) ^ 2) (c ^ 2 * (Q + 2))]

/-- **Least-norm tails lie in the span of the moment rows.** -/
theorem IsLeastNormMomentRepair.exists_tail_eq {θ : ℝ} {N : ℕ} {P : Finset ℤ} {b : ℤ → ℝ}
    {a : ℕ → ℝ} (h : IsLeastNormMomentRepair θ N P b a) :
    ∃ lam : P → ℝ, ∀ k ∈ Finset.Ioc 0 N, θ * N < k → a k = ∑ p : P, lam p * (k : ℝ) ^ (p : ℤ) := by
  classical
  obtain ⟨hpre, hmom, hmin⟩ := h
  set T := (Finset.Ioc 0 N).filter (fun k : ℕ => θ * N < k) with hT
  -- the moment functionals and the tail functional on `ℕ → ℝ`
  let Lp : P → (ℕ → ℝ) →ₗ[ℝ] ℝ := fun p =>
    { toFun := fun v => ∑ k ∈ T, v k * (k : ℝ) ^ (p : ℤ)
      map_add' := fun v w => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  let Ka : (ℕ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ k ∈ T, a k * v k
      map_add' := fun v w => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  have hker : ⨅ p, LinearMap.ker (Lp p) ≤ LinearMap.ker Ka := by
    intro v hv
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv
    rw [LinearMap.mem_ker]
    -- the variation `a + s v` restricted to the tail is admissible
    set v' : ℕ → ℝ := fun k => if k ∈ T then v k else 0 with hv'
    have hQ : 0 ≤ ∑ k ∈ T, v k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine eq_zero_of_forall_quadratic_nonneg hQ fun s => ?_
    have hadm := hmin (fun k => a k + s * v' k)
      (fun k hk => by
        have hkT : k ∉ T := fun hkT => absurd hk (not_le.mpr (Finset.mem_filter.mp hkT).2)
        simp only [hv', hkT, if_false, mul_zero, add_zero]
        exact hpre k hk)
      (fun p hp => by
        have hvar : ∑ k ∈ Finset.Ioc 0 N, v' k * (k : ℝ) ^ p = 0 := by
          rw [← hv ⟨p, hp⟩]
          simp only [hv', ite_mul, zero_mul, Lp, LinearMap.coe_mk, AddHom.coe_mk]
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
            Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hvar, mul_zero,
          add_zero]
        exact hmom p hp)
    have hexp : ∑ k ∈ T, (a k + s * v' k) ^ 2 =
        ∑ k ∈ T, a k ^ 2 + (2 * s * Ka v + s ^ 2 * ∑ k ∈ T, v k ^ 2) := by
      simp only [Ka, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [hv', hk, if_true]
      ring
    rw [hexp] at hadm
    linarith
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨lam, fun k hk hkθ => ?_⟩
  have hkT : k ∈ T := Finset.mem_filter.mpr ⟨hk, hkθ⟩
  have hev := congrArg (fun F : (ℕ → ℝ) →ₗ[ℝ] ℝ => F (Pi.single k 1)) hlam
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, Ka, Lp,
    LinearMap.coe_mk, AddHom.coe_mk] at hev
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', hkT, if_true] at hev
  exact hev.symm

/-! ### The monomial tail spaces -/

/-- The span of the monomials `x ↦ x^p`, `p ∈ P`. -/
def zpowMonomialSpan (P : Finset ℤ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (Set.range fun p : P => fun x : ℝ => x ^ (p : ℤ))

instance (P : Finset ℤ) : FiniteDimensional ℝ (zpowMonomialSpan P) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem contDiffOn_of_mem_zpowMonomialSpan {θ : ℝ} (hθ0 : 0 < θ) {P : Finset ℤ} {f : ℝ → ℝ}
    (hf : f ∈ zpowMonomialSpan P) : ContDiffOn ℝ 1 f (Icc θ 1) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact contDiffOn_zpow_of_pos hθ0 p
  | zero => exact contDiffOn_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_smul c

/-- **Least-norm moment repair with a fixed moment system cannot converge in `L²`.**  For every
fixed finite exponent set `P` and all right-hand sides, there is `ε > 0` such that at arbitrarily
large `N` every least-coefficient-norm moment repair has residual at least `ε`. -/
theorem leastNormMomentRepair_obstruction {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (P : Finset ℤ)
    (b : ℕ → ℤ → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N ≥ N₀, ∀ a : ℕ → ℝ, IsLeastNormMomentRepair θ N P (b N) a →
      ε ≤ chronologicalL2Norm (chronologicalHeatError a N) := by
  obtain ⟨ε, hε, hN⟩ := chronologicalFiniteTail_obstruction_of_contDiffOn hθ0 hθ1 (zpowMonomialSpan P)
    fun f hf => contDiffOn_of_mem_zpowMonomialSpan hθ0 hf
  refine ⟨ε, hε, fun N₀ => ?_⟩
  obtain ⟨N, hNN₀, hall⟩ := hN (N₀ + 1)
  refine ⟨N, by omega, fun a ha => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨lam, hlam⟩ := ha.exists_tail_eq
  set f : ℝ → ℝ := fun x => ∑ p : P, (lam p * (N : ℝ) ^ (p : ℤ)) * x ^ (p : ℤ) with hfdef
  have hfV : f ∈ zpowMonomialSpan P := by
    have : f = ∑ p : P, (lam p * (N : ℝ) ^ (p : ℤ)) • fun x : ℝ => x ^ (p : ℤ) := by
      funext x; simp [hfdef, Finset.sum_apply, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  have heq : chronologicalHeatError a N = chronologicalHeatError (prefixTailArray θ f N) N := by
    funext t
    simp only [chronologicalHeatError]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    congr 1
    by_cases hkθ : (k : ℝ) ≤ θ * N
    · rw [prefixTailArray, if_pos hkθ, ha.1 k hkθ]
    · rw [prefixTailArray, if_neg hkθ, hlam k hk (lt_of_not_ge hkθ), hfdef]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [div_zpow]
      field_simp [zpow_ne_zero (p : ℤ) hNpos.ne']
  rw [heq]
  exact hall f hfV

/-- The fixed-order moment exponents `{-1, 0, 1, 3, …, 2m - 1}`. -/
def momentExponents (m : ℕ) : Finset ℤ :=
  insert (-1) (insert 0 ((Finset.range m).image fun j : ℕ => (2 * j + 1 : ℤ)))

/-- The fixed-order moment values: harmonic charge `0`, constant `-2`, and odd jets
`-2j/B_{2j}` at `p = 2j - 1`. -/
def momentValues (p : ℤ) : ℝ :=
  if p = -1 then 0 else if p = 0 then -2 else
    -(2 * ((p + 1) / 2 : ℤ) : ℝ) / (bernoulli (2 * ((p + 1) / 2 : ℤ).toNat) : ℝ)

/-- **Fixed-order least-norm moment repair of the half-length Möbius prefix cannot converge.** -/
theorem leastNormMomentRepair_fixedOrder_obstruction (m : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N ≥ N₀, ∀ a : ℕ → ℝ,
      IsLeastNormMomentRepair (1 / 2) N (momentExponents m) momentValues a →
        ε ≤ chronologicalL2Norm (chronologicalHeatError a N) :=
  leastNormMomentRepair_obstruction (by norm_num) (by norm_num) (momentExponents m)
    fun _ => momentValues

end RHTower
