import GaloisForLFunctions.HTGeometry.GaussCauchyPolynomialIdentity
import GaloisForLFunctions.HTGeometry.QuasiQuadrature

/-!
# The Cauchy transform of a quasi-orthogonal quadrature measure

Fix a level `n` and a quasi parameter `t`.  The quadrature measure supported on the zeros of
`Q_{n+1} + t·Qₙ` with the interpolatory weights has Cauchy transform

`∑ₓ wₓ/(x − z) = −s₀·(R_{n+1} + t·Rₙ)(z) / (Q_{n+1} + t·Qₙ)(z)`,

the ratio of the two quasi-orthogonal combinations of the second and first kind.  The proof is the
divided-difference identity: the quadrature is exact on the divided difference of `Q_{n+1} + t·Qₙ`,
which the moment functional sends to `s₀·(R_{n+1} + t·Rₙ)`, while at each node the divided
difference collapses to `−(Q_{n+1} + t·Qₙ)(z)/(x − z)`.

Clearing both denominators makes this an identity of polynomials, hence valid after any ring map,
in particular at every complex point.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The quasi-orthogonal combination of the second kind, `R_{n+1} + t·Rₙ`. -/
noncomputable def quasiSecondKind (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : Polynomial ℝ :=
  secondKind s (n + 1) + C t * secondKind s n

theorem quasiSecondKind_eval (s : ℕ → ℝ) (n : ℕ) (t x : ℝ) :
    (quasiSecondKind s n t).eval x
      = (secondKind s (n + 1)).eval x + t * (secondKind s n).eval x := by
  rw [quasiSecondKind]; simp

/-- The divided difference of the quasi-orthogonal polynomial. -/
noncomputable def quasiTransformDividedDiff (s : ℕ → ℝ) (n : ℕ) (t z : ℝ) : Polynomial ℝ :=
  firstKindDividedDiff s (n + 1) z + C t * firstKindDividedDiff s n z

/-- The defining identity: multiplying back by `X − z` returns the difference. -/
theorem mul_quasiTransformDividedDiff (s : ℕ → ℝ) (n : ℕ) (t z : ℝ) :
    (X - C z) * quasiTransformDividedDiff s n t z
      = quasiOrtho s n t - C ((quasiOrtho s n t).eval z) := by
  have h1 := mul_firstKindDividedDiff s (n + 1) z
  have h2 := mul_firstKindDividedDiff s n z
  rw [quasiTransformDividedDiff, quasiOrtho]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.C_add,
    Polynomial.C_mul]
  linear_combination h1 + C t * h2

/-- The divided difference of a first-kind polynomial has degree below the index. -/
theorem firstKindDividedDiff_degree_lt' (s : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    (firstKindDividedDiff s n z).degree < (n : WithBot ℕ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hne : monicOrtho s n - C ((monicOrtho s n).eval z) ≠ 0 := by
      intro hcon
      have heq : monicOrtho s n = C ((monicOrtho s n).eval z) := by rwa [sub_eq_zero] at hcon
      have hdc : (monicOrtho s n).degree ≤ 0 := by rw [heq]; exact Polynomial.degree_C_le
      rw [monicOrtho_degree] at hdc
      exact absurd hdc (by exact_mod_cast (by omega : ¬ (n ≤ 0)))
    have hdeg : (monicOrtho s n - C ((monicOrtho s n).eval z)).degree ≤ (n : WithBot ℕ) := by
      refine le_trans (Polynomial.degree_sub_le _ _) (max_le (le_of_eq (monicOrtho_degree s n)) ?_)
      exact le_trans Polynomial.degree_C_le (by exact_mod_cast Nat.zero_le n)
    have hlt : (firstKindDividedDiff s n z).degree
        < (monicOrtho s n - C ((monicOrtho s n).eval z)).degree := by
      rw [firstKindDividedDiff]
      refine Polynomial.degree_divByMonic_lt _ (X - C z) hne ?_
      rw [Polynomial.degree_X_sub_C]; norm_num
    exact lt_of_lt_of_le hlt hdeg

theorem quasiDividedDiff_degree_le (s : ℕ → ℝ) (n : ℕ) (t z : ℝ) :
    (quasiTransformDividedDiff s n t z).degree ≤ (n : WithBot ℕ) := by
  refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)
  · exact Order.le_of_lt_succ (firstKindDividedDiff_degree_lt' s (n + 1) z)
  · refine le_trans (Polynomial.degree_mul_le _ _) ?_
    have h1 : (firstKindDividedDiff s n z).degree ≤ (n : WithBot ℕ) :=
      le_of_lt (firstKindDividedDiff_degree_lt' s n z)
    calc (C t).degree + (firstKindDividedDiff s n z).degree
        ≤ 0 + (n : WithBot ℕ) := add_le_add Polynomial.degree_C_le h1
      _ = (n : WithBot ℕ) := zero_add _

/-- **The moment functional of the quasi divided difference.** -/
theorem momentFunctional_quasiDividedDiff (h : PositiveMomentForm s) (n : ℕ) (t z : ℝ) :
    momentFunctional s (quasiTransformDividedDiff s n t z)
      = s 0 * (quasiSecondKind s n t).eval z := by
  have hC : momentFunctional s (C t * firstKindDividedDiff s n z)
      = t * momentFunctional s (firstKindDividedDiff s n z) := by
    rw [momentFunctional_eq_inner_one, momentFunctional_eq_inner_one, momentInner_C_mul_left]
  rw [quasiTransformDividedDiff, momentFunctional_add, hC,
    momentFunctional_firstKindDividedDiff h, momentFunctional_firstKindDividedDiff h,
    quasiSecondKind_eval]
  ring


/-! ## The finite-stage closed form -/

/-- **The quasi-orthogonal polynomial factors over its node set.** -/
theorem quasiOrtho_eq_prod (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    quasiOrtho s n t = ∏ y ∈ quasiNodes s n t, (X - C y) := by
  classical
  have hmonic : (quasiOrtho s n t).Monic := quasiOrtho_monic s n t
  have hcard : (quasiOrtho s n t).roots.card = (quasiOrtho s n t).natDegree := by
    rw [quasiOrtho_roots_card h n t, quasiOrtho_natDegree]
  have hfac := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [← hfac, quasiNodes, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (quasiOrtho_roots_nodup h n t)]

/-- **Finite-stage closed form.**  Off the nodes, the Cauchy transform of the quasi-orthogonal
quadrature measure is `−s₀·(R_{n+1} + t·Rₙ)(z)/(Q_{n+1} + t·Qₙ)(z)`. -/
theorem quasiSum_cauchy_eq_ratio (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {z : ℝ}
    (hz : (quasiOrtho s n t).eval z ≠ 0) :
    ∑ x ∈ quasiNodes s n t, quasiWeight s n t x / (x - z)
      = -(s 0 * (quasiSecondKind s n t).eval z) / (quasiOrtho s n t).eval z := by
  classical
  set P := quasiOrtho s n t with hP
  set D := quasiTransformDividedDiff s n t z with hD
  have hDdeg : D.degree ≤ ((2 * n : ℕ) : WithBot ℕ) :=
    le_trans (quasiDividedDiff_degree_le s n t z)
      (by exact_mod_cast (by omega : n ≤ 2 * n))
  have hquad := momentFunctional_eq_quasiSum h n t D hDdeg
  have hmom := momentFunctional_quasiDividedDiff h n t z
  have hnode : ∀ x ∈ quasiNodes s n t, D.eval x = -(P.eval z) / (x - z) := by
    intro x hx
    have hxz : x - z ≠ 0 := by
      intro hcon
      apply hz
      have hxeq : x = z := by linarith [sub_eq_zero.mp hcon]
      rw [← hxeq]
      exact (mem_quasiNodes_iff n t x).mp hx
    have hmul := congrArg (Polynomial.eval x) (mul_quasiTransformDividedDiff s n t z)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hmul
    rw [(mem_quasiNodes_iff n t x).mp hx] at hmul
    field_simp at hmul ⊢
    linarith [hmul]
  rw [hmom] at hquad
  rw [eq_div_iff hz, Finset.sum_mul]
  have hlhs : ∀ x ∈ quasiNodes s n t,
      quasiWeight s n t x / (x - z) * P.eval z = quasiWeight s n t x * D.eval x * (-1) := by
    intro x hx
    rw [hnode x hx]
    field_simp
  rw [Finset.sum_congr rfl hlhs, ← Finset.sum_mul, ← hquad]
  ring

/-! ## The cleared numerator is the quasi second kind -/

/-- The cleared numerator of the quasi-orthogonal quadrature Cauchy transform. -/
noncomputable def quasiCauchyNumerator (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : Polynomial ℝ :=
  ∑ x ∈ quasiNodes s n t,
    C (quasiWeight s n t x) * ∏ y ∈ (quasiNodes s n t).erase x, (X - C y)

theorem eval_quasiCauchyNumerator (s : ℕ → ℝ) (n : ℕ) (t z : ℝ) :
    (quasiCauchyNumerator s n t).eval z
      = ∑ x ∈ quasiNodes s n t,
          quasiWeight s n t x * ∏ y ∈ (quasiNodes s n t).erase x, (z - y) := by
  classical
  rw [quasiCauchyNumerator, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  exact Finset.prod_congr rfl fun y _ => by simp

/-- **The cleared numerator is exactly `s₀·(R_{n+1} + t·Rₙ)`.**  Both sides are polynomials that
agree at every real point off the finite node set, hence identically — so the identity survives any
ring map and holds at every complex point. -/
theorem quasiCauchyNumerator_eq (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    quasiCauchyNumerator s n t = C (s 0) * quasiSecondKind s n t := by
  classical
  set S : Set ℝ := {z : ℝ | (quasiOrtho s n t).eval z ≠ 0} with hS
  have hSinf : S.Infinite := by
    have hfin : {z : ℝ | (quasiOrtho s n t).eval z = 0}.Finite := by
      have hsub : {z : ℝ | (quasiOrtho s n t).eval z = 0}
          ⊆ (quasiOrtho s n t).roots.toFinset := by
        intro z hz
        simp only [Finset.mem_coe, Multiset.mem_toFinset,
          Polynomial.mem_roots (quasiOrtho_ne_zero s n t)]
        exact hz
      exact Set.Finite.subset ((quasiOrtho s n t).roots.toFinset).finite_toSet hsub
    refine (Set.Finite.infinite_compl hfin).mono ?_
    intro z hz
    simpa [hS] using hz
  refine Polynomial.eq_of_infinite_eval_eq _ _ (hSinf.mono ?_)
  intro z hz
  have hzne : (quasiOrtho s n t).eval z ≠ 0 := hz
  have hnodes : ∀ y ∈ quasiNodes s n t, z - y ≠ 0 := by
    intro y hy hcon
    apply hzne
    have hzy : z = y := by linarith [sub_eq_zero.mp hcon]
    rw [hzy]
    exact (mem_quasiNodes_iff n t y).mp hy
  have hprod : (quasiOrtho s n t).eval z = ∏ y ∈ quasiNodes s n t, (z - y) := by
    rw [quasiOrtho_eq_prod h n t, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun y _ => by simp
  have hratio := quasiSum_cauchy_eq_ratio h n t hzne
  have hclear : (∑ x ∈ quasiNodes s n t, quasiWeight s n t x / (x - z)) *
      ∏ y ∈ quasiNodes s n t, (z - y)
      = -∑ x ∈ quasiNodes s n t,
          quasiWeight s n t x * ∏ y ∈ (quasiNodes s n t).erase x, (z - y) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.mul_prod_erase (quasiNodes s n t) (fun y => z - y) hx]
    have hxz : z - x ≠ 0 := hnodes x hx
    have hxz' : x - z ≠ 0 := fun hc => hxz (by linarith [sub_eq_zero.mp hc])
    field_simp
    ring
  simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C,
    eval_quasiCauchyNumerator]
  rw [hratio, ← hprod] at hclear
  field_simp at hclear ⊢
  linarith [hclear]


/-! ## The closed form at a complex point -/

theorem aeval_quasiOrtho_eq_prod (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (z : ℂ) :
    Polynomial.aeval z (quasiOrtho s n t) = ∏ y ∈ quasiNodes s n t, (z - ((y : ℝ) : ℂ)) := by
  classical
  rw [quasiOrtho_eq_prod h n t, map_prod]
  exact Finset.prod_congr rfl fun y _ => by simp

theorem aeval_quasiCauchyNumerator (s : ℕ → ℝ) (n : ℕ) (t : ℝ) (z : ℂ) :
    Polynomial.aeval z (quasiCauchyNumerator s n t)
      = ∑ x ∈ quasiNodes s n t, ((quasiWeight s n t x : ℝ) : ℂ) *
          ∏ y ∈ (quasiNodes s n t).erase x, (z - ((y : ℝ) : ℂ)) := by
  classical
  rw [quasiCauchyNumerator, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_prod]
  simp

/-- **The Cauchy transform of the quasi-orthogonal quadrature measure at a complex point.** -/
theorem quasiSum_cauchy_complex (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {z : ℂ}
    (hz : ∀ y ∈ quasiNodes s n t, z - ((y : ℝ) : ℂ) ≠ 0) :
    ∑ x ∈ quasiNodes s n t, ((quasiWeight s n t x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - z)
      = -((s 0 : ℂ) * Polynomial.aeval z (quasiSecondKind s n t)) /
          Polynomial.aeval z (quasiOrtho s n t) := by
  classical
  have hprod : Polynomial.aeval z (quasiOrtho s n t)
      = ∏ y ∈ quasiNodes s n t, (z - ((y : ℝ) : ℂ)) := aeval_quasiOrtho_eq_prod h n t z
  have hne : Polynomial.aeval z (quasiOrtho s n t) ≠ 0 := by
    rw [hprod]
    exact Finset.prod_ne_zero_iff.mpr hz
  have hnum : Polynomial.aeval z (quasiCauchyNumerator s n t)
      = (s 0 : ℂ) * Polynomial.aeval z (quasiSecondKind s n t) := by
    rw [quasiCauchyNumerator_eq h n t, map_mul]
    simp
  rw [eq_div_iff hne, Finset.sum_mul, hprod]
  have hterm : ∀ x ∈ quasiNodes s n t,
      ((quasiWeight s n t x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - z) *
          ∏ y ∈ quasiNodes s n t, (z - ((y : ℝ) : ℂ))
        = -(((quasiWeight s n t x : ℝ) : ℂ) *
            ∏ y ∈ (quasiNodes s n t).erase x, (z - ((y : ℝ) : ℂ))) := by
    intro x hx
    rw [← Finset.mul_prod_erase (quasiNodes s n t) (fun y => z - ((y : ℝ) : ℂ)) hx]
    have hxz : z - ((x : ℝ) : ℂ) ≠ 0 := hz x hx
    have hxz' : ((x : ℝ) : ℂ) - z ≠ 0 := fun hc => hxz (by linear_combination -hc)
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← aeval_quasiCauchyNumerator, hnum]


end HTGeometry
