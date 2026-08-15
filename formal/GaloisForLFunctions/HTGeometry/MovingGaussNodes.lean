import GaloisForLFunctions.HTGeometry.HausdorffDifferenceInertia

/-!
# Moving quadrature nodes under a moment flow

A moment sequence obeying the shifted flow `∂_y s k = -(k+1) s (k+1)` moves its Gauss quadrature.
Differentiating the exactness identity against a test polynomial that vanishes at every node and
whose derivative is the indicator of one node isolates the velocity of that node.  The result is
the exact law

`x_i' = -x_i² - 2N h / (w_i p'(x_i)²)`,

the canonical Möbius drift `-x_i²` corrected by the top-moment defect `h = L(p²)`.
-/

open Polynomial

noncomputable section

namespace HTGeometry

/-- The polynomial operator dual to the moment flow: `g ↦ X·(X·g)'`. -/
def momentFlowPoly (g : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.X * (Polynomial.X * g).derivative

theorem momentFunctional_momentFlowPoly (s : ℕ → ℝ) (g : Polynomial ℝ) :
    momentFunctional s (momentFlowPoly g)
      = ∑ k ∈ Finset.range (g.natDegree + 1), ((k : ℝ) + 1) * g.coeff k * s (k + 1) := by
  have hg : g = ∑ k ∈ Finset.range (g.natDegree + 1),
      Polynomial.C (g.coeff k) * Polynomial.X ^ k := by
    conv_lhs => rw [Polynomial.as_sum_range' g (g.natDegree + 1) (Nat.lt_succ_self _)]
    exact Finset.sum_congr rfl fun k _ => (Polynomial.C_mul_X_pow_eq_monomial).symm
  have hk : ∀ k : ℕ,
      Polynomial.X * (Polynomial.X * (Polynomial.C (g.coeff k) * Polynomial.X ^ k)).derivative
        = Polynomial.C (((k : ℝ) + 1) * g.coeff k) * Polynomial.X ^ (k + 1) := by
    intro k
    have h1 : Polynomial.X * (Polynomial.C (g.coeff k) * Polynomial.X ^ k)
        = Polynomial.C (g.coeff k) * Polynomial.X ^ (k + 1) := by ring
    rw [h1, Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
    simp only [Nat.add_sub_cancel, Polynomial.C_mul]
    push_cast
    ring
  have hexp : momentFlowPoly g
      = ∑ k ∈ Finset.range (g.natDegree + 1),
          Polynomial.C (((k : ℝ) + 1) * g.coeff k) * Polynomial.X ^ (k + 1) := by
    rw [momentFlowPoly]
    conv_lhs => rw [hg]
    rw [Finset.mul_sum, Polynomial.derivative_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hk k
  rw [hexp, momentFunctional_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [momentFunctional_C_mul_X_pow]

/-- **The moment functional moves by the dual flow.** -/
theorem hasDerivAt_momentFunctional {s : ℝ → ℕ → ℝ} {y : ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (g : Polynomial ℝ) :
    HasDerivAt (fun t => momentFunctional (s t) g)
      (-(momentFunctional (s y) (momentFlowPoly g))) y := by
  have hrange : ∀ t : ℝ, momentFunctional (s t) g
      = ∑ k ∈ Finset.range (g.natDegree + 1), g.coeff k * s t k := by
    intro t
    rw [momentFunctional, Polynomial.sum_over_range' _ (fun n => by simp) _
      (Nat.lt_succ_self _)]
  have hsum0 := HasDerivAt.sum (fun k (_ : k ∈ Finset.range (g.natDegree + 1)) =>
    (hs k).const_mul (g.coeff k))
  have hfun : (∑ k ∈ Finset.range (g.natDegree + 1), fun t : ℝ => g.coeff k * s t k)
      = fun t : ℝ => ∑ k ∈ Finset.range (g.natDegree + 1), g.coeff k * s t k := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at hsum0
  have hsum : HasDerivAt (fun t => ∑ k ∈ Finset.range (g.natDegree + 1), g.coeff k * s t k)
      (∑ k ∈ Finset.range (g.natDegree + 1),
        g.coeff k * (-(((k : ℝ) + 1) * s y (k + 1)))) y := hsum0
  have hval : ∑ k ∈ Finset.range (g.natDegree + 1),
      g.coeff k * (-(((k : ℝ) + 1) * s y (k + 1)))
      = -(momentFunctional (s y) (momentFlowPoly g)) := by
    rw [momentFunctional_momentFlowPoly]
    rw [Finset.sum_congr rfl (fun k _ =>
      (by ring : g.coeff k * (-(((k : ℝ) + 1) * s y (k + 1)))
        = -(((k : ℝ) + 1) * g.coeff k * s y (k + 1))))]
    exact Finset.sum_neg_distrib (fun k : ℕ => ((k : ℝ) + 1) * g.coeff k * s y (k + 1))
  rw [hval] at hsum
  exact hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrange t)

/-! ## The node polynomial and the velocity test polynomial -/

variable {n : ℕ}

/-- The monic polynomial with the given nodes as simple roots. -/
def nodePoly (x : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∏ i, (Polynomial.X - Polynomial.C (x i))

/-- The cofactor of one node. -/
def nodeCofactorPoly (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j))

/-- The separation `p'(x i) = ∏_{j ≠ i} (x i - x j)`. -/
def nodeSeparation (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (x i - x j)

theorem monic_nodePoly (x : Fin (n + 1) → ℝ) : (nodePoly x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (x i)

theorem natDegree_nodePoly (x : Fin (n + 1) → ℝ) : (nodePoly x).natDegree = n + 1 := by
  rw [nodePoly, Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero (x i)]
  calc ∑ i : Fin (n + 1), (Polynomial.X - Polynomial.C (x i)).natDegree
      = ∑ _i : Fin (n + 1), 1 :=
        Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_sub_C (x i)
    _ = n + 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem monic_nodeCofactorPoly (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeCofactorPoly x i).Monic := by
  classical
  exact Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (x j)

theorem natDegree_nodeCofactorPoly (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeCofactorPoly x i).natDegree = n := by
  classical
  rw [nodeCofactorPoly,
    Polynomial.natDegree_prod _ _ fun j _ => Polynomial.X_sub_C_ne_zero (x j)]
  have hcard : (Finset.univ.erase i).card = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  calc ∑ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j)).natDegree
      = ∑ _j ∈ Finset.univ.erase i, 1 :=
        Finset.sum_congr rfl fun j _ => Polynomial.natDegree_X_sub_C (x j)
    _ = n := by rw [Finset.sum_const, hcard, smul_eq_mul, mul_one]

theorem eval_nodeCofactorPoly (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    (nodeCofactorPoly x i).eval (x j) = if j = i then nodeSeparation x i else 0 := by
  classical
  rw [nodeCofactorPoly, Polynomial.eval_prod]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, nodeSeparation]
    exact Finset.prod_congr rfl fun l _ => by simp
  · rw [if_neg hji]
    refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩) ?_
    simp

/-- The velocity test polynomial: it vanishes at every node and its derivative is the indicator
of the chosen node. -/
def nodeVelocityTest (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Polynomial ℝ :=
  Polynomial.C ((nodeSeparation x i)⁻¹ ^ 2) *
    ((Polynomial.X - Polynomial.C (x i)) * (nodeCofactorPoly x i) ^ 2)

theorem eval_nodeVelocityTest (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    (nodeVelocityTest x i).eval (x j) = 0 := by
  classical
  rw [nodeVelocityTest]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  by_cases hji : j = i
  · subst hji
    simp
  · rw [eval_nodeCofactorPoly, if_neg hji]
    ring

theorem eval_derivative_nodeVelocityTest (x : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hsep : nodeSeparation x i ≠ 0) (j : Fin (n + 1)) :
    (nodeVelocityTest x i).derivative.eval (x j) = if j = i then 1 else 0 := by
  classical
  have hder : (nodeVelocityTest x i).derivative
      = Polynomial.C ((nodeSeparation x i)⁻¹ ^ 2) *
        ((nodeCofactorPoly x i) ^ 2 +
          (Polynomial.X - Polynomial.C (x i)) *
            (Polynomial.C 2 * (nodeCofactorPoly x i) *
              (nodeCofactorPoly x i).derivative)) := by
    rw [nodeVelocityTest, Polynomial.derivative_C_mul, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      Polynomial.derivative_pow]
    ring_nf
  rw [hder]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, eval_nodeCofactorPoly, if_pos rfl, sub_self]
    field_simp
    ring
  · rw [if_neg hji, eval_nodeCofactorPoly, if_neg hji]
    ring

/-! ## Degrees, leading coefficients, and the top-moment correction -/

/-- The monic part of the velocity test polynomial. -/
def nodeVelocityCore (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C (x i)) * (nodeCofactorPoly x i) ^ 2

theorem monic_nodeVelocityCore (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeVelocityCore x i).Monic :=
  (Polynomial.monic_X_sub_C (x i)).mul ((monic_nodeCofactorPoly x i).pow 2)

theorem natDegree_nodeVelocityCore (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeVelocityCore x i).natDegree = 2 * n + 1 := by
  rw [nodeVelocityCore,
    Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C (x i))
      ((monic_nodeCofactorPoly x i).pow 2),
    Polynomial.natDegree_X_sub_C, Polynomial.natDegree_pow, natDegree_nodeCofactorPoly]
  ring

theorem nodeVelocityTest_eq (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    nodeVelocityTest x i = Polynomial.C ((nodeSeparation x i)⁻¹ ^ 2) * nodeVelocityCore x i := rfl

theorem natDegree_nodeVelocityTest_le (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeVelocityTest x i).natDegree ≤ 2 * n + 1 := by
  rw [nodeVelocityTest_eq]
  exact le_trans (Polynomial.natDegree_C_mul_le _ _)
    (le_of_eq (natDegree_nodeVelocityCore x i))

theorem coeff_nodeVelocityTest_top (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeVelocityTest x i).coeff (2 * n + 1) = (nodeSeparation x i)⁻¹ ^ 2 := by
  rw [nodeVelocityTest_eq, Polynomial.coeff_C_mul]
  have h := (monic_nodeVelocityCore x i).coeff_natDegree
  rw [natDegree_nodeVelocityCore] at h
  rw [h, mul_one]

theorem eval_nodePoly (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    (nodePoly x).eval (x j) = 0 := by
  rw [nodePoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

/-- **The top-moment correction.**  Exactness through degree `2n+1` extends to degree `2n+2` with
one correction term, the defect `L(p²)`. -/
theorem momentFunctional_eq_quadSum_add_top {s : ℕ → ℝ} {x w : Fin (n + 1) → ℝ}
    (hquad : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional s g = ∑ i, w i * g.eval (x i))
    (q : Polynomial ℝ) (hq : q.natDegree ≤ 2 * n + 2) :
    momentFunctional s q
      = (∑ i, w i * q.eval (x i)) + q.coeff (2 * n + 2) * momentFunctional s ((nodePoly x) ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = q.coeff (2 * n + 2) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Polynomial ℝ, r = q - Polynomial.C c * (nodePoly x) ^ 2 := ⟨_, rfl⟩
  have hmonic : ((nodePoly x) ^ 2).Monic := (monic_nodePoly x).pow 2
  have hdeg : ((nodePoly x) ^ 2).natDegree = 2 * n + 2 := by
    rw [Polynomial.natDegree_pow, natDegree_nodePoly]
    ring
  have hrdeg : r.natDegree ≤ 2 * n + 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
    rw [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with hm2 | hm2
    · rw [← hm2, hc]
      have hcm : ((nodePoly x) ^ 2).coeff (2 * n + 2) = 1 := by
        have := hmonic.coeff_natDegree
        rwa [hdeg] at this
      rw [hcm, mul_one, sub_self]
    · have h1 : q.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h2 : ((nodePoly x) ^ 2).coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h1, h2, mul_zero, sub_zero]
  have hq' : q = r + Polynomial.C c * (nodePoly x) ^ 2 := by rw [hr]; ring
  have hnodes : ∀ j, ((nodePoly x) ^ 2).eval (x j) = 0 := by
    intro j
    rw [Polynomial.eval_pow, eval_nodePoly]
    ring
  rw [hq', momentFunctional_add, momentFunctional_C_mul, hquad r hrdeg]
  have hsum : ∑ i, w i * (r + Polynomial.C c * (nodePoly x) ^ 2).eval (x i)
      = ∑ i, w i * r.eval (x i) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hnodes j]
    ring
  rw [hsum]
  have hcoeff : (r + Polynomial.C c * (nodePoly x) ^ 2).coeff (2 * n + 2) = c := by
    rw [← hq', ← hc]
  rw [hcoeff]

end HTGeometry

end
