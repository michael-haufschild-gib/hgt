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
  Polynomial.C ((nodeSeparation x i)⁻¹ ^ (2 : ℕ)) *
    ((Polynomial.X - Polynomial.C (x i)) * (nodeCofactorPoly x i) ^ (2 : ℕ))

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
      = Polynomial.C ((nodeSeparation x i)⁻¹ ^ (2 : ℕ)) *
        ((nodeCofactorPoly x i) ^ (2 : ℕ) +
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
  (Polynomial.X - Polynomial.C (x i)) * (nodeCofactorPoly x i) ^ (2 : ℕ)

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
    nodeVelocityTest x i = Polynomial.C ((nodeSeparation x i)⁻¹ ^ (2 : ℕ)) * nodeVelocityCore x i := rfl

theorem natDegree_nodeVelocityTest_le (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeVelocityTest x i).natDegree ≤ 2 * n + 1 := by
  rw [nodeVelocityTest_eq]
  exact le_trans (Polynomial.natDegree_C_mul_le _ _)
    (le_of_eq (natDegree_nodeVelocityCore x i))

theorem coeff_nodeVelocityTest_top (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeVelocityTest x i).coeff (2 * n + 1) = (nodeSeparation x i)⁻¹ ^ (2 : ℕ) := by
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
      = (∑ i, w i * q.eval (x i)) + q.coeff (2 * n + 2) * momentFunctional s ((nodePoly x) ^ (2 : ℕ)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = q.coeff (2 * n + 2) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Polynomial ℝ, r = q - Polynomial.C c * (nodePoly x) ^ (2 : ℕ) := ⟨_, rfl⟩
  have hmonic : ((nodePoly x) ^ (2 : ℕ)).Monic := (monic_nodePoly x).pow 2
  have hdeg : ((nodePoly x) ^ (2 : ℕ)).natDegree = 2 * n + 2 := by
    rw [Polynomial.natDegree_pow, natDegree_nodePoly]
    ring
  have hrdeg : r.natDegree ≤ 2 * n + 1 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
    rw [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with hm2 | hm2
    · rw [← hm2, hc]
      have hcm : ((nodePoly x) ^ (2 : ℕ)).coeff (2 * n + 2) = 1 := by
        have := hmonic.coeff_natDegree
        rwa [hdeg] at this
      rw [hcm, mul_one, sub_self]
    · have h1 : q.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h2 : ((nodePoly x) ^ (2 : ℕ)).coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h1, h2, mul_zero, sub_zero]
  have hq' : q = r + Polynomial.C c * (nodePoly x) ^ (2 : ℕ) := by rw [hr]; ring
  have hnodes : ∀ j, ((nodePoly x) ^ (2 : ℕ)).eval (x j) = 0 := by
    intro j
    rw [Polynomial.eval_pow, eval_nodePoly]
    ring
  have hLHS : momentFunctional s q
      = momentFunctional s r + c * momentFunctional s ((nodePoly x) ^ (2 : ℕ)) := by
    rw [hq', momentFunctional_add, ← Polynomial.smul_eq_C_mul, momentFunctional_smul]
  have hsum : ∑ i, w i * q.eval (x i) = ∑ i, w i * r.eval (x i) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hq', Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hnodes j]
    ring
  rw [hLHS, hsum, hquad r hrdeg, ← hc]

/-! ## The moving master identity -/

/-- **Differentiating exactness.**  For a fixed test polynomial the quadrature identity
differentiates into a relation between the node and weight velocities and the dual moment flow. -/
theorem moving_master {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ} {g : Polynomial ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t)) :
    ∑ i, (w' i * g.eval (x i y) + w i y * (g.derivative.eval (x i y) * x' i))
      = -(momentFunctional (s y) (momentFlowPoly g)) := by
  have hL := hasDerivAt_momentFunctional hs g
  have hR0 : HasDerivAt (∑ i : Fin (n + 1), fun t : ℝ => w i t * g.eval (x i t))
      (∑ i : Fin (n + 1),
        (w' i * g.eval (x i y) + w i y * (g.derivative.eval (x i y) * x' i))) y := by
    refine HasDerivAt.sum (A := fun i t => w i t * g.eval (x i t))
      (A' := fun i => w' i * g.eval (x i y) + w i y * (g.derivative.eval (x i y) * x' i))
      fun i _ => ?_
    have hcomp : HasDerivAt (fun t => g.eval (x i t)) (g.derivative.eval (x i y) * x' i) y :=
      (Polynomial.hasDerivAt g (x i y)).comp y (hx i)
    exact (hw i).mul hcomp
  have hfun : (∑ i : Fin (n + 1), fun t : ℝ => w i t * g.eval (x i t))
      = fun t : ℝ => ∑ i : Fin (n + 1), w i t * g.eval (x i t) := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at hR0
  have hR : HasDerivAt (fun t => ∑ i : Fin (n + 1), w i t * g.eval (x i t))
      (∑ i : Fin (n + 1),
        (w' i * g.eval (x i y) + w i y * (g.derivative.eval (x i y) * x' i))) y := hR0
  have heq : (fun t => momentFunctional (s t) g)
      = fun t => ∑ i : Fin (n + 1), w i t * g.eval (x i t) := funext hquad
  rw [heq] at hL
  exact hR.unique hL

set_option maxHeartbeats 2000000 in
/-- **The node velocity.**  Under the shifted moment flow every quadrature node moves with the
canonical Möbius drift `-x²` corrected by the top-moment defect. -/
theorem weight_mul_nodeVelocity {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (i₀ : Fin (n + 1)) (hsep : nodeSeparation (fun j => x j y) i₀ ≠ 0) :
    w i₀ y * x' i₀
      = -(w i₀ y * (x i₀ y) ^ (2 : ℕ)
          + (2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
              / (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ)) := by
  classical
  obtain ⟨X0, hX0⟩ : ∃ X0 : Fin (n + 1) → ℝ, X0 = fun j => x j y := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Polynomial ℝ, G = nodeVelocityTest X0 i₀ := ⟨_, rfl⟩
  obtain ⟨hh, hhdef⟩ : ∃ hh : ℝ, hh = momentFunctional (s y) ((nodePoly X0) ^ (2 : ℕ)) := ⟨_, rfl⟩
  obtain ⟨sep, hsepdef⟩ : ∃ sep : ℝ, sep = nodeSeparation X0 i₀ := ⟨_, rfl⟩
  have hsep' : sep ≠ 0 := by rw [hsepdef, hX0]; exact hsep
  have hGdeg : G.natDegree ≤ 2 * n + 1 := by
    rw [hG]; exact natDegree_nodeVelocityTest_le X0 i₀
  have hGtop : G.coeff (2 * n + 1) = sep⁻¹ ^ (2 : ℕ) := by
    rw [hG, hsepdef]; exact coeff_nodeVelocityTest_top X0 i₀
  have hGeval : ∀ j, G.eval (X0 j) = 0 := by
    intro j; rw [hG]; exact eval_nodeVelocityTest X0 i₀ j
  have hGderiv : ∀ j, G.derivative.eval (X0 j) = if j = i₀ then 1 else 0 := by
    intro j
    rw [hG]
    exact eval_derivative_nodeVelocityTest X0 i₀ (by rw [← hsepdef]; exact hsep') j
  have hquadY : ∀ q : Polynomial ℝ, q.natDegree ≤ 2 * n + 1 →
      momentFunctional (s y) q = ∑ i, w i y * q.eval (X0 i) := by
    intro q hq
    rw [hX0]
    exact hquad y q hq
  -- the master identity for the velocity test polynomial
  have hmaster := moving_master (g := G) hs hx hw
    (fun t => hquad t G hGdeg)
  have hLHS : ∑ i, (w' i * G.eval (x i y) + w i y * (G.derivative.eval (x i y) * x' i))
      = w i₀ y * x' i₀ := by
    have hstep : ∀ i : Fin (n + 1),
        w' i * G.eval (x i y) + w i y * (G.derivative.eval (x i y) * x' i)
          = if i = i₀ then w i₀ y * x' i₀ else 0 := by
      intro i
      have h1 : G.eval (x i y) = 0 := by rw [← congrFun hX0 i]; exact hGeval i
      have h2 : G.derivative.eval (x i y) = if i = i₀ then 1 else 0 := by
        rw [← congrFun hX0 i]; exact hGderiv i
      rw [h1, h2, mul_zero, zero_add]
      by_cases hi : i = i₀
      · subst hi; simp
      · rw [if_neg hi, if_neg hi]; ring
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_ite_eq' Finset.univ i₀]
    rw [if_pos (Finset.mem_univ i₀)]
  rw [hLHS] at hmaster
  rw [hmaster]
  -- evaluate the dual flow of the test polynomial
  have hflow : momentFlowPoly G = Polynomial.X * G + Polynomial.X * (Polynomial.X * G.derivative) := by
    rw [momentFlowPoly, Polynomial.derivative_mul, Polynomial.derivative_X]
    ring
  have hdeg1 : (Polynomial.X * G).natDegree ≤ 2 * n + 2 := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_X]
    omega
  have hdeg2 : (Polynomial.X * (Polynomial.X * G.derivative)).natDegree ≤ 2 * n + 2 := by
    have hd : G.derivative.natDegree ≤ 2 * n := by
      refine le_trans (Polynomial.natDegree_derivative_le G) ?_
      omega
    have h1 : (Polynomial.X * G.derivative).natDegree ≤ 2 * n + 1 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_X]
      omega
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_X]
    omega
  have hval1 : momentFunctional (s y) (Polynomial.X * G) = sep⁻¹ ^ (2 : ℕ) * hh := by
    rw [momentFunctional_eq_quadSum_add_top hquadY _ hdeg1]
    have hz : ∀ i : Fin (n + 1), w i y * (Polynomial.X * G).eval (X0 i) = 0 := by
      intro i
      rw [Polynomial.eval_mul, hGeval i]
      ring
    rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero, zero_add,
      Polynomial.coeff_X_mul, hGtop, hhdef]
  have hval2 : momentFunctional (s y) (Polynomial.X * (Polynomial.X * G.derivative))
      = w i₀ y * (X0 i₀) ^ (2 : ℕ) + (2 * (n : ℝ) + 1) * (sep⁻¹ ^ (2 : ℕ) * hh) := by
    rw [momentFunctional_eq_quadSum_add_top hquadY _ hdeg2]
    have hz : ∀ i : Fin (n + 1),
        w i y * (Polynomial.X * (Polynomial.X * G.derivative)).eval (X0 i)
          = if i = i₀ then w i₀ y * (X0 i₀) ^ (2 : ℕ) else 0 := by
      intro i
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, hGderiv i]
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg hi, if_neg hi]; ring
    rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_ite_eq' Finset.univ i₀,
      if_pos (Finset.mem_univ i₀), Polynomial.coeff_X_mul, Polynomial.coeff_X_mul,
      Polynomial.coeff_derivative, hGtop, hhdef]
    push_cast
    ring
  rw [hflow, momentFunctional_add, hval1, hval2]
  have hxi : x i₀ y = X0 i₀ := (congrFun hX0 i₀).symm
  have hnp : (nodePoly fun j => x j y) = nodePoly X0 := by rw [hX0]
  have hsp : nodeSeparation (fun j => x j y) i₀ = sep := by rw [hsepdef, hX0]
  rw [hxi, hnp, ← hhdef, hsp]
  field_simp
  ring

/-- The Christoffel-type normalization `γ_i = w_i · p'(x_i)²`. -/
def nodeEnergy (x w : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  w i * (nodeSeparation x i) ^ (2 : ℕ)

set_option maxHeartbeats 2000000 in
/-- **The hard-coordinate velocity.**  The centred reciprocal coordinate `y - 1/x_i` moves with
velocity `-(2n+2)·L(p²)/(x_i²·γ_i)`, which is strictly negative in a positive chamber. -/
theorem hasDerivAt_hardCoordinate {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (i₀ : Fin (n + 1)) (hsep : nodeSeparation (fun j => x j y) i₀ ≠ 0)
    (hw0 : w i₀ y ≠ 0) (hx0 : x i₀ y ≠ 0) :
    HasDerivAt (fun t => t - (x i₀ t)⁻¹)
      (-((2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
          / ((x i₀ y) ^ (2 : ℕ) * nodeEnergy (fun j => x j y) (fun j => w j y) i₀))) y := by
  have hvel := weight_mul_nodeVelocity hs hx hw hquad i₀ hsep
  have hsep2 : (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hsep
  have hx2 : (x i₀ y) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx0
  have hkey : (w i₀ y * (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ)) * ((x i₀ y) ^ (2 : ℕ) + x' i₀)
      = -((2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))) := by
    field_simp at hvel
    linear_combination hvel
  have hinv : HasDerivAt (fun t => (x i₀ t)⁻¹) (-x' i₀ / (x i₀ y) ^ (2 : ℕ)) y := (hx i₀).inv hx0
  have hsub : HasDerivAt (fun t => t - (x i₀ t)⁻¹) (1 - -x' i₀ / (x i₀ y) ^ (2 : ℕ)) y :=
    (hasDerivAt_id y).sub hinv
  have hval : -((2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
      / ((x i₀ y) ^ (2 : ℕ) * nodeEnergy (fun j => x j y) (fun j => w j y) i₀))
      = 1 - -x' i₀ / (x i₀ y) ^ (2 : ℕ) := by
    rw [nodeEnergy]
    field_simp
    linear_combination -hkey
  rw [hval]
  exact hsub

/-- **The hard coordinate moves strictly left.**  In a positive chamber the defect `L(p²)` and the
node energy are positive, so the velocity is negative. -/
theorem hardCoordinateVelocity_neg {x w : Fin (n + 1) → ℝ} {h : ℝ} (i₀ : Fin (n + 1))
    (hh : 0 < h) (hw : 0 < w i₀) (hsep : nodeSeparation x i₀ ≠ 0) (hx0 : x i₀ ≠ 0) :
    -((2 * (n : ℝ) + 2) * h / ((x i₀) ^ (2 : ℕ) * nodeEnergy x w i₀)) < 0 := by
  have hsep2 : (0 : ℝ) < (nodeSeparation x i₀) ^ (2 : ℕ) :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsep))
  have hx2 : (0 : ℝ) < (x i₀) ^ (2 : ℕ) :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx0))
  have hE : (0 : ℝ) < nodeEnergy x w i₀ := by
    rw [nodeEnergy]
    exact mul_pos hw hsep2
  have hnum : (0 : ℝ) < (2 * (n : ℝ) + 2) * h := by positivity
  have hden : (0 : ℝ) < (x i₀) ^ (2 : ℕ) * nodeEnergy x w i₀ := mul_pos hx2 hE
  have : (0 : ℝ) < (2 * (n : ℝ) + 2) * h / ((x i₀) ^ (2 : ℕ) * nodeEnergy x w i₀) :=
    div_pos hnum hden
  linarith

/-! ## The weight velocity -/

/-- The logarithmic derivative of the cofactor at its own node. -/
def nodeLogDeriv (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, (x i - x k)⁻¹

theorem eval_derivative_nodeCofactorPoly (x : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hdist : ∀ k ∈ Finset.univ.erase i, x i - x k ≠ 0) :
    (nodeCofactorPoly x i).derivative.eval (x i)
      = nodeSeparation x i * nodeLogDeriv x i := by
  classical
  rw [nodeCofactorPoly, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum,
    nodeSeparation, nodeLogDeriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hne : x i - x k ≠ 0 := hdist k hk
  have hsplit : ∏ l ∈ Finset.univ.erase i, (x i - x l)
      = (x i - x k) * ∏ l ∈ (Finset.univ.erase i).erase k, (x i - x l) :=
    (Finset.mul_prod_erase _ _ hk).symm
  rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, Polynomial.eval_one, mul_one,
    hsplit]
  have hterm : ∀ l ∈ (Finset.univ.erase i).erase k,
      (Polynomial.X - Polynomial.C (x l)).eval (x i) = x i - x l := by
    intro l _
    simp
  rw [Finset.prod_congr rfl hterm]
  field_simp

/-- The Hermite basis element dual to the weight of one node. -/
def nodeWeightTest (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Polynomial ℝ :=
  Polynomial.C ((nodeSeparation x i)⁻¹ ^ (2 : ℕ)) *
    ((1 - Polynomial.C (2 * nodeLogDeriv x i) * (Polynomial.X - Polynomial.C (x i))) *
      (nodeCofactorPoly x i) ^ (2 : ℕ))

theorem eval_nodeWeightTest (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1))
    (hsep : nodeSeparation x i ≠ 0) :
    (nodeWeightTest x i).eval (x j) = if j = i then 1 else 0 := by
  classical
  rw [nodeWeightTest]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, eval_nodeCofactorPoly, if_pos rfl, sub_self, mul_zero, sub_zero, one_mul]
    field_simp
  · rw [if_neg hji, eval_nodeCofactorPoly, if_neg hji]
    ring

theorem eval_derivative_nodeWeightTest (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1))
    (hsep : nodeSeparation x i ≠ 0)
    (hdist : ∀ k ∈ Finset.univ.erase i, x i - x k ≠ 0) :
    (nodeWeightTest x i).derivative.eval (x j) = 0 := by
  classical
  have hder : (nodeWeightTest x i).derivative
      = Polynomial.C ((nodeSeparation x i)⁻¹ ^ (2 : ℕ)) *
        ((-(Polynomial.C (2 * nodeLogDeriv x i))) * (nodeCofactorPoly x i) ^ (2 : ℕ)
          + (1 - Polynomial.C (2 * nodeLogDeriv x i) * (Polynomial.X - Polynomial.C (x i))) *
              (Polynomial.C 2 * (nodeCofactorPoly x i) *
                (nodeCofactorPoly x i).derivative)) := by
    rw [nodeWeightTest, Polynomial.derivative_C_mul, Polynomial.derivative_mul,
      Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_C_mul,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      Polynomial.derivative_pow]
    simp only [Polynomial.C_mul]
    push_cast
    ring
  rw [hder]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  by_cases hji : j = i
  · subst hji
    rw [eval_nodeCofactorPoly, if_pos rfl, eval_derivative_nodeCofactorPoly x j hdist, sub_self,
      mul_zero, sub_zero]
    field_simp
    ring
  · rw [eval_nodeCofactorPoly, if_neg hji]
    ring

theorem nodeWeightTest_eq (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    nodeWeightTest x i = Polynomial.C ((nodeSeparation x i)⁻¹ ^ (2 : ℕ)) *
      ((nodeCofactorPoly x i) ^ (2 : ℕ)
        - Polynomial.C (2 * nodeLogDeriv x i) * nodeVelocityCore x i) := by
  rw [nodeWeightTest, nodeVelocityCore]
  ring

theorem natDegree_nodeWeightTest_le (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeWeightTest x i).natDegree ≤ 2 * n + 1 := by
  rw [nodeWeightTest_eq]
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  have h1 : ((nodeCofactorPoly x i) ^ (2 : ℕ)).natDegree ≤ 2 * n + 1 := by
    rw [Polynomial.natDegree_pow, natDegree_nodeCofactorPoly]
    omega
  have h2 : (Polynomial.C (2 * nodeLogDeriv x i) * nodeVelocityCore x i).natDegree
      ≤ 2 * n + 1 := by
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    exact le_of_eq (natDegree_nodeVelocityCore x i)
  omega

theorem coeff_nodeWeightTest_top (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (nodeWeightTest x i).coeff (2 * n + 1)
      = -(2 * nodeLogDeriv x i) * (nodeSeparation x i)⁻¹ ^ (2 : ℕ) := by
  rw [nodeWeightTest_eq, Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  have h1 : ((nodeCofactorPoly x i) ^ (2 : ℕ)).coeff (2 * n + 1) = 0 := by
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    rw [Polynomial.natDegree_pow, natDegree_nodeCofactorPoly]
    omega
  have h2 : (nodeVelocityCore x i).coeff (2 * n + 1) = 1 := by
    have := (monic_nodeVelocityCore x i).coeff_natDegree
    rwa [natDegree_nodeVelocityCore] at this
  rw [h1, h2, mul_one, zero_sub]
  ring

set_option maxHeartbeats 2000000 in
/-- **The weight velocity.**  Under the shifted moment flow the Gauss weights move with the
canonical Möbius drift `-w_i x_i` corrected by the top-moment defect through the node separation. -/
theorem weightVelocity {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (i₀ : Fin (n + 1)) (hsep : nodeSeparation (fun j => x j y) i₀ ≠ 0)
    (hdist : ∀ k ∈ Finset.univ.erase i₀, x i₀ y - x k y ≠ 0) :
    w' i₀ = -(w i₀ y * x i₀ y)
      + (2 * (n : ℝ) + 2) * (2 * nodeLogDeriv (fun j => x j y) i₀)
          * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
          / (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ) := by
  classical
  obtain ⟨X0, hX0⟩ : ∃ X0 : Fin (n + 1) → ℝ, X0 = fun j => x j y := ⟨_, rfl⟩
  have hsep' : nodeSeparation X0 i₀ ≠ 0 := by rw [hX0]; exact hsep
  have hdist' : ∀ k ∈ Finset.univ.erase i₀, X0 i₀ - X0 k ≠ 0 := by
    intro k hk
    rw [hX0]
    exact hdist k hk
  obtain ⟨G, hG⟩ : ∃ G : Polynomial ℝ, G = nodeWeightTest X0 i₀ := ⟨_, rfl⟩
  obtain ⟨hh, hhdef⟩ : ∃ hh : ℝ, hh = momentFunctional (s y) ((nodePoly X0) ^ (2 : ℕ)) := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = -(2 * nodeLogDeriv X0 i₀) * (nodeSeparation X0 i₀)⁻¹ ^ (2 : ℕ) :=
    ⟨_, rfl⟩
  have hGdeg : G.natDegree ≤ 2 * n + 1 := by
    rw [hG]; exact natDegree_nodeWeightTest_le X0 i₀
  have hGtop : G.coeff (2 * n + 1) = c₁ := by
    rw [hG, hc₁]; exact coeff_nodeWeightTest_top X0 i₀
  have hGeval : ∀ j, G.eval (X0 j) = if j = i₀ then 1 else 0 := by
    intro j; rw [hG]; exact eval_nodeWeightTest X0 i₀ j hsep'
  have hGderiv : ∀ j, G.derivative.eval (X0 j) = 0 := by
    intro j; rw [hG]; exact eval_derivative_nodeWeightTest X0 i₀ j hsep' hdist'
  have hquadY : ∀ q : Polynomial ℝ, q.natDegree ≤ 2 * n + 1 →
      momentFunctional (s y) q = ∑ i, w i y * q.eval (X0 i) := by
    intro q hq
    rw [hX0]
    exact hquad y q hq
  have hmaster := moving_master (g := G) hs hx hw (fun t => hquad t G hGdeg)
  have hLHS : ∑ i, (w' i * G.eval (x i y) + w i y * (G.derivative.eval (x i y) * x' i))
      = w' i₀ := by
    have hstep : ∀ i : Fin (n + 1),
        w' i * G.eval (x i y) + w i y * (G.derivative.eval (x i y) * x' i)
          = if i = i₀ then w' i₀ else 0 := by
      intro i
      have h1 : G.eval (x i y) = if i = i₀ then 1 else 0 := by
        rw [← congrFun hX0 i]; exact hGeval i
      have h2 : G.derivative.eval (x i y) = 0 := by
        rw [← congrFun hX0 i]; exact hGderiv i
      rw [h1, h2, zero_mul, mul_zero, add_zero]
      by_cases hi : i = i₀
      · subst hi; rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg hi, if_neg hi, mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hstep i, Finset.sum_ite_eq' Finset.univ i₀,
      if_pos (Finset.mem_univ i₀)]
  rw [hLHS] at hmaster
  rw [hmaster]
  have hflow : momentFlowPoly G
      = Polynomial.X * G + Polynomial.X * (Polynomial.X * G.derivative) := by
    rw [momentFlowPoly, Polynomial.derivative_mul, Polynomial.derivative_X]
    ring
  have hdeg1 : (Polynomial.X * G).natDegree ≤ 2 * n + 2 := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_X]
    omega
  have hdeg2 : (Polynomial.X * (Polynomial.X * G.derivative)).natDegree ≤ 2 * n + 2 := by
    have hd : G.derivative.natDegree ≤ 2 * n := by
      refine le_trans (Polynomial.natDegree_derivative_le G) ?_
      omega
    have h1 : (Polynomial.X * G.derivative).natDegree ≤ 2 * n + 1 := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_X]
      omega
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_X]
    omega
  have hval1 : momentFunctional (s y) (Polynomial.X * G) = w i₀ y * X0 i₀ + c₁ * hh := by
    rw [momentFunctional_eq_quadSum_add_top hquadY _ hdeg1]
    have hz : ∀ i : Fin (n + 1), w i y * (Polynomial.X * G).eval (X0 i)
        = if i = i₀ then w i₀ y * X0 i₀ else 0 := by
      intro i
      rw [Polynomial.eval_mul, Polynomial.eval_X, hGeval i]
      by_cases hi : i = i₀
      · subst hi; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg hi, if_neg hi]; ring
    rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_ite_eq' Finset.univ i₀,
      if_pos (Finset.mem_univ i₀), Polynomial.coeff_X_mul, hGtop, hhdef]
  have hval2 : momentFunctional (s y) (Polynomial.X * (Polynomial.X * G.derivative))
      = (2 * (n : ℝ) + 1) * (c₁ * hh) := by
    rw [momentFunctional_eq_quadSum_add_top hquadY _ hdeg2]
    have hz : ∀ i : Fin (n + 1),
        w i y * (Polynomial.X * (Polynomial.X * G.derivative)).eval (X0 i) = 0 := by
      intro i
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, hGderiv i]
      ring
    rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero, zero_add,
      Polynomial.coeff_X_mul, Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hGtop, hhdef]
    push_cast
    ring
  rw [hflow, momentFunctional_add, hval1, hval2, hc₁, hhdef]
  have hxi : X0 i₀ = x i₀ y := congrFun hX0 i₀
  have hsp : nodeSeparation X0 i₀ = nodeSeparation (fun j => x j y) i₀ := by rw [hX0]
  have hld : nodeLogDeriv X0 i₀ = nodeLogDeriv (fun j => x j y) i₀ := by rw [hX0]
  have hnp : (nodePoly X0) = nodePoly (fun j => x j y) := by rw [hX0]
  rw [hxi, hsp, hld, hnp]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- **(MPW.13) Residue transport.**  The Padé residue `ρ_i = w_i/x_i` of one node moves with the
exact rate `2N·L(p²)·(1 + 2λ_i x_i)/(x_i² p'(x_i)²)`. -/
theorem hasDerivAt_nodeResidue {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (i₀ : Fin (n + 1)) (hsep : nodeSeparation (fun j => x j y) i₀ ≠ 0)
    (hdist : ∀ k ∈ Finset.univ.erase i₀, x i₀ y - x k y ≠ 0) (hx0 : x i₀ y ≠ 0) :
    HasDerivAt (fun t => w i₀ t / x i₀ t)
      ((2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
        * (1 + 2 * nodeLogDeriv (fun j => x j y) i₀ * x i₀ y)
        / ((x i₀ y) ^ (2 : ℕ) * (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ))) y := by
  have hwv := weightVelocity hs hx hw hquad i₀ hsep hdist
  have hxv := weight_mul_nodeVelocity hs hx hw hquad i₀ hsep
  have hquot : HasDerivAt (fun t => w i₀ t / x i₀ t)
      ((w' i₀ * x i₀ y - w i₀ y * x' i₀) / (x i₀ y) ^ (2 : ℕ)) y :=
    (hw i₀).div (hx i₀) hx0
  have hnum : w' i₀ * x i₀ y - w i₀ y * x' i₀
      = (2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
        * (1 + 2 * nodeLogDeriv (fun j => x j y) i₀ * x i₀ y)
        / (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ) := by
    have hsep2 : (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hsep
    rw [hwv]
    field_simp
    field_simp at hxv
    linear_combination -hxv
  rw [hnum] at hquot
  have hx2 : (x i₀ y) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx0
  have hsep2 : (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hsep
  have hrw : (2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
        * (1 + 2 * nodeLogDeriv (fun j => x j y) i₀ * x i₀ y)
        / (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ) / (x i₀ y) ^ (2 : ℕ)
      = (2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
        * (1 + 2 * nodeLogDeriv (fun j => x j y) i₀ * x i₀ y)
        / ((x i₀ y) ^ (2 : ℕ) * (nodeSeparation (fun j => x j y) i₀) ^ (2 : ℕ)) := by
    field_simp
  rw [← hrw]
  exact hquot

/-! ## Total residue growth -/

/-- The Hermite interpolant of `1/X` at the nodes: `(1 - p²/p(0)²)/X`. -/
def reciprocalNodeTest (x : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  Polynomial.divX (1 - Polynomial.C ((((nodePoly x).eval 0) ^ (2 : ℕ))⁻¹) * (nodePoly x) ^ (2 : ℕ))

theorem X_mul_reciprocalNodeTest (x : Fin (n + 1) → ℝ) (h0 : (nodePoly x).eval 0 ≠ 0) :
    Polynomial.X * reciprocalNodeTest x
      = 1 - Polynomial.C ((((nodePoly x).eval 0) ^ (2 : ℕ))⁻¹) * (nodePoly x) ^ (2 : ℕ) := by
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ,
      q = 1 - Polynomial.C ((((nodePoly x).eval 0) ^ (2 : ℕ))⁻¹) * (nodePoly x) ^ (2 : ℕ) := ⟨_, rfl⟩
  have hc : q.coeff 0 = 0 := by
    rw [hq, Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow]
    field_simp
    norm_num
  have hX := Polynomial.X_mul_divX_add q
  rw [hc, Polynomial.C_0, add_zero] at hX
  rw [reciprocalNodeTest, ← hq, hX]

theorem natDegree_reciprocalNodeTest_le (x : Fin (n + 1) → ℝ) :
    (reciprocalNodeTest x).natDegree ≤ 2 * n + 1 := by
  rw [reciprocalNodeTest, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  have hq : (1 - Polynomial.C ((((nodePoly x).eval 0) ^ (2 : ℕ))⁻¹) * (nodePoly x) ^ (2 : ℕ)).natDegree
      ≤ 2 * n + 2 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    have h1 : (1 : Polynomial ℝ).natDegree = 0 := Polynomial.natDegree_one
    have h2 : (Polynomial.C ((((nodePoly x).eval 0) ^ (2 : ℕ))⁻¹) * (nodePoly x) ^ (2 : ℕ)).natDegree
        ≤ 2 * n + 2 := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_pow, natDegree_nodePoly]
      omega
    omega
  omega

theorem eval_reciprocalNodeTest (x : Fin (n + 1) → ℝ) (h0 : (nodePoly x).eval 0 ≠ 0)
    (j : Fin (n + 1)) (hxj : x j ≠ 0) : (reciprocalNodeTest x).eval (x j) = (x j)⁻¹ := by
  have h := congrArg (Polynomial.eval (x j)) (X_mul_reciprocalNodeTest x h0)
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_pow, eval_nodePoly] at h
  have h1 : x j * (reciprocalNodeTest x).eval (x j) = 1 := by
    rw [h]
    ring
  field_simp
  linear_combination h1

theorem eval_derivative_reciprocalNodeTest (x : Fin (n + 1) → ℝ)
    (h0 : (nodePoly x).eval 0 ≠ 0) (j : Fin (n + 1)) (hxj : x j ≠ 0) :
    (reciprocalNodeTest x).derivative.eval (x j) = -((x j) ^ (2 : ℕ))⁻¹ := by
  have hder := congrArg Polynomial.derivative (X_mul_reciprocalNodeTest x h0)
  rw [Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.derivative_C_mul, Polynomial.derivative_pow] at hder
  have h2 := congrArg (Polynomial.eval (x j)) hder
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_zero, Polynomial.eval_C, Polynomial.eval_pow, eval_nodePoly] at h2
  have hval := eval_reciprocalNodeTest x h0 j hxj
  have h3 : (x j)⁻¹ + x j * (reciprocalNodeTest x).derivative.eval (x j) = 0 := by
    rw [← hval]
    rw [h2]
    norm_num
  field_simp at h3 ⊢
  linear_combination h3

set_option maxHeartbeats 2000000 in
/-- **(MPW.14) Total residue growth.**  The total reciprocal weight `∑ w_i/x_i` grows at the exact
rate `2N·L(p²)/p(0)²`. -/
theorem hasDerivAt_totalResidue {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (h0 : (nodePoly (fun j => x j y)).eval 0 ≠ 0) (hxj : ∀ j, x j y ≠ 0) :
    HasDerivAt (fun t => ∑ i, w i t / x i t)
      ((2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
        / ((nodePoly (fun j => x j y)).eval 0) ^ (2 : ℕ)) y := by
  classical
  obtain ⟨X0, hX0⟩ : ∃ X0 : Fin (n + 1) → ℝ, X0 = fun j => x j y := ⟨_, rfl⟩
  have h0'' : (nodePoly X0).eval 0 ≠ 0 := by rw [hX0]; exact h0
  have hxj' : ∀ j, X0 j ≠ 0 := by intro j; rw [hX0]; exact hxj j
  have hgdeg : (reciprocalNodeTest X0).natDegree ≤ 2 * n + 1 :=
    natDegree_reciprocalNodeTest_le X0
  have hmaster := moving_master (g := reciprocalNodeTest X0) hs hx hw
    (fun t => hquad t (reciprocalNodeTest X0) hgdeg)
  have hsum0 : HasDerivAt (∑ i : Fin (n + 1), fun t : ℝ => w i t / x i t)
      (∑ i : Fin (n + 1), (w' i * x i y - w i y * x' i) / (x i y) ^ (2 : ℕ)) y := by
    refine HasDerivAt.sum (A := fun i t => w i t / x i t)
      (A' := fun i => (w' i * x i y - w i y * x' i) / (x i y) ^ (2 : ℕ)) fun i _ => ?_
    exact (hw i).div (hx i) (hxj i)
  have hfun : (∑ i : Fin (n + 1), fun t : ℝ => w i t / x i t)
      = fun t : ℝ => ∑ i : Fin (n + 1), w i t / x i t := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at hsum0
  have hLHS : ∑ i : Fin (n + 1),
      (w' i * (reciprocalNodeTest X0).eval (x i y)
        + w i y * ((reciprocalNodeTest X0).derivative.eval (x i y) * x' i))
      = ∑ i : Fin (n + 1), (w' i * x i y - w i y * x' i) / (x i y) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : x i y ≠ 0 := hxj i
    have hev : (reciprocalNodeTest X0).eval (x i y) = (x i y)⁻¹ := by
      rw [← congrFun hX0 i]
      exact eval_reciprocalNodeTest X0 h0'' i (hxj' i)
    have hdv : (reciprocalNodeTest X0).derivative.eval (x i y) = -((x i y) ^ (2 : ℕ))⁻¹ := by
      rw [← congrFun hX0 i]
      exact eval_derivative_reciprocalNodeTest X0 h0'' i (hxj' i)
    rw [hev, hdv, eq_div_iff (pow_ne_zero 2 hne)]
    field_simp
    ring
  rw [hLHS] at hmaster
  have hXg : Polynomial.X * reciprocalNodeTest X0
      = 1 - Polynomial.C (((( nodePoly X0).eval 0) ^ (2 : ℕ))⁻¹) * (nodePoly X0) ^ (2 : ℕ) :=
    X_mul_reciprocalNodeTest X0 h0''
  have hflow : momentFlowPoly (reciprocalNodeTest X0)
      = Polynomial.C (-(2 * (((nodePoly X0).eval 0) ^ (2 : ℕ))⁻¹)) *
        (Polynomial.X * ((nodePoly X0) * (nodePoly X0).derivative)) := by
    rw [momentFlowPoly, hXg, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_C_mul, Polynomial.derivative_pow]
    simp only [Polynomial.C_neg, Polynomial.C_mul]
    push_cast
    ring
  have hpdeg : (nodePoly X0).natDegree = n + 1 := natDegree_nodePoly X0
  have hpmonic : (nodePoly X0).Monic := monic_nodePoly X0
  have hpderivdeg : (nodePoly X0).derivative.natDegree = n := by
    rw [Polynomial.natDegree_derivative (nodePoly X0), hpdeg]
    omega
  have hlead : (nodePoly X0).derivative.leadingCoeff = (n : ℝ) + 1 := by
    rw [Polynomial.leadingCoeff, hpderivdeg, Polynomial.coeff_derivative]
    have hc : (nodePoly X0).coeff (n + 1) = 1 := by
      have := hpmonic.coeff_natDegree
      rwa [hpdeg] at this
    rw [hc]
    ring
  have htop : (Polynomial.X * ((nodePoly X0) * (nodePoly X0).derivative)).coeff (2 * n + 2)
      = (n : ℝ) + 1 := by
    have hcm := Polynomial.coeff_mul_degree_add_degree (nodePoly X0) (nodePoly X0).derivative
    rw [hpdeg, hpderivdeg, hpmonic.leadingCoeff, one_mul, hlead] at hcm
    have hidx : 2 * n + 2 = (n + 1 + n) + 1 := by omega
    rw [hidx, Polynomial.coeff_X_mul, hcm]
  have hdegXpp :
      (Polynomial.X * ((nodePoly X0) * (nodePoly X0).derivative)).natDegree ≤ 2 * n + 2 := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    refine le_trans (Nat.add_le_add_left Polynomial.natDegree_mul_le _) ?_
    rw [Polynomial.natDegree_X, hpdeg, hpderivdeg]
    omega
  have hquadY : ∀ q : Polynomial ℝ, q.natDegree ≤ 2 * n + 1 →
      momentFunctional (s y) q = ∑ i, w i y * q.eval (X0 i) := by
    intro q hq
    rw [hX0]
    exact hquad y q hq
  have hLXpp : momentFunctional (s y)
      (Polynomial.X * ((nodePoly X0) * (nodePoly X0).derivative))
      = ((n : ℝ) + 1) * momentFunctional (s y) ((nodePoly X0) ^ (2 : ℕ)) := by
    rw [momentFunctional_eq_quadSum_add_top hquadY _ hdegXpp, htop]
    have hz : ∀ i : Fin (n + 1),
        w i y * (Polynomial.X * ((nodePoly X0) * (nodePoly X0).derivative)).eval (X0 i) = 0 := by
      intro i
      have hpz : (nodePoly X0).eval (X0 i) = 0 := eval_nodePoly X0 i
      simp only [Polynomial.eval_mul, hpz]
      ring
    rw [Finset.sum_congr rfl fun i _ => hz i, Finset.sum_const_zero, zero_add]
  have hval : momentFunctional (s y) (momentFlowPoly (reciprocalNodeTest X0))
      = -(2 * (((nodePoly X0).eval 0) ^ (2 : ℕ))⁻¹) *
        (((n : ℝ) + 1) * momentFunctional (s y) ((nodePoly X0) ^ (2 : ℕ))) := by
    rw [hflow, ← Polynomial.smul_eq_C_mul, momentFunctional_smul, hLXpp]
  rw [hval] at hmaster
  have hgoal : (2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
      / ((nodePoly (fun j => x j y)).eval 0) ^ (2 : ℕ)
      = ∑ i : Fin (n + 1), (w' i * x i y - w i y * x' i) / (x i y) ^ (2 : ℕ) := by
    rw [hmaster, ← hX0]
    field_simp
  rw [hgoal]
  exact hsum0

/-! ## The hard node coordinate and the iterated moment jets -/

set_option maxHeartbeats 2000000 in
/-- **(GJRS.11) The hard node coordinate moves strictly right.**  `u_i = 1/x_i - y` has velocity
`2N·L(p²)/(x_i²·γ_i)`. -/
theorem hasDerivAt_hardNodeCoordinate {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (i₀ : Fin (n + 1)) (hsep : nodeSeparation (fun j => x j y) i₀ ≠ 0)
    (hw0 : w i₀ y ≠ 0) (hx0 : x i₀ y ≠ 0) :
    HasDerivAt (fun t => (x i₀ t)⁻¹ - t)
      ((2 * (n : ℝ) + 2) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ))
          / ((x i₀ y) ^ (2 : ℕ) * nodeEnergy (fun j => x j y) (fun j => w j y) i₀)) y := by
  have h := hasDerivAt_hardCoordinate hs hx hw hquad i₀ hsep hw0 hx0
  have hn := h.neg
  rw [neg_neg] at hn
  refine hn.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.neg_apply]
  ring

/-- **The iterated moment jets.**  The shifted moment ODE integrates to
`s^{(r)}(k) = (-1)^r (k+1)(k+2)…(k+r) s(k+r)`. -/
theorem iteratedDeriv_moment {s : ℝ → ℕ → ℝ}
    (hs : ∀ (t : ℝ) (k : ℕ), HasDerivAt (fun u => s u k) (-(((k : ℝ) + 1) * s t (k + 1))) t)
    (r k : ℕ) :
    iteratedDeriv r (fun t => s t k)
      = fun y => (-1) ^ r * (∏ i ∈ Finset.range r, ((k : ℝ) + 1 + i)) * s y (k + r) := by
  induction r with
  | zero =>
      funext y
      simp
  | succ r ih =>
      funext y
      rw [iteratedDeriv_succ, ih]
      have hderiv : HasDerivAt
          (fun z => (-1 : ℝ) ^ r * (∏ i ∈ Finset.range r, ((k : ℝ) + 1 + i)) * s z (k + r))
          ((-1 : ℝ) ^ r * (∏ i ∈ Finset.range r, ((k : ℝ) + 1 + i)) *
            (-((((k + r : ℕ) : ℝ) + 1) * s y (k + r + 1)))) y :=
        HasDerivAt.const_mul ((-1 : ℝ) ^ r * (∏ i ∈ Finset.range r, ((k : ℝ) + 1 + i)))
          (hs y (k + r))
      rw [hderiv.deriv]
      have hprod : (∏ i ∈ Finset.range (r + 1), ((k : ℝ) + 1 + i))
          = (∏ i ∈ Finset.range r, ((k : ℝ) + 1 + i)) * ((k : ℝ) + 1 + r) := by
        rw [Finset.prod_range_succ]
      have hidx : k + (r + 1) = k + r + 1 := by omega
      rw [hprod, hidx]
      push_cast
      ring

/-! ## Flat faces -/

/-- **(GJRS.19) at order one.**  At a flat face the top-moment defect vanishes, so every hard node
coordinate is stationary. -/
theorem hasDerivAt_hardNodeCoordinate_flat {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (i₀ : Fin (n + 1)) (hsep : nodeSeparation (fun j => x j y) i₀ ≠ 0)
    (hw0 : w i₀ y ≠ 0) (hx0 : x i₀ y ≠ 0)
    (hflat : momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ)) = 0) :
    HasDerivAt (fun t => (x i₀ t)⁻¹ - t) 0 y := by
  have h := hasDerivAt_hardNodeCoordinate hs hx hw hquad i₀ hsep hw0 hx0
  rw [hflat] at h
  simpa using h

set_option maxHeartbeats 2000000 in
/-- **(GJRS.16) The first jet of the top quadrature moment at a flat face.**  With the defect
absent, the quadrature moment of order `2N` moves exactly as the atomic Möbius flow. -/
theorem hasDerivAt_topQuadratureMoment_flat {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hsep : ∀ i, nodeSeparation (fun j => x j y) i ≠ 0)
    (hdist : ∀ i : Fin (n + 1), ∀ k ∈ Finset.univ.erase i, x i y - x k y ≠ 0)
    (hflat : momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ)) = 0) :
    HasDerivAt (fun t => ∑ i, w i t * (x i t) ^ (2 * n + 2))
      (-(2 * (n : ℝ) + 3) * ∑ i, w i y * (x i y) ^ (2 * n + 3)) y := by
  have hterm : ∀ i : Fin (n + 1),
      HasDerivAt (fun t => w i t * (x i t) ^ (2 * n + 2))
        (w' i * (x i y) ^ (2 * n + 2)
          + w i y * (((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 1) * x' i)) y := by
    intro i
    have hpow : HasDerivAt (fun t => (x i t) ^ (2 * n + 2))
        (((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 2 - 1) * x' i) y := (hx i).pow _
    have hpow' : HasDerivAt (fun t => (x i t) ^ (2 * n + 2))
        (((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 1) * x' i) y := by
      have hidx : 2 * n + 2 - 1 = 2 * n + 1 := by omega
      rwa [hidx] at hpow
    exact (hw i).mul hpow'
  have hsum0 : HasDerivAt (∑ i : Fin (n + 1), fun t : ℝ => w i t * (x i t) ^ (2 * n + 2))
      (∑ i : Fin (n + 1), (w' i * (x i y) ^ (2 * n + 2)
        + w i y * (((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 1) * x' i))) y := by
    refine HasDerivAt.sum (A := fun i t => w i t * (x i t) ^ (2 * n + 2))
      (A' := fun i => w' i * (x i y) ^ (2 * n + 2)
        + w i y * (((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 1) * x' i)) fun i _ => hterm i
  have hfun : (∑ i : Fin (n + 1), fun t : ℝ => w i t * (x i t) ^ (2 * n + 2))
      = fun t : ℝ => ∑ i : Fin (n + 1), w i t * (x i t) ^ (2 * n + 2) := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at hsum0
  have hval : ∀ i : Fin (n + 1),
      w' i * (x i y) ^ (2 * n + 2)
        + w i y * (((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 1) * x' i)
        = -(2 * (n : ℝ) + 3) * (w i y * (x i y) ^ (2 * n + 3)) := by
    intro i
    have hwv := weightVelocity hs hx hw hquad i (hsep i) (hdist i)
    have hxv := weight_mul_nodeVelocity hs hx hw hquad i (hsep i)
    rw [hflat] at hwv hxv
    simp only [mul_zero, zero_div, add_zero] at hwv hxv
    have hrw : w i y * (((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 1) * x' i)
        = ((2 * n + 2 : ℕ) : ℝ) * (x i y) ^ (2 * n + 1) * (w i y * x' i) := by ring
    rw [hwv, hrw, hxv]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => hval i, ← Finset.mul_sum] at hsum0
  exact hsum0

/-- **(GJRS.16) The defect ladder at a flat face.**  The top-moment defect moves with rate
`-(2N+1)` times the next defect. -/
theorem hasDerivAt_topDefect_flat {s : ℝ → ℕ → ℝ} {y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hsep : ∀ i, nodeSeparation (fun j => x j y) i ≠ 0)
    (hdist : ∀ i : Fin (n + 1), ∀ k ∈ Finset.univ.erase i, x i y - x k y ≠ 0)
    (hflat : momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ (2 : ℕ)) = 0) :
    HasDerivAt (fun t => s t (2 * n + 2) - ∑ i, w i t * (x i t) ^ (2 * n + 2))
      (-(2 * (n : ℝ) + 3) * (s y (2 * n + 3) - ∑ i, w i y * (x i y) ^ (2 * n + 3))) y := by
  have hquadDeriv := hasDerivAt_topQuadratureMoment_flat hs hx hw hquad hsep hdist hflat
  have hsderiv : HasDerivAt (fun t => s t (2 * n + 2))
      (-((2 * (n : ℝ) + 3) * s y (2 * n + 3))) y := by
    have h := hs (2 * n + 2)
    have hcast : (((2 * n + 2 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) + 3 := by push_cast; ring
    rw [hcast] at h
    have hidx : 2 * n + 2 + 1 = 2 * n + 3 := by omega
    rwa [hidx] at h
  have hsub := hsderiv.sub hquadDeriv
  have hval : -((2 * (n : ℝ) + 3) * s y (2 * n + 3))
      - -(2 * (n : ℝ) + 3) * ∑ i, w i y * (x i y) ^ (2 * n + 3)
      = -(2 * (n : ℝ) + 3) * (s y (2 * n + 3) - ∑ i, w i y * (x i y) ^ (2 * n + 3)) := by
    ring
  rwa [hval] at hsub

/-! ## The hard-edge normalization -/

/-- **(GJRS.25)-(GJRS.26) The derivative of the hard-edge normalized polynomial at a root.**
`S(u) = (1 + u/y₀)^n p(1/(y₀+u))` has `S'(u_i) = -(1+u_i/y₀)^n x_i² p'(x_i)` at a root. -/
theorem hasDerivAt_hardEdgeNormalization_root (y₀ : ℝ) (hy₀ : y₀ ≠ 0) (nn : ℕ)
    (p : Polynomial ℝ) (u : ℝ) (hu : y₀ + u ≠ 0)
    (hroot : p.eval ((y₀ + u)⁻¹) = 0) :
    HasDerivAt (fun v => (1 + v / y₀) ^ nn * p.eval ((y₀ + v)⁻¹))
      (-((1 + u / y₀) ^ nn * ((y₀ + u)⁻¹) ^ (2 : ℕ) * p.derivative.eval ((y₀ + u)⁻¹))) u := by
  have hlin : HasDerivAt (fun v : ℝ => 1 + v / y₀) (1 / y₀) u := by
    have h : HasDerivAt (fun v : ℝ => v / y₀) (1 / y₀) u := by
      simpa using (hasDerivAt_id u).div_const y₀
    simpa using h.const_add (1 : ℝ)
  have hpow : HasDerivAt (fun v : ℝ => (1 + v / y₀) ^ nn)
      ((nn : ℝ) * (1 + u / y₀) ^ (nn - 1) * (1 / y₀)) u := hlin.pow nn
  have hinv : HasDerivAt (fun v : ℝ => (y₀ + v)⁻¹) (-1 / (y₀ + u) ^ (2 : ℕ)) u := by
    have hbase : HasDerivAt (fun v : ℝ => y₀ + v) 1 u := by
      simpa using (hasDerivAt_id u).const_add y₀
    exact hbase.inv hu
  have hp : HasDerivAt (fun v : ℝ => p.eval ((y₀ + v)⁻¹))
      (p.derivative.eval ((y₀ + u)⁻¹) * (-1 / (y₀ + u) ^ (2 : ℕ))) u := by
    have h2 : HasDerivAt (fun x : ℝ => p.eval x) (p.derivative.eval ((y₀ + u)⁻¹))
        ((y₀ + u)⁻¹) := Polynomial.hasDerivAt p ((y₀ + u)⁻¹)
    exact h2.comp u hinv
  have hmul := hpow.mul hp
  have hval : (nn : ℝ) * (1 + u / y₀) ^ (nn - 1) * (1 / y₀) * p.eval ((y₀ + u)⁻¹)
      + (1 + u / y₀) ^ nn * (p.derivative.eval ((y₀ + u)⁻¹) * (-1 / (y₀ + u) ^ (2 : ℕ)))
      = -((1 + u / y₀) ^ nn * ((y₀ + u)⁻¹) ^ (2 : ℕ) * p.derivative.eval ((y₀ + u)⁻¹)) := by
    rw [hroot, mul_zero, zero_add, inv_pow]
    field_simp
  rwa [hval] at hmul

/-- **(GJRS.29) The scale-invariant residue law.**  The Padé residue `ω/x` is the hard-edge energy
`y₀ x⁴ γ` divided by `t^{2n+1} S'(u)²`. -/
theorem gaussNodeResidue_law (y₀ x ω pd : ℝ) (ht : y₀ * x ≠ 0) (hx : x ≠ 0) (hpd : pd ≠ 0)
    (nn : ℕ) :
    (y₀ * x ^ (4 : ℕ) * (ω * pd ^ (2 : ℕ)))
      / ((y₀ * x) ^ (2 * nn + 1) * (-(((y₀ * x) ^ nn)⁻¹ * x ^ (2 : ℕ) * pd)) ^ (2 : ℕ))
      = ω / x := by
  have hy₀ : y₀ ≠ 0 := by
    intro h
    exact ht (by rw [h]; ring)
  have htn : ((y₀ * x) ^ nn) ≠ 0 := pow_ne_zero _ ht
  have hsplit : (y₀ * x) ^ (2 * nn + 1) = ((y₀ * x) ^ nn) ^ (2 : ℕ) * (y₀ * x) := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  rw [hsplit]
  field_simp

end HTGeometry

end
