import GaloisForLFunctions.HTGeometry.MovingGaussNodes

/-!
# The moving-center equation of a Gauss resolvent

The quadrature resolvent `R_y(Y) = ∑ w_i/(1 + (Y-y)x_i)` moves under the shifted moment flow.
Differentiating it at a fixed absolute centre `Y` against the Hermite interpolant of
`1/(1 + Δ X)` collapses every term except the top-moment defect: the whole `y`-derivative is
`-2N·L(p²)` times the top coefficient of that interpolant, and the top coefficient is
`-1/(Δ p(-1/Δ)²)`.  Since `∏(1 + Δ x_i) = (-Δ)^N p(-1/Δ)`, this is the one-monomial law

`∂_y R_y(Y) = 2N·L(p²)·(Y-y)^{2N-1} / (∏(1 + (Y-y)x_i))²`.
-/

open Polynomial

noncomputable section

namespace HTGeometry

variable {n : ℕ}

/-- The Hermite interpolant of `1/(1 + Δ X)` at the nodes. -/
def resolventTest (x : Fin (n + 1) → ℝ) (Δ : ℝ) : Polynomial ℝ :=
  Polynomial.C Δ⁻¹ *
    ((1 - Polynomial.C ((((nodePoly x).eval (-Δ⁻¹)) ^ 2)⁻¹) * (nodePoly x) ^ 2) /ₘ
      (Polynomial.X - Polynomial.C (-Δ⁻¹)))

theorem linear_mul_resolventTest (x : Fin (n + 1) → ℝ) {Δ : ℝ} (hΔ : Δ ≠ 0)
    (h0 : (nodePoly x).eval (-Δ⁻¹) ≠ 0) :
    (1 + Polynomial.C Δ * Polynomial.X) * resolventTest x Δ
      = 1 - Polynomial.C ((((nodePoly x).eval (-Δ⁻¹)) ^ 2)⁻¹) * (nodePoly x) ^ 2 := by
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ,
      q = 1 - Polynomial.C ((((nodePoly x).eval (-Δ⁻¹)) ^ 2)⁻¹) * (nodePoly x) ^ 2 := ⟨_, rfl⟩
  have hroot : q.IsRoot (-Δ⁻¹) := by
    rw [Polynomial.IsRoot, hq]
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow]
    rw [inv_mul_cancel₀ (pow_ne_zero 2 h0), sub_self]
  have hdvd : (Polynomial.X - Polynomial.C (-Δ⁻¹)) * (q /ₘ (Polynomial.X - Polynomial.C (-Δ⁻¹)))
      = q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hlin : (1 + Polynomial.C Δ * Polynomial.X)
      = Polynomial.C Δ * (Polynomial.X - Polynomial.C (-Δ⁻¹)) := by
    have hprod : Δ * -Δ⁻¹ = -1 := by field_simp
    rw [mul_sub, ← Polynomial.C_mul, hprod, Polynomial.C_neg, Polynomial.C_1, sub_neg_eq_add,
      add_comm]
  rw [resolventTest, ← hq, hlin]
  calc Polynomial.C Δ * (Polynomial.X - Polynomial.C (-Δ⁻¹)) *
      (Polynomial.C Δ⁻¹ * (q /ₘ (Polynomial.X - Polynomial.C (-Δ⁻¹))))
      = (Polynomial.C Δ * Polynomial.C Δ⁻¹) *
        ((Polynomial.X - Polynomial.C (-Δ⁻¹)) *
          (q /ₘ (Polynomial.X - Polynomial.C (-Δ⁻¹)))) := by ring
    _ = q := by
        rw [hdvd, ← Polynomial.C_mul, mul_inv_cancel₀ hΔ, Polynomial.C_1, one_mul]

theorem eval_resolventTest (x : Fin (n + 1) → ℝ) {Δ : ℝ} (hΔ : Δ ≠ 0)
    (h0 : (nodePoly x).eval (-Δ⁻¹) ≠ 0) (j : Fin (n + 1)) (hden : 1 + Δ * x j ≠ 0) :
    (resolventTest x Δ).eval (x j) = (1 + Δ * x j)⁻¹ := by
  have h := congrArg (Polynomial.eval (x j)) (linear_mul_resolventTest x hΔ h0)
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_pow, eval_nodePoly] at h
  field_simp at h ⊢
  linear_combination h

theorem eval_derivative_resolventTest (x : Fin (n + 1) → ℝ) {Δ : ℝ} (hΔ : Δ ≠ 0)
    (h0 : (nodePoly x).eval (-Δ⁻¹) ≠ 0) (j : Fin (n + 1)) (hden : 1 + Δ * x j ≠ 0) :
    (resolventTest x Δ).derivative.eval (x j) = -Δ / (1 + Δ * x j) ^ 2 := by
  have hder := congrArg Polynomial.derivative (linear_mul_resolventTest x hΔ h0)
  rw [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.derivative_C_mul, Polynomial.derivative_pow] at hder
  have h := congrArg (Polynomial.eval (x j)) hder
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_pow,
    eval_nodePoly] at h
  have hval := eval_resolventTest x hΔ h0 j hden
  rw [hval] at h
  field_simp at h ⊢
  linear_combination h

theorem natDegree_resolventTest_le (x : Fin (n + 1) → ℝ) (Δ : ℝ) :
    (resolventTest x Δ).natDegree ≤ 2 * n + 1 := by
  rw [resolventTest]
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C (-Δ⁻¹)),
    Polynomial.natDegree_X_sub_C]
  have hnum : (1 - Polynomial.C ((((nodePoly x).eval (-Δ⁻¹)) ^ 2)⁻¹) * (nodePoly x) ^ 2).natDegree
      ≤ 2 * n + 2 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    have h1 : (1 : Polynomial ℝ).natDegree = 0 := Polynomial.natDegree_one
    have h2 : (Polynomial.C ((((nodePoly x).eval (-Δ⁻¹)) ^ 2)⁻¹) * (nodePoly x) ^ 2).natDegree
        ≤ 2 * n + 2 := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_pow, natDegree_nodePoly]
      omega
    omega
  omega

theorem coeff_resolventTest_top (x : Fin (n + 1) → ℝ) {Δ : ℝ} (hΔ : Δ ≠ 0)
    (h0 : (nodePoly x).eval (-Δ⁻¹) ≠ 0) :
    Δ * (resolventTest x Δ).coeff (2 * n + 1)
      = -((((nodePoly x).eval (-Δ⁻¹)) ^ 2)⁻¹) := by
  have hdegg := natDegree_resolventTest_le x Δ
  have hzero : (resolventTest x Δ).coeff (2 * n + 2) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h := congrArg (fun P : Polynomial ℝ => P.coeff (2 * n + 2))
    (linear_mul_resolventTest x hΔ h0)
  simp only [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul] at h
  have hXg : (Polynomial.X * resolventTest x Δ).coeff (2 * n + 2)
      = (resolventTest x Δ).coeff (2 * n + 1) := by
    have hidx : 2 * n + 2 = (2 * n + 1) + 1 := by omega
    rw [hidx, Polynomial.coeff_X_mul]
  have hCX : (Polynomial.C Δ * Polynomial.X * resolventTest x Δ).coeff (2 * n + 2)
      = Δ * (resolventTest x Δ).coeff (2 * n + 1) := by
    rw [mul_assoc, Polynomial.coeff_C_mul, hXg]
  have hp2 : ((nodePoly x) ^ 2).coeff (2 * n + 2) = 1 := by
    have hm : (((nodePoly x) ^ 2)).Monic := (monic_nodePoly x).pow 2
    have hd : ((nodePoly x) ^ 2).natDegree = 2 * n + 2 := by
      rw [Polynomial.natDegree_pow, natDegree_nodePoly]
      ring
    have := hm.coeff_natDegree
    rwa [hd] at this
  have hone : (1 : Polynomial ℝ).coeff (2 * n + 2) = 0 := by
    rw [Polynomial.coeff_one]
    norm_num
  rw [hzero, hCX, hone, hp2, mul_one, zero_add] at h
  rw [h]
  ring

set_option maxHeartbeats 4000000 in
/-- **(MPW.5) The moving-centre equation.**  At a fixed absolute centre the quadrature resolvent
moves with the one-monomial rate `2N·L(p²)/(Δ·p(-1/Δ)²)`, `Δ = Y - y`. -/
theorem hasDerivAt_movingCenterResolvent {s : ℝ → ℕ → ℝ} {y Y : ℝ} {x w : Fin (n + 1) → ℝ → ℝ}
    {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hΔ : Y - y ≠ 0)
    (h0 : (nodePoly (fun j => x j y)).eval (-(Y - y)⁻¹) ≠ 0)
    (hden : ∀ i, 1 + (Y - y) * x i y ≠ 0) :
    HasDerivAt (fun t => ∑ i, w i t / (1 + (Y - t) * x i t))
      (2 * ((n : ℝ) + 1) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
        / ((Y - y) * ((nodePoly (fun j => x j y)).eval (-(Y - y)⁻¹)) ^ 2)) y := by
  classical
  obtain ⟨X0, hX0⟩ : ∃ X0 : Fin (n + 1) → ℝ, X0 = fun j => x j y := ⟨_, rfl⟩
  have h0' : (nodePoly X0).eval (-(Y - y)⁻¹) ≠ 0 := by rw [hX0]; exact h0
  obtain ⟨G, hG⟩ : ∃ G : Polynomial ℝ, G = resolventTest X0 (Y - y) := ⟨_, rfl⟩
  obtain ⟨hh, hhdef⟩ : ∃ hh : ℝ, hh = momentFunctional (s y) ((nodePoly X0) ^ 2) := ⟨_, rfl⟩
  obtain ⟨gt, hgt⟩ : ∃ gt : ℝ, gt = G.coeff (2 * n + 1) := ⟨_, rfl⟩
  have hGdeg : G.natDegree ≤ 2 * n + 1 := by
    rw [hG]; exact natDegree_resolventTest_le X0 (Y - y)
  have hgtop : (Y - y) * gt = -((((nodePoly X0).eval (-(Y - y)⁻¹)) ^ 2)⁻¹) := by
    rw [hgt, hG]; exact coeff_resolventTest_top X0 hΔ h0'
  have hGeval : ∀ j, G.eval (X0 j) = (1 + (Y - y) * X0 j)⁻¹ := by
    intro j
    rw [hG]
    refine eval_resolventTest X0 hΔ h0' j ?_
    rw [hX0]
    exact hden j
  have hGderiv : ∀ j, G.derivative.eval (X0 j) = -(Y - y) / (1 + (Y - y) * X0 j) ^ 2 := by
    intro j
    rw [hG]
    refine eval_derivative_resolventTest X0 hΔ h0' j ?_
    rw [hX0]
    exact hden j
  have hquadY : ∀ q : Polynomial ℝ, q.natDegree ≤ 2 * n + 1 →
      momentFunctional (s y) q = ∑ i, w i y * q.eval (X0 i) := by
    intro q hq
    rw [hX0]
    exact hquad y q hq
  have hmaster := moving_master (g := G) hs hx hw (fun t => hquad t G hGdeg)
  -- the derivative of the resolvent, term by term
  have hterm : ∀ i : Fin (n + 1),
      HasDerivAt (fun t => w i t / (1 + (Y - t) * x i t))
        ((w' i * (1 + (Y - y) * x i y)
            - w i y * (-x i y + (Y - y) * x' i)) / (1 + (Y - y) * x i y) ^ 2) y := by
    intro i
    have hd : HasDerivAt (fun t => 1 + (Y - t) * x i t) (-x i y + (Y - y) * x' i) y := by
      have h1 : HasDerivAt (fun t : ℝ => Y - t) (-1) y := by
        simpa using (hasDerivAt_id y).const_sub Y
      have h2 : HasDerivAt (fun t => (Y - t) * x i t)
          ((-1) * x i y + (Y - y) * x' i) y := h1.mul (hx i)
      have heq : (-1 : ℝ) * x i y + (Y - y) * x' i = -x i y + (Y - y) * x' i := by ring
      rw [heq] at h2
      exact h2.const_add (1 : ℝ)
    exact (hw i).div hd (hden i)
  have hsum0 : HasDerivAt (∑ i : Fin (n + 1), fun t : ℝ => w i t / (1 + (Y - t) * x i t))
      (∑ i : Fin (n + 1), (w' i * (1 + (Y - y) * x i y)
          - w i y * (-x i y + (Y - y) * x' i)) / (1 + (Y - y) * x i y) ^ 2) y := by
    refine HasDerivAt.sum (A := fun i t => w i t / (1 + (Y - t) * x i t))
      (A' := fun i => (w' i * (1 + (Y - y) * x i y)
        - w i y * (-x i y + (Y - y) * x' i)) / (1 + (Y - y) * x i y) ^ 2) fun i _ => ?_
    exact hterm i
  have hfun : (∑ i : Fin (n + 1), fun t : ℝ => w i t / (1 + (Y - t) * x i t))
      = fun t : ℝ => ∑ i : Fin (n + 1), w i t / (1 + (Y - t) * x i t) := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at hsum0
  -- rewrite the derivative sum as the master sum plus the centre-motion sum
  have hsplit : ∀ i : Fin (n + 1),
      (w' i * (1 + (Y - y) * x i y) - w i y * (-x i y + (Y - y) * x' i))
          / (1 + (Y - y) * x i y) ^ 2
        = (w' i * G.eval (x i y) + w i y * (G.derivative.eval (x i y) * x' i))
          + w i y * x i y / (1 + (Y - y) * x i y) ^ 2 := by
    intro i
    have hev : G.eval (x i y) = (1 + (Y - y) * x i y)⁻¹ := by
      rw [← congrFun hX0 i]; exact hGeval i
    have hdv : G.derivative.eval (x i y) = -(Y - y) / (1 + (Y - y) * x i y) ^ 2 := by
      rw [← congrFun hX0 i]; exact hGderiv i
    rw [hev, hdv]
    have hne := hden i
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, hmaster] at hsum0
  -- evaluate the dual flow
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
  have hval1 : momentFunctional (s y) (Polynomial.X * G)
      = (∑ i, w i y * X0 i / (1 + (Y - y) * X0 i)) + gt * hh := by
    rw [momentFunctional_eq_quadSum_add_top hquadY _ hdeg1]
    have hz : ∀ i : Fin (n + 1),
        w i y * (Polynomial.X * G).eval (X0 i) = w i y * X0 i / (1 + (Y - y) * X0 i) := by
      intro i
      rw [Polynomial.eval_mul, Polynomial.eval_X, hGeval i]
      field_simp
    rw [Finset.sum_congr rfl fun i _ => hz i, Polynomial.coeff_X_mul, ← hgt, hhdef]
  have hval2 : momentFunctional (s y) (Polynomial.X * (Polynomial.X * G.derivative))
      = (∑ i, w i y * X0 i ^ 2 * (-(Y - y) / (1 + (Y - y) * X0 i) ^ 2))
        + (2 * (n : ℝ) + 1) * (gt * hh) := by
    rw [momentFunctional_eq_quadSum_add_top hquadY _ hdeg2]
    have hz : ∀ i : Fin (n + 1),
        w i y * (Polynomial.X * (Polynomial.X * G.derivative)).eval (X0 i)
          = w i y * X0 i ^ 2 * (-(Y - y) / (1 + (Y - y) * X0 i) ^ 2) := by
      intro i
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, hGderiv i]
      ring
    rw [Finset.sum_congr rfl fun i _ => hz i, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul,
      Polynomial.coeff_derivative, ← hgt, hhdef]
    push_cast
    ring
  have hsumzero : (∑ i, w i y * X0 i / (1 + (Y - y) * X0 i))
      + (∑ i, w i y * X0 i ^ 2 * (-(Y - y) / (1 + (Y - y) * X0 i) ^ 2))
      = ∑ i, w i y * X0 i / (1 + (Y - y) * X0 i) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : 1 + (Y - y) * X0 i ≠ 0 := by rw [hX0]; exact hden i
    field_simp
    ring
  have hcancel : -(momentFunctional (s y) (momentFlowPoly G))
      + ∑ i : Fin (n + 1), w i y * x i y / (1 + (Y - y) * x i y) ^ 2
      = -((2 * (n : ℝ) + 2) * (gt * hh)) := by
    rw [hflow, momentFunctional_add, hval1, hval2]
    have hX : (∑ i : Fin (n + 1), w i y * x i y / (1 + (Y - y) * x i y) ^ 2)
        = ∑ i : Fin (n + 1), w i y * X0 i / (1 + (Y - y) * X0 i) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← congrFun hX0 i]
    rw [hX, ← hsumzero]
    ring
  rw [hcancel] at hsum0
  have hp02 : ((nodePoly X0).eval (-(Y - y)⁻¹)) ^ 2 ≠ 0 := pow_ne_zero 2 h0'
  have hgt' : gt = -((((nodePoly X0).eval (-(Y - y)⁻¹)) ^ 2)⁻¹) / (Y - y) := by
    rw [← hgtop]
    field_simp
  have hnp : (nodePoly (fun j => x j y)) = nodePoly X0 := by rw [hX0]
  have hfinal : -((2 * (n : ℝ) + 2) * (gt * hh))
      = 2 * ((n : ℝ) + 1) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
        / ((Y - y) * ((nodePoly (fun j => x j y)).eval (-(Y - y)⁻¹)) ^ 2) := by
    rw [hnp, ← hhdef, hgt']
    field_simp
  rw [hfinal] at hsum0
  exact hsum0

theorem pow_mul_eval_nodePoly_neg_inv (x : Fin (n + 1) → ℝ) {Δ : ℝ} (hΔ : Δ ≠ 0) :
    (-Δ) ^ (n + 1) * (nodePoly x).eval (-Δ⁻¹) = ∏ i, (1 + Δ * x i) := by
  rw [nodePoly, Polynomial.eval_prod]
  have hev : ∀ i : Fin (n + 1),
      (Polynomial.X - Polynomial.C (x i)).eval (-Δ⁻¹) = -Δ⁻¹ - x i := by
    intro i
    simp
  rw [Finset.prod_congr rfl fun i _ => hev i]
  have hcard : ((-Δ) ^ (n + 1) : ℝ) = ∏ _i : Fin (n + 1), (-Δ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hcard, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- **(MPW.5) in the Padé denominator form.**  `∂_y R_y(Y) = 2N·L(p²)·(Y-y)^{2N-1}/D_y(Y)²`. -/
theorem hasDerivAt_movingCenterResolvent_prod {s : ℝ → ℕ → ℝ} {y Y : ℝ}
    {x w : Fin (n + 1) → ℝ → ℝ} {x' w' : Fin (n + 1) → ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-(((k : ℝ) + 1) * s y (k + 1))) y)
    (hx : ∀ i, HasDerivAt (x i) (x' i) y) (hw : ∀ i, HasDerivAt (w i) (w' i) y)
    (hquad : ∀ t : ℝ, ∀ g : Polynomial ℝ, g.natDegree ≤ 2 * n + 1 →
      momentFunctional (s t) g = ∑ i, w i t * g.eval (x i t))
    (hΔ : Y - y ≠ 0)
    (h0 : (nodePoly (fun j => x j y)).eval (-(Y - y)⁻¹) ≠ 0)
    (hden : ∀ i, 1 + (Y - y) * x i y ≠ 0) :
    HasDerivAt (fun t => ∑ i, w i t / (1 + (Y - t) * x i t))
      (2 * ((n : ℝ) + 1) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
        * (Y - y) ^ (2 * n + 1) / (∏ i, (1 + (Y - y) * x i y)) ^ 2) y := by
  have hbase := hasDerivAt_movingCenterResolvent hs hx hw hquad hΔ h0 hden
  have hD := pow_mul_eval_nodePoly_neg_inv (fun j => x j y) hΔ
  have hDne : (∏ i, (1 + (Y - y) * x i y)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => hden i
  have hDsq : (∏ i, (1 + (Y - y) * x i y)) ^ 2
      = (Y - y) ^ (2 * n + 2) * ((nodePoly (fun j => x j y)).eval (-(Y - y)⁻¹)) ^ 2 := by
    rw [← hD, mul_pow, ← pow_mul]
    have hsign : ((-(Y - y)) ^ ((n + 1) * 2) : ℝ) = (Y - y) ^ (2 * n + 2) := by
      rw [neg_pow]
      have hpar : (-1 : ℝ) ^ ((n + 1) * 2) = 1 := by
        rw [mul_comm, pow_mul]
        norm_num
      rw [hpar, one_mul]
      congr 1
      ring
    rw [hsign]

  have hval : 2 * ((n : ℝ) + 1) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
      / ((Y - y) * ((nodePoly (fun j => x j y)).eval (-(Y - y)⁻¹)) ^ 2)
      = 2 * ((n : ℝ) + 1) * momentFunctional (s y) ((nodePoly (fun j => x j y)) ^ 2)
        * (Y - y) ^ (2 * n + 1) / (∏ i, (1 + (Y - y) * x i y)) ^ 2 := by
    rw [hDsq]
    have hp2 : ((nodePoly (fun j => x j y)).eval (-(Y - y)⁻¹)) ^ 2 ≠ 0 := pow_ne_zero 2 h0
    have hpow : (Y - y) ^ (2 * n + 2) = (Y - y) * (Y - y) ^ (2 * n + 1) := by
      rw [← pow_succ']
    rw [hpow]
    field_simp
  rw [← hval]
  exact hbase

end HTGeometry

end
