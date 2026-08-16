import GaloisForLFunctions.HTGeometry.GermPolynomialDivisibility

/-!
# Every distinguished polynomial is independent

The free-module independence proved for the Weierstrass polynomial of a regular germ holds for an
arbitrary distinguished polynomial: monic in the distinguished coordinate, with coefficients in the
parameter germ ring vanishing at the origin.

The proof is the same shrinking argument, with the root multiset of the Weierstrass polynomial
replaced by the root multiset of the moving polynomial itself — available because `ℂ` is
algebraically closed and the polynomial is monic — and with the a priori root bound supplied by the
Cauchy estimate instead of by the geometry of the preparation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Filter Topology Metric
open _root_.HTGeometry (multisetLinearProd)

variable {n : ℕ}

/-- The moving monic polynomial attached to a coefficient family. -/
noncomputable def movingPoly (d : ℕ) (a : ℕ → (Fin n → ℂ) → ℂ) (y : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ d + lowDegreePoly (fun j => a j y) d

theorem movingPoly_monic (d : ℕ) (a : ℕ → (Fin n → ℂ) → ℂ) (y : Fin n → ℂ) :
    (movingPoly d a y).Monic :=
  monic_X_pow_add (degree_lowDegreePoly_lt _ d)

theorem natDegree_movingPoly (d : ℕ) (a : ℕ → (Fin n → ℂ) → ℂ) (y : Fin n → ℂ) :
    (movingPoly d a y).natDegree = d := by
  have hdeg : (movingPoly d a y).degree = (d : ℕ) := by
    have h : (lowDegreePoly (fun j => a j y) d).degree
        < (Polynomial.X ^ d : Polynomial ℂ).degree := by
      rw [degree_X_pow]
      exact degree_lowDegreePoly_lt _ d
    rw [movingPoly, degree_add_eq_left_of_degree_lt h, degree_X_pow]
  exact natDegree_eq_of_degree_eq_some hdeg

theorem eval_movingPoly (d : ℕ) (a : ℕ → (Fin n → ℂ) → ℂ) (y : Fin n → ℂ) (z : ℂ) :
    (movingPoly d a y).eval z = z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j := by
  rw [movingPoly, eval_add, eval_pow, eval_X, eval_lowDegreePoly]

theorem card_roots_movingPoly (d : ℕ) (a : ℕ → (Fin n → ℂ) → ℂ) (y : Fin n → ℂ) :
    Multiset.card (movingPoly d a y).roots = d := by
  have hsplits : Multiset.card (movingPoly d a y).roots = (movingPoly d a y).natDegree :=
    (splits_iff_card_roots.mp (IsAlgClosed.splits _))
  rw [hsplits, natDegree_movingPoly]

theorem multisetLinearProd_roots_movingPoly (d : ℕ) (a : ℕ → (Fin n → ℂ) → ℂ) (y : Fin n → ℂ)
    (z : ℂ) :
    multisetLinearProd (movingPoly d a y).roots z
      = z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j := by
  rw [← eval_multisetProd_eq_multisetLinearProd,
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (movingPoly_monic d a y)
      (by rw [card_roots_movingPoly, natDegree_movingPoly]),
    eval_movingPoly]

/-- **Every distinguished polynomial has the free-module independence property.** -/
theorem germIndependent_of_distinguished {d : ℕ} (hd : 0 < d)
    {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → analyticGermValue (0 : Fin n → ℂ) (α j) = 0) :
    GermIndependent d α := by
  classical
  choose a haA haeq using fun j : ℕ => (α j).2
  have hαeq : ∀ j, α j = analyticGermOf (haA j) := fun j => Subtype.ext (haeq j).symm
  have hazero : ∀ j, j < d → a j (0 : Fin n → ℂ) = 0 := by
    intro j hj
    have := hzero j hj
    rw [hαeq j, analyticGermValue_of (haA j)] at this
    exact this
  intro q β hrel
  obtain ⟨Q, hQA, hQeq⟩ := q.2
  choose B hBA hBeq using fun j : ℕ => (β j).2
  have hqeq : q = analyticGermOf hQA := Subtype.ext hQeq.symm
  have hβeq : ∀ j, β j = analyticGermOf (hBA j) := fun j => Subtype.ext (hBeq j).symm
  -- the relation between functions, near the origin
  have hfun : ((fun w : Fin (n + 1) → ℂ =>
      Q w * ((w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j)
        + ∑ j ∈ Finset.range d, B j (Fin.tail w) * (w 0) ^ j) :
        (Fin (n + 1) → ℂ) → ℂ) =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0 := by
    have hcoerce := congrArg
      (fun x : AnalyticGerm (0 : Fin (n + 1) → ℂ) => (x : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)) hrel
    rw [Subring.coe_add, Subring.coe_mul, hqeq] at hcoerce
    simp only [hβeq, hαeq] at hcoerce
    rw [coe_germDistinguished haA, coe_germPolyTail hBA, ZeroMemClass.coe_zero] at hcoerce
    exact Germ.coe_eq.mp hcoerce
  obtain ⟨rE, hrE, hEspec⟩ := Metric.eventually_nhds_iff.mp hfun
  obtain ⟨rQ, hrQ, hQball⟩ := exists_ball_analyticOnNhd hQA
  set s : ℝ := min rQ rE with hs
  have hspos : 0 < s := lt_min hrQ hrE
  set t₁ : ℝ := s / 2 with ht₁
  have ht₁pos : 0 < t₁ := by positivity
  obtain ⟨δ₂, hδ₂, hδ₂spec⟩ :=
    exists_param_ball_roots_lt_monic (a := a) hd (fun j => (haA j).continuousAt) hazero ht₁pos
  set δ₁ : ℝ := min (s / 2) δ₂ with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min (by positivity) hδ₂
  have hsub : prepPolydisc (n := n) t₁ δ₁ ⊆ ball (0 : Fin (n + 1) → ℂ) (s / 2) :=
    prepPolydisc_subset_ball le_rfl (min_le_left _ _)
  have hsball : ∀ w ∈ prepPolydisc (n := n) t₁ δ₁, ‖w‖ < s / 2 := by
    intro w hw
    simpa [dist_zero_right] using mem_ball.mp (hsub hw)
  -- pointwise relation on the shrunken polydisc
  have hpt : ∀ y : Fin n → ℂ, ‖y‖ < δ₁ → ∀ z : ℂ, ‖z‖ < t₁ →
      Q (Fin.cons z y) * multisetLinearProd (movingPoly d a y).roots z
        + ∑ j ∈ Finset.range d, B j y * z ^ j = 0 := by
    intro y hy z hz
    have hmem : (Fin.cons z y : Fin (n + 1) → ℂ) ∈ prepPolydisc (n := n) t₁ δ₁ := by
      refine ⟨?_, ?_⟩
      · rw [Fin.tail_cons, mem_ball, dist_zero_right]
        exact hy
      · rw [Fin.cons_zero]
        exact hz
    have hdist : dist (Fin.cons z y : Fin (n + 1) → ℂ) 0 < rE := by
      rw [dist_zero_right]
      refine lt_of_lt_of_le (hsball _ hmem) ?_
      have : s ≤ rE := min_le_right _ _
      linarith
    have hval := hEspec hdist
    simp only [Pi.zero_apply, Fin.tail_cons, Fin.cons_zero] at hval
    rw [multisetLinearProd_roots_movingPoly]
    exact hval
  -- roots are small on the shrunken parameter ball
  have hsmall : ∀ y : Fin n → ℂ, ‖y‖ < δ₁ → ∀ ρ ∈ (movingPoly d a y).roots, ‖ρ‖ < t₁ := by
    intro y hy ρ hρ
    refine hδ₂spec y (lt_of_lt_of_le hy (min_le_right _ _)) ρ ?_
    have hev : (movingPoly d a y).eval ρ = 0 := by
      have hne : movingPoly d a y ≠ 0 := (movingPoly_monic d a y).ne_zero
      exact (mem_roots hne).mp hρ
    rw [eval_movingPoly] at hev
    exact hev
  -- apply the slice independence for each parameter
  have hkill : ∀ y : Fin n → ℂ, ‖y‖ < δ₁ →
      (∀ j, j < d → B j y = 0) ∧ ∀ z ∈ ball (0 : ℂ) t₁, Q (Fin.cons z y) = 0 := by
    intro y hy
    refine lowDegree_and_quotient_eq_zero (hsmall y hy) ?_ (card_roots_movingPoly d a y).symm ?_
    · intro z hz
      have hin : (Fin.cons z y : Fin (n + 1) → ℂ) ∈ prepPolydisc (n := n) t₁ δ₁ := by
        refine ⟨?_, ?_⟩
        · rw [Fin.tail_cons, mem_ball, dist_zero_right]
          exact hy
        · rw [Fin.cons_zero]
          simpa [dist_zero_right] using mem_ball.mp hz
      have hsQ : s / 2 ≤ rQ := by
        have hle : s ≤ rQ := min_le_left _ _
        linarith
      have hmem : (Fin.cons z y : Fin (n + 1) → ℂ) ∈ ball (0 : Fin (n + 1) → ℂ) rQ := by
        rw [mem_ball, dist_zero_right]
        have h2 := hsball _ hin
        linarith
      have hQc : ContinuousAt Q (Fin.cons z y) := (hQball _ hmem).continuousAt
      have hcc : ContinuousAt (fun w : ℂ => (Fin.cons w y : Fin (n + 1) → ℂ)) z :=
        (_root_.HTGeometry.differentiable_consFirst y z).continuousAt
      exact (ContinuousAt.comp (x := z) hQc hcc).continuousWithinAt
    · intro z hz
      exact hpt y hy z (by simpa [dist_zero_right] using mem_ball.mp hz)
  constructor
  · refine Subtype.ext ?_
    rw [hqeq, ZeroMemClass.coe_zero, analyticGermOf_val]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [(isOpen_prepPolydisc t₁ δ₁).mem_nhds (zero_mem_prepPolydisc ht₁pos hδ₁pos)]
      with w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hy : ‖Fin.tail w‖ < δ₁ := by simpa [dist_zero_right] using mem_ball.mp hw1
    have := (hkill (Fin.tail w) hy).2 (w 0) (by
      rw [mem_ball, dist_zero_right]
      exact hw2)
    rwa [Fin.cons_self_tail] at this
  · intro j hj
    refine Subtype.ext ?_
    rw [hβeq j, ZeroMemClass.coe_zero, analyticGermOf_val]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [ball_mem_nhds (0 : Fin n → ℂ) hδ₁pos] with y hy
    exact (hkill y (by simpa [dist_zero_right] using mem_ball.mp hy)).1 j hj

/-- **Uniqueness of the Weierstrass preparation.**  Two distinguished polynomials whose evaluations
differ by a unit are equal. -/
theorem distPoly_eq_of_unit_mul {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    {α₁ α₂ : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (h₁ : ∀ j, j < d₁ → analyticGermValue (0 : Fin n → ℂ) (α₁ j) = 0)
    (h₂ : ∀ j, j < d₂ → analyticGermValue (0 : Fin n → ℂ) (α₂ j) = 0)
    {v : AnalyticGerm (0 : Fin (n + 1) → ℂ)} (hv : IsUnit v)
    (h : germEval n (distPoly d₁ α₁) = germEval n (distPoly d₂ α₂) * v) :
    distPoly d₁ α₁ = distPoly d₂ α₂ := by
  obtain ⟨w, hw⟩ := hv
  have hdvd₁ : distPoly d₂ α₂ ∣ distPoly d₁ α₁ := by
    refine (dvd_germEval_iff (germIndependent_of_distinguished hd₂ h₂) _).mp ?_
    exact ⟨v, h⟩
  have hdvd₂ : distPoly d₁ α₁ ∣ distPoly d₂ α₂ := by
    refine (dvd_germEval_iff (germIndependent_of_distinguished hd₁ h₁) _).mp ?_
    refine ⟨(↑w⁻¹ : AnalyticGerm (0 : Fin (n + 1) → ℂ)), ?_⟩
    rw [h, mul_assoc, ← hw, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  exact eq_of_monic_of_associated (distPoly_monic d₁ α₁) (distPoly_monic d₂ α₂)
    (associated_of_dvd_dvd hdvd₂ hdvd₁)

end GaloisForLFunctions.HTGeometry
