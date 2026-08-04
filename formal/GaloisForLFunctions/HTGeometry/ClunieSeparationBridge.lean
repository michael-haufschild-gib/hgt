import GaloisForLFunctions.HTGeometry.MonomialIndependence

/-!
# From a quantitative separated point to the Clunie separation hypothesis

The Clunie induction consumes `SeparatesLast`, an existential over points at which the dependent
state outgrows a weight built from three blocks: the coefficients, the earlier states, and the
reciprocal of the top grouped coefficient.  Each block is bounded by data that the geometric
machinery produces directly — a floor for the grouped coefficient, uniform bounds on the coefficients
and earlier states, and a growth bound for the dependent state.

This file performs that translation, so that `SeparatesLast` reduces to a purely numeric
point-existence statement with no reference to `clunieWeight`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {k : ℕ}

/-- A floor on a nonzero quantity bounds the positive logarithm of its reciprocal. -/
theorem posLog_inv_le_of_floor {c : ℝ} {x : ℂ} (hc : 0 < c) (hx : c ≤ ‖x‖) :
    Real.posLog (1 / ‖x‖) ≤ Real.posLog (1 / c) := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le hc hx
  have hle : 1 / ‖x‖ ≤ 1 / c := one_div_le_one_div_of_le hc hx
  exact Real.posLog_le_posLog (by positivity) hle

/-- **The Clunie weight, bounded by explicit data.**  A bound `W` on the coefficient-and-earlier-state
block and a floor `c` for the top grouped coefficient bound the whole weight. -/
theorem clunieWeight_le {S : Finset (Fin (k + 1) → ℕ)} {A : (Fin (k + 1) → ℕ) → ℂ}
    {x : Fin (k + 1) → ℂ} {N : ℕ} {W c : ℝ}
    (hW : ∑ e ∈ S, (Real.posLog ‖A e‖
        + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖) ≤ W)
    (hc : 0 < c) (hfloor : c ≤ ‖groupedCoeff S A x N‖) :
    clunieWeight S A x N
      ≤ W + (N : ℝ) * Real.posLog (1 / c)
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 := by
  have h := posLog_inv_le_of_floor hc hfloor
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left h hN0
  rw [clunieWeight]
  linarith

/-- A separated point, from a floor for the top grouped coefficient and a growth bound. -/
theorem clunieWeight_lt_of_floor {S : Finset (Fin (k + 1) → ℕ)} {A : (Fin (k + 1) → ℕ) → ℂ}
    {x : Fin (k + 1) → ℂ} {N : ℕ} {W c : ℝ}
    (hW : ∑ e ∈ S, (Real.posLog ‖A e‖
        + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖) ≤ W)
    (hc : 0 < c) (hfloor : c ≤ ‖groupedCoeff S A x N‖)
    (hbig : W + (N : ℝ) * Real.posLog (1 / c)
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
        < Real.posLog ‖x (Fin.last k)‖) :
    clunieWeight S A x N < Real.posLog ‖x (Fin.last k)‖ :=
  lt_of_le_of_lt (clunieWeight_le hW hc hfloor) hbig

/-- **The coefficient-and-earlier-state block, bounded uniformly.**  With `a` bounding the
coefficients, `b` bounding the earlier states and `D` bounding the total earlier degree, the block is
at most `|S| · (a + D · b)`. -/
theorem clunie_block_le {S : Finset (Fin (k + 1) → ℕ)} {A : (Fin (k + 1) → ℕ) → ℂ}
    {x : Fin (k + 1) → ℂ} {a b D : ℝ}
    (hA : ∀ e ∈ S, Real.posLog ‖A e‖ ≤ a)
    (hx : ∀ i ∈ Finset.univ.erase (Fin.last k), Real.posLog ‖x i‖ ≤ b) (hb : 0 ≤ b)
    (hD : ∀ e ∈ S, ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) ≤ D) :
    ∑ e ∈ S, (Real.posLog ‖A e‖
        + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖)
      ≤ (S.card : ℝ) * (a + D * b) := by
  classical
  have hterm : ∀ e ∈ S, (Real.posLog ‖A e‖
      + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖)
      ≤ a + D * b := by
    intro e he
    have hinner : ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖
        ≤ ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * b := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i hi) (Nat.cast_nonneg _)
    have hsum : ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * b
        = (∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ)) * b := by
      rw [Finset.sum_mul]
    have hDb : (∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ)) * b ≤ D * b :=
      mul_le_mul_of_nonneg_right (hD e he) hb
    linarith [hA e he, hinner, hsum.le, hsum.ge, hDb]
  calc ∑ e ∈ S, (Real.posLog ‖A e‖
        + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖)
      ≤ ∑ _e ∈ S, (a + D * b) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (a + D * b) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **`SeparatesLast` from a numeric point-existence statement.**  All reference to `clunieWeight`
is discharged: what has to be produced is a point carrying a floor for the top grouped coefficient, a
bound for the coefficient-and-earlier-state block, and the resulting strict inequality. -/
theorem separatesLast_of_pointwise {F : Fin (k + 1) → ℂ → ℂ}
    (h : ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
      1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
      ∃ (z : ℂ) (W c : ℝ), 0 < c ∧
        c ≤ ‖groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N‖ ∧
        (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖)) ≤ W ∧
        W + (N : ℝ) * Real.posLog (1 / c)
          + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2
          < Real.posLog ‖F (Fin.last k) z‖) :
    SeparatesLast F := by
  intro S A N hN1 hN hex
  obtain ⟨z, W, c, hc, hfloor, hW, hbig⟩ := h S A N hN1 hN hex
  refine ⟨z, ?_, ?_⟩
  · intro hcon
    rw [hcon] at hfloor
    simp only [norm_zero] at hfloor
    linarith
  · exact clunieWeight_lt_of_floor hW hc hfloor hbig

/-! ## The grouped coefficient as an analytic function -/

/-- The top grouped coefficient of a monomial relation, as a function of the point. -/
noncomputable def groupedCoeffFun (S : Finset (Fin (k + 1) → ℕ))
    (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (F : Fin (k + 1) → ℂ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N

theorem groupedCoeffFun_apply (S : Finset (Fin (k + 1) → ℕ))
    (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (F : Fin (k + 1) → ℂ → ℂ) (N : ℕ) (z : ℂ) :
    groupedCoeffFun S A F N z
      = groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N := rfl

/-- The grouped coefficient is analytic wherever all the states are. -/
theorem analyticOnNhd_groupedCoeffFun {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → Polynomial ℂ} {F : Fin (k + 1) → ℂ → ℂ} {N : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ∀ i, AnalyticOnNhd ℂ (F i) U) :
    AnalyticOnNhd ℂ (groupedCoeffFun S A F N) U := by
  classical
  have hpoly : ∀ e : (Fin (k + 1) → ℕ), AnalyticOnNhd ℂ (fun z => (A e).eval z) U :=
    fun e => ((A e).differentiable.differentiableOn).analyticOnNhd hU
  refine Finset.analyticOnNhd_fun_sum _ ?_
  intro e _
  refine AnalyticOnNhd.mul (hpoly e) ?_
  refine Finset.analyticOnNhd_fun_prod _ ?_
  intro i _
  exact fun z hz => (hF i z hz).pow (e i)

/-- **The grouped coefficient vanishes nowhere locally once it is nonzero somewhere.**  The plane is
connected, so an analytic function vanishing on a neighbourhood vanishes identically. -/
theorem not_eventually_zero_groupedCoeffFun {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → Polynomial ℂ} {F : Fin (k + 1) → ℂ → ℂ} {N : ℕ}
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) Set.univ)
    (hex : ∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) :
    ∀ a ∈ (Set.univ : Set ℂ), ¬ ∀ᶠ z in nhds a, groupedCoeffFun S A F N z = 0 := by
  obtain ⟨w, hw⟩ := hex
  intro a _ hcon
  have han : AnalyticOnNhd ℂ (groupedCoeffFun S A F N) Set.univ :=
    analyticOnNhd_groupedCoeffFun isOpen_univ hF
  have hev : groupedCoeffFun S A F N =ᶠ[nhds a] 0 := by
    filter_upwards [hcon] with z hz
    exact hz
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_univ) (Set.mem_univ a) hev
  exact hw (this (Set.mem_univ w))

/-- The coefficient-and-earlier-state block at a point of the disc, from bounds valid on the disc. -/
theorem clunie_block_le_of_sup {S : Finset (Fin (k + 1) → ℕ)}
    {A : (Fin (k + 1) → ℕ) → Polynomial ℂ} {F : Fin (k + 1) → ℂ → ℂ} {z : ℂ} {B a b D : ℝ}
    (hz : ‖z‖ ≤ B)
    (hA : ∀ e ∈ S, ∀ w : ℂ, ‖w‖ ≤ B → Real.posLog ‖(A e).eval w‖ ≤ a)
    (hF : ∀ i ∈ Finset.univ.erase (Fin.last k), ∀ w : ℂ, ‖w‖ ≤ B → Real.posLog ‖F i w‖ ≤ b)
    (hb : 0 ≤ b)
    (hD : ∀ e ∈ S, ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) ≤ D) :
    ∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
        + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖)
      ≤ (S.card : ℝ) * (a + D * b) :=
  clunie_block_le (fun e he => hA e he z hz) (fun i hi => hF i hi z hz) hb hD

/-! ## From a modulus bound to the separation inequality

The growth chain delivers `exp B · C ≤ ‖F_last z‖`.  The Clunie separation needs
`weight < log⁺‖F_last z‖`.  These meet through the logarithm: it suffices that the weight be below
`B + log C`, and `B` is the quantity the composition growth makes large. -/

/-- **The separation inequality from a modulus bound.** -/
theorem lt_posLog_of_exp_mul_le {x W B C : ℝ} (hC : 0 < C)
    (hB : Real.exp B * C ≤ x) (hlt : W < B + Real.log C) :
    W < Real.posLog x := by
  have hpos : 0 < Real.exp B * C := by positivity
  have hlog : B + Real.log C ≤ Real.log x := by
    have h := Real.log_le_log hpos hB
    rwa [Real.log_mul (ne_of_gt (Real.exp_pos B)) (ne_of_gt hC), Real.log_exp] at h
  have hle : Real.log x ≤ Real.posLog x := le_max_right _ _
  linarith

/-- **The separation inequality, in the form the point selection produces.**  The floor `c₀` for the
top grouped coefficient and the modulus bound for the dependent state combine into the hypothesis of
`separatesLast_of_pointwise`. -/
theorem clunieWeight_lt_of_exp_mul_le {S : Finset (Fin (k + 1) → ℕ)} {A : (Fin (k + 1) → ℕ) → ℂ}
    {x : Fin (k + 1) → ℂ} {N : ℕ} {W c₀ B C : ℝ}
    (hW : ∑ e ∈ S, (Real.posLog ‖A e‖
        + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖x i‖) ≤ W)
    (hc₀ : 0 < c₀) (hfloor : c₀ ≤ ‖groupedCoeff S A x N‖)
    (hC : 0 < C) (hB : Real.exp B * C ≤ ‖x (Fin.last k)‖)
    (hlt : W + (N : ℝ) * Real.posLog (1 / c₀)
        + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 < B + Real.log C) :
    clunieWeight S A x N < Real.posLog ‖x (Fin.last k)‖ :=
  clunieWeight_lt_of_floor hW hc₀ hfloor (lt_posLog_of_exp_mul_le hC hB hlt)

/-! ## The Archimedean step

The second main theorem makes the growth quantity `B` linear in the number of values `p`, with a
positive slope, while the Clunie weight is fixed once the relation is fixed.  Choosing `p` large
enough therefore settles the separation. -/

/-- **A linear quantity with positive slope eventually beats any fixed bound.** -/
theorem exists_gt_of_linear {β γ W : ℝ} (hβ : 0 < β) : ∃ p : ℕ, W < (p : ℝ) * β - γ := by
  obtain ⟨p, hp⟩ := exists_nat_gt ((W + γ) / β)
  refine ⟨p, ?_⟩
  rw [lt_sub_iff_add_lt]
  rw [div_lt_iff₀ hβ] at hp
  linarith

/-- **The separation holds for a large enough number of values.**  With the growth quantity linear in
`p` and the weight fixed, the hypothesis of `clunieWeight_lt_of_exp_mul_le` is met for some `p`. -/
theorem exists_separation_index {β γ W c₀ C : ℝ} {N Scard : ℕ} (hβ : 0 < β) :
    ∃ p : ℕ, W + (N : ℝ) * Real.posLog (1 / c₀)
        + ((N : ℝ) * (Scard : ℝ) + (N : ℝ)) * Real.log 2
      < ((p : ℝ) * β - γ) + Real.log C := by
  obtain ⟨p, hp⟩ := exists_gt_of_linear (β := β) (γ := γ)
    (W := W + (N : ℝ) * Real.posLog (1 / c₀)
      + ((N : ℝ) * (Scard : ℝ) + (N : ℝ)) * Real.log 2 - Real.log C) hβ
  exact ⟨p, by linarith⟩

/-! ## The assembled separation criterion -/

/-- **`SeparatesLast` from a modulus bound.**  The form the growth chain produces: at a point of the
selected circle the top grouped coefficient has a floor `c₀`, the coefficient-and-earlier-state block
is bounded by `W`, and the dependent state satisfies a modulus bound `exp B · C ≤ ‖F_last z‖` whose
exponent beats the weight.

All reference to `clunieWeight` and to `log⁺` is discharged; what a caller has to produce is a point
together with those four constants. -/
theorem separatesLast_of_modulus_bound {F : Fin (k + 1) → ℂ → ℂ}
    (h : ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
      1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
      ∃ (z : ℂ) (W c₀ C B : ℝ), 0 < c₀ ∧ 0 < C ∧
        c₀ ≤ ‖groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N‖ ∧
        (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖)) ≤ W ∧
        Real.exp B * C ≤ ‖F (Fin.last k) z‖ ∧
        W + (N : ℝ) * Real.posLog (1 / c₀)
          + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 < B + Real.log C) :
    SeparatesLast F := by
  intro S A N hN1 hN hex
  obtain ⟨z, W, c₀, C, B, hc₀, hC, hfloor, hW, hB, hlt⟩ := h S A N hN1 hN hex
  refine ⟨z, ?_, ?_⟩
  · intro hcon
    rw [hcon] at hfloor
    simp only [norm_zero] at hfloor
    linarith
  · exact clunieWeight_lt_of_exp_mul_le hW hc₀ hfloor hC hB hlt

/-- **Cascade independence from the modulus bound at every level.**  Feeding the assembled criterion
into the Clunie induction: if at each level the growth chain produces a separated point, the whole
family is polynomially independent.

This is the criterion the cascade theorem applies: `PolyIndependent` for the states is exactly the
statement that no nontrivial polynomial relation over `ℂ[z]` holds among them, which is what pins the
differential order of the composition. -/
theorem polyIndependent_of_modulus_bound {n : ℕ} (F : Fin n → ℂ → ℂ)
    (h : ∀ (m : ℕ) (hm : m + 1 ≤ n),
      ∀ (S : Finset (Fin (m + 1) → ℕ)) (A : (Fin (m + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
        1 ≤ N → (∀ e ∈ S, e (Fin.last m) ≤ N) →
        (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w)
          (fun i => F (Fin.castLE hm i) w) N ≠ 0) →
        ∃ (z : ℂ) (W c₀ C B : ℝ), 0 < c₀ ∧ 0 < C ∧
          c₀ ≤ ‖groupedCoeff S (fun e => (A e).eval z)
            (fun i => F (Fin.castLE hm i) z) N‖ ∧
          (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
            + ∑ i ∈ Finset.univ.erase (Fin.last m), (e i : ℝ)
                * Real.posLog ‖F (Fin.castLE hm i) z‖)) ≤ W ∧
          Real.exp B * C ≤ ‖F (Fin.castLE hm (Fin.last m)) z‖ ∧
          W + (N : ℝ) * Real.posLog (1 / c₀)
            + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 < B + Real.log C) :
    PolyIndependent F :=
  polyIndependent_of_chain n F fun m hm => separatesLast_of_modulus_bound (h m hm)

/-! ## A shape-independent interface

The growth chain delivers a lower bound on `‖F_last z‖` whose exact shape varies — `exp B · C`, or
that minus the shift `‖a‖`.  Taking the lower bound as a single number `v` makes the separation
criterion independent of which. -/

/-- **The separation inequality from any positive lower bound.** -/
theorem lt_posLog_of_le {x W v : ℝ} (hv : 0 < v) (hvx : v ≤ x) (hlt : W < Real.log v) :
    W < Real.posLog x := by
  have hlog : Real.log v ≤ Real.log x := Real.log_le_log hv hvx
  have hle : Real.log x ≤ Real.posLog x := le_max_right _ _
  linarith

/-- **`SeparatesLast` from a value bound.**  The lower bound on the dependent state is a single
positive number `v`, whatever the growth chain's shape. -/
theorem separatesLast_of_value_bound {F : Fin (k + 1) → ℂ → ℂ}
    (h : ∀ (S : Finset (Fin (k + 1) → ℕ)) (A : (Fin (k + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
      1 ≤ N → (∀ e ∈ S, e (Fin.last k) ≤ N) →
      (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w) (fun i => F i w) N ≠ 0) →
      ∃ (z : ℂ) (W c₀ v : ℝ), 0 < c₀ ∧ 0 < v ∧
        c₀ ≤ ‖groupedCoeff S (fun e => (A e).eval z) (fun i => F i z) N‖ ∧
        (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
          + ∑ i ∈ Finset.univ.erase (Fin.last k), (e i : ℝ) * Real.posLog ‖F i z‖)) ≤ W ∧
        v ≤ ‖F (Fin.last k) z‖ ∧
        W + (N : ℝ) * Real.posLog (1 / c₀)
          + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 < Real.log v) :
    SeparatesLast F := by
  intro S A N hN1 hN hex
  obtain ⟨z, W, c₀, v, hc₀, hv, hfloor, hW, hvx, hlt⟩ := h S A N hN1 hN hex
  refine ⟨z, ?_, ?_⟩
  · intro hcon
    rw [hcon] at hfloor
    simp only [norm_zero] at hfloor
    linarith
  · exact clunieWeight_lt_of_floor hW hc₀ hfloor (lt_posLog_of_le hv hvx hlt)

/-- Cascade independence from the value-bound criterion. -/
theorem polyIndependent_of_value_bound {n : ℕ} (F : Fin n → ℂ → ℂ)
    (h : ∀ (m : ℕ) (hm : m + 1 ≤ n),
      ∀ (S : Finset (Fin (m + 1) → ℕ)) (A : (Fin (m + 1) → ℕ) → Polynomial ℂ) (N : ℕ),
        1 ≤ N → (∀ e ∈ S, e (Fin.last m) ≤ N) →
        (∃ w : ℂ, groupedCoeff S (fun e => (A e).eval w)
          (fun i => F (Fin.castLE hm i) w) N ≠ 0) →
        ∃ (z : ℂ) (W c₀ v : ℝ), 0 < c₀ ∧ 0 < v ∧
          c₀ ≤ ‖groupedCoeff S (fun e => (A e).eval z)
            (fun i => F (Fin.castLE hm i) z) N‖ ∧
          (∑ e ∈ S, (Real.posLog ‖(A e).eval z‖
            + ∑ i ∈ Finset.univ.erase (Fin.last m), (e i : ℝ)
                * Real.posLog ‖F (Fin.castLE hm i) z‖)) ≤ W ∧
          v ≤ ‖F (Fin.castLE hm (Fin.last m)) z‖ ∧
          W + (N : ℝ) * Real.posLog (1 / c₀)
            + ((N : ℝ) * (S.card : ℝ) + (N : ℝ)) * Real.log 2 < Real.log v) :
    PolyIndependent F :=
  polyIndependent_of_chain n F fun m hm => separatesLast_of_value_bound (h m hm)

end GaloisForLFunctions.HTGeometry
