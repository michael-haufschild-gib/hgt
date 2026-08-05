import Mathlib

/-!
# The parity vortex of the squarefree Gibbs gas

The multiplicative-energy lattice gas on a finite set `S` of integers `≥ 2` has diagonal
partition polynomial

  `P_S(z, x) = ∑_{T ⊆ S} z^{|T|}·exp(−x·∏_{p∈T} p)`,

the Laplace-weighted generating polynomial of `z^{ω(n)}` over the divisors built from `S`.
Its parity point `z = −1` carries the Möbius–Laplace current `∑_{n|∏S} μ(n)e^{−nx}`.

This file proves the structural laws of that parity point:

* `gibbsDiag_insert` — the **cutoff recursion**: adjoining an element couples the gas to
  itself at the dilated scale, `P_{S∪p}(z,x) = P_S(z,x) + z·P_S(z,px)`;
* `two_prime_real_rooted` — the two-element gas is Lee–Yang at every coupling `x > 0`
  (two distinct real roots), by AM–GM and `p + q < pq + 1`;
* `hasDerivAt_gibbsDiag_parity` — the **parity-jet law**: at `x = 0` the parity point is
  a `k`-fold root, and `∂ₓ|₀ P_S(−1+w, x) = −∏_{p∈S}(pw − (p−1))`, the resolvent
  polynomial of the vortex, with all roots real in `(0,1)`;
* `hasDerivAt_gibbs_current` — at `w = 0` the derivative of the current is
  `(−1)^{k+1}·∏_{p∈S}(p−1)`: **Euler's totient is the vortex intensity**.
-/

namespace RHTower.GibbsGas

open Real Filter

/-- The diagonal partition polynomial of the multiplicative-energy gas. -/
noncomputable def gibbsDiag (S : Finset ℕ) (x z : ℝ) : ℝ :=
  ∑ T ∈ S.powerset, z ^ T.card * Real.exp (-(x * ∏ p ∈ T, (p : ℝ)))

theorem gibbsDiag_empty (x z : ℝ) : gibbsDiag ∅ x z = Real.exp (-x) := by
  simp [gibbsDiag]

/-- **The cutoff recursion**: adjoining an element couples the gas to itself at the
dilated scale. -/
theorem gibbsDiag_insert (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x z : ℝ) :
    gibbsDiag (insert p S) x z
      = gibbsDiag S x z + z * gibbsDiag S ((p : ℝ) * x) z := by
  classical
  have hdisj : Disjoint S.powerset (S.powerset.image (insert p)) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    rw [Finset.mem_powerset] at hT
    obtain ⟨T', _, rfl⟩ := Finset.mem_image.mp hT'
    exact hp (hT (Finset.mem_insert_self p T'))
  have hinj : ∀ T₁ ∈ S.powerset, ∀ T₂ ∈ S.powerset,
      insert p T₁ = insert p T₂ → T₁ = T₂ := by
    intro T₁ h₁ T₂ h₂ h
    rw [Finset.mem_powerset] at h₁ h₂
    have e₁ : (insert p T₁).erase p = T₁ :=
      Finset.erase_insert (fun hmem => hp (h₁ hmem))
    have e₂ : (insert p T₂).erase p = T₂ :=
      Finset.erase_insert (fun hmem => hp (h₂ hmem))
    rw [← e₁, ← e₂, h]
  rw [gibbsDiag, Finset.powerset_insert, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  have hterm : ∀ T ∈ S.powerset,
      z ^ (insert p T).card * Real.exp (-(x * ∏ q ∈ insert p T, (q : ℝ)))
        = z * (z ^ T.card * Real.exp (-((p : ℝ) * x * ∏ q ∈ T, (q : ℝ)))) := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hpT : p ∉ T := fun hmem => hp (hT hmem)
    rw [Finset.card_insert_of_notMem hpT, Finset.prod_insert hpT, pow_succ]
    have harg : -(x * ((p : ℝ) * ∏ q ∈ T, (q : ℝ)))
        = -((p : ℝ) * x * ∏ q ∈ T, (q : ℝ)) := by ring
    rw [harg]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rfl

/-- At coupling zero the gas is free: the parity point is a `k`-fold zero. -/
theorem gibbsDiag_zero (S : Finset ℕ) (z : ℝ) :
    gibbsDiag S 0 z = (1 + z) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [gibbsDiag_empty]
  | insert p S hp ih =>
    rw [gibbsDiag_insert p S hp, mul_zero, ih,
      Finset.card_insert_of_notMem hp, pow_succ]
    ring

/-- Derivative of one Boltzmann factor at coupling zero. -/
theorem hasDerivAt_exp_neg_mul (c : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(x * c))) (-c) 0 := by
  have h1 : HasDerivAt (fun x : ℝ => x * c) c 0 := hasDerivAt_mul_const c
  have h : HasDerivAt (fun x : ℝ => -(x * c)) (-c) 0 := h1.neg
  have h2 := h.exp
  simpa using h2

/-- **The parity-jet law.**  The coupling-derivative of the gas at the shifted parity
point `z = −1 + w` is `−∏_{p∈S}(p·w − (p−1))`: the resolvent polynomial of the vortex,
with all roots real in `(0,1)` at `w = 1 − 1/p`. -/
theorem hasDerivAt_gibbsDiag_parity (S : Finset ℕ) (w : ℝ) :
    HasDerivAt (fun x => gibbsDiag S x (-1 + w))
      (-(∏ p ∈ S, ((p : ℝ) * w - ((p : ℝ) - 1)))) 0 := by
  classical
  have hterm : ∀ T ∈ S.powerset,
      HasDerivAt (fun x => (-1 + w) ^ T.card * Real.exp (-(x * ∏ p ∈ T, (p : ℝ))))
        ((-1 + w) ^ T.card * (-(∏ p ∈ T, (p : ℝ)))) 0 :=
    fun T _ => (hasDerivAt_exp_neg_mul _).const_mul _
  have hsum := HasDerivAt.sum hterm
  have hval : ∑ T ∈ S.powerset, (-1 + w) ^ T.card * (-(∏ p ∈ T, (p : ℝ)))
      = -(∏ p ∈ S, ((p : ℝ) * w - ((p : ℝ) - 1))) := by
    have h1 : ∀ T ∈ S.powerset, (-1 + w) ^ T.card * (-(∏ p ∈ T, (p : ℝ)))
        = -(∏ p ∈ T, ((w - 1) * (p : ℝ))) := by
      intro T _
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hw : (-1 + w : ℝ) = (w - 1) := by ring
      rw [hw]
      ring
    rw [Finset.sum_congr rfl h1]
    have h2 := Finset.prod_add (fun p : ℕ => (w - 1) * (p : ℝ))
      (fun _ : ℕ => (1 : ℝ)) S
    have h3 : ∀ p ∈ S, (p : ℝ) * w - ((p : ℝ) - 1) = (w - 1) * (p : ℝ) + 1 := by
      intro p _
      ring
    rw [Finset.prod_congr rfl h3, h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one]
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [gibbsDiag, Finset.sum_apply]

/-- **The totient is the vortex intensity**: the Möbius–Laplace current of the finite gas
has coupling-derivative `(−1)^{k+1}·∏_{p∈S}(p−1)` at zero. -/
theorem hasDerivAt_gibbs_current (S : Finset ℕ) :
    HasDerivAt (fun x => gibbsDiag S x (-1))
      ((-1) ^ (S.card + 1) * ∏ p ∈ S, ((p : ℝ) - 1)) 0 := by
  have h := hasDerivAt_gibbsDiag_parity S 0
  have hval : -(∏ p ∈ S, ((p : ℝ) * 0 - ((p : ℝ) - 1)))
      = (-1) ^ (S.card + 1) * ∏ p ∈ S, ((p : ℝ) - 1) := by
    have h1 : ∀ p ∈ S, (p : ℝ) * 0 - ((p : ℝ) - 1) = (-1) * ((p : ℝ) - 1) := by
      intro p _
      ring
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, pow_succ]
    ring
  rw [hval] at h
  simpa using h

theorem gibbsDiag_singleton (q : ℕ) (x z : ℝ) :
    gibbsDiag {q} x z = Real.exp (-x) + z * Real.exp (-((q : ℝ) * x)) := by
  have h : ({q} : Finset ℕ) = insert q ∅ := by simp
  rw [h, gibbsDiag_insert q ∅ (Finset.notMem_empty q), gibbsDiag_empty, gibbsDiag_empty]

/-- **Two-element Lee–Yang.**  For distinct `p, q ≥ 2` the quadratic gas has two distinct
real roots at every coupling `x > 0`: the parity point is stable at order two. -/
theorem two_prime_real_rooted (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : p ≠ q)
    (x : ℝ) (hx : 0 < x) :
    ∃ u v : ℝ, u ≠ v ∧ ∀ z : ℝ,
      gibbsDiag {p, q} x z
        = Real.exp (-((q : ℝ) * ((p : ℝ) * x))) * ((z - u) * (z - v)) := by
  classical
  have hpq' : p ∉ ({q} : Finset ℕ) := by simp [hpq]
  have hexp : ∀ z : ℝ, gibbsDiag {p, q} x z
      = Real.exp (-x) + (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x))) * z
        + Real.exp (-((q:ℝ)*((p:ℝ)*x))) * z^2 := by
    intro z
    rw [gibbsDiag_insert p {q} hpq', gibbsDiag_singleton, gibbsDiag_singleton]
    ring
  set A : ℝ := Real.exp (-((q:ℝ)*((p:ℝ)*x))) with hA
  set Bc : ℝ := Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) with hB
  set E0 : ℝ := Real.exp (-x) with hE0
  set D : ℝ := Bc^2 - 4 * (A * E0) with hD
  have hA0 : 0 < A := Real.exp_pos _
  have hAne : A ≠ 0 := ne_of_gt hA0
  have hDpos : 0 < D := by
    rw [hD, hB, hA, hE0]
    have hAM : (Real.exp (-((p:ℝ)*x)) - Real.exp (-((q:ℝ)*x)))^2 ≥ 0 := sq_nonneg _
    have hprod : Real.exp (-((p:ℝ)*x)) * Real.exp (-((q:ℝ)*x))
        = Real.exp (-(((p:ℝ)+(q:ℝ))*x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexparg : Real.exp (-((q:ℝ)*((p:ℝ)*x))) * Real.exp (-x)
        = Real.exp (-(((p:ℝ)*(q:ℝ)+1)*x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlt : Real.exp (-(((p:ℝ)*(q:ℝ)+1)*x)) < Real.exp (-(((p:ℝ)+(q:ℝ))*x)) := by
      apply Real.exp_lt_exp.mpr
      have hp' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      have hq' : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      have hpos := mul_pos (show (0:ℝ) < (p:ℝ)-1 by linarith)
        (show (0:ℝ) < (q:ℝ)-1 by linarith)
      nlinarith [hpos, hx]
    nlinarith [hAM, hprod, hexparg, hlt]
  set s : ℝ := Real.sqrt D with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hDpos
  have hs2 : s^2 = D := Real.sq_sqrt hDpos.le
  have h2A : (2*A) ≠ 0 := mul_ne_zero two_ne_zero hAne
  have hs2' : s^2 = Bc^2 - 4 * (A * E0) := by rw [hs2, hD]
  refine ⟨(-Bc + s) / (2*A), (-Bc - s) / (2*A), ?_, ?_⟩
  · intro hcon
    rw [div_eq_div_iff h2A h2A] at hcon
    have h4 : s * (4*A) = 0 := by linarith [hcon]
    rcases mul_eq_zero.mp h4 with h | h
    · exact (ne_of_gt hs0) h
    · exact absurd h (by positivity)
  · intro z
    rw [hexp z]
    field_simp
    linear_combination hs2'

/-- Vieta's formulas, extracted from a pointwise real factorization of a cubic. -/
theorem cubic_vieta (a3 a2 a1 a0 r₁ r₂ r₃ : ℝ)
    (h : ∀ w : ℝ, a3*w^3 + a2*w^2 + a1*w + a0
      = a3 * ((w - r₁) * ((w - r₂) * (w - r₃)))) :
    a2 = -(a3*(r₁+r₂+r₃)) ∧ a1 = a3*(r₁*r₂+r₁*r₃+r₂*r₃) ∧ a0 = -(a3*(r₁*r₂*r₃)) := by
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1/2 : ℝ) * h1 + (1/2 : ℝ) * hm - h0
  · linear_combination (1/2 : ℝ) * h1 - (1/2 : ℝ) * hm
  · linear_combination h0

/-- A real cubic with a real root factorization has nonnegative discriminant:
`Δ = a₃⁴·∏(rᵢ−rⱼ)²`. -/
theorem cubic_discrim_nonneg_of_real_rooted (a3 a2 a1 a0 r₁ r₂ r₃ : ℝ)
    (h : ∀ w : ℝ, a3*w^3 + a2*w^2 + a1*w + a0
      = a3 * ((w - r₁) * ((w - r₂) * (w - r₃)))) :
    0 ≤ 18 * a3 * a2 * a1 * a0 - 4 * a2^3 * a0 + a2^2 * a1^2
      - 4 * a3 * a1^3 - 27 * a3^2 * a0^2 := by
  obtain ⟨hb, hc, hd⟩ := cubic_vieta a3 a2 a1 a0 r₁ r₂ r₃ h
  have key : 18 * a3 * a2 * a1 * a0 - 4 * a2^3 * a0 + a2^2 * a1^2
      - 4 * a3 * a1^3 - 27 * a3^2 * a0^2
      = (a3^2 * ((r₁ - r₂) * ((r₁ - r₃) * (r₂ - r₃))))^2 := by
    rw [hb, hc, hd]
    ring
  rw [key]
  exact sq_nonneg _

/-- **The current–discriminant inequality.**  Whenever the parity jet factors through real
roots, the squared constant term (the parity current, at the parity point) is dominated by
an explicit polynomial in the higher jet: real-rootedness is a current detector. -/
theorem current_sq_le_of_real_rooted (a3 a2 a1 a0 r₁ r₂ r₃ : ℝ)
    (h : ∀ w : ℝ, a3*w^3 + a2*w^2 + a1*w + a0
      = a3 * ((w - r₁) * ((w - r₂) * (w - r₃)))) :
    27 * a3^2 * a0^2
      ≤ 18 * a3 * a2 * a1 * a0 - 4 * a2^3 * a0 + a2^2 * a1^2 - 4 * a3 * a1^3 := by
  have h1 := cubic_discrim_nonneg_of_real_rooted a3 a2 a1 a0 r₁ r₂ r₃ h
  linarith

/-- Transport of the Boltzmann derivative along a pointwise rewriting of the exponent. -/
theorem hasDerivAt_exp_neg_of_eq (c : ℝ) (f : ℝ → ℝ)
    (hf : ∀ y : ℝ, f y = Real.exp (-(y * c))) : HasDerivAt f (-c) 0 :=
  (hasDerivAt_exp_neg_mul c).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => hf y)

/-- **The parity-vortex theorem.**  For any three distinct integers `≥ 2`, at every
sufficiently small coupling `x > 0` the cubic gas admits **no** real factorization at the
parity point: its discriminant is `−27·((p−1)(q−1)(r−1))²·x² + O(x³) < 0`.  The parity
current itself drives the parity cluster off the real axis. -/
theorem parity_vortex_three (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), ¬ ∃ r₁ r₂ r₃ : ℝ, ∀ w : ℝ,
      gibbsDiag {p, q, r} x (-1 + w)
        = Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) * ((w - r₁) * ((w - r₂) * (w - r₃))) := by
  classical
  have hqr' : q ∉ ({r} : Finset ℕ) := by simp [hqr]
  have hp' : p ∉ ({q, r} : Finset ℕ) := by simp [hpq, hpr]
  have hexp2 : ∀ y z : ℝ, gibbsDiag {q, r} y z
      = Real.exp (-y) + (Real.exp (-((q:ℝ)*y)) + Real.exp (-((r:ℝ)*y))) * z
        + Real.exp (-((r:ℝ)*((q:ℝ)*y))) * z^2 := by
    intro y z
    rw [gibbsDiag_insert q {r} hqr', gibbsDiag_singleton, gibbsDiag_singleton]
    ring
  have hexp3 : ∀ x z : ℝ, gibbsDiag {p, q, r} x z
      = Real.exp (-x)
        + (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x))) * z
        + (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
            + Real.exp (-((r:ℝ)*((q:ℝ)*x)))) * z^2
        + Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) * z^3 := by
    intro x z
    rw [gibbsDiag_insert p {q, r} hp', hexp2, hexp2]
    ring
  -- the parity jets
  set g0 : ℝ → ℝ := fun x =>
    Real.exp (-x)
      - (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x)))
      + (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
          + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
      - Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) with hg0
  set g1 : ℝ → ℝ := fun x =>
    (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x)))
      - 2 * (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
          + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
      + 3 * Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) with hg1
  set g2 : ℝ → ℝ := fun x =>
    (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
        + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
      - 3 * Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) with hg2
  set g3 : ℝ → ℝ := fun x => Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) with hg3
  have hjet : ∀ x w : ℝ, gibbsDiag {p, q, r} x (-1 + w)
      = g3 x * w^3 + g2 x * w^2 + g1 x * w + g0 x := by
    intro x w
    rw [hexp3, hg0, hg1, hg2, hg3]
    ring
  -- values at coupling zero
  have hg00 : g0 0 = 0 := by rw [hg0]; norm_num [Real.exp_zero]
  have hg10 : g1 0 = 0 := by rw [hg1]; norm_num [Real.exp_zero]
  have hg20 : g2 0 = 0 := by rw [hg2]; norm_num [Real.exp_zero]
  -- derivative of the current: the totient
  set φ : ℝ := ((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1)) with hφ
  have hφ0 : 0 < φ := by
    rw [hφ]
    have h1 : (0:ℝ) < (p:ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      linarith
    have h2 : (0:ℝ) < (q:ℝ) - 1 := by
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith
    have h3 : (0:ℝ) < (r:ℝ) - 1 := by
      have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      linarith
    exact mul_pos h1 (mul_pos h2 h3)
  have hg0d : HasDerivAt g0 φ 0 := by
    have hE : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-(1:ℝ)) 0 :=
      hasDerivAt_exp_neg_of_eq 1 _ (fun y => by norm_num)
    have hP : HasDerivAt (fun x : ℝ => Real.exp (-((p:ℝ)*x))) (-(p:ℝ)) 0 :=
      hasDerivAt_exp_neg_of_eq _ _ (fun y => by rw [mul_comm])
    have hQ : HasDerivAt (fun x : ℝ => Real.exp (-((q:ℝ)*x))) (-(q:ℝ)) 0 :=
      hasDerivAt_exp_neg_of_eq _ _ (fun y => by rw [mul_comm])
    have hR : HasDerivAt (fun x : ℝ => Real.exp (-((r:ℝ)*x))) (-(r:ℝ)) 0 :=
      hasDerivAt_exp_neg_of_eq _ _ (fun y => by rw [mul_comm])
    have hQP : HasDerivAt (fun x : ℝ => Real.exp (-((q:ℝ)*((p:ℝ)*x))))
        (-((q:ℝ)*(p:ℝ))) 0 :=
      hasDerivAt_exp_neg_of_eq _ _ (fun y => by congr 1; ring)
    have hRP : HasDerivAt (fun x : ℝ => Real.exp (-((r:ℝ)*((p:ℝ)*x))))
        (-((r:ℝ)*(p:ℝ))) 0 :=
      hasDerivAt_exp_neg_of_eq _ _ (fun y => by congr 1; ring)
    have hRQ : HasDerivAt (fun x : ℝ => Real.exp (-((r:ℝ)*((q:ℝ)*x))))
        (-((r:ℝ)*(q:ℝ))) 0 :=
      hasDerivAt_exp_neg_of_eq _ _ (fun y => by congr 1; ring)
    have hRQP : HasDerivAt (fun x : ℝ => Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))))
        (-((r:ℝ)*((q:ℝ)*(p:ℝ)))) 0 :=
      hasDerivAt_exp_neg_of_eq _ _ (fun y => by congr 1; ring)
    have hchain := ((hE.sub ((hP.add hQ).add hR)).add ((hQP.add hRP).add hRQ)).sub hRQP
    rw [hg0, hφ, show ((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1))
        = -1 - (-(p:ℝ) + -(q:ℝ) + -(r:ℝ))
          + (-((q:ℝ)*(p:ℝ)) + -((r:ℝ)*(p:ℝ)) + -((r:ℝ)*(q:ℝ)))
          - -((r:ℝ)*((q:ℝ)*(p:ℝ))) from by ring]
    exact hchain
  -- the other jets are differentiable; their exact derivatives are irrelevant
  have hd1 : DifferentiableAt ℝ g1 0 := by
    rw [hg1]
    fun_prop
  have hd2 : DifferentiableAt ℝ g2 0 := by
    rw [hg2]
    fun_prop
  -- slope limits along the punctured right neighbourhood
  have hmono : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) {y | y ≠ 0} :=
    nhdsWithin_mono 0 (fun y hy => ne_of_gt hy)
  have hslope : ∀ (g : ℝ → ℝ) (d : ℝ), g 0 = 0 → HasDerivAt g d 0 →
      Filter.Tendsto (fun x => g x / x) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds d) := by
    intro g d hg0' hgd
    have h1 := hasDerivAt_iff_tendsto_slope.mp hgd
    have h2 : Filter.Tendsto (fun x => g x / x)
        (nhdsWithin (0:ℝ) {y | y ≠ 0}) (nhds d) := by
      refine h1.congr fun y => ?_
      simp [slope_def_field, hg0']
    exact h2.mono_left hmono
  have hs0 := hslope g0 φ hg00 hg0d
  have hs1 := hslope g1 (deriv g1 0) hg10 hd1.hasDerivAt
  have hs2 := hslope g2 (deriv g2 0) hg20 hd2.hasDerivAt
  -- continuity of the leading jet
  have hg3c : Filter.Tendsto g3 (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hc : Continuous g3 := by
      rw [hg3]
      fun_prop
    have h1 := hc.tendsto 0
    have h30 : g3 0 = 1 := by simp [hg3]
    rw [h30] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hxlim : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  -- the rescaled discriminant
  set Gf : ℝ → ℝ := fun x =>
    x * (18 * g3 x * (g2 x / x) * (g1 x / x) * (g0 x / x))
      - x^2 * (4 * (g2 x / x)^3 * (g0 x / x))
      + x^2 * ((g2 x / x)^2 * (g1 x / x)^2)
      - x * (4 * g3 x * (g1 x / x)^3)
      - 27 * (g3 x)^2 * (g0 x / x)^2 with hGf
  have hGlim : Filter.Tendsto Gf (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (0 * (18 * 1 * (deriv g2 0) * (deriv g1 0) * φ)
        - 0^2 * (4 * (deriv g2 0)^3 * φ)
        + 0^2 * ((deriv g2 0)^2 * (deriv g1 0)^2)
        - 0 * (4 * 1 * (deriv g1 0)^3)
        - 27 * 1^2 * φ^2)) := by
    rw [hGf]
    exact (((((hxlim.mul ((((Filter.Tendsto.const_mul 18 hg3c).mul hs2).mul hs1).mul
        hs0)).sub ((hxlim.pow 2).mul ((Filter.Tendsto.const_mul 4 (hs2.pow 3)).mul
        hs0))).add ((hxlim.pow 2).mul ((hs2.pow 2).mul (hs1.pow 2)))).sub
        (hxlim.mul ((Filter.Tendsto.const_mul 4 hg3c).mul (hs1.pow 3)))).sub
        ((Filter.Tendsto.const_mul 27 (hg3c.pow 2)).mul (hs0.pow 2)))
  have hGneg : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), Gf x < 0 := by
    have hlim0 : (0 * (18 * 1 * (deriv g2 0) * (deriv g1 0) * φ)
        - 0^2 * (4 * (deriv g2 0)^3 * φ)
        + 0^2 * ((deriv g2 0)^2 * (deriv g1 0)^2)
        - 0 * (4 * 1 * (deriv g1 0)^3)
        - 27 * 1^2 * φ^2) < 0 := by
      have := mul_pos hφ0 hφ0
      nlinarith [this]
    exact hGlim.eventually_lt_const hlim0
  have hxpos : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx
  filter_upwards [hGneg, hxpos] with x hG hx
  rintro ⟨r₁, r₂, r₃, hfac⟩
  have hforall : ∀ w : ℝ, g3 x * w^3 + g2 x * w^2 + g1 x * w + g0 x
      = g3 x * ((w - r₁) * ((w - r₂) * (w - r₃))) := by
    intro w
    rw [← hjet x w, hfac w, hg3]
  have hnonneg := cubic_discrim_nonneg_of_real_rooted (g3 x) (g2 x) (g1 x) (g0 x)
    r₁ r₂ r₃ hforall
  have hxne : x ≠ 0 := ne_of_gt hx
  have hΔG : 18 * g3 x * g2 x * g1 x * g0 x - 4 * (g2 x)^3 * g0 x
      + (g2 x)^2 * (g1 x)^2 - 4 * g3 x * (g1 x)^3 - 27 * (g3 x)^2 * (g0 x)^2
      = x^2 * Gf x := by
    rw [hGf]
    field_simp
  have hneg : 18 * g3 x * g2 x * g1 x * g0 x - 4 * (g2 x)^3 * g0 x
      + (g2 x)^2 * (g1 x)^2 - 4 * g3 x * (g1 x)^3 - 27 * (g3 x)^2 * (g0 x)^2 < 0 := by
    rw [hΔG]
    exact mul_neg_of_pos_of_neg (by positivity) hG
  linarith

end RHTower.GibbsGas
