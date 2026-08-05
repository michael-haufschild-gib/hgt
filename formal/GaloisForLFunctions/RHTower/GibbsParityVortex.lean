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
    linear_combination (1 - A) * hs2'

end RHTower.GibbsGas
