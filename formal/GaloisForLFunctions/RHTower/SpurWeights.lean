/-
Docs 26–27 weight identities (task #143): the Stieltjes sum rule and the energy identity,
machine-checked for real-rooted polynomials.

For `P = ∏_{r ∈ s}(X − r)` (real root multiset) and a critical point `c` (`P′(c) = 0`,
`P(c) ≠ 0`):
* `eval_derivative_rootProd_div` — the logarithmic-derivative sum `P′/P = Σ 1/(z−r)`;
* `energy_eq_neg_second_derivative` — **(E1)**: `Σ (c−r)^{−2} = −P″(c)/P(c)` (the exact
  electrostatic energy identity, doc 24 §2 / doc 25 (E1));
* `weight_sum_rule` — **Ση = 0**: `Σ c/(c−r) = 0` (doc 26/27's constraint, the Stieltjes
  equilibrium in weight form);
* `S_eq_card_add_energy` — **S = d + c²ℰ**: `Σ (1 − c/(c−r))² = card s + c²·Σ (c−r)^{−2}`
  (doc 27 §0: the scale-invariant energy in original coordinates).
-/
import Mathlib

namespace RHTower

open Polynomial

/-- The monic real-rooted polynomial with root multiset `s`. -/
noncomputable def rootProd (s : Multiset ℝ) : Polynomial ℝ :=
  (s.map fun r => X - C r).prod

theorem eval_rootProd (s : Multiset ℝ) (z : ℝ) :
    eval z (rootProd s) = (s.map fun r => z - r).prod := by
  rw [rootProd, eval_multiset_prod, Multiset.map_map]
  congr 1
  ext r
  simp

theorem eval_rootProd_cons (a : ℝ) (s : Multiset ℝ) (z : ℝ) :
    eval z (rootProd (a ::ₘ s)) = (z - a) * eval z (rootProd s) := by
  rw [eval_rootProd, eval_rootProd, Multiset.map_cons, Multiset.prod_cons]

theorem sub_ne_zero_of_eval_rootProd_ne_zero {s : Multiset ℝ} {z : ℝ}
    (hz : eval z (rootProd s) ≠ 0) : ∀ r ∈ s, z - r ≠ 0 := by
  intro r hr h0
  rw [eval_rootProd] at hz
  exact hz (Multiset.prod_eq_zero (by
    rw [Multiset.mem_map]
    exact ⟨r, hr, h0⟩))

/-- Product form of the logarithmic-derivative sum:
`P′(z) = P(z) · Σ_{r ∈ s} (z − r)⁻¹` off the zeros. -/
theorem eval_derivative_rootProd (s : Multiset ℝ) (z : ℝ)
    (hz : eval z (rootProd s) ≠ 0) :
    eval z (derivative (rootProd s))
      = eval z (rootProd s) * (s.map fun r => (z - r)⁻¹).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProd]
  | cons a s ih =>
      have hsplit := eval_rootProd_cons a s z
      have hQ : eval z (rootProd s) ≠ 0 := fun h0 => hz (by rw [hsplit, h0, mul_zero])
      have ha : z - a ≠ 0 := fun h0 => hz (by rw [hsplit, h0, zero_mul])
      have hcons : rootProd (a ::ₘ s) = (X - C a) * rootProd s := by
        rw [rootProd, rootProd, Multiset.map_cons, Multiset.prod_cons]
      rw [hcons, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
        one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, ih hQ, ← hcons, hsplit,
        Multiset.map_cons, Multiset.sum_cons]
      have hinv : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ ha
      linear_combination (-(eval z (rootProd s))) * hinv

/-- The weight-sum rule **Ση = 0** at critical points: `Σ_{r ∈ s} c/(c − r) = 0`. -/
theorem weight_sum_rule {s : Multiset ℝ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0) (hcrit : eval c (derivative (rootProd s)) = 0) :
    (s.map fun r => c / (c - r)).sum = 0 := by
  have h := eval_derivative_rootProd s c hc
  rw [hcrit] at h
  have hsum : (s.map fun r => (c - r)⁻¹).sum = 0 :=
    ((mul_eq_zero.mp h.symm).resolve_left hc)
  calc (s.map fun r => c / (c - r)).sum
      = (s.map fun r => c * (c - r)⁻¹).sum := by simp only [div_eq_mul_inv]
    _ = c * (s.map fun r => (c - r)⁻¹).sum := Multiset.sum_map_mul_left
    _ = 0 := by rw [hsum, mul_zero]

/-- Derivative of the reciprocal-sum field: `d/dz Σ (z−r)⁻¹ = −Σ (z−r)⁻²`. -/
theorem hasDerivAt_inv_sum (s : Multiset ℝ) (c : ℝ) (hc : ∀ r ∈ s, c - r ≠ 0) :
    HasDerivAt (fun z => (s.map fun r => (z - r)⁻¹).sum)
      (-(s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum) c := by
  induction s using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const c (0 : ℝ)
  | cons a s ih =>
      have ha : c - a ≠ 0 := hc a (Multiset.mem_cons_self ..)
      have hs : ∀ r ∈ s, c - r ≠ 0 := fun r hr => hc r (Multiset.mem_cons_of_mem hr)
      have h1 : HasDerivAt (fun z : ℝ => (z - a)⁻¹) (-((c - a) ^ (2 : ℕ))⁻¹) c := by
        have hbase : HasDerivAt (fun z : ℝ => z - a) 1 c := (hasDerivAt_id c).sub_const a
        have h2 := hbase.inv ha
        have h3 : (-1 : ℝ) / (c - a) ^ (2 : ℕ) = -((c - a) ^ (2 : ℕ))⁻¹ := by
          rw [neg_div, one_div]
        exact h3 ▸ h2
      have hfun : (fun z : ℝ => ((a ::ₘ s).map fun r => (z - r)⁻¹).sum)
          = fun z : ℝ => (z - a)⁻¹ + (s.map fun r => (z - r)⁻¹).sum := by
        funext z
        rw [Multiset.map_cons, Multiset.sum_cons]
      rw [hfun, Multiset.map_cons, Multiset.sum_cons, neg_add]
      exact h1.add (ih hs)

/-- **(E1), the energy identity** at critical points:
`Σ_{r ∈ s} (c − r)⁻² = −P″(c)/P(c)`, stated division-free. -/
theorem energy_eq_neg_second_derivative {s : Multiset ℝ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0) (hcrit : eval c (derivative (rootProd s)) = 0) :
    eval c (derivative (derivative (rootProd s)))
      = -((s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum) * eval c (rootProd s) := by
  set P := rootProd s with hP
  -- the product identity P′ = P · (Σ (z−r)⁻¹) holds eventually near c
  have hopen : ∀ᶠ z in nhds c, eval z P ≠ 0 := by
    have hcont : Continuous fun z : ℝ => eval z P := by
      simpa [Polynomial.aeval_def] using! P.continuous_aeval
    exact hcont.continuousAt.eventually_ne hc
  have hev : (fun z => eval z (derivative P)) =ᶠ[nhds c]
      fun z => eval z P * (s.map fun r => (z - r)⁻¹).sum := by
    filter_upwards [hopen] with z hz
    exact eval_derivative_rootProd s z hz
  -- differentiate both sides at c
  have hlhs : HasDerivAt (fun z => eval z (derivative P))
      (eval c (derivative (derivative P))) c := (derivative P).hasDerivAt c
  have hsum := hasDerivAt_inv_sum s c (sub_ne_zero_of_eval_rootProd_ne_zero hc)
  have hrhs : HasDerivAt (fun z => eval z P * (s.map fun r => (z - r)⁻¹).sum)
      (eval c (derivative P) * (s.map fun r => (c - r)⁻¹).sum
        + eval c P * (-(s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum)) c :=
    (P.hasDerivAt c).mul hsum
  have heq := (hlhs.congr_of_eventuallyEq hev.symm).unique hrhs
  rw [hcrit, zero_mul, zero_add] at heq
  rw [heq]
  ring

/-- **S = d + c²ℰ** (doc 27 §0): given the sum rule, the ξ-weights satisfy
`Σ (1 − c/(c−r))² = card s + c²·Σ (c−r)⁻²`. -/
theorem S_eq_card_add_energy {s : Multiset ℝ} {c : ℝ}
    (hc : eval c (rootProd s) ≠ 0) (hcrit : eval c (derivative (rootProd s)) = 0) :
    (s.map fun r => (1 - c / (c - r)) ^ (2 : ℕ)).sum
      = (s.card : ℝ) + c ^ (2 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum := by
  have hne := sub_ne_zero_of_eval_rootProd_ne_zero hc
  have hrule := weight_sum_rule hc hcrit
  have hpt : (s.map fun r => (1 - c / (c - r)) ^ (2 : ℕ))
      = (s.map fun r => 1 - 2 * (c / (c - r)) + c ^ (2 : ℕ) * ((c - r) ^ (2 : ℕ))⁻¹) := by
    apply Multiset.map_congr rfl
    intro r hr
    have h := hne r hr
    field_simp
    ring
  rw [hpt]
  have h1 : (s.map fun r => 1 - 2 * (c / (c - r)) + c ^ (2 : ℕ) * ((c - r) ^ (2 : ℕ))⁻¹).sum
      = (s.map fun r => 1 - 2 * (c / (c - r))).sum
        + (s.map fun r => c ^ (2 : ℕ) * ((c - r) ^ (2 : ℕ))⁻¹).sum := Multiset.sum_map_add
  have h2 : (s.map fun r => 1 - 2 * (c / (c - r))).sum
      = (s.map fun _ => (1 : ℝ)).sum - (s.map fun r => 2 * (c / (c - r))).sum :=
    Multiset.sum_map_sub
  have h3 : (s.map fun r => 2 * (c / (c - r))).sum
      = 2 * (s.map fun r => c / (c - r)).sum := Multiset.sum_map_mul_left
  have h4 : (s.map fun r => c ^ (2 : ℕ) * ((c - r) ^ (2 : ℕ))⁻¹).sum
      = c ^ (2 : ℕ) * (s.map fun r => ((c - r) ^ (2 : ℕ))⁻¹).sum := Multiset.sum_map_mul_left
  rw [h1, h2, h3, h4, hrule, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    mul_one, mul_zero, sub_zero]

end RHTower
