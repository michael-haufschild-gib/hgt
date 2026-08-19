import Mathlib

/-!
# Truncating a squarefree Euler product by size, not by the number of factors

The bounding sum of a Selberg sieve is the part of `∏_p (1 + a_p)` carried by squarefree divisors
below the level.  Keeping only the divisors with at most `k` prime factors is a valid but expensive
truncation: it forces the level to exceed the sifting bound raised to a power that grows with
`∑_p a_p`, and hence costs a factor `(log log)²` in the saving of a dimension-two sieve.

Rankin's device truncates by the size of the divisor itself.  With the *right* exponent — one
comparable to `1/log(\text{sifting bound})` rather than one comparable to `1/∑ a_p` — the level need
only exceed a fixed power of the sifting bound, and the full saving survives.
-/

namespace RHTower.Sieve

open Finset

/-- The real value of a squarefree divisor named by its prime set. -/
def natProdR (t : Finset ℕ) : ℝ := ∏ p ∈ t, (p : ℝ)

theorem natProdR_nonneg (t : Finset ℕ) : 0 ≤ natProdR t :=
  Finset.prod_nonneg fun p _ => Nat.cast_nonneg p

/-- A squarefree Euler product is the sum over subsets. -/
theorem prod_one_add_eq_sum_powerset_real {s : Finset ℕ} (a : ℕ → ℝ) :
    ∏ p ∈ s, (a p + 1) = ∑ t ∈ s.powerset, ∏ p ∈ t, a p := by
  classical
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp

/-- **Rankin's truncation.**  If the level `D` satisfies `∑_p (p^α − 1) a_p + log 2 ≤ α·log D` for
some `α > 0`, the divisors below `D` carry at least half of the Euler product. -/
theorem sum_powerset_prod_le_ge {s : Finset ℕ} {a : ℕ → ℝ} (ha0 : ∀ p ∈ s, 0 ≤ a p)
    (hp1 : ∀ p ∈ s, 1 ≤ p) {α D : ℝ} (hα : 0 < α) (hD : 0 < D)
    (hcond : (∑ p ∈ s, ((p : ℝ) ^ α - 1) * a p) + Real.log 2 ≤ α * Real.log D) :
    (1 / 2) * ∏ p ∈ s, (a p + 1)
      ≤ ∑ t ∈ s.powerset.filter (fun t => natProdR t ≤ D), ∏ p ∈ t, a p := by
  classical
  have hpR : ∀ p ∈ s, (1 : ℝ) ≤ (p : ℝ) := fun p hp => by exact_mod_cast hp1 p hp
  have hpow1 : ∀ p ∈ s, (1 : ℝ) ≤ (p : ℝ) ^ α := fun p hp =>
    Real.one_le_rpow (hpR p hp) hα.le
  have hDα : (0 : ℝ) < D ^ α := Real.rpow_pos_of_pos hD α
  -- the whole product is the sum over all subsets
  have hall : ∏ p ∈ s, (a p + 1) = ∑ t ∈ s.powerset, ∏ p ∈ t, a p :=
    prod_one_add_eq_sum_powerset_real a
  have hnonneg : ∀ t ∈ s.powerset, (0 : ℝ) ≤ ∏ p ∈ t, a p := by
    intro t ht
    refine Finset.prod_nonneg fun p hp => ha0 p (Finset.mem_powerset.1 ht hp)
  -- the tail, by Rankin's device
  have htail : ∑ t ∈ s.powerset.filter (fun t => ¬ (natProdR t ≤ D)), ∏ p ∈ t, a p
      ≤ (D ^ α)⁻¹ * ∏ p ∈ s, ((p : ℝ) ^ α * a p + 1) := by
    have hstep : ∀ t ∈ s.powerset.filter (fun t => ¬ (natProdR t ≤ D)),
        (∏ p ∈ t, a p) ≤ (D ^ α)⁻¹ * ∏ p ∈ t, ((p : ℝ) ^ α * a p) := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_powerset] at ht
      obtain ⟨hts, hbig⟩ := ht
      rw [not_le] at hbig
      have hprodpos : ∀ p ∈ t, (0 : ℝ) ≤ (p : ℝ) := fun p hp => by
        have := hpR p (hts hp); linarith
      have hsplit : ∏ p ∈ t, ((p : ℝ) ^ α * a p)
          = (natProdR t) ^ α * ∏ p ∈ t, a p := by
        rw [Finset.prod_mul_distrib, natProdR, Real.finsetProd_rpow t _ hprodpos α]
      rw [hsplit]
      have hbig' : D ^ α ≤ (natProdR t) ^ α :=
        Real.rpow_le_rpow hD.le hbig.le hα.le
      have ha0t : (0 : ℝ) ≤ ∏ p ∈ t, a p :=
        Finset.prod_nonneg fun p hp => ha0 p (hts hp)
      rw [inv_mul_eq_div, le_div_iff₀ hDα]
      have : (∏ p ∈ t, a p) * D ^ α ≤ (∏ p ∈ t, a p) * (natProdR t) ^ α :=
        mul_le_mul_of_nonneg_left hbig' ha0t
      nlinarith [this]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hsub : s.powerset.filter (fun t => ¬ (natProdR t ≤ D)) ⊆ s.powerset :=
      Finset.filter_subset _ _
    have hmono : ∑ t ∈ s.powerset.filter (fun t => ¬ (natProdR t ≤ D)),
          ∏ p ∈ t, ((p : ℝ) ^ α * a p)
        ≤ ∑ t ∈ s.powerset, ∏ p ∈ t, ((p : ℝ) ^ α * a p) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun t ht _ => ?_
      refine Finset.prod_nonneg fun p hp => ?_
      have hps := Finset.mem_powerset.1 ht hp
      exact mul_nonneg (le_trans zero_le_one (hpow1 p hps)) (ha0 p hps)
    have heq : ∑ t ∈ s.powerset, ∏ p ∈ t, ((p : ℝ) ^ α * a p)
        = ∏ p ∈ s, ((p : ℝ) ^ α * a p + 1) :=
      (prod_one_add_eq_sum_powerset_real (fun p => (p : ℝ) ^ α * a p)).symm
    rw [heq] at hmono
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  -- the weighted product against the plain one
  have hcmp : ∏ p ∈ s, ((p : ℝ) ^ α * a p + 1)
      ≤ (∏ p ∈ s, (a p + 1)) * Real.exp (∑ p ∈ s, ((p : ℝ) ^ α - 1) * a p) := by
    rw [Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have := hpow1 p hp
      have := ha0 p hp
      positivity
    · intro p hp
      have h1 := hpow1 p hp
      have h2 := ha0 p hp
      have hexp : 1 + ((p : ℝ) ^ α - 1) * a p ≤ Real.exp (((p : ℝ) ^ α - 1) * a p) := by
        have := Real.add_one_le_exp (((p : ℝ) ^ α - 1) * a p)
        linarith
      have hstep : (p : ℝ) ^ α * a p + 1 ≤ (a p + 1) * (1 + ((p : ℝ) ^ α - 1) * a p) := by
        have hkey : (0 : ℝ) ≤ a p * (a p * ((p : ℝ) ^ α - 1)) :=
          mul_nonneg h2 (mul_nonneg h2 (by linarith))
        nlinarith [hkey]
      have hpos : (0 : ℝ) ≤ a p + 1 := by linarith
      calc (p : ℝ) ^ α * a p + 1 ≤ (a p + 1) * (1 + ((p : ℝ) ^ α - 1) * a p) := hstep
        _ ≤ (a p + 1) * Real.exp (((p : ℝ) ^ α - 1) * a p) :=
            mul_le_mul_of_nonneg_left hexp hpos
  -- the condition turns the tail into half the product
  have hexpbd : Real.exp (∑ p ∈ s, ((p : ℝ) ^ α - 1) * a p) ≤ D ^ α / 2 := by
    have h1 : (∑ p ∈ s, ((p : ℝ) ^ α - 1) * a p)
        ≤ α * Real.log D - Real.log 2 := by linarith [hcond]
    have h2 := Real.exp_le_exp.2 h1
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)] at h2
    have h3 : Real.exp (α * Real.log D) = D ^ α := by
      rw [Real.rpow_def_of_pos hD]
      ring_nf
    rw [h3] at h2
    exact h2
  have hprod0 : (0 : ℝ) ≤ ∏ p ∈ s, (a p + 1) :=
    Finset.prod_nonneg fun p hp => by linarith [ha0 p hp]
  have hhalf : ∑ t ∈ s.powerset.filter (fun t => ¬ (natProdR t ≤ D)), ∏ p ∈ t, a p
      ≤ (1 / 2) * ∏ p ∈ s, (a p + 1) := by
    refine htail.trans ?_
    have hchain : ∏ p ∈ s, ((p : ℝ) ^ α * a p + 1)
        ≤ (∏ p ∈ s, (a p + 1)) * (D ^ α / 2) :=
      hcmp.trans (mul_le_mul_of_nonneg_left hexpbd hprod0)
    have := mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.2 hDα))
    calc (D ^ α)⁻¹ * ∏ p ∈ s, ((p : ℝ) ^ α * a p + 1)
        ≤ (D ^ α)⁻¹ * ((∏ p ∈ s, (a p + 1)) * (D ^ α / 2)) := this
      _ = (1 / 2) * ∏ p ∈ s, (a p + 1) := by
          field_simp
  -- split the powerset
  have hsplit : ∑ t ∈ s.powerset.filter (fun t => natProdR t ≤ D), ∏ p ∈ t, a p
      + ∑ t ∈ s.powerset.filter (fun t => ¬ (natProdR t ≤ D)), ∏ p ∈ t, a p
      = ∑ t ∈ s.powerset, ∏ p ∈ t, a p :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  linarith [hsplit, hhalf, hall]

end RHTower.Sieve
