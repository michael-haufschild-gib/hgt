import GaloisForLFunctions.RHTower.Sieve.PrimeBlockPowerCofactorMeanSquare

/-!
# Mean values for the Matomäki–Radziwiłł ladder

Polynomials are `logPoly a s w = Σ_{n ∈ s} a_n n^{2πiw}` (`Sieve.logPoly`).

* **Moment computation with arbitrary prime coefficients**
  (`integral_normSq_logPoly_pow_mul_logPoly_le`): for primes `B ⊂ [S_min, B_max]`, `|a_p| ≤ 1`, and
  cofactors `D ⊂ [1, X]`, `|c_m| ≤ 1`,
  `∫_{|w| ≤ W} |Q^ℓ C|² ≤ (5πW/2 + 5e B_max^ℓ X/2) · #B^ℓ X (#B + ℓ B_max)^ℓ / S_min^ℓ`,
  `Q = logPoly a B`, `C = logPoly c D`.  The corpus proof for Möbius prime coefficients
  (`Sieve.integral_normSq_primeBlockPoly_pow_mul_logPoly_le`) uses only `|μ(p)| ≤ 1`: the fibre energy
  is bounded by coincidences of `(∏ g_i) m`, which do not see the coefficients.
-/

open Finset MeasureTheory RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `(Σ_{p∈B} a_p p^{2πiw})^ℓ · Σ_{m∈D} c_m m^{2πiw}` expanded over `B^ℓ × D`. -/
theorem logPoly_pow_mul_logPoly_eq (B D : Finset ℕ) (hB : ∀ p ∈ B, 0 < p)
    (hD : ∀ m ∈ D, 0 < m) (a c : ℕ → ℂ) (ℓ : ℕ) (w : ℝ) :
    logPoly a B w ^ ℓ * logPoly c D w
      = ∑ t ∈ (Fintype.piFinset fun _ : Fin ℓ => B) ×ˢ D,
          ((∏ i, a (t.1 i)) * c t.2) * unitLogPhase w ((∏ i, t.1 i) * t.2) := by
  classical
  rw [logPoly_eq_sum_mul_unitLogPhase, ← Fin.prod_const, Finset.prod_univ_sum,
    logPoly_eq_sum_mul_unitLogPhase, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun m hm => ?_
  have hgB : ∀ i, g i ∈ B := Fintype.mem_piFinset.mp hg
  have hgpos : ∀ i ∈ (Finset.univ : Finset (Fin ℓ)), 0 < g i := fun i _ => hB _ (hgB i)
  rw [Finset.prod_mul_distrib, prod_unitLogPhase _ _ hgpos,
    unitLogPhase_mul w (Finset.prod_pos hgpos).ne' (hD m hm).ne']
  ring

/-- **The moment computation with arbitrary bounded prime coefficients.** -/
theorem integral_normSq_logPoly_pow_mul_logPoly_le {B D : Finset ℕ}
    (hB : ∀ p ∈ B, p.Prime) {a c : ℕ → ℂ} (ha : ∀ p, ‖a p‖ ≤ 1) (hc : ∀ m, ‖c m‖ ≤ 1) {X : ℕ}
    (hD : ∀ m ∈ D, 1 ≤ m ∧ m ≤ X) {Smin : ℝ} (hSmin : 0 < Smin) (hmin : ∀ p ∈ B, Smin ≤ p)
    {Bmax : ℕ} (hmax : ∀ p ∈ B, p ≤ Bmax) (ℓ : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a B w ^ ℓ * logPoly c D w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ ℓ * X : ℕ) : ℝ))
          * ((B.card : ℝ) ^ ℓ * X * ((B.card : ℝ) + ℓ * Bmax) ^ ℓ / Smin ^ ℓ) := by
  classical
  set G := Fintype.piFinset fun _ : Fin ℓ => B with hG
  have hGB : ∀ g ∈ G, ∀ i, g i ∈ B := fun g hg => Fintype.mem_piFinset.mp hg
  simp_rw [logPoly_pow_mul_logPoly_eq B D (fun p hp => (hB p hp).pos)
    (fun m hm => (hD m hm).1) a c ℓ]
  have hpos : ∀ t ∈ G ×ˢ D, 0 < (∏ i, t.1 i) * t.2 := by
    intro t ht
    obtain ⟨hg, hm⟩ := Finset.mem_product.mp ht
    exact Nat.mul_pos (Finset.prod_pos fun i _ => (hB _ (hGB _ hg i)).pos) (hD _ hm).1
  have hle : ∀ t ∈ G ×ˢ D, (∏ i, t.1 i) * t.2 ≤ Bmax ^ ℓ * X := by
    intro t ht
    obtain ⟨hg, hm⟩ := Finset.mem_product.mp ht
    refine Nat.mul_le_mul ?_ (hD _ hm).2
    have := Finset.prod_le_pow_card Finset.univ t.1 Bmax fun i _ => hmax _ (hGB _ hg i)
    simpa using this
  have hbase := integral_normSq_sum_unitLogPhase_le (G ×ˢ D) (fun t => (∏ i, t.1 i) * t.2)
    (fun t => (∏ i, a (t.1 i)) * c t.2) hpos hle hW
  have hb : ∀ t ∈ G ×ˢ D, ‖(∏ i, a (t.1 i)) * c t.2‖ ≤ 1 := by
    intro t _
    rw [norm_mul, norm_prod]
    have hprod : ∏ i, ‖a (t.1 i)‖ ≤ 1 :=
      Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => ha _
    calc (∏ i, ‖a (t.1 i)‖) * ‖c t.2‖ ≤ 1 * 1 :=
          mul_le_mul hprod (hc _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have henergy := (sum_normSq_fibre_le_coincidences (G ×ˢ D) (fun t => (∏ i, t.1 i) * t.2)
    (fun t => (∏ i, a (t.1 i)) * c t.2) hb).trans
      (sum_card_coincidences_le hB hD hSmin hmin hmax ℓ)
  have hcoef : 0 ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((Bmax ^ ℓ * X : ℕ) : ℝ) := by
    have := Real.pi_pos; have := (Real.exp_pos 1).le
    have : (0 : ℝ) ≤ W := by linarith
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left henergy hcoef)

end

end GaloisForLFunctions.MatomakiRadziwill
