import GaloisForLFunctions.RHTower.SuzukiLatticeShellSummability

/-!
# Geometric convergence of orbit sums over an `S`-unit lattice

§VII Lemma 1(a), (8) and (10) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The `S`-unit group maps, with finite kernel, onto a lattice in the trace-zero hyperplane of
`ℝ^S`, and the word metric satisfies `Sup_S |q_v| ≥ exp d(q,1)` (8).  Together with the ambient
overlap estimate (10), the inner products `⟨f₁, U(q) f₂⟩` are `O(exp(-d(q,1)))`, so the orbit
sum converges geometrically.  The convergence itself is the statement that an exponentially
decaying family on `ℤ^d` is summable: the exponential dominates every polynomial weight, and
polynomial weights above the lattice dimension are corpus-owned.
-/

open Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- An exponential is dominated by every reciprocal power of `1 + t`. -/
theorem connes_exp_neg_le_rpow_inv {c : ℝ} (hc : 0 < c) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(c * t))
      ≤ (Real.exp c * (n.factorial : ℝ) / c ^ n) * (1 + t) ^ (-(n : ℝ)) := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hs : (0 : ℝ) ≤ c * (1 + t) := by positivity
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hbase : (0 : ℝ) < (c * (1 + t)) ^ n / (n.factorial : ℝ) := by positivity
  have hpow := Real.pow_div_factorial_le_exp (c * (1 + t)) hs n
  have hinv : (Real.exp (c * (1 + t)))⁻¹ ≤ ((c * (1 + t)) ^ n / (n.factorial : ℝ))⁻¹ :=
    inv_anti₀ hbase hpow
  have hsplit : Real.exp (-(c * t)) = Real.exp c * (Real.exp (c * (1 + t)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hrhs : ((c * (1 + t)) ^ n / (n.factorial : ℝ))⁻¹
      = ((n.factorial : ℝ) / c ^ n) * (1 + t) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg h1t.le, Real.rpow_natCast, mul_pow]
    field_simp
  rw [hrhs] at hinv
  rw [hsplit]
  calc Real.exp c * (Real.exp (c * (1 + t)))⁻¹
      ≤ Real.exp c * ((n.factorial : ℝ) / c ^ n * (1 + t) ^ (-(n : ℝ))) :=
        mul_le_mul_of_nonneg_left hinv (Real.exp_pos c).le
    _ = Real.exp c * (n.factorial : ℝ) / c ^ n * (1 + t) ^ (-(n : ℝ)) := by ring

/-- **Geometric convergence on the lattice.**  An exponentially decaying family on `ℤ^d` is
summable. -/
theorem connes_summable_exp_neg_latticeL1 {d : ℕ} (hd : 0 < d) {c : ℝ} (hc : 0 < c) :
    Summable fun ν : Fin d → ℤ => Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ))) := by
  set n : ℕ := d + 1 with hn
  set C : ℝ := Real.exp c * (n.factorial : ℝ) / c ^ n with hC
  have hlt : (d : ℝ) < (n : ℝ) := by
    rw [hn]
    push_cast
    linarith
  have hpoly := _root_.RHTower.summable_polyDecay_fin (d := d) (p := (n : ℝ)) hd hlt
  refine Summable.of_nonneg_of_le (fun ν => (Real.exp_pos _).le) (fun ν => ?_)
    (hpoly.mul_left C)
  exact connes_exp_neg_le_rpow_inv hc n (Nat.cast_nonneg _)

/-- **§VII Lemma 1(a).**  A family on the `S`-unit lattice whose terms are dominated by
`exp(-c·d(q,1))` is absolutely summable: the orbit sum converges geometrically. -/
theorem connes_summable_of_exp_bound {d : ℕ} (hd : 0 < d) {c C : ℝ} (hc : 0 < c)
    {F : (Fin d → ℤ) → ℂ}
    (hF : ∀ ν, ‖F ν‖ ≤ C * Real.exp (-(c * (_root_.RHTower.latticeL1 ν : ℝ)))) :
    Summable F := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun ν => norm_nonneg _) hF ?_
  exact (connes_summable_exp_neg_latticeL1 hd hc).mul_left C

end

end GaloisForLFunctions.RHTower
