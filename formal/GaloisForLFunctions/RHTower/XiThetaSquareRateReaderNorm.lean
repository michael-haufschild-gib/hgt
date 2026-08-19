import GaloisForLFunctions.RHTower.XiThetaSquareRateBlaschkeLimit

/-!
# The exact reader norm of the theta square-rate system

The half-line exponentials of the physical heat rates `λ_k = π (k+1)²` have, by the co-distance
law, squared Gram--Schmidt length equal to the squared Blaschke product of the other rates against
`λ_n`, divided by `2 λ_n`.  The square-rate Blaschke limit evaluates that product, so the finite
co-distances converge to

`π / (2 sinh (π (n+1))²)`,

whose reciprocal square root is the exact reader norm `√(2/π) · sinh (π (n+1))` of the card.
-/

open Filter Topology Finset
open scoped InnerProductSpace
open InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The physical heat rates -/

/-- The physical heat rates `λ_k = π (k+1)²`. -/
def heatRateSeq (k : ℕ) : ℝ := Real.pi * ((k : ℝ) + 1) ^ 2

theorem heatRateSeq_pos (k : ℕ) : 0 < heatRateSeq k := by
  rw [heatRateSeq]
  positivity

theorem heatRateSeq_injective : Function.Injective heatRateSeq := by
  intro a b hab
  rw [heatRateSeq, heatRateSeq] at hab
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have h2 : ((a : ℝ) + 1) ^ 2 = ((b : ℝ) + 1) ^ 2 := by
    field_simp at hab
    exact hab
  have hpa : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hpb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have h3 : (((a : ℝ) + 1) - ((b : ℝ) + 1)) * (((a : ℝ) + 1) + ((b : ℝ) + 1)) = 0 := by
    nlinarith [h2]
  have h4 : (((a : ℝ) + 1) + ((b : ℝ) + 1)) ≠ 0 := by positivity
  have h5 := (mul_eq_zero.mp h3).resolve_right h4
  have h6 : (a : ℝ) = (b : ℝ) := by linarith
  exact_mod_cast h6

/-! ## The real co-distance law -/

/-- **The real co-distance law.** -/
theorem normSq_gramSchmidt_coSystem {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k)
    (hinj : Function.Injective lam) {n N : ℕ} (hn : n ≤ N) :
    ‖gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖ ^ 2 *
        ((∏ m ∈ (Finset.range (N + 1)).erase n, (lam m + lam n)) ^ 2 * (lam n + lam n))
      = (∏ m ∈ (Finset.range (N + 1)).erase n, (lam m - lam n)) ^ 2 := by
  have hc := inner_gramSchmidt_coSystem hpos hinj hn
  have hself : inner ℂ
      (gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N)
      (gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N) =
      ((‖gramSchmidt ℂ (expSystem (fun k => lam (coIdx n N k)) (fun _ => hpos _)) N‖ : ℂ)) ^ 2 :=
    inner_self_eq_norm_sq_to_K _
  refine Complex.ofReal_inj.mp ?_
  push_cast
  rw [← hself]
  exact hc

/-! ## The Blaschke form of the co-distance -/

theorem heatRate_blaschke_factor (n k : ℕ) :
    (heatRateSeq k - heatRateSeq n) / (heatRateSeq k + heatRateSeq n) =
      (1 - (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2) /
        (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2) := by
  have hk : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [heatRateSeq, heatRateSeq]
  have hden1 : Real.pi * ((k : ℝ) + 1) ^ 2 + Real.pi * ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have hden2 : (1 : ℝ) + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  field_simp

/-! ## The finite co-distance in Blaschke form, and its limit -/

theorem normSq_gramSchmidt_heatRate {n N : ℕ} (hn : n ≤ N) :
    ‖gramSchmidt ℂ
        (expSystem (fun k => heatRateSeq (coIdx n N k)) (fun _ => heatRateSeq_pos _)) N‖ ^ 2 *
        (2 * heatRateSeq n)
      = (∏ k ∈ (Finset.range (N + 1)).erase n,
          ((1 - (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2) /
            (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2))) ^ 2 := by
  have hkey := normSq_gramSchmidt_coSystem heatRateSeq_pos heatRateSeq_injective hn
  have hplus : (∏ m ∈ (Finset.range (N + 1)).erase n,
      (heatRateSeq m + heatRateSeq n)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun m _ => ?_)
    have := heatRateSeq_pos m
    have := heatRateSeq_pos n
    positivity
  have hb : (∏ k ∈ (Finset.range (N + 1)).erase n,
        ((1 - (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2) /
          (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2))) =
      (∏ m ∈ (Finset.range (N + 1)).erase n, (heatRateSeq m - heatRateSeq n)) /
        (∏ m ∈ (Finset.range (N + 1)).erase n, (heatRateSeq m + heatRateSeq n)) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl (fun k _ => (heatRate_blaschke_factor n k).symm)
  rw [hb, div_pow, eq_div_iff (pow_ne_zero 2 hplus), ← hkey]
  ring

/-- **The exact limiting co-distance of the theta square-rate system.** -/
theorem tendsto_normSq_gramSchmidt_heatRate (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ‖gramSchmidt ℂ
        (expSystem (fun k => heatRateSeq (coIdx n N k)) (fun _ => heatRateSeq_pos _)) N‖ ^ 2)
      Filter.atTop
      (nhds (Real.pi / (2 * Real.sinh (Real.pi * ((n : ℝ) + 1)) ^ 2))) := by
  have hsinhpos : 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) := by
    have hx : (0 : ℝ) < Real.pi * ((n : ℝ) + 1) := by positivity
    have h0 : Real.sinh 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) :=
      Real.sinh_lt_sinh.mpr hx
    rwa [Real.sinh_zero] at h0
  have hrate : (0 : ℝ) < 2 * heatRateSeq n := by
    have := heatRateSeq_pos n
    positivity
  have hsq := (tendsto_blaschke_square_rate n).pow 2
  have hdiv := hsq.div_const (2 * heatRateSeq n)
  have hval : ((-1 : ℝ) ^ n * (Real.pi * ((n : ℝ) + 1)) /
        Real.sinh (Real.pi * ((n : ℝ) + 1))) ^ 2 / (2 * heatRateSeq n) =
      Real.pi / (2 * Real.sinh (Real.pi * ((n : ℝ) + 1)) ^ 2) := by
    rw [heatRateSeq]
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hsne : Real.sinh (Real.pi * ((n : ℝ) + 1)) ≠ 0 := ne_of_gt hsinhpos
    have hone : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [div_pow, mul_pow, mul_pow, hone]
    field_simp
  rw [hval] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  have hne : heatRateSeq n ≠ 0 := ne_of_gt (heatRateSeq_pos n)
  rw [← normSq_gramSchmidt_heatRate hN]
  field_simp


end

end RHTower
