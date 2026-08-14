import GaloisForLFunctions.RHTower.RouteEAntiscaleEnergyTransport
import GaloisForLFunctions.RHTower.RouteEPhysicalSaddleAntiscaleBarrier

/-!
# The exact logarithmic Euler deficit

For a finite prime aperture the positive squared Euler law and the moving Mellin Euler product
differ by exactly the transverse antiscale energy of each factor:

```text
|M_{σ,Y}(t)|² / G_{σ,Y} = ∏_{p ≤ Y} (1 - z_p),
    z_p = p^{-σ}|1 + p^{it}|² / (1 + p^{-σ})²,
```

so the logarithmic deficit is `log(G/|M|²) = ∑_{p ≤ Y} -log(1 - z_p)`.  Each local coordinate
obeys `0 ≤ z_p ≤ 4p^{-σ}` and `1 - z_p ≥ (1 - p^{-σ})²/(1 + p^{-σ})² > 0`, so no factor
degenerates.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## The local deficit coordinate -/

/-- The local antiscale deficit coordinate `z_p = p^(a-1)|1 + p^{it}|²/(1 + p^(a-1))²`. -/
def eulerDeficitCoord (a t : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p)) / (1 + (p : ℝ) ^ (a - 1)) ^ 2

/-- The positive squared Euler law `G = ∏_{p ≤ Y}(1 + p^(a-1))²`. -/
def positiveEulerSquare (a Y : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 + (p : ℝ) ^ (a - 1)) ^ 2

/-- The squared modulus of the moving Euler product `|M(t)|² = ∏_{p ≤ Y}|1 - p^(a-1-it)|²`. -/
def eulerMellinNormSq (a t Y : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊Y⌋₊,
    Complex.normSq (1 - (((p : ℝ) ^ (a - 1) : ℝ) : ℂ) *
      Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I))

/-- The logarithmic Euler deficit `log(G/|M(t)|²)`. -/
def eulerLogDeficit (a t Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, -Real.log (1 - eulerDeficitCoord a t p)

theorem eulerDeficitCoord_nonneg {a t : ℝ} {p : ℕ} (hp : p.Prime) :
    0 ≤ eulerDeficitCoord a t p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
  have hcos : (0 : ℝ) ≤ 2 + 2 * Real.cos (t * Real.log p) := by
    have := Real.neg_one_le_cos (t * Real.log p)
    linarith
  rw [eulerDeficitCoord]
  positivity

theorem eulerDeficitCoord_le {a t : ℝ} {p : ℕ} (hp : p.Prime) :
    eulerDeficitCoord a t p ≤ 4 * (p : ℝ) ^ (a - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
  have hcos : 2 + 2 * Real.cos (t * Real.log p) ≤ 4 := by
    have := Real.cos_le_one (t * Real.log p)
    linarith
  have hden : (1 : ℝ) ≤ (1 + (p : ℝ) ^ (a - 1)) ^ 2 := by nlinarith
  have hdenpos : (0 : ℝ) < (1 + (p : ℝ) ^ (a - 1)) ^ 2 := by positivity
  rw [eulerDeficitCoord, div_le_iff₀ hdenpos]
  have hnum : (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p))
      ≤ (p : ℝ) ^ (a - 1) * 4 := mul_le_mul_of_nonneg_left hcos hu.le
  nlinarith [hnum, hu, hden]

/-- No local factor degenerates: `1 - z_p ≥ ((1 - u)/(1 + u))²`. -/
theorem one_sub_eulerDeficitCoord_ge {a t : ℝ} {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ) ^ (a - 1)) ^ 2 / (1 + (p : ℝ) ^ (a - 1)) ^ 2
      ≤ 1 - eulerDeficitCoord a t p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
  have hdenpos : (0 : ℝ) < (1 + (p : ℝ) ^ (a - 1)) ^ 2 := by positivity
  have hcos : 2 + 2 * Real.cos (t * Real.log p) ≤ 4 := by
    have := Real.cos_le_one (t * Real.log p)
    linarith
  have hkey : (1 - (p : ℝ) ^ (a - 1)) ^ 2
      ≤ (1 + (p : ℝ) ^ (a - 1)) ^ 2
        - (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p)) := by
    nlinarith [mul_le_mul_of_nonneg_left hcos hu.le]
  have hrw : 1 - eulerDeficitCoord a t p
      = ((1 + (p : ℝ) ^ (a - 1)) ^ 2
          - (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p)))
        / (1 + (p : ℝ) ^ (a - 1)) ^ 2 := by
    rw [eulerDeficitCoord]
    field_simp
  rw [hrw]
  exact div_le_div_of_nonneg_right hkey hdenpos.le

theorem one_sub_eulerDeficitCoord_pos {a t : ℝ} {p : ℕ} (hp : p.Prime) (ha : a < 1) :
    0 < 1 - eulerDeficitCoord a t p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
  have hult : (p : ℝ) ^ (a - 1) < 1 := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith : a - 1 < 0)
    exact h
  have hbound := one_sub_eulerDeficitCoord_ge (a := a) (t := t) hp
  have hnum : (0 : ℝ) < (1 - (p : ℝ) ^ (a - 1)) ^ 2 := by
    have : (1 : ℝ) - (p : ℝ) ^ (a - 1) > 0 := by linarith
    positivity
  have hden : (0 : ℝ) < (1 + (p : ℝ) ^ (a - 1)) ^ 2 := by positivity
  have : (0 : ℝ) < (1 - (p : ℝ) ^ (a - 1)) ^ 2 / (1 + (p : ℝ) ^ (a - 1)) ^ 2 :=
    div_pos hnum hden
  linarith

/-! ## The exact deficit identity -/

/-- **Exact Euler deficit identity.**  The moving Euler product is the positive squared law times
the product of the local antiscale deficits. -/
theorem eulerMellinNormSq_div_positiveEulerSquare (a t Y : ℝ) :
    eulerMellinNormSq a t Y / positiveEulerSquare a Y
      = ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 - eulerDeficitCoord a t p) := by
  have hradius : ∀ p ∈ Nat.primesLE ⌊Y⌋₊, ((p : ℝ) ^ (a - 1)) ≠ -1 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
    intro h
    rw [h] at hu
    linarith
  have h := routeE_finiteEuler_normalized_deficit (s := Nat.primesLE ⌊Y⌋₊)
    (radius := fun p : ℕ => (p : ℝ) ^ (a - 1)) (phase := fun p : ℕ => t * Real.log p) hradius
  rw [eulerMellinNormSq, positiveEulerSquare, h]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [eulerDeficitCoord]
  congr 2
  rw [two_add_two_cos_eq_normSq (t * Real.log p), Complex.sq_norm]

/-- **The logarithmic deficit.** -/
theorem eulerLogDeficit_eq_log_sub {a t Y : ℝ} (ha : a < 1) :
    eulerLogDeficit a t Y
      = Real.log (positiveEulerSquare a Y) - Real.log (eulerMellinNormSq a t Y) := by
  have hpos : ∀ p ∈ Nat.primesLE ⌊Y⌋₊, (0 : ℝ) < 1 - eulerDeficitCoord a t p := by
    intro p hp
    exact one_sub_eulerDeficitCoord_pos (Nat.prime_of_mem_primesLE hp) ha
  have hG : (0 : ℝ) < positiveEulerSquare a Y := by
    rw [positiveEulerSquare]
    refine Finset.prod_pos fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hu : (0 : ℝ) < (p : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos hp0 _
    positivity
  have hM : (0 : ℝ) < eulerMellinNormSq a t Y := by
    have hprod : (0 : ℝ) < ∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 - eulerDeficitCoord a t p) :=
      Finset.prod_pos hpos
    have hdiv : (0 : ℝ) < eulerMellinNormSq a t Y / positiveEulerSquare a Y := by
      rw [eulerMellinNormSq_div_positiveEulerSquare]
      exact hprod
    have hmul := mul_pos hdiv hG
    rwa [div_mul_cancel₀ _ (ne_of_gt hG)] at hmul
  have hlog : Real.log (eulerMellinNormSq a t Y / positiveEulerSquare a Y)
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log (1 - eulerDeficitCoord a t p) := by
    rw [eulerMellinNormSq_div_positiveEulerSquare]
    exact Real.log_prod (fun p hp => ne_of_gt (hpos p hp))
  rw [Real.log_div (ne_of_gt hM) (ne_of_gt hG)] at hlog
  rw [eulerLogDeficit, Finset.sum_neg_distrib]
  linarith [hlog]

end

end RHTower
