import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionStaircaseTrains
import GaloisForLFunctions.BiScaleUncertainty.PrimeTowerDeletionLocalEulerFactor

/-!
# Whole towers read the composite nodes

Deleting one prime power per prime costs the same on the prime-power blind cone and on the
integer-grid blind cone (`PrimePowerDeletionStaircaseTrains`): the composite nodes are free. Deleting
whole towers is different. On the prime-power cone the towers of a finite set of primes `P` have
supremum price `Σ_{p∈P} 2 log p/(√p − 1)` (`PrimeTowerDeletionLocalEulerFactor`), approached by divisor
trains whose spectral density concentrates where every local Euler factor peaks at once; that
joint phase is exactly where the composite nodes `p^i q^j` are charged most.

**Theorem** (`gridTowerDeviation_le`, `gridTowerDeviation_ge`). Let `p ≠ q` be primes of `P`,
`x_r = r^{−1/2}`. On the cone blind at every integer `n ≥ 2` that is not a power of a prime of `P`
(so blind at `pq`), every deviation satisfies

`(A − W)/‖c‖² ≤ Σ_{r∈P} 2 log r/(√r − 1) − c₀`   for `c₀ ≤ log r · x_r/(1 − x_r²)`, `r = p, q`,

`(A − W)/‖c‖² ≥ −Σ_{r∈P} 2 log r/(√r + 1) + c₀`  for `c₀ ≤ log r · x_r(1 − x_r)/(1 + x_r)³`.

For `{2, 3}` the supremum drops by at least `9/10` (`gridTowerDeviation_two_three_le`): blindness at
`log 6` is free for the single nodes `{2, 3}` and costs at least `9/10` for the whole towers.

**Mechanism.** By the tower spectral identity `π(A − W) = ∫ G_c Σ_r log r · S_{x_r}(t log r)`, and
blindness at `pq` adds the free term `−(c₀/2) ∫ G_c cos(t log pq)`. The dual certificate
`Σ_r log r S_{x_r}(t log r) − (c₀/2) cos(t log p + t log q)` is bounded by its value at the joint phase
`t log p ≡ t log q ≡ 0`, because each Poisson symbol falls quadratically away from its peak,
`S_x(θ) ≤ x/(1−x) − x(1 − cos θ)/(1 − x²)` (`eulerSymbol_le_sub`), faster than the composite cosine
can rise, `1 − cos(a + b) ≤ 2(1 − cos a) + 2(1 − cos b)` (`one_sub_cos_add_le`).
-/

open MeasureTheory Set Complex Finsupp Filter
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Quadratic drop of the Poisson symbol and the composite cosine -/

/-- `S_x(θ) ≤ x/(1−x) − x(1 − cos θ)/(1 − x²)`: the symbol falls quadratically from its peak. -/
theorem eulerSymbol_le_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    eulerSymbol x θ ≤ x / (1 - x) - x / (1 - x ^ 2) * (1 - Real.cos θ) := by
  have hD := eulerSymbol_denom_pos hx1 θ hx0
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - x ^ 2 := by nlinarith
  have hc := Real.cos_le_one θ
  have hc' := Real.neg_one_le_cos θ
  rw [eulerSymbol, div_le_iff₀ hD]
  have e : (x / (1 - x) - x / (1 - x ^ 2) * (1 - Real.cos θ)) * (1 - 2 * x * Real.cos θ + x ^ 2) -
      (x * Real.cos θ - x ^ 2) =
      x * (1 - Real.cos θ) * ((1 + x) ^ 2 - (1 - 2 * x * Real.cos θ + x ^ 2)) / (1 - x ^ 2) := by
    field_simp
    ring
  have hnum : 0 ≤ x * (1 - Real.cos θ) * ((1 + x) ^ 2 - (1 - 2 * x * Real.cos θ + x ^ 2)) := by
    have : 0 ≤ (1 + x) ^ 2 - (1 - 2 * x * Real.cos θ + x ^ 2) := by nlinarith
    exact mul_nonneg (mul_nonneg hx0 (by linarith)) this
  have := div_nonneg hnum h2.le
  linarith

/-- `S_x(θ) ≥ −x/(1+x) + x(1−x)(1 + cos θ)/(1+x)³`: the symbol rises quadratically from its bottom. -/
theorem eulerSymbol_ge_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    -(x / (1 + x)) + x * (1 - x) / (1 + x) ^ 3 * (1 + Real.cos θ) ≤ eulerSymbol x θ := by
  have hD := eulerSymbol_denom_pos hx1 θ hx0
  have h1 : 0 < 1 + x := by linarith
  have hc := Real.cos_le_one θ
  have hc' := Real.neg_one_le_cos θ
  rw [eulerSymbol, le_div_iff₀ hD]
  have e : (x * Real.cos θ - x ^ 2) - (-(x / (1 + x)) + x * (1 - x) / (1 + x) ^ 3 *
      (1 + Real.cos θ)) * (1 - 2 * x * Real.cos θ + x ^ 2) =
      x * (1 - x) * (1 + Real.cos θ) * ((1 + x) ^ 2 - (1 - 2 * x * Real.cos θ + x ^ 2)) /
        (1 + x) ^ 3 := by
    field_simp
    ring
  have hnum : 0 ≤ x * (1 - x) * (1 + Real.cos θ) *
      ((1 + x) ^ 2 - (1 - 2 * x * Real.cos θ + x ^ 2)) := by
    have : 0 ≤ (1 + x) ^ 2 - (1 - 2 * x * Real.cos θ + x ^ 2) := by nlinarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hx0 (by linarith)) (by linarith)) this
  have := div_nonneg hnum (by positivity : (0 : ℝ) ≤ (1 + x) ^ 3)
  linarith

/-- `1 − cos(a + b) ≤ 2(1 − cos a) + 2(1 − cos b)`: half-angle sines are subadditive. -/
theorem one_sub_cos_add_le (a b : ℝ) :
    1 - Real.cos (a + b) ≤ 2 * (1 - Real.cos a) + 2 * (1 - Real.cos b) := by
  have half : ∀ y : ℝ, 1 - Real.cos y = 2 * Real.sin (y / 2) ^ 2 := fun y => by
    have h := Real.cos_sq (y / 2)
    rw [show 2 * (y / 2) = y by ring] at h
    have := Real.sin_sq_add_cos_sq (y / 2)
    linarith
  have ha := half a
  have hb := half b
  have hab := half (a + b)
  rw [ha, hb, hab, show (a + b) / 2 = a / 2 + b / 2 by ring, Real.sin_add]
  have h1 := Real.sin_sq_add_cos_sq (a / 2)
  have h2 := Real.sin_sq_add_cos_sq (b / 2)
  nlinarith [sq_nonneg (Real.sin (a / 2) * Real.cos (b / 2) - Real.cos (a / 2) * Real.sin (b / 2)),
    sq_nonneg (Real.cos (a / 2)), sq_nonneg (Real.cos (b / 2)), sq_nonneg (Real.sin (a / 2)),
    sq_nonneg (Real.sin (b / 2))]

/-! ### 2. The integer-grid tower cone -/

/-- The deviations `(A − W)/‖c‖²` on the cone blind at every integer `n ≥ 2` that is not a power of a
prime of `P`. -/
def gridTowerDeviations (P : Finset ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn ({n | 2 ≤ n} \ towerNodes P) c ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem gridTowerDeviations_subset (P : Finset ℕ) : gridTowerDeviations P ⊆ towerDeviations P := by
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  exact ⟨c, hc, fun j hj => hb j ⟨j.2, hj.2⟩, hpos, rfl⟩

/-- **The tower spectral identity**: `π(A − W) = ∫ G_c Σ_{r∈P} log r · S_{x_r}(t log r)`. -/
theorem pi_mul_towerSide_eq {c : WeilTestFn →₀ ℝ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hb : BlindOn (primePowerNodes \ towerNodes P) c) :
    π * (nodeArchEnergy c - weilEnergy c) = ∫ t, combinationSpectralDensity c t *
      ∑ r ∈ P, Real.log r * eulerSymbol (Real.sqrt r)⁻¹ (t * Real.log r) := by
  have hK : ∀ p ∈ P, ∀ k, nodeBound c ≤ k → nodeAt c (p ^ (k + 1)) = 0 :=
    fun p hp k hk => nodeAt_pow_eq_zero (hP p hp).two_le hk
  rw [nodeArchEnergy_sub_weilEnergy_eq_towers hP hb hK, Finset.mul_sum]
  have hint : ∀ r ∈ P, Integrable fun t => combinationSpectralDensity c t *
      (Real.log r * eulerSymbol (Real.sqrt r)⁻¹ (t * Real.log r)) := by
    intro r hr
    have hsq : 1 < Real.sqrt r := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (hP r hr).one_lt)
    have hx0 : 0 ≤ (Real.sqrt r)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hx1 : (Real.sqrt r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsq
    have hcos : Continuous fun t : ℝ => Real.cos (t * Real.log r) :=
      Real.continuous_cos.comp (continuous_id.mul continuous_const)
    have hcont : Continuous fun t : ℝ => Real.log r * eulerSymbol (Real.sqrt r)⁻¹ (t * Real.log r) :=
      continuous_const.mul (((continuous_const.mul hcos).sub continuous_const).div
        ((continuous_const.sub (continuous_const.mul hcos)).add continuous_const)
        fun t => (eulerSymbol_denom_pos hx1 _ hx0).ne')
    refine (integrable_combinationSpectralDensity c).mul_bdd
      (c := |Real.log r| * max ((Real.sqrt r)⁻¹ / (1 + (Real.sqrt r)⁻¹))
        ((Real.sqrt r)⁻¹ / (1 - (Real.sqrt r)⁻¹))) hcont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]
    constructor
    · linarith [neg_le_eulerSymbol hx0 hx1 (t * Real.log r),
        le_max_left ((Real.sqrt r)⁻¹ / (1 + (Real.sqrt r)⁻¹)) ((Real.sqrt r)⁻¹ / (1 - (Real.sqrt r)⁻¹))]
    · linarith [eulerSymbol_le hx0 hx1 (t * Real.log r),
        le_max_right ((Real.sqrt r)⁻¹ / (1 + (Real.sqrt r)⁻¹)) ((Real.sqrt r)⁻¹ / (1 - (Real.sqrt r)⁻¹))]
  rw [show (fun t => combinationSpectralDensity c t *
      ∑ r ∈ P, Real.log r * eulerSymbol (Real.sqrt r)⁻¹ (t * Real.log r)) =
      fun t => ∑ r ∈ P, combinationSpectralDensity c t *
        (Real.log r * eulerSymbol (Real.sqrt r)⁻¹ (t * Real.log r)) from
      funext fun t => Finset.mul_sum _ _ _, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [show (fun t => combinationSpectralDensity c t *
      (Real.log r * eulerSymbol (Real.sqrt r)⁻¹ (t * Real.log r))) =
      fun t => Real.log r * (combinationSpectralDensity c t *
        eulerSymbol (Real.sqrt r)⁻¹ (t * Real.log r)) from funext fun t => by ring,
    integral_const_mul, integral_spectral_mul_eulerSymbol c (hP r hr).two_le (hK r hr)]
  ring

/-- **Blindness at `pq` kills one cosine moment**: `∫ G_c(t) cos(t log p + t log q) dt = 0`. -/
theorem integral_spectral_mul_cos_composite_eq_zero {c : WeilTestFn →₀ ℝ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hb : BlindOn ({n | 2 ≤ n} \ towerNodes P) c) {p q : ℕ} (hp : p ∈ P)
    (hq : q ∈ P) (hpq : p ≠ q) :
    ∫ t, combinationSpectralDensity c t * Real.cos (t * Real.log p + t * Real.log q) = 0 := by
  have hp2 := (hP p hp).two_le
  have hq2 := (hP q hq).two_le
  have h2 : 2 ≤ p * q := by nlinarith
  have hco : Nat.Coprime p q := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  have hnot : p * q ∉ towerNodes P := by
    rintro ⟨r, hr, k, hk⟩
    exact not_isPrimePow_mul_of_coprime hco hp2 hq2 (hk ▸ (hP r hr).isPrimePow.pow (by omega))
  have hlog : ∀ t : ℝ, t * Real.log p + t * Real.log q = t * Real.log ((p * q : ℕ) : ℝ) := by
    intro t; push_cast; rw [Real.log_mul (by positivity) (by positivity)]; ring
  simp_rw [hlog]
  rw [integral_combinationSpectralDensity_mul_cos_log c h2, hb ⟨p * q, h2⟩ ⟨h2, hnot⟩, mul_zero]

/-! ### 3. The composite charge of the towers -/

/-- `x/(1 − x) = 1/(√r − 1)` and `x/(1 + x) = 1/(√r + 1)` for `x = r^{−1/2}`. -/
theorem towerPrices_eq_sum {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    towerPriceAbove P = 2 * ∑ r ∈ P, Real.log r * ((Real.sqrt r)⁻¹ / (1 - (Real.sqrt r)⁻¹)) ∧
      towerPriceBelow P = 2 * ∑ r ∈ P, Real.log r * ((Real.sqrt r)⁻¹ / (1 + (Real.sqrt r)⁻¹)) := by
  have hsq : ∀ r ∈ P, 1 < Real.sqrt r := fun r hr => by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (hP r hr).one_lt)
  constructor
  · rw [towerPriceAbove, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [mul_left_comm, inv_sqrt_div_one_sub (hsq r hr)]; ring
  · rw [towerPriceBelow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [mul_left_comm, inv_sqrt_div_one_add (hsq r hr)]; ring

/-- **Whole towers read the composite node: the supremum drops.** -/
theorem gridTowerDeviation_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {p q : ℕ} (hp : p ∈ P)
    (hq : q ∈ P) (hpq : p ≠ q) {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hcp : c₀ ≤ Real.log p * ((Real.sqrt p)⁻¹ / (1 - (Real.sqrt p)⁻¹ ^ 2)))
    (hcq : c₀ ≤ Real.log q * ((Real.sqrt q)⁻¹ / (1 - (Real.sqrt q)⁻¹ ^ 2))) :
    ∀ x ∈ gridTowerDeviations P, x ≤ towerPriceAbove P - c₀ := by
  classical
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have hbPP : BlindOn (primePowerNodes \ towerNodes P) c := fun j hj => hb j ⟨j.2, hj.2⟩
  set G := combinationSpectralDensity c
  have hG := integrable_combinationSpectralDensity c
  have hGn := combinationSpectralDensity_nonneg hc
  set x : ℕ → ℝ := fun r => (Real.sqrt r)⁻¹ with hxdef
  have hsq : ∀ r ∈ P, 1 < Real.sqrt r := fun r hr => by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (hP r hr).one_lt)
  have hx0 : ∀ r, 0 ≤ x r := fun r => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hx1 : ∀ r ∈ P, x r < 1 := fun r hr => inv_lt_one_of_one_lt₀ (hsq r hr)
  have hl : ∀ r ∈ P, 0 ≤ Real.log r := fun r hr => Real.log_nonneg (by exact_mod_cast (hP r hr).one_lt.le)
  -- the bound `B` of the dual certificate
  set B : ℝ := ∑ r ∈ P, Real.log r * (x r / (1 - x r)) - c₀ / 2 with hB
  have hpt : ∀ t : ℝ, (∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) -
      c₀ / 2 * Real.cos (t * Real.log p + t * Real.log q) ≤ B := by
    intro t
    set θ₁ := t * Real.log p
    set θ₂ := t * Real.log q
    have hpP : P = insert p (insert q ((P.erase p).erase q)) := by
      rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩), Finset.insert_erase hp]
    have hpn : p ∉ insert q ((P.erase p).erase q) := by
      simp [hpq]
    have hqn : q ∉ (P.erase p).erase q := by simp
    have hsplit : ∀ F : ℕ → ℝ, ∑ r ∈ P, F r = F p + F q + ∑ r ∈ (P.erase p).erase q, F r := by
      intro F
      conv_lhs => rw [hpP]
      rw [Finset.sum_insert hpn, Finset.sum_insert hqn]; ring
    rw [hsplit (fun r => Real.log r * eulerSymbol (x r) (t * Real.log r)), hB,
      hsplit (fun r => Real.log r * (x r / (1 - x r)))]
    have hrest : ∑ r ∈ (P.erase p).erase q, Real.log r * eulerSymbol (x r) (t * Real.log r) ≤
        ∑ r ∈ (P.erase p).erase q, Real.log r * (x r / (1 - x r)) := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hrP : r ∈ P := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
      exact mul_le_mul_of_nonneg_left (eulerSymbol_le (hx0 r) (hx1 r hrP) _) (hl r hrP)
    have hSp := mul_le_mul_of_nonneg_left (eulerSymbol_le_sub (hx0 p) (hx1 p hp) θ₁) (hl p hp)
    have hSq := mul_le_mul_of_nonneg_left (eulerSymbol_le_sub (hx0 q) (hx1 q hq) θ₂) (hl q hq)
    have hcos := one_sub_cos_add_le θ₁ θ₂
    have h1 : 0 ≤ 1 - Real.cos θ₁ := by linarith [Real.cos_le_one θ₁]
    have h2 : 0 ≤ 1 - Real.cos θ₂ := by linarith [Real.cos_le_one θ₂]
    have e1 := mul_le_mul_of_nonneg_right hcp h1
    have e2 := mul_le_mul_of_nonneg_right hcq h2
    nlinarith
  -- integrate the certificate
  have hint : ∀ r ∈ P, Integrable fun t => G t * (Real.log r * eulerSymbol (x r) (t * Real.log r)) := by
    intro r hr
    have hcos : Continuous fun t : ℝ => Real.cos (t * Real.log r) :=
      Real.continuous_cos.comp (continuous_id.mul continuous_const)
    have hcont : Continuous fun t : ℝ => Real.log r * eulerSymbol (x r) (t * Real.log r) :=
      continuous_const.mul (((continuous_const.mul hcos).sub continuous_const).div
        ((continuous_const.sub (continuous_const.mul hcos)).add continuous_const)
        fun t => (eulerSymbol_denom_pos (hx1 r hr) _ (hx0 r)).ne')
    refine hG.mul_bdd (c := |Real.log r| * max (x r / (1 + x r)) (x r / (1 - x r)))
      hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]
    constructor
    · linarith [neg_le_eulerSymbol (hx0 r) (hx1 r hr) (t * Real.log r),
        le_max_left (x r / (1 + x r)) (x r / (1 - x r))]
    · linarith [eulerSymbol_le (hx0 r) (hx1 r hr) (t * Real.log r),
        le_max_right (x r / (1 + x r)) (x r / (1 - x r))]
  have hsumint : Integrable fun t => G t * ∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r) := by
    have := integrable_finsetSum P hint
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Finset.mul_sum]
  have hcosint : Integrable fun t => G t * Real.cos (t * Real.log p + t * Real.log q) :=
    hG.mul_bdd (c := 1) ((Real.continuous_cos.comp ((continuous_id.mul continuous_const).add
      (continuous_id.mul continuous_const))).aestronglyMeasurable)
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hid := pi_mul_towerSide_eq hP hbPP
  have hzero := integral_spectral_mul_cos_composite_eq_zero hP hb hp hq hpq
  have hmass := integral_combinationSpectralDensity c
  have hcert : π * (nodeArchEnergy c - weilEnergy c) ≤ ∫ t, G t * B := by
    calc π * (nodeArchEnergy c - weilEnergy c)
        = ∫ t, G t * ((∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) -
            c₀ / 2 * Real.cos (t * Real.log p + t * Real.log q)) := by
          rw [hid]
          have e : (fun t => G t * ((∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) -
              c₀ / 2 * Real.cos (t * Real.log p + t * Real.log q))) =
              fun t => G t * (∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) -
                c₀ / 2 * (G t * Real.cos (t * Real.log p + t * Real.log q)) := by
            funext t; ring
          rw [e, integral_sub hsumint (hcosint.const_mul _), integral_const_mul, hzero, mul_zero,
            sub_zero]
      _ ≤ ∫ t, G t * B := integral_mono ((hsumint.sub (hcosint.const_mul (c₀ / 2))).congr
            (Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring))
          (hG.mul_const _) fun t => mul_le_mul_of_nonneg_left (hpt t) (hGn t)
  rw [integral_mul_const, hmass] at hcert
  rw [div_le_iff₀ hpos, (towerPrices_eq_sum hP).1]
  have : nodeArchEnergy c - weilEnergy c ≤ 2 * B * massOf c := by
    have hπ := Real.pi_pos
    nlinarith
  rw [hB] at this
  linarith

/-- **Whole towers read the composite node: the infimum rises.** -/
theorem gridTowerDeviation_ge {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {p q : ℕ} (hp : p ∈ P)
    (hq : q ∈ P) (hpq : p ≠ q) {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hcp : c₀ ≤ Real.log p * ((Real.sqrt p)⁻¹ * (1 - (Real.sqrt p)⁻¹) / (1 + (Real.sqrt p)⁻¹) ^ 3))
    (hcq : c₀ ≤ Real.log q * ((Real.sqrt q)⁻¹ * (1 - (Real.sqrt q)⁻¹) / (1 + (Real.sqrt q)⁻¹) ^ 3)) :
    ∀ x ∈ gridTowerDeviations P, -towerPriceBelow P + c₀ ≤ x := by
  classical
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have hbPP : BlindOn (primePowerNodes \ towerNodes P) c := fun j hj => hb j ⟨j.2, hj.2⟩
  set G := combinationSpectralDensity c
  have hG := integrable_combinationSpectralDensity c
  have hGn := combinationSpectralDensity_nonneg hc
  set x : ℕ → ℝ := fun r => (Real.sqrt r)⁻¹ with hxdef
  have hsq : ∀ r ∈ P, 1 < Real.sqrt r := fun r hr => by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (hP r hr).one_lt)
  have hx0 : ∀ r, 0 ≤ x r := fun r => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hx1 : ∀ r ∈ P, x r < 1 := fun r hr => inv_lt_one_of_one_lt₀ (hsq r hr)
  have hl : ∀ r ∈ P, 0 ≤ Real.log r := fun r hr => Real.log_nonneg (by exact_mod_cast (hP r hr).one_lt.le)
  set B : ℝ := -∑ r ∈ P, Real.log r * (x r / (1 + x r)) + c₀ / 2 with hB
  have hpt : ∀ t : ℝ, B ≤ (∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) +
      c₀ / 2 * Real.cos (t * Real.log p + t * Real.log q) := by
    intro t
    set θ₁ := t * Real.log p
    set θ₂ := t * Real.log q
    have hpP : P = insert p (insert q ((P.erase p).erase q)) := by
      rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩), Finset.insert_erase hp]
    have hpn : p ∉ insert q ((P.erase p).erase q) := by simp [hpq]
    have hqn : q ∉ (P.erase p).erase q := by simp
    have hsplit : ∀ F : ℕ → ℝ, ∑ r ∈ P, F r = F p + F q + ∑ r ∈ (P.erase p).erase q, F r := by
      intro F
      conv_lhs => rw [hpP]
      rw [Finset.sum_insert hpn, Finset.sum_insert hqn]; ring
    rw [hsplit (fun r => Real.log r * eulerSymbol (x r) (t * Real.log r)), hB,
      hsplit (fun r => Real.log r * (x r / (1 + x r)))]
    have hrest : -∑ r ∈ (P.erase p).erase q, Real.log r * (x r / (1 + x r)) ≤
        ∑ r ∈ (P.erase p).erase q, Real.log r * eulerSymbol (x r) (t * Real.log r) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun r hr => ?_
      have hrP : r ∈ P := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
      have := mul_le_mul_of_nonneg_left (neg_le_eulerSymbol (hx0 r) (hx1 r hrP) (t * Real.log r))
        (hl r hrP)
      linarith
    have hSp := mul_le_mul_of_nonneg_left (eulerSymbol_ge_add (hx0 p) (hx1 p hp) θ₁) (hl p hp)
    have hSq := mul_le_mul_of_nonneg_left (eulerSymbol_ge_add (hx0 q) (hx1 q hq) θ₂) (hl q hq)
    -- the composite cosine at the joint bottom `θ₁ ≡ θ₂ ≡ π`
    have hcos := one_sub_cos_add_le (θ₁ + π) (θ₂ + π)
    rw [show θ₁ + π + (θ₂ + π) = θ₁ + θ₂ + 2 * π by ring, Real.cos_add_two_pi, Real.cos_add_pi,
      Real.cos_add_pi] at hcos
    have h1 : 0 ≤ 1 + Real.cos θ₁ := by linarith [Real.neg_one_le_cos θ₁]
    have h2 : 0 ≤ 1 + Real.cos θ₂ := by linarith [Real.neg_one_le_cos θ₂]
    have e1 := mul_le_mul_of_nonneg_right hcp h1
    have e2 := mul_le_mul_of_nonneg_right hcq h2
    nlinarith
  have hint : ∀ r ∈ P, Integrable fun t => G t * (Real.log r * eulerSymbol (x r) (t * Real.log r)) := by
    intro r hr
    have hcos : Continuous fun t : ℝ => Real.cos (t * Real.log r) :=
      Real.continuous_cos.comp (continuous_id.mul continuous_const)
    have hcont : Continuous fun t : ℝ => Real.log r * eulerSymbol (x r) (t * Real.log r) :=
      continuous_const.mul (((continuous_const.mul hcos).sub continuous_const).div
        ((continuous_const.sub (continuous_const.mul hcos)).add continuous_const)
        fun t => (eulerSymbol_denom_pos (hx1 r hr) _ (hx0 r)).ne')
    refine hG.mul_bdd (c := |Real.log r| * max (x r / (1 + x r)) (x r / (1 - x r)))
      hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]
    constructor
    · linarith [neg_le_eulerSymbol (hx0 r) (hx1 r hr) (t * Real.log r),
        le_max_left (x r / (1 + x r)) (x r / (1 - x r))]
    · linarith [eulerSymbol_le (hx0 r) (hx1 r hr) (t * Real.log r),
        le_max_right (x r / (1 + x r)) (x r / (1 - x r))]
  have hsumint : Integrable fun t => G t * ∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r) := by
    have := integrable_finsetSum P hint
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [Finset.mul_sum]
  have hcosint : Integrable fun t => G t * Real.cos (t * Real.log p + t * Real.log q) :=
    hG.mul_bdd (c := 1) ((Real.continuous_cos.comp ((continuous_id.mul continuous_const).add
      (continuous_id.mul continuous_const))).aestronglyMeasurable)
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hid := pi_mul_towerSide_eq hP hbPP
  have hzero := integral_spectral_mul_cos_composite_eq_zero hP hb hp hq hpq
  have hmass := integral_combinationSpectralDensity c
  have hcert : ∫ t, G t * B ≤ π * (nodeArchEnergy c - weilEnergy c) := by
    calc ∫ t, G t * B
        ≤ ∫ t, G t * ((∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) +
            c₀ / 2 * Real.cos (t * Real.log p + t * Real.log q)) :=
          integral_mono (hG.mul_const _) ((hsumint.add (hcosint.const_mul (c₀ / 2))).congr
            (Eventually.of_forall fun t => by simp only [Pi.add_apply]; ring))
            fun t => mul_le_mul_of_nonneg_left (hpt t) (hGn t)
      _ = π * (nodeArchEnergy c - weilEnergy c) := by
          rw [hid]
          have e : (fun t => G t * ((∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) +
              c₀ / 2 * Real.cos (t * Real.log p + t * Real.log q))) =
              fun t => G t * (∑ r ∈ P, Real.log r * eulerSymbol (x r) (t * Real.log r)) +
                c₀ / 2 * (G t * Real.cos (t * Real.log p + t * Real.log q)) := by
            funext t; ring
          rw [e, integral_add hsumint (hcosint.const_mul _), integral_const_mul, hzero, mul_zero,
            add_zero]
  rw [integral_mul_const, hmass] at hcert
  rw [le_div_iff₀ hpos, (towerPrices_eq_sum hP).2]
  have : 2 * B * massOf c ≤ nodeArchEnergy c - weilEnergy c := by
    have hπ := Real.pi_pos
    nlinarith
  rw [hB] at this
  linarith

/-- **For the towers of `2` and `3` blindness at the composites costs at least `9/10`.** On the
integer-grid tower cone every deviation is at most `2 log 2/(√2 − 1) + 2 log 3/(√3 − 1) − 9/10`, while
on the prime-power cone the supremum is `2 log 2/(√2 − 1) + 2 log 3/(√3 − 1)`. -/
theorem gridTowerDeviation_two_three_le :
    ∀ x ∈ gridTowerDeviations {2, 3},
      x ≤ 2 * Real.log 2 / (Real.sqrt 2 - 1) + 2 * Real.log 3 / (Real.sqrt 3 - 1) - 9 / 10 := by
  intro x hx
  have h := gridTowerDeviation_le primes_two_three (p := 2) (q := 3) (by simp) (by simp)
    (by norm_num) (c₀ := 9 / 10) (by norm_num) ?_ ?_ x hx
  · rwa [towerPriceAbove, Finset.sum_pair (by norm_num), Nat.cast_ofNat, Nat.cast_ofNat] at h
  · have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 2 := by positivity
    have e : Real.log 2 * ((Real.sqrt 2)⁻¹ / (1 - (Real.sqrt 2)⁻¹ ^ 2)) = 2 * atomTwo := by
      rw [atomTwo, inv_pow, hs]; field_simp; ring
    push_cast; rw [e]; linarith [atomTwo_near.1]
  · have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 3 := by positivity
    have e : Real.log 3 * ((Real.sqrt 3)⁻¹ / (1 - (Real.sqrt 3)⁻¹ ^ 2)) = 3 / 2 * atomThree := by
      rw [atomThree, inv_pow, hs]; field_simp; ring
    push_cast; rw [e]; linarith [atomThree_near.1]

end

end GaloisForLFunctions.BiScaleUncertainty
