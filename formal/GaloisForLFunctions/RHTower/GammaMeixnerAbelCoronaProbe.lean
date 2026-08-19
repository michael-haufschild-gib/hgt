import GaloisForLFunctions.RHTower.PrimeLogZetaAbelPole
import GaloisForLFunctions.RHTower.WeightedEulerCoefficientSpaces

/-!
# The Gamma--Meixner Abel family detects the Mertens corona class

For `θ > 0` the Gamma--Meixner shape kernel is

```text
w_θ(p) = cosh(2 log p)^(-θ/2)
```

and the normalised Gamma-shape Abel functional on prime coefficient fields is

```text
L_θ(b) = θ · ∑_p (log p)/p · w_θ(p) · b_p .
```

This file proves the card's chain:

* `meixnerShape_factorization` — the exact prime factorization
  `w_θ(p) = 2^(θ/2) p^(-θ) (1 + p^(-4))^(-θ/2)`;
* `meixnerShape_le`, `meixnerShape_ge` — the two-sided comparison with `p^(-θ)`, uniform in `p`;
* `abs_gammaShapeAbelFunctional_le` — `sup_{0<θ≤1} ‖L_θ‖_{M_log^*} < ∞`;
* `tendsto_gammaShapeAbelFunctional_vanishingTail` — `L_θ(b) → 0` for every `b` in the
  vanishing-tail layer `M_0`;
* `tendsto_gammaShapeAbelFunctional_unit` — `L_θ(1) → 1` on the actual Euler unit field;
* `tendsto_gammaShapeAbelFunctional_unit_add` — hence `L_θ(1 + b) → 1` for every `b ∈ M_0`;
* `meixnerShape_memVanishingTailLayer` together with the corpus's
  `unitField_not_memVanishingTailLayer` — for every fixed positive shape the kernel lies in the
  vanishing-tail layer while the unit field does not, so the boundary passage `θ → 0` is
  genuinely singular.

Every weak-star cluster point of `(L_θ)` therefore annihilates `M_0` and evaluates the Mertens
corona coset `[1]` as one.

The analytic input is `RHTower.tendsto_mul_primeLogZeta` (the Abelian pole of the prime log-zeta
function, from Mertens' first theorem) together with the general Abelian bound
`RHTower.summable_and_mul_tsum_weightedDirichlet_le`.
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The Gamma--Meixner shape kernel -/

/-- The Gamma--Meixner shape kernel `w_θ(p) = cosh(2 log p)^(-θ/2)`. -/
def meixnerShape (θ : ℝ) (n : ℕ) : ℝ := Real.cosh (2 * Real.log n) ^ (-θ / 2)

theorem meixnerShape_pos (θ : ℝ) (n : ℕ) : 0 < meixnerShape θ n :=
  Real.rpow_pos_of_pos (Real.cosh_pos _) _

theorem cosh_two_mul_log {x : ℝ} (hx : 0 < x) :
    Real.cosh (2 * Real.log x) = x ^ (2 : ℝ) * (1 + x ^ (-(4 : ℝ))) / 2 := by
  have h1 : Real.exp (2 * Real.log x) = x ^ (2 : ℝ) := by
    rw [Real.rpow_def_of_pos hx]
    ring_nf
  have h2 : Real.exp (-(2 * Real.log x)) = x ^ (-(2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hx]
    ring_nf
  have h3 : x ^ (2 : ℝ) * x ^ (-(4 : ℝ)) = x ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [Real.cosh_eq, h1, h2]
  rw [show x ^ (2 : ℝ) * (1 + x ^ (-(4 : ℝ))) = x ^ (2 : ℝ) + x ^ (2 : ℝ) * x ^ (-(4 : ℝ)) by ring,
    h3]

/-- **The exact prime factorization of the Gamma--Meixner kernel.** -/
theorem meixnerShape_factorization (θ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    meixnerShape θ n
      = 2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ) * (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-θ / 2) := by
  have hx : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hpow : (0 : ℝ) ≤ ((n : ℝ)) ^ (2 : ℝ) := (Real.rpow_pos_of_pos hx _).le
  have hone : (0 : ℝ) ≤ 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by positivity
  rw [meixnerShape, cosh_two_mul_log hx]
  rw [Real.div_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2)]
  rw [Real.mul_rpow hpow hone]
  have hsq : (((n : ℝ)) ^ (2 : ℝ)) ^ (-θ / 2) = ((n : ℝ)) ^ (-θ) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    ring
  have htwo : (2 : ℝ) ^ (-θ / 2) = ((2 : ℝ) ^ (θ / 2))⁻¹ := by
    rw [show (-θ / 2 : ℝ) = -(θ / 2) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsq, htwo]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (θ / 2) := Real.rpow_pos_of_pos (by norm_num) _
  field_simp

theorem meixnerShape_le (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (hn : 1 ≤ n) :
    meixnerShape θ n ≤ 2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ) := by
  have hx : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  rw [meixnerShape_factorization θ hn]
  have hquartpos : (0 : ℝ) < ((n : ℝ)) ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hbase : (1 : ℝ) ≤ 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by linarith
  have hle : (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-θ / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hbase ?_
    linarith
  have hpos : (0 : ℝ) ≤ 2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ) := by positivity
  nlinarith [hpos]

theorem meixnerShape_ge (θ : ℝ) (hθ : 0 ≤ θ) {n : ℕ} (hn : 2 ≤ n) :
    (17 / 16 : ℝ) ^ (-θ / 2) * (2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ)) ≤ meixnerShape θ n := by
  have hn1 : 1 ≤ n := by omega
  have hx : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  rw [meixnerShape_factorization θ hn1]
  have hquart : ((n : ℝ)) ^ (-(4 : ℝ)) ≤ (1 / 16 : ℝ) := by
    have h : ((n : ℝ)) ^ (-(4 : ℝ)) ≤ (2 : ℝ) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
    have h2 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
      rw [show (-(4:ℝ)) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [h2] at h
    exact h
  have hbase : (1 : ℝ) + ((n : ℝ)) ^ (-(4 : ℝ)) ≤ 17 / 16 := by linarith
  have hquartpos : (0 : ℝ) < ((n : ℝ)) ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have hbase1 : (1 : ℝ) ≤ 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by linarith
  have hmono : (17 / 16 : ℝ) ^ (-θ / 2) ≤ (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-θ / 2) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hbase (by linarith)
  have hpos : (0 : ℝ) ≤ 2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ) := by positivity
  nlinarith [hpos]

theorem meixnerShape_le_one {θ : ℝ} (hθ : 0 ≤ θ) (n : ℕ) : meixnerShape θ n ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_cosh _) (by linarith)

/-! ## The Abel functional -/

/-- The normalized Gamma-shape Abel functional `L_θ(b) = θ ∑_p (log p)/p · w_θ(p) · b_p`. -/
def gammaShapeAbelFunctional (θ : ℝ) (b : ℕ → ℝ) : ℝ :=
  θ * ∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * b n

/-- The absolute prime-log weight of a coefficient field. -/
def primeLogAbsWeight (b : ℕ → ℝ) (n : ℕ) : ℝ := mertensPrimeWeight n * |b n|

theorem primeLogAbsWeight_zero (b : ℕ → ℝ) : primeLogAbsWeight b 0 = 0 := by
  simp [primeLogAbsWeight, mertensPrimeWeight]

theorem primeLogAbsWeight_nonneg (b : ℕ → ℝ) (n : ℕ) : 0 ≤ primeLogAbsWeight b n :=
  mul_nonneg (mertensPrimeWeight_nonneg n) (abs_nonneg _)

theorem weightPartialSum_primeLogAbsWeight (b : ℕ → ℝ) (N : ℕ) :
    weightPartialSum (primeLogAbsWeight b) N = primeLogMass b N := by
  rw [weightPartialSum, primeLogMass]
  simp only [primeLogAbsWeight, mertensPrimeWeight]
  rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega,
    Finset.sum_insert (by simp), Finset.sum_filter]
  simp

theorem primeLogMass_le_logAffine {b : ℕ → ℝ} {C : ℝ}
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) (N : ℕ) :
    primeLogMass b N ≤ max C 0 * (Real.log N + 1) := by
  have hK0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hCK : C ≤ max C 0 := le_max_left _ _
  rcases lt_or_ge N 2 with hN | hN
  · have hzero : primeLogMass b N = 0 := by
      rw [primeLogMass]
      refine Finset.sum_eq_zero fun n hn => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, hp⟩ := hn
      exact absurd hp (by
        have : n = 1 := by omega
        rw [this]
        exact Nat.not_prime_one)
    rw [hzero]
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    positivity
  · have hlogpos : 0 < Real.log N := log_cutoff_pos hN
    have hq := hC N hN
    rw [marcinkiewiczLogQuotient, div_le_iff₀ hlogpos] at hq
    calc primeLogMass b N ≤ C * Real.log N := hq
      _ ≤ max C 0 * Real.log N := mul_le_mul_of_nonneg_right hCK hlogpos.le
      _ ≤ max C 0 * (Real.log N + 1) := by nlinarith

theorem norm_gammaShapeTerm_le {θ : ℝ} (hθ : 0 ≤ θ) (b : ℕ → ℝ) (n : ℕ) :
    ‖mertensPrimeWeight n * meixnerShape θ n * b n‖
      ≤ 2 ^ (θ / 2) * (primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ)) := by
  rcases lt_or_ge n 1 with hn | hn
  · have hn0 : n = 0 := by omega
    simp [hn0, mertensPrimeWeight, primeLogAbsWeight]
  · have hw : 0 ≤ mertensPrimeWeight n := mertensPrimeWeight_nonneg n
    have hs := meixnerShape_le θ hθ hn
    have hspos := (meixnerShape_pos θ n).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hspos]
    calc mertensPrimeWeight n * meixnerShape θ n * |b n|
        ≤ mertensPrimeWeight n * (2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ)) * |b n| := by
          have := mul_le_mul_of_nonneg_left hs hw
          exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = 2 ^ (θ / 2) * (primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ)) := by
          rw [primeLogAbsWeight]
          ring

theorem summable_primeLogAbsWeight_rpow {θ : ℝ} (hθ : 0 < θ) {b : ℕ → ℝ} {C : ℝ}
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) :
    Summable (fun n : ℕ => primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ)) :=
  (summable_and_mul_tsum_weightedDirichlet_le (primeLogAbsWeight_zero b)
    (primeLogAbsWeight_nonneg b) (le_max_right C 0)
    (fun n => by
      rw [weightPartialSum_primeLogAbsWeight]
      exact primeLogMass_le_logAffine hC n) hθ).1

theorem mul_tsum_primeLogAbsWeight_rpow_le {θ : ℝ} (hθ : 0 < θ) {b : ℕ → ℝ} {C : ℝ}
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) :
    θ * (∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ)) ≤ max C 0 * (1 + θ) :=
  (summable_and_mul_tsum_weightedDirichlet_le (primeLogAbsWeight_zero b)
    (primeLogAbsWeight_nonneg b) (le_max_right C 0)
    (fun n => by
      rw [weightPartialSum_primeLogAbsWeight]
      exact primeLogMass_le_logAffine hC n) hθ).2

theorem summable_gammaShapeTerm {θ : ℝ} (hθ : 0 < θ) {b : ℕ → ℝ} {C : ℝ}
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) :
    Summable (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * b n) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_gammaShapeTerm_le hθ.le b n) ?_
  exact (summable_primeLogAbsWeight_rpow hθ hC).mul_left _

/-- **Uniform boundedness of the Abel family on the Marcinkiewicz layer.** -/
theorem abs_gammaShapeAbelFunctional_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    {b : ℕ → ℝ} {C : ℝ} (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) :
    |gammaShapeAbelFunctional θ b| ≤ 2 * Real.sqrt 2 * max C 0 := by
  have hsum := summable_gammaShapeTerm hθ0 hC
  have habs := summable_primeLogAbsWeight_rpow hθ0 hC
  have hK0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hstep : |∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * b n|
      ≤ 2 ^ (θ / 2) * ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ) := by
    have h1 : ‖∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * b n‖
        ≤ ∑' n : ℕ, ‖mertensPrimeWeight n * meixnerShape θ n * b n‖ :=
      norm_tsum_le_tsum_norm (by
        refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
          (fun n => norm_gammaShapeTerm_le hθ0.le b n) ?_
        exact habs.mul_left _)
    have h2 : (∑' n : ℕ, ‖mertensPrimeWeight n * meixnerShape θ n * b n‖)
        ≤ ∑' n : ℕ, 2 ^ (θ / 2) * (primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ)) := by
      refine Summable.tsum_le_tsum (fun n => norm_gammaShapeTerm_le hθ0.le b n) ?_ ?_
      · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
          (fun n => norm_gammaShapeTerm_le hθ0.le b n) ?_
        exact habs.mul_left _
      · exact habs.mul_left _
    rw [tsum_mul_left] at h2
    rw [Real.norm_eq_abs] at h1
    linarith
  have h2pow : (2 : ℝ) ^ (θ / 2) ≤ Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hbnd := mul_tsum_primeLogAbsWeight_rpow_le hθ0 hC
  have htsum_nonneg : 0 ≤ ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ) :=
    tsum_nonneg fun n => mul_nonneg (primeLogAbsWeight_nonneg b n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [gammaShapeAbelFunctional, abs_mul, abs_of_pos hθ0]
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (θ / 2) := Real.rpow_pos_of_pos (by norm_num) _
  calc θ * |∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * b n|
      ≤ θ * (2 ^ (θ / 2) * ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ)) :=
        mul_le_mul_of_nonneg_left hstep hθ0.le
    _ = 2 ^ (θ / 2) * (θ * ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-θ)) := by ring
    _ ≤ Real.sqrt 2 * (max C 0 * (1 + θ)) := by
        refine mul_le_mul h2pow hbnd (by positivity) (Real.sqrt_nonneg 2)
    _ ≤ 2 * Real.sqrt 2 * max C 0 := by
        have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hprod : (0 : ℝ) ≤ Real.sqrt 2 * max C 0 := mul_nonneg hs2 hK0
        nlinarith [mul_nonneg hprod (by linarith : (0 : ℝ) ≤ 1 - θ)]

/-! ## Additivity and the finite-gauge head -/

theorem gammaShapeAbelFunctional_add_of_summable {θ : ℝ} {b₁ b₂ : ℕ → ℝ}
    (h₁ : Summable (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * b₁ n))
    (h₂ : Summable (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * b₂ n)) :
    gammaShapeAbelFunctional θ (fun n => b₁ n + b₂ n)
      = gammaShapeAbelFunctional θ b₁ + gammaShapeAbelFunctional θ b₂ := by
  have hrw : ∀ n : ℕ, mertensPrimeWeight n * meixnerShape θ n * (b₁ n + b₂ n)
      = mertensPrimeWeight n * meixnerShape θ n * b₁ n
        + mertensPrimeWeight n * meixnerShape θ n * b₂ n := by
    intro n; ring
  rw [gammaShapeAbelFunctional, gammaShapeAbelFunctional, gammaShapeAbelFunctional]
  rw [show (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * (b₁ n + b₂ n))
      = fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * b₁ n
        + mertensPrimeWeight n * meixnerShape θ n * b₂ n from funext hrw]
  rw [Summable.tsum_add h₁ h₂]
  ring

theorem summable_gammaShapeTerm_head {θ : ℝ} (b : ℕ → ℝ) (P : ℕ) :
    Summable (fun n : ℕ =>
      mertensPrimeWeight n * meixnerShape θ n * primeCoefficientHead b P n) := by
  refine summable_of_ne_finset_zero (s := Finset.range (P + 1)) fun n hn => ?_
  have hlt : ¬ n < P + 1 := by simpa using hn
  have hP : P < n := by omega
  simp [primeCoefficientHead, hP]

theorem abs_gammaShapeAbelFunctional_head_le {θ : ℝ} (hθ : 0 < θ) (b : ℕ → ℝ) (P : ℕ) :
    |gammaShapeAbelFunctional θ (primeCoefficientHead b P)| ≤ θ * primeLogMass b P := by
  have hzero : ∀ n ∉ Finset.range (P + 1),
      mertensPrimeWeight n * meixnerShape θ n * primeCoefficientHead b P n = 0 := by
    intro n hn
    have hlt : ¬ n < P + 1 := by simpa using hn
    have hP : P < n := by omega
    simp [primeCoefficientHead, hP]
  rw [gammaShapeAbelFunctional, tsum_eq_sum hzero, abs_mul, abs_of_pos hθ]
  refine mul_le_mul_of_nonneg_left ?_ hθ.le
  have hterm : ∀ n ∈ Finset.range (P + 1),
      |mertensPrimeWeight n * meixnerShape θ n * primeCoefficientHead b P n|
        ≤ primeLogAbsWeight b n := by
    intro n hn
    have hnP : n ≤ P := by
      have := Finset.mem_range.mp hn
      omega
    have hhead : primeCoefficientHead b P n = b n := by
      simp [primeCoefficientHead, Nat.not_lt.mpr hnP]
    have hw : 0 ≤ mertensPrimeWeight n := mertensPrimeWeight_nonneg n
    have hspos := (meixnerShape_pos θ n).le
    rw [hhead, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hspos, primeLogAbsWeight]
    have hs1 := meixnerShape_le_one hθ.le n
    calc mertensPrimeWeight n * meixnerShape θ n * |b n|
        ≤ mertensPrimeWeight n * 1 * |b n| := by
          have := mul_le_mul_of_nonneg_left hs1 hw
          exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ = mertensPrimeWeight n * |b n| := by ring
  calc |∑ n ∈ Finset.range (P + 1),
        mertensPrimeWeight n * meixnerShape θ n * primeCoefficientHead b P n|
      ≤ ∑ n ∈ Finset.range (P + 1),
          |mertensPrimeWeight n * meixnerShape θ n * primeCoefficientHead b P n| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (P + 1), primeLogAbsWeight b n := Finset.sum_le_sum hterm
    _ = primeLogMass b P := by
        rw [← weightPartialSum_primeLogAbsWeight b P, weightPartialSum]
        congr 1
        ext n
        simp [Finset.mem_Icc, Finset.mem_range]

/-- **The Abel family annihilates the finite-gauge/vanishing-tail layer.** -/
theorem tendsto_gammaShapeAbelFunctional_vanishingTail {b : ℕ → ℝ}
    (hb : MemVanishingTailLayer b) :
    Tendsto (fun θ : ℝ => gammaShapeAbelFunctional θ b) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set ε' : ℝ := ε / (8 * Real.sqrt 2) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; positivity
  obtain ⟨P, hP⟩ := hb ε' hε'pos
  set M : ℝ := primeLogMass b P with hMdef
  have hM0 : 0 ≤ M := primeLogMass_nonneg b P
  set c : ℝ := min 1 (ε / (2 * (M + 1))) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    refine lt_min one_pos ?_
    positivity
  have hsplit : (fun n : ℕ => primeCoefficientHead b P n + primeCoefficientTail b P n) = b := by
    funext n
    simp only [primeCoefficientHead, primeCoefficientTail]
    split_ifs <;> ring
  filter_upwards [Ioo_mem_nhdsGT hcpos] with θ hθ
  obtain ⟨hθ0, hθc⟩ := hθ
  have hθ1 : θ ≤ 1 := le_trans hθc.le (min_le_left _ _)
  have hθM : θ < ε / (2 * (M + 1)) := lt_of_lt_of_le hθc (min_le_right _ _)
  have hhead_sum := summable_gammaShapeTerm_head (θ := θ) b P
  have htail_sum := summable_gammaShapeTerm hθ0 hP
  have hadd := gammaShapeAbelFunctional_add_of_summable hhead_sum htail_sum
  rw [hsplit] at hadd
  have hh := abs_gammaShapeAbelFunctional_head_le hθ0 b P
  have ht := abs_gammaShapeAbelFunctional_le hθ0 hθ1 hP
  rw [max_eq_left hε'pos.le] at ht
  have hbnd : |gammaShapeAbelFunctional θ b| ≤ θ * M + 2 * Real.sqrt 2 * ε' := by
    rw [hadd]
    exact le_trans (abs_add_le _ _) (add_le_add hh ht)
  have hfirst : θ * M < ε / 2 := by
    have hMle : θ * M ≤ θ * (M + 1) := by nlinarith
    have hpos : (0 : ℝ) < M + 1 := by linarith
    have hlt : θ * (M + 1) < (ε / (2 * (M + 1))) * (M + 1) :=
      mul_lt_mul_of_pos_right hθM hpos
    have heq : (ε / (2 * (M + 1))) * (M + 1) = ε / 2 := by
      have hne : (M + 1 : ℝ) ≠ 0 := by positivity
      field_simp
    linarith
  have hsecond : 2 * Real.sqrt 2 * ε' = ε / 4 := by
    rw [hε'def]
    have hne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2
    field_simp
    ring
  rw [Real.norm_eq_abs]
  linarith [hbnd, hfirst, hsecond]

/-! ## The unit limit on the actual Euler source -/

theorem tsum_mertensPrimeWeight_rpow {θ : ℝ} :
    (∑' n : ℕ, mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)) = primeLogZeta (1 + θ) := by
  rw [← tsum_primeLogIndicatorRpow (s := 1 + θ)]
  refine tsum_congr fun n => ?_
  rw [mertensPrimeWeight]
  by_cases hp : n.Prime
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    rw [if_pos hp, if_pos hp, div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ),
      show -(1 + θ) = -1 + -θ by ring, Real.rpow_add hn0]
    ring
  · rw [if_neg hp, if_neg hp, zero_mul]

theorem summable_mertensPrimeWeight_rpow {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)) := by
  obtain ⟨C, hC⟩ := unitField_memMarcinkiewiczLogLayer
  have h := summable_primeLogAbsWeight_rpow hθ hC
  refine h.congr fun n => ?_
  rw [primeLogAbsWeight]
  norm_num

theorem summable_gammaShapeTerm_unit {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := unitField_memMarcinkiewiczLogLayer
  exact summable_gammaShapeTerm hθ hC

theorem gammaShapeAbelFunctional_unit_le {θ : ℝ} (hθ : 0 < θ) :
    gammaShapeAbelFunctional θ (fun _ => (1 : ℝ))
      ≤ 2 ^ (θ / 2) * (θ * primeLogZeta (1 + θ)) := by
  have hterm : ∀ n : ℕ, mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ)
      ≤ 2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)) := by
    intro n
    rcases lt_or_ge n 1 with hn | hn
    · have hn0 : n = 0 := by omega
      simp [hn0, mertensPrimeWeight]
    · have hw : 0 ≤ mertensPrimeWeight n := mertensPrimeWeight_nonneg n
      have hs := meixnerShape_le θ hθ.le hn
      calc mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ)
          = mertensPrimeWeight n * meixnerShape θ n := by ring
        _ ≤ mertensPrimeWeight n * (2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ)) :=
            mul_le_mul_of_nonneg_left hs hw
        _ = 2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)) := by ring
  have hle : (∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ))
      ≤ ∑' n : ℕ, 2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)) :=
    Summable.tsum_le_tsum hterm (summable_gammaShapeTerm_unit hθ)
      ((summable_mertensPrimeWeight_rpow hθ).mul_left _)
  rw [tsum_mul_left, tsum_mertensPrimeWeight_rpow] at hle
  rw [gammaShapeAbelFunctional]
  calc θ * ∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ)
      ≤ θ * (2 ^ (θ / 2) * primeLogZeta (1 + θ)) := mul_le_mul_of_nonneg_left hle hθ.le
    _ = 2 ^ (θ / 2) * (θ * primeLogZeta (1 + θ)) := by ring

theorem gammaShapeAbelFunctional_unit_ge {θ : ℝ} (hθ : 0 < θ) :
    (17 / 16 : ℝ) ^ (-θ / 2) * (2 ^ (θ / 2) * (θ * primeLogZeta (1 + θ)))
      ≤ gammaShapeAbelFunctional θ (fun _ => (1 : ℝ)) := by
  have hterm : ∀ n : ℕ,
      (17 / 16 : ℝ) ^ (-θ / 2) * (2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)))
        ≤ mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ) := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · have hw : mertensPrimeWeight n = 0 := by
        rw [mertensPrimeWeight, if_neg]
        intro hp
        exact absurd hp.two_le (by omega)
      simp [hw]
    · have hw : 0 ≤ mertensPrimeWeight n := mertensPrimeWeight_nonneg n
      have hs := meixnerShape_ge θ hθ.le hn
      calc (17 / 16 : ℝ) ^ (-θ / 2) *
            (2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)))
          = mertensPrimeWeight n *
              ((17 / 16 : ℝ) ^ (-θ / 2) * (2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ))) := by ring
        _ ≤ mertensPrimeWeight n * meixnerShape θ n := mul_le_mul_of_nonneg_left hs hw
        _ = mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ) := by ring
  have hge : (∑' n : ℕ, (17 / 16 : ℝ) ^ (-θ / 2) *
        (2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ))))
      ≤ ∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ) :=
    Summable.tsum_le_tsum hterm
      (((summable_mertensPrimeWeight_rpow hθ).mul_left _).mul_left _)
      (summable_gammaShapeTerm_unit hθ)
  rw [tsum_mul_left, tsum_mul_left, tsum_mertensPrimeWeight_rpow] at hge
  rw [gammaShapeAbelFunctional]
  calc (17 / 16 : ℝ) ^ (-θ / 2) * (2 ^ (θ / 2) * (θ * primeLogZeta (1 + θ)))
      = θ * ((17 / 16 : ℝ) ^ (-θ / 2) * (2 ^ (θ / 2) * primeLogZeta (1 + θ))) := by ring
    _ ≤ θ * ∑' n : ℕ, mertensPrimeWeight n * meixnerShape θ n * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hge hθ.le

theorem tendsto_const_rpow_half {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Tendsto (fun θ : ℝ => a ^ (r * θ)) (nhds 0) (nhds 1) := by
  have hfun : (fun θ : ℝ => a ^ (r * θ)) = fun θ : ℝ => Real.exp (Real.log a * (r * θ)) := by
    funext θ
    rw [Real.rpow_def_of_pos ha]
  have hcont : Continuous (fun θ : ℝ => a ^ (r * θ)) := by
    rw [hfun]
    fun_prop
  have h := hcont.tendsto 0
  simpa using h

/-- **The Abel family evaluates the actual Euler unit field as one.** -/
theorem tendsto_gammaShapeAbelFunctional_unit :
    Tendsto (fun θ : ℝ => gammaShapeAbelFunctional θ (fun _ => (1 : ℝ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hpole := tendsto_mul_primeLogZeta
  have h2 : Tendsto (fun θ : ℝ => (2 : ℝ) ^ (θ / 2)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have h := tendsto_const_rpow_half (by norm_num : (0:ℝ) < 2) (1 / 2)
    have h' : (fun θ : ℝ => (2 : ℝ) ^ ((1 / 2 : ℝ) * θ)) = fun θ : ℝ => (2 : ℝ) ^ (θ / 2) := by
      funext θ; congr 1; ring
    rw [h'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h17 : Tendsto (fun θ : ℝ => (17 / 16 : ℝ) ^ (-θ / 2)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have h := tendsto_const_rpow_half (by norm_num : (0:ℝ) < 17 / 16) (-(1 / 2))
    have h' : (fun θ : ℝ => (17 / 16 : ℝ) ^ ((-(1 / 2) : ℝ) * θ))
        = fun θ : ℝ => (17 / 16 : ℝ) ^ (-θ / 2) := by
      funext θ; congr 1; ring
    rw [h'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto (fun θ : ℝ => 2 ^ (θ / 2) * (θ * primeLogZeta (1 + θ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using h2.mul hpole
  have hlower : Tendsto
      (fun θ : ℝ => (17 / 16 : ℝ) ^ (-θ / 2) * (2 ^ (θ / 2) * (θ * primeLogZeta (1 + θ))))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using h17.mul hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact gammaShapeAbelFunctional_unit_ge hθ
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact gammaShapeAbelFunctional_unit_le hθ

/-- **The Abel family evaluates the whole Mertens corona coset `1 + M_0` as one.** -/
theorem tendsto_gammaShapeAbelFunctional_unit_add {b : ℕ → ℝ}
    (hb : MemVanishingTailLayer b) :
    Tendsto (fun θ : ℝ => gammaShapeAbelFunctional θ (fun n => 1 + b n))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  obtain ⟨C, hC⟩ := memMarcinkiewiczLogLayer_of_memVanishingTailLayer hb
  have hlim : Tendsto
      (fun θ : ℝ => gammaShapeAbelFunctional θ (fun _ => (1 : ℝ))
        + gammaShapeAbelFunctional θ b) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have h := tendsto_gammaShapeAbelFunctional_unit.add
      (tendsto_gammaShapeAbelFunctional_vanishingTail hb)
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ
  exact (gammaShapeAbelFunctional_add_of_summable (summable_gammaShapeTerm_unit hθ0)
    (summable_gammaShapeTerm hθ0 hC)).symm

/-! ## The boundary passage is singular -/

/-- Every fixed positive Gamma shape lies in the vanishing-tail layer. -/
theorem meixnerShape_memVanishingTailLayer {θ : ℝ} (hθ : 0 < θ) :
    MemVanishingTailLayer (meixnerShape θ) := by
  refine memVanishingTailLayer_of_memCriticalSummableLayer ?_
  rw [MemCriticalSummableLayer]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_mertensPrimeWeight_rpow hθ).mul_left (2 ^ (θ / 2)))
  · by_cases hp : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
      have : (0 : ℝ) ≤ Real.log n / n := div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
      positivity
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
  · by_cases hp : n.Prime
    · have hn1 : 1 ≤ n := hp.one_le
      rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
      have hval : Real.log n / n * |meixnerShape θ n| = mertensPrimeWeight n * meixnerShape θ n := by
        rw [mertensPrimeWeight, if_pos hp, abs_of_pos (meixnerShape_pos θ n)]
      rw [hval]
      have hw : 0 ≤ mertensPrimeWeight n := mertensPrimeWeight_nonneg n
      calc mertensPrimeWeight n * meixnerShape θ n
          ≤ mertensPrimeWeight n * (2 ^ (θ / 2) * ((n : ℝ)) ^ (-θ)) :=
            mul_le_mul_of_nonneg_left (meixnerShape_le θ hθ.le hn1) hw
        _ = 2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)) := by ring
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
      have hw : 0 ≤ mertensPrimeWeight n := mertensPrimeWeight_nonneg n
      have : (0 : ℝ) ≤ 2 ^ (θ / 2) * (mertensPrimeWeight n * ((n : ℝ)) ^ (-θ)) := by
        have hpow : (0 : ℝ) ≤ ((n : ℝ)) ^ (-θ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        positivity
      exact this

/-- **The boundary passage is genuinely singular.**  For every fixed positive shape the kernel
lies in the vanishing-tail layer, while the actual Euler unit field does not; so no fixed shape
sees the corona class, and only the limit `θ → 0⁺` does. -/
theorem meixnerShape_singular_boundary {θ : ℝ} (hθ : 0 < θ) :
    MemVanishingTailLayer (meixnerShape θ) ∧ ¬ MemVanishingTailLayer (fun _ => (1 : ℝ)) :=
  ⟨meixnerShape_memVanishingTailLayer hθ, unitField_not_memVanishingTailLayer⟩

end

end RHTower
