import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonDivergenceLivesOnTheTorsionOrbits

/-!
# The horizon counterterm is a tensor product

The horizon divergence of Weil's prime form is the square of the polar functional on uniform
profiles (`TheHorizonCountertermIsPolar`) and has unbounded rank on the `p`-adic valuation classes
(`TheHorizonDivergenceLivesOnTheTorsionOrbits`). This file joins the two: on **class-wise step
profiles** `x = Σ_{j ≤ J} Σ_i c_{ji} w_j^{(M_i)}` the counterterm is exactly

    Σ_{j ≤ J} δ_j^{−1} ℓ_j(x)²,      ℓ_j(x) = Σ_{v_p(n) = j} x_n n^{−1/2},   δ_j = (1 − 1/p)/p^j,

up to `O(H_N)` per unit of absolute coefficient mass (`abs_atomicWeilForm_classProfile_sub_le`).

* **Class densities are orbit sizes** (`classDensity_eq_orbit`): `δ_j = φ(p^{J+1−j})/p^{J+1}`, the
  number of points of the torsion orbit `O_{p^{J+1−j}}` dual to the class `j` per point of
  `μ_{p^{J+1}}`.
* **Class masses** (`unitHarmonic_eq`, `abs_unitHarmonic_sub_le`, `classMass_eq_unitHarmonic`,
  `abs_classMass_sub_le`): `|w_j^{(M)}|² = ℓ_j(w_j^{(M)}) = δ_j log M + O(1)`.
* **The class Gram** (`primeBilinear_classPole_two_eq`, `abs_classGram_self_sub_le`,
  `classGram_cross_le`): `⟨w_j^{(M)}, P w_j^{(M')}⟩ = δ_j^{−1} |w_j^{(M)}|² |w_j^{(M')}|² + O(|w_j|²)`,
  and the cross terms between classes are `O(mass)`.
* **The tensor law** (`abs_atomicWeilForm_classProfile_sub_le`,
  `abs_atomicWeilForm_classProfile_le_of_polar`): the horizon counterterm is the diagonal sum of the
  class polar squares weighted by the inverse orbit densities; its survival cone is the class-wise
  polar hyperplane `ℓ_j(x) = 0` for every `j`.

So the counterterm of the prime place at the horizon is the tensor product of the torsion
counterterm — diagonal on the orbits, weighted by `φ` (RBG: the Abel torsion germ's counterterm
`φ(n) δ_{mn}`) — and the archimedean counterterm — the polar projection on log-scale profiles (RBG:
the lattice germ's `𝟙𝟙ᵀ`). Its survival cone is the tensor product of their survival cones: `{0}` on
no factor, the polar hyperplane on each class.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {p : ℕ}

/-! ### Class densities and orbit sizes -/

/-- The density `δ_j = (1 − 1/p)/p^j` of the valuation class `j`. -/
def classDensity (p j : ℕ) : ℝ := (1 - 1 / (p : ℝ)) / (p : ℝ) ^ j

theorem classDensity_pos (hp : p.Prime) (j : ℕ) : 0 < classDensity p j := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  unfold classDensity
  have : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; exact hp1
  positivity

/-- **Class densities are orbit sizes**: `δ_j = φ(p^{J+1−j})/p^{J+1}` for `j ≤ J`. -/
theorem classDensity_eq_orbit (hp : p.Prime) {j J : ℕ} (hj : j ≤ J) :
    classDensity p j = (Nat.totient (p ^ (J + 1 - j)) : ℝ) / (p : ℝ) ^ (J + 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [show J + 1 - j = (J - j) + 1 by omega, Nat.totient_prime_pow_succ hp, classDensity]
  push_cast [Nat.cast_sub hp.one_le]
  rw [show (p : ℝ) ^ (J + 1) = (p : ℝ) ^ (J - j) * (p : ℝ) ^ j * p by
    rw [← pow_add, ← pow_succ]; congr 1; omega]
  field_simp

/-! ### Class masses -/

/-- The harmonic sum over the units of `p`: `Σ_{k ≤ X, p ∤ k} 1/k`. -/
def unitHarmonic (p X : ℕ) : ℝ := ∑ k ∈ (Icc 1 X).filter (fun k => ¬ p ∣ k), 1 / (k : ℝ)

theorem unitHarmonic_eq (hp : p.Prime) (X : ℕ) :
    unitHarmonic p X = harmonicSum X - harmonicSum (X / p) / p := by
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 X) (fun k => p ∣ k) (fun k => 1 / (k : ℝ))
  have hmult : ∑ k ∈ (Icc 1 X).filter (fun k => p ∣ k), 1 / (k : ℝ) = harmonicSum (X / p) / p := by
    rw [filter_dvd_Icc_eq_image hp.pos,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h, harmonicSum, sum_div]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rw [div_div, mul_comm]
  have hH : harmonicSum X = ∑ k ∈ Icc 1 X, 1 / (k : ℝ) := rfl
  rw [unitHarmonic, hH, ← hsplit, hmult]
  ring

/-- **`Σ_{k ≤ X, p ∤ k} 1/k = (1 − 1/p) log X + O(1)`**, with error at most `2 + log p`. -/
theorem abs_unitHarmonic_sub_le (hp : p.Prime) {X : ℕ} (hX : 1 ≤ X) :
    |unitHarmonic p X - (1 - 1 / (p : ℝ)) * Real.log X| ≤ 2 + Real.log p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hl2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hH1 := log_le_harmonicSum X
  have hH2 := harmonicSum_le X
  rw [unitHarmonic_eq hp, abs_le]
  rcases Nat.eq_zero_or_pos (X / p) with hq | hq
  · -- `X < p`: only the units below `p`
    rw [hq]
    have hH0 : harmonicSum 0 = 0 := by simp [harmonicSum]
    rw [hH0, zero_div, sub_zero]
    have hXp : (X : ℝ) < p := by
      have := (Nat.div_eq_zero_iff_lt hp.pos).mp hq
      exact_mod_cast this
    have hlXp : Real.log X ≤ Real.log p := Real.log_le_log (by exact_mod_cast hX) hXp.le
    have h1p : 0 ≤ 1 / (p : ℝ) * Real.log X := by positivity
    have h1p' : 1 / (p : ℝ) * Real.log X ≤ Real.log X := by
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; exact hp1.le
      nlinarith
    constructor <;> nlinarith
  · -- `X ≥ p`: subtract the multiples of `p`
    have hHq1 := log_le_harmonicSum (X / p)
    have hHq2 := harmonicSum_le (X / p)
    have hlow := log_le_log_div_add_log hp.pos ((Nat.le_div_iff_mul_le hp.pos).mp hq |>.trans_eq'
      (by ring) |>.trans (le_refl _))
    have hup := log_div_add_log_le hp.pos ((Nat.le_div_iff_mul_le hp.pos).mp hq |>.trans_eq'
      (by ring) |>.trans (le_refl _))
    have hinv : 1 / (p : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
    have hinv0 : 0 < 1 / (p : ℝ) := by positivity
    have hd1 : harmonicSum (X / p) / p = 1 / (p : ℝ) * harmonicSum (X / p) := by ring
    rw [hd1]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hHq2 hinv0.le, mul_le_mul_of_nonneg_left hup hinv0.le]
    · nlinarith [mul_le_mul_of_nonneg_left hHq1 hinv0.le, mul_le_mul_of_nonneg_left hlow hinv0.le]

/-- The class `j` below `M` is the image of the units below `M/p^j` under `k ↦ p^j k`. -/
theorem filter_factorization_eq_image (hp : p.Prime) (j M : ℕ) :
    (Icc 1 M).filter (fun n => n.factorization p = j) =
      ((Icc 1 (M / p ^ j)).filter (fun k => ¬ p ∣ k)).image (p ^ j * ·) := by
  have hpj : 0 < p ^ j := pow_pos hp.pos j
  ext n
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, hv⟩
    have hn0 : n ≠ 0 := by omega
    refine ⟨n / p ^ n.factorization p, ⟨⟨Nat.ordCompl_pos p hn0, ?_⟩,
      Nat.not_dvd_ordCompl hp hn0⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le hpj, ← hv, mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
      exact h2
    · rw [← hv]; exact Nat.ordProj_mul_ordCompl_eq_self n p
  · rintro ⟨k, ⟨⟨hk1, hk2⟩, hpk⟩, rfl⟩
    refine ⟨⟨Nat.mul_pos hpj hk1, ?_⟩, ?_⟩
    · rw [Nat.le_div_iff_mul_le hpj] at hk2; linarith [mul_comm k (p ^ j)]
    · rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpk,
        add_zero]

/-- `|w_j^{(M)}|² = p^{−j} Σ_{k ≤ M/p^j, p ∤ k} 1/k`. -/
theorem classMass_eq_unitHarmonic (hp : p.Prime) (j M : ℕ) :
    classMass p j M = unitHarmonic p (M / p ^ j) / (p : ℝ) ^ j := by
  have hpj : 0 < p ^ j := pow_pos hp.pos j
  rw [classMass, ← sum_filter, filter_factorization_eq_image hp,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hpj h, unitHarmonic, sum_div]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  rw [div_div, mul_comm]

/-- **Class masses**: `|w_j^{(M)}|² = δ_j log M + O(1)` for `M ≥ p^j`. -/
theorem abs_classMass_sub_le (hp : p.Prime) {j M : ℕ} (hM : p ^ j ≤ M) :
    |classMass p j M - classDensity p j * Real.log M| ≤ 3 + (j + 1) * Real.log p := by
  have hpj : 0 < p ^ j := pow_pos hp.pos j
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hY : 1 ≤ M / p ^ j := (Nat.le_div_iff_mul_le hpj).mpr (by linarith)
  have hu := abs_unitHarmonic_sub_le hp hY
  have hPj : (1 : ℝ) ≤ (p : ℝ) ^ j := one_le_pow₀ hp1.le
  have hlogY1 := log_div_add_log_le hpj hM
  have hlogY2 := log_le_log_div_add_log hpj hM
  have hlogpj : Real.log ((p ^ j : ℕ) : ℝ) = j * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlogpj] at hlogY1 hlogY2
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hp1.le
  have hc1 : 1 - 1 / (p : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith
  -- `classMass − δ_j log M = p^{−j} [(unit − (1 − 1/p) log Y) + (1 − 1/p)(log Y − log M)]`
  rw [classMass_eq_unitHarmonic hp, classDensity]
  set Y := M / p ^ j
  have hkey : unitHarmonic p Y / (p : ℝ) ^ j - (1 - 1 / (p : ℝ)) / (p : ℝ) ^ j * Real.log M =
      ((unitHarmonic p Y - (1 - 1 / (p : ℝ)) * Real.log Y) +
        (1 - 1 / (p : ℝ)) * (Real.log Y - Real.log M)) / (p : ℝ) ^ j := by
    field_simp; ring
  rw [hkey, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ j)]
  rw [div_le_iff₀ (by positivity)]
  have hjl : 0 ≤ (j : ℝ) * Real.log p := by positivity
  have hdiff : |Real.log Y - Real.log M| ≤ j * Real.log p + Real.log 2 := by
    rw [abs_le]; constructor <;> linarith
  calc |unitHarmonic p Y - (1 - 1 / (p : ℝ)) * Real.log Y +
        (1 - 1 / (p : ℝ)) * (Real.log Y - Real.log M)|
      ≤ |unitHarmonic p Y - (1 - 1 / (p : ℝ)) * Real.log Y| +
          |(1 - 1 / (p : ℝ)) * (Real.log Y - Real.log M)| := abs_add_le _ _
    _ ≤ (2 + Real.log p) + (j * Real.log p + Real.log 2) := by
        refine add_le_add hu ?_
        rw [abs_mul, abs_of_nonneg hc]
        calc (1 - 1 / (p : ℝ)) * |Real.log Y - Real.log M| ≤ 1 * |Real.log Y - Real.log M| :=
              mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
          _ ≤ j * Real.log p + Real.log 2 := by rw [one_mul]; exact hdiff
    _ ≤ (3 + (j + 1) * Real.log p) * 1 := by nlinarith
    _ ≤ (3 + (j + 1) * Real.log p) * (p : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left hPj (by positivity)

theorem classMass_le_harmonicSum (p j M : ℕ) : classMass p j M ≤ harmonicSum M :=
  sum_le_sum fun n _ => by
    split_ifs
    · exact le_rfl
    · positivity

/-! ### The class Gram -/

/-- The class row is at most the full row. -/
theorem classRow_le_row (p j M m : ℕ) :
    classRow p j M m ≤ ∑ n ∈ Icc 1 M, weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) :=
  sum_le_sum fun n _ => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (weilPrimeKernel_nonneg m n) (Real.sqrt_nonneg _)

/-- **The class Gram through rows, two horizons**: for `M ≤ M' ≤ N`,
`⟨w_j^{(M)}, P w_{j'}^{(M')}⟩ = Σ_{m ≤ M, v_p(m) = j} classRow_{j'}^{(M')}(m)/m`. -/
theorem primeBilinear_classPole_two_eq (p j j' : ℕ) {M M' N : ℕ} (hMM' : M ≤ M')
    (hM'N : M' ≤ N) :
    primeBilinear N (classPole p j M) (classPole p j' M') =
      ∑ m ∈ Icc 1 M, (if m.factorization p = j then classRow p j' M' m / m else 0) := by
  unfold primeBilinear
  have hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, classPole p j M m * classPole p j' M' n *
      weilPrimeKernel m n = if m ≤ M then
        (if m.factorization p = j then classRow p j' M' m / m else 0) else 0 := by
    intro m hm
    have hm0 := pos_of_mem_Icc' hm
    by_cases hmM : m ≤ M
    · rw [if_pos hmM]
      by_cases hj : m.factorization p = j
      · rw [if_pos hj, classRow, sum_div, ← sum_truncate hM'N]
        refine sum_congr rfl fun n hn => ?_
        have hn0 := pos_of_mem_Icc' hn
        simp only [classPole, truncPole, if_pos hj, if_pos hmM]
        by_cases hnM : n ≤ M'
        · by_cases h1 : n.factorization p = j'
          · simp only [if_pos hnM, if_pos h1]
            rw [poleVector_mul_poleVector_mul hm0 hn0]
          · simp [h1]
        · simp [hnM]
      · rw [if_neg hj]
        simp [classPole, hj]
    · rw [if_neg hmM]
      simp [classPole, truncPole, hmM]
  rw [sum_congr rfl hrow, sum_truncate (hMM'.trans hM'N)]

/-- The constant of the tensor law. -/
def tensorConstant (p J : ℕ) : ℝ :=
  (Real.log 8 + 4 + Real.log p / ((p : ℝ) - 1) + J * Real.log p) +
    (3 + (J + 1) * Real.log p) * (p : ℝ) ^ J / (1 - 1 / (p : ℝ))

/-- **The class Gram on one class**: for `M ≤ M' ≤ N` and `j ≤ J`,
`|⟨w_j^{(M)}, P w_j^{(M')}⟩ − δ_j^{−1}|w_j^{(M)}|²|w_j^{(M')}|²| ≤ C_{p,J} |w_j^{(M)}|²`. -/
theorem abs_classGram_self_sub_le (hp : p.Prime) {j J M M' N : ℕ} (hj : j ≤ J) (hMM' : M ≤ M')
    (hM'N : M' ≤ N) :
    |primeBilinear N (classPole p j M) (classPole p j M') -
        classMass p j M * classMass p j M' / classDensity p j| ≤
      tensorConstant p J * classMass p j M := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hδ := classDensity_pos hp j
  have hc : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; exact hp1
  have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
  have hpjJ : (p : ℝ) ^ j ≤ (p : ℝ) ^ J := pow_le_pow_right₀ hp1.le hj
  -- pointwise: every class row is `δ_j^{-1}|w_j^{(M')}|² + O(1)`
  have hpt : ∀ m ∈ Icc 1 M, m.factorization p = j →
      |classRow p j M' m - classMass p j M' / classDensity p j| ≤ tensorConstant p J := by
    intro m hm hv
    have hm0 := pos_of_mem_Icc' hm
    have hmM' := (mem_Icc.mp hm).2.trans hMM'
    -- `p^j ∣ m`, so the class is nonempty below `M'`
    have hpjm : p ^ j ≤ M' := by
      have h := (hp.pow_dvd_iff_le_factorization hm0.ne').mpr hv.ge
      exact (Nat.le_of_dvd hm0 h).trans hmM'
    have hlow := classRow_self_ge hp hm0 hmM'
    rw [hv] at hlow
    have hup := (classRow_le_row p j M' m).trans_eq (row_eq hm0 hmM') |>.trans (row_le hm0 hmM')
    have hmass := abs_classMass_sub_le hp hpjm
    -- `|w_j^{(M')}|²/δ_j = log M' + O(e_j/δ_j)`
    have hdiv : |classMass p j M' / classDensity p j - Real.log M'| ≤
        (3 + (j + 1) * Real.log p) / classDensity p j := by
      rw [show classMass p j M' / classDensity p j - Real.log M' =
        (classMass p j M' - classDensity p j * Real.log M') / classDensity p j by
          field_simp, abs_div, abs_of_pos hδ]
      exact div_le_div_of_nonneg_right hmass hδ.le
    have hinvδ : (3 + (j + 1) * Real.log p) / classDensity p j ≤
        (3 + (J + 1) * Real.log p) * (p : ℝ) ^ J / (1 - 1 / (p : ℝ)) := by
      rw [classDensity, div_div_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ hc.le
      exact mul_le_mul (by nlinarith) hpjJ (by positivity) (by positivity)
    have hl4 : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have hlp1 : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg hlogp (by linarith)
    rw [abs_le] at hdiv ⊢
    unfold tensorConstant
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hjJ hlogp]
  rw [primeBilinear_classPole_two_eq p j j hMM' hM'N, classMass, sum_mul, mul_sum]
  -- `δ_j^{-1}|w|²|w'|² = Σ_{m ∈ class} |w'|²/(δ_j m)`
  have hsum : (∑ m ∈ Icc 1 M, (if m.factorization p = j then 1 / (m : ℝ) else 0) *
      classMass p j M') / classDensity p j = ∑ m ∈ Icc 1 M,
        (if m.factorization p = j then classMass p j M' / classDensity p j / m else 0) := by
    rw [sum_div]
    refine sum_congr rfl fun m _ => ?_
    split_ifs
    · field_simp
    · simp
  rw [hsum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  by_cases hv : m.factorization p = j
  · rw [if_pos hv, if_pos hv, if_pos hv, ← sub_div, abs_div,
      abs_of_pos (by exact_mod_cast pos_of_mem_Icc' hm : (0 : ℝ) < m), mul_one_div]
    exact div_le_div_of_nonneg_right (hpt m hm hv) (Nat.cast_nonneg _)
  · rw [if_neg hv, if_neg hv, if_neg hv]; simp

/-- **Cross terms between classes are `O(mass)`**: for `j ≠ j'`, `M ≤ M' ≤ N`, `j ≤ J`,
`0 ≤ ⟨w_j^{(M)}, P w_{j'}^{(M')}⟩ ≤ C_{p,J} |w_j^{(M)}|²`. -/
theorem classGram_cross_le (hp : p.Prime) {j j' J M M' N : ℕ} (hjj : j ≠ j') (hj : j ≤ J)
    (hMM' : M ≤ M') (hM'N : M' ≤ N) :
    0 ≤ primeBilinear N (classPole p j M) (classPole p j' M') ∧
      primeBilinear N (classPole p j M) (classPole p j' M') ≤
        tensorConstant p J * classMass p j M := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
  rw [primeBilinear_classPole_two_eq p j j' hMM' hM'N]
  refine ⟨sum_nonneg fun m _ => ?_, ?_⟩
  · split_ifs
    · exact div_nonneg (classRow_nonneg _ _ _ _) (Nat.cast_nonneg _)
    · exact le_rfl
  rw [classMass, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hm0 := pos_of_mem_Icc' hm
  have hmM' := (mem_Icc.mp hm).2.trans hMM'
  split_ifs with hv
  · have h1 := classRow_le_offClassRow (p := p) (j := j') (M := M') (m := m)
      (by rw [hv]; exact Ne.symm hjj)
    have h2 := offClassRow_le hp hm0 hmM'
    rw [hv] at h2
    have hc0 : 0 ≤ (3 + (J + 1) * Real.log p) * (p : ℝ) ^ J / (1 - 1 / (p : ℝ)) := by
      have : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; exact hp1
      positivity
    have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hle : Real.log p / ((p : ℝ) - 1) + j * Real.log p ≤ tensorConstant p J := by
      unfold tensorConstant; nlinarith [mul_le_mul_of_nonneg_right hjJ hlogp]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (h1.trans (h2.trans hle)) (Nat.cast_nonneg _)
  · simp

/-! ### The tensor law -/

theorem primeBilinear_fintype_sum_left {ι : Type*} [Fintype ι] (N : ℕ) (c : ι → ℝ)
    (x : ι → ℕ → ℝ) (y : ℕ → ℝ) :
    primeBilinear N (fun n => ∑ i, c i * x i n) y = ∑ i, c i * primeBilinear N (x i) y := by
  unfold primeBilinear
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (∑ i, c i * x i m) * y n * weilPrimeKernel m n
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ∑ i, c i * (x i m * y n * weilPrimeKernel m n) := by
        refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
        rw [sum_mul, sum_mul]
        exact sum_congr rfl fun i _ => by ring
    _ = ∑ m ∈ Icc 1 N, ∑ i, ∑ n ∈ Icc 1 N, c i * (x i m * y n * weilPrimeKernel m n) :=
        sum_congr rfl fun m _ => sum_comm
    _ = ∑ i, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c i * (x i m * y n * weilPrimeKernel m n) := sum_comm
    _ = ∑ i, c i * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x i m * y n * weilPrimeKernel m n := by
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by rw [mul_sum]

/-- A **class-wise step profile** `Σ_{j ≤ J} Σ_i c_{ji} w_j^{(M_i)}`. -/
def classProfile {J k : ℕ} (p : ℕ) (c : Fin (J + 1) × Fin k → ℝ) (M : Fin k → ℕ) (n : ℕ) : ℝ :=
  ∑ a : Fin (J + 1) × Fin k, c a * classPole p a.1 (M a.2) n

/-- The **class polar functional** `ℓ_j(x) = Σ_{n ≤ N, v_p(n) = j} x_n n^{−1/2}`. -/
def classPolar (p j N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, (if n.factorization p = j then x n * poleVector n else 0)

theorem classPolar_classPole {j j' M N : ℕ} (hMN : M ≤ N) :
    classPolar p j N (classPole p j' M) = if j' = j then classMass p j M else 0 := by
  unfold classPolar classMass
  split_ifs with hjj
  · subst hjj
    rw [← sum_truncate hMN]
    refine sum_congr rfl fun n _ => ?_
    simp only [classPole, truncPole]
    split_ifs <;> simp [← sq, poleVector_sq, *]
  · refine sum_eq_zero fun n _ => ?_
    simp only [classPole]
    split_ifs with h1 h2
    · exact absurd (h2.symm.trans h1) hjj
    · simp
    · rfl

theorem classPolar_classProfile {J k N : ℕ} (c : Fin (J + 1) × Fin k → ℝ) (M : Fin k → ℕ)
    (hM : ∀ i, M i ≤ N) (j : ℕ) :
    classPolar p j N (classProfile p c M) =
      ∑ a : Fin (J + 1) × Fin k, c a * (if (a.1 : ℕ) = j then classMass p j (M a.2) else 0) := by
  unfold classPolar classProfile
  have h : ∀ n ∈ Icc 1 N, (if n.factorization p = j then
      (∑ a : Fin (J + 1) × Fin k, c a * classPole p a.1 (M a.2) n) * poleVector n else 0) =
      ∑ a : Fin (J + 1) × Fin k, c a * (if n.factorization p = j then
        classPole p a.1 (M a.2) n * poleVector n else 0) := by
    intro n _
    split_ifs
    · rw [sum_mul]; exact sum_congr rfl fun a _ => by ring
    · simp
  rw [sum_congr rfl h, sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← mul_sum]
  congr 1
  exact classPolar_classPole (hM a.2)

/-- **The tensor law.** For every class-wise step profile on the orders `≤ N` (classes `j ≤ J`),
`|P_N(x) − Σ_{j ≤ J} δ_j^{−1} ℓ_j(x)²| ≤ C_{p,J} H_N (Σ |c|)²`: the horizon counterterm is the sum
of the class polar squares weighted by the inverse orbit densities. -/
theorem abs_atomicWeilForm_classProfile_sub_le (hp : p.Prime) {J k N : ℕ}
    (c : Fin (J + 1) × Fin k → ℝ) (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N) :
    |atomicWeilForm N (classProfile p c M) -
        ∑ j : Fin (J + 1), classPolar p j N (classProfile p c M) ^ 2 / classDensity p j| ≤
      tensorConstant p J * harmonicSum N * (∑ a, |c a|) ^ 2 := by
  set G : Fin (J + 1) × Fin k → Fin (J + 1) × Fin k → ℝ := fun a b =>
    primeBilinear N (classPole p a.1 (M a.2)) (classPole p b.1 (M b.2))
  set T : Fin (J + 1) × Fin k → Fin (J + 1) × Fin k → ℝ := fun a b =>
    if a.1 = b.1 then classMass p a.1 (M a.2) * classMass p a.1 (M b.2) / classDensity p a.1
    else 0
  -- the form and the target expand over pairs of generators
  have hexp : atomicWeilForm N (classProfile p c M) = ∑ a, ∑ b, c a * c b * G a b := by
    have hL : ∀ y, primeBilinear N (classProfile p c M) y =
        ∑ a, c a * primeBilinear N (classPole p a.1 (M a.2)) y := fun y =>
      primeBilinear_fintype_sum_left N c (fun a => classPole p a.1 (M a.2)) y
    rw [atomicWeilForm_eq_primeBilinear, hL]
    refine sum_congr rfl fun a _ => ?_
    rw [primeBilinear_comm, hL, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    simp only [G]
    rw [primeBilinear_comm]
    ring
  have htarget : ∑ j : Fin (J + 1), classPolar p j N (classProfile p c M) ^ 2 / classDensity p j =
      ∑ a, ∑ b, c a * c b * T a b := by
    have hℓ : ∀ j : Fin (J + 1), classPolar p j N (classProfile p c M) =
        ∑ a, (if a.1 = j then c a * classMass p j (M a.2) else 0) := by
      intro j
      rw [classPolar_classProfile c M hM]
      refine sum_congr rfl fun a _ => ?_
      by_cases h : a.1 = j
      · rw [if_pos (congrArg Fin.val h), if_pos h]
      · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, mul_zero]
    simp only [hℓ, sq, sum_mul_sum, sum_div]
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [sum_eq_single a.1 (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul, zero_div])
      (by simp)]
    simp only [T]
    by_cases hab : a.1 = b.1
    · rw [if_pos hab.symm, if_pos hab]
      simp only [hab, ↓reduceIte]
      ring
    · rw [if_neg (Ne.symm hab), if_neg hab]; ring
  -- termwise error
  have hterm : ∀ a b, |G a b - T a b| ≤ tensorConstant p J * harmonicSum N := by
    intro a b
    have hja : (a.1 : ℕ) ≤ J := Nat.lt_succ_iff.mp a.1.2
    have hjb : (b.1 : ℕ) ≤ J := Nat.lt_succ_iff.mp b.1.2
    have hC0 : 0 ≤ tensorConstant p J := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hc : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; exact hp1
      unfold tensorConstant
      have : 0 ≤ Real.log p / ((p : ℝ) - 1) :=
        div_nonneg (Real.log_nonneg hp1.le) (by linarith)
      have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
      have : 0 ≤ Real.log p := Real.log_nonneg hp1.le
      positivity
    have hmassN : ∀ j M', M' ≤ N → classMass p j M' ≤ harmonicSum N := fun j M' h =>
      (classMass_le_harmonicSum p j M').trans (harmonicSum_mono h)
    by_cases hab : a.1 = b.1
    · -- one class: the polar square
      simp only [T, if_pos hab]
      simp only [G]
      rw [← hab]
      rcases le_total (M a.2) (M b.2) with h | h
      · exact (abs_classGram_self_sub_le hp hja h (hM b.2)).trans
          (mul_le_mul_of_nonneg_left (hmassN _ _ (hM a.2)) hC0)
      · rw [primeBilinear_comm, mul_comm (classMass p (a.1 : ℕ) (M a.2))]
        exact (abs_classGram_self_sub_le hp hja h (hM a.2)).trans
          (mul_le_mul_of_nonneg_left (hmassN _ _ (hM b.2)) hC0)
    · -- two classes: no polar square
      simp only [T, if_neg hab, sub_zero, G]
      have hne : (a.1 : ℕ) ≠ b.1 := fun h => hab (Fin.ext h)
      rcases le_total (M a.2) (M b.2) with h | h
      · obtain ⟨h0, h1⟩ := classGram_cross_le hp hne hja h (hM b.2)
        rw [abs_of_nonneg h0]
        exact h1.trans (mul_le_mul_of_nonneg_left (hmassN _ _ (hM a.2)) hC0)
      · obtain ⟨h0, h1⟩ := classGram_cross_le hp (Ne.symm hne) hjb h (hM a.2)
        rw [primeBilinear_comm, abs_of_nonneg h0]
        exact h1.trans (mul_le_mul_of_nonneg_left (hmassN _ _ (hM b.2)) hC0)
  rw [hexp, htarget, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc |∑ a, ∑ b, (c a * c b * G a b - c a * c b * T a b)|
      ≤ ∑ a, ∑ b, |c a * c b * G a b - c a * c b * T a b| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, |c a| * |c b| * (tensorConstant p J * harmonicSum N) := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
        rw [← mul_sub, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hterm a b) (by positivity)
    _ = tensorConstant p J * harmonicSum N * (∑ a, |c a|) ^ 2 := by
        rw [sq, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun b _ => by ring

/-- **The survival cone of the tensor law is the class-wise polar hyperplane**: if `ℓ_j(x) = 0` for
every class `j ≤ J`, the horizon form of the class-wise step profile does not diverge. -/
theorem abs_atomicWeilForm_classProfile_le_of_polar (hp : p.Prime) {J k N : ℕ}
    (c : Fin (J + 1) × Fin k → ℝ) (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N)
    (hpolar : ∀ j : Fin (J + 1), classPolar p j N (classProfile p c M) = 0) :
    |atomicWeilForm N (classProfile p c M)| ≤
      tensorConstant p J * harmonicSum N * (∑ a, |c a|) ^ 2 := by
  have h := abs_atomicWeilForm_classProfile_sub_le hp c M hM
  rw [show (∑ j : Fin (J + 1), classPolar p j N (classProfile p c M) ^ 2 / classDensity p j) = 0 from
    sum_eq_zero fun j _ => by rw [hpolar j]; simp, sub_zero] at h
  exact h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
