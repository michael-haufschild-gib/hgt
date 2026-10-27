import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAnomalyCostsHalfALogarithm

/-!
# The horizon counterterm is polar

The Abel radius regularizes the self-energy of every torsion point; its counterterm is the identity
and nothing survives (RBG). Weil's form uses a different regulator: the **horizon**, the orders
`≤ N`. Weil's prime kernel has no diagonal, so the divergence as `N → ∞` is not a self-energy; this
file shows that on log-scale profiles it is **rank one and polar**.

A **step profile** is a combination `x = Σ_i c_i u^{(M_i)}` of truncated pole vectors
`u^{(M)}_n = n^{−1/2} 𝟙_{n ≤ M}` (`truncPole`, `stepProfile`): in the log-scale variable it is the
profile `g = Σ c_i 𝟙_{[0, a_i]}`, `M_i = N^{a_i}`. The **polar functional** `ℓ(x) = Σ x_n n^{−1/2}` is
one factor of Weil's pole term `(Σ x_n √n)(Σ x_n/√n)`.

* **The pole rows** (`primeBilinear_truncPole_eq`): for `M ≤ M'`,
  `Σ_{m ≤ M, n ≤ M'} u_m u_n P(m, n) = Σ_{m ≤ M} (A(⌊M'/m⌋) + log m)/m`, by the exact Schur rows of
  `TheCovariantCountertermIsTheAnomaly`.
* **The pole Gram is the product of polar functionals** (`abs_primeBilinear_truncPole_sub_le`):
  `|⟨u^{(M)}, P u^{(M')}⟩ − H_M H_{M'}| ≤ (log 8 + 5) H_{min(M, M')}`, with `H_M = ℓ(u^{(M)})`.
* **Polarity** (`abs_atomicWeilForm_stepProfile_sub_le`): for every step profile on the orders `≤ N`,
  `|P_N(x) − ℓ(x)²| ≤ (log 8 + 5) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}`, while the mass is
  `|x|² = Σ_{i,j} c_i c_j H_{min(M_i, M_j)}` (`sum_stepProfile_sq`).
* **The survival cone is the polar hyperplane** (`abs_atomicWeilForm_stepProfile_le_of_polar`): on
  polar-neutral profiles, `ℓ(x) = 0`, the prime form is bounded by the absolute mass, with no
  divergence.

For a fixed profile `g` and `N → ∞`, `ℓ(x)² ≍ (log N)² (∫ g)²` and `|x|² ≍ log N ∫ g²`, while the
remainder is `O(log N)`: the Rayleigh quotient of the prime place is
`log N · (∫ g)²/∫ g² + O(1)`. The horizon divergence is the square of the polar functional — rank
one, carried by the arithmetic point — exactly the shape of the archimedean lattice germ's
counterterm `𝟙𝟙ᵀ` (RBG). The rank dichotomy of the Abel radius (identity versus rank one) is a
property of the regulator: at the horizon both places diverge along one polar direction.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-! ### Truncated pole vectors and step profiles -/

/-- The **truncated pole vector** `u^{(M)}_n = n^{−1/2} 𝟙_{n ≤ M}`. -/
def truncPole (M n : ℕ) : ℝ := if n ≤ M then poleVector n else 0

/-- A **step profile** `Σ_i c_i u^{(M_i)}`. -/
def stepProfile {k : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ) (n : ℕ) : ℝ :=
  ∑ i, c i * truncPole (M i) n

/-- The bilinear prime form `Σ_{m, n ≤ N} x_m y_n P(m, n)`. -/
def primeBilinear (N : ℕ) (x y : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * y n * weilPrimeKernel m n

/-- The **polar functional** `ℓ(x) = Σ_{n ≤ N} x_n n^{−1/2}`. -/
def polarFunctional (N : ℕ) (x : ℕ → ℝ) : ℝ := ∑ n ∈ Icc 1 N, x n * poleVector n

theorem atomicWeilForm_eq_primeBilinear (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x = primeBilinear N x x := rfl

theorem primeBilinear_comm (N : ℕ) (x y : ℕ → ℝ) : primeBilinear N x y = primeBilinear N y x := by
  unfold primeBilinear
  rw [sum_comm]
  exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [weilPrimeKernel_comm]; ring

/-- Summing a truncated vector over `[1, N]` with `M ≤ N` is summing over `[1, M]`. -/
theorem sum_truncate {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (if n ≤ M then f n else 0) = ∑ n ∈ Icc 1 M, f n := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Icc]
  omega

/-! ### The pole rows -/

/-- **The pole rows**: for `M ≤ M' ≤ N`, `⟨u^{(M)}, P u^{(M')}⟩ = Σ_{m ≤ M} (A(⌊M'/m⌋) + log m)/m`. -/
theorem primeBilinear_truncPole_eq {M M' N : ℕ} (hMM' : M ≤ M') (hM'N : M' ≤ N) :
    primeBilinear N (truncPole M) (truncPole M') =
      ∑ m ∈ Icc 1 M, (mertensSum (M' / m) + Real.log m) / m := by
  unfold primeBilinear
  have hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, truncPole M m * truncPole M' n * weilPrimeKernel m n =
      if m ≤ M then (mertensSum (M' / m) + Real.log m) / m else 0 := by
    intro m hm
    have hm0 := (mem_Icc.mp hm).1
    unfold truncPole
    split_ifs with hmM
    · have hinner : ∑ n ∈ Icc 1 N, poleVector m * (if n ≤ M' then poleVector n else 0) *
          weilPrimeKernel m n = poleVector m * ∑ n ∈ Icc 1 M', weilPrimeKernel m n * poleVector n := by
        rw [mul_sum, ← sum_truncate hM'N]
        refine sum_congr rfl fun n _ => ?_
        split_ifs <;> ring
      rw [hinner, sum_weilPrimeKernel_poleVector hm0 (hmM.trans hMM')]
      have h2 : poleVector m * poleVector m = 1 / m := by rw [← sq, poleVector_sq]
      linear_combination (mertensSum (M' / m) + Real.log m) * h2
    · simp
  rw [sum_congr rfl hrow, sum_truncate (hMM'.trans hM'N)]

/-- `log M ≤ H_M ≤ 1 + log M`. -/
theorem log_le_harmonicSum (M : ℕ) : Real.log M ≤ harmonicSum M := by
  have h := log_add_one_le_harmonic M
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  have hmono : Real.log M ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · exact Real.log_le_log (by exact_mod_cast hM) (by push_cast; linarith)
  have : harmonicSum M = ∑ i ∈ Icc 1 M, ((i : ℝ))⁻¹ := by simp [harmonicSum, one_div]
  linarith

/-- **The pole Gram, sandwich**: for `1 ≤ M ≤ M' ≤ N`,
`(log M' − log 8 − 4) H_M ≤ ⟨u^{(M)}, P u^{(M')}⟩ ≤ (log M' + log 4 + 4) H_M`. -/
theorem primeBilinear_truncPole_sandwich {M M' N : ℕ} (hMM' : M ≤ M') (hM'N : M' ≤ N) :
    (Real.log M' - (Real.log 8 + 4)) * harmonicSum M ≤
        primeBilinear N (truncPole M) (truncPole M') ∧
      primeBilinear N (truncPole M) (truncPole M') ≤
        (Real.log M' + (Real.log 4 + 4)) * harmonicSum M := by
  rw [primeBilinear_truncPole_eq hMM' hM'N, harmonicSum, mul_sum, mul_sum]
  constructor
  · refine sum_le_sum fun m hm => ?_
    have hm' := mem_Icc.mp hm
    have h := row_ge hm'.1 (hm'.2.trans hMM')
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'.1
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right h hm0.le
  · refine sum_le_sum fun m hm => ?_
    have hm' := mem_Icc.mp hm
    have h := row_le hm'.1 (hm'.2.trans hMM')
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'.1
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right h hm0.le

theorem harmonicSum_nonneg (M : ℕ) : 0 ≤ harmonicSum M :=
  sum_nonneg fun n _ => by positivity

theorem harmonicSum_mono {M M' : ℕ} (h : M ≤ M') : harmonicSum M ≤ harmonicSum M' :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl h) fun _ _ _ => by positivity

/-- **The pole Gram is the product of polar functionals**, up to the smaller mass:
`|⟨u^{(M)}, P u^{(M')}⟩ − H_M H_{M'}| ≤ (log 8 + 5) H_{min(M, M')}` for `M, M' ≤ N`. -/
theorem abs_primeBilinear_truncPole_sub_le {M M' N : ℕ} (hMN : M ≤ N) (hM'N : M' ≤ N) :
    |primeBilinear N (truncPole M) (truncPole M') - harmonicSum M * harmonicSum M'| ≤
      (Real.log 8 + 5) * harmonicSum (min M M') := by
  have hl8 : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  -- the case `a ≤ b`
  have key : ∀ a b : ℕ, a ≤ b → b ≤ N →
      |primeBilinear N (truncPole a) (truncPole b) - harmonicSum a * harmonicSum b| ≤
        (Real.log 8 + 5) * harmonicSum a := by
    intro a b hab hbN
    obtain ⟨h1, h2⟩ := primeBilinear_truncPole_sandwich (N := N) hab hbN
    have hHa := harmonicSum_nonneg a
    have hb1 := log_le_harmonicSum b
    have hb2 := harmonicSum_le b
    rw [abs_le]
    constructor <;> nlinarith
  rcases le_total M M' with h | h
  · rw [min_eq_left h]; exact key M M' h hM'N
  · rw [min_eq_right h, primeBilinear_comm, mul_comm]; exact key M' M h hMN

/-! ### Polarity on step profiles -/

theorem polarFunctional_truncPole {M N : ℕ} (hMN : M ≤ N) :
    polarFunctional N (truncPole M) = harmonicSum M := by
  unfold polarFunctional truncPole harmonicSum
  have : ∀ n ∈ Icc 1 N, (if n ≤ M then poleVector n else 0) * poleVector n =
      if n ≤ M then 1 / (n : ℝ) else 0 := fun n _ => by
    split_ifs
    · rw [← sq, poleVector_sq]
    · simp
  rw [sum_congr rfl this, sum_truncate hMN]

theorem primeBilinear_sum_left {k : ℕ} (N : ℕ) (c : Fin k → ℝ) (x : Fin k → ℕ → ℝ)
    (y : ℕ → ℝ) :
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

/-- The prime form of a step profile expands into the pole Gram. -/
theorem atomicWeilForm_stepProfile {k : ℕ} (N : ℕ) (c : Fin k → ℝ) (M : Fin k → ℕ) :
    atomicWeilForm N (stepProfile c M) =
      ∑ i, ∑ j, c i * c j * primeBilinear N (truncPole (M i)) (truncPole (M j)) := by
  have hL : ∀ y, primeBilinear N (stepProfile c M) y =
      ∑ i, c i * primeBilinear N (truncPole (M i)) y := fun y =>
    primeBilinear_sum_left N c (fun i => truncPole (M i)) y
  rw [atomicWeilForm_eq_primeBilinear, hL]
  refine sum_congr rfl fun i _ => ?_
  rw [primeBilinear_comm, hL, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [primeBilinear_comm]
  ring

theorem polarFunctional_stepProfile {k : ℕ} {N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ)
    (hM : ∀ i, M i ≤ N) :
    polarFunctional N (stepProfile c M) = ∑ i, c i * harmonicSum (M i) := by
  unfold polarFunctional stepProfile
  have h : ∀ n ∈ Icc 1 N, (∑ i, c i * truncPole (M i) n) * poleVector n =
      ∑ i, c i * (truncPole (M i) n * poleVector n) := fun n _ => by
    rw [sum_mul]; exact sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl h, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sum, ← polarFunctional_truncPole (hM i)]
  rfl

/-- `Σ_n u^{(M)}_n u^{(M')}_n = H_{min(M, M')}`. -/
theorem sum_truncPole_mul {M N : ℕ} (M' : ℕ) (hMN : M ≤ N) :
    ∑ n ∈ Icc 1 N, truncPole M n * truncPole M' n = harmonicSum (min M M') := by
  unfold truncPole harmonicSum
  have : ∀ n ∈ Icc 1 N, (if n ≤ M then poleVector n else 0) * (if n ≤ M' then poleVector n else 0)
      = if n ≤ min M M' then 1 / (n : ℝ) else 0 := fun n _ => by
    by_cases h1 : n ≤ M <;> by_cases h2 : n ≤ M' <;>
      simp [h1, h2, ← sq, poleVector_sq]
  rw [sum_congr rfl this, sum_truncate ((min_le_left _ _).trans hMN)]

/-- **The mass of a step profile**: `|x|² = Σ_{i,j} c_i c_j H_{min(M_i, M_j)}`. -/
theorem sum_stepProfile_sq {k : ℕ} {N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ)
    (hM : ∀ i, M i ≤ N) :
    ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2 =
      ∑ i, ∑ j, c i * c j * harmonicSum (min (M i) (M j)) := by
  unfold stepProfile
  simp only [sq, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_truncPole_mul (M j) (hM i), mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- **Polarity of the horizon divergence.** For every step profile on the orders `≤ N`,
`|P_N(x) − ℓ(x)²| ≤ (log 8 + 5) Σ_{i,j} |c_i| |c_j| H_{min(M_i, M_j)}`. -/
theorem abs_atomicWeilForm_stepProfile_sub_le {k : ℕ} {N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ)
    (hM : ∀ i, M i ≤ N) :
    |atomicWeilForm N (stepProfile c M) - polarFunctional N (stepProfile c M) ^ 2| ≤
      (Real.log 8 + 5) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) := by
  rw [atomicWeilForm_stepProfile, polarFunctional_stepProfile c M hM, sq, sum_mul_sum,
    ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have h := abs_primeBilinear_truncPole_sub_le (hM i) (hM j)
  have hrw : c i * c j * primeBilinear N (truncPole (M i)) (truncPole (M j)) -
      c i * harmonicSum (M i) * (c j * harmonicSum (M j)) =
      (c i * c j) * (primeBilinear N (truncPole (M i)) (truncPole (M j)) -
        harmonicSum (M i) * harmonicSum (M j)) := by ring
  rw [hrw, abs_mul, abs_mul]
  calc |c i| * |c j| * |primeBilinear N (truncPole (M i)) (truncPole (M j)) -
        harmonicSum (M i) * harmonicSum (M j)|
      ≤ |c i| * |c j| * ((Real.log 8 + 5) * harmonicSum (min (M i) (M j))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (Real.log 8 + 5) * (|c i| * |c j| * harmonicSum (min (M i) (M j))) := by ring

/-- **On the polar hyperplane the horizon form does not diverge**: if `ℓ(x) = 0`, the prime form of
the step profile is bounded by `(log 8 + 5)` times its absolute mass. -/
theorem abs_atomicWeilForm_stepProfile_le_of_polar {k : ℕ} {N : ℕ} (c : Fin k → ℝ)
    (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N) (hpolar : polarFunctional N (stepProfile c M) = 0) :
    |atomicWeilForm N (stepProfile c M)| ≤
      (Real.log 8 + 5) * ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) := by
  have h := abs_atomicWeilForm_stepProfile_sub_le c M hM
  rwa [hpolar, sq, mul_zero, sub_zero] at h

/-- For nonnegative coefficients the absolute mass is the mass: `|P_N(x) − ℓ(x)²| ≤ (log 8 + 5)|x|²`. -/
theorem abs_atomicWeilForm_stepProfile_sub_le_mass {k : ℕ} {N : ℕ} (c : Fin k → ℝ)
    (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N) (hc : ∀ i, 0 ≤ c i) :
    |atomicWeilForm N (stepProfile c M) - polarFunctional N (stepProfile c M) ^ 2| ≤
      (Real.log 8 + 5) * ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2 := by
  rw [sum_stepProfile_sq c M hM]
  have h := abs_atomicWeilForm_stepProfile_sub_le c M hM
  simp only [abs_of_nonneg (hc _)] at h
  exact h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
