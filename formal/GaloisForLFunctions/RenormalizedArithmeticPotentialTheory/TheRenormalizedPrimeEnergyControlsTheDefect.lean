import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasFiniteRamanujanApproximation
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints

/-!
# Bounded renormalized matrix energy has bounded prime defect

The sharp arithmetic counterterm applies to every actual horizon vector after
extension by zero. Its defect bound therefore supplies finite Ramanujan
approximation uniformly on each bounded matrix-energy sublevel.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics ArithmeticEffectivityTheory

/-- Extend an actual Euclidean horizon vector by zero outside its integer interval. -/
def primeHorizonExtension {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (n : ℕ) : ℝ := if h : n ∈ Icc 1 N then x ⟨n, h⟩ else 0

@[simp] theorem primeHorizonExtension_coe {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) (n : PrimeHorizonIndex N) :
    primeHorizonExtension x n = x n := by
  simp only [primeHorizonExtension, dif_pos n.property]

theorem sum_primeHorizonExtension_sq {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2) = ‖x‖ ^ 2 := by
  rw [← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension x n ^ 2),
    EuclideanSpace.real_norm_sq_eq]
  exact sum_congr rfl fun n _ => by rw [primeHorizonExtension_coe]

/-- The arithmetic double sum is exactly the actual Euclidean matrix form. -/
theorem atomicWeilForm_primeHorizonExtension {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    atomicWeilForm N (primeHorizonExtension x) =
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) x, x⟫ := by
  rw [atomicWeilForm,
    ← sum_coe_sort (Icc 1 N) (fun m => ∑ n ∈ Icc 1 N,
      primeHorizonExtension x m * primeHorizonExtension x n * weilPrimeKernel m n),
    EuclideanSpace.inner_eq_star_dotProduct]
  change _ = ∑ m : PrimeHorizonIndex N,
    x m * (∑ n : PrimeHorizonIndex N, weilPrimeKernel m n * x n)
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_coe_sort (Icc 1 N) (fun n =>
    primeHorizonExtension x m * primeHorizonExtension x n * weilPrimeKernel m n), mul_sum]
  exact sum_congr rfl fun n _ => by
    rw [primeHorizonExtension_coe, primeHorizonExtension_coe]
    ring

/-- The quadratic form after subtracting the common logarithmic divergence. -/
def renormalizedPrimeEnergy (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) : ℝ :=
  Real.log N * ‖x‖ ^ 2 - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) x, x⟫

/-- One finite defect bound works for all unit vectors in a fixed energy sublevel. -/
theorem eventually_poleDefect_le_of_renormalizedPrimeEnergy_le (T : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖x‖ = 1 → renormalizedPrimeEnergy N x ≤ T →
        poleDefect N (primeHorizonExtension x) ≤
          max 0 (2 * (T - Real.eulerMascheroniConstant + 1)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [eventually_ge_atTop N₀] with N hN x hx henergy
  have h := hN₀ N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension, hx] at h
  simp only [renormalizedPrimeEnergy, hx, one_pow, mul_one] at henergy
  have hb := le_max_right (0 : ℝ) (2 * (T - Real.eulerMascheroniConstant + 1))
  nlinarith only [h, henergy, hb]

/-- Every bounded actual energy sublevel is uniformly approximated by one fixed
finite Ramanujan span, with arbitrary prescribed squared error. -/
theorem exists_finite_ramanujan_approximation_of_renormalizedPrimeEnergy_le
    (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → renormalizedPrimeEnergy N x ≤ T →
          ∃ a : ℕ → ℝ, ‖x - ∑ m ∈ S, a m • ramanujanHorizonVector m N‖ ^ 2 ≤ η := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le
    (max 0 (2 * (T - Real.eulerMascheroniConstant + 1))) hη
  refine ⟨S, hS, ?_⟩
  filter_upwards [eventually_poleDefect_le_of_renormalizedPrimeEnergy_le T]
    with N hN x hx henergy
  obtain ⟨a, ha⟩ := happ N (primeHorizonExtension x)
    (by rw [sum_primeHorizonExtension_sq, hx]; norm_num) (hN x hx henergy)
  refine ⟨a, ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← sum_coe_sort (Icc 1 N) (fun n =>
    (primeHorizonExtension x n - ∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2)] at ha
  convert ha using 1
  apply sum_congr rfl
  intro n _
  have hsum : (∑ m ∈ S, a m • ramanujanHorizonVector m N) n =
      ∑ m ∈ S, a m * ramanujanPoleProfile m n := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n) (∑ m ∈ S, a m • ramanujanHorizonVector m N) = _
    rw [map_sum]
    exact sum_congr rfl fun m _ => rfl
  simp only [PiLp.sub_apply, hsum, primeHorizonExtension_coe]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
