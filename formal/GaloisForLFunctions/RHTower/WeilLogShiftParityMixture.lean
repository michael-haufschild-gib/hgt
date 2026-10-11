import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalParity

/-! Parity reads the mixture coordinate exactly, before any asymptotic limit. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeil_parity_tilt_reading {ι : Type} [Fintype ι]
    (p σ : ι → ℝ) (a : ℝ) (hσ : ∀ i, σ i ^ 2 = 1)
    (hp : ∑ i, p i = 1) (hm : ∑ i, σ i * p i = 0) :
    (∑ i, σ i * ((1 + (2 * a - 1) * σ i) * p i)) = 2 * a - 1 := by
  calc
    _ = ∑ i, (σ i * p i + (2 * a - 1) * p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = σ i * p i + (2 * a - 1) * p i * σ i ^ 2 := by ring
        _ = _ := by rw [hσ i, mul_one]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hm, hp, mul_one, zero_add]

theorem finiteWeilCanonicalMixture_parity_factor (r k : ℕ) (a : ℝ) (i : Fin (r + 2)) :
    finiteWeilCanonicalMixture r k a i =
      (1 + (2 * a - 1) * finiteWeilBinomialParity r i) *
        finiteWeilCanonicalMixture r k (1 / 2) i := by
  let c := finiteWeilCanonicalCluster r k i
  let S := finiteWeilAbsMass (finiteWeilCanonicalCluster r k)
  let σ := finiteWeilBinomialParity r i
  have hc : c = σ * |c| := finiteWeilCanonicalCluster_parity r k i
  rw [finiteWeilCanonicalMixture_midpoint_abs]
  change a * ((|c| + c) / S) + (1 - a) * ((|c| - c) / S) =
    (1 + (2 * a - 1) * σ) * (|c| / S)
  calc
    _ = (|c| + (2 * a - 1) * c) / S := by ring
    _ = (|c| + (2 * a - 1) * (σ * |c|)) / S :=
      congrArg (fun z => (|c| + (2 * a - 1) * z) / S) hc
    _ = _ := by ring

theorem finiteWeilCanonicalMixture_midpoint_parity (r k : ℕ) :
    (∑ i, finiteWeilBinomialParity r i * finiteWeilCanonicalMixture r k (1 / 2) i) = 0 := by
  simp only [finiteWeilCanonicalMixture_midpoint_abs, ← mul_div_assoc,
    ← finiteWeilCanonicalCluster_parity, ← Finset.sum_div,
    finiteWeilCanonicalCluster_sum_zero, zero_div]

/-- The parity coordinate remains exact for every real mixture parameter. -/
theorem finiteWeilCanonicalMixture_parity_reading (r k : ℕ) (a : ℝ) :
    (∑ i, finiteWeilBinomialParity r i * finiteWeilCanonicalMixture r k a i) =
      2 * a - 1 := by
  calc
    _ = ∑ i, finiteWeilBinomialParity r i *
        ((1 + (2 * a - 1) * finiteWeilBinomialParity r i) *
          finiteWeilCanonicalMixture r k (1 / 2) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z => finiteWeilBinomialParity r i * z)
        (finiteWeilCanonicalMixture_parity_factor r k a i)
    _ = _ := finiteWeil_parity_tilt_reading (finiteWeilCanonicalMixture r k (1 / 2))
      (finiteWeilBinomialParity r) a (finiteWeilBinomialParity_sq r)
      (finiteWeilCanonicalMixture_mem r k (1 / 2) (by norm_num) (by norm_num)).2.1
      (finiteWeilCanonicalMixture_midpoint_parity r k)

theorem finiteWeilBinomialParity_multiplier_bounds (r : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (i : Fin (r + 2)) :
    0 ≤ 1 + (2 * a - 1) * finiteWeilBinomialParity r i ∧
      1 + (2 * a - 1) * finiteWeilBinomialParity r i ≤ 2 := by
  have h : |2 * a - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hm : |(2 * a - 1) * finiteWeilBinomialParity r i| ≤ 1 := by
    rwa [abs_mul, finiteWeilBinomialParity_abs, mul_one]
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor <;> linarith

end RHTower
