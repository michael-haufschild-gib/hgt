import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeReceiverEnergy

/-!
# The complete Schur balance of a coherent charge and its receiver

The source energy vanishes and the complementary mixed pairing persists,
but the receiver energy grows logarithmically. Their two-dimensional
complete form has a strictly positive limiting determinant for nonzero
charge. Thus charge retention alone does not obstruct energy Schur bounds.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory

/-- The literal determinant of the complete form on source and complementary receiver. -/
def primeChargeSchurDeterminant (φ : ℝ → ℝ) (K : ℝ) (X : ℕ) (t : ℝ) : ℝ :=
  let c := 2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)
  completeWeilEnergy φ c (X ^ 40) (harmonicPrimeChargeVector (X ^ 2) (X ^ 40) t) *
      completeWeilEnergy φ c (X ^ 40) (primeChargeTerminalReceiver X) -
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c (X ^ 40))
      (harmonicPrimeChargeVector (X ^ 2) (X ^ 40) t), primeChargeTerminalReceiver X⟫ ^ 2

/-- The growing receiver pays its mixed pairing with a strict positive Schur reserve. -/
theorem tendsto_primeChargeSchurDeterminant {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun X : ℕ => primeChargeSchurDeterminant φ K X t)
      atTop (𝓝 (6239 / 6400 * t ^ 2)) := by
  have hs := tendsto_harmonicPrimeCharge_polynomial_complete_energy
    hφ hφ0 hsupp hM hK (a := 2) (d := 40) (by omega) (by omega) t
  have hr := tendsto_primeChargeTerminalReceiver_complete_scaled hφ hφ0 hsupp hM hK
  have hb := tendsto_harmonicPrimeCharge_complete_terminalReceiver hφ hφ0 hsupp hM hK t
  have h := (hs.mul hr).sub (hb.pow 2)
  convert h using 1
  · funext X
    dsimp only [primeChargeSchurDeterminant]
    rw [harmonicPrimeChargeVector_energy]
    ring
  · norm_num
    ring

/-- For nonzero charge the literal Schur determinant is eventually strictly positive. -/
theorem eventually_primeChargeSchurDeterminant_pos {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {t : ℝ} (ht : t ≠ 0) :
    ∀ᶠ X : ℕ in atTop, 0 < primeChargeSchurDeterminant φ K X t :=
  (tendsto_primeChargeSchurDeterminant hφ hφ0 hsupp hM hK t).eventually
    (lt_mem_nhds (mul_pos (by norm_num) (sq_pos_of_ne_zero ht)))

private theorem binary_form_pos_of_schur {a b d u v : ℝ}
    (ha : 0 < a) (hdet : 0 < a * d - b ^ 2) (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < a * u ^ 2 + 2 * b * u * v + d * v ^ 2 := by
  have he : a * (a * u ^ 2 + 2 * b * u * v + d * v ^ 2) =
      (a * u + b * v) ^ 2 + (a * d - b ^ 2) * v ^ 2 := by ring
  have hp : 0 < (a * u + b * v) ^ 2 + (a * d - b ^ 2) * v ^ 2 := by
    by_cases hv : v = 0
    · have hu : u ≠ 0 := huv.resolve_right (not_not.mpr hv)
      simpa only [hv, mul_zero, add_zero, zero_pow (by omega : 2 ≠ 0)] using
        sq_pos_of_ne_zero (mul_ne_zero ha.ne' hu)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hv))
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left ha).mp hp

/-- Every nonzero linear combination of charge source and exact receiver eventually has positive complete energy. -/
theorem eventually_primeCharge_source_receiver_form_pos {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {t : ℝ} (ht : t ≠ 0) :
    ∀ᶠ X : ℕ in atTop, ∀ u v : ℝ, u ≠ 0 ∨ v ≠ 0 →
      0 < completeWeilEnergy φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
        (u • harmonicPrimeChargeVector (X ^ 2) (X ^ 40) t + v • primeChargeTerminalReceiver X) := by
  have hs := tendsto_harmonicPrimeCharge_polynomial_complete_energy
    hφ hφ0 hsupp hM hK (a := 2) (d := 40) (by omega) (by omega) t
  have hspos : 0 < t ^ 2 * ((40 : ℝ) / 2 - 1 / 2) :=
    mul_pos (sq_pos_of_ne_zero ht) (by norm_num)
  filter_upwards [eventually_ge_atTop 2, hs.eventually (lt_mem_nhds hspos),
    eventually_primeChargeSchurDeterminant_pos hφ hφ0 hsupp hM hK ht] with X hX hsX hdX
  intro u v huv
  let c := 2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)
  let x := harmonicPrimeChargeVector (X ^ 2) (X ^ 40) t
  let r := primeChargeTerminalReceiver X
  let W := Matrix.toEuclideanLin (completeWeilMatrix φ c (X ^ 40))
  have ha : 0 < completeWeilEnergy φ c (X ^ 40) x := by
    rw [show x = harmonicPrimeChargeVector (X ^ 2) (X ^ 40) t from rfl,
      harmonicPrimeChargeVector_energy]
    exact div_pos hsX (Real.log_pos (by exact_mod_cast
      (hX.trans (Nat.le_pow (by omega : 0 < 40)))))
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian φ c (X ^ 40))
  have hcross : ⟪W r, x⟫ = ⟪W x, r⟫ := by rw [hsym, real_inner_comm]
  have hpos := binary_form_pos_of_schur ha hdX huv
  change 0 < ⟪W (u • x + v • r), u • x + v • r⟫
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hcross]
  convert hpos using 1
  dsimp only [completeWeilEnergy, x, r, W]
  ring

#print axioms tendsto_primeChargeSchurDeterminant
#print axioms eventually_primeCharge_source_receiver_form_pos

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
