import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds

/-!
# Finite reciprocal criteria for constrained spectral bounds

A linear constraint removes one negative diagonal direction exactly when
its reciprocal coordinate mass fits the squared ground coefficient.
Finite packets control the omitted mass through a denominator gap; eventual
packet bounds transfer their limiting values to the full expression.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

/-- A single negative diagonal direction is paid by a linear constraint exactly
when its weighted reciprocal mass fits within the squared head coefficient. -/
theorem diagonal_hyperplane_nonneg_iff {ι : Type*} (s : Finset ι)
    (w a : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) {b c : ℝ} (hb : 0 < b) (hc : c ≠ 0) :
    (∀ (x₀ : ℝ) (x : ι → ℝ), c * x₀ + ∑ i ∈ s, a i * x i = 0 →
      0 ≤ -b * x₀ ^ 2 + ∑ i ∈ s, w i * x i ^ 2) ↔
      b * (∑ i ∈ s, a i ^ 2 / w i) ≤ c ^ 2 := by
  have hS0 : 0 ≤ ∑ i ∈ s, a i ^ 2 / w i :=
    sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le
  have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  constructor
  · intro hform
    have hlin : c * (-(∑ i ∈ s, a i ^ 2 / w i) / c) +
        ∑ i ∈ s, a i * (a i / w i) = 0 := by
      have he : (∑ i ∈ s, a i * (a i / w i)) = ∑ i ∈ s, a i ^ 2 / w i :=
        sum_congr rfl fun i _ => by ring
      rw [he]
      field_simp [hc]
      ring
    have htest := hform (-(∑ i ∈ s, a i ^ 2 / w i) / c) (fun i => a i / w i) hlin
    have he : (∑ i ∈ s, w i * (a i / w i) ^ 2) = ∑ i ∈ s, a i ^ 2 / w i := by
      refine sum_congr rfl fun i hi => ?_
      field_simp [(hw i hi).ne']
    rw [he] at htest
    by_cases hz : (∑ i ∈ s, a i ^ 2 / w i) = 0
    · rw [hz, mul_zero]
      exact hc2.le
    have hS : 0 < ∑ i ∈ s, a i ^ 2 / w i := lt_of_le_of_ne hS0 (Ne.symm hz)
    have hscale := mul_nonneg hc2.le htest
    have hfactor : c ^ 2 *
        (-b * (-(∑ i ∈ s, a i ^ 2 / w i) / c) ^ 2 + ∑ i ∈ s, a i ^ 2 / w i) =
        (∑ i ∈ s, a i ^ 2 / w i) * (c ^ 2 - b * (∑ i ∈ s, a i ^ 2 / w i)) := by
      field_simp [hc]
      ring
    rw [hfactor] at hscale
    have hpaid : (∑ i ∈ s, a i ^ 2 / w i) * (b * (∑ i ∈ s, a i ^ 2 / w i)) ≤
        (∑ i ∈ s, a i ^ 2 / w i) * c ^ 2 := by linarith only [hscale]
    exact le_of_mul_le_mul_left hpaid hS
  · intro hpaid x₀ x hlin
    have hE : 0 ≤ ∑ i ∈ s, w i * x i ^ 2 :=
      sum_nonneg fun i hi => mul_nonneg (hw i hi).le (sq_nonneg _)
    have hCS : (∑ i ∈ s, a i * x i) ^ 2 ≤
        (∑ i ∈ s, a i ^ 2 / w i) * (∑ i ∈ s, w i * x i ^ 2) := by
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le)
        (fun i hi => mul_nonneg (hw i hi).le (sq_nonneg _))
      intro i hi
      apply le_of_eq
      field_simp [(hw i hi).ne']
    have hcon : (∑ i ∈ s, a i * x i) ^ 2 = c ^ 2 * x₀ ^ 2 := by
      have he : (∑ i ∈ s, a i * x i) = -(c * x₀) := by linarith only [hlin]
      rw [he, neg_sq, mul_pow]
    have hbound : c ^ 2 * (b * x₀ ^ 2) ≤ c ^ 2 * (∑ i ∈ s, w i * x i ^ 2) := by
      calc
        _ = b * (∑ i ∈ s, a i * x i) ^ 2 := by rw [hcon]; ring
        _ ≤ b * ((∑ i ∈ s, a i ^ 2 / w i) * (∑ i ∈ s, w i * x i ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS hb.le
        _ = (b * (∑ i ∈ s, a i ^ 2 / w i)) * (∑ i ∈ s, w i * x i ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpaid hE
    have h := le_of_mul_le_mul_left hbound hc2
    linarith only [h]

/-- A finite packet controls the reciprocal quadratic mass with an explicit
remainder paid by the denominator gap outside that packet. -/
theorem reciprocal_mass_le_packet_add_tail {ι : Type*} [DecidableEq ι]
    (U S : Finset ι) (hSU : S ⊆ U) (w a : ι → ℝ) {η : ℝ} (hη : 0 < η)
    (htail : ∀ i ∈ U \ S, η ≤ w i) :
    (∑ i ∈ U, a i ^ 2 / w i) ≤ (∑ i ∈ S, a i ^ 2 / w i) +
      ((∑ i ∈ U, a i ^ 2) - ∑ i ∈ S, a i ^ 2) / η := by
  have he : (∑ i ∈ U, a i ^ 2 / w i) = (∑ i ∈ S, a i ^ 2 / w i) +
      ∑ i ∈ U \ S, a i ^ 2 / w i := by
    calc
      _ = (∑ i ∈ U \ S, a i ^ 2 / w i) + ∑ i ∈ S, a i ^ 2 / w i :=
        (sum_sdiff hSU).symm
      _ = _ := add_comm _ _
  have hm : (∑ i ∈ U \ S, a i ^ 2) + (∑ i ∈ S, a i ^ 2) =
      ∑ i ∈ U, a i ^ 2 := sum_sdiff hSU
  have hdiff : (∑ i ∈ U, a i ^ 2) - (∑ i ∈ S, a i ^ 2) =
      ∑ i ∈ U \ S, a i ^ 2 := by linarith only [hm]
  rw [he, hdiff, sum_div]
  apply add_le_add le_rfl
  exact sum_le_sum fun i hi => div_le_div_of_nonneg_left (sq_nonneg _) hη (htail i hi)

/-- Strict failure of the reciprocal-mass condition produces a negative vector
on the constraint hyperplane. -/
theorem exists_negative_diagonal_on_hyperplane {ι : Type*} (s : Finset ι)
    (w a : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) {b c : ℝ} (hb : 0 < b) (hc : c ≠ 0)
    (hbad : c ^ 2 < b * (∑ i ∈ s, a i ^ 2 / w i)) :
    ∃ (x₀ : ℝ) (x : ι → ℝ), c * x₀ + ∑ i ∈ s, a i * x i = 0 ∧
      -b * x₀ ^ 2 + (∑ i ∈ s, w i * x i ^ 2) < 0 := by
  classical
  have hn : ¬ (∀ (x₀ : ℝ) (x : ι → ℝ), c * x₀ + ∑ i ∈ s, a i * x i = 0 →
      0 ≤ -b * x₀ ^ 2 + ∑ i ∈ s, w i * x i ^ 2) := by
    intro h
    exact (not_le_of_gt hbad) ((diagonal_hyperplane_nonneg_iff s w a hw hb hc).mp h)
  obtain ⟨x₀, hx₀⟩ := not_forall.mp hn
  obtain ⟨x, hx⟩ := not_forall.mp hx₀
  exact ⟨x₀, x, (Classical.not_imp.mp hx).1, lt_of_not_ge (Classical.not_imp.mp hx).2⟩

/-- The reciprocal criterion with the exceptional coordinate retained in the
same finite index set as all positive directions. -/
theorem one_negative_diagonal_nonneg_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d a : ι → ℝ) (i₀ : ι) (hneg : d i₀ < 0) (hpos : ∀ i, i ≠ i₀ → 0 < d i)
    (ha : a i₀ ≠ 0) :
    (∀ x : ι → ℝ, (∑ i, a i * x i) = 0 → 0 ≤ ∑ i, d i * x i ^ 2) ↔
      (-d i₀) * (∑ i ∈ univ.erase i₀, a i ^ 2 / d i) ≤ a i₀ ^ 2 := by
  have hp : ∀ i ∈ univ.erase i₀, 0 < d i := fun i hi => hpos i (mem_erase.mp hi).1
  constructor
  · intro h
    apply (diagonal_hyperplane_nonneg_iff (univ.erase i₀) d a hp (neg_pos.mpr hneg) ha).mp
    intro x₀ x hlin
    let y := Function.update x i₀ x₀
    have hy₀ : y i₀ = x₀ := by simp [y]
    have hy (i : ι) (hi : i ∈ univ.erase i₀) : y i = x i := by
      simp only [y, Function.update_of_ne (mem_erase.mp hi).1]
    have hliny : (∑ i, a i * y i) = 0 := by
      rw [← sum_erase_add _ _ (mem_univ i₀), hy₀,
        sum_congr rfl (fun i hi => by rw [hy i hi])]
      linarith only [hlin]
    have hform := h y hliny
    rw [← sum_erase_add _ _ (mem_univ i₀), hy₀,
      sum_congr rfl (fun i hi => by rw [hy i hi])] at hform
    simpa only [neg_neg, add_comm] using hform
  · intro hpaid x hlin
    have hlin' : a i₀ * x i₀ + ∑ i ∈ univ.erase i₀, a i * x i = 0 := by
      rw [← sum_erase_add _ _ (mem_univ i₀)] at hlin
      linarith only [hlin]
    have hform := (diagonal_hyperplane_nonneg_iff (univ.erase i₀) d a hp
      (neg_pos.mpr hneg) ha).mpr hpaid (x i₀) x hlin'
    rw [← sum_erase_add _ _ (mem_univ i₀)]
    simpa only [neg_neg, add_comm] using hform

/-- At an energy between the ground and all other eigenvalues, the exact
Hermitian hyperplane bound is a scalar reciprocal-coordinate inequality. -/
theorem hermitian_hyperplane_bound_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (v : EuclideanSpace ℝ ι)
    (L t : ℝ) (i₀ : ι) (hneg : L - hA.eigenvalues i₀ < t)
    (hpos : ∀ i, i ≠ i₀ → t < L - hA.eigenvalues i)
    (hv : ⟪v, hA.eigenvectorBasis i₀⟫ ≠ 0) :
    (∀ x : EuclideanSpace ℝ ι, ⟪v, x⟫ = 0 →
      t * ‖x‖ ^ 2 ≤ L * ‖x‖ ^ 2 - ⟪Matrix.toEuclideanLin A x, x⟫) ↔
      (t - (L - hA.eigenvalues i₀)) *
        (∑ i ∈ univ.erase i₀,
          ⟪v, hA.eigenvectorBasis i⟫ ^ 2 / (L - hA.eigenvalues i - t)) ≤
            ⟪v, hA.eigenvectorBasis i₀⟫ ^ 2 := by
  let d : ι → ℝ := fun i => L - hA.eigenvalues i - t
  let a : ι → ℝ := fun i => ⟪v, hA.eigenvectorBasis i⟫
  have hd₀ : d i₀ < 0 := sub_neg.mpr hneg
  have hd : ∀ i, i ≠ i₀ → 0 < d i := fun i hi => sub_pos.mpr (hpos i hi)
  have hhead : -d i₀ = t - (L - hA.eigenvalues i₀) := by dsimp only [d]; ring
  have hdiag := one_negative_diagonal_nonneg_iff d a i₀ hd₀ hd hv
  rw [hhead] at hdiag
  constructor
  · intro h
    apply hdiag.mp
    intro q hq
    let x : EuclideanSpace ℝ ι := ∑ i, q i • hA.eigenvectorBasis i
    have horth (i j : ι) : ⟪hA.eigenvectorBasis i, hA.eigenvectorBasis j⟫ =
        if i = j then 1 else 0 := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
    have hcoeff (i : ι) : ⟪x, hA.eigenvectorBasis i⟫ = q i := by
      simp only [x, sum_inner, real_inner_smul_left, horth, mul_ite, mul_one, mul_zero,
        sum_ite_eq', mem_univ, ite_true]
    have hx : ⟪v, x⟫ = 0 := by
      rw [show ⟪v, x⟫ = ∑ i, q i * ⟪v, hA.eigenvectorBasis i⟫ by
        simp only [x, inner_sum, real_inner_smul_right]]
      simpa only [a, mul_comm] using hq
    have hbound := h x hx
    have he := HTGeometry.shiftedHermitianEnergy_eq_sum hA (L - t) x
    simp only [hcoeff] at he
    have hshift (i : ι) : L - t - hA.eigenvalues i = d i := by dsimp only [d]; ring
    simp only [hshift] at he
    nlinarith only [hbound, he]
  · intro hpaid x hx
    have hq : (∑ i, a i * ⟪x, hA.eigenvectorBasis i⟫) = 0 := by
      calc
        _ = ∑ i, ⟪v, hA.eigenvectorBasis i⟫ * ⟪hA.eigenvectorBasis i, x⟫ := by
          refine sum_congr rfl fun i _ => ?_
          rw [real_inner_comm x (hA.eigenvectorBasis i)]
        _ = ⟪v, x⟫ := hA.eigenvectorBasis.sum_inner_mul_inner v x
        _ = 0 := hx
    have hform := hdiag.mpr hpaid (fun i => ⟪x, hA.eigenvectorBasis i⟫) hq
    have he := HTGeometry.shiftedHermitianEnergy_eq_sum hA (L - t) x
    have hshift (i : ι) : L - t - hA.eigenvalues i = d i := by dsimp only [d]; ring
    simp only [hshift] at he
    nlinarith only [hform, he]

/-- Finite packet bounds determine a full limit once both packet limits
converge to the same value. Each packet may have its own eventual horizon. -/
theorem tendsto_of_eventual_packet_bounds {A : ℕ → ℝ} {a : ℝ}
    {lower upper : ℕ → ℕ → ℝ} {lowerLimit upperLimit : ℕ → ℝ}
    (hl : ∀ k, Tendsto (lower k) atTop (𝓝 (lowerLimit k)))
    (hu : ∀ k, Tendsto (upper k) atTop (𝓝 (upperLimit k)))
    (hll : Tendsto lowerLimit atTop (𝓝 a))
    (hul : Tendsto upperLimit atTop (𝓝 a))
    (hb : ∀ k, ∀ᶠ N : ℕ in atTop, lower k N ≤ A N ∧ A N ≤ upper k N) :
    Tendsto A atTop (𝓝 a) := by
  rw [tendsto_order]
  constructor
  · intro b hb'
    obtain ⟨k, hk⟩ := (hll.eventually_const_lt hb').exists
    filter_upwards [(hl k).eventually_const_lt hk, hb k] with N hN hbound
    exact hN.trans_le hbound.1
  · intro b hb'
    obtain ⟨k, hk⟩ := (hul.eventually_lt_const hb').exists
    filter_upwards [(hu k).eventually_lt_const hk, hb k] with N hN hbound
    exact hbound.2.trans_lt hN

end GaloisForLFunctions.ArithmeticCountingPositivity
