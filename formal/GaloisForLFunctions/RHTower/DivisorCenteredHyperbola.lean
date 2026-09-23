import GaloisForLFunctions.HTGeometry.CenteredModularAbel
import GaloisForLFunctions.RHTower.SymmetricHyperbolaFloorCount

/-!
# Signed half-order cancellation in the centered divisor hyperbola

The literal floor-divisor sum splits exactly into a harmonic boundary and centered
modular ramps. Reindexing the complete moving hyperbola by its square births retains
every coefficient and terminal block. Its centered half-order response is nonpositive
with magnitude at most `sqrt(M-1)/16`. No Möbius cross-channel estimate is assumed.
-/

noncomputable section
open Finset HTGeometry
namespace RHTower

/-- Centered remainder on the short strip of the symmetric divisor hyperbola. -/
def centeredDivisorHyperbola (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 (Nat.sqrt N), centeredModularRamp d N

/-- The complete half-order time response of the centered divisor hyperbola. -/
def centeredDivisorHyperbolaAbel (M : ℕ) : ℝ :=
  ∑ k ∈ range M, centeredDivisorHyperbola k * halfOrderAbelStep 0 k

/-- Exact harmonic and centered-remainder decomposition of the literal divisor sum. -/
theorem sum_floorDivisor_eq_centeredHyperbola (N : ℕ) :
    (∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ)) =
      (2 * (N : ℝ) + 1) * (∑ d ∈ Icc 1 (Nat.sqrt N), (1 : ℝ) / d) -
        (Nat.sqrt N : ℝ)^(2 : ℕ) - Nat.sqrt N - 2 * centeredDivisorHyperbola N := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 (Nat.sqrt N)) :
      2 * ((N / d : ℕ) : ℝ) =
        (2 * (N : ℝ) + 1) * (1 / d) - 1 - 2 * centeredModularRamp d N := by
    have hdpos : 0 < d := by have := (mem_Icc.mp hd).1; omega
    have hdR : (d : ℝ) ≠ 0 := by positivity
    have hid : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.div_add_mod N d
    unfold centeredModularRamp
    field_simp
    nlinarith
  have hsum := Finset.sum_congr rfl hpoint
  have hcount : (∑ _d ∈ Icc 1 (Nat.sqrt N), (1 : ℝ)) = Nat.sqrt N := by simp
  have hsum' : 2 * (∑ d ∈ Icc 1 (Nat.sqrt N), ((N / d : ℕ) : ℝ)) =
      (2 * (N : ℝ) + 1) * (∑ d ∈ Icc 1 (Nat.sqrt N), (1 : ℝ) / d) -
        Nat.sqrt N - 2 * centeredDivisorHyperbola N := by
    simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount,
      centeredDivisorHyperbola] using hsum
  have hhyper : (∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ)) +
      (Nat.sqrt N : ℝ) * Nat.sqrt N =
        2 * (∑ d ∈ Icc 1 (Nat.sqrt N), ((N / d : ℕ) : ℝ)) := by
    exact_mod_cast sum_div_add_sqrt_sq N
  nlinarith

/-- Finite Fubini over all active hyperbola labels. The square birth and moving endpoint are
both literal; no complete-period truncation or rectangular padding is discarded. -/
theorem centeredDivisorHyperbolaAbel_eq_birth_channels (M : ℕ) :
    centeredDivisorHyperbolaAbel M =
      ∑ d ∈ Icc 1 (Nat.sqrt (M-1)),
        ∑ k ∈ Ico (d*d) M, centeredModularRamp d k * halfOrderAbelStep 0 k := by
  let D := Icc 1 (Nat.sqrt (M-1))
  have hfibre (k : ℕ) (hk : k ∈ range M) :
      Icc 1 (Nat.sqrt k) = D.filter (fun d => d*d ≤ k) := by
    have hkM : k ≤ M-1 := by have := mem_range.mp hk; omega
    ext d
    simp only [mem_Icc, mem_filter, D]
    constructor
    · intro hd
      exact ⟨⟨hd.1, hd.2.trans (Nat.sqrt_le_sqrt hkM)⟩, Nat.le_sqrt.mp hd.2⟩
    · intro hd
      exact ⟨hd.1.1, Nat.le_sqrt.mpr hd.2⟩
  have htime (d : ℕ) : (range M).filter (fun k => d*d ≤ k) = Ico (d*d) M := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  unfold centeredDivisorHyperbolaAbel centeredDivisorHyperbola
  simp_rw [Finset.sum_mul]
  calc
    (∑ k ∈ range M, ∑ d ∈ Icc 1 (Nat.sqrt k),
        centeredModularRamp d k * halfOrderAbelStep 0 k) =
        ∑ k ∈ range M, ∑ d ∈ D,
          if d*d ≤ k then centeredModularRamp d k * halfOrderAbelStep 0 k else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [hfibre k hk, sum_filter]
    _ = ∑ d ∈ D, ∑ k ∈ range M,
          if d*d ≤ k then centeredModularRamp d k * halfOrderAbelStep 0 k else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro d _
      rw [← sum_filter, htime]

/-- Unconditional signed square-root ceiling for the entire moving centered hyperbola. -/
theorem centeredDivisorHyperbolaAbel_bounds (M : ℕ) :
    -(Nat.sqrt (M-1) : ℝ) / 16 ≤ centeredDivisorHyperbolaAbel M ∧
      centeredDivisorHyperbolaAbel M ≤ 0 := by
  rw [centeredDivisorHyperbolaAbel_eq_birth_channels]
  constructor
  · calc
      -(Nat.sqrt (M-1) : ℝ) / 16 =
          ∑ _d ∈ Icc 1 (Nat.sqrt (M-1)), -(1/16 : ℝ) := by simp; ring
      _ ≤ _ := by
        apply sum_le_sum
        intro d _
        exact (sum_centeredModularRamp_halfOrder_Ico_bounds d M).1
  · apply sum_nonpos
    intro d _
    exact (sum_centeredModularRamp_halfOrder_Ico_bounds d M).2

end RHTower
