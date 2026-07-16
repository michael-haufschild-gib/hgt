import GaloisForLFunctions.RHTower.PrimeArchBernsteinRpowPacketGrowth
import GaloisForLFunctions.RHTower.FiniteExponentialPencilDominantConstant

/-!
# Absolutely summable atomic Bernstein packets

An absolutely summable complex atomic functional with weights `c j` and nodes `u j` has the
degree-`n` Bernstein coefficient packet

`a(n,i) = sum_j c j * choose(n,i) * u_j^i * (1-u_j)^(n-i)`.

This file proves the exact pencil identity, the affine-amplitude `l1` envelope, and the resulting
real-`p` growth theorem under a finite noncancelling maximal-mode hypothesis.  No property of Xi
or of any particular divisor is used.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One atom's contribution to a Bernstein coefficient. -/
def atomicBernsteinCoefficientTerm {I : Type*}
    (c u : I → ℂ) (n i : ℕ) (j : I) : ℂ :=
  c j * (n.choose i : ℂ) * u j ^ i * (1 - u j) ^ (n - i)

/-- Bernstein coefficients of an atomic functional. -/
def atomicBernsteinCoefficient {I : Type*}
    (c u : I → ℂ) (n i : ℕ) : ℂ :=
  ∑' j : I, atomicBernsteinCoefficientTerm c u n i j

/-- The triangular coefficient packet of an atomic functional. -/
def atomicBernsteinPacket {I : Type*} (c u : I → ℂ) : ℕ → ℕ → ℂ :=
  fun n i => atomicBernsteinCoefficient c u n i

/-- The exponential pencil associated with an atomic Bernstein packet. -/
def atomicBernsteinPencil {I : Type*}
    (c u : I → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑' j : I, c j * (1 - u j + u j * w) ^ n

/-- Total variation of the atomic weights. -/
def atomicWeightL1 {I : Type*} (c : I → ℂ) : ℝ :=
  ∑' j : I, ‖c j‖

private lemma norm_atomicBernsteinCoefficientTerm
    {I : Type*} (c u : I → ℂ) (n i : ℕ) (j : I) :
    ‖atomicBernsteinCoefficientTerm c u n i j‖ =
      ‖c j‖ * (n.choose i : ℝ) * ‖u j‖ ^ i * ‖1 - u j‖ ^ (n - i) := by
  simp only [atomicBernsteinCoefficientTerm, norm_mul, norm_pow,
    Complex.norm_natCast]
  ring

private lemma binomial_term_le_affineAmplitude_pow
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {n i : ℕ} (hi : i ≤ n) :
    (n.choose i : ℝ) * x ^ i * y ^ (n - i) ≤ (x + y) ^ n := by
  rw [add_pow]
  apply Finset.single_le_sum
  · intro j hj
    positivity
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi)

/-- Under a uniform affine-amplitude ceiling, every atomic coefficient series is absolutely
summable. -/
lemma summable_atomicBernsteinCoefficientTerm
    {I : Type*} {c u : I → ℂ} (hc : Summable c)
    {B : ℝ}
    (hB : ∀ j : I, ‖u j‖ + ‖1 - u j‖ ≤ B)
    {n i : ℕ} (hi : i ≤ n) :
    Summable (atomicBernsteinCoefficientTerm c u n i) := by
  apply (hc.norm.mul_right (B ^ n)).of_norm_bounded
  intro j
  rw [norm_atomicBernsteinCoefficientTerm]
  have hterm := binomial_term_le_affineAmplitude_pow
    (norm_nonneg (u j)) (norm_nonneg (1 - u j)) hi
  have hamp : (‖u j‖ + ‖1 - u j‖) ^ n ≤ B ^ n :=
    pow_le_pow_left₀ (by positivity) (hB j) n
  calc
    ‖c j‖ * (n.choose i : ℝ) * ‖u j‖ ^ i * ‖1 - u j‖ ^ (n - i) =
        ‖c j‖ * ((n.choose i : ℝ) * ‖u j‖ ^ i * ‖1 - u j‖ ^ (n - i)) := by
      ring
    _ ≤ ‖c j‖ * (‖u j‖ + ‖1 - u j‖) ^ n :=
      mul_le_mul_of_nonneg_left hterm (norm_nonneg _)
    _ ≤ ‖c j‖ * B ^ n :=
      mul_le_mul_of_nonneg_left hamp (norm_nonneg _)

/-- The complete atomic Bernstein packet has `l1` norm at most total atomic variation times the
maximal affine amplitude to the degree. -/
theorem finitePacketL1_atomicBernsteinPacket_le
    {I : Type*} {c u : I → ℂ} (hc : Summable c)
    {B : ℝ}
    (hB : ∀ j : I, ‖u j‖ + ‖1 - u j‖ ≤ B)
    (n : ℕ) :
    finitePacketL1 (atomicBernsteinPacket c u) n ≤ atomicWeightL1 c * B ^ n := by
  have hsumm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      Summable (atomicBernsteinCoefficientTerm c u n i) :=
    summable_atomicBernsteinCoefficientTerm hc hB (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  rw [finitePacketL1, atomicBernsteinPacket, atomicBernsteinCoefficient]
  calc
    (∑ i ∈ Finset.range (n + 1),
        ‖∑' j : I, atomicBernsteinCoefficientTerm c u n i j‖) ≤
      ∑ i ∈ Finset.range (n + 1),
        ∑' j : I, ‖atomicBernsteinCoefficientTerm c u n i j‖ := by
      exact Finset.sum_le_sum fun i hi => norm_tsum_le_tsum_norm (hsumm i hi).norm
    _ = ∑' j : I, ∑ i ∈ Finset.range (n + 1),
        ‖atomicBernsteinCoefficientTerm c u n i j‖ := by
      rw [Summable.tsum_finsetSum]
      intro i hi
      exact (hsumm i hi).norm
    _ = ∑' j : I, ‖c j‖ * (‖u j‖ + ‖1 - u j‖) ^ n := by
      apply tsum_congr
      intro j
      simp_rw [norm_atomicBernsteinCoefficientTerm]
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Nat.cast_ofNat] using
        (add_pow ‖u j‖ ‖1 - u j‖ n).symm
    _ ≤ ∑' j : I, ‖c j‖ * B ^ n := by
      apply Summable.tsum_le_tsum
      · intro j
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (hB j) n) (norm_nonneg _)
      · exact Summable.of_nonneg_of_le
          (fun j => mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) n))
          (fun j => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (hB j) n) (norm_nonneg _))
          (hc.norm.mul_right (B ^ n))
      · exact hc.norm.mul_right (B ^ n)
    _ = atomicWeightL1 c * B ^ n := by
      rw [atomicWeightL1, tsum_mul_right]

/-- The finite coefficient transform is exactly the infinite atomic pencil. -/
theorem finitePacketTransform_atomicBernsteinPacket_eq
    {I : Type*} {c u : I → ℂ} (hc : Summable c)
    {B : ℝ}
    (hB : ∀ j : I, ‖u j‖ + ‖1 - u j‖ ≤ B)
    (n : ℕ) (w : ℂ) :
    finitePacketTransform (atomicBernsteinPacket c u) n w =
      atomicBernsteinPencil c u n w := by
  have hsumm (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      Summable (fun j : I => atomicBernsteinCoefficientTerm c u n i j * w ^ i) :=
    (summable_atomicBernsteinCoefficientTerm hc hB
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).mul_right (w ^ i)
  rw [finitePacketTransform, atomicBernsteinPacket, atomicBernsteinCoefficient,
    atomicBernsteinPencil]
  calc
    (∑ i ∈ Finset.range (n + 1),
        (∑' j : I, atomicBernsteinCoefficientTerm c u n i j) * w ^ i) =
      ∑ i ∈ Finset.range (n + 1),
        ∑' j : I, atomicBernsteinCoefficientTerm c u n i j * w ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [tsum_mul_right]
    _ = ∑' j : I, ∑ i ∈ Finset.range (n + 1),
        atomicBernsteinCoefficientTerm c u n i j * w ^ i := by
      rw [Summable.tsum_finsetSum hsumm]
    _ = ∑' j : I, c j * (1 - u j + u j * w) ^ n := by
      apply tsum_congr
      intro j
      rw [show 1 - u j + u j * w = u j * w + (1 - u j) by ring, add_pow]
      simp_rw [atomicBernsteinCoefficientTerm]
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring

/-- A finite noncancelling maximal atomic mode supplies the transform lower envelope required by
the abstract packet theorem. -/
theorem eventually_norm_atomicBernsteinPencil_ge_of_dominant_constant
    {I : Type*} (c u : I → ℂ) (hc : Summable c)
    (D : Finset I) {B : ℝ} (hB : 0 < B) {w beta : ℂ}
    (hdom : ∀ j ∈ D, 1 - u j + u j * w = beta)
    (hsub : ∀ j ∉ D, ‖1 - u j + u j * w‖ < B)
    (hbeta : ‖beta‖ = B)
    (hC : ∑ j ∈ D, c j ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (‖∑ j ∈ D, c j‖ / 2) * B ^ n ≤
        ‖atomicBernsteinPencil c u n w‖ := by
  let b : I → ℂ := fun j => 1 - u j + u j * w
  have hnormalized :=
    eventually_norm_tsum_normalizedExponentialPencil_ge_of_dominant_constant
      c b hc D hB hdom hsub hbeta hC
  filter_upwards [hnormalized] with n hn
  have hBpow : 0 < B ^ n := pow_pos hB n
  have heq :
      ∑' j : I, c j * (b j / (B : ℂ)) ^ n =
        (∑' j : I, c j * b j ^ n) / (B : ℂ) ^ n := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro j
    rw [div_pow]
    ring
  rw [heq, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hB] at hn
  have := (le_div_iff₀ hBpow).mp hn
  simpa only [b, atomicBernsteinPencil] using this

/-- **Atomic real-`p` Bernstein growth theorem.**  For an absolutely summable atomic functional,
a common affine-amplitude ceiling `B` together with a finite noncancelling maximal mode forces
the degree-`n` Bernstein packet's real-`p` energy to have nth-root limit `B^p`, for every
`1 <= p < infinity`. -/
theorem tendsto_atomicBernsteinPacketRpowEnergy_rpow_inv_natCast
    {I : Type*} (c u : I → ℂ) (hc : Summable c)
    {p B : ℝ} (hp : 1 ≤ p) (hB : 0 < B)
    (hamp : ∀ j : I, ‖u j‖ + ‖1 - u j‖ ≤ B)
    (D : Finset I) {w beta : ℂ} (hw : ‖w‖ ≤ 1)
    (hdom : ∀ j ∈ D, 1 - u j + u j * w = beta)
    (hsub : ∀ j ∉ D, ‖1 - u j + u j * w‖ < B)
    (hbeta : ‖beta‖ = B)
    (hC : ∑ j ∈ D, c j ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        finitePacketRpowEnergy (atomicBernsteinPacket c u) p n ^ ((n : ℝ)⁻¹))
      atTop (nhds (B ^ p)) := by
  have hmass : 0 ≤ atomicWeightL1 c := tsum_nonneg fun _ => norm_nonneg _
  have hCpos : 0 < ‖∑ j ∈ D, c j‖ / 2 := half_pos (norm_pos_iff.mpr hC)
  apply tendsto_finitePacketRpowEnergy_rpow_inv_natCast
    (atomicBernsteinPacket c u) hp hmass hB hCpos hw
  · intro n
    exact finitePacketL1_atomicBernsteinPacket_le hc hamp n
  · have hpencil := eventually_norm_atomicBernsteinPencil_ge_of_dominant_constant
      c u hc D hB hdom hsub hbeta hC
    filter_upwards [hpencil] with n hn
    rwa [finitePacketTransform_atomicBernsteinPacket_eq hc hamp n w]

end

end RHTower
