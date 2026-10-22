import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CriticalEnergyFamilies
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedMoebiusFirstMomentAndChebyshevTangentBridge

/-!
# The function-field calibration of the continuation mechanism

Over `F_q[T]` the zeta function of the polynomial ring is `1/(1 − q^{1-s})`, so its reciprocal is a
*polynomial*: the degree-wise Möbius sums are

`Σ_{deg f = 0} μ(f) = 1`,  `Σ_{deg f = 1} μ(f) = −q`,  `Σ_{deg f = k} μ(f) = 0` for `k ≥ 2`.

This module takes those three facts as the definition of the model (`fqMobiusDegreeSum`), builds the
damped source with the same divisor prefix, the same pole subtraction `1/ζ(1+ε) = 1 − q^{-ε}` and
the same observation weight as the number-field programme, and computes.  The answer is as sharp as
it could be: the centred prefix is **exactly constant**,

`A^{F_q}_ε(n) = q^{-ε}`  for every degree `n ≥ 1` and every damping (`fqCenteredPrefix_eq`),

so the critical energy is bounded by one, *uniformly in the damping and in the horizon*
(`fqEnergy_le_one`, `fqUniformlyAdmitsOn`), and the continuation budget is zero: in the
function-field model there is nothing to transport.

What plays the role of the damping is the same `q^{-ε}` twist, and the analogue of the open demand
(C) is not merely provable there — it is vacuous.  The reason is the exact vanishing of the
degree-wise Möbius sums beyond degree one: keeping the same centring and adding any positive mass at
degree two makes the prefix grow without bound (`exists_fqPerturbedPrefix_gt`).  So the calibration
places the whole number-field difficulty in the absence of that cancellation, not in the shape of
the transport mechanism.
-/

open Finset Filter GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The model -/

/-- The degree-wise Möbius sums of `F_q[T]`: `1, −q, 0, 0, …`. -/
def fqMobiusDegreeSum (q : ℕ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then -(q : ℝ) else 0

/-- The number of monic polynomials of degree at most `j`. -/
def fqMonicCount (q : ℕ) (j : ℕ) : ℝ := ∑ i ∈ range (j + 1), (q : ℝ) ^ i

/-- The function-field density `1/ζ(1+ε) = 1 − q^{-ε}`. -/
def fqDensity (q : ℕ) (ε : ℝ) : ℝ := 1 - (q : ℝ) ^ (-ε)

/-- The centred prefix of the damped function-field Möbius source. -/
def fqCenteredPrefix (q : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ range (n + 1), fqMobiusDegreeSum q k * (q : ℝ) ^ (-ε * (k : ℝ)) *
      fqMonicCount q (n - k)) -
    fqMonicCount q n * fqDensity q ε

/-- The critical energy of the model, with the same observation weight. -/
def fqEnergy (q : ℕ) (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, fqCenteredPrefix q ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-! ## §2. The counting identity -/

/-- `N(n) − q N(n−1) = 1`: one more monic polynomial than multiples of the linear ones. -/
theorem fqMonicCount_sub (q : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    fqMonicCount q n - (q : ℝ) * fqMonicCount q (n - 1) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [fqMonicCount, Nat.add_sub_cancel]
  rw [Finset.sum_range_succ' (fun i => (q : ℝ) ^ i) (m + 1), Finset.mul_sum]
  have hterm : ∀ i ∈ range (m + 1), (q : ℝ) * (q : ℝ) ^ i = (q : ℝ) ^ (i + 1) :=
    fun i _ => by rw [pow_succ]; ring
  rw [Finset.sum_congr rfl hterm]
  simp

theorem le_fqMonicCount {q : ℕ} (hq : 1 ≤ q) (j : ℕ) : ((j : ℝ) + 1) ≤ fqMonicCount q j := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hterm : ∀ i ∈ range (j + 1), (1 : ℝ) ≤ (q : ℝ) ^ i := fun i _ => one_le_pow₀ hq1
  have h := Finset.card_nsmul_le_sum (range (j + 1)) (fun i => (q : ℝ) ^ i) 1 hterm
  rw [nsmul_eq_mul, card_range, mul_one] at h
  rw [fqMonicCount]
  push_cast at h
  linarith

/-! ## §3. The centred prefix is exactly constant -/

/-- **The function-field centred source is constant.**  Only degrees zero and one contribute, and
the counting identity cancels everything but the damping factor. -/
theorem fqCenteredPrefix_eq (q : ℕ) (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    fqCenteredPrefix q ε n = (q : ℝ) ^ (-ε) := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (n + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [mem_range]
    rcases hk with rfl | rfl <;> omega
  have hzero : ∀ k ∈ range (n + 1), k ∉ ({0, 1} : Finset ℕ) →
      fqMobiusDegreeSum q k * (q : ℝ) ^ (-ε * (k : ℝ)) * fqMonicCount q (n - k) = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [fqMobiusDegreeSum, if_neg hk.1, if_neg hk.2]
    ring
  have hsum := (Finset.sum_subset hsub hzero).symm
  rw [fqCenteredPrefix, hsum, Finset.sum_insert (by simp), Finset.sum_singleton, fqDensity,
    fqMobiusDegreeSum, fqMobiusDegreeSum]
  norm_num
  have hcount := fqMonicCount_sub q hn
  linear_combination ((q : ℝ) ^ (-ε)) * hcount

/-! ## §4. Uniform admission at every damping, with budget zero -/

theorem fqEnergy_le_one {q : ℕ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 ≤ ε) (T : ℕ) :
    fqEnergy q ε T ≤ 1 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hA : ∀ n ∈ Icc 1 T, fqCenteredPrefix q ε n ^ 2 ≤ 1 := by
    intro n hn
    rw [fqCenteredPrefix_eq q ε (mem_Icc.mp hn).1]
    have h1 : (q : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
    have h0 : (0 : ℝ) ≤ (q : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg q) _
    nlinarith
  calc fqEnergy q ε T ≤ ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 := (mem_Icc.mp hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        exact div_le_div_of_nonneg_right (hA n hn) (by positivity)
    _ ≤ 1 := by
        rw [sum_Icc_pronic_mass]
        have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
        linarith

/-- **The calibration.**  In the function-field model the critical energy is bounded by one at every
damping and every horizon: uniform admission, with budget zero. -/
theorem fqUniformlyAdmitsOn {q : ℕ} (hq : 1 ≤ q) :
    UniformlyAdmitsOn (fqEnergy q) (Set.Ici (0 : ℝ)) :=
  ⟨1, fun _ hε T => fqEnergy_le_one hq (Set.mem_Ici.mp hε) T⟩

/-! ## §5. The vanishing beyond degree one is what makes it work -/

/-- The model perturbed by a mass `c` at degree two, with the same centring. -/
def fqPerturbedPrefix (q : ℕ) (c ε : ℝ) (n : ℕ) : ℝ :=
  fqCenteredPrefix q ε n + c * (q : ℝ) ^ (-ε * 2) * fqMonicCount q (n - 2)

/-- **A single extra degree destroys the constancy.**  With any positive mass at degree two the
prefix exceeds every bound, so the exact vanishing of the higher degree-wise Möbius sums is what
makes the function-field continuation free. -/
theorem exists_fqPerturbedPrefix_gt {q : ℕ} (hq : 1 ≤ q) {c ε : ℝ} (hc : 0 < c) (C : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ C < fqPerturbedPrefix q c ε n := by
  have hqpow : (0 : ℝ) < (q : ℝ) ^ (-ε * 2) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    exact Real.rpow_pos_of_pos hq0 _
  have hstep : 0 < c * (q : ℝ) ^ (-ε * 2) := mul_pos hc hqpow
  obtain ⟨N, hN⟩ := exists_nat_gt ((C + 1) / (c * (q : ℝ) ^ (-ε * 2)))
  refine ⟨N + 2, by omega, ?_⟩
  have hpre : fqCenteredPrefix q ε (N + 2) = (q : ℝ) ^ (-ε) :=
    fqCenteredPrefix_eq q ε (by omega)
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hcount : ((N : ℝ) + 1) ≤ fqMonicCount q (N + 2 - 2) := by
    have h : (N + 2 - 2 : ℕ) = N := by omega
    rw [h]
    exact le_fqMonicCount hq N
  have hkey : (C + 1) < c * (q : ℝ) ^ (-ε * 2) * (N : ℝ) := by
    rw [div_lt_iff₀ hstep] at hN
    linarith
  have hmono : c * (q : ℝ) ^ (-ε * 2) * (N : ℝ) ≤
      c * (q : ℝ) ^ (-ε * 2) * fqMonicCount q (N + 2 - 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hstep.le
    linarith
  rw [fqPerturbedPrefix, hpre]
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
