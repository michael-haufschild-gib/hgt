import GaloisForLFunctions.RHTower.SmoothAFEFinitePrimeCofactorModes
import GaloisForLFunctions.RHTower.SmoothAFEZetaRightReflectedPrimalEnergyEvent

/-!
# Literal reflected-primal channels through smoothed cofactor modes

A logarithmic shift of cofactor phases absorbs the common height exactly. The actual
largest-prime channel then factors through the fixed-node Gaussian cofactor vector, with
its exact floor-dependent smoothing scale. A second identity separates the conductor scale,
common row phase, cofactor length, and fixed-node floor correction.

The floor correction approaches one uniformly as the cofactor length grows. This supplies
the literal channel bridge for the independent covariance construction; it does not assert
a target law or recurrence.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower

/-- Add a logarithmic phase so each multiplicative character acquires `n^(i*tau)`. -/
def steinhausLogPhaseShift (omega : SteinhausModel.Omega) (tau : ℝ) : SteinhausModel.Omega :=
  fun p => omega p + tau * Real.log p / (2 * Real.pi)

/-- The logarithmic phase shift absorbs the literal common-height power. -/
theorem X_steinhausLogPhaseShift (omega : SteinhausModel.Omega) (tau : ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    SteinhausModel.X n (steinhausLogPhaseShift omega tau) =
      SteinhausModel.X n omega * (n : ℂ) ^ ((tau : ℂ) * I) := by
  have hphase : (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
        (omega p + tau * Real.log p / (2 * Real.pi))) =
      (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * omega p) +
        tau / (2 * Real.pi) * Real.log n := by
    rw [Real.log_nat_eq_sum_factorization]
    simp only [Finsupp.sum, Nat.support_factorization, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  unfold SteinhausModel.X steinhausLogPhaseShift
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), hlog, ← Complex.exp_add, hphase]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem nat_mul_cpow (p m : ℕ) (z : ℂ) :
    ((p * m : ℕ) : ℂ) ^ z = (p : ℂ) ^ z * (m : ℂ) ^ z := by
  simpa only [Complex.ofReal_natCast, Nat.cast_mul] using
    (Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg m) z)

/-- Rewrite the actual positive-index AFE coefficient without its zero-based index. -/
theorem reflectedPrimalPositiveCoefficient_eq_power_cutoff
    (d tau r : ℝ) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N n =
      zetaChi (rightDisplacedLinePt d tau) * (n : ℂ) ^ (rightDisplacedLinePt d tau - 1) *
        smoothAFECutoff (r * ((n : ℝ) / N)) := by
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hidxC : (↑(n - 1) + 1 : ℂ) = n := by exact_mod_cast hindex
  have hidxR : (↑(n - 1) + 1 : ℝ) = n := by exact_mod_cast hindex
  unfold smoothAFEZetaRightReflectedPrimalPositiveCoefficient smoothAFEZetaRightReflectedPrimalCoefficient
  rw [hidxC, hidxR]
  congr 1
  congr 1
  simp only [div_div_eq_mul_div]
  ring

/-- Exact literal prime-channel factorization through a fixed-node smoothed cofactor vector.
The common height is absorbed by the cofactor phase shift before the floor is normalized. -/
theorem reflectedPrimalChannel_eq_smoothCofactor
    {J : ℕ} (d b : Fin J → ℝ) (tau r : ℝ) (N p : ℕ)
    (hp : 0 < p) (hL : 0 < N / p) (omega : SteinhausModel.Omega) (j : Fin J) :
    steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N) N p omega =
      (zetaChi (rightDisplacedLinePt (d j) (tau + b j)) *
        (p : ℂ) ^ (rightDisplacedLinePt (d j) (tau + b j) - 1) *
        ((N / p : ℕ) : ℂ) ^ (rightDisplacedLinePt (d j) (b j))) *
      smoothCofactorNodeVector (fun j => rightDisplacedLinePt (d j) (b j))
        (r * (p : ℝ) * (N / p : ℕ) / N) (N / p) (steinhausLogPhaseShift omega tau) j := by
  let L := N / p
  let s := rightDisplacedLinePt (d j) (b j)
  let z := rightDisplacedLinePt (d j) (tau + b j)
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le hL (Nat.div_le_self N p)))
  have hz : z - 1 = (s - 1) + (tau : ℂ) * I := by
    simp only [s, z, rightDisplacedLinePt, Complex.ofReal_add]
    ring
  have hcancel : (L : ℂ) ^ s * (L : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hLC, add_neg_cancel, Complex.cpow_zero]
  have hterm : ∀ m ∈ Icc 1 L,
      smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N (p * m) *
        SteinhausModel.X m omega =
      (zetaChi z * (p : ℂ) ^ (z - 1)) *
        (smoothAFECutoff ((r * (p : ℝ) * L / N) * ((m : ℝ) / L)) *
          SteinhausModel.X m (steinhausLogPhaseShift omega tau) * (m : ℂ) ^ (s - 1)) := by
    intro m hm
    have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hm).1
    rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ (Nat.mul_pos hp hmpos),
      nat_mul_cpow, X_steinhausLogPhaseShift omega tau (ne_of_gt hmpos)]
    change _ = (zetaChi z * (p : ℂ) ^ (z - 1)) * _
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
    have hpow : (m : ℂ) ^ (z - 1) = (m : ℂ) ^ (s - 1) *
        (m : ℂ) ^ ((tau : ℂ) * I) := by rw [hz, Complex.cpow_add _ _ hmC]
    have hcut : r * (((p * m : ℕ) : ℝ) / N) =
        (r * (p : ℝ) * L / N) * ((m : ℝ) / L) := by
      push_cast
      field_simp
    change zetaChi z * ((p : ℂ) ^ (z - 1) * (m : ℂ) ^ (z - 1)) * _ * _ = _
    rw [hpow, hcut]
    ring
  unfold steinhausLargePrimeChannel
  change (∑ m ∈ Icc 1 L, _) = _
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  change (zetaChi z * (p : ℂ) ^ (z - 1)) * (∑ m ∈ Icc 1 L, _) =
    (zetaChi z * (p : ℂ) ^ (z - 1) * (L : ℂ) ^ s) *
      ((∑ m ∈ Icc 1 L, _) * (L : ℂ) ^ (-s))
  calc
    _ = (zetaChi z * (p : ℂ) ^ (z - 1)) * (∑ m ∈ Icc 1 L, _) *
        ((L : ℂ) ^ s * (L : ℂ) ^ (-s)) := by rw [hcancel, mul_one]
    _ = _ := by ring

/-- The floor correction left by a literal prime channel after normalization. -/
def primeCofactorFloorRatio (N p : ℕ) : ℝ := (p : ℝ) * (N / p : ℕ) / N

/-- The integer cofactor cutoff places the correction in a shrinking interval below one. -/
theorem primeCofactorFloorRatio_bounds {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (hL : 0 < N / p) :
    0 < primeCofactorFloorRatio N p ∧ primeCofactorFloorRatio N p ≤ 1 ∧
      ((N / p : ℕ) : ℝ) / ((N / p : ℕ) + 1) < primeCofactorFloorRatio N p := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hLR : (0 : ℝ) < (N / p : ℕ) := by exact_mod_cast hL
  have hle : (p : ℝ) * (N / p : ℕ) ≤ N := by exact_mod_cast Nat.mul_div_le N p
  have hlt : (N : ℝ) < (p : ℝ) * ((N / p : ℕ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N hp
  refine ⟨div_pos (mul_pos hpR hLR) hNR, (div_le_one hNR).mpr hle, ?_⟩
  rw [primeCofactorFloorRatio, div_lt_div_iff₀ (by positivity) hNR]
  nlinarith

/-- After a sufficiently large cofactor cutoff, its complex floor factor is uniformly
close to one for every actual prime channel. The exponent is fixed, with no moving height. -/
theorem exists_primeCofactorFloorRatio_cpow_close (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, 0 < B ∧ ∀ N p : ℕ, 0 < N → 0 < p → B ≤ N / p →
      ‖(primeCofactorFloorRatio N p : ℂ) ^ z - 1‖ < ε := by
  have hc : ContinuousAt (fun x : ℝ => (x : ℂ) ^ z) 1 :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr one_ne_zero)
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc ε hε
  obtain ⟨C, hC⟩ := exists_nat_gt (1 / δ)
  refine ⟨C + 1, by omega, ?_⟩
  intro N p hN hp hL
  obtain ⟨_, hqle, hqlt⟩ := primeCofactorFloorRatio_bounds hN hp (by omega)
  have hCδ : 1 < (C : ℝ) * δ := (div_lt_iff₀ hδ).mp hC
  have hCL : (C : ℝ) ≤ (N / p : ℕ) := by exact_mod_cast (show C ≤ N / p by omega)
  have hLδ : 1 < ((N / p : ℕ) : ℝ) * δ := hCδ.trans_le (mul_le_mul_of_nonneg_right hCL hδ.le)
  have hnear : 1 - δ < ((N / p : ℕ) : ℝ) / ((N / p : ℕ) + 1) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hdist : dist (primeCofactorFloorRatio N p) 1 < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hqle)]
    linarith
  simpa only [Complex.ofReal_one, Complex.one_cpow, dist_eq_norm] using hcont hdist

/-- Separate the conductor scale, common unit row phase, and fixed-node floor factor. -/
theorem reflectedPrimalChannel_eq_normalized_smoothCofactor
    {J : ℕ} (d b : Fin J → ℝ) (tau r : ℝ) (N p : ℕ)
    (hp : 0 < p) (hL : 0 < N / p) (omega : SteinhausModel.Omega) (j : Fin J) :
    steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N) N p omega =
      (zetaChi (rightDisplacedLinePt (d j) (tau + b j)) *
        (N : ℂ) ^ (rightDisplacedLinePt (d j) (tau + b j) - 1)) *
      (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I) * (N / p : ℕ) *
      (primeCofactorFloorRatio N p : ℂ) ^ (rightDisplacedLinePt (d j) (b j) - 1) *
      smoothCofactorNodeVector (fun j => rightDisplacedLinePt (d j) (b j))
        (r * primeCofactorFloorRatio N p) (N / p) (steinhausLogPhaseShift omega tau) j := by
  let L := N / p
  let s := rightDisplacedLinePt (d j) (b j)
  let z := rightDisplacedLinePt (d j) (tau + b j)
  let q := primeCofactorFloorRatio N p
  have hN := lt_of_lt_of_le hL (Nat.div_le_self N p)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hqR : 0 < q := (primeCofactorFloorRatio_bounds hN hp hL).1
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hz : z - 1 = s - 1 + (tau : ℂ) * I := by
    simp only [z, s, rightDisplacedLinePt, Complex.ofReal_add]
    ring
  have hscale : (N : ℂ) * (q : ℂ) = (p : ℂ) * (L : ℂ) := by
    dsimp only [q, primeCofactorFloorRatio, L]
    push_cast
    field_simp
  have hqpow : (N : ℂ) ^ (s - 1) * (q : ℂ) ^ (s - 1) =
      (p : ℂ) ^ (s - 1) * (L : ℂ) ^ (s - 1) := by
    have h₁ := Complex.mul_cpow_ofReal_nonneg hNR.le hqR.le (s - 1)
    have h₂ := Complex.mul_cpow_ofReal_nonneg hpR.le hLR.le (s - 1)
    simp only [Complex.ofReal_natCast] at h₁ h₂
    rw [← h₁, hscale, h₂]
  have hheight : (N : ℂ) ^ ((tau : ℂ) * I) *
      (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I) = (p : ℂ) ^ ((tau : ℂ) * I) := by
    have h := Complex.mul_cpow_ofReal_nonneg hNR.le (div_pos hpR hNR).le ((tau : ℂ) * I)
    have hinner : (N : ℝ) * ((p : ℝ) / N) = p := by field_simp
    rw [← Complex.ofReal_mul, hinner] at h
    simpa only [Complex.ofReal_natCast] using h.symm
  have hLp : (L : ℂ) ^ s = (L : ℂ) ^ (s - 1) * (L : ℂ) := by
    calc
      (L : ℂ) ^ s = (L : ℂ) ^ (s - 1 + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hLC, Complex.cpow_one]
  have hfactor : (p : ℂ) ^ (z - 1) * (L : ℂ) ^ s =
      (N : ℂ) ^ (z - 1) * (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I) *
        (L : ℂ) * (q : ℂ) ^ (s - 1) := by
    rw [hz, Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hNC, hLp]
    calc
      _ = ((p : ℂ) ^ (s - 1) * (L : ℂ) ^ (s - 1)) *
          (p : ℂ) ^ ((tau : ℂ) * I) * (L : ℂ) := by ring
      _ = ((N : ℂ) ^ (s - 1) * (q : ℂ) ^ (s - 1)) *
          ((N : ℂ) ^ ((tau : ℂ) * I) *
            (((p : ℝ) / N : ℝ) : ℂ) ^ ((tau : ℂ) * I)) * (L : ℂ) := by rw [hqpow, hheight]
      _ = _ := by ring
  have hrscale : r * (p : ℝ) * (N / p : ℕ) / N = r * q := by
    dsimp only [q, primeCofactorFloorRatio]
    ring
  rw [reflectedPrimalChannel_eq_smoothCofactor d b tau r N p hp hL omega j, hrscale]
  change (zetaChi z * (p : ℂ) ^ (z - 1) * (L : ℂ) ^ s) * _ =
    (zetaChi z * (N : ℂ) ^ (z - 1)) * _ * (L : ℂ) * (q : ℂ) ^ (s - 1) * _
  rw [mul_assoc (zetaChi z), hfactor]
  ring

end RHTower
