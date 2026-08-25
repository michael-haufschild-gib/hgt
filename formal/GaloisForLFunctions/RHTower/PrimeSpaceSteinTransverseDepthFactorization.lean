import GaloisForLFunctions.RHTower.PrimeSpaceInertiaSteinLaw
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Transverse depth factorization of prime-space Stein response

The rank-two Stein displacement factors every finite, arbitrarily weighted prime packet into
products of response and bare boundary moments at each valuation depth. Boundary transversality
cancels depth zero exactly. The translated finite-packet residual vanishes cofinally, while a
weighted Vandermonde argument proves that a packet transverse at every depth must be zero.

Thus infinite completion loses no signed coefficient interference. It also cannot manufacture the
missing sign: after depth-zero cancellation, the products of shifted response and boundary moments
remain the exact obstruction.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def primeSpaceSteinPacketQuadratic
    {I : Type*} [Fintype I] (p : I → Nat.Primes)
    (response : Nat.Primes → ℝ) (c : I → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * primeSpaceSteinResponseKernel response (p i) (p j)

def primeSpaceSteinPacketBoundaryMoment
    {I : Type*} [Fintype I] (p : I → Nat.Primes)
    (c : I → ℝ) (n : ℕ) : ℝ :=
  ∑ i, c i * xiTransversePrimeApertureDiskNode 1 (p i) ^ n *
    primeSpaceSteinBoundaryVector (p i)

def primeSpaceSteinPacketResponseBoundaryMoment
    {I : Type*} [Fintype I] (p : I → Nat.Primes)
    (response : Nat.Primes → ℝ) (c : I → ℝ) (n : ℕ) : ℝ :=
  ∑ i, c i * xiTransversePrimeApertureDiskNode 1 (p i) ^ n *
    primeSpaceSteinResponseBoundaryVector response (p i)

def primeSpaceSteinPacketShift
    {I : Type*} (p : I → Nat.Primes) (c : I → ℝ) (N : ℕ) : I → ℝ :=
  fun i => c i * xiTransversePrimeApertureDiskNode 1 (p i) ^ N

private theorem finite_sum_rankTwo_factorization
    {I : Type*} [Fintype I]
    (c α β : I → ℝ) :
    (∑ i, ∑ j, c i * c j * (α i * β j + β i * α j)) =
      2 * (∑ i, c i * α i) * (∑ i, c i * β i) := by
  have hαβ : (∑ i, ∑ j, c i * c j * α i * β j) =
      (∑ i, c i * α i) * (∑ j, c j * β j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hβα : (∑ i, ∑ j, c i * c j * β i * α j) =
      (∑ i, c i * β i) * (∑ j, c j * α j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    (∑ i, ∑ j, c i * c j * (α i * β j + β i * α j)) =
        ∑ i, ∑ j,
          (c i * c j * α i * β j + c i * c j * β i * α j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, c i * c j * α i * β j) +
          (∑ i, ∑ j, c i * c j * β i * α j) := by
      simp_rw [Finset.sum_add_distrib]
    _ = 2 * (∑ i, c i * α i) * (∑ i, c i * β i) := by
      rw [hαβ, hβα]
      ring

theorem primeSpaceSteinPacketQuadratic_eq_depthPrefix_add_shift
    {I : Type*} [Fintype I]
    (N : ℕ) (p : I → Nat.Primes) (response : Nat.Primes → ℝ) (c : I → ℝ) :
    primeSpaceSteinPacketQuadratic p response c =
      2 * ∑ n ∈ Finset.range N,
        primeSpaceSteinPacketResponseBoundaryMoment p response c n *
          primeSpaceSteinPacketBoundaryMoment p c n +
      primeSpaceSteinPacketQuadratic p response (primeSpaceSteinPacketShift p c N) := by
  have hpoint (i j : I) :
      primeSpaceSteinResponseKernel response (p i) (p j) =
        (∑ n ∈ Finset.range N,
          (xiTransversePrimeApertureDiskNode 1 (p i) *
            xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
            (primeSpaceSteinResponseBoundaryVector response (p i) *
                primeSpaceSteinBoundaryVector (p j) +
              primeSpaceSteinBoundaryVector (p i) *
                primeSpaceSteinResponseBoundaryVector response (p j))) +
        (xiTransversePrimeApertureDiskNode 1 (p i) *
          xiTransversePrimeApertureDiskNode 1 (p j)) ^ N *
          primeSpaceSteinResponseKernel response (p i) (p j) := by
    have h := primeSpaceSteinResponseKernel_sub_prefix_eq_residual
      N response (p i) (p j)
    linarith
  have hdepth (n : ℕ) :
      (∑ i, ∑ j, c i * c j *
        ((xiTransversePrimeApertureDiskNode 1 (p i) *
          xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
          (primeSpaceSteinResponseBoundaryVector response (p i) *
              primeSpaceSteinBoundaryVector (p j) +
            primeSpaceSteinBoundaryVector (p i) *
              primeSpaceSteinResponseBoundaryVector response (p j)))) =
        2 * primeSpaceSteinPacketResponseBoundaryMoment p response c n *
          primeSpaceSteinPacketBoundaryMoment p c n := by
    rw [show (∑ i, ∑ j, c i * c j *
        ((xiTransversePrimeApertureDiskNode 1 (p i) *
          xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
          (primeSpaceSteinResponseBoundaryVector response (p i) *
              primeSpaceSteinBoundaryVector (p j) +
            primeSpaceSteinBoundaryVector (p i) *
              primeSpaceSteinResponseBoundaryVector response (p j)))) =
      ∑ i, ∑ j, c i * c j *
        ((xiTransversePrimeApertureDiskNode 1 (p i) ^ n *
            primeSpaceSteinResponseBoundaryVector response (p i)) *
          (xiTransversePrimeApertureDiskNode 1 (p j) ^ n *
            primeSpaceSteinBoundaryVector (p j)) +
        (xiTransversePrimeApertureDiskNode 1 (p i) ^ n *
            primeSpaceSteinBoundaryVector (p i)) *
          (xiTransversePrimeApertureDiskNode 1 (p j) ^ n *
            primeSpaceSteinResponseBoundaryVector response (p j))) by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      ring]
    rw [finite_sum_rankTwo_factorization]
    simp only [primeSpaceSteinPacketResponseBoundaryMoment,
      primeSpaceSteinPacketBoundaryMoment]
    ring
  have hprefix :
      (∑ i, ∑ j,
        c i * c j *
          (∑ n ∈ Finset.range N,
            (xiTransversePrimeApertureDiskNode 1 (p i) *
              xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
              (primeSpaceSteinResponseBoundaryVector response (p i) *
                  primeSpaceSteinBoundaryVector (p j) +
                primeSpaceSteinBoundaryVector (p i) *
                  primeSpaceSteinResponseBoundaryVector response (p j)))) =
        2 * ∑ n ∈ Finset.range N,
          primeSpaceSteinPacketResponseBoundaryMoment p response c n *
            primeSpaceSteinPacketBoundaryMoment p c n := by
    calc
      _ = ∑ i, ∑ j, ∑ n ∈ Finset.range N,
          c i * c j *
            ((xiTransversePrimeApertureDiskNode 1 (p i) *
              xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
              (primeSpaceSteinResponseBoundaryVector response (p i) *
                  primeSpaceSteinBoundaryVector (p j) +
                primeSpaceSteinBoundaryVector (p i) *
                  primeSpaceSteinResponseBoundaryVector response (p j))) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ i, ∑ n ∈ Finset.range N, ∑ j,
            c i * c j *
              ((xiTransversePrimeApertureDiskNode 1 (p i) *
                xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
                (primeSpaceSteinResponseBoundaryVector response (p i) *
                    primeSpaceSteinBoundaryVector (p j) +
                  primeSpaceSteinBoundaryVector (p i) *
                    primeSpaceSteinResponseBoundaryVector response (p j))) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
      _ = ∑ n ∈ Finset.range N, ∑ i, ∑ j,
            c i * c j *
              ((xiTransversePrimeApertureDiskNode 1 (p i) *
                xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
                (primeSpaceSteinResponseBoundaryVector response (p i) *
                    primeSpaceSteinBoundaryVector (p j) +
                  primeSpaceSteinBoundaryVector (p i) *
                    primeSpaceSteinResponseBoundaryVector response (p j))) := by
            rw [Finset.sum_comm]
      _ = ∑ n ∈ Finset.range N,
          2 * (primeSpaceSteinPacketResponseBoundaryMoment p response c n *
            primeSpaceSteinPacketBoundaryMoment p c n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hdepth]
        ring
      _ = 2 * ∑ n ∈ Finset.range N,
          primeSpaceSteinPacketResponseBoundaryMoment p response c n *
            primeSpaceSteinPacketBoundaryMoment p c n := by
        rw [Finset.mul_sum]
  have hresidual :
      (∑ i, ∑ j,
        c i * c j *
          ((xiTransversePrimeApertureDiskNode 1 (p i) *
            xiTransversePrimeApertureDiskNode 1 (p j)) ^ N *
              primeSpaceSteinResponseKernel response (p i) (p j))) =
        primeSpaceSteinPacketQuadratic p response
          (primeSpaceSteinPacketShift p c N) := by
    simp only [primeSpaceSteinPacketQuadratic,
      primeSpaceSteinPacketShift]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  change (∑ i, ∑ j,
      c i * c j * primeSpaceSteinResponseKernel response (p i) (p j)) = _
  calc
    _ = ∑ i, ∑ j,
        c i * c j *
          ((∑ n ∈ Finset.range N,
            (xiTransversePrimeApertureDiskNode 1 (p i) *
              xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
              (primeSpaceSteinResponseBoundaryVector response (p i) *
                  primeSpaceSteinBoundaryVector (p j) +
                primeSpaceSteinBoundaryVector (p i) *
                  primeSpaceSteinResponseBoundaryVector response (p j))) +
          (xiTransversePrimeApertureDiskNode 1 (p i) *
            xiTransversePrimeApertureDiskNode 1 (p j)) ^ N *
              primeSpaceSteinResponseKernel response (p i) (p j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun x => c i * c j * x) (hpoint i j)
    _ = (∑ i, ∑ j,
        c i * c j *
          (∑ n ∈ Finset.range N,
            (xiTransversePrimeApertureDiskNode 1 (p i) *
              xiTransversePrimeApertureDiskNode 1 (p j)) ^ n *
              (primeSpaceSteinResponseBoundaryVector response (p i) *
                  primeSpaceSteinBoundaryVector (p j) +
                primeSpaceSteinBoundaryVector (p i) *
                  primeSpaceSteinResponseBoundaryVector response (p j)))) +
      (∑ i, ∑ j,
        c i * c j *
          ((xiTransversePrimeApertureDiskNode 1 (p i) *
            xiTransversePrimeApertureDiskNode 1 (p j)) ^ N *
              primeSpaceSteinResponseKernel response (p i) (p j))) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
    _ = 2 * ∑ n ∈ Finset.range N,
          primeSpaceSteinPacketResponseBoundaryMoment p response c n *
            primeSpaceSteinPacketBoundaryMoment p c n +
        primeSpaceSteinPacketQuadratic p response
          (primeSpaceSteinPacketShift p c N) := by
      rw [hprefix, hresidual]

/-- Every finite packet's translated Stein residual vanishes at infinite valuation depth. -/
theorem tendsto_primeSpaceSteinPacketQuadratic_shift_atTop_zero
    {I : Type*} [Fintype I]
    (p : I → Nat.Primes) (response : Nat.Primes → ℝ) (c : I → ℝ) :
    Tendsto
      (fun N => primeSpaceSteinPacketQuadratic p response
        (primeSpaceSteinPacketShift p c N))
      atTop (nhds 0) := by
  have hterm (i j : I) :
      Tendsto
        (fun N =>
          (c i * xiTransversePrimeApertureDiskNode 1 (p i) ^ N) *
            (c j * xiTransversePrimeApertureDiskNode 1 (p j) ^ N) *
              primeSpaceSteinResponseKernel response (p i) (p j))
        atTop (nhds 0) := by
    let q := xiTransversePrimeApertureDiskNode 1 (p i)
    let r := xiTransversePrimeApertureDiskNode 1 (p j)
    have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos 1 (p i)).le
    have hq1 : q < 1 :=
      xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) (p i)
    have hr0 : 0 ≤ r := (xiTransversePrimeApertureDiskNode_pos 1 (p j)).le
    have hr1 : r < 1 :=
      xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) (p j)
    have hqr0 : 0 ≤ q * r := mul_nonneg hq0 hr0
    have hqr1 : q * r < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hq0 hq1 hr1.le
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hqr0 hqr1
    have hscaled := hpow.const_mul
      (c i * c j * primeSpaceSteinResponseKernel response (p i) (p j))
    simpa only [mul_zero, q, r, mul_pow] using hscaled.congr' (by
      filter_upwards with N
      ring)
  have hinner (i : I) :
      Tendsto
        (fun N => ∑ j,
          (c i * xiTransversePrimeApertureDiskNode 1 (p i) ^ N) *
            (c j * xiTransversePrimeApertureDiskNode 1 (p j) ^ N) *
              primeSpaceSteinResponseKernel response (p i) (p j))
        atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => hterm i j)
  have houter := tendsto_finsetSum Finset.univ (fun i _ => hinner i)
  simpa [primeSpaceSteinPacketQuadratic,
    primeSpaceSteinPacketShift] using houter

/-- Infinite completion of the exact signed depth factorization for arbitrary packet
coefficients. -/
theorem tendsto_primeSpaceSteinPacket_depthPrefix_atTop
    {I : Type*} [Fintype I]
    (p : I → Nat.Primes) (response : Nat.Primes → ℝ) (c : I → ℝ) :
    Tendsto
      (fun N => 2 * ∑ n ∈ Finset.range N,
        primeSpaceSteinPacketResponseBoundaryMoment p response c n *
          primeSpaceSteinPacketBoundaryMoment p c n)
      atTop (nhds (primeSpaceSteinPacketQuadratic p response c)) := by
  have hres := tendsto_primeSpaceSteinPacketQuadratic_shift_atTop_zero p response c
  have hconst : Tendsto
      (fun _ : ℕ => primeSpaceSteinPacketQuadratic p response c)
      atTop (nhds (primeSpaceSteinPacketQuadratic p response c)) :=
    tendsto_const_nhds
  have hsub := hconst.sub hres
  convert hsub using 1
  · funext N
    have hfactor :=
      primeSpaceSteinPacketQuadratic_eq_depthPrefix_add_shift N p response c
    linarith
  · simp

/-- On a boundary-transverse null line, the depth-zero interference cancels exactly; the complete
finite-depth response starts with the first shifted boundary moment. -/
theorem primeSpaceSteinPacketQuadratic_eq_positiveDepthPrefix_add_shift_of_transverse
    {I : Type*} [Fintype I]
    (N : ℕ) (p : I → Nat.Primes) (response : Nat.Primes → ℝ) (c : I → ℝ)
    (htransverse : primeSpaceSteinPacketBoundaryMoment p c 0 = 0) :
    primeSpaceSteinPacketQuadratic p response c =
      2 * ∑ n ∈ Finset.range N,
        primeSpaceSteinPacketResponseBoundaryMoment p response c (n + 1) *
          primeSpaceSteinPacketBoundaryMoment p c (n + 1) +
      primeSpaceSteinPacketQuadratic p response
        (primeSpaceSteinPacketShift p c (N + 1)) := by
  have h := primeSpaceSteinPacketQuadratic_eq_depthPrefix_add_shift
    (N + 1) p response c
  rw [Finset.sum_range_succ'] at h
  simp only [htransverse, mul_zero, add_zero] at h
  exact h

/-- Every prime boundary amplitude in the Stein displacement is strictly positive. -/
theorem primeSpaceSteinBoundaryVector_pos (p : Nat.Primes) :
    0 < primeSpaceSteinBoundaryVector p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) p
  simp only [primeSpaceSteinBoundaryVector]
  exact div_pos (mul_pos hq0 (sub_pos.mpr hq1)) (by linarith)

/-- Weighted Vandermonde rigidity: a finite packet transverse to every shifted boundary depth is
the zero packet. -/
theorem primeSpaceSteinPacketBoundaryMoment_allDepth_eq_zero_imp_coeff_zero
    {m : ℕ} (p : Fin m → Nat.Primes) (hp : Function.Injective p) (c : Fin m → ℝ)
    (hzero : ∀ n : Fin m, primeSpaceSteinPacketBoundaryMoment p c n = 0) :
    c = 0 := by
  let q : Fin m → ℝ := fun i => xiTransversePrimeApertureDiskNode 1 (p i)
  let a : Fin m → ℝ := fun i => c i * primeSpaceSteinBoundaryVector (p i)
  have hq : Function.Injective q :=
    xiTransversePrimeApertureDiskNode_one_injective.comp hp
  have hdet : (Matrix.vandermonde q).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    exact hq
  have hmul : Matrix.mulVec (Matrix.vandermonde q).transpose a = 0 := by
    funext n
    rw [Pi.zero_apply]
    have hn := hzero n
    simp only [primeSpaceSteinPacketBoundaryMoment] at hn
    rw [Matrix.mulVec, dotProduct]
    simpa only [Matrix.transpose_apply, Matrix.vandermonde_apply, q, a,
      mul_assoc, mul_comm, mul_left_comm] using hn
  have ha : a = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  funext i
  have hai := congrFun ha i
  simp only [a, Pi.zero_apply] at hai
  exact (mul_eq_zero.mp hai).resolve_right (ne_of_gt (primeSpaceSteinBoundaryVector_pos (p i)))

end

end RHTower

