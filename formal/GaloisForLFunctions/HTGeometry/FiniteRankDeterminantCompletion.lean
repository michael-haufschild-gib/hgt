/-
# Finite-rank determinants exhaust the order-two completion

A kernel supported in a finite block `s × s` has an honest determinant, the characteristic
polynomial `det(1 − z·K|ₛ)` of its block.  This file identifies that polynomial with the
Hilbert--Carleman determinant of the kernel completed by its own diagonal trace,

  `det(1 − z·K|ₛ) = det₂(1 − zK)·e^{−z·tr K}`,

and then shows every completion is reached: for a Hilbert--Schmidt kernel `K` and *any* prescribed
scalar `c`, there are finitely supported kernels converging to `K` in Hilbert--Schmidt norm whose
honest determinants converge pointwise to `det₂(1 − zK)·e^{−cz}`.

Together with `tendsto_completionCoefficient`, which shows no other limits occur and that the
coordinate is continuous, this is the determinant-completion law at Schatten order two for a
one-dimensional pencil: the closure of the finite-rank determinant graph is exactly the completed
determinants, and the fibre is the single adjoined trace coordinate.

Main results:
* `entireDet2_eq_finiteDet2_of_support` — the regularized determinant of a block kernel.
* `det_one_sub_smul_blockMatrix` — the honest determinant is a completed determinant.
* `exists_finiteRank_det_tendsto_completedDet2` — every completion is a limit of honest
  finite-rank determinants.
-/
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantTraceRecovery
import GaloisForLFunctions.HTGeometry.FiniteRankTracePrescription

open HilbertSchmidt Metric Filter

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} [DecidableEq ι]

/-! ## Kernels supported in a finite block -/

/-- Truncation to a block containing the support is the identity. -/
theorem truncKernel_eq_self_of_support {K : ι × ι → ℂ} {s : Finset ι}
    (h : ∀ p : ι × ι, p ∉ s ×ˢ s → K p = 0) : truncKernel K s = K := by
  funext p
  by_cases hp : p.1 ∈ s ∧ p.2 ∈ s
  · simp [truncKernel, hp]
  · have hz : K p = 0 := h p fun hcon => hp (Finset.mem_product.mp hcon)
    simp [truncKernel, hp, hz]

omit [DecidableEq ι] in
/-- For a kernel supported in a finite block the diagonal trace is the trace of the block. -/
theorem trace_blockMatrix_eq_hsTraceDiag {K : ι × ι → ℂ} {s : Finset ι}
    (h : ∀ p : ι × ι, p ∉ s ×ˢ s → K p = 0) :
    (blockMatrix K s).trace = hsTraceDiag K := by
  have hvanish : ∀ i : ι, i ∉ s → K (i, i) = 0 := fun i hi =>
    h (i, i) (by simp [Finset.mem_product, hi])
  rw [hsTraceDiag, tsum_eq_sum hvanish, Matrix.trace]
  simpa [blockMatrix] using Finset.sum_coe_sort s fun i => K (i, i)

/-- **The regularized determinant of a block kernel is the finite one.** -/
theorem entireDet2_eq_finiteDet2_of_support {K : ι × ι → ℂ} (hK : IsHS K) {s : Finset ι}
    (h : ∀ p : ι × ι, p ∉ s ×ˢ s → K p = 0) :
    entireDet2 K = fun z => finiteDet2 (-(blockMatrix K s)) z := by
  refine (isRegularizedDet_entireDet2 hK).unique
    ⟨differentiable_finiteDet2 _, detRadius K, detRadius_pos K, detRadius_mul_hsNorm_lt K,
      fun z hz => ?_⟩
  have hzr : ‖z‖ < detRadius K := by rwa [mem_ball_zero_iff] at hz
  have hbound : ‖z‖ * hsNorm (truncKernel K s) < 1 := by
    rw [truncKernel_eq_self_of_support h]
    calc ‖z‖ * hsNorm K
        ≤ detRadius K * hsNorm K := mul_le_mul_of_nonneg_right hzr.le (hsNorm_nonneg K)
      _ < 1 := detRadius_mul_hsNorm_lt K
  have hfd := fredholmDet_truncKernel_eq K s hbound
  rw [truncKernel_eq_self_of_support h] at hfd
  exact hfd.symm

/-- **The honest determinant of a finite block is a completed regularized determinant**, with the
completion coordinate equal to the diagonal trace of the kernel. -/
theorem det_one_sub_smul_blockMatrix {K : ι × ι → ℂ} (hK : IsHS K) {s : Finset ι}
    (h : ∀ p : ι × ι, p ∉ s ×ˢ s → K p = 0) (z : ℂ) :
    ((1 : Matrix ↥s ↥s ℂ) - z • blockMatrix K s).det = completedDet2 K (hsTraceDiag K) z := by
  have htr : (blockMatrix K s).trace = hsTraceDiag K := trace_blockMatrix_eq_hsTraceDiag h
  have hE : entireDet2 K z = finiteDet2 (-(blockMatrix K s)) z :=
    congrFun (entireDet2_eq_finiteDet2_of_support hK h) z
  have hfd : finiteDet2 (-(blockMatrix K s)) z
      = ((1 : Matrix ↥s ↥s ℂ) - z • blockMatrix K s).det
        * Complex.exp (z * (blockMatrix K s).trace) := by
    rw [finiteDet2, Matrix.trace_neg, smul_neg, ← sub_eq_add_neg]
    congr 2
    ring
  rw [completedDet2, hE, hfd, ← htr, mul_assoc, ← Complex.exp_add]
  have hzero : z * (blockMatrix K s).trace + -(z * (blockMatrix K s).trace) = 0 := by ring
  rw [hzero, Complex.exp_zero, mul_one]

/-! ## Every completion is a limit of honest finite-rank determinants -/

/-- **Sufficiency in the determinant-completion law at Schatten order two.**  For every
Hilbert--Schmidt kernel and every prescribed completion coordinate there are finitely supported
kernels converging to it in Hilbert--Schmidt norm whose honest block determinants converge
pointwise to the prescribed completed determinant.

The trace is genuinely free in the limit: spreading it over ever more diagonal entries costs no
Hilbert--Schmidt energy. -/
theorem exists_finiteRank_det_tendsto_completedDet2 {K : ℕ × ℕ → ℂ} (hK : IsHS K) (c : ℂ) :
    ∃ (N : ℕ → ℕ) (K' : ℕ → (ℕ × ℕ → ℂ)),
      (∀ k, ∀ p : ℕ × ℕ, p ∉ (Finset.range (N k)) ×ˢ (Finset.range (N k)) → K' k p = 0) ∧
      (∀ k, IsHS (K' k)) ∧
      Tendsto (fun k => hsNorm (K' k - K)) atTop (nhds 0) ∧
      ∀ z : ℂ, Tendsto (fun k =>
          ((1 : Matrix ↥(Finset.range (N k)) ↥(Finset.range (N k)) ℂ)
            - z • blockMatrix (K' k) (Finset.range (N k))).det)
        atTop (nhds (completedDet2 K c z)) := by
  choose N K' hsupp hHS hnorm htr using fun k : ℕ =>
    exists_finiteSupport_hsNorm_sub_lt_and_hsTraceDiag_eq hK c
      (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
  have hlim0 : Tendsto (fun k => hsNorm (K' k - K)) atTop (nhds 0) :=
    squeeze_zero (fun k => hsNorm_nonneg _) (fun k => (hnorm k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨N, K', hsupp, hHS, hlim0, fun z => ?_⟩
  have h2 := tendsto_entireDet2_of_hsNorm_sub_tendsto_zero K' K hHS hK hlim0 z
  have h3 : Tendsto (fun k => completedDet2 (K' k) c z) atTop (nhds (completedDet2 K c z)) :=
    h2.mul_const (Complex.exp (-(z * c)))
  refine h3.congr fun k => ?_
  rw [← htr k]
  exact (det_one_sub_smul_blockMatrix (hHS k) (hsupp k) z).symm
