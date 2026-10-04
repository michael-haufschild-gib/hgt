import GaloisForLFunctions.RHTower.BeurlingRandomPrimeDeletion
import GaloisForLFunctions.HTGeometry.DirichletSeriesBoundedPartialSums

/-!
# The zeta function of a square-root thinning of the primes

Let `0 < α < 1` and let `S` be a set of primes with square-root discrepancy against the weights
`p^{α−1}` at every frequency (`DeletionData`):

`|Σ_{p ≤ x} (1_S(p) − p^{α−1}) p^{−it}| ≤ C x^{α/2} (log x + 1) √log(|t| + 2)`.

**The correction series** (`corr`).  The Dirichlet series `Σ_p (1_S(p) − p^{α−1}) p^{−s}`
continues holomorphically to `Re s > α/2` (`differentiableOn_corr`), equals the series on
`Re s > 1` (`corr_eq_LSeries`), and grows at most like `√log |t|`:
`|corr(σ + it)| ≤ K_δ √log(|t| + 2)` for `σ ≥ α/2 + δ` (`norm_corr_le`).  The proof is partial
summation from the discrepancy bound (`HTGeometry.BoundedPartialSums`).

**Counting `S`** (`sum_indicator_le`).  `#{p ∈ S : p ≤ x} ≤ C' x^α (log x + 1)`, so
`Σ_{p ∈ S} p^{−σ}` converges for `σ > α`.
-/

open Complex Finset Filter Topology
open GaloisForLFunctions.HTGeometry.BoundedPartialSums

noncomputable section

namespace RHTower.BeurlingDeletion

/-- A set of primes with square-root discrepancy against `p^{α−1}` at every frequency. -/
structure DeletionData (α : ℝ) where
  S : Set ℕ
  prime : ∀ p ∈ S, p.Prime
  C : ℝ
  C_nonneg : 0 ≤ C
  disc : ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
    ‖∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      (S.indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * (p : ℂ) ^ (-((t : ℂ) * I))‖ ≤
      C * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt (Real.log (|t| + 2))

theorem exists_deletionData {α : ℝ} (hα0 : 0 < α) (hα : α < 1) : Nonempty (DeletionData α) := by
  obtain ⟨S, hS, C, hC, hdisc⟩ := exists_deletedPrimes hα0 hα
  exact ⟨⟨S, hS, C, hC, hdisc⟩⟩

variable {α : ℝ} (D : DeletionData α)

namespace DeletionData

/-- The coefficients `1_S(p) − p^{α−1}` on the primes. -/
def coeff (n : ℕ) : ℂ :=
  if n.Prime then D.S.indicator (fun _ => (1 : ℂ)) n - (delWeight α n : ℂ) else 0

theorem coeff_zero : D.coeff 0 = 0 := by simp [coeff, Nat.not_prime_zero]

theorem norm_coeff_le (hα : α < 1) (n : ℕ) : ‖D.coeff n‖ ≤ 2 := by
  classical
  unfold coeff
  split_ifs with hn
  · have hw : delWeight α n ≤ 1 := by
      unfold delWeight
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn.one_lt.le) (by linarith)
    have h1 : ‖D.S.indicator (fun _ => (1 : ℂ)) n‖ ≤ 1 := by
      rw [Set.indicator_apply]; split_ifs <;> simp
    calc _ ≤ ‖D.S.indicator (fun _ => (1 : ℂ)) n‖ + ‖(delWeight α n : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          gcongr
          rw [Complex.norm_real, Real.norm_of_nonneg (delWeight_nonneg α n)]; exact hw
      _ = 2 := by norm_num
  · simp

theorem range_succ_eq_Iic (n : ℕ) : Finset.range (n + 1) = Finset.Iic n := by
  ext m; simp

/-- The twisted partial sums are the discrepancy sums. -/
theorem partialSum_twisted (n : ℕ) (t : ℝ) :
    partialSum (LSeries.term D.coeff ((t : ℂ) * I)) (n + 1) =
      ∑ p ∈ (Finset.Iic n).filter Nat.Prime,
        (D.S.indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * (p : ℂ) ^ (-((t : ℂ) * I)) := by
  unfold partialSum
  rw [range_succ_eq_Iic, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [Nat.not_prime_zero]
  · rw [LSeries.term_of_ne_zero hp.ne', div_eq_mul_inv, ← Complex.cpow_neg, coeff]
    split_ifs <;> simp

theorem log_add_one_le {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x + 1 ≤ (1 + 2 / δ) * x ^ (δ / 2) := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x) (half_pos hδ)
  have h2 : (1 : ℝ) ≤ x ^ (δ / 2) := Real.one_le_rpow hx (by linarith)
  rw [show x ^ (δ / 2) / (δ / 2) = 2 / δ * x ^ (δ / 2) by field_simp] at h1
  nlinarith

/-- The constant of the twisted partial-sum bound at abscissa `α/2 + δ`. -/
def baseConst (δ : ℝ) : ℝ :=
  D.C * (1 + 2 / δ) * (1 + (α / 2 + δ) * ∑' i : ℕ, (i : ℝ) ^ (-δ / 2 - 1))

/-- **Bounded partial sums at every base point right of `α/2`.** -/
theorem norm_partialSum_le (hα0 : 0 < α) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (N : ℕ) :
    ‖∑ n ∈ range N, LSeries.term D.coeff (((α / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) n‖ ≤
      D.baseConst δ * Real.sqrt (Real.log (|t| + 2)) := by
  set L := Real.sqrt (Real.log (|t| + 2)) with hL
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hterm : ∀ n, LSeries.term D.coeff (((α / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) n =
      LSeries.term D.coeff ((t : ℂ) * I) n * powNeg ((α / 2 + δ : ℝ) : ℂ) n := by
    intro n
    rw [term_eq_mul_powNeg D.coeff ((t : ℂ) * I)]
    congr 2
    ring
  simp_rw [hterm]
  have hgrowth : ∀ n : ℕ, 1 ≤ n →
      ‖partialSum (LSeries.term D.coeff ((t : ℂ) * I)) (n + 1)‖ ≤
        (D.C * (1 + 2 / δ) * L) * (n : ℝ) ^ (α / 2 + δ / 2) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [D.partialSum_twisted]
    have h := D.disc (n : ℝ) hn1 t
    rw [Nat.floor_natCast] at h
    have hlog := log_add_one_le hδ hn1
    calc _ ≤ D.C * (n : ℝ) ^ (α / 2) * (Real.log n + 1) * L := h
      _ ≤ D.C * (n : ℝ) ^ (α / 2) * ((1 + 2 / δ) * (n : ℝ) ^ (δ / 2)) * L := by
          have := D.C_nonneg
          gcongr
      _ = (D.C * (1 + 2 / δ) * L) * (n : ℝ) ^ (α / 2 + δ / 2) := by
          rw [Real.rpow_add (by linarith)]; ring
  have h := norm_sum_mul_powNeg_le_of_growth (a := LSeries.term D.coeff ((t : ℂ) * I))
    (θ := α / 2 + δ / 2) (K := D.C * (1 + 2 / δ) * L) (by linarith)
    (by have := D.C_nonneg; positivity) (by simp) hgrowth
    (z := ((α / 2 + δ : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; linarith) N
  rw [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h
  rw [show α / 2 + δ / 2 - (α / 2 + δ) - 1 = -δ / 2 - 1 by ring] at h
  calc _ ≤ _ := h
    _ = D.baseConst δ * L := by unfold baseConst; ring

theorem baseConst_nonneg (hα0 : 0 < α) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ D.baseConst δ := by
  have := D.C_nonneg
  unfold baseConst
  have : 0 ≤ ∑' i : ℕ, (i : ℝ) ^ (-δ / 2 - 1) := tsum_nonneg fun i => by positivity
  positivity

/-! ## The continuation -/

/-- The base abscissa halfway to `α/2`. -/
def baseRe (α : ℝ) (s : ℂ) : ℝ := α / 2 + (s.re - α / 2) / 2

/-- **The correction series** `Σ_p (1_S(p) − p^{α−1}) p^{−s}`, continued to `Re s > α/2`. -/
def corr (s : ℂ) : ℂ := contLSeries D.coeff ((baseRe α s : ℝ) : ℂ) s

theorem corr_eq_cont (hα0 : 0 < α) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) {s : ℂ}
    (hs : α / 2 + δ < s.re) :
    D.corr s = contLSeries D.coeff (((α / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) s := by
  have hb : 0 < baseRe α s - α / 2 := by unfold baseRe; linarith
  have h0 := D.norm_partialSum_le hα0 hb 0
  have h1 := D.norm_partialSum_le hα0 hδ t
  simp only [Complex.ofReal_zero, zero_mul, add_zero, add_sub_cancel] at h0
  unfold corr
  refine contLSeries_eq_of_base h0 h1 ?_ ?_
  · rw [Complex.ofReal_re]; unfold baseRe; linarith
  · simp; linarith

theorem differentiableOn_corr (hα0 : 0 < α) : DifferentiableOn ℂ D.corr {s | α / 2 < s.re} := by
  intro s hs
  have hs' : α / 2 < s.re := hs
  set δ := (s.re - α / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hU : IsOpen {w : ℂ | α / 2 + δ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ {w : ℂ | α / 2 + δ < w.re} := by show α / 2 + δ < s.re; rw [hδ]; linarith
  have hev : D.corr =ᶠ[𝓝 s] contLSeries D.coeff (((α / 2 + δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) := by
    filter_upwards [hU.mem_nhds hsU] with w hw
    exact D.corr_eq_cont hα0 hδ0 0 hw
  have hd := differentiableOn_contLSeries (D.norm_partialSum_le hα0 hδ0 0)
  have hd' : DifferentiableAt ℂ (contLSeries D.coeff
      (((α / 2 + δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)) s :=
    hd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp; linarith))
  exact (hd'.congr_of_eventuallyEq hev).differentiableWithinAt

theorem lseriesSummable_coeff (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable D.coeff s :=
  LSeriesSummable_of_le_const_mul_rpow hs ⟨2, fun n _ => by
    simpa using D.norm_coeff_le hα n⟩

theorem corr_eq_LSeries (hα0 : 0 < α) (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    D.corr s = LSeries D.coeff s := by
  have hb : 0 < baseRe α s - α / 2 := by unfold baseRe; linarith
  have h0 := D.norm_partialSum_le hα0 hb 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, add_sub_cancel] at h0
  exact contLSeries_eq_LSeries h0 (by rw [Complex.ofReal_re]; unfold baseRe; linarith)
    (D.lseriesSummable_coeff hα hs)

/-- **The correction grows at most like `√log |t|`.** -/
theorem norm_corr_le (hα0 : 0 < α) {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : α / 2 + δ ≤ s.re) :
    ‖D.corr s‖ ≤ 3 * D.baseConst (δ / 2) * Real.sqrt (Real.log (|s.im| + 2)) := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  rw [D.corr_eq_cont hα0 hδ2 s.im (by linarith)]
  set b : ℂ := ((α / 2 + δ / 2 : ℝ) : ℂ) + (s.im : ℂ) * I with hbdef
  have hsplit : s = b + ((s.re - (α / 2 + δ / 2) : ℝ) : ℂ) := by
    rw [hbdef]; apply Complex.ext <;> simp
  have hb : 0 < s.re - (α / 2 + δ / 2) := by linarith
  have h := norm_contLSeries_add_ofReal_le (D.norm_partialSum_le hα0 hδ2 s.im) hb
  rw [← hbdef, ← hsplit] at h
  calc _ ≤ 3 * (D.baseConst (δ / 2) * Real.sqrt (Real.log (|s.im| + 2))) := h
    _ = _ := by ring

end DeletionData

end RHTower.BeurlingDeletion
