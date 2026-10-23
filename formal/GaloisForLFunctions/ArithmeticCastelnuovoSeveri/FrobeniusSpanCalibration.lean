import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AdjunctionThresholdLaw
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Dist

/-!
# The Frobenius span: Weil's form is the Castelnuovo–Severi defect

For a curve `C/𝔽_q` of genus `g` with Frobenius eigenvalues `α₁, …, α_{2g}`, write `β = α/√q`
for the normalized eigenvalues and `Γ_k` for the graph of the `k`-th power of Frobenius on
`C × C` (`Γ₀ = Δ`). The intersection numbers on the span of the `Γ_k` are dictated by two
classical formulas, both read off a single **Lefschetz number**
`N_j = q^j + 1 − q^{j/2} Σ_i β_i^j` (`pointCount`):

* **Lefschetz / pull-back:** `Γ_k · Γ_l = q^{min(k,l)} N_{|k−l|}`; for `l = 0` this is the point
  count `Γ_k · Δ = N_k = #C(𝔽_{q^k})`;
* **adjunction:** `Γ_k² = q^k (2 − 2g)`; it is the same formula at lag `0`, where the Lefschetz
  number is the Euler characteristic `N_0 = 2 − 2g` (`graphPair_self`).

The fibres meet the graphs in `Γ_k · H = 1`, `Γ_k · V = q^k`. Then the Castelnuovo–Severi defect
of a span class `D = Σ d_k Γ_k` is a **Toeplitz form in the power sums**
(`spanDefect_eq_toeplitz`):

    2(D·H)(D·V) − D² = Σ_{k,l} e_k e_l Re(Σ_i β_i^{|k−l|}),   e_k = q^{k/2} d_k,

which is Weil's explicit formula over `𝔽_q`: the pole plane `q^{±j/2}` is the polar part, the
point counts are the prime side, the genus `2g = Σ_i β_i^0` is the lag-`0` (adjunction) term.

If every `|β_i| = 1` the Toeplitz form is `Σ_i |Σ_k e_k β_i^k|²` (`toeplitz_eq_sum_normSq`);
conversely its `2 × 2` minors at lags `0, j` bound the power sums by the genus
(`norm_powerSum_le`). Both directions together are the equivalence of Hodge index on the span
with RH for the datum (`FrobeniusSpanHodgeIndexIsRH`).
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A **curve datum**: field size `q > 1` and normalized Frobenius eigenvalues `β i = α i/√q`
indexed by a finite type `ι` (with multiplicity), closed under complex conjugation and under the
functional equation `α ↦ q/α`, i.e. `β ↦ β⁻¹`. The genus is `#ι/2`. -/
structure CurveDatum (ι : Type*) [Fintype ι] where
  q : ℝ
  one_lt_q : 1 < q
  β : ι → ℂ
  conjPerm : Equiv.Perm ι
  β_conjPerm : ∀ i, β (conjPerm i) = starRingEnd ℂ (β i)
  fePerm : Equiv.Perm ι
  β_fePerm : ∀ i, β (fePerm i) * β i = 1

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The power sum `Σ_i β_i^j`. -/
def powerSum (j : ℕ) : ℂ := ∑ i, D.β i ^ j

/-- The real trace `Re Σ_i β_i^j`; the power sum is real by conjugation symmetry. -/
def trace (j : ℕ) : ℝ := (D.powerSum j).re

theorem conj_powerSum (j : ℕ) : starRingEnd ℂ (D.powerSum j) = D.powerSum j := by
  unfold powerSum
  rw [map_sum]
  simp_rw [map_pow, ← D.β_conjPerm]
  exact Equiv.sum_comp D.conjPerm (fun i => D.β i ^ j)

theorem powerSum_eq_trace (j : ℕ) : D.powerSum j = (D.trace j : ℂ) :=
  (Complex.conj_eq_iff_re.mp (D.conj_powerSum j)).symm

theorem trace_zero : D.trace 0 = Fintype.card ι := by
  simp [trace, powerSum]

/-- `√q`. -/
def sqrtq : ℝ := Real.sqrt D.q

theorem sqrtq_pos : 0 < D.sqrtq := Real.sqrt_pos.mpr (by linarith [D.one_lt_q])

theorem sqrtq_sq : D.sqrtq ^ 2 = D.q := Real.sq_sqrt (by linarith [D.one_lt_q])

/-- The **Lefschetz number** `N_j = q^j + 1 − q^{j/2} Σ_i β_i^j`; `N_0 = 2 − 2g`. -/
def pointCount (j : ℕ) : ℝ := D.q ^ j + 1 - D.sqrtq ^ j * D.trace j

theorem pointCount_zero : D.pointCount 0 = 2 - Fintype.card ι := by
  simp [pointCount, trace_zero]; ring

/-- The pairing of Frobenius graphs, `Γ_k · Γ_l = q^{min(k,l)} N_{|k−l|}`. -/
def graphPair (k l : ℕ) : ℝ := D.q ^ min k l * D.pointCount (Nat.dist k l)

theorem graphPair_comm (k l : ℕ) : D.graphPair k l = D.graphPair l k := by
  simp only [graphPair, min_comm, Nat.dist_comm]

/-- **Adjunction**: `Γ_k² = q^k (2 − 2g)`. -/
theorem graphPair_self (k : ℕ) : D.graphPair k k = D.q ^ k * (2 - Fintype.card ι) := by
  simp [graphPair, Nat.dist_self, pointCount_zero]

/-- **Lefschetz**: `Γ_k · Δ = N_k`. -/
theorem graphPair_zero (k : ℕ) : D.graphPair k 0 = D.pointCount k := by
  simp [graphPair, Nat.dist_zero_right]

/-- The Castelnuovo–Severi defect `2(D·H)(D·V) − D²` of `D = Σ_{k ∈ S} d_k Γ_k`, with
`Γ_k · H = 1` and `Γ_k · V = q^k`. -/
def spanDefect (S : Finset ℕ) (d : ℕ → ℝ) : ℝ :=
  2 * (∑ k ∈ S, d k) * (∑ k ∈ S, d k * D.q ^ k) - ∑ k ∈ S, ∑ l ∈ S, d k * d l * D.graphPair k l

/-- The Toeplitz form of the power sums, `Σ_{k,l} e_k e_l Re(Σ_i β_i^{|k−l|})`. -/
def toeplitz (S : Finset ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ k ∈ S, ∑ l ∈ S, e k * e l * D.trace (Nat.dist k l)

/-- The exponent bookkeeping `min + dist = max` and `2 min + dist = k + l`. -/
theorem min_add_dist (k l : ℕ) :
    min k l + Nat.dist k l = max k l ∧ 2 * min k l + Nat.dist k l = k + l := by
  rcases le_total k l with h | h
  · rw [min_eq_left h, max_eq_right h, Nat.dist_eq_sub_of_le h]; omega
  · rw [min_eq_right h, max_eq_left h, Nat.dist_comm, Nat.dist_eq_sub_of_le h]; omega

theorem graphPair_entry (k l : ℕ) :
    D.q ^ k + D.q ^ l - D.graphPair k l
      = D.sqrtq ^ k * D.sqrtq ^ l * D.trace (Nat.dist k l) := by
  obtain ⟨h1, h2⟩ := min_add_dist k l
  have hq : D.q = D.sqrtq ^ 2 := D.sqrtq_sq.symm
  have hkl : D.q ^ k + D.q ^ l = D.q ^ min k l * D.q ^ Nat.dist k l + D.q ^ min k l := by
    rw [← pow_add, h1]
    rcases le_total k l with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]
  have hs : D.q ^ min k l * D.sqrtq ^ Nat.dist k l = D.sqrtq ^ k * D.sqrtq ^ l := by
    rw [hq, ← pow_mul, ← pow_add, ← pow_add, h2]
  rw [hkl, graphPair, pointCount, ← hs]
  ring

/-- **The defect of a span class is the Toeplitz form of the power sums**, in the normalized
coefficients `e_k = q^{k/2} d_k`. -/
theorem spanDefect_eq_toeplitz (S : Finset ℕ) (d : ℕ → ℝ) :
    D.spanDefect S d = D.toeplitz S (fun k => d k * D.sqrtq ^ k) := by
  have hpol : 2 * (∑ k ∈ S, d k) * (∑ k ∈ S, d k * D.q ^ k)
      = ∑ k ∈ S, ∑ l ∈ S, d k * d l * (D.q ^ k + D.q ^ l) := by
    have e1 : ∑ k ∈ S, ∑ l ∈ S, d k * d l * (D.q ^ k + D.q ^ l)
        = (∑ k ∈ S, d k * D.q ^ k) * (∑ l ∈ S, d l)
          + (∑ k ∈ S, d k) * (∑ l ∈ S, d l * D.q ^ l) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e1]; ring
  rw [spanDefect, hpol, ← Finset.sum_sub_distrib, toeplitz]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_sub, graphPair_entry]
  ring

/-- On the unit circle `Re(β^k β̄^l) = Re β^{|k−l|}`. -/
theorem re_pow_mul_conj_pow {b : ℂ} (hb : ‖b‖ = 1) (k l : ℕ) :
    (b ^ k * starRingEnd ℂ b ^ l).re = (b ^ Nat.dist k l).re := by
  have hbb : b * starRingEnd ℂ b = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hb]; norm_num
  rcases le_total k l with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, hbb,
      one_pow, one_mul, ← map_pow, Complex.conj_re]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left, pow_add, mul_comm,
      ← mul_assoc, ← mul_pow, mul_comm (starRingEnd ℂ b), hbb, one_pow, one_mul]

/-- **Unitary data: the defect is a sum of squares**, `Σ_i |Σ_k e_k β_i^k|²`. -/
theorem toeplitz_eq_sum_normSq (hU : ∀ i, ‖D.β i‖ = 1) (S : Finset ℕ) (e : ℕ → ℝ) :
    D.toeplitz S e = ∑ i, ‖∑ k ∈ S, (e k : ℂ) * D.β i ^ k‖ ^ 2 := by
  have hsq : ∀ i, ‖∑ k ∈ S, (e k : ℂ) * D.β i ^ k‖ ^ 2
      = ∑ k ∈ S, ∑ l ∈ S, e k * e l * (D.β i ^ k * starRingEnd ℂ (D.β i) ^ l).re := by
    intro i
    have key : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := fun z => by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    rw [key, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal, map_pow]
    have : (e k : ℂ) * D.β i ^ k * ((e l : ℂ) * starRingEnd ℂ (D.β i) ^ l)
        = ((e k * e l : ℝ) : ℂ) * (D.β i ^ k * starRingEnd ℂ (D.β i) ^ l) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  simp_rw [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [re_pow_mul_conj_pow (hU _)]
  rw [trace, powerSum, Complex.re_sum]

/-- A span class at the two lags `0, j`: `(1 + t²)·2g + 2t Re Σ β^j`. -/
theorem toeplitz_pair (j : ℕ) (hj : j ≠ 0) (t : ℝ) :
    D.toeplitz {0, j} (fun k => if k = 0 then 1 else t)
      = (1 + t ^ 2) * Fintype.card ι + 2 * t * D.trace j := by
  rw [toeplitz, Finset.sum_pair (Ne.symm hj), Finset.sum_pair (Ne.symm hj),
    Finset.sum_pair (Ne.symm hj)]
  simp [hj, Nat.dist_self, Nat.dist_zero_left, Nat.dist_zero_right, trace_zero]
  ring

/-- **The genus bounds the power sums**: positivity of the defect on the span forces
`|Σ_i β_i^j| ≤ 2g` at every lag. -/
theorem norm_powerSum_le (h : ∀ S e, 0 ≤ D.toeplitz S e) (j : ℕ) :
    ‖D.powerSum j‖ ≤ Fintype.card ι := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [D.powerSum_eq_trace, trace_zero]
  have h1 := h {0, j} (fun k => if k = 0 then 1 else 1)
  have h2 := h {0, j} (fun k => if k = 0 then 1 else -1)
  rw [toeplitz_pair D j hj] at h1 h2
  rw [D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- **Genus zero (`𝔽_q[T]`)**: the defect vanishes identically on the span, and every span class
is Castelnuovo–Severi extremal. -/
theorem spanDefect_eq_zero_of_genusZero [IsEmpty ι] (S : Finset ℕ) (d : ℕ → ℝ) :
    D.spanDefect S d = 0 := by
  rw [spanDefect_eq_toeplitz, toeplitz]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  simp [trace, powerSum]

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
