import GaloisForLFunctions.HTGeometry.StandardRationalExpansion
import GaloisForLFunctions.HTGeometry.PolygammaFactorialComparison

/-!
# The polygamma jets expand to arbitrary depth

Expanding the reciprocal power `x^{-(m+2)}` in reciprocal rising factorials to depth `K+1` and
summing over the shift orbit — the rising factorials sum in closed form, the remainder is a standard
rational function of defect `m+K+3` and is controlled by the orbit bound — gives, for every depth,

`ψ^{(m+1)}(σ+it) = ∑_{i≤K} b_i /(s(s+1)⋯(s+m+i)) + O(t^{-(m+2+K)})`

on every vertical line in the right half plane.  This is the asymptotic expansion the general form of
the residue law needs: the coefficients are explicit, and the error is smaller than every term kept.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- **The depth-`K+1` expansion of a polygamma jet on a vertical line.** -/
theorem exists_jet_expansion (m K : ℕ) :
    ∃ (b : ℕ → ℂ) (C : ℝ), 0 ≤ C ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ i ∈ Finset.range (K + 1),
            b i * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1 + i))⁻¹‖
        ≤ C / t ^ (m + 2 + K) := by
  classical
  obtain ⟨c, g, hg, hgval⟩ := (isStdRat_inv_pow (m + 2)).expansion (by omega) (K + 1)
  obtain ⟨Cg, hCg, hgbound⟩ := hg.exists_norm_le
  refine ⟨fun i => (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ) * c i * (((m + i : ℕ) : ℂ) + 1)⁻¹,
    (((m + 1).factorial : ℕ) : ℝ) * (4 * Cg), by positivity, fun σ t hσ ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have hshift : ∀ n : ℕ, (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re :=
    fun n => re_add_nat_pos hsre n
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
    intro n
    have := norm_vertical_add_nat_ge_im (σ := σ) t n
    linarith
  -- the termwise expansion of the reciprocal power
  have hterm : ∀ n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹
      = (∑ i ∈ Finset.range (K + 1),
          c i * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2 + i))⁻¹)
        + g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) :=
    fun n => hgval _ (hshift n)
  -- each rising factorial series sums in closed form
  have hrise : ∀ i : ℕ, HasSum
      (fun n : ℕ => (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2 + i))⁻¹)
      ((((m + i : ℕ) : ℂ) + 1)⁻¹
        * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + i + 1))⁻¹) := by
    intro i
    have h := hasSum_inv_risingProd hsre (m + i)
    have hidx : m + i + 2 = m + 2 + i := by omega
    rwa [hidx] at h
  -- the remainder is summable, with the orbit bound
  have hgnorm : ∀ n : ℕ, ‖g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖
      ≤ Cg * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (m + 2 + (K + 1)) :=
    fun n => hgbound _ (hshift n) (hone n)
  have hmajor : Summable (fun n : ℕ =>
      Cg * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (m + 2 + (K + 1))) :=
    (summable_norm_shift_inv_pow hσ t (k := m + 2 + (K + 1)) (by omega)).mul_left Cg
  have hgsummable : Summable (fun n : ℕ => g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgnorm hmajor)
  have hsum_rise : HasSum (fun n : ℕ => ∑ i ∈ Finset.range (K + 1),
      c i * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2 + i))⁻¹)
      (∑ i ∈ Finset.range (K + 1), c i * ((((m + i : ℕ) : ℂ) + 1)⁻¹
        * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + i + 1))⁻¹)) :=
    hasSum_sum (fun i _ => (hrise i).mul_left (c i))
  have htotal : HasSum (fun n : ℕ => (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
      ((∑ i ∈ Finset.range (K + 1), c i * ((((m + i : ℕ) : ℂ) + 1)⁻¹
          * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + i + 1))⁻¹))
        + ∑' n : ℕ, g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))) := by
    have heq : (fun n : ℕ => (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
        = fun n : ℕ => (∑ i ∈ Finset.range (K + 1),
            c i * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2 + i))⁻¹)
          + g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) := funext hterm
    rw [heq]
    exact hsum_rise.add hgsummable.hasSum
  have hpoly := hasSum_polygamma_series hσ t m
  have hval := hpoly.unique htotal
  -- pass to the jet
  have hfacne : (((m + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
  have hjet : iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      - ∑ i ∈ Finset.range (K + 1),
        ((-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ) * c i * (((m + i : ℕ) : ℂ) + 1)⁻¹)
          * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1 + i))⁻¹
      = (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ)
        * ∑' n : ℕ, g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) := by
    have hsq : ((-1 : ℂ)) ^ m * ((-1 : ℂ)) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have hidx : ∀ i : ℕ, m + i + 1 = m + 1 + i := by intro i; omega
    have hsum_eq : ∑ i ∈ Finset.range (K + 1),
        ((-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ) * c i * (((m + i : ℕ) : ℂ) + 1)⁻¹)
          * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1 + i))⁻¹
        = (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ)
          * ∑ i ∈ Finset.range (K + 1), c i * ((((m + i : ℕ) : ℂ) + 1)⁻¹
            * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + i + 1))⁻¹) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hidx i]
      ring
    rw [hsum_eq]
    have hpsi : iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ)
          * ((∑ i ∈ Finset.range (K + 1), c i * ((((m + i : ℕ) : ℂ) + 1)⁻¹
              * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + i + 1))⁻¹))
            + ∑' n : ℕ, g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))) := by
      rw [← hval, show ((-1 : ℂ)) ^ m * (((m + 1).factorial : ℕ) : ℂ)
          * (((-1 : ℂ)) ^ m / (((m + 1).factorial : ℕ) : ℂ)
            * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
          = (((-1 : ℂ)) ^ m * ((-1 : ℂ)) ^ m)
            * ((((m + 1).factorial : ℕ) : ℂ) / (((m + 1).factorial : ℕ) : ℂ))
            * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) from by
          field_simp]
      rw [hsq, div_self hfacne]
      ring
    rw [hpsi]
    ring
  rw [hjet, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  -- estimate the remainder sum
  have htail : ‖∑' n : ℕ, g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖
      ≤ 4 * Cg / t ^ (m + 2 + K) := by
    refine le_trans (norm_tsum_le_tsum_norm
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgnorm hmajor)) ?_
    refine le_trans (Summable.tsum_le_tsum hgnorm
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgnorm hmajor) hmajor) ?_
    rw [tsum_mul_left]
    have horbit := tsum_norm_shift_inv_pow_le hσ ht (m + K)
    have hidx : m + K + 3 = m + 2 + (K + 1) := by omega
    rw [hidx] at horbit
    have hstep : Cg * (∑' n : ℕ,
        ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (m + 2 + (K + 1)))
        ≤ Cg * (4 / t ^ (m + K + 2)) := mul_le_mul_of_nonneg_left horbit hCg
    refine le_trans hstep (le_of_eq ?_)
    have hidx2 : m + K + 2 = m + 2 + K := by omega
    rw [hidx2]
    ring
  have hfacnn : (0 : ℝ) ≤ (((m + 1).factorial : ℕ) : ℝ) := by positivity
  calc (((m + 1).factorial : ℕ) : ℝ)
        * ‖∑' n : ℕ, g ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖
      ≤ (((m + 1).factorial : ℕ) : ℝ) * (4 * Cg / t ^ (m + 2 + K)) :=
        mul_le_mul_of_nonneg_left htail hfacnn
    _ = (((m + 1).factorial : ℕ) : ℝ) * (4 * Cg) / t ^ (m + 2 + K) := by ring

end GaloisForLFunctions
