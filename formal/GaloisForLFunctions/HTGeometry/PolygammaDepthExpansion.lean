import GaloisForLFunctions.HTGeometry.StandardRationalExpansion
import GaloisForLFunctions.HTGeometry.WeightedProductBound
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

/-- The depth-`K` approximation of a jet is a standard rational function of the jet's own defect. -/
theorem exists_jet_stdRat_approx (m K : ℕ) :
    ∃ (F : ℂ → ℂ) (C : ℝ), IsStdRat F (m + 1) ∧ 0 ≤ C ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / t ^ (m + 2 + K) := by
  obtain ⟨b, C, hC, hbound⟩ := exists_jet_expansion m K
  refine ⟨fun x => ∑ i ∈ Finset.range (K + 1), b i * (risingProd x (m + 1 + i))⁻¹, C, ?_, hC,
    fun σ t hσ ht => hbound σ t hσ ht⟩
  refine IsStdRat.sum (Finset.range (K + 1)) _ fun i _ => ?_
  exact ((isStdRat_inv_risingProd (m + 1 + i)).const_mul (b i)).mono (by omega)

/-- **The jet package.**  Each jet, its depth-`K` standard approximation, and the error, all measured
against the powers of `1/t` that the weighted product estimate consumes. -/
theorem exists_jet_package (m K : ℕ) :
    ∃ (F : ℂ → ℂ) (A : ℝ), IsStdRat F (m + 1) ∧ 1 ≤ A ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ A * (1 / t) ^ (m + 1)
        ∧ ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 / t) ^ (m + 1)
        ∧ ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
            - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 / t) ^ (m + 1 + K) := by
  obtain ⟨F, C, hFstd, hC, hFbound⟩ := exists_jet_stdRat_approx m K
  obtain ⟨CF, hCF, hFsize⟩ := hFstd.exists_norm_le
  refine ⟨F, C + CF + 1, hFstd, by linarith, fun σ t hσ ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have hu0 : (0 : ℝ) ≤ 1 / t := by positivity
  have hu1 : (1 : ℝ) / t ≤ 1 := by
    rw [div_le_one htpos]
    linarith
  have hsre : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have hnormge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    calc t = |((σ : ℂ) + (t : ℂ) * Complex.I).im| := by rw [him, abs_of_nonneg htpos.le]
      _ ≤ _ := Complex.abs_im_le_norm _
  have hone : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
  have hinv : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖⁻¹ ≤ 1 / t := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le htpos hnormge
  have hinvpow : ∀ k : ℕ, ‖(σ : ℂ) + (t : ℂ) * Complex.I‖⁻¹ ^ k ≤ (1 / t) ^ k :=
    fun k => pow_le_pow_left₀ (by positivity) hinv k
  -- the approximant
  have hFsz : ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CF * (1 / t) ^ (m + 1) := by
    refine le_trans (hFsize _ hsre hone) ?_
    exact mul_le_mul_of_nonneg_left (hinvpow (m + 1)) hCF
  -- the error
  have herr : ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 / t) ^ (m + 1 + K) := by
    refine le_trans (hFbound σ t hσ ht) ?_
    have hpow : (1 / t) ^ (m + 2 + K) ≤ (1 / t) ^ (m + 1 + K) :=
      pow_le_pow_of_le_one hu0 hu1 (by omega)
    have hdiv : C / t ^ (m + 2 + K) = C * (1 / t) ^ (m + 2 + K) := by
      rw [div_pow, one_pow]
      ring
    rw [hdiv]
    exact mul_le_mul_of_nonneg_left hpow hC
  have hpow0 : (0 : ℝ) ≤ (1 / t) ^ (m + 1) := by positivity
  have herr' : ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (1 / t) ^ (m + 1) := by
    refine le_trans herr ?_
    have hpow : (1 / t) ^ (m + 1 + K) ≤ (1 / t) ^ (m + 1) :=
      pow_le_pow_of_le_one hu0 hu1 (by omega)
    exact mul_le_mul_of_nonneg_left hpow hC
  refine ⟨?_, ?_, ?_⟩
  · have hsplit : iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          - F ((σ : ℂ) + (t : ℂ) * Complex.I)) + F ((σ : ℂ) + (t : ℂ) * Complex.I) := by ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have : C * (1 / t) ^ (m + 1) + CF * (1 / t) ^ (m + 1)
        ≤ (C + CF + 1) * (1 / t) ^ (m + 1) := by nlinarith
    linarith [herr', hFsz]
  · refine le_trans hFsz ?_
    have hle : CF ≤ C + CF + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hle hpow0
  · refine le_trans herr ?_
    have hle : C ≤ C + CF + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **The power package.**  A power of a jet, its standard approximation, and the error, at the
weight `(m+1)·e`. -/
theorem exists_jet_pow_package (m K e : ℕ) :
    ∃ (F : ℂ → ℂ) (A : ℝ), IsStdRat F ((m + 1) * e) ∧ 1 ≤ A ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e‖
          ≤ A * (1 / t) ^ ((m + 1) * e)
        ∧ ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 / t) ^ ((m + 1) * e)
        ∧ ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e
            - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 / t) ^ ((m + 1) * e + K) := by
  classical
  obtain ⟨F, A, hFstd, hA, hpkg⟩ := exists_jet_package m K
  refine ⟨fun x => F x ^ e, (e : ℝ) * A ^ e + A ^ e + 1, ?_, ?_, fun σ t hσ ht => ?_⟩
  · have := hFstd.pow e
    rwa [] at this
  · have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
    have : (0 : ℝ) ≤ (e : ℝ) * A ^ e := by positivity
    have h1 : (1 : ℝ) ≤ A ^ e := one_le_pow₀ hA
    linarith
  · have htpos : (0 : ℝ) < t := by linarith
    have hu0 : (0 : ℝ) ≤ 1 / t := by positivity
    obtain ⟨hjet, hF, herr⟩ := hpkg σ t hσ ht
    -- constant families over `Finset.range e`
    have hjetc : ∀ i ∈ Finset.range e,
        ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ A * (1 / t) ^ (m + 1) := fun i _ => hjet
    have hFc : ∀ i ∈ Finset.range e, ‖F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ A * (1 / t) ^ (m + 1) := fun i _ => hF
    have herrc : ∀ i ∈ Finset.range e,
        ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * (1 / t) ^ (m + 1 + K) := fun i _ => herr
    have hprodjet := norm_prod_le_mul_pow
      (fun _ : ℕ => iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      (fun _ : ℕ => m + 1) hA hu0 (Finset.range e) hjetc
    have hprodF := norm_prod_le_mul_pow
      (fun _ : ℕ => F ((σ : ℂ) + (t : ℂ) * Complex.I))
      (fun _ : ℕ => m + 1) hA hu0 (Finset.range e) hFc
    have hproderr := norm_prod_sub_prod_mul_pow_le
      (fun _ : ℕ => iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      (fun _ : ℕ => F ((σ : ℂ) + (t : ℂ) * Complex.I))
      (fun _ : ℕ => m + 1) hA hu0 K (Finset.range e) hjetc hFc herrc
    rw [Finset.prod_const, Finset.card_range, Finset.sum_const, Finset.card_range,
      smul_eq_mul] at hprodjet
    rw [Finset.prod_const, Finset.card_range, Finset.sum_const, Finset.card_range,
      smul_eq_mul] at hprodF
    rw [Finset.prod_const, Finset.prod_const, Finset.card_range, Finset.sum_const,
      Finset.card_range, smul_eq_mul] at hproderr
    have hmulcomm : e * (m + 1) = (m + 1) * e := by ring
    rw [hmulcomm] at hprodjet hprodF hproderr
    have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
    have hAe : (1 : ℝ) ≤ A ^ e := one_le_pow₀ hA
    have hpow0 : (0 : ℝ) ≤ (1 / t) ^ ((m + 1) * e) := by positivity
    have hpow0' : (0 : ℝ) ≤ (1 / t) ^ ((m + 1) * e + K) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · refine le_trans hprodjet ?_
      have hle : A ^ e ≤ (e : ℝ) * A ^ e + A ^ e + 1 := by
        have : (0 : ℝ) ≤ (e : ℝ) * A ^ e := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right hle hpow0
    · show ‖F ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e‖ ≤ _
      refine le_trans hprodF ?_
      have hle : A ^ e ≤ (e : ℝ) * A ^ e + A ^ e + 1 := by
        have : (0 : ℝ) ≤ (e : ℝ) * A ^ e := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right hle hpow0
    · show ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e
        - F ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e‖ ≤ _
      refine le_trans hproderr ?_
      have hle : (e : ℝ) * A ^ e ≤ (e : ℝ) * A ^ e + A ^ e + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hle hpow0'

/-- **The monomial package.**  A monomial in the digamma jets is approximated, to the monomial weight
plus the depth, by a standard rational function of that weight. -/
theorem exists_monomial_package (N K : ℕ) (e : Fin N → ℕ) :
    ∃ (F : ℂ → ℂ) (A : ℝ), IsStdRat F (∑ i : Fin N, ((i : ℕ) + 1) * e i) ∧ 1 ≤ A ∧
      ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
        ‖(∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e i)
            - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ A * (1 / t) ^ ((∑ i : Fin N, ((i : ℕ) + 1) * e i) + K) := by
  classical
  choose F A hstd hA hpkg using fun i : Fin N => exists_jet_pow_package (i : ℕ) K (e i)
  set B : ℝ := 1 + ∑ i : Fin N, A i with hB
  have hAle : ∀ i : Fin N, A i ≤ B := by
    intro i
    have hsum : A i ≤ ∑ j : Fin N, A j :=
      Finset.single_le_sum (f := A) (fun j _ => le_trans zero_le_one (hA j)) (Finset.mem_univ i)
    rw [hB]
    linarith
  have hB1 : 1 ≤ B := by
    have hnn : (0 : ℝ) ≤ ∑ j : Fin N, A j :=
      Finset.sum_nonneg fun j _ => le_trans zero_le_one (hA j)
    rw [hB]
    linarith
  refine ⟨fun x => ∏ i : Fin N, F i x, (N : ℝ) * B ^ N + 1,
    IsStdRat.prod Finset.univ (fun i => F i) (fun i => ((i : ℕ) + 1) * e i)
      (fun i _ => hstd i), ?_, fun σ t hσ ht => ?_⟩
  · have hnn : (0 : ℝ) ≤ (N : ℝ) * B ^ N := by
      have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
      positivity
    linarith
  have htpos : (0 : ℝ) < t := by linarith
  have hu0 : (0 : ℝ) ≤ 1 / t := by positivity
  have hsize : ∀ i : Fin N,
      ‖iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e i‖
        ≤ B * (1 / t) ^ (((i : ℕ) + 1) * e i) := by
    intro i
    refine le_trans (hpkg i σ t hσ ht).1 ?_
    exact mul_le_mul_of_nonneg_right (hAle i) (by positivity)
  have hsizeF : ∀ i : Fin N, ‖F i ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ B * (1 / t) ^ (((i : ℕ) + 1) * e i) := by
    intro i
    refine le_trans (hpkg i σ t hσ ht).2.1 ?_
    exact mul_le_mul_of_nonneg_right (hAle i) (by positivity)
  have herr : ∀ i : Fin N,
      ‖iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e i
          - F i ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ B * (1 / t) ^ (((i : ℕ) + 1) * e i + K) := by
    intro i
    refine le_trans (hpkg i σ t hσ ht).2.2 ?_
    exact mul_le_mul_of_nonneg_right (hAle i) (by positivity)
  have hprod := norm_prod_sub_prod_mul_pow_le
    (fun i : Fin N => iteratedDeriv ((i : ℕ) + 1) Complex.digamma
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e i)
    (fun i : Fin N => F i ((σ : ℂ) + (t : ℂ) * Complex.I))
    (fun i : Fin N => ((i : ℕ) + 1) * e i) hB1 hu0 K Finset.univ
    (fun i _ => hsize i) (fun i _ => hsizeF i) (fun i _ => herr i)
  rw [Finset.card_univ, Fintype.card_fin] at hprod
  refine le_trans hprod ?_
  have hle : (N : ℝ) * B ^ N ≤ (N : ℝ) * B ^ N + 1 := by linarith
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **The jet-polynomial package.**  A finite combination of jet monomials, all of weight at least
`W`, is approximated to depth `K` by a standard rational function of defect `W`. -/
theorem exists_jetPoly_package (N M K W : ℕ) (e : Fin M → Fin N → ℕ) (a : Fin M → ℂ)
    (hW : ∀ α : Fin M, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) :
    ∃ (F : ℂ → ℂ) (A : ℝ), IsStdRat F W ∧ 1 ≤ A ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖(∑ α : Fin M, a α * ∏ i : Fin N,
            iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
          - F ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ A * (1 / t) ^ (W + K) := by
  classical
  choose F A hstd hA hpkg using fun α : Fin M => exists_monomial_package N K (e α)
  refine ⟨fun x => ∑ α : Fin M, a α * F α x, 1 + ∑ α : Fin M, ‖a α‖ * A α, ?_, ?_,
    fun σ t hσ ht => ?_⟩
  · refine IsStdRat.sum Finset.univ _ fun α _ => ?_
    exact ((hstd α).const_mul (a α)).mono (hW α)
  · have hnn : (0 : ℝ) ≤ ∑ α : Fin M, ‖a α‖ * A α :=
      Finset.sum_nonneg fun α _ => by
        have := le_trans zero_le_one (hA α)
        positivity
    linarith
  · have htpos : (0 : ℝ) < t := by linarith
    have hu0 : (0 : ℝ) ≤ 1 / t := by positivity
    have hu1 : (1 : ℝ) / t ≤ 1 := by
      rw [div_le_one htpos]
      linarith
    have hsplit : (∑ α : Fin M, a α * ∏ i : Fin N,
          iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
        - (∑ α : Fin M, a α * F α ((σ : ℂ) + (t : ℂ) * Complex.I))
        = ∑ α : Fin M, a α * ((∏ i : Fin N,
            iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
          - F α ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      ring
    show ‖(∑ α : Fin M, a α * ∏ i : Fin N,
        iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
      - ∑ α : Fin M, a α * F α ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ _
    rw [hsplit]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ α : Fin M, ‖a α * ((∏ i : Fin N,
          iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
        - F α ((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ (‖a α‖ * A α) * (1 / t) ^ (W + K) := by
      intro α
      rw [norm_mul]
      have hpow : (1 / t) ^ ((∑ i : Fin N, ((i : ℕ) + 1) * e α i) + K) ≤ (1 / t) ^ (W + K) :=
        pow_le_pow_of_le_one hu0 hu1 (by have := hW α; omega)
      have hstep : ‖(∏ i : Fin N,
            iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
          - F α ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A α * (1 / t) ^ (W + K) := by
        refine le_trans (hpkg α σ t hσ ht) ?_
        exact mul_le_mul_of_nonneg_left hpow (le_trans zero_le_one (hA α))
      calc ‖a α‖ * ‖(∏ i : Fin N,
              iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)
            - F α ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖a α‖ * (A α * (1 / t) ^ (W + K)) :=
            mul_le_mul_of_nonneg_left hstep (norm_nonneg _)
        _ = (‖a α‖ * A α) * (1 / t) ^ (W + K) := by ring
    refine le_trans (Finset.sum_le_sum fun α _ => hterm α) ?_
    rw [← Finset.sum_mul]
    have hle : (∑ α : Fin M, ‖a α‖ * A α) ≤ 1 + ∑ α : Fin M, ‖a α‖ * A α := by linarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)

end GaloisForLFunctions
