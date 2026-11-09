import GaloisForLFunctions.RHTower.HeadConditionedRoughDecoupling
import GaloisForLFunctions.RHTower.MontgomeryPhaseSeriesProducts

/-!
# Prime-head conditioning of the infinite rough current

The sharp integer-frequency mean-value theorem respects the exact factorization
of smooth and rough integers. Its error is the product of their weighted square
masses, with no dependence on a truncation cutoff. Absolute convergence then
admits the complete rough current. This form permits damping to vary with the
height horizon while retaining explicit dependence on the head probe.
-/

open Complex Filter Topology MeasureTheory RHTower
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

private theorem familyHeightPoly_sharp_mean {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (k : ι → ℕ) (a : ι → ℂ) (T : ℝ)
    (hk0 : ∀ q ∈ A, 0 < k q)
    (hinj : ∀ q ∈ A, ∀ q' ∈ A, k q = k q' → q = q') :
    |(∫ t in (0 : ℝ)..T, ‖familyHeightPoly A k a t‖ ^ 2) -
        T * ∑ q ∈ A, ‖a q‖ ^ 2| ≤
      104 * ∑ q ∈ A, (k q : ℝ) * ‖a q‖ ^ 2 := by
  let N := A.sup k
  have hkN : ∀ q ∈ A, k q ≤ N := fun q hq => Finset.le_sup hq
  have hmaps : ∀ q ∈ A, k q - 1 ∈ Finset.range N := by
    intro q hq
    have h0 := hk0 q hq
    have hN := hkN q hq
    exact Finset.mem_range.mpr (by omega)
  have hdiag : ∑ j : Fin N, ‖familyFibreCoeff A k a (j : ℕ)‖ ^ 2 =
      ∑ q ∈ A, ‖a q‖ ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖familyFibreCoeff A k a i‖ ^ 2) N]
    simp only [normSq_familyFibreCoeff hk0 hinj]
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  have hweight : ∑ j : Fin N, ((j : ℝ) + 1) * ‖familyFibreCoeff A k a (j : ℕ)‖ ^ 2 =
      ∑ q ∈ A, (k q : ℝ) * ‖a q‖ ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => ((i : ℝ) + 1) * ‖familyFibreCoeff A k a i‖ ^ 2) N]
    calc
      _ = ∑ i ∈ Finset.range N, ∑ q ∈ A with k q - 1 = i, (k q : ℝ) * ‖a q‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [normSq_familyFibreCoeff hk0 hinj, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        obtain ⟨hqA, hqi⟩ := Finset.mem_filter.mp hq
        have hk : k q = i + 1 := by have := hk0 q hqA; omega
        simp only [hk, Nat.cast_add, Nat.cast_one]
      _ = _ := Finset.sum_fiberwise_of_maps_to hmaps _
  have h := Sieve.dirichlet_meanValue_sharp N
    (fun j : Fin N => familyFibreCoeff A k a (j : ℕ)) T
  rw [hdiag, hweight] at h
  simpa only [familyHeightPoly_eq_dirPoly hk0 hkN] using h

/-- The sharp error for a finite smooth–rough product factors into weighted
square masses. Its constant is independent of the largest rough index. -/
theorem abs_integral_head_mul_roughPoly_sub_diag_le {Y : ℕ}
    (S M : Finset ℕ) (w a : ℕ → ℂ) (T : ℝ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers Y)
    (hM0 : ∀ n ∈ M, n ≠ 0)
    (hMr : ∀ n ∈ M, ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n) :
    |(∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2 * ‖integerHeightPoly M a t‖ ^ 2) -
        T * ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑ n ∈ M, ‖a n‖ ^ 2)| ≤
      104 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) * ∑ n ∈ M, (n : ℝ) * ‖a n‖ ^ 2 := by
  classical
  have hS0 : ∀ s ∈ S, s ≠ 0 := fun s hs => Nat.ne_zero_of_mem_smoothNumbers (hS s hs)
  have hk0 : ∀ q ∈ S ×ˢ M, 0 < q.1 * q.2 := by
    intro q hq
    obtain ⟨hs, hn⟩ := Finset.mem_product.mp hq
    exact Nat.mul_pos (Nat.pos_of_ne_zero (hS0 _ hs)) (Nat.pos_of_ne_zero (hM0 _ hn))
  have hinj : ∀ q ∈ S ×ˢ M, ∀ q' ∈ S ×ˢ M, q.1 * q.2 = q'.1 * q'.2 → q = q' := by
    intro q hq q' hq' he
    obtain ⟨hs, hn⟩ := Finset.mem_product.mp hq
    obtain ⟨hs', hn'⟩ := Finset.mem_product.mp hq'
    obtain ⟨h1, h2⟩ := smooth_rough_pair_unique (hS _ hs) (hM0 _ hn) (hMr _ hn)
      (hS _ hs') (hM0 _ hn') (hMr _ hn') he
    exact Prod.ext h1 h2
  have hdiag : (∑ q ∈ S ×ˢ M, ‖w q.1 * a q.2‖ ^ 2) =
      (∑ s ∈ S, ‖w s‖ ^ 2) * ∑ n ∈ M, ‖a n‖ ^ 2 := by
    simp only [Finset.sum_product, norm_mul, mul_pow, Finset.sum_mul_sum]
  have hweight : (∑ q ∈ S ×ˢ M, ((q.1 * q.2 : ℕ) : ℝ) * ‖w q.1 * a q.2‖ ^ 2) =
      (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) * ∑ n ∈ M, (n : ℝ) * ‖a n‖ ^ 2 := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun n _ => ?_
    simp only [Nat.cast_mul, norm_mul, mul_pow]
    ring
  have hprod : ∀ t : ℝ, ‖integerHeightPoly S w t‖ ^ 2 * ‖integerHeightPoly M a t‖ ^ 2 =
      ‖familyHeightPoly (S ×ˢ M) (fun q => q.1 * q.2) (fun q => w q.1 * a q.2) t‖ ^ 2 := by
    intro t
    rw [← integerHeightPoly_mul_eq_familyHeightPoly hS0 hM0, norm_mul, mul_pow]
  have h := familyHeightPoly_sharp_mean (S ×ˢ M) (fun q => q.1 * q.2)
    (fun q => w q.1 * a q.2) T hk0 hinj
  rw [hdiag, hweight] at h
  simpa only [hprod, mul_assoc] using h

/-- The full arithmetic phase series, with the same sign convention as the
finite height polynomials. -/
def integerHeightSeries (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  PhaseSeries.phaseSeries a (-t)

theorem partialSum_neg_eq_integerHeightPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    PhaseSeries.partialSum a N (-t) = integerHeightPoly (Finset.range N) a t := by
  simp only [PhaseSeries.partialSum, integerHeightPoly, familyHeightPoly, id_eq,
    neg_mul, Complex.ofReal_neg, neg_neg]

private theorem norm_integerHeightPoly_le (S : Finset ℕ) (w : ℕ → ℂ) (t : ℝ) :
    ‖integerHeightPoly S w t‖ ≤ ∑ s ∈ S, ‖w s‖ := by
  unfold integerHeightPoly familyHeightPoly
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The complete absolutely convergent rough current obeys the sharp
head-conditioned bracket. The error contains weighted square mass, never a
finite cutoff. -/
theorem abs_integral_head_mul_infiniteRough_sub_diag_le {Y : ℕ}
    (S : Finset ℕ) (w a : ℕ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers Y) (ha0 : a 0 = 0)
    (hr : ∀ n : ℕ, a n ≠ 0 → ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n)
    (ha : Summable fun n => ‖a n‖)
    (ha1 : Summable fun n : ℕ => (n : ℝ) * ‖a n‖ ^ 2) (T : ℝ) :
    |(∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2 * ‖integerHeightSeries a t‖ ^ 2) -
        T * ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑' n : ℕ, ‖a n‖ ^ 2)| ≤
      104 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) * ∑' n : ℕ, (n : ℝ) * ‖a n‖ ^ 2 := by
  classical
  have ha2 := PhaseSeries.summable_normSq_of_mul ha0 ha1
  have hfinite : ∀ N : ℕ,
      |(∫ t in (0 : ℝ)..T, ‖integerHeightPoly S w t‖ ^ 2 *
          ‖integerHeightPoly (Finset.range N) a t‖ ^ 2) -
        T * ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2)| ≤
      104 * (∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2) *
        ∑ n ∈ Finset.range N, (n : ℝ) * ‖a n‖ ^ 2 := by
    intro N
    let M := (Finset.range N).filter (fun n => a n ≠ 0)
    have hM0 : ∀ n ∈ M, n ≠ 0 := by
      intro n hn hz
      exact (Finset.mem_filter.mp hn).2 (hz ▸ ha0)
    have hMr : ∀ n ∈ M, ∀ p ∈ Nat.primesBelow Y, ¬ p ∣ n :=
      fun n hn => hr n (Finset.mem_filter.mp hn).2
    have hpoly : ∀ t : ℝ, integerHeightPoly M a t = integerHeightPoly (Finset.range N) a t := by
      intro t
      unfold integerHeightPoly familyHeightPoly
      dsimp [M]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : a n = 0 <;> simp [hn]
    have hs0 : (∑ n ∈ M, ‖a n‖ ^ 2) = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
      dsimp [M]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : a n = 0 <;> simp [hn]
    have hs1 : (∑ n ∈ M, (n : ℝ) * ‖a n‖ ^ 2) =
        ∑ n ∈ Finset.range N, (n : ℝ) * ‖a n‖ ^ 2 := by
      dsimp [M]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : a n = 0 <;> simp [hn]
    simpa only [hpoly, hs0, hs1] using abs_integral_head_mul_roughPoly_sub_diag_le S M w a T hS hM0 hMr
  have hpoint : ∀ t : ℝ, Tendsto (fun N : ℕ => integerHeightPoly (Finset.range N) a t)
      atTop (𝓝 (integerHeightSeries a t)) := by
    intro t
    have hs := (PhaseSeries.lseriesSummable ha0 ha (-t)).tendsto_sum_tsum_nat
    have he : ∀ N : ℕ, (∑ n ∈ Finset.range N, LSeries.term a ((-t : ℝ) * I) n) =
        integerHeightPoly (Finset.range N) a t := by
      intro N
      simp only [PhaseSeries.term_eq ha0]
      exact partialSum_neg_eq_integerHeightPoly a N t
    simpa only [he, integerHeightSeries, PhaseSeries.phaseSeries, LSeries] using hs
  have hbound : ∀ N t, ‖integerHeightPoly (Finset.range N) a t‖ ≤ ∑' n, ‖a n‖ := by
    intro N t
    rw [← partialSum_neg_eq_integerHeightPoly]
    exact PhaseSeries.norm_partialSum_le ha N (-t)
  have hint : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..T,
      ‖integerHeightPoly S w t‖ ^ 2 * ‖integerHeightPoly (Finset.range N) a t‖ ^ 2)
      atTop (𝓝 (∫ t in (0 : ℝ)..T,
        ‖integerHeightPoly S w t‖ ^ 2 * ‖integerHeightSeries a t‖ ^ 2)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => (∑ s ∈ S, ‖w s‖) ^ 2 * (∑' n, ‖a n‖) ^ 2)
    · exact Eventually.of_forall fun N =>
        (((continuous_integerHeightPoly S w).norm.pow 2).mul
          ((continuous_integerHeightPoly (Finset.range N) a).norm.pow 2)).aestronglyMeasurable
    · refine Eventually.of_forall fun N => Eventually.of_forall fun t _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_integerHeightPoly_le S w t) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hbound N t) 2) (by positivity) (by positivity)
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun t _ => tendsto_const_nhds.mul ((hpoint t).norm.pow 2)
  have hleft := (hint.sub
    ((ha2.tendsto_sum_tsum_nat.const_mul (∑ s ∈ S, ‖w s‖ ^ 2)).const_mul T)).abs
  have hright := ha1.tendsto_sum_tsum_nat.const_mul (104 * ∑ s ∈ S, (s : ℝ) * ‖w s‖ ^ 2)
  exact le_of_tendsto_of_tendsto' hleft hright hfinite

#print axioms abs_integral_head_mul_roughPoly_sub_diag_le
#print axioms abs_integral_head_mul_infiniteRough_sub_diag_le

end GaloisForLFunctions.EulerFETransportTheory
