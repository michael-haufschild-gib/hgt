import GaloisForLFunctions.HTGeometry.TopSumMajorization
import GaloisForLFunctions.ArithmeticElectrostatics.TheLogarithmicDepthThresholdIsALimit
import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatDivisorObeysLogarithmicThresholds

/-!
# Products of the deepest surviving polynomial roots

Threshold sums are the hinge tests for weak majorization after taking
logarithms. Their comparison bounds every product of the largest surviving
elapsed squared depths by the corresponding initial product. The vectors
may have different lengths because nonreal pairs can collide with the axis.
-/

open Finset Polynomial Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

theorem topSum_le_threshold_hinge {n k : ℕ} (v : Fin n → ℝ) (hk : k ≤ n) (b : ℝ) :
    topSum k v ≤ (k : ℝ) * b + ∑ i, max (v i - b) 0 := by
  obtain ⟨S, hcard, hsum⟩ := exists_sum_eq_topSum v hk
  rw [← hsum]
  calc
    (∑ i ∈ S, v i) ≤ ∑ i ∈ S, (b + max (v i - b) 0) := by
      apply Finset.sum_le_sum
      intro i _
      linarith only [le_max_left (v i - b) 0]
    _ = (k : ℝ) * b + ∑ i ∈ S, max (v i - b) 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => le_max_right _ _))

/-- The `k`th largest coordinate is a supporting threshold for the top sum. -/
theorem exists_threshold_hinge_eq_topSum {n k : ℕ} (v : Fin n → ℝ)
    (hk0 : 0 < k) (hk : k ≤ n) :
    ∃ b : ℝ, (k : ℝ) * b + ∑ i, max (v i - b) 0 = topSum k v := by
  classical
  let q : Fin n := ⟨k - 1, by omega⟩
  let b := sortDesc v q
  have hsort : (∑ i, max (sortDesc v i - b) 0) = ∑ i, max (v i - b) 0 :=
    Equiv.sum_comp (descPerm v) (fun i => max (v i - b) 0)
  have hdrop : (∑ i, max (sortDesc v i - b) 0) =
      ∑ i ∈ firstIdx n k, (sortDesc v i - b) := by
    calc
      _ = ∑ i, if i ∈ firstIdx n k then sortDesc v i - b else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ firstIdx n k
        · have hle : i ≤ q := by
            change i.val ≤ q.val
            dsimp only [q]
            have h := mem_firstIdx.mp hi
            omega
          rw [if_pos hi, max_eq_left (sub_nonneg.mpr (antitone_sortDesc v hle))]
        · have hle : q ≤ i := by
            change q.val ≤ i.val
            dsimp only [q]
            have h : ¬ i.val < k := fun h => hi (mem_firstIdx.mpr h)
            omega
          rw [if_neg hi, max_eq_right (sub_nonpos.mpr (antitone_sortDesc v hle))]
      _ = _ := by simp
  refine ⟨b, ?_⟩
  rw [← hsort, hdrop, Finset.sum_sub_distrib, Finset.sum_const, card_firstIdx hk, nsmul_eq_mul,
    topSum]
  ring

/-- Hinge comparisons control top sums even when the vectors have different lengths. -/
theorem topSum_le_of_all_threshold_hinges {n m k : ℕ} (v : Fin n → ℝ) (w : Fin m → ℝ)
    (hkn : k ≤ n) (hkm : k ≤ m)
    (h : ∀ b : ℝ, (∑ i, max (v i - b) 0) ≤ ∑ j, max (w j - b) 0) :
    topSum k v ≤ topSum k w := by
  by_cases hk0 : k = 0
  · subst k
    simp [topSum, firstIdx]
  obtain ⟨b, hb⟩ := exists_threshold_hinge_eq_topSum w (Nat.pos_of_ne_zero hk0) hkm
  exact (topSum_le_threshold_hinge v hkn b).trans
    ((add_le_add le_rfl (h b)).trans_eq hb)

/-- With ordered lengths, all hinge tests are equivalent to all available top sums. -/
theorem all_threshold_hinges_iff_topSums {n m : ℕ} (v : Fin n → ℝ) (w : Fin m → ℝ)
    (hnm : n ≤ m) :
    (∀ b : ℝ, (∑ i, max (v i - b) 0) ≤ ∑ j, max (w j - b) 0) ↔
      ∀ k : ℕ, k ≤ n → topSum k v ≤ topSum k w := by
  classical
  constructor
  · intro h k hk
    exact topSum_le_of_all_threshold_hinges v w hk (hk.trans hnm) h
  · intro h b
    let S := Finset.univ.filter (fun i => b < v i)
    have hSn : S.card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S)
    have hsum : (∑ i, max (v i - b) 0) = ∑ i ∈ S, (v i - b) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : b < v i
      · rw [if_pos hi, max_eq_left (sub_nonneg.mpr hi.le)]
      · rw [if_neg hi, max_eq_right (sub_nonpos.mpr (le_of_not_gt hi))]
    have hbound := (sum_le_topSum (v := v) (t := S) hSn rfl).trans
      ((h S.card hSn).trans (topSum_le_threshold_hinge w (hSn.trans hnm) b))
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith only [hbound]

/-- Product of the largest `k` positive depths, expressed through sorted logarithms. -/
def largestDepthProduct {n : ℕ} (k : ℕ) (v : Fin n → ℝ) : ℝ :=
  Real.exp (topSum k (fun i => Real.log (v i)))

theorem largestDepthProduct_eq_prod {n : ℕ} (k : ℕ) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) :
    largestDepthProduct k v =
      ∏ i ∈ firstIdx n k, v (descPerm (fun j => Real.log (v j)) i) := by
  rw [largestDepthProduct, topSum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  change Real.exp (Real.log (v (descPerm (fun j => Real.log (v j)) i))) = _
  exact Real.exp_log (hv _)

theorem largestDepthProduct_le_of_logarithmicThresholds {n m k : ℕ}
    (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ j, 0 < w j)
    (hkn : k ≤ n) (hkm : k ≤ m)
    (h : ∀ a : ℝ, 0 < a →
      (∑ i, logarithmicDepthThreshold a (v i)) ≤ ∑ j, logarithmicDepthThreshold a (w j)) :
    largestDepthProduct k v ≤ largestDepthProduct k w := by
  apply Real.exp_le_exp.mpr
  apply topSum_le_of_all_threshold_hinges _ _ hkn hkm
  intro b
  have hI {l : ℕ} (x : Fin l → ℝ) (hx : ∀ i, 0 < x i) :
      (∑ i, logarithmicDepthThreshold (Real.exp b) (x i)) = ∑ i, max (Real.log (x i) - b) 0 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [logarithmicDepthThreshold_eq_max_log_sub (Real.exp_pos b) (hx i), Real.log_exp]
  have hb := h (Real.exp b) (Real.exp_pos b)
  rwa [hI v hv, hI w hw] at hb

/-- Positive logarithmic threshold tests and largest-product comparisons are equivalent. -/
theorem logarithmicThresholds_iff_largestDepthProducts {n m : ℕ}
    (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ j, 0 < w j)
    (hnm : n ≤ m) :
    (∀ a : ℝ, 0 < a →
      (∑ i, logarithmicDepthThreshold a (v i)) ≤ ∑ j, logarithmicDepthThreshold a (w j)) ↔
      ∀ k : ℕ, k ≤ n → largestDepthProduct k v ≤ largestDepthProduct k w := by
  constructor
  · intro h k hk
    exact largestDepthProduct_le_of_logarithmicThresholds v w hv hw hk (hk.trans hnm) h
  · intro h a ha
    have htop : ∀ k : ℕ, k ≤ n →
        topSum k (fun i => Real.log (v i)) ≤ topSum k (fun j => Real.log (w j)) :=
      fun k hk => Real.exp_le_exp.mp (h k hk)
    have hhinge := (all_threshold_hinges_iff_topSums
      (fun i => Real.log (v i)) (fun j => Real.log (w j)) hnm).mpr htop (Real.log a)
    have heq {l : ℕ} (x : Fin l → ℝ) (hx : ∀ i, 0 < x i) :
        (∑ i, logarithmicDepthThreshold a (x i)) =
          ∑ i, max (Real.log (x i) - Real.log a) 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact logarithmicDepthThreshold_eq_max_log_sub ha (hx i)
    rwa [heq v hv, heq w hw]

/-- Squared heights of upper roots, with algebraic multiplicity. -/
def polynomialUpperSquaredDepths (p : ℝ[X]) :
    Fin (RiemannGaussian.realPolynomialUpperRootMultiset p).toList.length → ℝ :=
  fun i => ((RiemannGaussian.realPolynomialUpperRootMultiset p).toList.get i).im ^ 2

private theorem sum_list_get (L : List ℂ) (F : ℂ → ℝ) :
    (∑ i : Fin L.length, F (L.get i)) = (L.map F).sum := by
  rw [← Fin.sum_ofFn, List.ofFn_comp', List.ofFn_get]

theorem sum_polynomialUpperSquaredDepths (p : ℝ[X]) (F : ℝ → ℝ) :
    (∑ i, F (polynomialUpperSquaredDepths p i)) =
      ((RiemannGaussian.realPolynomialUpperRootMultiset p).map (fun z => F (z.im ^ 2))).sum := by
  unfold polynomialUpperSquaredDepths
  rw [sum_list_get _ (fun z => F (z.im ^ 2))]
  change (((↑(RiemannGaussian.realPolynomialUpperRootMultiset p).toList : Multiset ℂ).map
    (fun z => F (z.im ^ 2))).sum) = _
  rw [Multiset.coe_toList]

theorem polynomialUpperSquaredDepths_pos (p : ℝ[X])
    (i : Fin (RiemannGaussian.realPolynomialUpperRootMultiset p).toList.length) :
    0 < polynomialUpperSquaredDepths p i := by
  have hz : (RiemannGaussian.realPolynomialUpperRootMultiset p).toList.get i ∈
      RiemannGaussian.realPolynomialUpperRootMultiset p :=
    Multiset.mem_toList.mp (List.get_mem _ i)
  exact sq_pos_of_pos (RiemannGaussian.realPolynomialUpperRootMultiset_im_pos p _ hz)

theorem polynomial_upper_root_card_heat_le {p : ℝ[X]} (hp : p ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).toList.length ≤
      (RiemannGaussian.realPolynomialUpperRootMultiset p).toList.length := by
  have hcount (P : ℝ[X]) : nonrealRootCount P =
      2 * (RiemannGaussian.realPolynomialUpperRootMultiset P).card := by
    have h := RiemannGaussian.realPolynomial_realRoot_card_add_two_mul_upperRoot_card P
    rw [realPolynomialRealRootMultiset_eq_map_roots, Multiset.card_map] at h
    unfold nonrealRootCount
    omega
  have hzero : RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat 0 p) =
      RiemannGaussian.realPolynomialUpperRootMultiset p := by
    unfold RiemannGaussian.realPolynomialUpperRootMultiset
    rw [← heatFlow_ofReal, Complex.ofReal_zero, heatFlow_zero_time]
  have h := antitone_nonrealRootCount_polyHeat hp ht
  change nonrealRootCount (polyHeat t p) ≤ nonrealRootCount (polyHeat 0 p) at h
  rw [hcount, hcount, hzero] at h
  have hcard : (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).card ≤
      (RiemannGaussian.realPolynomialUpperRootMultiset p).card := by omega
  simpa only [Multiset.length_toList] using hcard

/-- Every product of the deepest surviving elapsed depths spends its initial budget. -/
theorem polynomial_largest_elapsed_depth_product_le_initial {p : ℝ[X]} (hp : p ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hk : k ≤ (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).toList.length) :
    largestDepthProduct k (fun i => polynomialUpperSquaredDepths (polyHeat t p) i + 2 * t) ≤
      largestDepthProduct k (polynomialUpperSquaredDepths p) := by
  apply largestDepthProduct_le_of_logarithmicThresholds _ _
    (fun i => add_pos_of_pos_of_nonneg (polynomialUpperSquaredDepths_pos _ i)
      (mul_nonneg zero_le_two ht)) (polynomialUpperSquaredDepths_pos p)
    hk (hk.trans (polynomial_upper_root_card_heat_le hp ht))
  intro a ha
  have hl := sum_polynomialUpperSquaredDepths (polyHeat t p)
    (fun u => logarithmicDepthThreshold a (u + 2 * t))
  have hr := sum_polynomialUpperSquaredDepths p (logarithmicDepthThreshold a)
  rw [hl, hr]
  exact polynomial_upper_logarithmicThreshold_le_initial hp ht ha

#print axioms topSum_le_of_all_threshold_hinges
#print axioms largestDepthProduct_eq_prod
#print axioms largestDepthProduct_le_of_logarithmicThresholds
#print axioms logarithmicThresholds_iff_largestDepthProducts
#print axioms polynomial_largest_elapsed_depth_product_le_initial

end
end GaloisForLFunctions.ArithmeticElectrostatics
