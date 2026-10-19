import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgePhaseFibre

/-! Complete low-degree observations and an actual order-two obstruction. -/

noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BezoutValuationIncidence
open AffineSieve
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Complete translated arrays through a specified degree, including degree zero. -/
def MomentsThrough (N m : ℕ) (c e : ℕ → ℝ) : Prop :=
  ∀ r ≤ m, ∀ h : Fin r → ℕ, translatedMoment N c h = translatedMoment N e h

theorem momentsThrough_mono {N m l : ℕ} {c e : ℕ → ℝ}
    (h : MomentsThrough N m c e) (hl : l ≤ m) : MomentsThrough N l c e :=
  fun r hr => h r (hr.trans hl)

/-- The canonical order-two Ramanujan atom exists even at the smallest cutoff two. -/
def orderTwoWeight (N : ℕ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (fun q => if q=2 then 1 else 0) N

theorem coordinate_orderTwoWeight (N : ℕ) (hN : 2 ≤ N) (q : ℕ) :
    selbergMultiplesCoord N (orderTwoWeight N) q = if q=2 then 1 else 0 := by
  rw [orderTwoWeight,selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q=2
  · subst q
    simp [Finset.mem_Icc,hN]
  · simp [hq]

namespace ArithmeticEdges.Blocks
variable {V : Type*} [Fintype V] (D : Blocks V)

theorem quadratic_partner_realization (n : ℕ) (a e : ℕ → ℝ)
    (h : ∀ v : Fin 2 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) v =
      translatedMoment (D.cutoff n) e v) :
    ∃ b : ℕ → ℝ, ∀ k, sieveSeq (D.cutoff n) e k =
      sieveSeq (D.cutoff n) (D.weights n b) k := by
  have hs := (quadratic_moments_iff_coordinate_squares (D.cutoff n) (D.weights n a) e).mp h
  have he : D.EdgeSupported (D.cutoff n) e := by
    intro q hq
    have hh := hs q
    rw [D.coordinate_weights,D.profile_zero a q hq] at hh
    nlinarith only [hh]
  exact ⟨selbergMultiplesCoord (D.cutoff n) e,D.signal_realization n e he⟩

/-- On arithmetic edge support, quadratic translated arrays and all affine data are equivalent. -/
theorem affine_iff_quadratic (n : ℕ) (a e : ℕ → ℝ) :
    (∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t = affineMoment (D.cutoff n) e s t) ↔
      (∀ v : Fin 2 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) v =
        translatedMoment (D.cutoff n) e v) := by
  constructor
  · intro h
    obtain ⟨b,hb⟩ := D.affine_partner_realization n a e h
    have hab (s t : ℕ) : affineMoment (D.cutoff n) (D.weights n a) s t =
        affineMoment (D.cutoff n) (D.weights n b) s t := by
      simpa only [affineMoment,hb] using h s t
    have hs := (D.affine_weights_iff_squares n a b).mp hab
    intro v
    have hv := quadratic_moments_of_coordinate_squares (D.cutoff n) (D.weights n a)
      (D.weights n b) (D.coordinate_squares n a b hs) v
    simpa only [translatedMoment,hb] using hv
  · intro h
    obtain ⟨b,hb⟩ := D.quadratic_partner_realization n a e h
    have hq (v : Fin 2 → ℕ) : translatedMoment (D.cutoff n) (D.weights n a) v =
        translatedMoment (D.cutoff n) (D.weights n b) v := by
      simpa only [translatedMoment,hb] using h v
    have hs := (quadratic_moments_iff_coordinate_squares (D.cutoff n)
      (D.weights n a) (D.weights n b)).mp hq
    have hab := (D.affine_weights_iff_squares n a b).mpr (fun u v huv => by
      simpa only [D.coordinate_weights,D.profile_order a huv,D.profile_order b huv]
        using hs (D.order u v))
    intro s t
    simpa only [affineMoment,hb] using hab s t

theorem through_three_of_profile_squares (n : ℕ) (a b : ℕ → ℝ)
    (hs : ∀ q, (D.profile a q)^2 = (D.profile b q)^2) :
    MomentsThrough (D.cutoff n) 3 (D.weights n a) (D.weights n b) := by
  intro m hm h
  interval_cases m
  · simp [translatedMoment]
  · rw [D.odd_moment_zero n a 0 h,D.odd_moment_zero n b 0 h]
  · apply quadratic_moments_of_coordinate_squares
    intro q
    simpa only [D.coordinate_weights] using hs q
  · rw [D.odd_moment_zero n a 1 h,D.odd_moment_zero n b 1 h]

/-- Fourth arrays already determine every translated degree through five, for arbitrary competitors. -/
theorem through_five_of_fourth (n : ℕ) (a e : ℕ → ℝ)
    (h4 : ∀ v : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) v =
      translatedMoment (D.cutoff n) e v) :
    MomentsThrough (D.cutoff n) 5 (D.weights n a) e := by
  have he := ((D.fourth_weights_iff n a e).mp h4).1
  let b := selbergMultiplesCoord (D.cutoff n) e
  have hb (k : ℕ) : sieveSeq (D.cutoff n) e k =
      sieveSeq (D.cutoff n) (D.weights n b) k := D.signal_realization n e he k
  intro m hm h
  interval_cases m
  · simp [translatedMoment]
  · have hh := (D.odd_moment_zero n a 0 h).trans (D.odd_moment_zero n b 0 h).symm
    simpa only [translatedMoment,hb] using hh
  · exact quadratic_moments_of_coordinate_squares _ _ _
      (coordinate_squares_of_fourth_moments _ _ _ h4) h
  · have hh := (D.odd_moment_zero n a 1 h).trans (D.odd_moment_zero n b 1 h).symm
    simpa only [translatedMoment,hb] using hh
  · exact h4 h
  · have hh := (D.odd_moment_zero n a 2 h).trans (D.odd_moment_zero n b 2 h).symm
    simpa only [translatedMoment,hb] using hh

theorem affine_of_fourth (n : ℕ) (a e : ℕ → ℝ)
    (h4 : ∀ v : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) v =
      translatedMoment (D.cutoff n) e v) :
    ∀ s t, affineMoment (D.cutoff n) (D.weights n a) s t = affineMoment (D.cutoff n) e s t :=
  (D.affine_iff_quadratic n a e).mpr ((D.through_five_of_fourth n a e h4) 2 (by decide))

theorem profile_one_zero (a : ℕ → ℝ) : D.profile a 1 = 0 := by
  apply D.profile_zero
  rintro ⟨u,v,_,h⟩
  have hh := D.two_dvd_order u v
  rw [← h] at hh
  norm_num at hh

theorem profile_two_zero (a : ℕ → ℝ) : D.profile a 2 = 0 := by
  apply D.profile_zero
  rintro ⟨u,v,_,h⟩
  have hu := D.gt_one u
  have hv := D.gt_one v
  have hm : 4 ≤ D.value u*D.value v :=
    Nat.mul_le_mul (by omega : 2 ≤ D.value u) (by omega : 2 ≤ D.value v)
  unfold order at h
  nlinarith only [h,hm]

/-- A fixed order-two atom preserves all data through one, including at empty edge support. -/
theorem orderTwo_through_one (n : ℕ) (a : ℕ → ℝ) :
    MomentsThrough (D.cutoff n) 1 (D.weights n a) (orderTwoWeight (D.cutoff n)) := by
  intro m hm h
  interval_cases m
  · simp [translatedMoment]
  · apply translatedMoment_eq_of_resonant_products
    intro r hr
    have hz : r 0=0 := by simpa only [Fin.sum_univ_one] using hr
    simp only [Fin.prod_univ_one,hz,addOrderOf_zero,D.coordinate_weights,
      coordinate_orderTwoWeight _ (D.cutoff_two_le n)]
    norm_num [D.profile_one_zero]

theorem orderTwo_not_translate (n : ℕ) (a : ℕ → ℝ) :
    ¬ ∃ t, ∀ k, sieveSeq (D.cutoff n) (orderTwoWeight (D.cutoff n)) k =
      sieveSeq (D.cutoff n) (D.weights n a) (k+t) := by
  rintro ⟨t,ht⟩
  have h2 (h : Fin 2 → ℕ) :=
    (translatedMoment_of_signal_translate (D.cutoff n) (D.weights n a)
      (orderTwoWeight (D.cutoff n)) t ht h).symm
  have hs := (quadratic_moments_iff_coordinate_squares (D.cutoff n)
    (D.weights n a) (orderTwoWeight (D.cutoff n))).mp h2 2
  rw [D.coordinate_weights,D.profile_two_zero,coordinate_orderTwoWeight _ (D.cutoff_two_le n)] at hs
  norm_num at hs

end ArithmeticEdges.Blocks
end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
