import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.DivisorInversionAtTheProductBoundary
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PeriodicQuotientCancellation

/-!
# Both endpoints of every quotient cell in the capped spline

With product q fixed, the last allowable horizon is the smaller of the
spline horizon and the predecessor of ceil(q/2)². The last quotient
cell is truncated at that horizon. Finite summation exchanges keep
this correction on every conductor, including terminal partial octaves.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Exclusive upper horizon after imposing both original cutoffs. -/
def lastProductHorizon (n q : ℕ) : ℕ :=
  min (splineHorizon n + 1) (unitProductHorizonEnd q)

private theorem in_product_horizon {k q : ℕ} (hk : q ≤ k) :
    productLower 1 k < q ↔ k < unitProductHorizonEnd q := by
  rw [productLower, Real.nat_floor_real_sqrt_eq_nat_sqrt, min_lt_iff,unitProductHorizonEnd,← Nat.sqrt_lt']
  omega

/-- Fixed-product horizon sum, valid even when either moving endpoint cuts
through the support of the spline. -/
theorem spline_sum_by_product (n U : ℕ) (a : ℕ → ℝ) :
    splineCountReading n (fun k => ∑ q ∈ Ioc (max (productLower 1 k) U) k,
      a q * centeredPrimeWeight 1 (k/q)) =
      ∑ q ∈ Ioc U (splineHorizon n), a q *
        ∑ k ∈ Ico q (lastProductHorizon n q),
          centeredPrimeWeight 1 (k/q) * (sampledSpline n k - sampledSpline n (k+1)) := by
  let L := splineHorizon n
  let z := fun k => sampledSpline n k - sampledSpline n (k+1)
  let f := fun q k => a q * centeredPrimeWeight 1 (k/q) * z k
  have hkset (k : ℕ) (hk : k ∈ Icc 1 L) :
      Ioc (max (productLower 1 k) U) k =
        (Ioc U L).filter (fun q => q ≤ k ∧ k < unitProductHorizonEnd q) := by
    ext q
    simp only [mem_Ioc, mem_filter, max_lt_iff]
    constructor
    · rintro ⟨⟨hp,hU⟩,hq⟩
      exact ⟨⟨hU, hq.trans (mem_Icc.mp hk).2⟩,hq,(in_product_horizon hq).mp hp⟩
    · rintro ⟨⟨hU,_⟩,hq,he⟩
      exact ⟨⟨(in_product_horizon hq).mpr he,hU⟩,hq⟩
  have hqset (q : ℕ) (hq : q ∈ Ioc U L) :
      (Icc 1 L).filter (fun k => q ≤ k ∧ k < unitProductHorizonEnd q) =
        Ico q (lastProductHorizon n q) := by
    ext k
    have := (mem_Ioc.mp hq).1
    simp only [mem_Icc,mem_filter,mem_Ico,lastProductHorizon,lt_min_iff]
    change (1 ≤ k ∧ k ≤ L) ∧ q ≤ k ∧ k < _ ↔ q ≤ k ∧ k < L+1 ∧ k < _
    omega
  unfold splineCountReading
  calc _ = ∑ k ∈ Icc 1 L, ∑ q ∈ Ioc U L,
            if q ≤ k ∧ k < unitProductHorizonEnd q then f q k else 0 := by
             refine sum_congr rfl fun k hk => ?_
             rw [sum_mul,hkset k hk,sum_filter]
         _ = _ := by
             rw [sum_comm]
             apply sum_congr rfl
             intro q hq
             rw [←sum_filter,hqset q hq,mul_sum]
             exact sum_congr rfl fun k _ => mul_assoc _ _ _

/-- The clipped last cell is included. Each summand uses its two actual
spline samples, even if the last upper endpoint is not a multiple of q. -/
theorem product_horizon_quotient_cells (n : ℕ) {q : ℕ} (hq : 0 < q) :
    (∑ k ∈ Ico q (lastProductHorizon n q),
        centeredPrimeWeight 1 (k/q) * (sampledSpline n k - sampledSpline n (k+1))) =
      ∑ j ∈ (Icc 1 (lastProductHorizon n q / q)).filter (fun j => j*q < lastProductHorizon n q),
        centeredPrimeWeight 1 j * (sampledSpline n (j*q) -
          sampledSpline n (min ((j+1)*q) (lastProductHorizon n q))) := by
  let d := lastProductHorizon n q
  let S := (Icc 1 (d/q)).filter (fun j => j*q < d)
  have maps : ∀ k ∈ Ico q d, k/q ∈ S := by
    intro k hk
    obtain ⟨hl,hu⟩ := mem_Ico.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(Nat.one_le_div_iff hq).mpr hl,Nat.div_le_div_right hu.le⟩,
      (Nat.div_mul_le_self k q).trans_lt hu⟩
  change (∑ k ∈ Ico q d, _) = ∑ j ∈ S, _
  rw [←sum_fiberwise_of_maps_to maps]
  apply sum_congr rfl
  intro j hj
  have hj0 := (mem_Icc.mp (mem_filter.mp hj).1).1
  have hjd := (mem_filter.mp hj).2
  have hlow : q ≤ j*q := Nat.le_mul_of_pos_left q hj0
  have hef : (Ico q d).filter (fun k => k/q=j) = Ico (j*q) (min ((j+1)*q) d) := by
    ext k
    simp only [mem_filter, mem_Ico, lt_min_iff]
    constructor
    · rintro ⟨⟨_,hd⟩,he⟩
      exact ⟨(Nat.le_div_iff_mul_le hq).mp he.ge,(Nat.div_lt_iff_lt_mul hq).mp (he ▸ Nat.lt_succ_self j),hd⟩
    · rintro ⟨hl,hu,hd⟩
      exact ⟨⟨hlow.trans hl,hd⟩,le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr hu))
        ((Nat.le_div_iff_mul_le hq).mpr hl)⟩
  rw [sum_congr rfl (fun k hk => by rw [(mem_filter.mp hk).2]), hef, ←mul_sum]
  have hab : j*q ≤ min ((j+1)*q) d := le_min (Nat.mul_le_mul_right q (Nat.le_succ j)) hjd.le
  have ht (a b : ℕ) (hab : a ≤ b) :
      (∑ k ∈ Ico a b, (sampledSpline n k - sampledSpline n (k+1))) =
        sampledSpline n a - sampledSpline n b := by
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih => rw [sum_Ico_succ_top hab,ih]; ring
  rw [ht _ _ hab]

/-- Complete product and quotient rearrangement of the actual sharp residual. -/
theorem capped_spline_quotient_cells (n b U : ℕ) :
    cappedUpperProductReading U b n =
      ∑ q ∈ Ioc U (splineHorizon n), (productInnerWeight q * (Real.log q - omittedProductLog b q)) *
        ∑ j ∈ (Icc 1 (lastProductHorizon n q / q)).filter (fun j => j*q < lastProductHorizon n q),
          centeredPrimeWeight 1 j * (sampledSpline n (j*q) -
            sampledSpline n (min ((j+1)*q) (lastProductHorizon n q))) := by
  rw [capped_spline_divisor_inversion, spline_sum_by_product]
  refine sum_congr rfl fun q hq => ?_
  rw [product_horizon_quotient_cells n ((Nat.zero_le U).trans_lt (mem_Ioc.mp hq).1)]

/-- When the two product endpoints lie away from the spline support, a shell
has the complete single-product mesh. The first omitted horizons have zero
first spline difference, and the far product endpoint is beyond the horizon. -/
theorem detached_signed_product_shell {n V W : ℕ} (hn : 0 < n) (hVW : V ≤ W)
    (hWL : W ≤ splineHorizon n) (hY : productLower 1 (splineHorizon n) ≤ V)
    (hbirth : (W:ℝ) + 1 < Real.exp (-8)*(n:ℝ)^2) (a : ℕ → ℝ) :
    splineCountReading n (fun k => ∑ q ∈ Ioc (max (productLower 1 k) V) k,
      a q*centeredPrimeWeight 1 (k/q)) -
    splineCountReading n (fun k => ∑ q ∈ Ioc (max (productLower 1 k) W) k,
      a q*centeredPrimeWeight 1 (k/q)) =
        ∑ q ∈ Ioc V W, a q*unitHorizonPair n q := by
  let L := splineHorizon n
  let z := fun k => sampledSpline n k - sampledSpline n (k+1)
  let F := fun q => a q * ∑ k ∈ Ico q (lastProductHorizon n q), centeredPrimeWeight 1 (k/q)*z k
  rw [spline_sum_by_product,spline_sum_by_product]
  change (∑ q ∈ Ioc V L, F q) - ∑ q ∈ Ioc W L, F q = _
  rw [←sum_Ioc_consecutive F hVW hWL,add_sub_cancel_right]
  apply sum_congr rfl
  intro q hq
  have hqW := (mem_Ioc.mp hq).2
  have hL := (in_product_horizon (hqW.trans hWL)).mp (hY.trans_lt (mem_Ioc.mp hq).1)
  have hend : lastProductHorizon n q = L+1 := min_eq_left (Nat.succ_le_of_lt hL)
  dsimp only [F]
  rw [hend,unitHorizonPair]
  congr 1
  rw [sum_congr rfl (fun k _ => mul_comm (centeredPrimeWeight 1 (k/q)) (z k))]
  apply sum_subset
  · intro k hk; exact mem_range.mpr (mem_Ico.mp hk).2
  · intro k hk hnot
    have hkq : k < q := lt_of_not_ge fun h => hnot (mem_Ico.mpr ⟨h,mem_range.mp hk⟩)
    have hkw : (k:ℝ) ≤ W := Nat.cast_le.mpr (hkq.le.trans hqW)
    have h1 : ((k+1:ℕ):ℝ) < Real.exp (-8)*(n:ℝ)^2 := by push_cast; linarith only [hkw,hbirth]
    rw [show z k = 0 by dsimp [z]; rw [sampledSpline_eq_zero_before hn (by linarith only [hkw,hbirth]),
      sampledSpline_eq_zero_before hn h1,sub_self],zero_mul]

#print axioms detached_signed_product_shell
#print axioms capped_spline_quotient_cells
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
