import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartMinors
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ScaledCechMinor
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartDifferential
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact

/-! Dividing each column by its left coordinate ratio turns the local
diagonal minor into an integral determinant after row normalization. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] {d : ℕ} (T : WeightedChartSystem k d S E)

/-- Product of the inverse left affine coordinate ratios. -/
def minorColumnScale (i : Fin (d + 1)) : Sˣ :=
  ∏ m, T.X i * (T.X m)⁻¹

private theorem normalized_minorRow (hT : T.Good) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    {K : Finset (Fin (d + 1))} (hKI : K ⊆ I) (L : Finset (DiagonalIndex d))
    {t : Fin (d + 1) ⊕ₗ DiagonalIndex d} (ht : t ∈ uni K L) (m : Fin (d + 1)) :
    ((Sum.elim (fun _ => 1) (fun _ => T.X i * T.Y j) (ofLex t) : Sˣ)⁻¹ : Sˣ) *
      (T.minorRows t m * ((T.X i * (T.X m)⁻¹ : Sˣ) : S)) ∈ T.R I J := by
  obtain ⟨t, rfl⟩ := toLex.surjective t
  rcases t with a | l
  · have ha : a ∈ K := by
      simpa [uni, Finset.mem_map, Finset.mem_disjSum] using ht
    change ((1 : Sˣ)⁻¹ : Sˣ) * ((Pi.single a 1 : Fin (d + 1) → S) m *
      ((T.X i * (T.X m)⁻¹ : Sˣ) : S)) ∈ T.R I J
    by_cases hm : m = a
    · subst m
      simp only [inv_one, Units.val_one, Pi.single_eq_same, one_mul]
      exact hT.memX I J ⟨j, hj⟩ a (hKI ha) i
    · simp only [Pi.single_eq_of_ne hm, zero_mul, mul_zero]
      exact zero_mem _
  · let U := T.X i * T.Y j
    have he (a : Fin (d + 1)) :
        ((U⁻¹ : Sˣ) : S) * (((T.X m : S) * (T.Y a : S)) *
          ((T.X i * (T.X m)⁻¹ : Sˣ) : S)) = ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      apply congrArg (fun u : Sˣ => (u : S))
      calc
        _ = ((T.X i)⁻¹ * T.X i) * (T.X m * (T.X m)⁻¹) * (T.Y a * (T.Y j)⁻¹) := by
          dsimp only [U]
          rw [mul_inv]
          ac_nf0
          rw [mul_left_comm ((T.Y j)⁻¹) ((T.X m)⁻¹)]
        _ = _ := by rw [inv_mul_cancel, mul_inv_cancel, one_mul, one_mul]
    have hy (a : Fin (d + 1)) : ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R I J :=
      hT.memY I J ⟨i, hi⟩ j hj a
    change ((U⁻¹ : Sˣ) : S) *
      (((if m = (ofLex l).1 then (T.X m : S) * (T.Y (ofLex l).2 : S) else 0) -
        (if m = (ofLex l).2 then (T.X m : S) * (T.Y (ofLex l).1 : S) else 0)) *
        ((T.X i * (T.X m)⁻¹ : Sˣ) : S)) ∈ T.R I J
    rw [sub_mul, mul_sub]
    apply sub_mem
    · split_ifs with hm
      · rw [he]; exact hy _
      · rw [zero_mul, mul_zero]; exact zero_mem _
    · split_ifs with hm
      · rw [he]; exact hy _
      · rw [zero_mul, mul_zero]; exact zero_mem _

/-- Acting by a diagonal minor after cancelling its left affine volume
factor gives a coefficient in the scaled column lattice. The coordinate
rows may come from any subset of the left intersection. -/
theorem act_orderedChartMinor_mem_scaled (hT : T.Good) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    {K : Finset (Fin (d + 1))} (hKI : K ⊆ I) (L : Finset (DiagonalIndex d))
    {v : E} (hv : v ∈ T.M I J) :
    T.act (orderedMinor T.minorRows (uni K L))
      (T.act (T.minorColumnScale i : S) v) ∈
      (T.M I J).map (T.act ((∏ l ∈ L, T.weightUnit (fun _ => (1, 1)) i j l : Sˣ) : S)) := by
  let u (t : Fin (d + 1) ⊕ₗ DiagonalIndex d) : Sˣ :=
    Sum.elim (fun _ => 1) (fun _ => T.X i * T.Y j) (ofLex t)
  let c (m : Fin (d + 1)) : S := ((T.X i * (T.X m)⁻¹ : Sˣ) : S)
  have h := act_orderedMinor_mem_scaled (T.R I J) (T.M I J) T.act
    (hT.stab I J ⟨i, hi⟩ ⟨j, hj⟩) (fun t m => T.minorRows t m * c m)
    u (uni K L) (fun _ ht m => T.normalized_minorRow hT hi hj hKI L ht m) hv
  have hu : (∏ t ∈ uni K L, u t) = ∏ l ∈ L, T.weightUnit (fun _ => (1, 1)) i j l := by
    rw [uni, Finset.prod_map, Finset.prod_disjSum]
    simp only [u, Equiv.coe_toEmbedding, ofLex_toLex, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, one_mul,
      weightUnit, pow_one]
  rw [orderedMinor_mul_columns, hu] at h
  have hc : (∏ m, c m) = (T.minorColumnScale i : S) := (Units.coe_prod _ _).symm
  rw [hc, map_mul, Module.End.mul_apply] at h
  exact h

/-- The column obtained from one coordinate row and the homogeneous
equations, with its left affine volume removed. -/
def chartMinorColumn (i : Fin (d + 1)) (v : E) (L : Finset (DiagonalIndex d)) : E :=
  T.act (orderedMinor T.minorRows (uni {i} L)) (T.act (T.minorColumnScale i : S) v)

/-- The determinant identity gives a closed regular column of degree
equal to the relative dimension. -/
theorem chartMinorColumn_mem_cycles (hT : T.Good) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) {v : E} (hv : v ∈ T.M I J) :
    T.chartMinorColumn i v ∈
      (T.columnComplex (fun _ => (1, 1)) T.homogeneousMinor I J).Z (d : ℤ) := by
  refine ⟨?_, ?_⟩
  · rw [T.columnComplex_eq hT (fun _ => (1, 1)) T.homogeneousMinor hi hj]
    refine acx_mem_terms_iff.mpr fun L => ?_
    by_cases hL : (L.card : ℤ) = d
    · rw [if_pos hL]
      exact T.act_orderedChartMinor_mem_scaled hT hi hj (Finset.singleton_subset_iff.mpr hi) L hv
    · rw [if_neg hL, Submodule.mem_bot, chartMinorColumn]
      have hcard : (uni ({i} : Finset (Fin (d + 1))) L).card ≠ d + 1 := by
        rw [card_uni, Finset.card_singleton]
        omega
      rw [orderedMinor, dif_neg hcard, map_zero, LinearMap.zero_apply]
  · change wd (fun l => T.act (T.homogeneousMinor l)) (T.chartMinorColumn i v) = 0
    funext L
    let seed := T.act (T.minorColumnScale i : S) v
    have he := congrFun (T.wd_orderedChartMinor_eq_zero seed) (uni {i} L)
    rw [wd_uni, wd_apply, Finset.sum_singleton, Finset.erase_singleton, orderedMinor_left] at he
    simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add, Finset.card_singleton, pow_one,
      neg_one_zsmul, Pi.zero_apply, neg_eq_zero] at he
    exact he

end GlobalTheory.WH.WeightedChartSystem
