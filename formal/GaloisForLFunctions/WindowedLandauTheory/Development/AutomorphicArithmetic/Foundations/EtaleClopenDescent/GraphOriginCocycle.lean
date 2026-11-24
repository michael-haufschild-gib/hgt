import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphDiagonalWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LeftOriginWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LeftOriginMinors
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginVolumeCochain
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DeterminantJoinedCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartProjection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SingletonChartColumns

/-! The left origin determinant cocycle lifts the logarithmic origin
cochain to the weighted chart complex of a correspondence. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem

namespace GlobalTheory.WH

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k E L] [IsScalarTower k F L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F}

private theorem chartIndex_eq_zero {I : Finset (Fin (d + 1))} (h : 0 ∈ I) :
    chartIndex I = 0 := by
  rw [chartIndex, dif_pos ⟨0, h⟩]
  exact le_antisymm (Finset.min'_le _ _ h) (Fin.zero_le _)

/-- The weighted origin cocycle has the edge of the origin form as
its weight-free part and the affine volume in its origin column. -/
theorem exists_graphOriginCocycle
    (h : IsPd k x) (j₂ : E →ₐ[k] L) {q p : ℕ} (hqp : q + p = d)
    (a : rB k L x {0}) :
    let T := graphChartSystem h j₂ q p
    ∃ c ∈ (T.complex (fun _ => (1, 0)) T.leftOriginWeights).Z ((d : ℤ) + 2),
      chartPart c = edge1 (originVolumeCochain a) ∧
      ∀ j : Fin (d + 1),
        (T.scaleColumn (fun _ => (1, 0)) 0 j).symm (fun K => c (uni (uni {0} {j}) K)) Finset.univ =
          (-1 : k) ^ d • ((a : L) • originAffineVolume k L x) := by
  let T := graphChartSystem h j₂ q p
  let X (i : Fin (d + 1)) := algebraMap F L (x i)
  let t (i : Fin (d + 1)) := algebraMap F L (x i / x 0)
  let ρ := leftOriginRows X
  let v := (a : L) • vol0 k L x
  let b (J : Finset (Fin (d + 1))) := if J.card = 1 then v else 0
  let c := T.joinOrderedMinors ρ 1 b
  have hb : deltaL k (Fin (d + 1)) (DR k L) b = 0 := by
    let a₀ : Finset (Fin (d + 1)) → DR k L := Pi.single ∅ v
    have hd : b = deltaL k (Fin (d + 1)) (DR k L) a₀ := by
      funext J
      by_cases hJ : J.card = 1
      · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
        simp [b, a₀, deltaL_apply, Finset.filter_singleton, GlobalTheory.cubeSign,
          GaloisForLFunctions.HTGeometry.BorelWeil.cechSign,
          GaloisForLFunctions.HTGeometry.BorelWeil.belowCard]
      · rw [show b J = 0 from if_neg hJ, deltaL_apply]
        symm
        refine Finset.sum_eq_zero fun j hj => ?_
        have hne : J.erase j ≠ ∅ := by
          intro he
          have hc := Finset.card_erase_add_one hj
          rw [he, Finset.card_empty, zero_add] at hc
          exact hJ hc.symm
        simp only [a₀, Pi.single_eq_of_ne hne, smul_zero]
    rw [hd]
    simpa only [wd_one] using
      wd_wd (1 : Fin (d + 1) → Module.End k (DR k L)) (fun _ _ => Commute.one_left _) a₀
  have hb₀ (J : Finset (Fin (d + 1))) (hJ : J.card ≠ 1) : b J = 0 := if_neg hJ
  have hX (i : Fin (d + 1)) : (T.X i : L) = X i :=
    graphChartSystem_X h j₂ q p i
  have hw : wd (T.weights T.leftOriginWeights) c = 0 := by
    apply T.wd_joinOrderedMinors_eq_zero ρ T.leftOriginWeights _ 1 b hb hb₀
    intro m
    have he : (fun l : Fin (d + 1) ⊕ₗ Fin d =>
        Sum.elim (fun _ => 1) T.leftOriginWeights (ofLex l)) = leftOriginRowFactor X := by
      funext l
      rcases hl : ofLex l with i | i
      · simp only [leftOriginRowFactor, hl, Sum.elim_inl]
      · simp only [leftOriginRowFactor, leftOriginWeights, hl, Sum.elim_inr, hX]
    have hweight : (fun l : Fin (d + 1) ⊕ₗ Fin d =>
        T.act (Sum.elim (fun _ => 1) T.leftOriginWeights (ofLex l))) =
        fun l => T.act (leftOriginRowFactor X l) :=
      congrArg (fun w : Fin (d + 1) ⊕ₗ Fin d → L => fun l => T.act (w l)) he
    rw [hweight]
    exact wd_leftOriginMinors_eq_zero T.act X m
  have hprod (S : Finset (Fin (d + 1))) :
      (∏ i ∈ S, X i) = X 0 ^ S.card * ∏ i ∈ S, t i := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    change algebraMap F L (x i) = algebraMap F L (x 0) * algebraMap F L (x i / x 0)
    rw [← map_mul, mul_comm (x 0), div_mul_cancel₀ _ (h.ne 0)]
  refine ⟨c, ⟨?_, hw⟩, ?_, ?_⟩
  · refine acx_mem_terms_iff.mpr fun s => ?_
    obtain ⟨B, K, rfl⟩ : ∃ B K, s = uni B K := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
    rw [show c = T.joinOrderedMinors ρ 1 b from rfl, T.joinOrderedMinors_apply]
    by_cases hJ : J.card = 1
    · by_cases hθ : orderedMinor ρ (uni I K) = 0
      · rw [hθ, map_zero, LinearMap.zero_apply, smul_zero]
        exact zero_mem _
      · obtain ⟨hI, hf⟩ := leftOriginMinor_support X I K hθ
        have hc : I.card + K.card = d + 1 := by
          by_contra hn
          exact hθ (by simp only [orderedMinor, card_uni, dif_neg hn])
        have hgrade : ((uni (uni I J) K).card : ℤ) = (d : ℤ) + 2 := by
          rw [card_uni, card_uni]
          omega
        have hnec : I.Nonempty ∧ J.Nonempty := ⟨⟨0, hI⟩, Finset.card_pos.mp (by omega)⟩
        rw [if_pos hgrade, lft_uni, rgt_uni, mixedCoefficients, lft_uni, rgt_uni, if_pos hnec]
        let s₀ : k := orderedMinor (fun l i => if leftOriginRowIndex l = i then 1 else 0) (uni I K)
        have hθ' : orderedMinor ρ (uni I K) =
            X 0 ^ K.card * ((algebraMap k L s₀) * ∏ i ∈ Iᶜ, t i) := by
          have hprod' : (∏ i ∈ K, X i.succ) = ∏ m ∈ Iᶜ, X m := by
            rw [← hf, Finset.prod_map]
            rfl
          have hcard : Iᶜ.card = K.card := by rw [← hf, Finset.card_map]
          rw [orderedMinor_leftOriginRows_factor (k := k) X, hprod', hprod, hcard]
          ac_rfl
        let B := RY x j₂ I J
        have hreg : (∏ i ∈ Iᶜ, t i) • v ∈ omB k L B d :=
          omB_mono (le_sup_left : rB k L x I ≤ B) d (omittedCoordinates_smul_originVolume_mem h hI a)
        let u := (-1 : ℤ) ^ (1 * K.card) • (s₀ • ((∏ i ∈ Iᶜ, t i) • v))
        have hu : u ∈ T.M I J := by
          change u ∈ omB k L B (q + p)
          have hu' : u ∈ omB k L B d := zsmul_mem (Submodule.smul_mem _ s₀ hreg) _
          exact (congrArg (fun r => u ∈ omB k L B r) hqp.symm).mp hu'
        refine ⟨u, hu, ?_⟩
        have hU : ((∏ l ∈ K, T.weightUnit (fun _ => (1, 0)) (chartIndex I) (chartIndex J) l : Lˣ) : L) =
            X 0 ^ K.card := by
          simp only [weightUnit, pow_one, pow_zero, mul_one, chartIndex_eq_zero hI,
            Finset.prod_const, Units.val_pow_eq_pow_val, hX]
        rw [hU, hθ', show b J = v from if_pos hJ]
        change X 0 ^ K.card • u = (-1 : ℤ) ^ (1 * K.card) •
          ((X 0 ^ K.card * (algebraMap k L s₀ * ∏ i ∈ Iᶜ, t i)) • v)
        rw [show u = _ from rfl, smul_comm (X 0 ^ K.card) ((-1 : ℤ) ^ (1 * K.card))]
        congr 1
        rw [← IsScalarTower.algebraMap_smul L s₀ ((∏ i ∈ Iᶜ, t i) • v),
          smul_smul, smul_smul, mul_assoc]
    · rw [hb₀ J hJ, map_zero, smul_zero]
      exact zero_mem _
  · funext s
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [chartPart, show c = T.joinOrderedMinors ρ 1 b from rfl, T.joinOrderedMinors_apply]
    simp only [edge1, lft_uni, rgt_uni, Finset.card_empty, mul_zero, pow_zero, one_smul]
    by_cases hJ : J.card = 1
    · rw [show b J = v from if_pos hJ, if_pos hJ]
      by_cases hI : I = Finset.univ
      · subst I
        dsimp only [ρ]
        rw [leftOriginMinor_chartOnly, map_one, Module.End.one_apply, originVolumeCochain, if_pos rfl]
      · have hc : I.card ≠ d + 1 := fun he =>
          hI (Finset.eq_univ_of_card I (by simpa only [Fintype.card_fin] using he))
        dsimp only [ρ]
        rw [orderedMinor, dif_neg (by simpa only [card_uni, Finset.card_empty, add_zero] using hc),
          map_zero, LinearMap.zero_apply, originVolumeCochain, if_neg hI]
    · rw [hb₀ J hJ, if_neg hJ, map_zero]
  · intro j
    have hprod' : (∏ i : Fin d, X i.succ) = X 0 ^ d * ∏ i : Fin d, t i.succ := by
      let e : Fin d ↪ Fin (d + 1) := ⟨Fin.succ, Fin.succ_injective d⟩
      have he (i : Fin d) : e i = i.succ := rfl
      simpa only [Finset.prod_map, Finset.card_map, Finset.card_univ, Fintype.card_fin, he] using
        hprod (Finset.univ.map e)
    have hvalue : c (uni (uni {0} {j}) Finset.univ) =
        (-1 : ℤ) ^ d • (X 0 ^ d • ((a : L) • originAffineVolume k L x)) := by
      rw [show c = T.joinOrderedMinors ρ 1 b from rfl, T.joinOrderedMinors_apply]
      dsimp only [ρ]
      rw [leftOriginMinor_originOnly, show b {j} = v from if_pos (Finset.card_singleton j),
        Finset.card_univ, Fintype.card_fin, one_mul, hprod', originAffineVolume_eq_smul h]
      change (-1 : ℤ) ^ d • ((X 0 ^ d * (∏ i : Fin d, t i.succ)) • ((a : L) • vol0 k L x)) = _
      rw [mul_smul, smul_comm (∏ i : Fin d, t i.succ) (a : L)]
    let u := T.normalizationProduct (fun _ : Fin d => (1, 0)) 0 j Finset.univ
    have hu : (u : L) = X 0 ^ d := by
      simp only [u, normalizationProduct, weightUnit, pow_one, pow_zero, mul_one, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val, hX]
    change (((u⁻¹ : Lˣ) : L)) • c (uni (uni {0} {j}) Finset.univ) = _
    have hX₀ : X 0 ≠ 0 := (map_ne_zero _).mpr (h.ne 0)
    rw [Units.val_inv_eq_inv_val, hu, hvalue, smul_comm ((X 0 ^ d)⁻¹) ((-1 : ℤ) ^ d),
      smul_smul, inv_mul_cancel₀ (pow_ne_zero d hX₀), one_smul, ← Int.cast_smul_eq_zsmul k,
      Int.cast_pow, Int.cast_neg, Int.cast_one]

end GlobalTheory.WH
