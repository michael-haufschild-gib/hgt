import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicColumnLift
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DeterminantJoinedCech

/-! The determinant cocycle joined to a regular right Čech cocycle
lifts that cocycle through the logarithmic tensor coefficients. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)
local notation "V₀" => ExteriorDifferentials k E p
local notation "W₀" => (F ⊗[k] ExteriorDifferentials k E p)
local notation "A₀" => (fun J : Finset (Fin (d + 1)) => regularExteriorLattice (rB k E x J) p)

/-- The logarithmic lift has the prescribed Čech projection and the
expected determinant collapse in the highest Koszul degree. -/
theorem IsPd.exists_logarithmicTheta (h : IsPd k x) (m : ℕ)
    {β : Finset (Fin (d + 1)) → V₀} (hβ : β ∈ (cech A₀).Z (m : ℤ)) :
    let T := logarithmicChartSystem (E := E) h p
    ∃ c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + m + 2),
      Lev rightIndices (· ≤ (d : ℤ)) c ∧
      (∀ (I J : Finset (Fin (d + 1))) (L : Finset (DiagonalIndex d)), L.card = d →
        collapseLogarithmicTensor (k := k) (F := F) p (c (uni (uni I J) L)) =
          (-1 : ℤ) ^ ((m + 1) * d) •
            (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) •
              (if I.card = 1 then β J else 0))) ∧
      ∀ J, c (uni (uni Finset.univ J) ∅) = (1 : F) ⊗ₜ[k] β J := by
  let T := logarithmicChartSystem (E := E) h p
  let n : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  let r := m + 1
  let f : V₀ →ₗ[k] W₀ := TensorProduct.mk k F V₀ 1
  let fC := mapCochain (ι := Fin (d + 1)) (M := V₀) (N := W₀) f
  let b := fC β
  let c := T.minorJoin r b
  have hβC (J : Finset (Fin (d + 1))) :
      β J ∈ (if J.Nonempty ∧ J.card = r then A₀ J else ⊥ : Submodule k V₀) := by
    have he : ((J.card : ℤ) = (m : ℤ) + 1) ↔ J.card = r := by
      dsimp only [r]
      omega
    simpa only [he] using Submodule.mem_pi.mp hβ.1 J (Set.mem_univ J)
  have hβ₀ (J : Finset (Fin (d + 1))) (hJ : ¬ (J.Nonempty ∧ J.card = r)) : β J = 0 :=
    (Submodule.mem_bot k).mp (by simpa only [if_neg hJ] using hβC J)
  have hb₀ (J : Finset (Fin (d + 1))) (hJ : J.card ≠ r) : b J = 0 := by
    change f (β J) = 0
    rw [hβ₀ J (fun hJ' => hJ hJ'.2), map_zero]
  have hb : deltaL k (Fin (d + 1)) W₀ b = 0 := by
    have hmap : fC (deltaL k (Fin (d + 1)) V₀ β) = deltaL k (Fin (d + 1)) W₀ b :=
      mapCochain_delta (M := V₀) (N := W₀) f β
    rw [← hmap, show deltaL k (Fin (d + 1)) V₀ β = 0 from hβ.2, map_zero]
  have hzero (I J : Finset (Fin (d + 1))) (L : Finset (DiagonalIndex d))
      (h0 : I = ∅ ∨ ¬ (J.Nonempty ∧ J.card = r) ∨ I.card + L.card ≠ d + 1) :
      c (uni (uni I J) L) = 0 := by
    rw [show c = T.minorJoin r b from rfl, T.minorJoin_apply]
    rcases h0 with rfl | hJ | hIL
    · rw [T.orderedMinor_left, map_zero, LinearMap.zero_apply, smul_zero]
    · rw [show b J = 0 by change f (β J) = 0; rw [hβ₀ J hJ, map_zero], map_zero, smul_zero]
    · rw [orderedMinor, dif_neg (by rw [card_uni]; exact hIL), map_zero, LinearMap.zero_apply, smul_zero]
  refine ⟨c, ⟨?_, T.wd_minorJoin_eq_zero r b hb hb₀⟩, ?_, ?_, ?_⟩
  · refine acx_mem_terms_iff.mpr fun s => ?_
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
    by_cases hI : I.Nonempty
    · by_cases hJ : J.Nonempty ∧ J.card = r
      · by_cases hIL : I.card + L.card = d + 1
        · have hdeg : ((uni (uni I J) L).card : ℤ) = (d : ℤ) + m + 2 := by
            rw [card_uni, card_uni]
            dsimp only [r] at hJ
            omega
          rw [if_pos hdeg]
          change c (uni (uni I J) L) ∈ T.mixedCoefficients n (rgt (uni (uni I J) L))
            (lft (uni (uni I J) L))
          rw [lft_uni, rgt_uni, mixedCoefficients, lft_uni, rgt_uni, if_pos ⟨hI, hJ.1⟩]
          let i := chartIndex I
          let j := chartIndex J
          let a : F := ∏ l, x l / x i
          have hvol : logCoefficientScale x i * a = 1 := by
            change (∏ l, x i / x l) * (∏ l, x l / x i) = 1
            rw [← Finset.prod_mul_distrib]
            exact Finset.prod_eq_one fun l _ => by rw [div_mul_div_cancel₀ (h.ne l), div_self (h.ne i)]
          have ha : a ∈ logCoefficientLattice k x I := by
            apply (h.mem_logCoefficientLattice_iff (chartIndex_mem hI)).mpr
            rw [hvol]
            exact one_mem _
          have hseed : a ⊗ₜ[k] β J ∈ T.M I J :=
            Submodule.apply_mem_map₂ _ ha (by simpa only [if_pos hJ] using hβC J)
          have hs : T.act (T.minorColumnScale i : F ⊗[k] F) (a ⊗ₜ[k] β J) = b J := by
            change tensorScalarAction (T.minorColumnScale i : F ⊗[k] F) (a ⊗ₜ[k] β J) =
              (1 : F) ⊗ₜ[k] β J
            have ht : (T.minorColumnScale i : F ⊗[k] F) = logCoefficientScale x i ⊗ₜ[k] (1 : F) :=
              chartVolume_inv_tensor (E := E) (p := p) (q := p) h i
            rw [ht, tensorScalarAction_tmul, smul_eq_mul, hvol, one_smul]
          rw [show c = T.minorJoin r b from rfl, T.minorJoin_apply, ← hs]
          exact zsmul_mem (T.act_orderedChartMinor_mem_scaled
            (logarithmicChartSystem_good (E := E) h p) (chartIndex_mem hI) (chartIndex_mem hJ.1)
            Finset.Subset.rfl L hseed) _
        · rw [hzero I J L (Or.inr (Or.inr hIL))]
          exact zero_mem _
      · rw [hzero I J L (Or.inr (Or.inl hJ))]
        exact zero_mem _
    · rw [hzero I J L (Or.inl (Finset.not_nonempty_iff_eq_empty.mp hI))]
      exact zero_mem _
  · intro s hs
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    obtain ⟨I, J, rfl⟩ : ∃ I J, B = uni I J := ⟨lft B, rgt B, (uni_lft_rgt B).symm⟩
    have hcard : (((uni (uni I J) L ∩ rightIndices).card : ℕ) : ℤ) = L.card :=
      congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices (uni I J) L)
    have hlt : (d : ℤ) < (L.card : ℤ) := lt_of_not_ge (fun ht => hs (hcard.symm ▸ ht))
    apply hzero
    by_cases hI : I = ∅
    · exact Or.inl hI
    · have hpos : 0 < I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
      exact Or.inr (Or.inr (by omega))
  · intro I J L hL
    by_cases hI : I.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
      rw [show c = T.minorJoin r b from rfl, T.minorJoin_apply, hL,
        if_pos (Finset.card_singleton i), map_zsmul]
      change (-1 : ℤ) ^ (r * d) • tensorContraction (LinearMap.id : F →ₗ[F] F)
        (tensorScalarAction (orderedMinor T.minorRows (uni {i} L)) ((1 : F) ⊗ₜ[k] β J)) = _
      rw [tensorContraction_action, tensorContraction_tmul, LinearMap.id_apply, one_smul,
        T.map_orderedMinor_singleton_eq π (diagonalMinor_specializes (E := E) (p := p) (q := p) h) L i 0]
    · rw [hzero I J L (Or.inr (Or.inr (by omega))), map_zero, if_neg hI, smul_zero, smul_zero]
  · intro J
    rw [show c = T.minorJoin r b from rfl, T.minorJoin_apply, Finset.card_empty, Nat.mul_zero,
      pow_zero, one_smul, T.orderedMinor_univ, map_one, Module.End.one_apply]
    rfl

end GlobalTheory.PD
