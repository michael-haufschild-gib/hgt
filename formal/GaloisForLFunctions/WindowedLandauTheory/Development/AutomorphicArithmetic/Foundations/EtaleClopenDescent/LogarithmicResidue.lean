import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCoefficientMap
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.MixedCechCupBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact

/-! Taking the logarithmic residue in the full left intersection
sends mixed boundaries to right Čech boundaries. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p : ℕ}

local notation "V₀" => ExteriorDifferentials k E p
local notation "W₀" => (F ⊗[k] ExteriorDifferentials k E p)
local notation "A₀" => (fun J : Finset (Fin (d + 1)) => regularExteriorLattice (rB k E x J) p)

/-- Apply the logarithmic residue to the left coefficient. -/
def logarithmicResidueTensor (ρ : F →ₗ[k] k) : W₀ →ₗ[k] V₀ :=
  TensorProduct.lift ((Algebra.lsmul k k V₀).toLinearMap.comp ρ)

omit [CharZero k] [Algebra F E] [IsScalarTower k F E] in
theorem logarithmicResidueTensor_tmul (ρ : F →ₗ[k] k) (a : F) (v : V₀) :
    logarithmicResidueTensor ρ (a ⊗ₜ[k] v) = ρ a • v := by
  rw [logarithmicResidueTensor, TensorProduct.lift.tmul]
  rfl

/-- A mixed boundary of logarithmic coefficients integrates to a right
boundary by the vanishing of the residue on proper left intersections. -/
theorem IsPd.logarithmicResidueTensor_mem_boundary (h : IsPd k x)
    (ρ : F →ₗ[k] k) (hρ : IsRes x ρ) {m : ℕ}
    {c : Finset (ChartPair d) → W₀}
    (hc : c ∈ (mixedCech (logarithmicChartSystem (E := E) h p).M).B ((d : ℤ) + m + 2)) :
    (fun J => logarithmicResidueTensor ρ (c (uni Finset.univ J))) ∈ (cech A₀).B (m : ℤ) := by
  let T := logarithmicChartSystem (E := E) h p
  let f : W₀ →ₗ[k] V₀ := logarithmicResidueTensor ρ
  obtain ⟨y, hy, rfl⟩ := hc
  let v (J : Finset (Fin (d + 1))) : V₀ := f (y (uni Finset.univ J))
  have hyM (I J : Finset (Fin (d + 1))) : y (uni I J) = 0 ∨
      I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card : ℕ) : ℤ) = (d : ℤ) + m + 2 - 1 ∧
        y (uni I J) ∈ T.M I J := by
    have he := acx_mem_terms_iff.mp hy (uni I J)
    rw [card_uni, lft_uni, rgt_uni] at he
    split_ifs at he with hIJ hN
    · exact Or.inr ⟨hN.1, hN.2, hIJ, he⟩
    · exact Or.inl ((Submodule.mem_bot k).mp he)
    · exact Or.inl ((Submodule.mem_bot k).mp he)
  have hreg (I J : Finset (Fin (d + 1))) : T.M I J ≤ (A₀ J).comap f := by
    refine Submodule.map₂_le.mpr fun a _ w hw => ?_
    change logarithmicResidueTensor ρ (a ⊗ₜ[k] w) ∈ A₀ J
    rw [logarithmicResidueTensor_tmul]
    exact (A₀ J).smul_mem _ hw
  have hkill {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) {i : Fin (d + 1)} (hi : i ∉ I) :
      T.M I J ≤ LinearMap.ker f := by
    obtain ⟨j, hj⟩ := hI
    refine Submodule.map₂_le.mpr fun a ha w _ => ?_
    change logarithmicResidueTensor ρ (a ⊗ₜ[k] w) = 0
    rw [logarithmicResidueTensor_tmul,
      residue_eq_zero_of_missing_chart h ρ hρ hi hj a ((h.mem_logCoefficientLattice_iff hj).mp ha),
      zero_smul]
  have hv : v ∈ (cech A₀).C ((m : ℤ) - 1) := by
    refine Submodule.mem_pi.mpr fun J _ => ?_
    rcases hyM Finset.univ J with hy₀ | ⟨_, hJn, hJc, hj⟩
    · change f (y (uni Finset.univ J)) ∈ _
      rw [hy₀, map_zero]
      exact zero_mem _
    · simp only [Finset.card_univ, Fintype.card_fin] at hJc
      change v J ∈ (if J.Nonempty ∧ (J.card : ℤ) = (m : ℤ) - 1 + 1 then A₀ J else ⊥)
      rw [if_pos ⟨hJn, by omega⟩]
      exact hreg _ _ hj
  refine ⟨(-1 : ℤ) ^ (d + 1) • v, zsmul_mem hv _, ?_⟩
  change deltaL k (Fin (d + 1)) V₀ ((-1 : ℤ) ^ (d + 1) • v) =
    (fun J => f (wd (1 : ChartPair d → Module.End k W₀) y (uni Finset.univ J)))
  rw [wd_one, map_zsmul]
  funext J
  rw [Pi.smul_apply, deltaL_uni, map_add, map_zsmul, Finset.card_univ, Fintype.card_fin]
  have hleft : f (deltaL k (Fin (d + 1)) W₀ (fun I => y (uni I J)) Finset.univ) = 0 := by
    rw [deltaL_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul]
    rcases hyM (Finset.univ.erase i) J with hzero | ⟨hn, _, _, hp⟩
    · rw [hzero, map_zero, smul_zero]
    · have hz : f (y (uni (Finset.univ.erase i) J)) = 0 :=
        hkill hn (Finset.notMem_erase i Finset.univ) hp
      rw [hz, smul_zero]
  rw [hleft, zero_add]
  let fC := mapCochain (ι := Fin (d + 1)) (M := W₀) (N := V₀) f
  let u (K : Finset (Fin (d + 1))) := y (uni Finset.univ K)
  change (-1 : ℤ) ^ (d + 1) • deltaL k (Fin (d + 1)) V₀
    (fC u) J = (-1 : ℤ) ^ (d + 1) • fC (deltaL k (Fin (d + 1)) W₀ u) J
  have hcomm : fC (deltaL k (Fin (d + 1)) W₀ u) =
      deltaL k (Fin (d + 1)) V₀ (fC u) := mapCochain_delta (M := W₀) (N := V₀) f u
  rw [hcomm]

end GlobalTheory.PD
