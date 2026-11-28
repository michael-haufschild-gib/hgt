import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.CircuitDates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenChain

/-! # Affine evolution of a growing spectral edge on one frozen chain -/

open Filter Matrix Set Finset MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private abbrev Idx (n : ℕ) := Fin (n+2) → Bool
private abbrev count (n k : ℕ) := min k (Fintype.card (Idx n))

/-- On the original physical chain, the affine approximation has operator
error at most 1/K on the whole top-r subspace throughout the prescribed
horizon, once T ≥ K⁶(r+1)²L². Both infinite chains are drawn only once. -/
theorem frozen_edge_evolution (ranks : ℕ → ℕ) (phaseScale horizon : ℕ → ℝ) :
    ∀ᵐ ω ∂twoChains, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let r := count n (ranks n)
      let R := firstRanks (Idx n) r (min_le_right ..)
      let L := max 1 (phaseScale n)
      let T := max (K^6*((r:ℝ)+1)^2*L^2) (horizon n)
      let b := L/T
      let a := Real.sqrt (1-b^2)
      let x := observationPair n a b ω
      let U := (generator (base x)).2.isHermitian.eigenvectorUnitary
      let F := pathHamiltonian (pathPauliDisorderShell ω.1 n)
      ∀ t : ℝ, |t| ≤ T →
        let z := fun j => wave t (diagonalEnergy U F j)
        ‖(U.valᴴ*unitaryEvolution F t*U.val-diagonal z)*coordinateProjection R‖ ≤ 1/K := by
  let K (n : ℕ) : ℝ := (n+2:ℕ)
  let r (n : ℕ) := count n (ranks n)
  let R (n : ℕ) := firstRanks (Idx n) (r n) (min_le_right ..)
  let L (n : ℕ) := max 1 (phaseScale n)
  let T (n : ℕ) := max ((K n)^6*((r n:ℝ)+1)^2*(L n)^2) (horizon n)
  let b (n : ℕ) := L n/T n
  let a (n : ℕ) := Real.sqrt (1-(b n)^2)
  let η (n : ℕ) := (1/K n)^2/2
  let bad (n : ℕ) : Set (FieldPair n) := {x | ∃ t : ℝ, |t| ≤ T n ∧ η n<readingError (R n) (a n) (b n) x t}
  let event (n : ℕ) := observationPair n (a n) (b n) ⁻¹' bad n
  have hk (n : ℕ) : 1 ≤ K n := by dsimp only [K]; exact_mod_cast (by omega : 1≤n+2)
  have hk₀ (n : ℕ) : 0<K n := zero_lt_one.trans_le (hk n)
  have hl (n : ℕ) : 1≤L n := le_max_left ..
  have hl₀ (n : ℕ) : 0<L n := zero_lt_one.trans_le (hl n)
  have ht (n : ℕ) : L n ≤ T n := by
    apply le_trans _ (le_max_left ..)
    apply (le_self_pow₀ (hl n) (by norm_num : 2≠0)).trans
    apply le_mul_of_one_le_left (sq_nonneg _)
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (hk n)) (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg (r n)) : (1:ℝ)≤(r n:ℝ)+1))
  have ht₀ (n : ℕ) : 0<T n := (hl₀ n).trans_le (ht n)
  have he (n : ℕ) : 0<η n := div_pos (sq_pos_of_pos (one_div_pos.mpr (hk₀ n))) (by norm_num)
  have hs (n : ℕ) : (a n)^2+(b n)^2=1 := by
    have hb : b n ≤ 1 := (div_le_one (ht₀ n)).mpr (ht n)
    have hb₀ : 0≤b n := div_nonneg (hl₀ n).le (ht₀ n).le
    have hb₂ := pow_le_pow_left₀ hb₀ hb 2
    rw [one_pow] at hb₂
    rw [show (a n)^2=1-(b n)^2 from Real.sq_sqrt (sub_nonneg.mpr hb₂)]
    ring
  have hcost (n : ℕ) : twoChains.real (event n) ≤ 96/(K n)^3 := by
    have hmap := observation_law n (hs n)
    have hle := Measure.le_map_apply (μ:=twoChains) hmap.measurable.aemeasurable (bad n)
    rw [hmap.map_eq] at hle
    have hprob := (ENNReal.toReal_mono (measure_ne_top _ _) hle).trans (gaussian_ranked_readings n (R n) (hs n) (ht₀ n) (he n))
    apply hprob.trans
    have ha : 0 ≤ a n := Real.sqrt_nonneg _
    have ha' : a n ≤ 1 := by nlinarith only [hs n,sq_nonneg (b n),sq_nonneg (a n-1)]
    have hnn : 0≤1-a n := sub_nonneg.mpr ha'
    have hloss : 1-a n ≤ (b n)^2 := by nlinarith only [hs n,mul_nonneg ha (sub_nonneg.mpr ha')]
    have hm : (Fintype.card (PathLabel n):ℝ) ≤ 12*K n := by
      simp only [PathLabel,Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,Nat.cast_add,
        Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,K]
      linarith
    have hR : (rankWeight (R n):ℝ)=(r n:ℝ)^2 := by rw [firstRanks_weight,Nat.cast_pow]
    rw [hR]
    calc
      _ ≤ 4*T n*(b n)^2*((r n:ℝ)+1)^2*(12*K n)/η n := by
        have hr : (r n:ℝ) ≤ (r n:ℝ)+1 := le_add_of_nonneg_right zero_le_one
        gcongr
      _ = 96*(K n)^3*((r n:ℝ)+1)^2*(L n)^2/T n := by
        dsimp only [b,η]
        field_simp [(ht₀ n).ne',(hk₀ n).ne']
        ring
      _ ≤ _ := by
        apply (div_le_div_iff₀ (ht₀ n) (pow_pos (hk₀ n) 3)).mpr
        have hh : (K n)^6*((r n:ℝ)+1)^2*(L n)^2 ≤ T n := le_max_left ..
        linarith only [show 96*((K n)^6*((r n:ℝ)+1)^2*(L n)^2) ≤ 96*T n from
          mul_le_mul_of_nonneg_left hh (by norm_num)]
  have hp : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^3) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsum : Summable (fun n => twoChains.real (event n)) := by
    apply (((summable_nat_add_iff 2).mpr hp).mul_left 96).of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact (hcost n).trans_eq (by dsimp only [K]; ring)
  have hf : ∀ᵐ ω ∂twoChains, ∀ᶠ n : ℕ in atTop, ω∉event n := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top twoChains _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [hf] with ω hω
  filter_upwards [hω] with n hn
  intro K' r' R' L' T' b' a' x U F t ht' z
  let B := generator (rotated (a n) (b n) x)
  have hF : B.val=F := by dsimp only [B]; rw [recover_physical n (hs n) ω]; rfl
  have hgood : readingError (R n) (a n) (b n) x t ≤ η n := le_of_not_gt (fun h => hn ⟨t,ht',h⟩)
  let A := U.valᴴ*unitaryEvolution F t*U.val
  have hA : A ∈ unitary _ := mul_mem (mul_mem (Unitary.star_mem U.2) (unitaryEvolution_mem_unitary
    (isSelfAdjoint_pathHamiltonian _) t)) U.2
  have hz (j) : ‖z j‖=1 := by simp [z,wave,Complex.norm_exp]
  have hh := restricted_norm_sq (R n) A hA z hz
  have hsum' : (∑ j ∈ R n, ‖A j j-z j‖)=readingError (R n) (a n) (b n) x t := by
    change (∑ j ∈ R n, ‖(U.valᴴ*unitaryEvolution F t*U.val) j j-wave t (diagonalEnergy U F j)‖)=
      ∑ j ∈ R n, ‖(U.valᴴ*unitaryEvolution B.val t*U.val) j j-wave t (diagonalEnergy U B.val j)‖
    rw [hF]
  rw [hsum'] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (one_div_pos.mpr (hk₀ n)).le).mp
  exact hh.trans ((mul_le_mul_of_nonneg_left hgood (by norm_num : (0:ℝ)≤2)).trans_eq (by dsimp only [η]; ring))

#print axioms frozen_edge_evolution
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
