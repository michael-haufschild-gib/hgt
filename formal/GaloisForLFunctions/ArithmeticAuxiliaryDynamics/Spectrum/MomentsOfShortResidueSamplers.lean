import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.FiniteSamplersForShortPeriods
import GaloisForLFunctions.FiniteFreeProbability.EulerRootFilters

/-!
# The exact cost of balancing higher residue-class moments

Applying successive anchored Euler operators weights each sample by a
Newton polynomial in its index. Uniformity of all prefixes of any one
word requires exactly one additional cyclotomic factor per prefix.
Both the shift choices and their order drop out. The minimum integral
mass grows as a power of lcm(1,…,K), while the minimum span grows linearly
in the number of tested moments.
-/

open Finset Polynomial FiniteFreeProbability
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

/-- Equal residue mass initially and after each successive coefficient weighting. -/
def balancesEulerMoments (K : ℕ) : List ℕ → ℂ[X] → Prop
  | [], p => EquidistributesThrough K p
  | s::w,p => EquidistributesThrough K p ∧ balancesEulerMoments K w (eulerFilter s p)

private def nodeChain (z : ℂ) : List ℕ → ℂ[X] → Prop
  | [],p => p.IsRoot z
  | s::w,p => p.IsRoot z ∧ nodeChain z w (eulerFilter s p)

private theorem split_nodes (K : ℕ) (w : List ℕ) (p : ℂ[X]) :
    balancesEulerMoments K w p ↔ ∀ z ∈ shortPeriodNodes K, nodeChain z w p := by
  induction w generalizing p with
  | nil => exact equidistributesThrough_iff_nodes K p
  | cons s w ih =>
    simp only [balancesEulerMoments,nodeChain,equidistributesThrough_iff_nodes,ih]
    constructor
    · exact fun h z hz => ⟨h.1 z hz,h.2 z hz⟩
    · exact fun h => ⟨fun z hz => (h z hz).1,fun z hz => (h z hz).2⟩

private theorem filter_multiplicity (s : ℕ) {z : ℂ} (hz : z ≠ 0) {p : ℂ[X]}
    (hp : p ≠ 0) (hr : p.IsRoot z) :
    eulerFilter s p ≠ 0 ∧ (eulerFilter s p).rootMultiplicity z = p.rootMultiplicity z - 1 := by
  have hf : eulerFilter s p ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by
    rw [eulerFilter_natDegree]
    exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hp hr))
  have hX (n : ℕ) : ((X : ℂ[X])^n).rootMultiplicity z = 0 :=
    rootMultiplicity_eq_zero (by simpa only [Polynomial.IsRoot.def,eval_pow,eval_X] using pow_ne_zero n hz)
  have hl := derivative_rootMultiplicity_of_root (p := (X : ℂ[X])^(s+1)*p) (t := z)
    (by simpa only [Polynomial.IsRoot.def,eval_mul,show p.eval z = 0 from hr,mul_zero])
  rw [eulerFilter_derivative_lift,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hf),
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) hp),hX,hX,zero_add,zero_add] at hl
  exact ⟨hf,hl⟩

private theorem node_chain_iff {z : ℂ} (hz : z ≠ 0) (w : List ℕ) {p : ℂ[X]} (hp : p ≠ 0) :
    nodeChain z w p ↔ w.length < p.rootMultiplicity z := by
  induction w generalizing p with
  | nil => exact (rootMultiplicity_pos hp).symm
  | cons s w ih =>
    change (p.IsRoot z ∧ nodeChain z w (eulerFilter s p)) ↔ w.length+1 < p.rootMultiplicity z
    by_cases hr : p.IsRoot z
    · obtain ⟨hf,he⟩ := filter_multiplicity s hz hp hr
      rw [and_iff_right hr,ih hf,he]
      omega
    · simp [hr,rootMultiplicity_eq_zero hr]

private theorem node_ne_zero {K : ℕ} {z : ℂ} (h : z ∈ shortPeriodNodes K) : z ≠ 0 := by
  obtain ⟨k,hk,hz⟩ := mem_biUnion.mp h
  exact (isPrimitiveRoot_of_mem_primitiveRoots hz).ne_zero (by have := (mem_Icc.mp hk).1; omega)

/-- For every string of Euler weights, balancing all weighted masses is exactly
divisibility by a fixed power of the shortest unweighted filter. -/
theorem balancesEulerMoments_iff_power (K : ℕ) (w : List ℕ) (p : ℂ[X]) :
    balancesEulerMoments K w p ↔ shortPeriodFilter K ^ (w.length+1) ∣ p := by
  classical
  by_cases hp : p=0
  · subst p
    simp only [dvd_zero,iff_true]
    induction w with
    | nil => exact (equidistributesThrough_iff_dvd K _).mpr (dvd_zero _)
    | cons s w ih => simpa only [balancesEulerMoments,eulerFilter,map_zero,mul_zero,derivative_zero,add_zero]
        using And.intro ((equidistributesThrough_iff_dvd K _).mpr (dvd_zero _)) ih
  rw [split_nodes,shortPeriodFilter,←Finset.prod_pow]
  constructor
  · intro h
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact (pairwise_coprime_X_sub_C (K := ℂ) Function.injective_id hab).pow
    · intro z hz
      exact (le_rootMultiplicity_iff hp).mp ((node_chain_iff (node_ne_zero hz) w hp).mp (h z hz))
  · intro h z hz
    apply (node_chain_iff (node_ne_zero hz) w hp).mpr
    apply (le_rootMultiplicity_iff hp).mpr
    exact (dvd_prod_of_mem _ hz).trans h

/-- Word length alone determines which samplers balance all prefix moments. -/
theorem moment_orders_are_interchangeable (K : ℕ) (v w : List ℕ) (h : v.length=w.length) (p : ℂ[X]) :
    balancesEulerMoments K v p ↔ balancesEulerMoments K w p := by
  simp only [balancesEulerMoments_iff_power,h]

/-- The least degree and least nonzero total mass are simultaneously attained by the
same signed integer sampler at every order. -/
theorem integral_moment_sampler_optimal (K : ℕ) (w : List ℕ) :
    let q := integralShortSampler K ^ (w.length+1)
    balancesEulerMoments K w (q.map (Int.castRingHom ℂ)) ∧
      q.eval 1 = (Nat.lcmUpto K : ℤ)^(w.length+1) ∧
      q.natDegree = (w.length+1)*∑ k ∈ Icc 2 K, k.totient ∧
      ∀ p : ℤ[X], balancesEulerMoments K w (p.map (Int.castRingHom ℂ)) →
        q ∣ p ∧ q.eval 1 ∣ p.eval 1 ∧ (p ≠ 0 → q.natDegree ≤ p.natDegree) := by
  dsimp only
  have hmap : (integralShortSampler K).map (Int.castRingHom ℂ) = shortPeriodFilter K := by
    simp only [integralShortSampler,Polynomial.map_prod,map_cyclotomic,shortPeriodFilter_eq_cyclotomics]
  have hm : (integralShortSampler K).Monic := monic_prod_of_monic _ _ fun k _ => cyclotomic.monic k ℤ
  have hdeg : (integralShortSampler K).natDegree = (shortPeriodFilter K).natDegree :=
    (hm.natDegree_map (Int.castRingHom ℂ)).symm.trans (congrArg natDegree hmap)
  refine ⟨?_,?_,?_,?_⟩
  · rw [balancesEulerMoments_iff_power,Polynomial.map_pow,hmap]
  · rw [eval_pow,integralShortSampler_mass]
  · rw [Polynomial.natDegree_pow,hdeg,shortPeriodFilter_degree]
  · intro p h
    rw [balancesEulerMoments_iff_power,←hmap,←Polynomial.map_pow] at h
    have hd := (Polynomial.map_dvd_map (Int.castRingHom ℂ) Int.cast_injective (hm.pow _)).mp h
    refine ⟨hd,?_,fun hp => natDegree_le_of_dvd hd hp⟩
    obtain ⟨r,hr⟩ := hd
    exact ⟨r.eval 1,by rw [hr,eval_mul]⟩

#print axioms balancesEulerMoments_iff_power
#print axioms integral_moment_sampler_optimal

end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
