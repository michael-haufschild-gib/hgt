import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.IndependentModes
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Adjoint
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity
import GaloisForLFunctions.HTGeometry.ThetaCompletedPluckerSandwich

/-! # Logarithmic energy from the measured particle number operators -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open CoassociativeSplitting ModeCapacities Finset
open scoped LinearPMap

theorem embed_coordinate (f : Core) (m : Occupation) : embed f (label m) = f m := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, hu, hv]
  | single n c =>
    rw [embed, Finsupp.linearCombination_single, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply, Finsupp.single_apply]
    by_cases h : n=m
    · subst n
      simp
    · rw [if_neg h, Pi.single_eq_of_ne (fun eqn => h (label.injective eqn.symm)), mul_zero]

theorem embed_injective : Function.Injective embed := by
  intro f g h
  exact Finsupp.ext fun m => (embed_coordinate f m).symm.trans
    ((congrArg (fun x : Gas => x (label m)) h).trans (embed_coordinate g m))

theorem dense_core : Dense (LinearMap.range embed : Set Gas) := by
  have basis : Dense (Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ+)) : Set Gas) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ+).dense_span
  apply basis.mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨n,rfl⟩
  exact ⟨ket (label.symm n),by rw [embed_ket, label.apply_symm_apply, HilbertSchmidt.lpBasis_apply]⟩

def coreEnergy : Core →ₗ[ℂ] Core :=
  Finsupp.linearCombination ℂ fun m => (energy (label m) : ℂ) • ket m

theorem coreEnergy_ket (m : Occupation) : coreEnergy (ket m) = (energy (label m) : ℂ) • ket m := by
  change coreEnergy (Finsupp.single m 1) = _
  rw [coreEnergy, Finsupp.linearCombination_single, one_smul]

private def eigenstate (m : Occupation) : hamiltonian.domain :=
  ⟨lp.single 2 (label m) 1,by
    rw [← HilbertSchmidt.lpBasis_apply]
    exact _root_.RHTower.lpBasis_mem_maximalRealDiagonalDomain energy (label m)⟩

private def domainMap : Core →ₗ[ℂ] hamiltonian.domain := Finsupp.linearCombination ℂ eigenstate

private theorem domain_ket (m : Occupation) : domainMap (ket m)=eigenstate m := by
  rw [domainMap,ket,Finsupp.linearCombination_single,one_smul]

theorem physical_energy (f : Core) :
    ∃ g : hamiltonian.domain, g.val = embed f ∧ hamiltonian g = embed (coreEnergy f) := by
  have inc : hamiltonian.domain.subtype.comp domainMap = embed := by
    apply core_ext
    intro m
    simp only [LinearMap.comp_apply, domain_ket, embed_ket]
    rfl
  have action : hamiltonian.toFun.comp domainMap = embed.comp coreEnergy := by
    apply core_ext
    intro m
    simp only [LinearMap.comp_apply, domain_ket, coreEnergy_ket, map_smul, embed_ket]
    exact HTGeometry.maximalRealDiagonal_single energy (label m) (eigenstate m).property
  exact ⟨domainMap f,LinearMap.congr_fun inc f,LinearMap.congr_fun action f⟩

/-- Each finite superposition involves only finitely many physical species. -/
def activeModes (f : Core) : Finset Nat.Primes := f.support.biUnion Finsupp.support

def modeEnergy (K : Kernel) (S : Finset Nat.Primes) : Core →ₗ[ℂ] Core :=
  ∑ p ∈ S, (Real.log (p.val:ℝ):ℂ) • number K p

private theorem mode_ket (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (line : s.re=1/2)
    (m : Occupation) (S : Finset Nat.Primes) (sub : m.support ⊆ S) :
    modeEnergy (kernel s u v) S (ket m) = coreEnergy (ket m) := by
  rw [modeEnergy, LinearMap.sum_apply,coreEnergy_ket]
  simp only [LinearMap.smul_apply, number_ket, counts_on_line s hu hv _ line, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have vals : ∑ p ∈ m.support, (m p:ℝ) * Real.log (p.val:ℝ) = energy (label m) :=
    (log_primeProduct m).symm
  have eqn : ∑ p ∈ S, (m p:ℝ) * Real.log (p.val:ℝ) = energy (label m) := by
    rw [← vals]
    exact (Finset.sum_subset sub (fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp, Nat.cast_zero, zero_mul])).symm
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, mul_comm] using
    congrArg Complex.ofReal eqn

/-- On all finite superpositions the actual self-adjoint Hamiltonian
is the sum of the measured prime number operators weighted by log p. -/
theorem sum_number (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (line : s.re=1/2)
    (f : Core) : ∃ g : hamiltonian.domain, g.val = embed f ∧
      hamiltonian g = embed (modeEnergy (kernel s u v) (activeModes f) f) := by
  obtain ⟨g,inc,act⟩ := physical_energy f
  refine ⟨g,inc,act.trans (congrArg embed ?_)⟩
  let T := modeEnergy (kernel s u v) (activeModes f)
  have finite : ∑ m ∈ f.support, Finsupp.single m (f m) = f := Finsupp.sum_single f
  change coreEnergy f = T f
  calc
    coreEnergy f = ∑ m ∈ f.support, coreEnergy (Finsupp.single m (f m)) := by
      rw [← map_sum,finite]
    _ = ∑ m ∈ f.support, T (Finsupp.single m (f m)) := by
      apply sum_congr rfl
      intro m hm
      have sub : m.support ⊆ activeModes f := fun p hp => mem_biUnion.mpr ⟨m,hm,hp⟩
      have basis := mode_ket s hu hv line m (activeModes f) sub
      have single : Finsupp.single m (f m) = f m • ket m := by rw [ket,Finsupp.smul_single',mul_one]
      rw [single,coreEnergy.map_smul,T.map_smul,←basis]
    _ = T f := by rw [←map_sum,finite]

#print axioms embed_injective
#print axioms dense_core
#print axioms physical_energy
#print axioms sum_number

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
