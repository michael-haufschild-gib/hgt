import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCouplings.Resampling
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.GaussianActions

/-! # Replacing the last longitudinal coefficient of a physical prefix -/
open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrefixCouplings
open SpectralJets SpectralJets.BoundaryField
noncomputable section

def terminalCoordinate (k : ℕ) : ℕ × PathPauliDirections := (k+2,Sum.inl 2)

private def address {n : ℕ} : PathLabel n → ℕ × PathPauliDirections
  | .inl (s,a) => (s.val,.inl a)
  | .inr (e,ab) => (e.val,.inr ab)

private theorem address_injective (n : ℕ) : Function.Injective (address (n:=n)) := by
  rintro (⟨s,a⟩|⟨s,a⟩) (⟨t,b⟩|⟨t,b⟩) h
  all_goals simp only [address,Prod.mk.injEq,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,and_false] at h ⊢
  all_goals first | exact h.elim | exact ⟨Fin.ext h.1,h.2⟩

private def lastLabel (k : ℕ) : PathLabel (k+1) := .inl (Fin.last (k+2),2)

private theorem last_matrix (k : ℕ) :
    finitePauliMatrix (pathWord (lastLabel k))=SpinExtension.lastPauli (k+2) 2 := by
  rw [SpinExtension.lastPauli_word]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [lastLabel,pathWord,onsiteWord]
  · simp [lastLabel,pathWord,onsiteWord,Fin.castSucc_ne_last,pauliIdentityLabel]

/-- Replacing the Gaussian coordinate by y adds exactly y−ωᵢ copies of
the terminal Pauli, and all other terms in the Hamiltonian agree. -/
theorem boundary_update (ω : PathPauliDisorder) (k : ℕ) (y z : ℝ) :
    boundaryHamiltonian (Function.update ω (terminalCoordinate k) y) k z =
      boundaryHamiltonian ω k ((y-ω (terminalCoordinate k))+z) := by
  classical
  let i := terminalCoordinate k
  let l₀ := lastLabel k
  let δ := y-ω i
  let p := pathPauliDisorderShell ω (k+1)
  let q := pathPauliDisorderShell (Function.update ω i y) (k+1)
  let Z := SpinExtension.lastPauli (k+2) 2
  have hc (l : PathLabel (k+1)) : q l = Function.update ω (address l₀) y (address l) := by
    cases l with
    | inl v => rfl
    | inr v => rfl
  have hbase (l : PathLabel (k+1)) : p l=ω (address l) := by cases l <;> rfl
  have hH : pathHamiltonian q=pathHamiltonian p+(δ:ℂ) • Z := by
    rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum]
    calc
      _ = ∑ l : PathLabel (k+1), (((p l:ℂ) • finitePauliMatrix (pathWord l))+
            (if l=l₀ then (δ:ℂ) • Z else 0)) := Finset.sum_congr rfl fun l _ => by
        rw [hc]
        by_cases h : l=l₀
        · subst l
          rw [Function.update_self,if_pos rfl,show finitePauliMatrix (pathWord l₀)=Z from last_matrix k,
            ←add_smul]
          congr 1
          change (y:ℂ)=(ω i:ℂ)+((y-ω i:ℝ):ℂ)
          push_cast
          ring
        · rw [Function.update_of_ne ((address_injective _).ne h),if_neg h,add_zero,hbase]
      _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  change pathHamiltonian q+(z:ℂ) • Z=pathHamiltonian p+((δ+z:ℝ):ℂ) • Z
  rw [hH,Complex.ofReal_add,add_smul]
  exact add_assoc _ _ _

/-- Joint continuity in the infinite draw and in the increment; each
fixed prefix uses only finitely many coordinate projections. -/
theorem continuous_boundary_draw (k : ℕ) : Continuous (fun p : PathPauliDisorder×ℝ => boundaryHamiltonian p.1 k p.2) := by
  unfold boundaryHamiltonian
  simp_rw [pathHamiltonian_eq_sum]
  apply Continuous.add _ ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)
  apply continuous_finsetSum
  intro l _
  have h : Continuous (fun p : PathPauliDisorder×ℝ => pathPauliDisorderShell p.1 (k+1) l) := by
    cases l with
    | inl v => exact (continuous_apply (v.1.val,Sum.inl v.2)).comp continuous_fst
    | inr v => exact (continuous_apply (v.1.val,Sum.inr v.2)).comp continuous_fst
  exact (Complex.continuous_ofReal.comp h).smul continuous_const

#print axioms boundary_update
end
end GaloisForLFunctions.HTGeometry.PrefixCouplings
