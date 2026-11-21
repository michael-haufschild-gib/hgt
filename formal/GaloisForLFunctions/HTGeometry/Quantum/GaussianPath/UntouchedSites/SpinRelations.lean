import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.PauliFilter
import GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir
import GaloisForLFunctions.HTGeometry.FinitePauliDepolarizing

/-! # Local Pauli brackets and the scalar commutant of the full register -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section
variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem lift_spin (v : S) (a : Fin 3) : finiteSingleSiteMatrix v (finiteQubitPauli a) = spin v a :=
  finiteSingleSiteMatrix_pauli v a

theorem spin_comm {v w : S} (hv : v ≠ w) (a b : Fin 3) : Commute (spin v a) (spin w b) := by
  rw [←lift_spin,←lift_spin]
  exact finiteSingleSiteMatrix_comm_of_ne hv _ _

theorem spin_sq (v : S) (a : Fin 3) : spin v a*spin v a = 1 := finitePauliMatrix_mul_self _

theorem spin_pair {v w : S} (h : v ≠ w) (a b : Fin 3) :
    finitePauliMatrix (pairLabel v w a b) = spin v a*spin w b := by
  simp only [spin,finitePauliMatrix_eq_finiteLocalMatrix,finiteLocalMatrix_mul]
  congr 1
  funext s
  by_cases hs : s=v
  · subst s
    simp [pairLabel,siteLabel,h,boolPauliOption]
  · by_cases hw : s=w <;> simp [pairLabel,siteLabel,hs,hw,Ne.symm h,boolPauliOption]

theorem spin_bracket (v : S) (a : Fin 3) :
    spin v a * spin v (a+1) - spin v (a+1) * spin v a = (2*Complex.I) • spin v (a+2) := by
  have h := finiteSingleSitePauli_bracket v a (a+1)
  simp only [lift_spin] at h
  rw [h,Fin.sum_univ_three]
  fin_cases a <;> simp (config := {decide := true}) [pauliStructureCoeff]

theorem commute_third {U : SpinMatrix S} {v : S} (a : Fin 3) (h : Commute U (spin v a))
    (h' : Commute U (spin v (a+1))) : Commute U (spin v (a+2)) := by
  have hc := (h.mul_right h').sub_right (h'.mul_right h)
  rw [spin_bracket] at hc
  have he := hc.smul_right ((2*Complex.I)⁻¹ : ℂ)
  simpa only [smul_smul,inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) Complex.I_ne_zero),one_smul] using he

/-- The commutant of all on-site Pauli matrices is scalar. -/
theorem scalar_of_all_sites {U : SpinMatrix S} (r : S → Bool)
    (h : ∀ v a, Commute U (spin v a)) : U = U r r • (1 : SpinMatrix S) := by
  classical
  have hall (p : S → Option (Fin 3)) : Commute U (finitePauliMatrix p) := by
    let term (v : S) := finiteSingleSiteMatrix v (boolPauliOption (p v))
    have ht (v : S) : Commute U (term v) := by
      dsimp only [term]
      cases hp : p v with
      | none => rw [boolPauliOption,finiteSingleSiteMatrix_one]; exact Commute.one_right _
      | some a => change Commute U (finiteSingleSiteMatrix v (finiteQubitPauli a)); rw [lift_spin]; exact h v a
    let cut (s : Finset S) := finiteLocalMatrix fun v => if v ∈ s then boolPauliOption (p v) else 1
    have hcut (s : Finset S) : Commute U (cut s) := by
      induction s using Finset.induction_on with
      | empty =>
        have he : cut ∅ = 1 := by simp [cut,finiteLocalMatrix_one]
        rw [he]; exact Commute.one_right _
      | @insert v s hv ih =>
        have he : cut (insert v s) = term v * cut s := by
          dsimp [cut,term,finiteSingleSiteMatrix]
          rw [finiteLocalMatrix_mul]
          congr 1
          funext w
          by_cases h' : w=v
          · subst w; simp [hv]
          · simp [h']
        rw [he]; exact (ht v).mul_right ih
    have he : cut Finset.univ = finitePauliMatrix p := by
      simp [cut,finitePauliMatrix_eq_finiteLocalMatrix]
    rw [←he]; exact hcut _
  have hconj (p : S → Option (Fin 3)) : finitePauliMatrix p*U*finitePauliMatrix p=U := by
    rw [←(hall p).eq,mul_assoc,finitePauliMatrix_mul_self,mul_one]
  have hd := sum_finitePauliMatrix_conj U
  simp only [hconj,Finset.sum_const,Finset.card_univ] at hd
  let m := Fintype.card (S → Option (Fin 3))
  have hm : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : ∃ z : ℂ, U = z • (1 : SpinMatrix S) := by
    refine ⟨(m:ℂ)⁻¹*((2:ℂ)^Fintype.card S*U.trace),?_⟩
    calc
      U = (m:ℂ)⁻¹ • ((m:ℂ) • U) := by rw [smul_smul,inv_mul_cancel₀ hm,one_smul]
      _ = _ := by rw [Nat.cast_smul_eq_nsmul ℂ,hd,smul_smul]
  obtain ⟨z,hz⟩ := he
  rw [hz]
  simp

#print axioms scalar_of_all_sites
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
