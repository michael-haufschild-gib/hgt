import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.WeightedFilters
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.SpinRelations
import GaloisForLFunctions.HTGeometry.PathDiagonalCarrier
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich

/-! # Propagation from one longitudinal bond through a tilted Ising path -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section
open UntouchedSites

abbrev Register (n : ℕ) := SpinMatrix (Fin n)
abbrev ZIndex (n : ℕ) := Fin (n+2) ⊕ Fin (n+1)

def support {n : ℕ} : ZIndex n → Finset (Fin (n+2))
  | .inl v => {v}
  | .inr e => {e.castSucc,e.succ}

def longitudinal {n : ℕ} (j : ZIndex n) : Register (n+2) :=
  finitePauliMatrix (pauliZSetLabel (support j))

def transverse {N : ℕ} (v : Fin N) : Register N := spin v 0

def tilted (n : ℕ) : Register (n+2) :=
  weighted transverse Finset.univ + weighted (longitudinal (n:=n)) Finset.univ

private theorem longitudinal_comm {n : ℕ} (i j : ZIndex n) :
    Commute (longitudinal i) (longitudinal j) := by
  have he (k : ZIndex n) : longitudinal k = diagonal (fun x => (zSetSign (support k) x:ℂ)) := by
    ext x y
    by_cases h : x=y
    · subst y; simp [longitudinal,finitePauliMatrix_pauliZSetLabel]
    · simp [longitudinal,finitePauliMatrix_pauliZSetLabel,h]
  rw [he,he]
  change _*_= _*_
  rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
  congr 1; funext x; exact mul_comm _ _

private theorem transverse_comm {N : ℕ} (i j : Fin N) :
    Commute (transverse i) (transverse j) := by
  by_cases h : i=j
  · subst j; exact Commute.refl _
  exact spin_comm h _ _

private theorem sign_flip {n : ℕ} (v : Fin (n+2)) (j : ZIndex n) :
    finitePauliConjugationSign (siteLabel v 0) (pauliZSetLabel (support j)) =
      if v∈support j then -1 else 1 := by
  unfold finitePauliConjugationSign
  rw [Finset.prod_eq_single v]
  · by_cases h : v∈support j <;> simp [siteLabel,pauliZSetLabel,h,boolPauliConjugationSign]
  · intro w _ hw; simp [siteLabel,hw,boolPauliConjugationSign]
  · simp

private theorem flip_z {n : ℕ} (v : Fin (n+2)) (j : ZIndex n) :
    transverse v*longitudinal j*transverse v =
      if v∈support j then -(longitudinal j) else longitudinal j := by
  unfold transverse spin longitudinal
  rw [finitePauliMatrix_conj,sign_flip]
  split <;> simp

private theorem flip_x {n : ℕ} (j : ZIndex n) (v : Fin (n+2)) :
    longitudinal j*transverse v*longitudinal j =
      if v∈support j then -(transverse v) else transverse v := by
  have hs : finitePauliConjugationSign (pauliZSetLabel (support j)) (siteLabel v 0)=
      finitePauliConjugationSign (siteLabel v 0) (pauliZSetLabel (support j)) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases hv : i=v <;> by_cases hj : i∈support j <;>
      simp [siteLabel,pauliZSetLabel,boolPauliConjugationSign,hv,hj]
  unfold transverse spin longitudinal
  rw [finitePauliMatrix_conj,hs,sign_flip]
  split <;> simp

private theorem fixes_family {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι]
    (P : ι → Matrices d) (Q : Matrices d) (hs : Q*Q=1) (h : ∀ i, Commute Q (P i)) :
    Q*weighted P Finset.univ*Q=weighted P Finset.univ := by
  have hc : Commute Q (weighted P Finset.univ) :=
    Commute.sum_right _ _ _ (fun i _ => (h i).smul_right _)
  rw [hc.eq,mul_assoc,hs,mul_one]

/-- A matrix commuting with the tilted Hamiltonian and the sum of any
nonempty collection of its ZZ bonds is scalar. Resolving one bond detects
both of its transverse site fields. Each site then detects all incident
longitudinal terms and hence the transverse fields of its neighbors. -/
theorem tilted_bond_scalar {n : ℕ} (X : Register (n+2)) (T : Finset (ZIndex n))
    (e₀ : Fin (n+1)) (he₀ : Sum.inr e₀∈T) (r : Fin (n+2)→Bool)
    (hH : Commute X (tilted n)) (hT : Commute X (weighted longitudinal T)) :
    X=X r r • (1 : Register (n+2)) := by
  let Z := longitudinal (n:=n)
  let F := transverse (N:=n+2)
  have hZu (j : ZIndex n) : Z j∈unitary (Register (n+2)) := finitePauliMatrix_mem_unitary _
  have hZsq (j : ZIndex n) : Z j*Z j=1 := finitePauliMatrix_mul_self _
  have hFu (i : Fin (n+2)) : F i∈unitary (Register (n+2)) := finitePauliMatrix_mem_unitary _
  have hFsq (i : Fin (n+2)) : F i*F i=1 := spin_sq _ _
  have recoverF (j : ZIndex n) (hj : Commute X (Z j)) : ∀ i∈support j, Commute X (F i) :=
    resolve_rejection F hFu hFsq transverse_comm X (Z j) _ (support j) hj hH
      (fixes_family Z (Z j) (hZsq j) (longitudinal_comm j)) (flip_x j)
  have recoverZ (i : Fin (n+2)) (hi : Commute X (F i)) (j : ZIndex n) (hm : i∈support j) :
      Commute X (Z j) := by
    let S := Finset.univ.filter (fun k : ZIndex n => i∈support k)
    have hH' : Commute X (weighted Z Finset.univ+weighted F Finset.univ) := by
      rw [add_comm (weighted Z Finset.univ) (weighted F Finset.univ)]; exact hH
    exact resolve_rejection Z hZu hZsq longitudinal_comm X (F i) _ S hi hH'
      (fixes_family F (F i) (hFsq i) (transverse_comm i))
      (fun k => by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using flip_z i k)
      j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩)
  have hb := resolve_weighted Z hZu hZsq longitudinal_comm X T hT (.inr e₀) he₀
  let K (v : Fin (n+2)) := Commute X (F v)
  have step (e : Fin (n+1)) : K e.castSucc ↔ K e.succ := by
    have hl : e.castSucc∈support (.inr e) := Finset.mem_insert_self ..
    have hr : e.succ∈support (.inr e) := by simp [support]
    exact ⟨fun h => recoverF _ (recoverZ _ h _ hl) _ hr,fun h => recoverF _ (recoverZ _ h _ hr) _ hl⟩
  have base (v : Fin (n+2)) : K 0 ↔ K v := by
    induction v using Fin.induction with
    | zero => rfl
    | succ e ih => exact ih.trans (step e)
  have h0 := (base e₀.castSucc).mpr (recoverF _ hb _ (Finset.mem_insert_self ..))
  apply scalar_of_all_sites r
  intro i a
  have hx := (base i).mp h0
  have hz : Commute X (spin i 2) := by
    have h := recoverZ i hx (.inl i) (by simp [support])
    change Commute X (finitePauliMatrix (onsiteWord i 2))
    rw [onsiteWord_two]; exact h
  rcases fin3_eq_cases a with rfl | rfl | rfl
  · exact hx
  · exact commute_third 2 hz hx
  · exact hz

#print axioms tilted_bond_scalar
end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
