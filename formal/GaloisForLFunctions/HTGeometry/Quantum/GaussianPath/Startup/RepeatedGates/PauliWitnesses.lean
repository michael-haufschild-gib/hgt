import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.GaussianJet
import GaloisForLFunctions.HTGeometry.TwoReplicaPauliRelativeParityInverse
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordHallSymmetryReduction
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich

/-! # Second-order propagation along one or two physical bonds -/
open Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
open UntouchedSites
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n→Bool) (Fin n→Bool) ℂ

private theorem spin_anti {n : ℕ} (i : Fin n) {a b : Fin 3} (h : a ≠ b) :
    spin i a*spin i b=-(spin i b*spin i a) := by
  have lift (c : Fin 3) : finiteSingleSiteMatrix i (finiteQubitPauli c)=spin i c := finiteSingleSiteMatrix_pauli i c
  rw [←lift,←lift,
    finiteSingleSiteMatrix_mul,finiteSingleSiteMatrix_mul,finiteQubitPauli_mul_eq_neg_mul_of_ne h]
  simpa only [neg_one_smul] using finiteSingleSiteMatrix_smul i (-1) (finiteQubitPauli b*finiteQubitPauli a)

private theorem anti_symm {R : Type*} [Ring R] {A B : R} (h : A*B=-(B*A)) :
    B*A=-(A*B) := by rw [h,neg_neg]

private theorem anti_left {R : Type*} [Ring R] {A B C : R}
    (hb : A*B=-(B*A)) (hc : Commute A C) : A*(B*C)=-(B*C*A) := by
  rw [←mul_assoc,hb,neg_mul,mul_assoc B A C,hc.eq,mul_assoc]

private theorem anti_right {R : Type*} [Ring R] {A B C : R}
    (hb : Commute A B) (hc : A*C=-(C*A)) : A*(B*C)=-(B*C*A) := by
  rw [←mul_assoc,hb.eq,mul_assoc,hc,mul_neg,mul_assoc]

private theorem pair_sq {n : ℕ} {i j : Fin n} (h : i ≠ j) (a b : Fin 3) :
    (spin i a*spin j b)*(spin i a*spin j b)=1 := by
  rw [←spin_pair h]; exact finitePauliMatrix_mul_self _

private theorem unit_spin {n : ℕ} (i : Fin n) (a : Fin 3) : spin i a ∈ unitary _ :=
  finitePauliMatrix_mem_unitary _

private theorem eight_ne {n : ℕ} {M : Reg n} (h : M ∈ unitary _) : 8*M ≠ 0 := by
  intro hz
  have e := congrArg (fun T : Reg n => T*star M) hz
  simp only [mul_assoc,(Unitary.mem_iff.mp h).2,mul_one,zero_mul] at e
  let r : Fin n→Bool := fun _ => false
  have hrr := congrArg (fun T : Reg n => T r r) e
  norm_num [Matrix.ofNat_apply] at hrr

/-- Adjacent sites can carry a nonzero quadratic signal. The local Z
field supplies the second bracket with the XX bond. -/
private theorem one_bond {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    signal₂ (spin i 2) (spin j 2) (spin i 0*spin j 0+spin i 2) ≠ 0 := by
  let A := spin i 2
  let B := spin j 2
  let X := spin i 0*spin j 0
  have hax : A*X=-(X*A) := anti_left (spin_anti i (by decide : (2:Fin 3) ≠ 0)) (spin_comm h _ _)
  have hbx : B*X=-(X*B) := anti_right (spin_comm h.symm _ _) (spin_anti j (by decide : (2:Fin 3) ≠ 0))
  have hba : Commute B A := spin_comm h.symm _ _
  have e := double_bracket_of_paulis A B X A (pair_sq h _ _) (anti_symm hax)
    (Commute.refl A) hax hba.symm (anti_left (anti_right hba hbx) hba)
  rw [e]
  exact eight_ne (mul_mem (mul_mem (mul_mem (unit_spin i 2) (mul_mem (unit_spin i 0) (unit_spin j 0)))
    (unit_spin i 2)) (unit_spin j 2))

/-- Along a length-two segment the intermediate X and Y anticommute.
Each endpoint Z then detects the mixed term. -/
private theorem two_bonds {n : ℕ} {i m j : Fin n} (him : i ≠ m) (hmj : m ≠ j) (hij : i ≠ j) :
    signal₂ (spin i 2) (spin j 2) (spin i 0*spin m 0+spin m 1*spin j 0) ≠ 0 := by
  let A := spin i 2
  let B := spin j 2
  let X := spin i 0*spin m 0
  let Y := spin m 1*spin j 0
  have ha : A*X=-(X*A) := anti_left (spin_anti i (by decide : (2:Fin 3) ≠ 0)) (spin_comm him _ _)
  have hay : Commute A Y := (spin_comm him 2 1).mul_right (spin_comm hij 2 0)
  have hxi : Commute Y (spin i 0) := ((spin_comm him 0 1).mul_right (spin_comm hij 0 0)).symm
  have hxm : spin m 0*Y=-(Y*spin m 0) :=
    anti_left (spin_anti m (by decide : (0:Fin 3) ≠ 1)) (spin_comm hmj _ _)
  have hxy : Y*X=-(X*Y) := anti_right hxi (anti_symm hxm)
  have hba : Commute B A := spin_comm hij.symm _ _
  have hbx : Commute B X := (spin_comm hij.symm 2 0).mul_right (spin_comm hmj.symm 2 0)
  have hby : B*Y=-(Y*B) := anti_right (spin_comm hmj.symm _ _) (spin_anti j (by decide : (2:Fin 3) ≠ 0))
  have e := double_bracket_of_paulis A B X Y (pair_sq him _ _) (anti_symm ha) hay hxy hba.symm
    (anti_right (hba.mul_right hbx) hby)
  rw [e]
  exact eight_ne (mul_mem (mul_mem (mul_mem (unit_spin i 2) (mul_mem (unit_spin i 0) (unit_spin m 0)))
    (mul_mem (unit_spin m 1) (unit_spin j 0))) (unit_spin j 2))

/-- Both orientations of an edge are available in the real physical shell. -/
private theorem edge_word {n : ℕ} {i j : Fin (n+2)} (h : i.val+1=j.val ∨ j.val+1=i.val)
    (a b : Fin 3) : ∃ l : PathLabel n, finitePauliMatrix (pathWord l)=spin i a*spin j b := by
  have inc {u v : Fin (n+2)} (hu : u.val+1=v.val) (c d : Fin 3) :
      ∃ l : PathLabel n, finitePauliMatrix (pathWord l)=spin u c*spin v d := by
    let e : Fin (n+1) := ⟨u.val,by have := v.isLt; omega⟩
    have he : e.castSucc=u := Fin.ext rfl
    have hf : e.succ=v := Fin.ext hu
    refine ⟨.inr (e,c,d),?_⟩
    change finitePauliMatrix (pairLabel e.castSucc e.succ c d)=_
    have huv : u ≠ v := fun h => by have hv := congrArg Fin.val h; omega
    rw [he,hf,spin_pair huv]
  rcases h with h | h
  · exact inc h a b
  · obtain ⟨l,hl⟩ := inc h b a
    exact ⟨l,hl.trans (spin_comm (fun e => by subst j; omega : j ≠ i) _ _).eq⟩

private theorem two_terms {n : ℕ} (l k : PathLabel n) : ∃ w : PathShell n,
    pathHamiltonian w=finitePauliMatrix (pathWord l)+finitePauliMatrix (pathWord k) := by
  classical
  let f (a i : PathLabel n) : ℝ := if i=a then 1 else 0
  refine ⟨WithLp.toLp 2 (fun i => f l i+f k i),?_⟩
  rw [pathHamiltonian_eq_sum]
  simp only [Complex.ofReal_add,add_smul,Finset.sum_add_distrib]
  simp [f,ite_smul]

/-- Every ordered pair at distance one or two has a nonzero second
Heisenberg coefficient for almost every physical Gaussian generator. -/
theorem gaussian_short_signal₂ {n : ℕ} {i j : Fin (n+2)} (hij : i ≠ j)
    (hl : i.val ≤ j.val+2) (hr : j.val ≤ i.val+2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      signal₂ (spin i 2) (spin j 2) (pathHamiltonian (pathPauliDisorderShell ω n)) ≠ 0 := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases h : i.val+1=j.val ∨ j.val+1=i.val
  · obtain ⟨l,hl⟩ := edge_word h 0 0
    obtain ⟨w,hw⟩ := two_terms l (.inl (i,2))
    apply gaussian_signal₂_of_witness _ _ w
    rw [hw,hl]; exact one_bond hij
  · let m : Fin (n+2) := ⟨min i.val j.val+1,by have := i.isLt; have := j.isLt; omega⟩
    have hm : m.val=min i.val j.val+1 := rfl
    have him : i ≠ m := fun e => by have := congrArg Fin.val e; omega
    have hmj : m ≠ j := fun e => by have := congrArg Fin.val e; omega
    obtain ⟨l,hl'⟩ := edge_word (i:=i) (j:=m) (by omega) 0 0
    obtain ⟨k,hk'⟩ := edge_word (i:=m) (j:=j) (by omega) 1 0
    obtain ⟨w,hw⟩ := two_terms l k
    apply gaussian_signal₂_of_witness _ _ w
    rw [hw,hl',hk']; exact two_bonds him hmj hij

#print axioms gaussian_short_signal₂
end
end GaloisForLFunctions.HTGeometry.RepeatedGates
