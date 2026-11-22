import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.SelectedSpins

/-! # Four local spin flips cancel the common Hamiltonian background -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section
open LocalPatches
variable {n : ℕ}
local instance (N : ℕ) : CStarAlgebra (Register N) where

private def gen (u : PathShell n) := (-Complex.I) • pathHamiltonian u

private theorem gen_eq (u : PathShell n) (f : PathLabel n → ℝ) (v : PathShell n)
    (hv : ∀ l, v l=f l*u l) : gen v=weighted u f := by
  unfold gen weighted
  rw [pathHamiltonian_eq_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [hv,Complex.ofReal_mul,pathTermGenerator,←Complex.coe_smul,smul_smul]
  congr 1
  ring

private def family (u : PathShell n) (Q : Finset (Fin (n+1))) (X : Register (n+2)) :=
  ∃ f : PathLabel n → ℝ, (∀ l, |f l| ≤ 1) ∧ (∀ l∉nearBonds Q, f l=1) ∧ (X=weighted u f ∨ X= -weighted u f)

private theorem signed_bracket_le {R : Type*} [NormedRing R] (a b x y : R) (L : ℝ)
    (hx : x=a ∨ x= -a) (hy : y=b ∨ y= -b) (h : ‖a*b-b*a‖ ≤ L) : ‖x*y-y*x‖ ≤ L := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · exact h
  · rw [mul_neg,neg_mul,neg_sub_neg,norm_sub_rev]; exact h
  · rw [neg_mul,mul_neg,neg_sub_neg,norm_sub_rev]; exact h
  · simpa only [neg_mul,mul_neg,neg_neg] using h

private theorem family_bound (u : PathShell n) (Q : Finset (Fin (n+1))) (M : ℝ) (hM : 0≤M)
    (hm : ∀ e∈Q, localMass u e≤M^2) (X Y : Register (n+2)) (hx : family u Q X) (hy : family u Q Y) :
    ‖X*Y-Y*X‖ ≤ 4*43^2*Q.card*M^2 := by
  obtain ⟨f,hf,ho,he⟩ := hx
  obtain ⟨g,hg,hp,hj⟩ := hy
  exact signed_bracket_le (weighted u f) (weighted u g) X Y _ he hj
    (sparse_bracket u Q M hM hm f g hf hg (fun l hl => (ho l hl).trans (hp l hl).symm))

private theorem family_skew {u : PathShell n} {Q : Finset (Fin (n+1))} {X : Register (n+2)}
    (hx : family u Q X) : X ∈ skewAdjoint _ := by
  obtain ⟨f,_,_,he⟩ := hx
  have h : weighted u f ∈ skewAdjoint _ := (skewAdjoint _).sum_mem fun l _ =>
    skewAdjoint.smul_mem (f l) (pathTerm_properties u l).2.1
  rcases he with rfl|rfl
  · exact h
  · exact (skewAdjoint _).neg_mem h

/-- The error in replacing the echo by its mixed Hamiltonian is proportional
to the number of selected edges, regardless of the size of the full chain. -/
theorem echo_error (u : PathShell n) (Q : Finset (Fin (n+1))) (M t : ℝ) (hM : 0≤M) (ht : 0≤t)
    (hm : ∀ e∈Q, localMass u e≤M^2) (S T : Finset (Fin (n+2))) (hd : Disjoint S T)
    (hS : S⊆ends Q) (hT : T⊆ends Q) :
    ‖echo (unitaryEvolution (pathHamiltonian u) t) (flip S) (flip T)-
      unitaryEvolution (pathHamiltonian (mixedShell S T u)) (-t)‖ ≤ 16*(4*43^2*Q.card*M^2)*t^2 := by
  let v := signedShell S u
  let w := signedShell T u
  let p := signedShell S w
  let Z := [-gen u,gen v,-gen p,gen w]
  have hg (X : Register (n+2)) (hX : X∈Z) : family u Q X := by
    simp only [Z,List.mem_cons,List.not_mem_nil,or_false] at hX
    rcases hX with rfl|rfl|rfl|rfl
    · exact ⟨fun _ => 1,fun _ => abs_one.le,fun _ _ => rfl,Or.inr (congrArg Neg.neg (gen_eq u _ u fun _ => (one_mul _).symm))⟩
    · exact ⟨wordSign S,fun l => (wordSign_abs S l).le,off_sign hS,Or.inl (gen_eq u _ v fun _ => rfl)⟩
    · refine ⟨fun l => wordSign S l*wordSign T l,fun l => ?_,fun l hl => ?_,Or.inr (congrArg Neg.neg (gen_eq u _ p ?_))⟩
      · rw [abs_mul,wordSign_abs,wordSign_abs,one_mul]
      · change wordSign S l*wordSign T l=1
        rw [off_sign hS l hl,off_sign hT l hl,one_mul]
      · intro l; exact (mul_assoc ..).symm
    · exact ⟨wordSign T,fun l => (wordSign_abs T l).le,off_sign hT,Or.inl (gen_eq u _ w fun _ => rfl)⟩
  have hh := four_flow_error (-gen u) (gen v) (-gen p) (gen w) (4*43^2*Q.card*M^2) t ht
    (fun x hx => family_skew (hg x hx)) (fun x hx y hy => family_bound u Q M hM hm x y (hg x hx) (hg y hy))
  have hab := commute_of_isSiteSupported_disjoint hd (flip_supported S) (flip_supported T)
  have habH : (flip S*flip T)*pathHamiltonian u*(flip S*flip T)=pathHamiltonian p := by
    calc _=flip S*(flip T*pathHamiltonian u*flip T)*flip S := by
           conv_lhs => rhs; rw [hab.eq]
           simp only [mul_assoc]
         _=_ := by rw [conjugate_hamiltonian,conjugate_hamiltonian]
  let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  have he := echo_word H (flip S) (flip T) (finitePauliMatrix_mul_self _) (finitePauliMatrix_mul_self _) hab t
  dsimp only [H] at he
  rw [he,habH,conjugate_hamiltonian,conjugate_hamiltonian]
  have hsum : -gen u+gen v+-gen p+gen w= -gen (mixedShell S T u) := by
    unfold gen
    rw [←mixed_hamiltonian S T u,smul_sub,smul_add,smul_sub]; abel
  rw [hsum] at hh
  simpa only [unitaryEvolution,gen,v,p,w,neg_smul,smul_neg] using hh

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
