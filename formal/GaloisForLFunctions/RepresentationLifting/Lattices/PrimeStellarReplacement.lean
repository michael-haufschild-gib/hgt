import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Prime descent of lattice cone determinants

A modular kernel vector gives an integral interior ray of its support face.
Cramer’s rule strictly lowers every nonzero child determinant.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Matrix Finset
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Dividing a nonzero vector by common factors of a base at least two
terminates, independently of the lattice dimension or choice of a pivot. -/
private theorem primitive_at_base (p : ℕ) (hp : 1 < p) (v : ι → ℤ) (hv : v ≠ 0) :
    ∃ k : ℕ, ∃ w : ι → ℤ, v = ((p:ℤ)^k) • w ∧ ∃ i, ¬(p:ℤ) ∣ w i := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  change v i ≠ 0 at hi
  generalize he : (v i).natAbs = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases h : ∀ j, (p:ℤ) ∣ v j
    · choose u hu using h
      have hni := congrArg Int.natAbs (hu i)
      simp only [Int.natAbs_mul,Int.natAbs_natCast] at hni
      have hui : u i ≠ 0 := fun hz => hi (by rw [hu i,hz,mul_zero])
      have hn : (u i).natAbs < n := by
        rw [← he,hni]
        exact lt_of_eq_of_lt (one_mul _).symm
          (Nat.mul_lt_mul_of_pos_right hp (Int.natAbs_pos.mpr hui))
      have hnu : u ≠ 0 := fun hz => hui (congrFun hz i)
      obtain ⟨k,w,hw,ha⟩ := ih _ hn u hnu hui rfl
      refine ⟨k+1,w,?_,ha⟩
      funext j
      change v j = (p:ℤ)^(k+1)*w j
      rw [hu j,hw,pow_succ']
      change (p:ℤ)*((p:ℤ)^k*w j) = _
      ring
    · push Not at h
      exact ⟨0,v,by simp,h⟩

private theorem replacement_determinant (A : Matrix ι ι ℤ) (c : ι → ℤ) (i : ι) :
    (A.updateCol i (A *ᵥ c)).det = A.det * c i := by
  rw [← Matrix.cramer_apply,cramer_eq_adjugate_mulVec,mulVec_mulVec,adjugate_mul,smul_mulVec,one_mulVec]
  rfl

/-- At each prime dividing a nonzero facet determinant, a single nonzero
residue ray strictly reduces the absolute determinant of every replacement
in its support. Entries of the normalized dependence are in the first residue interval. -/
theorem prime_stellar_replacement (p : ℕ) [hp : Fact p.Prime]
    (A : Matrix ι ι ℤ) (ha : A.det ≠ 0) (hd : (p:ℤ) ∣ A.det) :
    ∃ (c : ι → Fin p) (w : ι → ℤ) (k : ℕ),
      (∃ i, (c i).val ≠ 0) ∧ (∃ i, ¬(p:ℤ) ∣ w i) ∧
      (A *ᵥ (fun i => ((c i).val:ℤ))) = ((p:ℤ)^(k+1)) • w ∧
      ∀ i, (p:ℤ)^(k+1) * (A.updateCol i w).det = (c i).val * A.det ∧
        ((c i).val ≠ 0 → 0 < (A.updateCol i w).det.natAbs ∧
          (A.updateCol i w).det.natAbs < A.det.natAbs) := by
  let f := Int.castRingHom (ZMod p)
  let B := f.mapMatrix A
  have hB : B.det = 0 := by
    rw [show B.det = f A.det from (RingHom.map_det f A).symm]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  obtain ⟨u,hu,hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB
  let c (i : ι) : Fin p := ⟨(u i).val,(u i).val_lt⟩
  let a (i : ι) : ℤ := (c i).val
  have hcast : f ∘ a = u := by
    funext i
    change (((u i).val : ℤ) : ZMod p) = _
    simp
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
  have hai : (c i).val ≠ 0 := by
    intro hh
    apply hi
    rw [← hcast]
    change ((a i : ℤ) : ZMod p) = 0
    simp [a,hh]
  have hane : a ≠ 0 := fun hh => hai (Int.ofNat_inj.mp
    (show ((c i).val : ℤ) = ((0:ℕ):ℤ) from congrFun hh i))
  have hx : A *ᵥ a ≠ 0 := fun h => ha (Matrix.exists_mulVec_eq_zero_iff.mp ⟨a,hane,h⟩)
  have hdiv (j : ι) : (p:ℤ) ∣ (A *ᵥ a) j := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    change f ((A *ᵥ a) j) = 0
    rw [f.map_mulVec,hcast]
    exact congrFun hzero j
  choose v hv using hdiv
  have hrel : A *ᵥ a = (p:ℤ) • v := funext hv
  have hvne : v ≠ 0 := fun hh => hx (by rw [hrel,hh,smul_zero])
  obtain ⟨k,w,hw,hprim⟩ := primitive_at_base p hp.out.one_lt v hvne
  rw [hw,smul_smul,← pow_succ'] at hrel
  refine ⟨c,w,k,⟨i,hai⟩,hprim,hrel,?_⟩
  intro j
  have hdet := replacement_determinant A a j
  rw [hrel,det_updateCol_smul,mul_comm A.det] at hdet
  refine ⟨hdet,fun hj => ?_⟩
  have habs := congrArg Int.natAbs hdet
  simp only [Int.natAbs_mul,Int.natAbs_pow,a,Int.natAbs_natCast] at habs
  have hA := Int.natAbs_pos.mpr ha
  have hpos : 0 < (A.updateCol j w).det.natAbs := by
    by_contra! hn
    have : (A.updateCol j w).det.natAbs = 0 := Nat.eq_zero_of_le_zero hn
    rw [this,mul_zero] at habs
    exact (Nat.mul_pos (Nat.pos_of_ne_zero hj) hA).ne' habs.symm
  have hpow : p ≤ p^(k+1) := by
    simpa using Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp.out.one_lt) (Nat.succ_le_succ (Nat.zero_le k))
  have hlt := Nat.mul_lt_mul_of_pos_right ((c j).isLt.trans_le hpow) hA
  rw [← habs] at hlt
  exact ⟨hpos,Nat.lt_of_mul_lt_mul_left hlt⟩

omit [DecidableEq ι] in
/-- A facet energy that decreases for any choice of a bad facet. Up to
the dimension many children may replace it. Each strict determinant drop
pays for every child, so no largest-determinant selection is necessary. -/
theorem stellar_children_energy_lt (S : Finset ι) (d : ι → ℕ) (D : ℕ)
    (hD : 0 < D) (h : ∀ i ∈ S, d i < D) :
    ∑ i ∈ S, (Fintype.card ι+1)^(d i) < (Fintype.card ι+1)^D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hD.ne'
  have hbase : 0 < Fintype.card ι+1 := Nat.succ_pos _
  calc
    _ ≤ ∑ _ ∈ S, (Fintype.card ι+1)^m :=
      sum_le_sum fun i hi => Nat.pow_le_pow_right hbase (Nat.le_of_lt_succ (h i hi))
    _ = S.card*(Fintype.card ι+1)^m := by simp
    _ < (Fintype.card ι+1)*(Fintype.card ι+1)^m :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_of_le S.card_le_univ) (pow_pos hbase _)
    _ = _ := (pow_succ' _ _).symm
#print axioms prime_stellar_replacement
#print axioms stellar_children_energy_lt

end
end GaloisForLFunctions.RepresentationLifting
