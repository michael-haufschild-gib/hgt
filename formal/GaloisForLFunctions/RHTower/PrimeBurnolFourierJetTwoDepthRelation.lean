import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetTwoDepthRefinement
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetCubicClosure

/-!
# Complete cubic: finite refinement failure and all-parameter graph classification

Subtracting the exact singleton graph assembly from the actual two-depth packet
graph yields an invertible vertical action on a prime-depth tail. Thus the finite
relation is single-valued exactly at zero, before any completion. Its closure is
G × G at every nonzero parameter and G × {0} at zero. Every source coordinate,
physical output, actual Gram inverse and term of the cubic is retained.
-/

open Complex Set Filter Topology Matrix
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem cellIndex_zero : (finSumFinEquiv.symm (0 : Fin 2) : Fin 1 ⊕ Fin 1)=Sum.inl 0 := rfl
private theorem cellIndex_one : (finSumFinEquiv.symm (1 : Fin 2) : Fin 1 ⊕ Fin 1)=Sum.inr 0 := rfl

def burnolJetCellRestriction {N : ℕ} (x : Fin N ⊕ Fin N → ℂ) (i : Fin N) : Fin 1 ⊕ Fin 1 → ℂ :=
  Sum.elim (fun _ => x (Sum.inl i)) (fun _ => x (Sum.inr i))

theorem primeBurnolJetPacketSynthesis_cells {N : ℕ} (pe : Fin N → Nat.Primes × ℕ)
    (x : Fin N ⊕ Fin N → ℂ) :
    primeBurnolJetPacketSynthesis pe x=∑ i,
      primeBurnolJetPacketSynthesis (primeBurnolSingletonPacket (pe i)) (burnolJetCellRestriction x i) := by
  simp [primeBurnolJetPacketSynthesis,Fintype.linearCombination_apply,Fintype.sum_sum_type,
    burnolJetCellRestriction,primeBurnolSingletonPacket,primeBurnolJetGraphColumn,
    Finset.sum_add_distrib]

theorem burnolJetCellRestriction_assembly_mulVec {N : ℕ}
    (A : Fin N → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)
    (x : Fin N ⊕ Fin N → ℂ) (i : Fin N) :
    burnolJetCellRestriction ((burnolJetCellAssembly (fun j => burnolJetCellReindex (A j))).mulVec x) i=
      (A i).mulVec (burnolJetCellRestriction x i) := by
  ext (j|j) <;> fin_cases j <;>
    simp [burnolJetCellRestriction,burnolJetCellAssembly,
      Matrix.diagonal,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,ite_mul,
      burnolJetCellReindex,Matrix.reindex_apply,cellIndex_zero,cellIndex_one]

theorem primeBurnolFourierJetCubic_twoDepth (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    primeBurnolFourierJetCubic (primeBurnolTwoDepthPacket p n) a=
      primeBurnolFourierJetConstantThetaCubic (primeBurnolTwoDepthPacket p n) p a := by
  have h : primeBurnolFourierJetThetaMatrix (primeBurnolTwoDepthPacket p n) a=
      burnolJetThetaMatrix 2 p a := by
    ext (i|i) (j|j) <;>
      simp [primeBurnolFourierJetThetaMatrix,primeBurnolTwoDepthPacket,burnolJetThetaMatrix,
        Matrix.diagonal,Matrix.one_apply,mul_ite]
  simp only [primeBurnolFourierJetCubic,h,primeBurnolFourierJetConstantThetaCubic]

theorem primeBurnolFourierJetCubicRelation_singleton_assembly (p : Nat.Primes) (n : ℕ) (a : ℝ)
    (x : Fin 2 ⊕ Fin 2 → ℂ) :
    (primeBurnolJetPacketSynthesis (primeBurnolTwoDepthPacket p n) x,
      primeBurnolJetPacketSynthesis (primeBurnolTwoDepthPacket p n)
        ((primeBurnolTwoDepthSingletonAssembly p n a).mulVec x)) ∈ primeBurnolFourierJetCubicRelation a := by
  have h (i : Fin 2) := primeBurnolFourierJetCubicRelation_packet
    (primeBurnolSingletonPacket (primeBurnolTwoDepthPacket p n i)) a (burnolJetCellRestriction x i)
  simp only [primeBurnolFourierJetCubic_singleton] at h
  have hh := Submodule.sum_mem (primeBurnolFourierJetCubicRelation a) (fun i (_ : i ∈ Finset.univ) => h i)
  rw [primeBurnolJetPacketSynthesis_cells,primeBurnolJetPacketSynthesis_cells]
  simp only [primeBurnolTwoDepthSingletonAssembly,burnolJetCellRestriction_assembly_mulVec]
  simpa [primeBurnolTwoDepthPacket] using hh

theorem primeBurnolFourierJetCubicRelation_refinement (p : Nat.Primes) (n : ℕ) (a : ℝ)
    (x : Fin 2 ⊕ Fin 2 → ℂ) :
    (0,primeBurnolJetPacketSynthesis (primeBurnolTwoDepthPacket p n)
      ((primeBurnolTwoDepthRefinement p n a).mulVec x)) ∈ primeBurnolFourierJetCubicRelation a := by
  have hp := primeBurnolFourierJetCubicRelation_packet (primeBurnolTwoDepthPacket p n) a x
  rw [primeBurnolFourierJetCubic_twoDepth] at hp
  have h := (primeBurnolFourierJetCubicRelation a).sub_mem hp
    (primeBurnolFourierJetCubicRelation_singleton_assembly p n a x)
  simpa only [Prod.mk_sub_mk,sub_self,primeBurnolTwoDepthRefinement,Matrix.sub_mulVec,map_sub] using h

theorem primeBurnolFourierJetCubicRelation_twoDepth_vertical (p : Nat.Primes) (n : ℕ) (a : ℝ)
    (hu : IsUnit (primeBurnolTwoDepthRefinement p n a)) (x : Fin 2 ⊕ Fin 2 → ℂ) :
    (0,primeBurnolJetPacketSynthesis (primeBurnolTwoDepthPacket p n) x) ∈ primeBurnolFourierJetCubicRelation a := by
  obtain ⟨y,hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu x
  simpa only [hy] using primeBurnolFourierJetCubicRelation_refinement p n a y

theorem primeBurnolFourierJetCubicRelation_twoDepth_horizontal (p : Nat.Primes) (n : ℕ) (a : ℝ)
    (hu : IsUnit (primeBurnolTwoDepthRefinement p n a)) (x : Fin 2 ⊕ Fin 2 → ℂ) :
    (primeBurnolJetPacketSynthesis (primeBurnolTwoDepthPacket p n) x,0) ∈ primeBurnolFourierJetCubicRelation a := by
  have hp := primeBurnolFourierJetCubicRelation_packet (primeBurnolTwoDepthPacket p n) a x
  have hv := primeBurnolFourierJetCubicRelation_twoDepth_vertical p n a hu
    ((primeBurnolFourierJetCubic (primeBurnolTwoDepthPacket p n) a).mulVec x)
  simpa only [Prod.mk_sub_mk,sub_zero,sub_self] using (primeBurnolFourierJetCubicRelation a).sub_mem hp hv

theorem primeBurnolFourierJetCubicRelation_twoDepth_first_vertical (p : Nat.Primes) (n : ℕ) (a : ℝ)
    (hu : IsUnit (primeBurnolTwoDepthRefinement p n a)) (i : Fin 1 ⊕ Fin 1) :
    (0,primeBurnolJetGraphColumn (primeBurnolSingletonPacket (p,n)) i) ∈ primeBurnolFourierJetCubicRelation a := by
  have h := primeBurnolFourierJetCubicRelation_twoDepth_vertical p n a hu
    (Pi.single (Sum.map (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (0 : Fin 2)) i) 1)
  cases i <;> simpa [primeBurnolJetPacketSynthesis,Fintype.linearCombination_apply_single,
    primeBurnolJetGraphColumn,primeBurnolSingletonPacket,primeBurnolTwoDepthPacket] using h

theorem primeBurnolFourierJetCubicRelation_twoDepth_first_horizontal (p : Nat.Primes) (n : ℕ) (a : ℝ)
    (hu : IsUnit (primeBurnolTwoDepthRefinement p n a)) (i : Fin 1 ⊕ Fin 1) :
    (primeBurnolJetGraphColumn (primeBurnolSingletonPacket (p,n)) i,0) ∈ primeBurnolFourierJetCubicRelation a := by
  have h := primeBurnolFourierJetCubicRelation_twoDepth_horizontal p n a hu
    (Pi.single (Sum.map (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (0 : Fin 2)) i) 1)
  cases i <;> simpa [primeBurnolJetPacketSynthesis,Fintype.linearCombination_apply_single,
    primeBurnolJetGraphColumn,primeBurnolSingletonPacket,primeBurnolTwoDepthPacket] using h

theorem primeBurnolFourierJetCubicRelation_closure_unbalanced (p : Nat.Primes) {a : ℝ}
    (ha : a≠0) (hb : primeBurnolThetaVisibility a p^2≠primeBurnolThetaContrast a p^2) :
    (primeBurnolFourierJetCubicRelation a).topologicalClosure=
      primeBurnolFourierJetEvenGraph.topologicalClosure.prod
        primeBurnolFourierJetEvenGraph.topologicalClosure := by
  let L := (primeBurnolFourierJetCubicRelation a).topologicalClosure
  obtain ⟨N,hN⟩ := eventually_atTop.mp (primeBurnolTwoDepthRefinement_eventually_isUnit p ha hb)
  have hv : ∀ w ∈ primeBurnolFourierJetEvenGraph.topologicalClosure, (0,w) ∈ L := by
    let V : Submodule ℂ BurnolJetAmbient := L.comap (LinearMap.inr ℂ _ _)
    have hV : IsClosed (V : Set BurnolJetAmbient) := by
      change IsClosed ((fun w : BurnolJetAmbient => ((0 : BurnolJetAmbient),w)) ⁻¹' (L : Set _))
      exact (primeBurnolFourierJetCubicRelation a).isClosed_topologicalClosure.preimage (by fun_prop)
    apply primeBurnolJetTail_columns_dense p N V hV
    intro n i
    exact (primeBurnolFourierJetCubicRelation a).le_topologicalClosure
      (primeBurnolFourierJetCubicRelation_twoDepth_first_vertical p (n+N) a
        (hN (n+N) (Nat.le_add_left N n)) i)
  have hh : ∀ w ∈ primeBurnolFourierJetEvenGraph.topologicalClosure, (w,0) ∈ L := by
    let H : Submodule ℂ BurnolJetAmbient := L.comap (LinearMap.inl ℂ _ _)
    have hH : IsClosed (H : Set BurnolJetAmbient) := by
      change IsClosed ((fun w : BurnolJetAmbient => (w,(0 : BurnolJetAmbient))) ⁻¹' (L : Set _))
      exact (primeBurnolFourierJetCubicRelation a).isClosed_topologicalClosure.preimage (by fun_prop)
    apply primeBurnolJetTail_columns_dense p N H hH
    intro n i
    exact (primeBurnolFourierJetCubicRelation a).le_topologicalClosure
      (primeBurnolFourierJetCubicRelation_twoDepth_first_horizontal p (n+N) a
        (hN (n+N) (Nat.le_add_left N n)) i)
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · intro z hz
      have h := primeBurnolFourierJetCubicRelation_le a hz
      exact ⟨primeBurnolFourierJetEvenGraph.le_topologicalClosure h.1,
        primeBurnolFourierJetEvenGraph.le_topologicalClosure h.2⟩
    · exact primeBurnolFourierJetEvenGraph.isClosed_topologicalClosure.prod
        primeBurnolFourierJetEvenGraph.isClosed_topologicalClosure
  · intro z hz
    have h := L.add_mem (hh z.1 hz.1) (hv z.2 hz.2)
    simpa only [Prod.mk_add_mk,add_zero,zero_add] using h

theorem primeBurnolTheta_exists_unbalanced (a : ℝ) :
    ∃ p : Nat.Primes, primeBurnolThetaVisibility a p^2≠primeBurnolThetaContrast a p^2 := by
  obtain ⟨r,_,hr⟩ := Nat.exists_infinite_primes 0
  let p : Nat.Primes := ⟨r,hr⟩
  by_cases hb : primeBurnolThetaVisibility a p^2=primeBurnolThetaContrast a p^2
  · obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (p.val+1)
    have hpq : p≠(⟨q,hprime⟩ : Nat.Primes) := by
      intro he
      have he' := congrArg Subtype.val he
      change p.val=q at he'
      omega
    exact ⟨⟨q,hprime⟩,fun h => hpq (primeBurnolTheta_balanced_prime_unique a hb h)⟩
  · exact ⟨p,hb⟩

theorem primeBurnolFourierJetCubicRelation_closure_nonzero {a : ℝ} (ha : a≠0) :
    (primeBurnolFourierJetCubicRelation a).topologicalClosure=
      primeBurnolFourierJetEvenGraph.topologicalClosure.prod
        primeBurnolFourierJetEvenGraph.topologicalClosure := by
  obtain ⟨p,hp⟩ := primeBurnolTheta_exists_unbalanced a
  exact primeBurnolFourierJetCubicRelation_closure_unbalanced p ha hp

theorem primeBurnolFourierJetCubicRelation_no_single_valued_extension {a : ℝ} (ha : a≠0) :
    ¬ ∃ L : Submodule ℂ (BurnolJetAmbient × BurnolJetAmbient),
      primeBurnolFourierJetCubicRelation a ≤ L ∧ ∀ z, (0,z) ∈ L → z=0 := by
  rintro ⟨L,hcontains,hsingle⟩
  obtain ⟨p,hp⟩ := primeBurnolTheta_exists_unbalanced a
  obtain ⟨N,hN⟩ := eventually_atTop.mp (primeBurnolTwoDepthRefinement_eventually_isUnit p ha hp)
  let z := primeBurnolJetGraphColumn (primeBurnolSingletonPacket (p,N)) (Sum.inl 0)
  have hz := primeBurnolFourierJetCubicRelation_twoDepth_first_vertical p N a (hN N le_rfl) (Sum.inl 0)
  have hzero := hsingle z (hcontains hz)
  have hf : primeBurnolEvenFeatureLp (p,N)=0 := congrArg (fun w : BurnolJetAmbient => w.1.1) hzero
  exact (primeBurnolFourierPair_linearIndependent (primeBurnolSingletonPacket (p,N))).ne_zero
    (Sum.inl 0) hf

/-- Complete parameter classification for the actual finite-packet relation. -/
theorem primeBurnolFourierJetCubicRelation_closure_classification (a : ℝ) :
    (primeBurnolFourierJetCubicRelation a).topologicalClosure=
      if a=0 then primeBurnolFourierJetEvenGraph.topologicalClosure.prod ⊥
      else primeBurnolFourierJetEvenGraph.topologicalClosure.prod
        primeBurnolFourierJetEvenGraph.topologicalClosure := by
  classical
  split_ifs with ha
  · subst a
    obtain ⟨p,_,hp⟩ := Nat.exists_infinite_primes 0
    exact primeBurnolFourierJetCubicRelation_closure_zero ⟨p,hp⟩
  · exact primeBurnolFourierJetCubicRelation_closure_nonzero ha

/-- Compatibility already fails algebraically away from zero, before completion. -/
theorem primeBurnolFourierJetCubicRelation_single_valued_iff (a : ℝ) :
    (∀ z, (0,z) ∈ primeBurnolFourierJetCubicRelation a → z=0) ↔ a=0 := by
  constructor
  · intro h
    by_contra ha
    exact primeBurnolFourierJetCubicRelation_no_single_valued_extension ha
      ⟨primeBurnolFourierJetCubicRelation a,le_rfl,h⟩
  · rintro rfl z hz
    have h := (primeBurnolFourierJetCubicRelation 0).le_topologicalClosure hz
    rw [primeBurnolFourierJetCubicRelation_closure_classification,if_pos rfl] at h
    exact h.2

end RHTower
