import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.CoordinateLift

/-! # One interval of exact circuit fits per extremal winding -/

open Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open SharpOccupation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The translates are spaced by one spectral period. Their widths depend only
on the original error and bandwidth; the two circuit diagonal phases set the origin. -/
def indexWindow (G offset x : ℝ) (N : ℤ) : Set ℝ :=
  Icc (((N:ℝ)+offset-x)/G) (((N:ℝ)+offset+x)/G)

private theorem index_mem {G offset x t : ℝ} (hG : 0<G) (N : ℤ) :
    t∈indexWindow G offset x N ↔ |t*G-offset-(N:ℝ)|≤x := by
  change _ ≤ t ∧ t ≤ _ ↔ _
  rw [div_le_iff₀ hG,le_div_iff₀ hG,abs_le]
  constructor <;> rintro ⟨hl,hu⟩ <;> constructor <;> linarith only [hl,hu]

private theorem unique_index {a x : ℝ} (hx : x<1/2) {N M : ℤ}
    (hN : |a-(N:ℝ)|≤x) (hM : |a-(M:ℝ)|≤x) : N=M := by
  have h (n : ℤ) (hn : |a-(n:ℝ)|≤x) : ⌊a+1/2⌋=n := by
    have hh := abs_lt.mp (hn.trans_lt hx)
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith only [hh.1,hh.2]
  exact (h N hN).symm.trans (h M hM)

/-- On every extremal clock band the exact operator-norm tube for a single
circuit is one interval, possibly empty. Its explicit relative winding uses
only one integer. All physical dates lie in these disjoint bands. -/
theorem exact_circuit_cells (W : unitary (Mat I)) (A : I → ℝ) (l u : I) {ε : ℝ}
    (he : ε∈Ioo (0:ℝ) (sqrt 2)) (hg : A l<A u) (hext : ∀ i, A i∈Icc (A l) (A u)) :
    let G := A u-A l
    let d := circuitTurns W
    let x := physicalArc ε
    let J := indexWindow G (d u-d l) x
    circuitDates W A ε ⊆ (⋃ N : ℤ, J N) ∧
      Pairwise (fun N M : ℤ => Disjoint (J N) (J M)) ∧
      ∀ N : ℤ, let m (i : I) := ⌊targetWord A d l u N i+1/2⌋
        (circuitDates W A ε ∩ J N=wordDates W A d m x ε ∩ J N) ∧
        Convex ℝ (circuitDates W A ε ∩ J N) := by
  intro G d x J
  have hx := (physicalArc_spec he.1 he.2).1.2
  have hG := sub_pos.mpr hg
  have hs : ε^2<2 := (pow_lt_pow_left₀ he.2 he.1.le (by decide : (2:ℕ)≠0)).trans_eq (sq_sqrt (by norm_num))
  have hit {t : ℝ} (hh : t∈circuitDates W A ε) :
      ∃ N : ℤ, t∈J N ∧ t∈wordDates W A d (fun i => ⌊targetWord A d l u N i+1/2⌋) x ε := by
    obtain ⟨m,hm⟩ := (date_iff_lift W A he).mp hh
    obtain ⟨hn,hword⟩ := canonical_word_date W A d m l u hx hg hext hm
    exact ⟨m u-m l,(index_mem hG _).mpr hn,hword⟩
  have hdis : Pairwise (fun N M : ℤ => Disjoint (J N) (J M)) := by
    intro N M hne
    exact disjoint_left.mpr fun _ hN hM => hne (unique_index hx ((index_mem hG N).mp hN) ((index_mem hG M).mp hM))
  refine ⟨fun t ht => ?_,hdis,?_⟩
  · obtain ⟨N,hN,_⟩ := hit ht
    exact mem_iUnion.mpr ⟨N,hN⟩
  · intro N m
    have heq : circuitDates W A ε ∩ J N=wordDates W A d m x ε ∩ J N := by
      ext t
      constructor
      · rintro ⟨ht,hN⟩
        obtain ⟨M,hM,hw⟩ := hit ht
        have he' : M=N := unique_index hx ((index_mem hG M).mp hM) ((index_mem hG N).mp hN)
        rw [he'] at hw
        exact ⟨hw,hN⟩
      · rintro ⟨hw,hN⟩
        exact ⟨(date_iff_lift W A he).mpr ⟨m,hw⟩,hN⟩
    exact ⟨heq,heq.symm ▸ (wordDates_convex W A d m hx.le hs).inter (convex_Icc _ _)⟩

#print axioms exact_circuit_cells
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
