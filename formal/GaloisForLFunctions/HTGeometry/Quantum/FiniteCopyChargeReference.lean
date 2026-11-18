import GaloisForLFunctions.HTGeometry.Quantum.AllCopyChargeGauge

/-!
# Finite determination of integer-charge phases

Normalize the occupied charge gaps by their gcd. When their absolute
values are at most Q, the observations through max(2,2Q−1) copies
determine every observation of a phase twist. Unequal magnitudes cost
at most 2Q−1. Equal magnitudes need only two edges.
-/

noncomputable section
open Finset Matrix
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation
open CollectiveDiophantineGeometry.Simplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem phase_multiple {z w : Circle} {d : ℤ} (h : z^d=w^d) (a : ℤ) :
    z^(a*d)=w^(a*d) := by rw [mul_comm a,zpow_mul,zpow_mul,h]

/-- A normalized pairwise minor tests one character. Equal magnitudes use
the primitive relation of length two even when both gaps are large. -/
private theorem minor_test (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian)
    (z w : Circle) (v : Edge A → ℤ) (g : ℤ) (hv : edgeGap q=g • v)
    (Q : ℕ) (hQ : ∀ e, (v e).natAbs≤Q)
    (tested : ∀ n≤max 2 (2*Q-1), ∀ d∈frequencies q b A n, z^d=w^d)
    (e f : Edge A) : z^(minorColumn v (edgeGap b) (e,f))=w^(minorColumn v (edgeGap b) (e,f)) := by
  have charge (i : Edge A) : edgeGap q i = g*v i := congrFun hv i
  have pair (u l : ℤ) (bal : u*v e+l*v f=0) (cost : u.natAbs+l.natAbs≤max 2 (2*Q-1)) :=
    tested _ cost _ (pair_frequency q b ha e f u l (by
      rw [charge,charge,show u*(g*v e)+l*(g*v f)=g*(u*v e+l*v f) by ring,bal,mul_zero]))
  by_cases h : (v e).natAbs=(v f).natAbs
  · have he : |v e|=|v f| := by simpa only [Int.natCast_natAbs] using congrArg (fun k : ℕ => (k : ℤ)) h
    rcases abs_eq_abs.mp he with he | he
    · have hp := pair (-1) 1 (by rw [he]; ring) (by simpa using (le_max_left 2 (2*Q-1)))
      have hs : z^(edgeGap b f-edgeGap b e)=w^(edgeGap b f-edgeGap b e) := by
        simpa only [neg_one_mul,one_mul,show -edgeGap b e+edgeGap b f=edgeGap b f-edgeGap b e by ring] using hp
      have hm : minorColumn v (edgeGap b) (e,f)=v e*(edgeGap b f-edgeGap b e) := by
        unfold minorColumn
        rw [he]
        ring
      rw [hm]
      exact phase_multiple hs _
    · have hp := pair 1 1 (by rw [he]; ring) (by simpa using (le_max_left 2 (2*Q-1)))
      have hs : z^(edgeGap b e+edgeGap b f)=w^(edgeGap b e+edgeGap b f) := by
        simpa only [one_mul] using hp
      have hm : minorColumn v (edgeGap b) (e,f)=v e*(edgeGap b e+edgeGap b f) := by
        unfold minorColumn
        rw [he]
        ring
      rw [hm]
      exact phase_multiple hs _
  · have hcost : (-(v f)).natAbs+(v e).natAbs≤max 2 (2*Q-1) := by
      rw [Int.natAbs_neg]
      have := hQ e
      have := hQ f
      omega
    have hp := pair (-(v f)) (v e) (by ring) hcost
    have he : -v f*edgeGap b e+v e*edgeGap b f=minorColumn v (edgeGap b) (e,f) := by
      unfold minorColumn
      ring
    simpa only [he] using hp

/-- A bound for all copy counts, uniform in the number of states and
the second family of phase labels. -/
theorem finite_determination (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian)
    (z w : Circle) (Q : ℕ)
    (hQ : ∀ e : Edge A, (edgeGap q e / content (edgeGap q (A:=A))).natAbs≤Q) :
    (∀ n≤max 2 (2*Q-1), observe q (twist b z A) n=observe q (twist b w A) n) ↔
      ∀ n, observe q (twist b z A) n=observe q (twist b w A) n := by
  refine ⟨fun h n => ?_,fun h n _ => h n⟩
  have tested (k : ℕ) (hk : k≤max 2 (2*Q-1)) := (indistinguishable_iff q b A k z w).1 (h k hk)
  apply (indistinguishable_iff q b A n z w).2
  intro d hd
  have hv : d∈vertical (edgeGap q (A:=A)) (edgeGap b) := (some_copy_iff q b ha d).1 ⟨n,hd⟩
  by_cases hz : edgeGap q (A:=A)=0
  · have one (e : Edge A) : z^(edgeGap b e)=w^(edgeGap b e) := by
      have hc : edgeGap q e=0 := congrFun hz e
      have hf := pair_frequency q b ha e e 1 0 (by simp [hc])
      have he : edgeGap b e∈frequencies q b A 1 := by simpa using hf
      exact tested 1 (by omega) _ he
    obtain ⟨c,_,rfl⟩ := hv
    change z^(∑ e, c e*edgeGap b e)=w^(∑ e, c e*edgeGap b e)
    simp only [product_character,one]
  · let v (e : Edge A) := edgeGap q e / content (edgeGap q (A:=A))
    have hw : edgeGap q (A:=A)=content (edgeGap q (A:=A)) • v := by
      funext e
      exact (Int.mul_ediv_cancel' (gcd_dvd (mem_univ e) : content (edgeGap q (A:=A))∣edgeGap q e)).symm
    obtain ⟨c,rfl⟩ := (normalized_minors_generate _ _ hz v hw d).1 hv
    change z^(∑ i, c i*minorColumn v (edgeGap b) i)=w^(∑ i, c i*minorColumn v (edgeGap b) i)
    rw [product_character,product_character]
    apply prod_congr rfl
    rintro ⟨e,f⟩ _
    rw [minor_test q b ha z w v _ hw Q hQ tested]

/-- With a nonzero diagonal entry all shorter balanced words can be
padded. One observation at the universal bound therefore suffices. -/
theorem single_observation (q b : ι → ℤ) {A : Matrix ι ι ℂ} (ha : A.IsHermitian)
    (i : ι) (hi : A i i≠0) (z w : Circle) (Q : ℕ)
    (hQ : ∀ e : Edge A, (edgeGap q e / content (edgeGap q (A:=A))).natAbs≤Q) :
    let N := max 2 (2*Q-1)
    observe q (twist b z A) N=observe q (twist b w A) N ↔
      ∀ n, observe q (twist b z A) n=observe q (twist b w A) n := by
  intro N
  constructor
  · intro h
    apply (finite_determination q b ha z w Q hQ).1
    have hm : Monotone (frequencies q b A) :=
      monotone_nat_of_le_succ fun k => frequencies_mono q b A i hi k
    intro n hn
    apply (indistinguishable_iff q b A n z w).2
    exact fun d hd => (indistinguishable_iff q b A N z w).1 h d (hm hn hd)
  · exact fun h => h N

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.finite_determination
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.single_observation
