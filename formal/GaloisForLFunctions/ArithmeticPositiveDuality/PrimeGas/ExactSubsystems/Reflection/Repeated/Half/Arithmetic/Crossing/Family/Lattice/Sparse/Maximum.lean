import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Grid
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Upper.Reflection

/-! # Sharp count of transcendental crossings on one prime frequency -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse

open Finset Real Set

private theorem gap {f : ℝ → ℝ} (cont : Continuous f) {a b : ℝ} (ab : a ≤ b) (cross : f a*f b<0) :
    ∃ t ∈ Ioo a b, f t=0 := by
  have image : (0 : ℝ) ∈ f '' Icc a b := by
    rcases mul_neg_iff.mp cross with ⟨p,m⟩ | ⟨m,p⟩
    · exact intermediate_value_Icc' ab cont.continuousOn ⟨m.le,p.le⟩
    · exact intermediate_value_Icc ab cont.continuousOn ⟨m.le,p.le⟩
  obtain ⟨t,ht,hit⟩ := image
  have left : t≠a := by rintro rfl; rw [hit,zero_mul] at cross; exact lt_irrefl _ cross
  have right : t≠b := by rintro rfl; rw [hit,mul_zero] at cross; exact lt_irrefl _ cross
  exact ⟨t,⟨lt_of_le_of_ne ht.1 left.symm,lt_of_le_of_ne ht.2 right⟩,hit⟩

private theorem opposite {b x y : ℝ} (hx : 0<b*x) (hy : 0<(-b)*y) : x*y<0 := by
  rw [neg_mul,neg_pos] at hy
  rcases mul_pos_iff.mp hx with ⟨bp,xp⟩ | ⟨bn,xn⟩
  · exact mul_neg_of_pos_of_neg xp ((mul_neg_iff.mp hy).resolve_right (fun h => bp.not_gt h.1)).2
  · exact mul_neg_of_neg_of_pos xn ((mul_neg_iff.mp hy).resolve_left (fun h => bn.not_gt h.1)).2

/-- On a fixed simple asymmetric spectrum the reflected zero bound counts
every positive blind temperature. -/
theorem power_bound {n : ℕ} (p : Nat.Primes) (k : Fin n ↪ ℕ) (asym : ¬Reflects (primeModes p k))
    (Z : Finset ℝ) (hit : ∀ t ∈ Z, 0<t ∧ agrees (primeModes p k) t) : 2*Z.card+3 ≤ n := by
  cases n with
  | zero => exact (asym ⟨0,Equiv.refl _,fun i => Fin.elim0 i⟩).elim
  | succ n =>
    let e := Tuple.sort (fun i => k i)
    let E := primeModes p k
    let A := centered E ∘ e
    have mono : StrictMono (k ∘ e) :=
      (Tuple.monotone_sort (fun i => k i)).strictMono_of_injective (k.injective.comp e.injective)
    have pos := log_pos (Nat.one_lt_cast.mpr p.property.one_lt)
    have increasing : StrictMono A := by
      intro i j h
      change primeModes p k (e i)-_ < primeModes p k (e j)-_
      rw [mode_grid]
      simp only [add_zero,levels]
      exact sub_lt_sub_right (mul_lt_mul_of_pos_left (Nat.cast_lt.mpr (mono h)) pos) _
    have mean : (∑ i, A i)=0 := (Equiv.sum_comp e (centered E)).trans (sum_centered E)
    have read (t : ℝ) : oddTrace A t=oddTrace (centered E) t :=
      Equiv.sum_comp e (fun i => oddTerm t (centered E i))
    have detected : oddTrace A 1≠0 := by
      intro zero
      rw [read] at zero
      have cap (j : ℕ) := (simple_multiplicity k.injective j).trans_lt p.property.one_lt
      have law := (algebraic_reading p k cap 1 (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ))).mp
        ((agrees_odd E 1).mpr zero)
      exact asym (law.resolve_left one_ne_zero)
    have bound := Upper.reflected_bound A increasing mean detected Z (fun t ht =>
      ⟨(hit t ht).1,(read t).trans ((agrees_odd E t).mp (hit t ht).2)⟩)
    omega

/-- Arbitrarily high distinct occupations of a fixed prime realize as many
positive transcendental blind temperatures as the reflected zero bound permits. -/
theorem attainable_iff (p : Nat.Primes) (n q M : ℕ) {ε : ℝ} (hε : 0<ε) :
    (∃ (k : Fin n ↪ ℕ) (Z : Finset ℝ), (∀ i, M<k i) ∧ ¬Reflects (primeModes p k) ∧ Z.card=q ∧
      ∀ z ∈ Z, z ∈ Ioo (0 : ℝ) ε ∧ Transcendental ℚ z ∧ agrees (primeModes p k) z) ↔
      2*q+3≤n := by
  classical
  constructor
  · rintro ⟨k,Z,_,asym,size,hit⟩
    rw [← size]
    exact power_bound p k asym Z (fun z hz => ⟨(hit z hz).1.1,(hit z hz).2.2⟩)
  · intro dim
    let t : Fin (q+1) ↪o Ioi (0 : ℝ) := OrderEmbedding.ofStrictMono
      (fun i : Fin (q+1) => (⟨(i.val : ℝ)+1,show (0 : ℝ)<_ by positivity⟩ : Ioi (0 : ℝ))) (by
        intro i j h
        change (i.val : ℝ)+1<(j.val : ℝ)+1
        have lt : (i.val : ℝ)<(j.val : ℝ) := Nat.cast_lt.mpr (show i.val<j.val from h)
        linarith only [lt])
    let b (i : Fin (q+1)) := (-1 : ℝ)^i.val
    obtain ⟨k,K,above,pos,large,pattern⟩ := signs_on_powers p (by omega : 2*(q+1)+1 ≤ n) t b
      (fun i => pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) M ((t (Fin.last q)).val/ε)
    let E := primeModes p k
    let f := oddTrace (centered E)
    have cont : Continuous f := by unfold f oddTrace oddTerm; fun_prop
    have asym : ¬Reflects E := by
      intro symm
      have blind := (agrees_odd E _).mp (reflection_agrees symm ((t 0).val/K))
      have h := pattern 0
      change 0<b 0*oddTrace (centered E) _ at h
      rw [blind,mul_zero] at h
      exact lt_irrefl _ h
    have gaps (i : Fin q) : ∃ z ∈ Ioo ((t i.castSucc).val/K) ((t i.succ).val/K), f z=0 := by
      have next := pattern i.succ
      rw [show b i.succ= -b i.castSucc by simp only [b,Fin.val_succ,Fin.val_castSucc,pow_succ,mul_neg_one]] at next
      have order : (t i.castSucc).val ≤ (t i.succ).val := t.monotone (Fin.castSucc_le_succ i)
      exact gap cont ((div_le_div_iff_of_pos_right pos).mpr order) (opposite (pattern i.castSucc) next)
    choose z window zero using gaps
    have mono : StrictMono z := by
      intro i j h
      have ordered : (t i.succ).val ≤ (t j.castSucc).val := t.monotone (show i.succ ≤ j.castSucc from h)
      exact ((window i).2.trans_le ((div_le_div_iff_of_pos_right pos).mpr ordered)).trans (window j).1
    refine ⟨k,univ.image z,above,asym,by rw [Finset.card_image_of_injective _ mono.injective,card_univ,Fintype.card_fin],?_⟩
    intro w hw
    obtain ⟨i,_,rfl⟩ := mem_image.mp hw
    have low := (div_pos (t i.castSucc).property pos).trans (window i).1
    have upper : (t i.succ).val ≤ (t (Fin.last q)).val := t.monotone (Fin.le_last _)
    have top : (t (Fin.last q)).val/K < ε := (div_lt_iff₀ pos).mpr (by rw [mul_comm]; exact (div_lt_iff₀ hε).mp large)
    have pass := (agrees_odd E _).mpr (zero i)
    refine ⟨⟨low,((window i).2.trans_le ((div_le_div_iff_of_pos_right pos).mpr upper)).trans top⟩,?_,pass⟩
    intro alg
    have cap (j : ℕ) := (simple_multiplicity k.injective j).trans_lt p.property.one_lt
    exact asym (((algebraic_reading p k cap _ alg).mp pass).resolve_left low.ne')

#print axioms power_bound
#print axioms attainable_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse
