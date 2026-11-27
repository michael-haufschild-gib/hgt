import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Gibbs
import GaloisForLFunctions.HTGeometry.HyperbolicSineScaleMonotonicity

/-! # Two-level sign tests depend only on multiplicities at positive temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell

open Finset Real

/-- Two distinct levels with arbitrary degeneracies. -/
def twoLevels (m n : ℕ) (a b : ℝ) : Fin m ⊕ Fin n → ℝ := Sum.elim (fun _ => a) (fun _ => b)

private theorem binary_response {m n : ℕ} (hm : 0 < m) (a b t : ℝ) :
    let z := (b-a)/((m : ℝ)+n)
    oddTrace (centered (twoLevels m n a b)) t=
      2*((n : ℝ)*sinh ((m : ℝ)*(t*z))-(m : ℝ)*sinh ((n : ℝ)*(t*z))) := by
  let z := (b-a)/((m : ℝ)+n)
  let D := twoLevels m n (-(n : ℝ)) m
  have hn : (m : ℝ)+(n : ℝ) ≠ 0 := (add_pos_of_pos_of_nonneg (Nat.cast_pos.mpr hm) (Nat.cast_nonneg n)).ne'
  have mean : (∑ i, D i)=0 := by
    simp only [D,twoLevels,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    ring
  have eq : twoLevels m n a b=fun i => z*D i+(a+z*n) := by
    funext i
    cases i with
    | inl i => change a=z*(-(n : ℝ))+(a+z*n); ring
    | inr i =>
      change b=z*(m : ℝ)+(a+z*n)
      rw [show z*(m : ℝ)+(a+z*n)=z*((m : ℝ)+n)+a by ring,div_mul_cancel₀ _ hn]
      ring
  rw [eq,centered_affine,centered_eq_of_sum_zero mean]
  have odd (s : ℝ) : oddTerm t (z*s)=2*sinh (s*(t*z)) := by
    rw [oddTerm,sinh_eq,show t*(z*s)=s*(t*z) by ring,neg_mul,show t*(z*s)=s*(t*z) by ring]
    ring
  simp only [oddTrace,odd,D,twoLevels,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,neg_mul,sinh_neg]
  change _=2*((n : ℝ)*sinh ((m : ℝ)*(t*z))-(m : ℝ)*sinh ((n : ℝ)*(t*z)))
  ring

private theorem weighted_sinh {r s x : ℝ} (rp : 0<r) (rs : r<s) (xp : 0<x) :
    s*sinh (r*x)<r*sinh (s*x) := by
  have a := mul_pos rp xp
  have b := mul_pos (rp.trans rs) xp
  have mono := _root_.HTGeometry.strictMonoOn_sinh_div_self a b (mul_lt_mul_of_pos_right rs xp)
  have cross := (div_lt_div_iff₀ a b).mp mono
  apply (mul_lt_mul_iff_left₀ xp).mp
  calc (s*sinh (r*x))*x = sinh (r*x)*(s*x) := by ring
       _ < sinh (s*x)*(r*x) := cross
       _ = (r*sinh (s*x))*x := by ring

/-- At positive temperature the ordering of the two centered partition
functions depends solely on which level has greater multiplicity. -/
theorem two_level_sign (m n : ℕ) (hm : 0 < m) (hn : 0<n) {a b t : ℝ}
    (gap : a<b) (ht : 0<t) : 0<oddTrace (centered (twoLevels m n a b)) t ↔ n < m := by
  rw [binary_response hm]
  let x := t*((b-a)/((m : ℝ)+n))
  have mp : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have np : 0<(n : ℝ) := Nat.cast_pos.mpr hn
  have xp : 0<x := mul_pos ht (div_pos (sub_pos.mpr gap) (add_pos mp np))
  change 0<2*((n : ℝ)*sinh ((m : ℝ)*x)-(m : ℝ)*sinh ((n : ℝ)*x)) ↔ n < m
  rw [mul_pos_iff_of_pos_left zero_lt_two,sub_pos]
  rcases lt_trichotomy n m with lt | eq | gt
  · exact iff_of_true (weighted_sinh np (Nat.cast_lt.mpr lt) xp) lt
  · subst m; simp only [lt_irrefl]
  · exact iff_of_false (weighted_sinh mp (Nat.cast_lt.mpr gt) xp).asymm gt.asymm

theorem two_level_indistinguishable (m n : ℕ) (hm : 0 < m) (hn : 0<n) {a b t u : ℝ}
    (gap : a<b) (ht : 0<t) (hu : 0<u) :
    0<oddTrace (centered (twoLevels m n a b)) t ↔ 0<oddTrace (centered (twoLevels m n a b)) u :=
  (two_level_sign m n hm hn gap ht).trans (two_level_sign m n hm hn gap hu).symm

/-- When the lower energy has more copies, a single signed comparison detects
the side of zero damping; equality detects zero itself. -/
theorem two_level_orientation (m n : ℕ) (hn : 0<n) (more : n < m) {a b : ℝ} (gap : a<b) (t : ℝ) :
    let r := oddTrace (centered (twoLevels m n a b)) t
    (0<r ↔ 0<t) ∧ (r=0 ↔ t=0) := by
  let E := centered (twoLevels m n a b)
  change (0<oddTrace E t ↔ 0<t) ∧ (oddTrace E t=0 ↔ t=0)
  have positive {v : ℝ} (vpos : 0<v) : 0<oddTrace E v :=
    (two_level_sign m n (hn.trans more) hn gap vpos).mpr more
  rcases lt_trichotomy t 0 with neg | zero | pos
  · have h := positive (neg_pos.mpr neg)
    have flip : oddTrace E (-t)= -oddTrace E t := by
      simp only [oddTrace,oddTerm,neg_neg,← sum_neg_distrib,neg_sub]
    rw [flip,neg_pos] at h
    exact ⟨iff_of_false h.asymm neg.asymm,iff_of_false h.ne neg.ne⟩
  · subst t
    simp only [odd_zero,lt_irrefl,iff_self,eq_self,and_self]
  · exact ⟨iff_of_true (positive pos) pos,iff_of_false (positive pos).ne' pos.ne'⟩

/-- Reindexing by the two level sets covers every finite spectrum with
at most two distinct energies, including constant and empty spectra. -/
theorem binary_alphabet {I : Type*} [Fintype I] (E : I → ℝ) {a b t u : ℝ} (gap : a<b)
    (alphabet : ∀ i, E i=a ∨ E i=b) (ht : 0<t) (hu : 0<u) :
    0<oddTrace (centered E) t ↔ 0<oddTrace (centered E) u := by
  classical
  have flat (c : ℝ) (h : ∀ i, E i=c) : ∀ v, oddTrace (centered E) v=0 := by
    intro v
    apply (agrees_odd E v).mp
    apply reflection_agrees
    exact ⟨c+c,Equiv.refl _,fun i => by simp only [Equiv.refl_apply,h]⟩
  by_cases ha : ∃ i, E i=a
  · by_cases hb : ∃ i, E i=b
    · let L := {i : I // E i=a}
      let H := {i : I // E i ≠ a}
      obtain ⟨i,hi⟩ := ha
      obtain ⟨j,hj⟩ := hb
      letI : Nonempty L := ⟨⟨i,hi⟩⟩
      letI : Nonempty H := ⟨⟨j,by rw [hj]; exact gap.ne'⟩⟩
      let l := (Fintype.equivFin L).symm
      let r := (Fintype.equivFin H).symm
      let e := (Equiv.sumCongr l r).trans (Equiv.sumCompl (fun i : I => E i=a))
      let D := twoLevels (Fintype.card L) (Fintype.card H) a b
      have eq : D=E ∘ e := by
        funext k
        cases k with
        | inl k => exact (l k).property.symm
        | inr k => exact ((alphabet (r k).val).resolve_left (r k).property).symm
      have mean : meanEnergy D=meanEnergy E := by
        unfold meanEnergy
        simp only [eq,Function.comp_apply,Equiv.sum_comp e E,Fintype.card_congr e]
      have center (k) : centered D k=centered E (e k) := by
        rw [centered,centered,mean,eq]; rfl
      have trace (v : ℝ) : oddTrace (centered D) v=oddTrace (centered E) v := by
        simp only [oddTrace,center]
        exact Equiv.sum_comp e (fun k => oddTerm v (centered E k))
      rw [← trace t,← trace u]
      exact two_level_indistinguishable _ _ Fintype.card_pos Fintype.card_pos gap ht hu
    · have zero := flat a (fun i => (alphabet i).resolve_right (fun h => hb ⟨i,h⟩))
      rw [zero t,zero u]
  · have zero := flat b (fun i => (alphabet i).resolve_left (fun h => ha ⟨i,h⟩))
    rw [zero t,zero u]

#print axioms binary_alphabet
#print axioms two_level_orientation
#print axioms two_level_sign
#print axioms two_level_indistinguishable

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell
