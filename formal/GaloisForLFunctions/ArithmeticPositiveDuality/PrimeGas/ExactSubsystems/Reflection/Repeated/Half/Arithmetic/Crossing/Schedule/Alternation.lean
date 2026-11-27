import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Schedule.Primes

/-! # Several distinct irrational blind temperatures on the same prime packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule

open Finset Real Set

variable {q n : ℕ}

private theorem opposite {b c d : ℝ} (hc : 0<b*c) (hd : 0<(-b)*d) : c*d<0 := by
  rw [neg_mul,neg_pos] at hd
  rcases mul_pos_iff.mp hc with ⟨bp,cp⟩ | ⟨bn,cn⟩
  · exact mul_neg_of_pos_of_neg cp ((mul_neg_iff.mp hd).resolve_right (fun h => bp.not_gt h.1)).2
  · exact mul_neg_of_neg_of_pos cn ((mul_neg_iff.mp hd).resolve_left (fun h => bn.not_gt h.1)).2

private theorem in_gap {S : Finset Nat.Primes} {a b : ℝ} (ab : a≤b)
    (h : reading S a*reading S b<0) : ∃ t ∈ Ioo a b, Coincides (elementary (S := S)) t := by
  have cont : Continuous (reading S) := by unfold reading oddTrace oddTerm; fun_prop
  have image : (0 : ℝ) ∈ reading S '' Icc a b := by
    rcases mul_neg_iff.mp h with ⟨p,m⟩ | ⟨m,p⟩
    · exact intermediate_value_Icc' ab cont.continuousOn ⟨m.le,p.le⟩
    · exact intermediate_value_Icc ab cont.continuousOn ⟨m.le,p.le⟩
  obtain ⟨t,ht,hit⟩ := image
  have left : t≠a := by rintro rfl; rw [hit,zero_mul] at h; exact (lt_irrefl _ h)
  have right : t≠b := by rintro rfl; rw [hit,mul_zero] at h; exact (lt_irrefl _ h)
  exact ⟨t,⟨lt_of_le_of_ne ht.1 left.symm,lt_of_le_of_ne ht.2 right⟩,(reading_zero S t).mp hit⟩

/-- Every interval between successive positive probes can contain its own blind
temperature on the same prime packet, up to a common arbitrary magnification. -/
theorem alternating_gaps (dim : 2*(q+1)+1≤n) (t : Fin (q+1) ↪o Ioi (0 : ℝ)) (M : ℕ) (A : ℝ) :
    ∃ (S : Finset Nat.Primes) (K : ℝ), S.card=n ∧ (∀ p ∈ S, M<p.val) ∧ 0<K ∧ A<K ∧
      ∀ i : Fin q, ∃ z ∈ Ioo ((t i.castSucc).val/K) ((t i.succ).val/K),
        Irrational z ∧ Coincides (elementary (S := S)) z := by
  let b := fun i : Fin (q+1) => (-1 : ℝ)^i.val
  obtain ⟨S,K,size,above,pos,large,pattern⟩ := signs_on_primes dim t b
    (fun i => pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) M A
  refine ⟨S,K,size,above,pos,large,fun i => ?_⟩
  have eq : b i.succ = -b i.castSucc := by simp only [b,Fin.val_succ,Fin.val_castSucc,pow_succ,mul_neg_one]
  have hi := pattern i.succ
  rw [eq] at hi
  have order : (t i.castSucc).val < (t i.succ).val := t.strictMono (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  obtain ⟨z,hz,hit⟩ := in_gap ((div_lt_div_iff_of_pos_right pos).mpr order).le (opposite (pattern i.castSucc) hi)
  have hzpos := (div_pos (t i.castSucc).property pos).trans hz.1
  exact ⟨z,hz,irrational_of_crossing (by omega) hzpos.ne' hit,hit⟩

/-- For \(N\ge 2q+3\) a single packet of \(N\) distinct primes can have at least
\(q\) distinct irrational blind temperatures in any prescribed interval \((0,\varepsilon)\). -/
theorem many_crossings (n q M : ℕ) (dim : 2*q+3≤n) {ε : ℝ} (hε : 0<ε) :
    ∃ (S : Finset Nat.Primes) (Z : Finset ℝ), S.card=n ∧ (∀ p ∈ S, M<p.val) ∧ Z.card=q ∧
      ∀ z ∈ Z, z ∈ Ioo (0 : ℝ) ε ∧ Irrational z ∧ Coincides (elementary (S := S)) z := by
  classical
  let t : Fin (q+1) ↪o Ioi (0 : ℝ) := OrderEmbedding.ofStrictMono
    (fun i : Fin (q+1) => (⟨(i.val : ℝ)+1,show (0 : ℝ) < _ by positivity⟩ : Ioi (0 : ℝ))) (by
      intro i j lt
      change (i.val : ℝ)+1 < (j.val : ℝ)+1
      have h : (i.val : ℝ)<(j.val : ℝ) := Nat.cast_lt.mpr (show i.val<j.val from lt)
      linarith only [h])
  obtain ⟨S,K,size,above,pos,large,all⟩ := alternating_gaps (by omega : 2*(q+1)+1≤n) t M ((t (Fin.last q)).val/ε)
  choose z between irr hit using all
  have mono : StrictMono z := by
    intro i j h
    have ordered : (t i.succ).val ≤ (t j.castSucc).val := t.monotone (show i.succ ≤ j.castSucc from h)
    exact (between i).2.trans_le ((div_le_div_iff_of_pos_right pos).mpr ordered) |>.trans (between j).1
  refine ⟨S,univ.image z,size,above,by rw [card_image_of_injective _ mono.injective,card_univ,Fintype.card_fin],?_⟩
  intro w hw
  obtain ⟨i,_,rfl⟩ := mem_image.mp hw
  have low := (div_pos (t i.castSucc).property pos).trans (between i).1
  have top : (t i.succ).val ≤ (t (Fin.last q)).val := t.monotone (Fin.le_last _)
  have cap : (t (Fin.last q)).val/K < ε := (div_lt_iff₀ pos).mpr (by rw [mul_comm]; exact (div_lt_iff₀ hε).mp large)
  exact ⟨⟨low,((between i).2.trans_le ((div_le_div_iff_of_pos_right pos).mpr top)).trans cap⟩,irr i,hit i⟩

#print axioms alternating_gaps
#print axioms many_crossings

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Schedule
