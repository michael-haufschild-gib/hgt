import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Repetition

/-! # Blocks complementary to a strided occupation digit -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

/-- After removing a digit of length d and stride a, one keeps the first a positions of each block. -/
def blockStart (a d : ℕ+) (v : Fin a.val × ℕ) := v.1.val+(a.val*d.val)*v.2

/-- Euclidean division first at a, then at d isolates the chosen digit. -/
def strideEquiv (a d : ℕ+) : Fin d.val × (Fin a.val × ℕ) ≃ ℕ :=
  let swap : Fin d.val × (Fin a.val × ℕ) ≃ Fin a.val × (Fin d.val × ℕ) :=
    ⟨fun v => (v.2.1,v.1,v.2.2),fun v => (v.2.1,v.1,v.2.2),fun _ => rfl,fun _ => rfl⟩
  (swap.trans ((Equiv.refl _).prodCongr (radixEquiv d))).trans (radixEquiv a)

theorem strideEquiv_apply (a d : ℕ+) (v : Fin d.val × (Fin a.val × ℕ)) :
    strideEquiv a d v = a.val*v.1.val+blockStart a d v.2 := by
  change v.2.1.val+a.val*(v.1.val+d.val*v.2.2) = _
  unfold blockStart
  ring

/-- An entire run of a consecutive starts fits in the complement only at a block boundary. -/
theorem full_run_iff (a d : ℕ+) (hd : 1 < d.val) (b : ℕ) :
    (∀ r : Fin a.val, b+r.val ∈ Set.range (blockStart a d)) ↔ a.val*d.val ∣ b := by
  let D := a.val*d.val
  have ha : a.val < D := by
    simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hd a.pos
  have hm (v : Fin a.val × ℕ) : blockStart a d v % D = v.1.val := by
    change (v.1.val+D*v.2) % D = _
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (v.1.isLt.trans ha)]
  constructor
  · intro h
    obtain ⟨v,hv⟩ := h ⟨0,a.pos⟩
    change blockStart a d v = b+0 at hv
    rw [Nat.add_zero] at hv
    by_cases hz : v.1.val = 0
    · refine ⟨v.2,?_⟩
      simpa only [blockStart,hz,Nat.zero_add] using hv.symm
    · let r : Fin a.val := ⟨a.val-v.1.val,by have := a.pos; omega⟩
      obtain ⟨w,hw⟩ := h r
      have hs : b+r.val = a.val+D*v.2 := by
        rw [← hv]
        change v.1.val+D*v.2+(a.val-v.1.val) = _
        have := v.1.isLt
        omega
      have he := congrArg (· % D) (hw.trans hs)
      rw [hm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha] at he
      exact False.elim (w.1.isLt.ne he)
  · rintro ⟨k,rfl⟩ r
    exact ⟨(r,k),Nat.add_comm _ _⟩

#print axioms strideEquiv_apply
#print axioms full_run_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
