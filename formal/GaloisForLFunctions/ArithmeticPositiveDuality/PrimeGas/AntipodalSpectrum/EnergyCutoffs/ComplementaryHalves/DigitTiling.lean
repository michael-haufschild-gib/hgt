import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedDigits

/-!
# Complementary positions of the balanced radix digits

Removing one base-C digit of X + C Y exchanges the roles of the
two balanced labels. This identifies the two-copy basis with ℕ.
-/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

abbrev Radix := {C : ℕ // 1 < C}
abbrev Half (C : Radix) := {x : ℕ // ∀ d ∈ (C.val^2).digits x, d < C.val}

private theorem square_gt (C : Radix) : 1 < C.val^2 := one_lt_pow₀ C.property (by norm_num)

private theorem base_le (C : Radix) : C.val ≤ C.val^2 := by
  rw [pow_two]
  exact Nat.le_mul_of_pos_right _ (zero_lt_one.trans C.property)

def origin (C : Radix) : Half C := ⟨0,by simp⟩

private theorem components (C : Radix) (x : Half C) :
    x.val%(C.val^2) < C.val ∧ ∀ d ∈ (C.val^2).digits (x.val/(C.val^2)), d < C.val := by
  by_cases hz : x.val = 0
  · simp [hz,zero_lt_one.trans C.property]
  · have h := x.property
    rw [Nat.digits_def' (square_gt C) (Nat.pos_of_ne_zero hz),List.forall_mem_cons] at h
    exact h

private def low (C : Radix) (x : Half C) : Fin C.val := ⟨_,(components C x).1⟩

private def drop (C : Radix) (x : Half C) : Half C := ⟨_,(components C x).2⟩

private def prepend (C : Radix) (d : Fin C.val) (x : Half C) : Half C := by
  refine ⟨d.val+C.val^2*x.val,?_⟩
  by_cases hz : d.val+C.val^2*x.val = 0
  · simp [hz]
  · have hd := d.isLt.trans_le (base_le C)
    rw [Nat.digits_def' (square_gt C) (Nat.pos_of_ne_zero hz),Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hd,Nat.add_mul_div_left _ _ (zero_lt_one.trans (square_gt C)),Nat.div_eq_of_lt hd,zero_add]
    exact List.forall_mem_cons.mpr ⟨d.isLt,x.property⟩

/-- Every single digit, including zero, is a balanced label. -/
def single (C : Radix) (d : Fin C.val) : Half C := prepend C d (origin C)

theorem single_val (C : Radix) (d : Fin C.val) : (single C d).val = d.val := by
  change d.val+C.val^2*0 = d.val
  simp

/-- The first omitted label is the radix. -/
theorem excludes_radix (C : Radix) (x : Half C) : x.val ≠ C.val := by
  intro he
  have h := (components C x).1
  have hc : C.val < C.val^2 := by
    rw [pow_two]
    simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left C.property (zero_lt_one.trans C.property)
  rw [he,Nat.mod_eq_of_lt hc] at h
  exact h.false

/-- Uniformly available large labels, obtained by appending a high nonzero digit. -/
theorem exists_large (C : Radix) (N : ℕ) : ∃ x : Half C, N < x.val := by
  let n := (C.val+1)*(N+1)
  let x := stretchEquiv C n
  refine ⟨x,?_⟩
  have h := (stretch_quadratic_bounds C n).1
  have hn : n ≤ n*(n+2) := Nat.le_mul_of_pos_right n (by omega)
  change N < stretchDigits C.val n
  by_contra! hle
  have h' := hn.trans (h.trans (Nat.mul_le_mul_left (C.val+1) hle))
  change (C.val+1)*(N+1) ≤ (C.val+1)*N at h'
  rw [Nat.mul_succ] at h'
  omega

def label (C : Radix) (p : Half C × Half C) := p.1.val+C.val*p.2.val

private def step (C : Radix) (d : Fin C.val) (p : Half C × Half C) : Half C × Half C :=
  (prepend C d p.2,p.1)

private def rest (C : Radix) (p : Half C × Half C) : Half C × Half C := (p.2,drop C p.1)

private theorem label_step (C : Radix) (d : Fin C.val) (p : Half C × Half C) :
    label C (step C d p) = d.val+C.val*label C p := by
  change (d.val+C.val^2*p.2.val)+C.val*p.1.val = d.val+C.val*(p.1.val+C.val*p.2.val)
  ring

private theorem restore (C : Radix) (p : Half C × Half C) : step C (low C p.1) (rest C p) = p := by
  apply Prod.ext
  · exact Subtype.ext (Nat.mod_add_div p.1.val (C.val^2))
  · rfl

private theorem label_parts (C : Radix) (p : Half C × Half C) :
    label C p % C.val = (low C p.1).val ∧ label C p / C.val = label C (rest C p) := by
  have he := label_step C (low C p.1) (rest C p)
  rw [restore] at he
  rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (low C p.1).isLt,
    Nat.add_mul_div_left _ _ (zero_lt_one.trans C.property),Nat.div_eq_of_lt (low C p.1).isLt,zero_add]
  exact ⟨rfl,rfl⟩

theorem unique_pair (C : Radix) (n : ℕ) : ∃! p, label C p = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨(origin C,origin C),by simp [label,origin],?_⟩
      intro p hp
      obtain ⟨hx,hy⟩ := Nat.add_eq_zero_iff.mp hp
      have hy' : p.2.val = 0 := (Nat.mul_eq_zero.mp hy).resolve_left (zero_lt_one.trans C.property).ne'
      exact Prod.ext (Subtype.ext hx) (Subtype.ext hy')
    · let d : Fin C.val := ⟨n%C.val,Nat.mod_lt _ (zero_lt_one.trans C.property)⟩
      obtain ⟨p,hp,hu⟩ := ih (n/C.val) (Nat.div_lt_self hn C.property)
      refine ⟨step C d p,?_,?_⟩
      · change label C (step C d p) = n
        rw [label_step,hp]
        exact Nat.mod_add_div n C.val
      · intro q hq
        obtain ⟨hm,hd⟩ := label_parts C q
        rw [hq] at hm hd
        have hlow : low C q.1 = d := Fin.ext hm.symm
        exact (restore C q).symm.trans (congrArg₂ (step C) hlow (hu _ hd.symm))

/-- Two balanced copies, offset by one base-C digit, enumerate all integer labels. -/
noncomputable def interleave (C : Radix) : Half C × Half C ≃ ℕ :=
  Equiv.ofBijective (label C) ⟨fun _ q h => (unique_pair C (label C q)).unique h rfl,
    fun n => (unique_pair C n).exists⟩

theorem interleave_apply (C : Radix) (p : Half C × Half C) : interleave C p = p.1.val+C.val*p.2.val := rfl

#print axioms interleave
#print axioms unique_pair

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
