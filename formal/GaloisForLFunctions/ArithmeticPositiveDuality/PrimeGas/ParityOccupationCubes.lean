import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PrimeParityPartition

/-!
# Boolean cubes in the two-copy prime gas

Dividing each second-copy occupation by two leaves a remainder bit. Moving
that bit between copies preserves the total energy and reverses the grading.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

abbrev Occupation := Nat.Primes →₀ ℕ

private def bitOccupation (S : Finset Nat.Primes) : Occupation :=
  Finsupp.indicator S (fun _ _ => 1)

private theorem bit_at (S : Finset Nat.Primes) (p : Nat.Primes) :
    bitOccupation S p = if p ∈ S then 1 else 0 := by
  simp only [bitOccupation, Finsupp.indicator_apply, dite_eq_ite]

private def oddModes (b : Occupation) := b.support.filter (fun p => b p % 2 = 1)

private theorem mem_odd (b : Occupation) (p : Nat.Primes) :
    p ∈ oddModes b ↔ b p % 2 = 1 := by
  rw [oddModes, Finset.mem_filter, Finsupp.mem_support_iff]
  exact ⟨And.right, fun h => ⟨by intro hz; simp [hz] at h, h⟩⟩

private theorem bit_odd (b : Occupation) (p : Nat.Primes) :
    bitOccupation (oddModes b) p = b p % 2 := by
  rw [bit_at]
  by_cases h : p ∈ oddModes b
  · rw [if_pos h, (mem_odd b p).mp h]
  · rw [if_neg h]
    have hn := mt (mem_odd b p).mpr h
    omega

/-- A pair of occupations at fixed residual and paired occupations is a subset of the residual support. -/
@[ext] structure OccupationCube where
  residual : Occupation
  pairs : Occupation
  bits : Finset Nat.Primes
  allowed : bits ⊆ residual.support

private theorem bit_le (c : OccupationCube) (p : Nat.Primes) : bitOccupation c.bits p ≤ c.residual p := by
  rw [bit_at]
  by_cases h : p ∈ c.bits
  · exact (if_pos h).trans_le (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (c.allowed h)))
  · rw [if_neg h]; exact Nat.zero_le _

private def encodePair (x : Occupation × Occupation) : OccupationCube where
  residual := x.1 + bitOccupation (oddModes x.2)
  pairs := x.2.mapRange (· / 2) rfl
  bits := oddModes x.2
  allowed := by
    intro p hp
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, bit_at, if_pos hp]
    omega

private def decodePair (c : OccupationCube) : Occupation × Occupation :=
  (c.residual - bitOccupation c.bits, c.pairs + c.pairs + bitOccupation c.bits)

/-- The cube coordinates are a bijection of the full two-copy basis. -/
def occupationCubes : (Occupation × Occupation) ≃ OccupationCube where
  toFun := encodePair
  invFun := decodePair
  left_inv x := by
    apply Prod.ext <;> apply Finsupp.ext <;> intro p
    · simp only [decodePair, encodePair, Finsupp.tsub_apply, Finsupp.add_apply, Nat.add_sub_cancel]
    · simp only [decodePair, encodePair, Finsupp.add_apply, Finsupp.mapRange_apply, bit_odd]
      omega
  right_inv c := by
    have hb : oddModes (decodePair c).2 = c.bits := by
      ext p
      rw [mem_odd]
      simp only [decodePair, Finsupp.add_apply, bit_at]
      by_cases h : p ∈ c.bits <;> simp only [h, if_true, if_false, iff_true, iff_false] <;> omega
    apply OccupationCube.ext
    · apply Finsupp.ext
      intro p
      change (decodePair c).1 p + bitOccupation (oddModes (decodePair c).2) p = c.residual p
      rw [hb]
      exact Nat.sub_add_cancel (bit_le c p)
    · apply Finsupp.ext
      intro p
      change (c.pairs p + c.pairs p + bitOccupation c.bits p) / 2 = c.pairs p
      rw [bit_at]
      split <;> omega
    · exact hb

private theorem decode_total (c : OccupationCube) :
    (decodePair c).1 + (decodePair c).2 = c.residual + (c.pairs + c.pairs) := by
  apply Finsupp.ext
  intro p
  have h := bit_le c p
  simp only [decodePair, Finsupp.add_apply, Finsupp.tsub_apply]
  omega

private theorem label_zero : label 0 = 1 := by
  apply PNat.coe_injective
  change Finsupp.prod 0 (fun p : Nat.Primes => fun k : ℕ => (p : ℕ)^k) = 1
  exact Finsupp.prod_zero_index

private theorem bit_insert (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∉ S) :
    bitOccupation (insert p S) = Finsupp.single p 1 + bitOccupation S := by
  apply Finsupp.ext
  intro q
  by_cases he : p=q
  · subst q; simp [bit_at, hp]
  · simp [bit_at, ne_comm.mp he]

private theorem bit_sign (S : Finset Nat.Primes) :
    primeParity (label (bitOccupation S)) = (-1 : Circle)^S.card := by
  induction S using Finset.induction_on with
  | empty =>
    have hz : bitOccupation ∅ = 0 := by ext p; simp [bit_at]
    rw [hz, label_zero, map_one, Finset.card_empty, pow_zero]
  | @insert p S hp ih =>
    have hprime : label (Finsupp.single p 1) = (p : ℕ+) := PNat.coe_injective (label_one_quantum p)
    rw [bit_insert S p hp, label_add, map_mul, hprime, primeParity_prime, ih,
      Finset.card_insert_of_notMem hp, pow_succ, mul_comm]

private theorem decode_sign (c : OccupationCube) :
    primeParity (label (decodePair c).2) = (-1 : Circle)^c.bits.card := by
  change primeParity (label (c.pairs + c.pairs + bitOccupation c.bits)) = _
  rw [label_add, label_add, map_mul, map_mul, bit_sign]
  have hs (n : ℕ+) : primeParity n * primeParity n = 1 := by
    change (-1 : Circle)^_ * (-1 : Circle)^_ = 1
    rw [← sq, ← pow_mul, mul_comm, pow_mul]
    simp
  rw [hs, one_mul]

private def toggle (p : Nat.Primes) (S : Finset Nat.Primes) :=
  if p ∈ S then S.erase p else insert p S

private theorem toggle_twice (p : Nat.Primes) (S : Finset Nat.Primes) : toggle p (toggle p S) = S := by
  by_cases hp : p ∈ S
  · simp [toggle, hp]
  · simp [toggle, hp]

private theorem toggle_ne (p : Nat.Primes) (S : Finset Nat.Primes) : toggle p S ≠ S := by
  intro h
  have hi := Finset.ext_iff.mp h p
  by_cases hp : p ∈ S <;> simp [toggle,hp] at hi

private theorem toggle_sign (p : Nat.Primes) (S : Finset Nat.Primes) :
    (-1 : Circle)^(toggle p S).card = -((-1 : Circle)^S.card) := by
  by_cases h : p ∈ S
  · rw [toggle, if_pos h]
    conv_rhs => rw [← Finset.card_erase_add_one h, pow_succ]
    simp
  · rw [toggle, if_neg h, Finset.card_insert_of_notMem h, pow_succ]
    simp

private noncomputable def pivot (A : Occupation) (h : A.support.Nonempty) : Nat.Primes :=
  letI := LinearOrder.lift' (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective
  A.support.min' h

private theorem pivot_mem (A : Occupation) (h : A.support.Nonempty) : pivot A h ∈ A.support := by
  letI := LinearOrder.lift' (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective
  exact Finset.min'_mem _ _

private def flipCube (c : OccupationCube) : OccupationCube :=
  if h : c.residual.support.Nonempty then
    { c with bits := toggle (pivot _ h) c.bits
             allowed := by
               unfold toggle
               split
               · exact (Finset.erase_subset _ _).trans c.allowed
               · exact Finset.insert_subset (pivot_mem _ h) c.allowed }
  else c

private theorem flip_twice (c : OccupationCube) : flipCube (flipCube c) = c := by
  by_cases h : c.residual.support.Nonempty
  · simp only [flipCube, dif_pos h, toggle_twice]
  · simp only [flipCube, dif_neg h]

private theorem flip_fixed (c : OccupationCube) : flipCube c = c ↔ c.residual = 0 := by
  by_cases h : c.residual.support.Nonempty
  · have hn : c.residual ≠ 0 := by intro he; simp [he] at h
    rw [iff_false_intro hn, iff_false]
    exact fun he => toggle_ne (pivot _ h) c.bits (by simpa only [flipCube, dif_pos h] using congrArg OccupationCube.bits he)
  · have hz : c.residual = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    exact iff_of_true (dif_neg h) hz

/-- Cube coordinates on pairs of integer energy labels. -/
def pairCubes : (ℕ+ × ℕ+) ≃ OccupationCube :=
  (label.symm.prodCongr label.symm).trans occupationCubes

/-- Energy-preserving exchange of one parity bit between the two copies. -/
def parityPartner (x : ℕ+ × ℕ+) := pairCubes.symm (flipCube (pairCubes x))

theorem parityPartner_involutive : Function.Involutive parityPartner := by
  intro x
  simp only [parityPartner, Equiv.apply_symm_apply, flip_twice, Equiv.symm_apply_apply]

/-- Total occupation is constant throughout each Boolean cube. -/
theorem cube_product (c : OccupationCube) :
    (pairCubes.symm c).1 * (pairCubes.symm c).2 = label (c.residual + (c.pairs+c.pairs)) := by
  change label (decodePair c).1 * label (decodePair c).2 = _
  rw [← label_add, decode_total]

/-- Second-copy parity is the alternating grading by subset cardinality. -/
theorem cube_parity (c : OccupationCube) :
    primeParity (pairCubes.symm c).2 = (-1 : Circle)^c.bits.card := decode_sign c

theorem parityPartner_product (x : ℕ+ × ℕ+) :
    (parityPartner x).1 * (parityPartner x).2 = x.1 * x.2 := by
  obtain ⟨c,rfl⟩ := pairCubes.symm.surjective x
  simp only [parityPartner, Equiv.apply_symm_apply, cube_product]
  by_cases h : c.residual.support.Nonempty
  · rw [flipCube, dif_pos h]
  · rw [flipCube, dif_neg h]

theorem parityPartner_sign (x : ℕ+ × ℕ+) (hx : parityPartner x ≠ x) :
    primeParity (parityPartner x).2 = -(primeParity x.2) := by
  obtain ⟨c,rfl⟩ := pairCubes.symm.surjective x
  simp only [parityPartner, Equiv.apply_symm_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq] at hx ⊢
  change primeParity (label (decodePair (flipCube c)).2) = -primeParity (label (decodePair c).2)
  rw [decode_sign, decode_sign]
  by_cases h : c.residual.support.Nonempty
  · simpa only [flipCube, dif_pos h] using toggle_sign (pivot _ h) c.bits
  · exact (hx (by simp only [flipCube, dif_neg h])).elim

/-- Exactly one unpaired state for each square, situated in the second copy. -/
def squareState (n : ℕ+) : ℕ+ × ℕ+ := (1,n*n)

private def vacuumCube (k : Occupation) : OccupationCube :=
  ⟨0,k,∅,Finset.empty_subset _⟩

private theorem vacuum_labels (k : Occupation) : pairCubes.symm (vacuumCube k) = squareState (label k) := by
  have hb : bitOccupation ∅ = 0 := by ext p; simp [bit_at]
  change (label (0 - bitOccupation ∅), label (k+k+bitOccupation ∅)) = _
  rw [hb, tsub_zero, label_zero, add_zero, label_add]
  rfl

theorem parityPartner_fixed_iff (x : ℕ+ × ℕ+) :
    parityPartner x = x ↔ x ∈ Set.range squareState := by
  obtain ⟨c,rfl⟩ := pairCubes.symm.surjective x
  simp only [parityPartner, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq, flip_fixed]
  constructor
  · intro h
    have hb : c.bits = ∅ := Finset.subset_empty.mp (by simpa only [h,Finsupp.support_zero] using c.allowed)
    have he : c = vacuumCube c.pairs := OccupationCube.ext h rfl hb
    exact ⟨label c.pairs, (vacuum_labels _).symm.trans (congrArg pairCubes.symm he.symm)⟩
  · rintro ⟨n,hn⟩
    have he := (vacuum_labels (label.symm n)).trans (by simpa only [Equiv.apply_symm_apply] using hn)
    exact (congrArg OccupationCube.residual (pairCubes.symm.injective he)).symm

theorem squareState_injective : Function.Injective squareState := by
  intro m n h
  have hh := congrArg (fun x : ℕ+ × ℕ+ => (x.2 : ℕ)) h
  change (m : ℕ) * m = (n : ℕ) * n at hh
  apply PNat.coe_injective
  exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hh

#print axioms occupationCubes
#print axioms parityPartner_involutive
#print axioms parityPartner_product
#print axioms parityPartner_sign
#print axioms parityPartner_fixed_iff
#print axioms squareState_injective

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
