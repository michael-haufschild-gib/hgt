import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Modes
import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm

/-! # Binary orientation as a squarefree factor in the two-copy Hilbert space -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation

abbrev SquarefreeLabel := {n : ℕ+ // Squarefree n.val}
abbrev Coordinates := ℕ+ × ℕ+ × SquarefreeLabel

private theorem occupation_at (n : ℕ+) (p : Nat.Primes) :
    label.symm n p = n.val.factorization p.val :=
  primeExponentVector_apply n.val p

private theorem label_exponent (a : Bose) (p : Nat.Primes) :
    (label a).val.factorization p.val = a p :=
  (occupation_at (label a) p).symm.trans (congrArg (fun v : Bose => v p) (label.symm_apply_apply a))

private theorem binary_squarefree (b : Binary) : Squarefree (label (binaryOccupations b)).val := by
  apply (Nat.squarefree_iff_factorization_le_one (label (binaryOccupations b)).ne_zero).mpr
  intro p
  by_cases hp : p.Prime
  · have he := label_exponent (binaryOccupations b) ⟨p,hp⟩
    change (label (binaryOccupations b)).val.factorization p = (b ⟨p,hp⟩).val at he
    rw [he]
    exact Nat.le_of_lt_succ (b ⟨p,hp⟩).isLt
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- Binary prime occupations label exactly the squarefree positive integers. -/
def squarefreeBasis : Binary ≃ SquarefreeLabel where
  toFun b := ⟨label (binaryOccupations b),binary_squarefree b⟩
  invFun n := (label.symm n.val).mapRange (fun r : ℕ => (⟨r%2,Nat.mod_lt _ zero_lt_two⟩ : Fin 2)) rfl
  left_inv b := by
    apply Finsupp.ext
    intro p
    apply Fin.ext
    simp only [Equiv.symm_apply_apply,Finsupp.mapRange_apply,binaryOccupations]
    exact Nat.mod_eq_of_lt (b p).isLt
  right_inv n := by
    apply Subtype.ext
    apply label.symm.injective
    rw [label.symm_apply_apply]
    apply Finsupp.ext
    intro p
    have hp := (Nat.squarefree_iff_factorization_le_one n.val.ne_zero).mp n.property p.val
    change (label.symm n.val p)%2 = label.symm n.val p
    rw [occupation_at]
    exact Nat.mod_eq_of_lt (by omega)

/-- Normal coordinates record the common label, the remaining ordinary label, and the squarefree orientation. -/
def basis : (ℕ+ × ℕ+) ≃ Coordinates :=
  (Equiv.prodCongr label.symm label.symm).trans
    (occupations.trans (Equiv.prodCongr label (Equiv.prodCongr label squarefreeBasis)))

theorem common_eq_gcd (q : ℕ+ × ℕ+) : (basis q).1 = q.1.gcd q.2 := by
  apply label.symm.injective
  apply Finsupp.ext
  intro p
  change label.symm (label _) p = label.symm (q.1.gcd q.2) p
  rw [label.symm_apply_apply,occupation_at,PNat.gcd_coe,Nat.factorization_gcd q.1.ne_zero q.2.ne_zero]
  change (mode (label.symm q.1 p,label.symm q.2 p)).1 = min _ _
  rw [common_mode,occupation_at,occupation_at]

/-- A prime marks the binary output precisely when its multiplicity is greater in the second input. -/
theorem oriented_prime_iff (q : ℕ+ × ℕ+) (p : Nat.Primes) :
    (basis q).2.2.val.val.factorization p.val = 1 ↔
      q.1.val.factorization p.val < q.2.val.factorization p.val := by
  change (label (binaryOccupations _)).val.factorization p.val = 1 ↔ _
  rw [label_exponent]
  change ((mode (label.symm q.1 p,label.symm q.2 p)).2.2).val = 1 ↔ _
  have he : ∀ b : Fin 2, b.val = 1 ↔ b = 1 := fun b => ⟨fun hb => Fin.ext hb,fun hb => hb ▸ rfl⟩
  rw [he,orientation_iff,occupation_at,occupation_at]

theorem product_identity (q : ℕ+ × ℕ+) :
    q.1*q.2 = (basis q).1^2*(basis q).2.1*(basis q).2.2.val := by
  let v := (label.symm q.1,label.symm q.2)
  have he := congrArg label (total_occupations v)
  simp only [label_add] at he
  change label (label.symm q.1)*label (label.symm q.2) =
    (basis q).1*(basis q).1*(basis q).2.1*(basis q).2.2.val at he
  simpa only [Equiv.apply_symm_apply,pow_two] using he

/-- The common mode costs twice its one-copy energy; both remaining factors cost their ordinary energies. -/
theorem energy_identity (q : ℕ+ × ℕ+) :
    energy q.1+energy q.2 = 2*energy (basis q).1+energy (basis q).2.1+energy (basis q).2.2.val := by
  have he := congrArg energy (product_identity q)
  simp only [pow_two,energy_mul] at he
  linarith only [he]

private theorem vacuum_label : label 0 = 1 := by
  apply PNat.coe_injective
  exact Finsupp.prod_zero_index (h := fun p : Nat.Primes => fun k : ℕ => p.val^k)

def vacuum : SquarefreeLabel := ⟨1,by simp⟩

theorem diagonal_basis (n : ℕ+) : basis (n,n) = (n,1,vacuum) := by
  change (label (occupations (label.symm n,label.symm n)).1,
    label (occupations (label.symm n,label.symm n)).2.1,
    squarefreeBasis (occupations (label.symm n,label.symm n)).2.2) = _
  rw [diagonal_occupations]
  apply Prod.ext
  · exact label.apply_symm_apply n
  · apply Prod.ext
    · exact vacuum_label
    · apply Subtype.ext
      change label (binaryOccupations 0) = 1
      rw [show binaryOccupations 0 = 0 from Finsupp.ext fun _ => rfl,vacuum_label]

/-- A collision is precisely the joint vacuum of the excess and orientation factors, at arbitrary common label. -/
theorem collision_iff_joint_vacuum (q : ℕ+ × ℕ+) :
    q.1 = q.2 ↔ (basis q).2 = (1,vacuum) := by
  rcases q with ⟨m,n⟩
  constructor
  · intro he
    change m = n at he
    subst n
    exact congrArg Prod.snd (diagonal_basis m)
  · intro h
    let k := (basis (m,n)).1
    have he : basis (m,n) = basis (k,k) := by
      rw [diagonal_basis]
      exact Prod.ext rfl h
    have hs := basis.injective he
    exact (congrArg Prod.fst hs).trans (congrArg Prod.snd hs).symm

/-- Unitary change of the energy basis from two bosonic labels to three independent occupation factors. -/
def normalUnitary := GaloisForLFunctions.HTGeometry.lpReindexEquiv basis

theorem normalUnitary_apply (f : lp (fun _ : ℕ+ × ℕ+ => ℂ) 2) (q : ℕ+ × ℕ+) :
    normalUnitary f (basis q) = f q := by
  change f (basis.symm (basis q)) = f q
  rw [basis.symm_apply_apply]

#print axioms common_eq_gcd
#print axioms oriented_prime_iff
#print axioms product_identity
#print axioms energy_identity
#print axioms diagonal_basis
#print axioms collision_iff_joint_vacuum
#print axioms normalUnitary_apply
#print axioms normalUnitary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation
