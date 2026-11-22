import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Partition
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# Lowest energy in an antipodal rejection

The occupied products are the missing powers of the primitive block times
squares. A square lowest block would have two coprime square factors.
Their roots hit the same antipode one doubling later, at lower energy.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open DyadicAperture.Binary

def shells (t : ℝ) : Set ℕ+ := {N | ∃ x, rejected t x ∧ x false*x true = N}

private def first (t : ExceptionalTime) : Missing (windingOrder t) :=
  ⟨1,fun h => (not_le.mpr (order_nontrivial t)) (Nat.le_of_dvd Nat.zero_lt_one h)⟩

/-- The entire energy support in multiplicative coordinates. -/
theorem shells_iff (t : ExceptionalTime) (N : ℕ+) : N ∈ shells t.val ↔
    ∃ (k : Missing (windingOrder t)) (n : ℕ+), N = (block t)^k.val*n^2 := by
  obtain ⟨a,b,_,_,hab,e,he⟩ := block_basis t
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨p,hp⟩ := e.surjective ⟨x,hx⟩
    have hword : (e p).val = x := congrArg Subtype.val hp
    rw [he] at hword
    exact ⟨p.2.1,p.2.2,by rw [← hword,ray_product,hab]⟩
  · rintro ⟨k,n,rfl⟩
    refine ⟨(e (false,k,n)).val,(e (false,k,n)).property,?_⟩
    rw [he,ray_product,hab]

theorem block_least (t : ExceptionalTime) : IsLeast (shells t.val) (block t) := by
  refine ⟨(shells_iff t _).mpr ⟨first t,1,by simp [first]⟩,?_⟩
  intro N hN
  obtain ⟨⟨k,hk⟩,n,rfl⟩ := (shells_iff t N).mp hN
  cases k with
  | zero => exact (hk (dvd_zero _)).elim
  | succ k =>
    change block t ≤ (block t)^(k+1)*n^2
    rw [pow_succ',mul_assoc]
    exact Nat.le_mul_of_pos_right _ ((block t)^k*n^2).pos

private theorem root_label (a : ℕ+) (h : IsSquare a.val) : ∃ c : ℕ+, a = c*c := by
  obtain ⟨c,hc⟩ := h
  have hn : c ≠ 0 := fun hz => a.ne_zero (by simpa only [hz,Nat.zero_mul] using hc)
  exact ⟨⟨c,Nat.pos_of_ne_zero hn⟩,PNat.coe_injective hc⟩

private theorem root_rejected (t : ℝ) (c d : ℕ+) (h : rejected t (pair (c*c) (d*d))) :
    rejected t (pair c d) := by
  obtain ⟨k,j,hj⟩ := (lost_winding t _).mp h
  change (2^k*t)*(energy (c*c)-energy (d*d)) = _ at hj
  rw [energy_mul,energy_mul] at hj
  refine (lost_winding t _).mpr ⟨k+1,j,?_⟩
  change (2^(k+1)*t)*(energy c-energy d) = _
  rw [pow_succ]
  linear_combination hj

/-- A square block would put its own square root in a lower occupied shell. -/
theorem block_nonsquare (t : ExceptionalTime) : ¬IsSquare (block t).val := by
  intro hs
  obtain ⟨a,b,hc,_,hab,e,he⟩ := block_basis t
  rw [← hab] at hs
  obtain ⟨ha,hb⟩ := _root_.RHTower.isSquare_and_isSquare_of_coprime_of_isSquare_mul (PNat.coprime_coe.mpr hc) hs
  have hx := (e (false,first t,1)).property
  rw [he] at hx
  have hr : ray a b false 1 1 = pair a b := by
    funext i
    cases i
    · change a^1*1 = a; simp
    · change b^1*1 = b; simp
  change rejected t.val (ray a b false 1 1) at hx
  rw [hr] at hx
  obtain ⟨c,rfl⟩ := root_label a ha
  obtain ⟨d,rfl⟩ := root_label b hb
  have hl := (block_least t).2 (show c*d ∈ shells t.val from ⟨pair c d,root_rejected _ _ _ hx,rfl⟩)
  change (block t).val ≤ (c*d).val at hl
  have hgt := (block_nontrivial t).trans_le hl
  have hsmall := Nat.mul_lt_mul_of_pos_right hgt (c*d).pos
  have heq : block t = (c*d)*(c*d) := by rw [← hab]; ac_rfl
  rw [Nat.one_mul] at hsmall
  rw [heq] at hl
  exact (not_le.mpr hsmall) hl

/-- Rejection of the prime two paired with vacuum determines the lowest block exactly. -/
theorem prime_vacuum_block (t : {t : ℝ // rejected t primeVacuum}) :
    block ⟨t.val,⟨_,t.property⟩⟩ = 2 := by
  let u : ExceptionalTime := ⟨t.val,⟨_,t.property⟩⟩
  have hmem : (2 : ℕ+) ∈ shells u.val :=
    ⟨primeVacuum,t.property,show (2:ℕ+)*1 = 2 from mul_one _⟩
  have hl := (block_least u).2 hmem
  have hg := block_nontrivial u
  change (block u).val ≤ 2 at hl
  apply PNat.coe_injective
  change (block u).val = 2
  omega

theorem block_two_dense : Dense {t : ℝ | ∃ h : t ∈ exceptional, block ⟨t,h⟩ = 2} :=
  Dense.mono (fun t h => ⟨⟨primeVacuum,h⟩,prime_vacuum_block ⟨t,h⟩⟩) prime_vacuum_dense

#print axioms shells_iff
#print axioms block_least
#print axioms block_nonsquare
#print axioms prime_vacuum_block
#print axioms block_two_dense

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
