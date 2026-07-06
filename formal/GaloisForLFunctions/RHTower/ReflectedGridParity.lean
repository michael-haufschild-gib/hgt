/-
The divisor-pair parity of reflected saddle collisions.

At the normalized height `T = 2πC`, the reflected saddle for mode `k` lands on the
integer grid point `m` exactly when `(k+1)m = C`.  Thus the integer-grid collisions of
the reflected saddle lattice are the divisor antidiagonal of `C`.

The reflection of the antidiagonal swaps the two factors.  All nonfixed collisions pair
off; the only possible unpaired collision is the square fixed point `r*r = C`.  Hence the
unit collision charge is paired unless `C` is a positive square, and the collision count is
odd exactly in that positive-square case.
-/
import GaloisForLFunctions.RHTower.ReflectedSaddleLattice
import GaloisForLFunctions.RHTower.SignatureParity

open Complex Real
open scoped BigOperators

namespace RHTower

/-! ### The reflected saddle/grid collision carrier -/

/-- The integer-grid collisions of the normalized reflected saddle lattice, represented as
factor pairs `n*m=C`.  Here `n=k+1` is the positive Fourier-mode label and `m` is the grid
point hit by the saddle. -/
def reflectedGridCollisions (C : ℕ) : Finset (ℕ × ℕ) :=
  C.divisorsAntidiagonal

/-- The reflection involution on the divisor antidiagonal. -/
def reflectedGridSwap (x : ℕ × ℕ) : ℕ × ℕ :=
  (x.2, x.1)

/-- Membership in the reflected grid-collision carrier is exactly the divisor equation. -/
theorem reflectedGridCollision_mem_iff {C : ℕ} {x : ℕ × ℕ} :
    x ∈ reflectedGridCollisions C ↔ x.1 * x.2 = C ∧ C ≠ 0 := by
  simp [reflectedGridCollisions, Nat.mem_divisorsAntidiagonal]

/-- Swapping the two factors preserves the reflected grid-collision carrier. -/
theorem reflectedGridSwap_mem {C : ℕ} {x : ℕ × ℕ} (hx : x ∈ reflectedGridCollisions C) :
    reflectedGridSwap x ∈ reflectedGridCollisions C := by
  rw [reflectedGridCollision_mem_iff] at hx ⊢
  exact ⟨by rw [reflectedGridSwap, Nat.mul_comm]; exact hx.1, hx.2⟩

/-- The factor swap is an involution. -/
theorem reflectedGridSwap_involutive (x : ℕ × ℕ) :
    reflectedGridSwap (reflectedGridSwap x) = x := by
  cases x
  rfl

/-- A fixed collision of the factor-swap reflection is a positive square. -/
theorem reflectedGridSwap_fixed_pos_square {C : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ reflectedGridCollisions C) (hfix : reflectedGridSwap x = x) :
    0 < x.1 ∧ x.1 * x.1 = C := by
  rw [reflectedGridCollision_mem_iff] at hx
  have h12 : x.2 = x.1 := by exact congrArg Prod.fst hfix
  have hsquare : x.1 * x.1 = C := by simpa [h12] using hx.1
  have hpos : 0 < x.1 := by
    by_contra hnot
    have hz : x.1 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz] at hsquare
    simp at hsquare
    exact hx.2 hsquare.symm
  exact ⟨hpos, hsquare⟩

/-- At height `T=2πC`, the reflected saddle hits grid point `m` exactly when
`(k+1)m=C`. -/
theorem reflectedSaddle_two_pi_nat_eq_nat_iff {C m : ℕ} {k : ℕ} :
    reflectedSaddle (2 * Real.pi * (C : ℝ)) k = (m : ℝ) ↔ (k + 1) * m = C := by
  unfold reflectedSaddle
  have hden : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    have hreal : ((k + 1 : ℕ) : ℝ) * (m : ℝ) = (C : ℝ) := by
      field_simp [hden] at h
      nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  · intro h
    have hreal : ((k + 1 : ℕ) : ℝ) * (m : ℝ) = (C : ℝ) := by exact_mod_cast h
    field_simp [hden]
    nlinarith [Real.pi_pos, hreal]

/-- The analytic saddle-grid condition and the divisor-antidiagonal condition are the same
finite carrier, modulo the nonzero condition built into `Nat.divisorsAntidiagonal`. -/
theorem reflectedGridCollision_iff_saddle_grid {C k m : ℕ} :
    (k + 1, m) ∈ reflectedGridCollisions C ↔
      reflectedSaddle (2 * Real.pi * (C : ℝ)) k = (m : ℝ) ∧ C ≠ 0 := by
  rw [reflectedGridCollision_mem_iff, reflectedSaddle_two_pi_nat_eq_nat_iff]

/-! ### The parity of the reflected collision carrier -/

/-- If the normalized height has no positive square fixed point, all reflected grid collisions
pair off under the factor swap. -/
theorem reflectedGridCollisions_even_of_no_pos_square {C : ℕ}
    (hnsq : ∀ n : ℕ, 0 < n → n * n ≠ C) :
    Even (reflectedGridCollisions C).card := by
  rw [Finset.card_eq_sum_ones]
  apply even_sum_of_fpf_involution (reflectedGridCollisions C)
    (fun x : ℕ × ℕ => reflectedGridSwap x) (fun _ => 1)
  · intro x hx
    exact reflectedGridSwap_mem hx
  · intro x hx
    exact reflectedGridSwap_involutive x
  · intro x hx hfix
    obtain ⟨hpos, hsquare⟩ := reflectedGridSwap_fixed_pos_square hx hfix
    exact hnsq x.1 hpos hsquare
  · intro x hx
    rfl

/-- The nonfixed reflected grid collisions always pair off. -/
theorem reflectedGridCollisions_nonfixed_even (C : ℕ) :
    Even ((reflectedGridCollisions C).filter fun x : ℕ × ℕ => ¬ x.1 = x.2).card := by
  rw [Finset.card_eq_sum_ones]
  apply even_sum_of_fpf_involution
    ((reflectedGridCollisions C).filter fun x : ℕ × ℕ => ¬ x.1 = x.2)
    (fun x : ℕ × ℕ => reflectedGridSwap x) (fun _ => 1)
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨reflectedGridSwap_mem hx.1, ?_⟩
    intro h
    apply hx.2
    simpa [reflectedGridSwap] using h.symm
  · intro x hx
    exact reflectedGridSwap_involutive x
  · intro x hx hfix
    rw [Finset.mem_filter] at hx
    have h21 : x.2 = x.1 := congrArg Prod.fst hfix
    exact hx.2 h21.symm
  · intro x hx
    rfl

/-- If `C=r²` with `r>0`, the fixed-point part of the collision carrier is the singleton
`(r,r)`. -/
theorem reflectedGridCollisions_fixed_eq_singleton {C r : ℕ} (hrpos : 0 < r) (hr : r * r = C) :
    ((reflectedGridCollisions C).filter fun x : ℕ × ℕ => x.1 = x.2) = {(r, r)} := by
  ext x
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx with ⟨hmem, heq⟩
    rw [reflectedGridCollision_mem_iff] at hmem
    have hsquare : x.1 * x.1 = C := by simpa [heq] using hmem.1
    have hx1 : x.1 = r := Nat.mul_self_inj.mp (by rw [hsquare, hr])
    cases x with
    | mk a b =>
      simp only at heq hx1 ⊢
      exact Prod.ext hx1 (by simpa [hx1] using heq.symm)
  · intro hx
    subst hx
    refine ⟨?_, rfl⟩
    rw [reflectedGridCollision_mem_iff]
    exact ⟨hr, by nlinarith⟩

/-- A positive square normalized height contributes exactly one unpaired collision, so the
ordered collision count is odd. -/
theorem reflectedGridCollisions_odd_of_pos_square {C r : ℕ} (hrpos : 0 < r) (hr : r * r = C) :
    Odd (reflectedGridCollisions C).card := by
  have hfixed := congrArg Finset.card (reflectedGridCollisions_fixed_eq_singleton (C := C) hrpos hr)
  simp at hfixed
  obtain ⟨k, hk⟩ := reflectedGridCollisions_nonfixed_even C
  have hpart := Finset.card_filter_add_card_filter_not
    (s := reflectedGridCollisions C) (p := fun x : ℕ × ℕ => x.1 = x.2)
  refine ⟨k, ?_⟩
  nlinarith

/-- **Sharp parity law for reflected saddle/grid collisions.**  The ordered collision carrier
has odd cardinality exactly when the normalized height `C` is a positive square. -/
theorem reflectedGridCollisions_odd_iff_pos_square {C : ℕ} :
    Odd (reflectedGridCollisions C).card ↔ ∃ r : ℕ, 0 < r ∧ r * r = C := by
  constructor
  · intro hodd
    by_contra hno
    push Not at hno
    obtain ⟨k, hk⟩ := reflectedGridCollisions_even_of_no_pos_square hno
    obtain ⟨j, hj⟩ := hodd
    omega
  · rintro ⟨r, hrpos, hr⟩
    exact reflectedGridCollisions_odd_of_pos_square hrpos hr

/-! ### Ledger interface for the reflected grid collisions -/

/-- The unit event list carried by the reflected grid-collision carrier. -/
def reflectedGridCollisionFluxList (C : ℕ) : List ℤ :=
  List.replicate (reflectedGridCollisions C).card 1

/-- The collision-flux list has sum equal to the collision count. -/
theorem reflectedGridCollisionFluxList_sum (C : ℕ) :
    (reflectedGridCollisionFluxList C).sum = (reflectedGridCollisions C).card := by
  simp [reflectedGridCollisionFluxList]

/-- If there is no positive square fixed point, the reflected collision unit events carry
paired flux. -/
theorem reflectedGridCollisionFluxPaired_of_no_pos_square {C : ℕ}
    (hnsq : ∀ n : ℕ, 0 < n → n * n ≠ C) :
    LedgerFluxPaired (reflectedGridCollisionFluxList C) := by
  rw [reflectedGridCollisionFluxList]
  exact ledgerFluxPaired_replicate_one
    (nonempty_bandEdgePairing_of_even (reflectedGridCollisions_even_of_no_pos_square hnsq).two_dvd)

/-- If there is no positive square fixed point, the reflected collision unit flux is even. -/
theorem reflectedGridCollisionFlux_two_dvd_sum_of_no_pos_square {C : ℕ}
    (hnsq : ∀ n : ℕ, 0 < n → n * n ≠ C) :
    (2 : ℤ) ∣ (reflectedGridCollisionFluxList C).sum := by
  exact ledgerFluxPaired_two_dvd_sum (reflectedGridCollisionFluxPaired_of_no_pos_square hnsq)

end RHTower
