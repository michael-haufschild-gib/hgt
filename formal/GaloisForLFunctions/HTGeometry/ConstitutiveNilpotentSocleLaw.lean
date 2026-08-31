import GaloisForLFunctions.QECLean.Stabilizer.Framework.Homological.BBBocksteinRank
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Constitutive nilpotent-socle law

The composite-kernel inequality from the homological transfer organ iterates to

`finrank (ker (N ^ k)) ≤ k * finrank (ker N)`.

Consequently a finite-dimensional nilpotent endomorphism with one-dimensional kernel has one
complete Jordan chain, without choosing coordinates.  Its top nonzero power has range exactly the
kernel; in dimension at least two this top power is a nonzero rank-one square-zero socle current.
-/

open Module LinearMap

namespace GaloisForLFunctions.HTGeometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Iterated composite-kernel conservation: an order-`k` invisible history has dimension at most
`k` times the one-step invisible dimension. -/
theorem finrank_ker_pow_le_mul_finrank_ker (N : Module.End K V) (k : ℕ) :
    finrank K (LinearMap.ker (N ^ k)) ≤
      k * finrank K (LinearMap.ker N) := by
  induction k with
  | zero =>
      have honeker : LinearMap.ker (1 : Module.End K V) = ⊥ := by
        apply LinearMap.ker_eq_bot.mpr
        intro x y hxy
        simpa using hxy
      change finrank K (LinearMap.ker (1 : Module.End K V)) ≤
        0 * finrank K (LinearMap.ker N)
      rw [honeker]
      simp
  | succ k ih =>
      rw [pow_succ]
      have hcomp :=
        Quantum.Stabilizer.Homological.BBBocksteinRank.finrank_ker_comp_le
          N (N ^ k)
      change finrank K (LinearMap.ker ((N ^ k) * N)) ≤ _ at hcomp
      calc
        finrank K (LinearMap.ker ((N ^ k) * N))
            ≤ finrank K (LinearMap.ker N) +
                finrank K (LinearMap.ker (N ^ k)) := hcomp
        _ ≤ finrank K (LinearMap.ker N) +
                k * finrank K (LinearMap.ker N) := Nat.add_le_add_left ih _
        _ = (k + 1) * finrank K (LinearMap.ker N) := by
          simp only [Nat.add_mul, one_mul]
          ac_rfl

/-- Corank one forces survival through the penultimate dimensional power.  Nilpotence is not
needed for this half of the single-chain law. -/
theorem pow_finrank_sub_one_ne_zero_of_finrank_ker_eq_one
    (N : Module.End K V)
    (hker : finrank K (LinearMap.ker N) = 1) :
    N ^ (finrank K V - 1) ≠ 0 := by
  intro hzero
  have hdimpos : 0 < finrank K V := by
    have hkerpos : 0 < finrank K (LinearMap.ker N) := by omega
    exact lt_of_lt_of_le hkerpos (Submodule.finrank_le (LinearMap.ker N))
  have hkerpowtop : LinearMap.ker (N ^ (finrank K V - 1)) = ⊤ := by
    rw [hzero, LinearMap.ker_zero]
  have hbound := finrank_ker_pow_le_mul_finrank_ker N (finrank K V - 1)
  rw [hkerpowtop, finrank_top, hker] at hbound
  omega

/-- A nilpotent endomorphism of a `d`-dimensional space vanishes at power `d`. -/
theorem pow_finrank_eq_zero_of_isNilpotent
    (N : Module.End K V) (hN : IsNilpotent N) :
    N ^ finrank K V = 0 := by
  have hchar := hN.charpoly_eq_X_pow_finrank
  simpa only [hchar, map_pow, Polynomial.aeval_X] using N.aeval_self_charpoly

/-- Coordinate-free single-Jordan-chain criterion: nilpotence and geometric multiplicity one
force nilpotency index equal to the total dimension. -/
theorem nilpotencyIndex_eq_finrank_of_finrank_ker_eq_one
    (N : Module.End K V) (hN : IsNilpotent N)
    (hker : finrank K (LinearMap.ker N) = 1) :
    N ^ finrank K V = 0 ∧ N ^ (finrank K V - 1) ≠ 0 := by
  exact ⟨pow_finrank_eq_zero_of_isNilpotent N hN,
    pow_finrank_sub_one_ne_zero_of_finrank_ker_eq_one N hker⟩

/-- Top nonzero power of a nilpotent one-chain reconstructs its unique eigenline exactly. -/
theorem range_pow_finrank_sub_one_eq_ker_of_isNilpotent_of_finrank_ker_eq_one
    (N : Module.End K V) (hN : IsNilpotent N)
    (hker : finrank K (LinearMap.ker N) = 1) :
    LinearMap.range (N ^ (finrank K V - 1)) = LinearMap.ker N := by
  let d := finrank K V
  have hdimpos : 0 < d := by
    have hkerpos : 0 < finrank K (LinearMap.ker N) := by omega
    exact lt_of_lt_of_le hkerpos (Submodule.finrank_le (LinearMap.ker N))
  have hpowd : N ^ d = 0 := pow_finrank_eq_zero_of_isNilpotent N hN
  have htopne : N ^ (d - 1) ≠ 0 :=
    pow_finrank_sub_one_ne_zero_of_finrank_ker_eq_one N hker
  have hrangele : LinearMap.range (N ^ (d - 1)) ≤ LinearMap.ker N := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    have hmul : N * N ^ (d - 1) = 0 := by
      rw [← pow_succ']
      have hd : d - 1 + 1 = d := by omega
      rw [hd, hpowd]
    have happ := LinearMap.congr_fun hmul x
    simpa using happ
  have hrangene : LinearMap.range (N ^ (d - 1)) ≠ ⊥ := by
    intro hrange
    exact htopne (LinearMap.range_eq_bot.mp hrange)
  apply Submodule.eq_of_le_of_finrank_eq hrangele
  have hpos : 0 < finrank K (LinearMap.range (N ^ (d - 1))) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrangene (Submodule.finrank_eq_zero.mp hzero)
  have hle := Submodule.finrank_mono hrangele
  omega

/-- Once dimension is at least two, the penultimate power of every nilpotent endomorphism is
square-zero.  In the corank-one case it is additionally nonzero and rank one. -/
theorem pow_finrank_sub_one_sq_eq_zero_of_isNilpotent
    (N : Module.End K V) (hN : IsNilpotent N)
    (hdim : 2 ≤ finrank K V) :
    (N ^ (finrank K V - 1)) ^ 2 = 0 := by
  have hpowd : N ^ finrank K V = 0 := pow_finrank_eq_zero_of_isNilpotent N hN
  rw [pow_two, ← pow_add]
  apply pow_eq_zero_of_le _ hpowd
  omega

/-- Canonical conormal/socle current attached to an endomorphism. -/
noncomputable def nilpotentSocleCurrent (N : Module.End K V) : Module.End K V :=
  N ^ (finrank K V - 1)

theorem nilpotentSocleCurrent_ne_zero
    (N : Module.End K V) (hker : finrank K (LinearMap.ker N) = 1) :
    nilpotentSocleCurrent N ≠ 0 :=
  pow_finrank_sub_one_ne_zero_of_finrank_ker_eq_one N hker

theorem range_nilpotentSocleCurrent
    (N : Module.End K V) (hN : IsNilpotent N)
    (hker : finrank K (LinearMap.ker N) = 1) :
    LinearMap.range (nilpotentSocleCurrent N) = LinearMap.ker N :=
  range_pow_finrank_sub_one_eq_ker_of_isNilpotent_of_finrank_ker_eq_one N hN hker

theorem finrank_range_nilpotentSocleCurrent
    (N : Module.End K V) (hN : IsNilpotent N)
    (hker : finrank K (LinearMap.ker N) = 1) :
    finrank K (LinearMap.range (nilpotentSocleCurrent N)) = 1 := by
  rw [range_nilpotentSocleCurrent N hN hker, hker]

theorem nilpotentSocleCurrent_sq_eq_zero
    (N : Module.End K V) (hN : IsNilpotent N)
    (hdim : 2 ≤ finrank K V) :
    nilpotentSocleCurrent N ^ 2 = 0 :=
  pow_finrank_sub_one_sq_eq_zero_of_isNilpotent N hN hdim

end GaloisForLFunctions.HTGeometry
