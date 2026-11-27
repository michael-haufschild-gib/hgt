import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.LevelCount
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Temperature

/-! # Calibrating divisor-splitting isometry by changing the elementary prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration

open Real Finset
open _root_.HTGeometry (finiteGibbsStateWeight)

variable {I : Type*} [Fintype I]

/-- The same occupation pattern is transplanted to the chosen prime. -/
def accepts (k : I → ℕ) (p : Nat.Primes) (d : ℝ) :=
  lawOrder (finiteGibbsStateWeight d (primeModes p k)) 1

def levelCount (k : I → ℕ) := (univ.image k).card

theorem log_pos_prime (p : Nat.Primes) : 0<log (p.val : ℝ) :=
  log_pos (Nat.one_lt_cast.mpr p.property.one_lt)

/-- Each prime supplies a distinct clock, with unchanged normalized occupation spectrum. -/
theorem accepts_iff (k : I → ℕ) (p : Nat.Primes) (d : ℝ) :
    accepts k p d ↔ agrees (levels k) (|d| * log p.val) := by
  rw [accepts,gibbs_order,one_mul,Sparse.mode_grid,agrees_affine,← agrees_abs (levels k) (d*log p.val),
    abs_mul,abs_of_pos (log_pos_prime p)]

theorem card_levels (k : I → ℕ) : (univ.image (levels k)).card=levelCount k := by
  classical
  have eq : univ.image (levels k)=(univ.image k).image (fun e : ℕ => (e : ℝ)) := by rw [image_image]; rfl
  rw [eq,card_image_of_injective _ Nat.cast_injective,levelCount]

theorem physical_level_count (p : Nat.Primes) (k : I → ℕ) :
    (univ.image (primeModes p k)).card=levelCount k := by
  classical
  let f (e : ℝ) := log p.val*e+0
  have inj : Function.Injective f := fun a b h =>
    mul_left_cancel₀ (log_pos_prime p).ne' (add_right_cancel h)
  have eq : univ.image (primeModes p k)=(univ.image (levels k)).image f := by
    rw [image_image,Sparse.mode_grid]; rfl
  rw [eq,card_image_of_injective _ inj,card_levels]

/-- Away from zero damping, an asymmetric packet cannot accept more than
its number of distinct occupations minus two different elementary primes. -/
theorem accepting_prime_bound (k : I → ℕ) (S : Finset Nat.Primes) {d : ℝ} (hd : d≠0)
    (asym : ¬Reflects (levels k)) (pass : ∀ p ∈ S, accepts k p d) :
    S.card+2≤levelCount k := by
  classical
  let fin := finite_blind (levels k)
  have size : S.card≤fin.toFinset.card := by
    apply card_le_card_of_injOn (fun p : Nat.Primes => |d| * log p.val)
    · intro p hp
      exact fin.mem_toFinset.mpr ⟨mul_pos (abs_pos.mpr hd) (log_pos_prime p),
        (accepts_iff k p d).mp (pass p hp),asym⟩
    · intro p _ q _ eq
      have logs := mul_left_cancel₀ (abs_ne_zero.mpr hd) eq
      have pos (r : Nat.Primes) : 0<(r.val : ℝ) := Nat.cast_pos.mpr r.property.pos
      have vals := (log_injOn_pos (pos p) (pos q) logs)
      exact Subtype.ext (Nat.cast_injective vals)
  have bound := blind_distinct_levels (levels k) asym
  rw [card_levels,Set.ncard_eq_toFinset_card _ fin] at bound
  omega

/-- With d distinct occupations, any d-1 distinct primes detect the critical
line for every asymmetric packet, without changing damping or multiplicities. -/
theorem prime_calibration (k : I → ℕ) (S : Finset Nat.Primes) (enough : levelCount k<S.card+2) (s : ℂ) :
    (∀ p ∈ S, accepts k p (2*s.re-1)) ↔
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨ Reflects (levels k) := by
  rw [split_isometric_iff]
  constructor
  · intro pass
    by_contra! no
    have non : 2*s.re-1≠0 := by intro h; apply no.1; linarith only [h]
    exact enough.not_ge (accepting_prime_bound k S non no.2 pass)
  · rintro (line | symm) p _
    · simp only [accepts_iff,show 2*s.re-1=0 by rw [line]; ring,abs_zero,zero_mul,agrees,neg_zero]
    · exact (accepts_iff k p _).mpr (reflection_agrees symm _)

#print axioms accepting_prime_bound
#print axioms prime_calibration

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration
