import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture.Angles
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.TorsionReadout

/-!
# The phases lost at maximal strict aperture

Dyadic powers reach the antipode exactly from nontrivial roots of
two-power order. At fixed time a common dyadic power detects the entire
two-primary part of the relative prime-gas spectrum.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture

open SampledClocks

theorem exp_pi : Circle.exp Real.pi = -1 := Subtype.ext Complex.exp_pi_mul_I

theorem angle_pi_iff (z : Circle) : angle z = Real.pi ↔ z = -1 := by
  constructor
  · intro hz
    rcases representatives z with h | h <;> simpa [hz,Circle.exp_neg,exp_pi] using h
  · rintro rfl
    rw [← exp_pi]
    exact exp_angle _ ⟨Real.pi_pos.le,le_rfl⟩

theorem misses_pi (z : Circle) : ¬Survives Real.pi z ↔ ∃ k : ℕ, z^(2^k : ℕ) = -1 := by
  unfold Survives
  push Not
  exact exists_congr fun k => ⟨fun h => (angle_pi_iff _).mp (le_antisymm (angle_mem _).2 h),
    fun h => ((angle_pi_iff _).mpr h).ge⟩

def DyadicReturn (z : Circle) := ∃ k : ℕ, z^(2^k : ℕ) = 1

private theorem square_one (z : Circle) (h : z^2 = 1) : z = 1 ∨ z = -1 := by
  have he : (z:ℂ)^2 = 1 := congrArg (fun w : Circle => (w:ℂ)) h
  rcases sq_eq_one_iff.mp he with hp | hn
  · exact Or.inl (Subtype.ext hp)
  · exact Or.inr (Subtype.ext hn)

theorem misses_iff_return (z : Circle) : ¬Survives Real.pi z ↔ DyadicReturn z ∧ z ≠ 1 := by
  rw [misses_pi]
  constructor
  · rintro ⟨k,h⟩
    refine ⟨⟨k+1,?_⟩,?_⟩
    · rw [pow_succ,pow_mul,h]; simp
    · rintro rfl
      have hh := congrArg (fun w : Circle => (w:ℂ)) h
      have hc : (1:ℂ) = -1 := by simpa using hh
      norm_num at hc
  · rintro ⟨h,hz⟩
    classical
    change ∃ k : ℕ, z^(2^k : ℕ) = 1 at h
    have hs := Nat.find_spec h
    obtain ⟨k,hk⟩ : ∃ k, Nat.find h = k+1 := by
      cases he : Nat.find h with
      | zero => rw [he,pow_zero,pow_one] at hs; exact (hz hs).elim
      | succ k => exact ⟨k,rfl⟩
    rw [hk,pow_succ,pow_mul] at hs
    have hn := Nat.find_min h (show k < Nat.find h by rw [hk]; exact Nat.lt_succ_self _)
    exact ⟨k,(square_one _ hs).resolve_left hn⟩

theorem binary_power (t : ℝ) (N : ℕ) (x : Bool → ℕ+) :
    (binary ((N:ℝ)*t)).Resonant x ↔ ((binary t).phase () x)^N = 1 := by
  have he := (binary t).multiple_phase N () x
  exact ⟨fun h => he ▸ h (),fun h _ => he.trans h⟩

/-- All dyadic returns of the arithmetic spectrum occur by one common doubling depth. -/
theorem common_dyadic (t : ℝ) : ∃ K : ℕ, ∀ x : Bool → ℕ+,
    DyadicReturn ((binary t).phase () x) ↔ ((binary t).phase () x)^(2^K : ℕ) = 1 := by
  obtain ⟨N,hN⟩ := TorsionReadout.common_return t
  refine ⟨N.val,fun x => ⟨?_,fun h => ⟨N.val,h⟩⟩⟩
  rintro ⟨k,hk⟩
  let z := (binary t).phase () x
  have hper : TorsionReadout.periodic t x := ⟨⟨2^k,pow_pos (by norm_num) k⟩,hk⟩
  rw [hN] at hper
  have hn := orderOf_dvd_of_pow_eq_one ((binary_power t N.val x).mp hper)
  have hd : orderOf z ∣ 2^k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hle : j ≤ N.val := (Nat.lt_two_pow_self (n := j)).le.trans
    (Nat.le_of_dvd N.pos (show 2^j ∣ N.val from hj ▸ hn))
  apply orderOf_dvd_iff_pow_eq_one.mp
  change orderOf z ∣ 2^N.val
  rw [hj]
  exact pow_dvd_pow 2 hle

#print axioms angle_pi_iff
#print axioms misses_iff_return
#print axioms common_dyadic

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DyadicAperture
