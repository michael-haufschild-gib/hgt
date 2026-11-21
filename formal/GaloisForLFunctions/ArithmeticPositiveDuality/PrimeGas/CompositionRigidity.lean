import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint
import GaloisForLFunctions.HTGeometry.IncommensuratePhaseClock
import GaloisForLFunctions.RHTower.CarrierDepthThreeOffLineZeros

/-!
# Rigidity of the cyclic-order composition law

Two prime shells determine the complex parameter dual to a splitter. The real
part is detected by attenuation and the imaginary part by the incommensurate
prime energies. Across all shells, divisor inversion recovers the multiplicity
of each order from conservation of probability.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open scoped ComplexConjugate LinearPMap

/-- The Hamiltonian on the maximal domain of its logarithmic multiplier. -/
def hamiltonian : Gas →ₗ.[ℂ] Gas := _root_.RHTower.maximalRealDiagonal energy

theorem hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian :=
  _root_.RHTower.maximalRealDiagonal_isSelfAdjoint energy

theorem hamiltonian_apply (f : hamiltonian.domain) (n : ℕ+) :
    hamiltonian f n = (energy n : ℂ) * (f : Gas) n := rfl

/-- The complex parameter of a heat wave is determined by its values at 2 and 3. -/
theorem two_prime_heat_injective : Function.Injective (fun s : ℂ => (heat s 2, heat s 3)) := by
  intro u v huv
  have h₂ : heat u 2 = heat v 2 := congrArg Prod.fst huv
  have h₃ : heat u 3 = heat v 3 := congrArg Prod.snd huv
  have hE : 0 < energy 2 := Real.log_pos (by norm_num)
  have hr : u.re = v.re := by
    have h := congrArg norm h₂
    rw [norm_heat, norm_heat] at h
    exact neg_injective (mul_right_cancel₀ hE.ne' (Real.exp_injective h))
  have phase (z : ℂ) (n : ℕ+) :
      heat z n = (Real.exp (-z.re * energy n) : ℂ) *
        _root_.HTGeometry.phaseClockValue (energy n) (-z.im) := by
    rw [heat, _root_.HTGeometry.phaseClockValue, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  have phaseEq (n : ℕ+) (h : heat u n = heat v n) :
      _root_.HTGeometry.phaseClockValue (energy n) (-u.im) =
      _root_.HTGeometry.phaseClockValue (energy n) (-v.im) := by
    rw [phase, phase, hr] at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) h
  have irr : Irrational (energy 3 / energy 2) :=
    _root_.RHTower.CarrierDepthThree.irrational_log_three_div_log_two
  have hi := _root_.HTGeometry.phaseClockPair_injective hE.ne' irr
    (Prod.ext (phaseEq 2 h₂) (phaseEq 3 h₃))
  exact Complex.ext hr (neg_injective hi)

/-- Unit cross-pairing already forces the reflected partner on the two smallest prime shells. -/
theorem dual_on_two_primes_iff (w s : ℂ) :
    (∀ n ∈ ({2, 3} : Finset ℕ+),
      ∑ a ∈ (n : ℕ).divisors, conj (channel w n a) * channel s n a = 1) ↔
      w = 1 - conj s := by
  constructor
  · intro h
    have same (n : ℕ+) (hn : n ∈ ({2, 3} : Finset ℕ+)) :
        heat (conj w + s) n = heat 1 n := by
      have he := (h n hn).trans (reflected_shell_pairing s n).symm
      simp only [shell_pairing, map_sub, map_one, Complex.conj_conj, sub_add_cancel] at he
      exact mul_left_cancel₀ (by exact_mod_cast n.ne_zero) he
    have hp := two_prime_heat_injective (a₁ := conj w + s) (a₂ := 1)
      (Prod.ext (same 2 (by simp)) (same 3 (by simp)))
    have hw : conj w = 1 - s := eq_sub_of_add_eq hp
    simpa only [Complex.conj_conj, map_sub, map_one] using congrArg conj hw
  · rintro rfl n _
    exact reflected_shell_pairing s n

/-- The partner selected by the two prime shells implements the reflection of the
completed partition function. -/
theorem completed_partition_dual (s : ℂ) :
    ∃! w : ℂ, (∀ n ∈ ({2, 3} : Finset ℕ+),
      ∑ a ∈ (n : ℕ).divisors, conj (channel w n a) * channel s n a = 1) ∧
      completedRiemannZeta (conj w) = completedRiemannZeta s := by
  refine ⟨1 - conj s, ⟨(dual_on_two_primes_iff _ _).2 rfl, ?_⟩,
    fun w hw => (dual_on_two_primes_iff w s).1 hw.1⟩
  simp only [map_sub, map_one, Complex.conj_conj, completedRiemannZeta_one_sub]

/-- Conservation in the heat-weighted divisor channels uniquely determines all positive
order multiplicities. The vacuum contributes its single residue. -/
theorem channel_multiplicity_rigidity (m : ℕ → ℕ) :
    (∀ n : ℕ+, (∑ d ∈ (n : ℕ).divisors, (m d : ℝ)) *
      ‖heat (1 / 2) n‖ ^ 2 = 1) ↔ (∀ d : ℕ+, m d = (d : ℕ).totient) := by
  have normed (n : ℕ+) : ((n : ℕ) : ℝ) * ‖heat (1 / 2) n‖ ^ 2 = 1 := by
    rw [← shellMass_eq]
    norm_num [shellMass]
  constructor
  · intro h
    have sums (n : ℕ+) : (n : ℕ).divisors.sum m = (n : ℕ) := by
      have he := (h n).trans (normed n).symm
      rw [← Nat.cast_sum] at he
      have hn : ‖heat (1 / 2) n‖ ^ 2 ≠ 0 := by rw [norm_heat]; positivity
      exact_mod_cast mul_right_cancel₀ hn he
    have recover (k : ℕ) : 0 < k → m k = k.totient := by
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro hk
        have he := (sums ⟨k, hk⟩).trans (Nat.sum_totient k).symm
        change k.divisors.sum m = k.divisors.sum Nat.totient at he
        rw [← Nat.cons_self_properDivisors hk.ne', Finset.sum_cons, Finset.sum_cons] at he
        have hproper : k.properDivisors.sum m = k.properDivisors.sum Nat.totient := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hdiv := Nat.mem_properDivisors.mp hd
          exact ih d hdiv.2 (Nat.pos_of_dvd_of_pos hdiv.1 hk)
        rw [hproper] at he
        exact Nat.add_right_cancel he
    exact fun d => recover d d.pos
  · intro h n
    have hd : ∑ d ∈ (n : ℕ).divisors, m d = (n : ℕ) := by
      exact (Finset.sum_congr rfl fun d hd => h ⟨d, Nat.pos_of_mem_divisors hd⟩).trans
        (Nat.sum_totient n)
    rw [← Nat.cast_sum, hd]
    exact normed n

#print axioms hamiltonian_selfAdjoint
#print axioms hamiltonian_apply
#print axioms dual_on_two_primes_iff
#print axioms completed_partition_dual
#print axioms channel_multiplicity_rigidity

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
