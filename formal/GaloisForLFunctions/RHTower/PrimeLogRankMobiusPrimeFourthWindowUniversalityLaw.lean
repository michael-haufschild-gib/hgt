import GaloisForLFunctions.RHTower.MixedPowerSupportedPrimeMassFiniteWindowUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeLogRankMobiusDistortionUniversalityLaw

/-!
# Prime-log rank, Möbius distortion, and prime fourth-window universality

The quarter-weighted prime packet has a rigid multiplicative convolution at every prime square:
unique factorization leaves only the diagonal pair `(p,p)`, with coefficient `p⁻¹/²`.  Hence the
same finite prime packet that carries independent logarithmic phases and critical Möbius
distortion also forces reciprocal-prime mass into its exact Steinhaus fourth moment and every
symmetric deterministic fourth-moment window.
-/

open Complex MeasureTheory intervalIntegral Finset
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- Quarter-weighted coefficient on the prime packet. -/
def primeQuarterCoeff (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 4 : ℝ))

/-- On a finite prime support, unique factorization leaves exactly the pair `(p,p)` in the
convolution fiber over `p²`. -/
theorem dpolyConv_primeQuarterCoeff_sq
    (P : Finset ℕ) (hprime : ∀ q ∈ P, q.Prime)
    {p : ℕ} (hpP : p ∈ P) :
    dpolyConv primeQuarterCoeff primeQuarterCoeff P P (p ^ 2) =
      (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hp : p.Prime := hprime p hpP
  have hfilter :
      (P ×ˢ P).filter (fun qr => qr.1 * qr.2 = p ^ 2) = {(p, p)} := by
    ext qr
    rcases qr with ⟨q, r⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hqP, hrP⟩, hqr⟩
      have hq : q.Prime := hprime q hqP
      have hr : r.Prime := hprime r hrP
      have hpdiv : p ∣ q * r := by
        rw [hqr]
        exact dvd_pow_self p two_ne_zero
      rcases hp.dvd_mul.mp hpdiv with hpq | hpr
      · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq |>.symm
        subst q
        have hrp : r = p := by
          apply Nat.mul_left_cancel hp.pos
          simpa [pow_two] using hqr
        simp [hrp]
      · have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr |>.symm
        subst r
        have hqp : q = p := by
          apply Nat.mul_right_cancel hp.pos
          simpa [pow_two] using hqr
        simp [hqp]
    · intro hqr
      injection hqr with hq hr
      subst q
      subst r
      exact ⟨⟨hpP, hpP⟩, by simp [pow_two]⟩
  unfold dpolyConv
  rw [hfilter]
  simp only [Finset.sum_singleton]
  unfold primeQuarterCoeff
  rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
  congr 1
  ring

/-- **Prime-packet fourth-window universality law.**  Every cutoff `N ≥ 2` gives one prime
packet with independent logarithmic phases, rank-controlled critical Möbius distortion, exact
Steinhaus fourth-moment convolution diagonal, reciprocal-prime mass in that random fourth
moment, and the same mass in every positive symmetric deterministic fourth-moment window after
subtracting only the explicit convolution sinc-collision energy. -/
theorem primeLogRank_mobiusDistortion_primeQuarterFourthWindow
    (N : ℕ) (hN : 2 ≤ N) (T : ℝ) (hT : 0 < T) :
    LinearIndependent ℤ
        (fun p : ((N + 1).primesBelow : Finset ℕ) => Real.log (p : ℕ)) ∧
      1 + 4 * ((Nat.primeCounting' (N + 1) : ℝ) / (N : ℝ)) ≤
        finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (N + 1)) ∧
      (∫ ω,
          ‖(∑ p ∈ Nat.primesBelow (N + 1),
              (primeQuarterCoeff p : ℂ) * X p ω) *
            (∑ p ∈ Nat.primesBelow (N + 1),
              (primeQuarterCoeff p : ℂ) * X p ω)‖ ^ 2 ∂steinhausMeasure =
        ∑ k ∈ prodSupport (Nat.primesBelow (N + 1)) (Nat.primesBelow (N + 1)),
          dpolyConv primeQuarterCoeff primeQuarterCoeff
              (Nat.primesBelow (N + 1)) (Nat.primesBelow (N + 1)) k ^ 2) ∧
      (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ)⁻¹) ≤
        ∫ ω,
          ‖(∑ p ∈ Nat.primesBelow (N + 1),
              (primeQuarterCoeff p : ℂ) * X p ω) *
            (∑ p ∈ Nat.primesBelow (N + 1),
              (primeQuarterCoeff p : ℂ) * X p ω)‖ ^ 2 ∂steinhausMeasure ∧
      (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ)⁻¹) -
          dpolySincOffDiagonalEnergy
            (dpolyConv primeQuarterCoeff primeQuarterCoeff
              (Nat.primesBelow (N + 1)) (Nat.primesBelow (N + 1)))
            (prodSupport (Nat.primesBelow (N + 1)) (Nat.primesBelow (N + 1))) T ≤
        (∫ τ in (-T)..T,
          ‖dpoly primeQuarterCoeff (Nat.primesBelow (N + 1)) τ *
            dpoly primeQuarterCoeff (Nat.primesBelow (N + 1)) τ‖ ^ 2) /
          (2 * T) := by
  let P := Nat.primesBelow (N + 1)
  have hprime : ∀ p ∈ P, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesBelow hp
  have hsupport : ∀ p ∈ P, p ^ 2 ∈ prodSupport P P := by
    intro p hp
    exact Finset.mem_image.mpr ⟨(p, p), by simp [hp], by simp [pow_two]⟩
  have hvalue : ∀ p ∈ P,
      1 * (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        |dpolyConv primeQuarterCoeff primeQuarterCoeff P P (p ^ 2)| := by
    intro p hp
    rw [one_mul, dpolyConv_primeQuarterCoeff_sq P hprime hp,
      abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast (hprime p hp).pos) _)]
  have hpositive : ∀ p ∈ P, 1 ≤ p :=
    fun p hp => (hprime p hp).one_le
  have hwindow :=
    mixedPowerSupportedPrimeMass_randomExact_deterministicWindowLowerBound
      primeQuarterCoeff primeQuarterCoeff P P hpositive hpositive
      (P := P) (δ := 1) (m := 2) two_ne_zero zero_le_one
      hsupport hvalue T hT
  have hpacket := primeLogRank_and_mobiusPhaseDistortion N hN
  exact ⟨hpacket.1, hpacket.2, by simpa only [P, one_pow, one_mul] using hwindow⟩

end

end RHTower
