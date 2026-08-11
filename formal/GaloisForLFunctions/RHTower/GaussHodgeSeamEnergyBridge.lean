import GaloisForLFunctions.RHTower.GaussHodgeMassCurrent
import GaloisForLFunctions.RHTower.XiPrimeSeamReflectionEnergy
import GaloisForLFunctions.RHTower.BurnolPrimeDilationCoPoissonQuotient
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# The Hodge mass current is the Burnol seam reflection energy

Two invariants built in different lanes measure the horizontal displacement of a Xi divisor
copy at a prime label: the Gauss-lane Hodge mass current `H(q,p)` — the residue-weighted
odd-square pairing of the two reflection-odd carrier components — and the Burnol FE–Schwarz
seam reflection-energy density `‖seam(p,q)‖²/p`.  This module proves they are one invariant.

The comparison passes through the centered cosh defect `p^t + p^{-t} - 2` at rate
`t = 2·Re - 1`.  The seam density equals `(log p)² p^{-2}` times the defect; the Hodge mass
shape `t·(p^t - p^{-t})` dominates the defect with constant `log p / 2` at every rate and is
dominated by it with constant `2 √p / log p` on the window `|t| ≤ 1`.  Every divisor copy lies
in the open critical strip, so at copies the two-sided equivalence is hypothesis-free.  The
two invariants vanish together, and their common vanishing over the divisor is exactly the
Riemann hypothesis — equivalently, unimodularity of the prime-2 Burnol character on the
divisor.

Two further laws fence the residual open core.  The FE-pair sample of the Burnol prime
character — the holomorphic bilinear channel — is the constant `1`, blind to the divisor, and
no function of it computes the Hermitian sample `‖character‖`: the horizontal information the
mass current measures lies strictly outside the holomorphic sample algebra.  And the full
prime-summed seam energy of a copy equals the convexity second difference of the prime
logarithmic moment curve: the prime side of the mass-zero law is completely evaluated, so what
remains open is only the divisor average of that convexity defect.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Strip placement of the divisor copies -/

/-- Every Xi divisor copy lies in the open critical strip. -/
theorem xiZeroCopy_re_mem_open_unit (q : XiZeroCopy) :
    0 < ((q.1 : ℂ)).re ∧ ((q.1 : ℂ)).re < 1 :=
  xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)

/-- The centered rate of every copy lies in the closed unit window. -/
theorem abs_centeredRate_le_one (q : XiZeroCopy) :
    |primeDepthBVWoldXiCenteredRate q.1| ≤ 1 := by
  obtain ⟨h0, h1⟩ := xiZeroCopy_re_mem_open_unit q
  rw [primeDepthBVWoldXiCenteredRate, abs_le]
  constructor <;> linarith

/-! ## The seam density in centered cosh-defect form -/

/-- The seam reflection-energy density at a nontrivial integer scale, in centered cosh-defect
form: `(log n)² n^{-2} (n^t + n^{-t} - 2)` at rate `t = 2·Re - 1`. -/
theorem orbitwiseNatSeamCharge_weighted_norm_sq_eq_coshDefect
    (rho : ℂ) {n : ℕ} (hn : 1 < n) :
    ‖orbitwiseNatPrimeSeamCharge n rho‖ ^ 2 / (n : ℝ) =
      Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (-2 : ℝ) *
        ((n : ℝ) ^ (2 * rho.re - 1) + (n : ℝ) ^ (-(2 * rho.re - 1)) - 2) := by
  have hp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hn
  rw [orbitwiseNatSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference rho n hn]
  have hA : (n : ℝ) ^ (-(1 + 2 * rho.re)) =
      (n : ℝ) ^ (-2 : ℝ) * (n : ℝ) ^ (-(2 * rho.re - 1)) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hB : (n : ℝ) ^ (-(3 - 2 * rho.re)) =
      (n : ℝ) ^ (-2 : ℝ) * (n : ℝ) ^ (2 * rho.re - 1) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [hA, hB]
  ring

/-- **A seam charge at a nontrivial integer scale vanishes exactly on the critical line.** -/
theorem orbitwiseNatSeamCharge_eq_zero_iff (rho : ℂ) {n : ℕ} (hn : 1 < n) :
    orbitwiseNatPrimeSeamCharge n rho = 0 ↔ rho.re = 1 / 2 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) := lt_trans one_pos hn1
  constructor
  · intro h
    have hnorm : ‖orbitwiseNatPrimeSeamCharge n rho‖ ^ 2 / (n : ℝ) = 0 := by
      rw [h]
      simp
    rw [orbitwiseNatSeamCharge_weighted_norm_sq_eq_coshDefect rho hn] at hnorm
    have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn1).ne'
    have hrp : (n : ℝ) ^ (-2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
    have hdef : (n : ℝ) ^ (2 * rho.re - 1) + (n : ℝ) ^ (-(2 * rho.re - 1)) - 2 = 0 := by
      rcases mul_eq_zero.mp hnorm with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 (pow_ne_zero 2 hlog)
        · exact absurd h2 hrp
      · exact h1
    have ht := (HTGeometry.rpow_add_rpow_neg_sub_two_eq_zero_iff hn1 _).mp hdef
    linarith
  · intro h
    have hzero : ‖orbitwiseNatPrimeSeamCharge n rho‖ ^ 2 / (n : ℝ) = 0 := by
      rw [orbitwiseNatSeamCharge_weighted_norm_sq_eq_coshDefect rho hn]
      have ht : 2 * rho.re - 1 = 0 := by rw [h]; ring
      rw [ht]
      simp
    have hsq : ‖orbitwiseNatPrimeSeamCharge n rho‖ ^ 2 = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right hp.ne'
    rw [sq_eq_zero_iff, norm_eq_zero] at hsq
    exact hsq

/-! ## Two-sided pointwise equivalence with the Hodge mass shape -/

/-- The seam density is dominated by the Hodge mass shape, all rates, constant
`(log n)³ n^{-2} / 2`. -/
theorem seamDensity_le_hodgeMassShape (rho : ℂ) {n : ℕ} (hn : 1 < n) :
    ‖orbitwiseNatPrimeSeamCharge n rho‖ ^ 2 / (n : ℝ) ≤
      Real.log (n : ℝ) ^ 3 * (n : ℝ) ^ (-2 : ℝ) / 2 *
        hodgeMassShape (n : ℝ) (2 * rho.re - 1) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [orbitwiseNatSeamCharge_weighted_norm_sq_eq_coshDefect rho hn, hodgeMassShape]
  have hdef := HTGeometry.rpow_add_rpow_neg_sub_two_le_shape hn1 (2 * rho.re - 1)
  have hw : (0 : ℝ) ≤ Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (-2 : ℝ) := by
    have hp : (0 : ℝ) < (n : ℝ) := lt_trans one_pos hn1
    have := Real.log_nonneg hn1.le
    positivity
  have h1 := mul_le_mul_of_nonneg_left hdef hw
  exact le_trans h1 (le_of_eq (by ring))

/-- At a divisor copy the Hodge mass shape is dominated by the seam density, constant
`2 n^{5/2} / (log n)³` — strip placement supplies the rate window. -/
theorem hodgeMassShape_le_seamDensity (q : XiZeroCopy) {n : ℕ} (hn : 1 < n) :
    hodgeMassShape (n : ℝ) (primeDepthBVWoldXiCenteredRate q.1) ≤
      2 * (n : ℝ) ^ ((5 : ℝ) / 2) / Real.log (n : ℝ) ^ 3 *
        (‖orbitwiseNatPrimeSeamCharge n (q.1 : ℂ)‖ ^ 2 / (n : ℝ)) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp : (0 : ℝ) < (n : ℝ) := lt_trans one_pos hn1
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hrate : primeDepthBVWoldXiCenteredRate q.1 = 2 * ((q.1 : ℂ)).re - 1 := rfl
  rw [orbitwiseNatSeamCharge_weighted_norm_sq_eq_coshDefect _ hn, hodgeMassShape, hrate]
  have hshape := HTGeometry.shape_le_rpow_defect hn1
    (t := 2 * ((q.1 : ℂ)).re - 1) (hrate ▸ abs_centeredRate_le_one q)
  refine le_trans hshape (le_of_eq ?_)
  have hinv : (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (-2 : ℝ) = 1 := by
    rw [← Real.rpow_add hp]
    norm_num
  have h52 : (n : ℝ) ^ ((5 : ℝ) / 2) = (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hp]
    norm_num
  rw [h52]
  calc 2 * (n : ℝ) ^ ((1 : ℝ) / 2) / Real.log (n : ℝ) *
        ((n : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) + (n : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2)
      = 2 * (n : ℝ) ^ ((1 : ℝ) / 2) / Real.log (n : ℝ) *
          ((n : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) + (n : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2) *
          ((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (-2 : ℝ)) := by
        rw [hinv, mul_one]
    _ = 2 * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (2 : ℝ)) / Real.log (n : ℝ) ^ 3 *
          (Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (-2 : ℝ) *
            ((n : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) + (n : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2)) := by
        field_simp
        ring

/-! ## The two-lane bridge at every copy, label, and depth -/

/-- **Seam is dominated by Hodge.**  The residue-weighted seam density is at most the Hodge
mass current times `(log p)³ p^{-2} / 2`. -/
theorem seamDensity_mul_le_gaussHodgeMassCurrent {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    Real.log 2 / 2 * gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p *
        (‖orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ)‖ ^ 2 / ((p : ℕ) : ℝ)) ≤
      Real.log ((p : ℕ) : ℝ) ^ 3 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) / 2 *
        gaussHodgeMassCurrent m q p := by
  have hW : 0 ≤ Real.log 2 / 2 * gaussChannelResidueCurrent m p *
      primeActivationOccupancyFisherDensity p := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hc := gaussChannelResidueCurrent_pos hm p
    have hf := primeActivationOccupancyFisherDensity_pos' p
    positivity
  have hd := seamDensity_le_hodgeMassShape (q.1 : ℂ) p.prop.one_lt
  have h1 := mul_le_mul_of_nonneg_left hd hW
  have hrate : primeDepthBVWoldXiCenteredRate q.1 = 2 * ((q.1 : ℂ)).re - 1 := rfl
  rw [gaussHodgeMassCurrent_eq_boost_square, hrate]
  exact le_trans (le_of_eq (by ring)) (le_trans h1 (le_of_eq (by ring)))

/-- **Hodge is dominated by seam.**  The Hodge mass current is at most the residue-weighted
seam density times `2 p^{5/2} / (log p)³`: with the previous bound, the Gauss-lane Hodge mass
and the Burnol seam energy are one invariant, two-sidedly and unconditionally. -/
theorem gaussHodgeMassCurrent_le_seamDensity_mul {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p ≤
      Real.log 2 / 2 * gaussChannelResidueCurrent m p *
        primeActivationOccupancyFisherDensity p *
        (2 * ((p : ℕ) : ℝ) ^ ((5 : ℝ) / 2) / Real.log ((p : ℕ) : ℝ) ^ 3) *
        (‖orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ)‖ ^ 2 / ((p : ℕ) : ℝ)) := by
  have hW : 0 ≤ Real.log 2 / 2 * gaussChannelResidueCurrent m p *
      primeActivationOccupancyFisherDensity p := by
    have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hc := gaussChannelResidueCurrent_pos hm p
    have hf := primeActivationOccupancyFisherDensity_pos' p
    positivity
  have hd := hodgeMassShape_le_seamDensity q p.prop.one_lt
  have h1 := mul_le_mul_of_nonneg_left hd hW
  rw [gaussHodgeMassCurrent_eq_boost_square]
  exact le_trans (le_of_eq (by ring)) (le_trans h1 (le_of_eq (by ring)))

/-- **Pointwise two-lane unification**: the Hodge mass current and the seam charge vanish
together, at every copy, label, and depth. -/
theorem gaussHodgeMassCurrent_eq_zero_iff_seamCharge_eq_zero {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p = 0 ↔
      orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ) = 0 := by
  rw [gaussHodgeMassCurrent_eq_zero_iff hm,
    orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) p.prop.one_lt]

/-! ## The Riemann hypothesis in seam vocabulary -/

/-- **RH ⟺ the prime-2 seam charge annihilates the divisor.** -/
theorem riemannHypothesis_iff_forall_seamCharge_eq_zero :
    RiemannHypothesis ↔
      ∀ q : XiZeroCopy, orbitwiseNatPrimeSeamCharge 2 (q.1 : ℂ) = 0 := by
  rw [← gaussHodgeMass_vanishing_iff_riemannHypothesis (le_refl 1)]
  constructor
  · intro h q
    rw [orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) one_lt_two,
      ← gaussHodgeMassCurrent_eq_zero_iff (le_refl 1) q ⟨2, Nat.prime_two⟩]
    exact h q ⟨2, Nat.prime_two⟩
  · intro h q p
    rw [gaussHodgeMassCurrent_eq_zero_iff (le_refl 1),
      ← orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) one_lt_two]
    exact h q

/-- The modulus of the Burnol prime character is the exponentiated centered half-rate. -/
theorem norm_burnolPrimeCharacter {p : ℝ} (hp : 0 < p) (s : ℂ) :
    ‖burnolPrimeCharacter p s‖ = p ^ (s.re - 1 / 2) := by
  rw [burnolPrimeCharacter, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.sub_re, Complex.ofReal_re]

/-- **RH as unimodularity of the prime-2 Burnol character on the divisor.** -/
theorem riemannHypothesis_iff_burnolPrimeCharacter_unimodular :
    RiemannHypothesis ↔
      ∀ q : XiZeroCopy, ‖burnolPrimeCharacter 2 (q.1 : ℂ)‖ = 1 := by
  rw [riemannHypothesis_iff_forall_seamCharge_eq_zero]
  refine forall_congr' fun q => ?_
  rw [orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) one_lt_two,
    norm_burnolPrimeCharacter (by norm_num : (0 : ℝ) < 2)]
  constructor
  · intro h
    rw [h, show (1 : ℝ) / 2 - 1 / 2 = 0 from by norm_num, Real.rpow_zero]
  · intro h
    have hneg : (2 : ℝ) ^ (-(((q.1 : ℂ)).re - 1 / 2)) = 1 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), h, inv_one]
    have hdef : (2 : ℝ) ^ (((q.1 : ℂ)).re - 1 / 2) +
        (2 : ℝ) ^ (-(((q.1 : ℂ)).re - 1 / 2)) - 2 = 0 := by
      rw [h, hneg]
      norm_num
    have := (HTGeometry.rpow_add_rpow_neg_sub_two_eq_zero_iff
      (by norm_num : (1 : ℝ) < 2) _).mp hdef
    linarith

/-! ## The information gap: the holomorphic channel is blind -/

/-- The FE-pair (holomorphic bilinear) sample of the Burnol prime character is the constant
`1`, independent of the spectral point: the channel a holomorphic explicit-formula evaluation
reaches is divisor-blind. -/
theorem burnolPrimeCharacter_mul_one_sub {p : ℝ} (hp : 0 < p) (s : ℂ) :
    burnolPrimeCharacter p s * burnolPrimeCharacter p (1 - s) = 1 := by
  have hpC : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [burnolPrimeCharacter, burnolPrimeCharacter, ← Complex.cpow_add _ _ hpC,
    show (s - 1 / 2) + (1 - s - 1 / 2) = 0 from by ring, Complex.cpow_zero]

/-- **The information gap.**  No function of the FE-pair sample computes the Hermitian sample:
the divisor-blind holomorphic channel cannot see the horizontal rate that the Hodge mass
current and the seam energy measure. -/
theorem no_function_of_fePair_computes_hermitian {p : ℝ} (hp : 1 < p) :
    ¬ ∃ F : ℂ → ℝ, ∀ s : ℂ,
        F (burnolPrimeCharacter p s * burnolPrimeCharacter p (1 - s)) =
          ‖burnolPrimeCharacter p s‖ := by
  rintro ⟨F, hF⟩
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have h1 := hF (((1 / 2 : ℝ) : ℂ))
  have h2 := hF (((3 / 2 : ℝ) : ℂ))
  rw [burnolPrimeCharacter_mul_one_sub hp0, norm_burnolPrimeCharacter hp0,
    Complex.ofReal_re, show (1 / 2 : ℝ) - 1 / 2 = 0 from by norm_num,
    Real.rpow_zero] at h1
  rw [burnolPrimeCharacter_mul_one_sub hp0, norm_burnolPrimeCharacter hp0,
    Complex.ofReal_re, show (3 / 2 : ℝ) - 1 / 2 = 1 from by norm_num,
    Real.rpow_one] at h2
  rw [h1] at h2
  exact absurd h2.symm hp.ne'

/-! ## The full prime-summed seam energy at the divisor -/

/-- **RH ⟺ the full prime-summed seam energy annihilates the divisor.** -/
theorem riemannHypothesis_iff_seamEnergy_eq_zero :
    RiemannHypothesis ↔
      ∀ q : XiZeroCopy, orbitwisePrimeSeamWeightedNormSq (q.1 : ℂ) = 0 := by
  rw [riemannHypothesis_iff_forall_seamCharge_eq_zero]
  constructor
  · intro h q
    have hre : ((q.1 : ℂ)).re = 1 / 2 :=
      (orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) one_lt_two).mp (h q)
    have hz : ∀ p : Nat.Primes,
        ‖orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ)‖ ^ 2 / ((p : ℕ) : ℝ) = 0 := by
      intro p
      rw [(orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) p.prop.one_lt).mpr hre]
      simp
    calc orbitwisePrimeSeamWeightedNormSq (q.1 : ℂ)
        = ∑' _p : Nat.Primes, (0 : ℝ) := tsum_congr hz
      _ = 0 := tsum_zero
  · intro h q
    have hstrip := xiZeroCopy_re_mem_open_unit q
    have hlow := primeTwo_reflectionSecondDifference_le_orbitwisePrimeSeamWeightedNormSq hstrip
    rw [h q] at hlow
    have hA : (2 : ℝ) ^ (-(1 + 2 * ((q.1 : ℂ)).re)) =
        (2 : ℝ) ^ (-2 : ℝ) * (2 : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hB : (2 : ℝ) ^ (-(3 - 2 * ((q.1 : ℂ)).re)) =
        (2 : ℝ) ^ (-2 : ℝ) * (2 : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [hA, hB] at hlow
    have hdefnn := HTGeometry.rpow_add_rpow_neg_sub_two_nonneg
      (by norm_num : (0 : ℝ) < 2) (2 * ((q.1 : ℂ)).re - 1)
    have hpos : (0 : ℝ) < Real.log 2 ^ 2 * (2 : ℝ) ^ (-2 : ℝ) := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      positivity
    have hfact : Real.log 2 ^ 2 * (2 : ℝ) ^ (-2 : ℝ) *
        ((2 : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
          (2 : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2) ≤
        Real.log 2 ^ 2 * (2 : ℝ) ^ (-2 : ℝ) * 0 := by
      rw [mul_zero]
      exact le_trans (le_of_eq (by ring)) hlow
    have hdefle := le_of_mul_le_mul_left hfact hpos
    have hdef0 : (2 : ℝ) ^ (2 * ((q.1 : ℂ)).re - 1) +
        (2 : ℝ) ^ (-(2 * ((q.1 : ℂ)).re - 1)) - 2 = 0 :=
      le_antisymm hdefle hdefnn
    have ht := (HTGeometry.rpow_add_rpow_neg_sub_two_eq_zero_iff
      (by norm_num : (1 : ℝ) < 2) _).mp hdef0
    rw [orbitwiseNatSeamCharge_eq_zero_iff (q.1 : ℂ) one_lt_two]
    linarith

/-- The full seam energy of a divisor copy is the convexity second difference of the prime
logarithmic moment curve: the prime side of the mass-zero law is completely evaluated. -/
theorem seamEnergy_at_copy_eq_momentCurve (q : XiZeroCopy) :
    orbitwisePrimeSeamWeightedNormSq (q.1 : ℂ) =
      primeLogSquareMoment (1 + 2 * ((q.1 : ℂ)).re) +
        primeLogSquareMoment (3 - 2 * ((q.1 : ℂ)).re) -
          2 * primeLogSquareMoment 2 :=
  orbitwisePrimeSeamWeightedNormSq_eq_primeLogSquareMoment_secondDifference
    (xiZeroCopy_re_mem_open_unit q)

end

end RHTower
