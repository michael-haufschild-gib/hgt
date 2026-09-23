import GaloisForLFunctions.RHTower.SemilocalCompressedEulerOrientation
import GaloisForLFunctions.RHTower.XiPrimeSeamReflectionEnergy

/-!
# The fixed two--three prime seam already detects the critical line

The existing semilocal route first makes every prime seam charge equal and then uses cofinal
decay to kill the common value.  The canonical seam values are more rigid than that argument
requires.  Off the critical line their norms at the first two primes satisfy

`\|C_2(rho)\| < \|C_3(rho)\|`.

Consequently equality of only the prime-`2` and prime-`3` charges forces
`re rho = 1 / 2`.  On the Xi divisor this fixed-pair equality is equivalent to RH.  Applying the
finite Calkin injection to the literal packet `![2, 3]` then gives fixed two-source orientation-Gram
and compression-commutator criteria.  No all-prime packet, cofinal limit, or common-charge
normalization remains in these interfaces.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Certified comparison of the two scalar coefficients occurring in the raw seam norms. -/
lemma log_two_sq_div_two_lt_log_three_sq_div_three :
    (Real.log 2) ^ (2 : ℕ) / 2 < (Real.log 3) ^ (2 : ℕ) / 3 := by
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2up := Real.log_two_lt_d9
  have h3low := Real.log_three_gt_d9
  nlinarith

/-- Away from zero, the squared hyperbolic displacement at scale `log 2` is strictly smaller
than at scale `log 3`. -/
lemma sinh_sq_mul_log_two_lt_three {x : ℝ} (hx : x ≠ 0) :
    Real.sinh (x * Real.log 2) ^ (2 : ℕ) <
      Real.sinh (x * Real.log 3) ^ (2 : ℕ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := by
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hpos : 0 < -x := neg_pos.mpr hxneg
    have harg : (-x) * Real.log 2 < (-x) * Real.log 3 :=
      mul_lt_mul_of_pos_left hlog23 hpos
    have hsinh := Real.sinh_strictMono harg
    have hs2pos : 0 < Real.sinh ((-x) * Real.log 2) :=
      Real.sinh_pos_iff.mpr (mul_pos hpos hlog2)
    have hs3pos : 0 < Real.sinh ((-x) * Real.log 3) :=
      Real.sinh_pos_iff.mpr (mul_pos hpos hlog3)
    rw [show x * Real.log 2 = -((-x) * Real.log 2) by ring,
      show x * Real.log 3 = -((-x) * Real.log 3) by ring,
      Real.sinh_neg, Real.sinh_neg]
    nlinarith
  · have harg : x * Real.log 2 < x * Real.log 3 :=
      mul_lt_mul_of_pos_left hlog23 hxpos
    have hsinh := Real.sinh_strictMono harg
    have hs2pos : 0 < Real.sinh (x * Real.log 2) :=
      Real.sinh_pos_iff.mpr (mul_pos hxpos hlog2)
    have hs3pos : 0 < Real.sinh (x * Real.log 3) :=
      Real.sinh_pos_iff.mpr (mul_pos hxpos hlog3)
    nlinarith

/-- Raw norm-square formula for the canonical prime-`2` seam charge. -/
lemma norm_sq_orbitwiseNatPrimeSeamCharge_two (rho : ℂ) :
    ‖orbitwiseNatPrimeSeamCharge 2 rho‖ ^ (2 : ℕ) =
      4 * ((Real.log 2) ^ (2 : ℕ) / 2) *
        Real.sinh ((rho.re - 1 / 2) * Real.log 2) ^ (2 : ℕ) := by
  have h := orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_sinh
    rho (⟨2, by norm_num⟩ : Nat.Primes)
  norm_num at h ⊢
  nlinarith

/-- Raw norm-square formula for the canonical prime-`3` seam charge. -/
lemma norm_sq_orbitwiseNatPrimeSeamCharge_three (rho : ℂ) :
    ‖orbitwiseNatPrimeSeamCharge 3 rho‖ ^ (2 : ℕ) =
      4 * ((Real.log 3) ^ (2 : ℕ) / 3) *
        Real.sinh ((rho.re - 1 / 2) * Real.log 3) ^ (2 : ℕ) := by
  have h := orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_sinh
    rho (⟨3, by norm_num⟩ : Nat.Primes)
  norm_num at h ⊢
  nlinarith

/-- **Two--three strict seam separation.** Off the critical line, the canonical prime-`2` seam
charge has strictly smaller norm than the prime-`3` seam charge.  No strip hypothesis is needed. -/
theorem norm_orbitwiseNatPrimeSeamCharge_two_lt_three_of_re_ne_half
    {rho : ℂ} (hre : rho.re ≠ 1 / 2) :
    ‖orbitwiseNatPrimeSeamCharge 2 rho‖ <
      ‖orbitwiseNatPrimeSeamCharge 3 rho‖ := by
  let x := rho.re - 1 / 2
  have hx : x ≠ 0 := sub_ne_zero.mpr hre
  have hsinh := sinh_sq_mul_log_two_lt_three hx
  have hcoeff := log_two_sq_div_two_lt_log_three_sq_div_three
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog3ne : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hcoeff3pos : 0 < (Real.log 3) ^ (2 : ℕ) / 3 :=
    div_pos (sq_pos_of_ne_zero hlog3ne) (by norm_num)
  have hsinh2pos : 0 < Real.sinh (x * Real.log 2) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr (mul_ne_zero hx hlog2ne))
  have hprod_left :
      (Real.log 2) ^ (2 : ℕ) / 2 * Real.sinh (x * Real.log 2) ^ (2 : ℕ) <
        (Real.log 3) ^ (2 : ℕ) / 3 * Real.sinh (x * Real.log 2) ^ (2 : ℕ) :=
    mul_lt_mul_of_pos_right hcoeff hsinh2pos
  have hprod_right :
      (Real.log 3) ^ (2 : ℕ) / 3 * Real.sinh (x * Real.log 2) ^ (2 : ℕ) <
        (Real.log 3) ^ (2 : ℕ) / 3 * Real.sinh (x * Real.log 3) ^ (2 : ℕ) :=
    mul_lt_mul_of_pos_left hsinh hcoeff3pos
  have hsq : ‖orbitwiseNatPrimeSeamCharge 2 rho‖ ^ (2 : ℕ) <
      ‖orbitwiseNatPrimeSeamCharge 3 rho‖ ^ (2 : ℕ) := by
    rw [norm_sq_orbitwiseNatPrimeSeamCharge_two,
      norm_sq_orbitwiseNatPrimeSeamCharge_three]
    change 4 * ((Real.log 2) ^ (2 : ℕ) / 2) *
          Real.sinh (x * Real.log 2) ^ (2 : ℕ) <
        4 * ((Real.log 3) ^ (2 : ℕ) / 3) *
          Real.sinh (x * Real.log 3) ^ (2 : ℕ)
    nlinarith
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Equality of the two fixed seam charges pins the critical line. -/
theorem re_eq_half_of_orbitwiseNatPrimeSeamCharge_two_eq_three
    {rho : ℂ}
    (hcharge : orbitwiseNatPrimeSeamCharge 2 rho =
      orbitwiseNatPrimeSeamCharge 3 rho) :
    rho.re = 1 / 2 := by
  by_contra hre
  have hlt := norm_orbitwiseNatPrimeSeamCharge_two_lt_three_of_re_ne_half hre
  rw [hcharge] at hlt
  exact lt_irrefl _ hlt

/-- The scalar diagonal-energy gap between the prime-`3` and prime-`2` seam charges. -/
def orbitwisePrimeTwoThreeSeamNormGap (rho : ℂ) : ℝ :=
  ‖orbitwiseNatPrimeSeamCharge 3 rho‖ ^ (2 : ℕ) -
    ‖orbitwiseNatPrimeSeamCharge 2 rho‖ ^ (2 : ℕ)

/-- The fixed two--three diagonal seam gap vanishes on the critical line. -/
theorem orbitwisePrimeTwoThreeSeamNormGap_eq_zero_of_re_eq_half
    {rho : ℂ} (hre : rho.re = 1 / 2) :
    orbitwisePrimeTwoThreeSeamNormGap rho = 0 := by
  rw [orbitwisePrimeTwoThreeSeamNormGap,
    norm_sq_orbitwiseNatPrimeSeamCharge_two,
    norm_sq_orbitwiseNatPrimeSeamCharge_three, hre]
  norm_num

/-- The fixed two--three diagonal seam gap is strictly positive at every off-line point. -/
theorem orbitwisePrimeTwoThreeSeamNormGap_pos_of_re_ne_half
    {rho : ℂ} (hre : rho.re ≠ 1 / 2) :
    0 < orbitwisePrimeTwoThreeSeamNormGap rho := by
  have hlt := norm_orbitwiseNatPrimeSeamCharge_two_lt_three_of_re_ne_half hre
  have hsq := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hlt
  exact sub_pos.mpr hsq

/-- **Positive fixed-pair defect.** The two--three diagonal seam gap is nonnegative everywhere,
and it is zero exactly on the critical line. -/
theorem orbitwisePrimeTwoThreeSeamNormGap_nonneg (rho : ℂ) :
    0 ≤ orbitwisePrimeTwoThreeSeamNormGap rho := by
  by_cases hre : rho.re = 1 / 2
  · rw [orbitwisePrimeTwoThreeSeamNormGap_eq_zero_of_re_eq_half hre]
  · exact (orbitwisePrimeTwoThreeSeamNormGap_pos_of_re_ne_half hre).le

/-- Exact zero set of the positive fixed two--three diagonal seam gap. -/
theorem orbitwisePrimeTwoThreeSeamNormGap_eq_zero_iff (rho : ℂ) :
    orbitwisePrimeTwoThreeSeamNormGap rho = 0 ↔ rho.re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hre
    exact (ne_of_gt (orbitwisePrimeTwoThreeSeamNormGap_pos_of_re_ne_half hre)) hzero
  · exact orbitwisePrimeTwoThreeSeamNormGap_eq_zero_of_re_eq_half

/-- Equality of only the two scalar seam energies already pins the critical line. -/
theorem re_eq_half_of_orbitwiseNatPrimeSeamCharge_two_three_norm_eq
    {rho : ℂ}
    (hnorm : ‖orbitwiseNatPrimeSeamCharge 2 rho‖ =
      ‖orbitwiseNatPrimeSeamCharge 3 rho‖) :
    rho.re = 1 / 2 := by
  apply (orbitwisePrimeTwoThreeSeamNormGap_eq_zero_iff rho).mp
  rw [orbitwisePrimeTwoThreeSeamNormGap, hnorm]
  ring

/-- Equality of the fixed prime-`2` and prime-`3` seam charges on every actual Xi divisor fibre. -/
def XiPrimeTwoThreeSeamChargesEqual : Prop :=
  ∀ rho : XiDivisorSupport,
    orbitwiseNatPrimeSeamCharge 2 (rho : ℂ) =
      orbitwiseNatPrimeSeamCharge 3 (rho : ℂ)

/-- Equality of the fixed prime-`2` and prime-`3` scalar seam energies on every Xi fibre. -/
def XiPrimeTwoThreeSeamNormsEqual : Prop :=
  ∀ rho : XiDivisorSupport,
    ‖orbitwiseNatPrimeSeamCharge 2 (rho : ℂ)‖ =
      ‖orbitwiseNatPrimeSeamCharge 3 (rho : ℂ)‖

/-- The fixed two-prime seam equality is already equivalent to RH.  The forward implication uses
strict norm separation directly, not all-prime coherence or cofinal decay. -/
theorem xiPrimeTwoThreeSeamChargesEqual_iff_riemannHypothesis :
    XiPrimeTwoThreeSeamChargesEqual ↔ RiemannHypothesis := by
  constructor
  · intro hpair
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hright hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hre := re_eq_half_of_orbitwiseNatPrimeSeamCharge_two_eq_three
      (hpair support)
    have hgt : 1 / 2 < rho.re := mem_rightHalf.mp hright
    have hre' : rho.re = 1 / 2 := by simpa [support] using hre
    exact (ne_of_gt hgt) hre'
  · intro hRH rho
    have hre := xi_divisor_support_re_eq_half_of_rh hRH rho
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mpr hre
        2 3 (by norm_num) (by norm_num)

/-- The diagonal two-prime energy equality is equivalent to RH.  This is weaker source data than
complex seam-charge equality: it retains only two nonnegative scalar values. -/
theorem xiPrimeTwoThreeSeamNormsEqual_iff_riemannHypothesis :
    XiPrimeTwoThreeSeamNormsEqual ↔ RiemannHypothesis := by
  constructor
  · intro hnorm
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hright hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hre := re_eq_half_of_orbitwiseNatPrimeSeamCharge_two_three_norm_eq
      (hnorm support)
    have hgt : 1 / 2 < rho.re := mem_rightHalf.mp hright
    have hre' : rho.re = 1 / 2 := by simpa [support] using hre
    exact (ne_of_gt hgt) hre'
  · intro hRH rho
    have hre := xi_divisor_support_re_eq_half_of_rh hRH rho
    have hgap := orbitwisePrimeTwoThreeSeamNormGap_eq_zero_of_re_eq_half hre
    unfold orbitwisePrimeTwoThreeSeamNormGap at hgap
    nlinarith [norm_nonneg (orbitwiseNatPrimeSeamCharge 2 (rho : ℂ)),
      norm_nonneg (orbitwiseNatPrimeSeamCharge 3 (rho : ℂ))]

/-- The fixed packet consisting of precisely the primes `2` and `3`. -/
def primeTwoThreePacket : Fin 2 → ℕ := ![2, 3]

/-- Every entry of the fixed two--three packet is prime. -/
lemma primeTwoThreePacket_prime (i : Fin 2) : (primeTwoThreePacket i).Prime := by
  fin_cases i <;> norm_num [primeTwoThreePacket]

/-- The fixed two--three packet has no repeated entry. -/
lemma primeTwoThreePacket_injective : Function.Injective primeTwoThreePacket := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [primeTwoThreePacket]

/-- The canonical seam coefficient packet at the fixed primes `2` and `3`. -/
def xiPrimeTwoThreeSeamPacket (rho : XiDivisorSupport) : Fin 2 → ℂ :=
  fun i ↦ orbitwiseNatPrimeSeamCharge (primeTwoThreePacket i) (rho : ℂ)

/-- Compactness of the fixed two-prime orientation Gram on every Xi divisor fibre. -/
def XiPrimeTwoThreeEulerOrientationGramCompact (a : ℝ) : Prop :=
  ∀ rho : XiDivisorSupport,
    IsCompactOperator
      (finiteArchimedeanEulerOrientationGram a
        (fun i ↦ (primeTwoThreePacket i : ℝ))
        (xiPrimeTwoThreeSeamPacket rho))

/-- **Fixed-packet Calkin criterion.** For every positive Sonin aperture, compactness of one
two-prime orientation Gram on each Xi fibre is equivalent to RH. -/
theorem xiPrimeTwoThreeEulerOrientationGramCompact_iff_riemannHypothesis
    (a : ℝ) (ha : 0 < a) :
    XiPrimeTwoThreeEulerOrientationGramCompact a ↔ RiemannHypothesis := by
  rw [← xiPrimeTwoThreeSeamChargesEqual_iff_riemannHypothesis]
  constructor
  · intro hcompact rho
    have hconstant :=
      (finitePrimeArchimedeanEulerOrientationGram_isCompactOperator_iff
        a ha primeTwoThreePacket primeTwoThreePacket_prime
        primeTwoThreePacket_injective (xiPrimeTwoThreeSeamPacket rho)).mp
          (hcompact rho)
    simpa [xiPrimeTwoThreeSeamPacket, primeTwoThreePacket] using
      hconstant (0 : Fin 2) (1 : Fin 2)
  · intro hpair rho
    apply (finitePrimeArchimedeanEulerOrientationGram_isCompactOperator_iff
      a ha primeTwoThreePacket primeTwoThreePacket_prime
      primeTwoThreePacket_injective (xiPrimeTwoThreeSeamPacket rho)).mpr
    have h23 := hpair rho
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [xiPrimeTwoThreeSeamPacket, primeTwoThreePacket]

/-- Essential commutation of the seam-weighted and unweighted compressed sources for the single
fixed packet `![2, 3]` on every Xi divisor fibre. -/
def XiPrimeTwoThreeEulerCompressionEssentiallyCommuting (a : ℝ) : Prop :=
  ∀ rho : XiDivisorSupport,
    IsCompactOperator
      (finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ))
          (xiPrimeTwoThreeSeamPacket rho) *
        finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ)) (fun _ ↦ 1) -
        finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ)) (fun _ ↦ 1) *
        finiteArchimedeanEulerCompression a
          (fun i ↦ (primeTwoThreePacket i : ℝ))
          (xiPrimeTwoThreeSeamPacket rho))

/-- **Fixed-packet source criterion.** For every positive aperture, essential commutation of the
two literal compressed Euler sources for only the packet `![2, 3]` is equivalent to RH. -/
theorem xiPrimeTwoThreeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis
    (a : ℝ) (ha : 0 < a) :
    XiPrimeTwoThreeEulerCompressionEssentiallyCommuting a ↔ RiemannHypothesis := by
  rw [← xiPrimeTwoThreeSeamChargesEqual_iff_riemannHypothesis]
  constructor
  · intro hcompact rho
    have hconstant :=
      (finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff
        a ha primeTwoThreePacket primeTwoThreePacket_prime
        primeTwoThreePacket_injective (xiPrimeTwoThreeSeamPacket rho)).mp
          (hcompact rho)
    simpa [xiPrimeTwoThreeSeamPacket, primeTwoThreePacket] using
      hconstant (0 : Fin 2) (1 : Fin 2)
  · intro hpair rho
    apply (finitePrimeArchimedeanEulerCompression_commutator_isCompactOperator_iff
      a ha primeTwoThreePacket primeTwoThreePacket_prime
      primeTwoThreePacket_injective (xiPrimeTwoThreeSeamPacket rho)).mpr
    have h23 := hpair rho
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [xiPrimeTwoThreeSeamPacket, primeTwoThreePacket]

end

end RHTower
