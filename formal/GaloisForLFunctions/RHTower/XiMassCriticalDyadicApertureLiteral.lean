import GaloisForLFunctions.RHTower.XiMassCriticalBesselCarrierBridge
import GaloisForLFunctions.RHTower.MassBesselDyadicAperture
import GaloisForLFunctions.RHTower.XiMassLevinsonPrimeSecantLanding
import GaloisForLFunctions.RHTower.XiMassCriticalTruePrimeCone

/-!
# Literal dyadic subpackets of the critical Xi-mass cone

The deep-time Bessel aperture is not an auxiliary model.  Above the first logarithmic cell it is
identically the corresponding finite dyadic subpacket of the literal damped prime current.  The
conversion uses the existing exact half-density identity
`exp (-log n / 2) = 1 / sqrt n`.
-/

open Complex Filter HTGeometry Topology

namespace RHTower

noncomputable section

/-- The literal damped prime current restricted to one dyadic arithmetic packet. -/
def xiMassCriticalDyadicPrimePacket (a sigma X u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log n)

/-- Above the first cell, the literal dyadic prime packet is the Bessel aperture exactly. -/
theorem xiMassCriticalDyadicPrimePacket_eq_massBesselDyadicAperture
    {a sigma X u : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (hX : 1 ≤ ⌊X⌋₊) :
    xiMassCriticalDyadicPrimePacket a sigma X u = massBesselDyadicAperture a sigma X u := by
  rw [xiMassCriticalDyadicPrimePacket, massBesselDyadicAperture]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnmem := Finset.mem_Ioc.mp hn
  have hnone : 1 < n := lt_of_le_of_lt hX hnmem.1
  have hnpos : 0 < n := lt_trans Nat.zero_lt_one hnone
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hnone)
  rw [xiMassCriticalDampedFourierProfile_eq_massBesselCarrier ha hsigma hlog,
    exp_neg_log_nat_div_two_eq_inv_sqrt hnpos, HTGeometry.apertureSpectralPoint]
  push_cast
  ring

/-- Literal dyadic prime packets are unbounded along the deep-time ray. -/
theorem tendsto_norm_xiMassCriticalDyadicPrimePacket_atTop (a sigma : ℝ)
    (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun X : ℝ => ‖xiMassCriticalDyadicPrimePacket a sigma X (Real.log X ^ (4 : ℕ))‖)
      atTop atTop := by
  refine (tendsto_norm_massBesselDyadicAperture_atTop a sigma ha hsigma).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hfloor : 1 ≤ ⌊X⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast hX
  exact congrArg norm
    (xiMassCriticalDyadicPrimePacket_eq_massBesselDyadicAperture ha hsigma hfloor).symm

/-- The literal packet has the same leading profile as the smooth prime-number-theorem
vacuum.  Its divergence is therefore a bulk effect; this estimate does not control the
centered arithmetic fluctuation. -/
theorem tendsto_xiMassCriticalDyadicPrimePacket_asymptotic (a sigma : ℝ)
    (ha : 0 < a) (hsigma : 0 < sigma) :
    Tendsto (fun X : ℝ =>
        ‖xiMassCriticalDyadicPrimePacket a sigma X (Real.log X ^ (4 : ℕ))
            - massBesselLeading a (apertureSpectralPoint sigma (Real.log X ^ (4 : ℕ)))
              * ((2 * (Real.sqrt 2 - 1) * Real.sqrt X : ℝ) : ℂ)‖
          / (‖massBesselLeading a (apertureSpectralPoint sigma (Real.log X ^ (4 : ℕ)))‖
              * Real.sqrt X))
      atTop (𝓝 0) := by
  refine (tendsto_massBesselDyadicAperture_asymptotic a sigma ha hsigma).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hfloor : 1 ≤ ⌊X⌋₊ := by
    apply Nat.le_floor
    exact_mod_cast hX
  rw [xiMassCriticalDyadicPrimePacket_eq_massBesselDyadicAperture ha hsigma hfloor]

/-- Along the deep-time ray every dyadic label lies inside every admissible moving cone. -/
theorem eventually_dyadic_prime_packet_inside_cone {d : ℝ} (hd : 1 / 2 < d) :
    ∀ᶠ X : ℝ in atTop,
      Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ ⊆
        Finset.Icc 2 ⌊Real.exp (d * Real.log X ^ (4 : ℕ) / (d - 1 / 2))⌋₊ := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (3 : ℝ)] with X hX hL
  have hX0 : 0 < X := by linarith
  have hL0 : 0 ≤ Real.log X := by linarith
  have hLsq : Real.log X + 1 ≤ Real.log X ^ (2 : ℕ) := by nlinarith
  have hLsq1 : 1 ≤ Real.log X ^ (2 : ℕ) := by nlinarith
  have hLpow : Real.log X ^ (2 : ℕ) ≤ Real.log X ^ (4 : ℕ) := by
    nlinarith [mul_nonneg (sq_nonneg (Real.log X)) (sub_nonneg.mpr hLsq1)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hu0 : 0 ≤ Real.log X ^ (4 : ℕ) := by positivity
  have hden : 0 < d - 1 / 2 := by linarith
  have hcone : Real.log X ^ (4 : ℕ) ≤
      d * Real.log X ^ (4 : ℕ) / (d - 1 / 2) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hlog : Real.log (2 * X) ≤
      d * Real.log X ^ (4 : ℕ) / (d - 1 / 2) := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    linarith
  have hXcone : 2 * X ≤
      Real.exp (d * Real.log X ^ (4 : ℕ) / (d - 1 / 2)) :=
    (Real.log_le_iff_le_exp (by linarith : (0 : ℝ) < 2 * X)).mp hlog
  have hfloor : ⌊2 * X⌋₊ ≤
      ⌊Real.exp (d * Real.log X ^ (4 : ℕ) / (d - 1 / 2))⌋₊ :=
    Nat.floor_le_floor hXcone
  have htwo : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  intro n hn
  rw [Finset.mem_Icc]
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.mp hn
  omega

/-- Terms of the moving cone outside the literal dyadic packet. -/
def xiMassCriticalDyadicConeComplement (a sigma d X : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 2
      ⌊Real.exp (d * Real.log X ^ (4 : ℕ) / (d - 1 / 2))⌋₊) \
        (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊),
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma (Real.log X ^ (4 : ℕ)) (Real.log n)

/-- Exact source split when the dyadic packet is contained in the moving cone. -/
theorem xiMassCriticalPrimeAtomConeSum_eq_packet_add_complement
    (a sigma d X : ℝ)
    (hsub : Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ ⊆
      Finset.Icc 2 ⌊Real.exp (d * Real.log X ^ (4 : ℕ) / (d - 1 / 2))⌋₊) :
    xiMassCriticalPrimeAtomConeSum a sigma d (Real.log X ^ (4 : ℕ)) =
      xiMassCriticalDyadicPrimePacket a sigma X (Real.log X ^ (4 : ℕ)) +
        xiMassCriticalDyadicConeComplement a sigma d X := by
  classical
  let u : ℝ := Real.log X ^ (4 : ℕ)
  let M : ℕ := ⌊Real.exp (d * u / (d - 1 / 2))⌋₊
  let f : ℕ → ℂ := fun n =>
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log n)
  have hcone : xiMassCriticalPrimeAtomConeSum a sigma d u =
      ∑ n ∈ Finset.Icc 2 M, f n := by
    calc
      xiMassCriticalPrimeAtomConeSum a sigma d u =
          ∑ n ∈ Finset.Icc 2 M,
            xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) n := by
        rw [xiMassCriticalPrimeAtomConeSum_eq_sum_centeredAtom]
        change (∑ k ∈ Finset.range (M - 1),
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2)) = _
        refine Finset.sum_nbij' (i := fun k => k + 2) (j := fun n => n - 2)
          ?_ ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_range] at hk
          rw [Finset.mem_Icc]
          omega
        · intro n hn
          rw [Finset.mem_Icc] at hn
          rw [Finset.mem_range]
          omega
        · intro k _
          omega
        · intro n hn
          rw [Finset.mem_Icc] at hn
          omega
        · intro k _
          rfl
      _ = ∑ n ∈ Finset.Icc 2 M, f n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        exact (vonMangoldt_mul_dampedProfile_eq_centeredPrimeAtom a sigma u
          (n := n) (by omega)).symm
  rw [hcone]
  change (∑ n ∈ Finset.Icc 2 M, f n) =
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n) +
      ∑ n ∈ (Finset.Icc 2 M) \
        (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊), f n
  simpa only [add_comm] using (Finset.sum_sdiff hsub (f := f)).symm

/-- The source split applies cofinally along the deep-time ray. -/
theorem eventually_xiMassCriticalPrimeAtomConeSum_eq_packet_add_complement
    (a sigma : ℝ) {d : ℝ} (hd : 1 / 2 < d) :
    ∀ᶠ X : ℝ in atTop,
      xiMassCriticalPrimeAtomConeSum a sigma d (Real.log X ^ (4 : ℕ)) =
        xiMassCriticalDyadicPrimePacket a sigma X (Real.log X ^ (4 : ℕ)) +
          xiMassCriticalDyadicConeComplement a sigma d X := by
  filter_upwards [eventually_dyadic_prime_packet_inside_cone hd] with X hsub
  exact xiMassCriticalPrimeAtomConeSum_eq_packet_add_complement a sigma d X hsub

/-- The arithmetic fluctuation inside the dyadic packet, after removing the integer vacuum. -/
def xiMassCriticalDyadicCenteredPacket (a sigma X u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log n)

/-- The rest of the centered arithmetic cone. -/
def xiMassCriticalDyadicCenteredConeComplement (a sigma d X : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 2
      ⌊Real.exp (d * Real.log X ^ (4 : ℕ) / (d - 1 / 2))⌋₊) \
        (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊),
    ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma (Real.log X ^ (4 : ℕ)) (Real.log n)

/-- The RH-equivalent centered source also splits exactly into local and remote fluctuations. -/
theorem xiMassCriticalCenteredAtomConeSum_eq_packet_add_complement
    (a sigma d X : ℝ)
    (hsub : Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ ⊆
      Finset.Icc 2 ⌊Real.exp (d * Real.log X ^ (4 : ℕ) / (d - 1 / 2))⌋₊) :
    xiMassCriticalCenteredAtomConeSum a sigma d (Real.log X ^ (4 : ℕ)) =
      xiMassCriticalDyadicCenteredPacket a sigma X (Real.log X ^ (4 : ℕ)) +
        xiMassCriticalDyadicCenteredConeComplement a sigma d X := by
  classical
  let u : ℝ := Real.log X ^ (4 : ℕ)
  let M : ℕ := ⌊Real.exp (d * u / (d - 1 / 2))⌋₊
  let f : ℕ → ℂ := fun n =>
    ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log n)
  have hcone : xiMassCriticalCenteredAtomConeSum a sigma d u =
      ∑ n ∈ Finset.Icc 2 M, f n := by
    rw [xiMassCriticalCenteredAtomConeSum]
    change (∑ k ∈ Finset.range (M - 1),
      ((ArithmeticFunction.vonMangoldt (k + 2) - 1 : ℝ) : ℂ) *
        xiMassCriticalDampedFourierProfile a sigma u (Real.log ((k : ℝ) + 2))) = _
    refine Finset.sum_nbij' (i := fun k => k + 2) (j := fun n => n - 2)
      ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    · intro k _
      omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      omega
    · intro k _
      congr 2
      push_cast
      ring
  rw [hcone]
  change (∑ n ∈ Finset.Icc 2 M, f n) =
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, f n) +
      ∑ n ∈ (Finset.Icc 2 M) \
        (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊), f n
  simpa only [add_comm] using (Finset.sum_sdiff hsub (f := f)).symm

/-- Cofinal source split at the centered, arithmetic fluctuation level. -/
theorem eventually_xiMassCriticalCenteredAtomConeSum_eq_packet_add_complement
    (a sigma : ℝ) {d : ℝ} (hd : 1 / 2 < d) :
    ∀ᶠ X : ℝ in atTop,
      xiMassCriticalCenteredAtomConeSum a sigma d (Real.log X ^ (4 : ℕ)) =
        xiMassCriticalDyadicCenteredPacket a sigma X (Real.log X ^ (4 : ℕ)) +
          xiMassCriticalDyadicCenteredConeComplement a sigma d X := by
  filter_upwards [eventually_dyadic_prime_packet_inside_cone hd] with X hsub
  exact xiMassCriticalCenteredAtomConeSum_eq_packet_add_complement a sigma d X hsub

end

end RHTower
