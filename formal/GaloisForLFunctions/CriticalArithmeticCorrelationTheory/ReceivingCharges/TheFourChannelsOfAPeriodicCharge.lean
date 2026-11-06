import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralChannelScaleDomination
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.MixedChannelDecomposition
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SharpenedMidBandAndCrossBounds
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions

/-!
# The four channels of a periodic coherent charge

A coherent prime charge twisted by a function of `gcd(·, M)` lies in the conductor subspace of `R = M Q`.
So its mixed error against the dilation form splits into four literal channels, each with its own bound
(`exists_gcdTwistedCharge_four_channels`):

* **upward**, `K B V W |t| (1/√log Q + ω_Q(M)/log Q)`, from `exists_literal_coherent_channel_law`;
* **overlap**, `C c² (1 + log R) √((1 + log c)/log N) + C c² R √(log N/N)`;
* **cross**, `C c²/√log N`;
* **center**, `C c (1 + log R)/√log N`.

The last three are multiples of `‖u‖`; the Mertens remainder costs `log 8 + 4` per unit of `‖u‖`.

With `B ≈ e c` and `W ≈ log c`, upward needs `log Q ≫ c² log² c` and overlap needs `c² log R ≪ √log N`.
Their common window `c² ≪ log Q ≪ √log N / c²` is nonempty exactly for `c⁴ ≪ √log N`, that is, below the
eighth root (`eventually_four_channels_small`).
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace
open GaloisForLFunctions.ArithmeticCouplingTheory
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open GaloisForLFunctions.CriticalScaleArithmeticRigidity
open GaloisForLFunctions.CompletedArithmeticForms

/-- A coherent prime charge twisted by a function of `gcd(·, M)`. -/
def gcdTwistedCharge (g : ℕ → ℝ) (M Q : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  g (j.gcd M) * incidencePacket ((Icc 1 Q).filter Nat.Prime) (fun _ => t / primePoleScale Q) j

/-- The twist is periodic. -/
theorem gcdTwist_periodic (g : ℕ → ℝ) (M : ℕ) : Function.Periodic (fun j : ℕ => g (j.gcd M)) M := by
  intro j
  simp only [Nat.gcd_add_self_left]

/-- Scalars pass through the packet vector. -/
theorem packetVector_const_mul (a : ℝ) (F : ℕ → ℝ) (N : ℕ) :
    packetVector (fun j => a * F j) N = a • packetVector F N := by
  ext n
  simp [packetVector, horizonProfileVector, atomAmplitude, mul_div_assoc]

/-- **A gcd-twisted charge lies in the conductor subspace of `M Q`.** -/
theorem packetVector_gcdTwistedCharge_mem (g : ℕ → ℝ) {M Q : ℕ} (hM : 0 < M) (t : ℝ) (N : ℕ) :
    packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N ∈
      conductorSubspace (M * Q) N := by
  obtain ⟨s, hs⟩ : ∃ s, s = t / primePoleScale Q := ⟨_, rfl⟩
  -- one prime of the band
  have hone : ∀ p ∈ (Icc 1 Q).filter Nat.Prime,
      packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ *
        (g (j.gcd M) * ((if p ∣ j then 1 else 0) - 1 / (p : ℝ)))) N ∈
        conductorSubspace (M * Q) N := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have hpQ := (mem_Icc.mp hpI).2
    have hMp : 0 < M * p := Nat.mul_pos hM hpp.pos
    obtain ⟨a, ha⟩ := exists_gcdProfile_normalizedRamanujan_expansion
      (fun d => g (d.gcd M) * ((if p ∣ d then 1 else 0) - 1 / (p : ℝ))) hMp
    have heq : packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ *
        (g (j.gcd M) * ((if p ∣ j then 1 else 0) - 1 / (p : ℝ)))) N =
        ∑ q ∈ (M * p).divisors, a q • normalizedRamanujanHorizonVector q N := by
      ext n
      have hn : 0 < (n : ℕ) := (mem_Icc.mp n.property).1
      have h1 := ha n hn
      simp only at h1
      have hg1 : ((n : ℕ).gcd (M * p)).gcd M = (n : ℕ).gcd M := by
        rw [Nat.gcd_assoc, Nat.gcd_eq_right (Dvd.intro p rfl)]
      have hg2 : p ∣ (n : ℕ).gcd (M * p) ↔ p ∣ (n : ℕ) :=
        ⟨fun h => h.trans (Nat.gcd_dvd_left _ _),
          fun h => Nat.dvd_gcd h (Dvd.intro_left M rfl)⟩
      rw [hg1] at h1
      simp only [hg2] at h1
      simp only [packetVector, horizonProfileVector, atomAmplitude, PiLp.toLp_apply,
        WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        normalizedRamanujanHorizonVector, ramanujanHorizonVector, ramanujanPoleProfile]
      rw [mul_div_assoc, h1, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [heq]
    refine Submodule.sum_mem _ fun q hq => Submodule.smul_mem _ _ ?_
    refine mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨?_, ?_⟩)
    · exact Nat.pos_of_mem_divisors hq
    · exact (Nat.divisor_le hq).trans (Nat.mul_le_mul_left M hpQ)
  -- the whole band
  have hband : packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N =
      ∑ p ∈ (Icc 1 Q).filter Nat.Prime, s • packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ *
        (g (j.gcd M) * ((if p ∣ j then 1 else 0) - 1 / (p : ℝ)))) N := by
    ext n
    simp only [packetVector, horizonProfileVector, atomAmplitude, PiLp.toLp_apply,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      gcdTwistedCharge, incidencePacket, ← hs]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [hband]
  exact Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ (hone p hp)

/-- The overlap, cross and center cost per unit of charge norm. -/
def chargeChannelRate (φ : ℝ → ℝ) (C : ℝ) (c : ℝ) (R N : ℕ) : ℝ :=
  144 * completeWeilPoleShift φ c * (1 + Real.log R) / Real.sqrt (Real.log N) +
    23 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * (c ^ 2 / Real.sqrt (Real.log N)) +
    C * (c ^ 2 * (1 + Real.log R) * Real.sqrt ((1 + Real.log c) / Real.log N) +
      c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N))

/-- **The four channels of a gcd-twisted coherent charge.** -/
theorem exists_gcdTwistedCharge_four_channels {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : 0 < ∫ u, φ u ^ 2) :
    ∃ Q₀ : ℕ, ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N M Q : ℕ, Q₀ ≤ Q →
        (linearPrimeStrip c : ℝ) ≤ Real.sqrt (Real.log Q) → 0 < M → 1 ≤ Real.log N →
        c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N →
        2 ≤ M * Q → (M * Q) ^ 6 ≤ N → 18 * (1 + Real.log ((M * Q : ℕ) : ℝ)) ≤ Real.log N →
        c / N ≤ 1 / 3 →
        (((M * Q) * (M * Q) : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ∀ (g : ℕ → ℝ) (t V : ℝ), 0 ≤ V → (∀ d, |g d| ≤ V) → ∀ G : ℕ → ℝ,
        packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N ∈
          (conductorSubspace 1 N)ᗮ →
        packetVector G N ∈ (conductorSubspace 1 N)ᗮ →
        ⟪packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N,
          packetVector G N⟫ = 0 →
        |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
            (packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N),
            packetVector G N⟫ -
          jumpPairing N (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) G| ≤
        (K * ((linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c) * |t| *
            (1 / Real.sqrt (Real.log Q) + periodBandDivisors Q M / Real.log Q) +
          (chargeChannelRate φ C c (M * Q) N + (Real.log 8 + 4)) *
            ‖packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N‖) *
          ‖packetVector G N‖ := by
  obtain ⟨Q₀, K, hK, hup⟩ := exists_literal_coherent_channel_law hφ hsupp hφ0 hmass
  obtain ⟨C, hC, hover⟩ :=
    exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace_of_four_log hφ hsupp hmass
  refine ⟨Q₀, K, C, hK, hC, ?_⟩
  intro c hc1 N M Q hQ₀ hB hM hlog hscale hR2 hR6 hR18 hwidth hrow g t V hV hg G hu1 hy1 hort
  have hc0 : 0 < c := by linarith only [hc1]
  have hL0 : 0 < Real.log N := by linarith only [hlog]
  have hN1 : 2 ≤ N := by
    by_contra hn
    have hN : N ≤ 1 := by omega
    have hle : Real.log N ≤ 0 := Real.log_nonpos (Nat.cast_nonneg N) (by exact_mod_cast hN)
    linarith only [hle, hL0]
  obtain ⟨F, hFd⟩ : ∃ F, F = fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j :=
    ⟨_, rfl⟩
  rw [← hFd] at hu1 hort ⊢
  have hmem : packetVector F N ∈ conductorSubspace (M * Q) N := by
    rw [hFd]
    exact packetVector_gcdTwistedCharge_mem g hM t N
  obtain ⟨u, hud⟩ : ∃ u, u = packetVector F N := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, y = packetVector G N := ⟨_, rfl⟩
  have hexact := complete_orthogonal_dilation_channels hφ hsupp hmass hc0 hN1 F G hu1 hy1 hort
  rw [hexact, ← hud, ← hyd]
  rw [← hud] at hmem hu1
  rw [← hyd] at hy1
  -- the four channels
  have hcenter := abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
    (completeWeilPoleShift φ c) hR2 hR6 hR18 hmem hu1 hy1
  have hα : |completeWeilPoleShift φ c| = completeWeilPoleShift φ c :=
    abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)
  rw [hα] at hcenter
  have hcrossSq := norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace hφ hsupp hmass hc0
    hR2 (by
      have h46 : (M * Q) ^ 4 ≤ (M * Q) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
      exact h46.trans hR6) hR18 hmem
  have hκ : 0 ≤ 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2) := by positivity
  have hsqrtL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hcross : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u‖ ≤
      23 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * (c ^ 2 / Real.sqrt (Real.log N)) * ‖u‖ := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    refine hcrossSq.trans ?_
    have hLs : c ^ 4 / Real.log N = (c ^ 2 / Real.sqrt (Real.log N)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hL0.le]
      ring
    rw [hLs]
    have hnn : 0 ≤ (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) ^ 2 *
        (c ^ 2 / Real.sqrt (Real.log N)) ^ 2 * ‖u‖ ^ 2 := by positivity
    nlinarith only [hnn]
  have hR2sq : (M * Q) * (M * Q) ≤ N := by
    have h26 : (M * Q) * (M * Q) ≤ (M * Q) ^ 6 := by
      rw [← sq]
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    exact h26.trans hR6
  have hR4log : 4 * Real.log ((M * Q : ℕ) : ℝ) + 18 ≤ Real.log N := by
    have h0 : 0 ≤ Real.log ((M * Q : ℕ) : ℝ) := Real.log_natCast_nonneg _
    linarith only [hR18, h0]
  have hoverlap := hover hR2 hR2sq hR4log hc1 hwidth hrow hmem
  have hupward := hup c hc1 N M Q hQ₀ hB hM hlog hscale (fun j => g (j.gcd M)) t V
    (gcdTwist_periodic g M) hV (fun j => hg _)
  have hupu : upwardPrimeVector φ c N u = upwardPrimeVector φ c N
      ((Real.sqrt (Real.log N))⁻¹ • packetVector
        (fun j => g (j.gcd M) * incidencePacket ((Icc 1 Q).filter Nat.Prime)
          (fun _ => t / primePoleScale Q) j) N) := by
    rw [hud, hFd, ← packetVector_const_mul]
    rfl
  rw [← hupu] at hupward
  have hmert := mertens_remainder_norm N F
  rw [← hud] at hmert
  -- assemble
  have hy0 := norm_nonneg y
  have hu0 := norm_nonneg u
  have t1 := abs_real_inner_le_norm (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u) y
  have t2 := abs_real_inner_le_norm (Matrix.toEuclideanLin (overlapMatrix φ c N) u -
    downwardPrimeVector φ c N u) y
  have t3 := abs_real_inner_le_norm (upwardPrimeVector φ c N u) y
  have t4 := abs_real_inner_le_norm (mertensHorizonRemainder N F) y
  have m1 := mul_le_mul_of_nonneg_right hcross hy0
  have m2 := mul_le_mul_of_nonneg_right hoverlap hy0
  have m3 := mul_le_mul_of_nonneg_right hupward hy0
  have m4 := mul_le_mul_of_nonneg_right hmert hy0
  have hsum : |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, y⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, y⟫ +
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, y⟫ -
      ⟪upwardPrimeVector φ c N u, y⟫ - ⟪mertensHorizonRemainder N F, y⟫| ≤
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) u, y⟫| +
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, y⟫| +
      |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, y⟫| +
      |⟪upwardPrimeVector φ c N u, y⟫| + |⟪mertensHorizonRemainder N F, y⟫| :=
    (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)) le_rfl)
  refine hsum.trans ?_
  unfold chargeChannelRate
  have hexpand : (144 * completeWeilPoleShift φ c * (1 + Real.log ((M * Q : ℕ) : ℝ)) /
      Real.sqrt (Real.log N)) * ‖u‖ * ‖y‖ =
      144 * completeWeilPoleShift φ c * (1 + Real.log ((M * Q : ℕ) : ℝ)) /
        Real.sqrt (Real.log N) * ‖u‖ * ‖y‖ := rfl
  nlinarith only [hcenter, t1, t2, t3, t4, m1, m2, m3, m4]

/-! ### The common window -/

/-- **The channels close below the eighth root.** On a window `2α < β`, `β + 2α < 1/2`, the overlap, cross
and center rates and the upward coefficient are all below `ε`. The window is nonempty exactly for `α < 1/8`. -/
theorem eventually_four_channels_small {φ : ℝ → ℝ} (C : ℝ) {α β ε : ℝ} (hα : 0 < α)
    (h1 : 2 * α < β) (h2 : β + 2 * α < 1 / 2) (hε : 0 < ε) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α → ∀ M Q : ℕ, 0 < M →
      Real.log N ^ β ≤ Real.log Q → Real.log Q ≤ 2 * Real.log N ^ β →
      Real.log M ≤ Real.log N ^ β →
      (periodBandDivisors Q M : ℝ) ≤ Real.sqrt (Real.log Q) →
      (linearPrimeStrip c : ℝ) * literalMultiplierWidth c *
          (1 / Real.sqrt (Real.log Q) + periodBandDivisors Q M / Real.log Q) ≤ ε ∧
        chargeChannelRate φ C c (M * Q) N ≤ ε := by
  sorry

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
