import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralChannelScaleDomination
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.MixedChannelDecomposition
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SharpenedMidBandAndCrossBounds
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.GcdProfilesHaveFiniteRamanujanExpansions
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant

/-!
# The four channels of a periodic coherent charge

A coherent prime charge twisted by a function of `gcd(·, M)` lies in the conductor subspace of `R = M Q`.
So its mixed error against the dilation form splits into four literal channels, each with its own bound
(`exists_gcdTwistedCharge_four_channels`):

* **upward**, `K B V W |t| (1/√log Q + ω_Q(M)/log Q)`, from `exists_literal_coherent_channel_law`;
* **overlap**, `C c² (1 + log R) √((1 + log c)/log N) + C c² R √(log N/N)`;
* **cross**, `C c²/√log N`;
* **center**, `C c (1 + log R)/√log N`.

The last three are multiples of `‖u‖`.

The Mertens remainder is `−γ` times the identity up to a multiplier that is small off the top rows. On an
orthogonal pair the identity drops out, and the top rows carry mass `O(log T / log N)` uniformly in the
conductor (`abs_mertens_inner_le_of_mem_conductorSubspace`).

With `B ≈ e c` and `W ≈ log c`, upward needs `log Q ≫ c² log² c` and overlap needs `c² log R ≪ √log N`.
Their common window `c² ≪ log Q ≪ √log N / c²` is nonempty exactly for `c⁴ ≪ √log N`, that is, below the
eighth root (`eventually_four_channels_small`). On that window the complete form is its jump pairing up to
`ε (V|t| + ‖u‖) ‖y‖` (`eventually_gcdTwistedCharge_mixed_error_small`).
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
          chargeChannelRate φ C c (M * Q) N *
            ‖packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N‖) *
          ‖packetVector G N‖ +
        |⟪mertensHorizonRemainder N
            (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j), packetVector G N⟫| := by
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
  -- assemble
  have hy0 := norm_nonneg y
  have hu0 := norm_nonneg u
  have t1 := abs_real_inner_le_norm (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u) y
  have t2 := abs_real_inner_le_norm (Matrix.toEuclideanLin (overlapMatrix φ c N) u -
    downwardPrimeVector φ c N u) y
  have t3 := abs_real_inner_le_norm (upwardPrimeVector φ c N u) y
  have m1 := mul_le_mul_of_nonneg_right hcross hy0
  have m2 := mul_le_mul_of_nonneg_right hoverlap hy0
  have m3 := mul_le_mul_of_nonneg_right hupward hy0
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
  nlinarith only [hcenter, t1, t2, t3, m1, m2, m3]

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
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by rw [hκd]; positivity
  obtain ⟨κ', hκ'd⟩ : ∃ κ', κ' = 152 * (∫ u, |φ u|) ^ 2 / ∫ u, φ u ^ 2 := ⟨_, rfl⟩
  have hκ' : 0 ≤ κ' := by rw [hκ'd]; positivity
  obtain ⟨w, hwd⟩ : ∃ w, w = 3 + |mertensWindowConstant| + α := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hwd]; positivity
  obtain ⟨γ', hγd⟩ : ∃ γ', γ' = β / 2 - α := ⟨_, rfl⟩
  have hγ : 0 < γ' := by rw [hγd]; linarith only [h1]
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = 1 / 2 - β - 2 * α := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδd]; linarith only [h2]
  have hβ : 0 < β := by linarith only [h1, hα]
  have hβ1 : β < 1 / 2 := by linarith only [h2, hα]
  obtain ⟨C₃, hC₃d⟩ : ∃ C₃, C₃ = 4 * (576 * κ + 23 * κ' + 4 * C) / ε := ⟨_, rfl⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htiny : ∀ᶠ L : ℝ in atTop, C * (L ^ 2 * Real.exp (-(L / 8))) ≤ ε / 4 := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 8))
    have h3 : Tendsto (fun L : ℝ => C * (64 * ((L / 8) ^ 2 * Real.exp (-(L / 8))))) atTop
        (𝓝 (C * (64 * 0))) := (h.const_mul 64).const_mul C
    rw [mul_zero, mul_zero] at h3
    refine (h3.eventually (ge_mem_nhds (by positivity : 0 < ε / 4))).mono fun L hL => ?_
    refine le_trans (le_of_eq ?_) hL
    ring
  have hratio : Tendsto (fun L : ℝ => L ^ (1 - β)) atTop atTop :=
    tendsto_rpow_atTop (by linarith only [hβ1])
  filter_upwards [hLlim.eventually_ge_atTop 2,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hγ (8 * w / ε)),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hδ C₃),
    hLlim.eventually htiny,
    hLlim.eventually (hratio.eventually_ge_atTop 12),
    eventually_ge_atTop 1]
    with N hL2 hupP hP htinyN hr12 hN1
  intro c hc1 hcα M Q hM hQlo hQhi hMhi hω
  obtain ⟨L, hLd⟩ : ∃ L, L = Real.log (N : ℝ) := ⟨_, rfl⟩
  rw [← hLd] at hL2 hupP hP htinyN hr12 hcα hQlo hQhi hMhi
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hL0 : 0 < L := by linarith only [hL2]
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hc0 : 0 < c := by linarith only [hc1]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨a, had⟩ : ∃ a, a = L ^ α := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b, b = L ^ β := ⟨_, rfl⟩
  rw [← had] at hcα
  rw [← hbd] at hQlo hQhi hMhi
  have ha1 : 1 ≤ a := by rw [had]; exact Real.one_le_rpow hL1 hα.le
  have hb1 : 1 ≤ b := by rw [hbd]; exact Real.one_le_rpow hL1 hβ.le
  have ha0 : 0 < a := by linarith only [ha1]
  have hb0 : 0 < b := by linarith only [hb1]
  obtain ⟨P, hPd⟩ : ∃ P, P = L ^ δ := ⟨_, rfl⟩
  obtain ⟨P', hP'd⟩ : ∃ P', P' = L ^ γ' := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hPd]; positivity
  have hP'0 : 0 < P' := by rw [hP'd]; positivity
  have hs : Real.sqrt L = a ^ 2 * b * P := by
    rw [Real.sqrt_eq_rpow, had, hbd, hPd, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0, hδd]
    congr 1
    push_cast
    ring
  have hsqrtb : Real.sqrt b = a * P' := by
    rw [Real.sqrt_eq_rpow, had, hbd, hP'd, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, hγd]
    congr 1
    ring
  have hupP' : 8 * w / ε * (1 + Real.log L) ≤ P' := by
    rw [hP'd]
    simpa only [pow_one] using hupP
  have hP' : C₃ * (1 + Real.log L) ≤ P := by
    rw [hPd]
    simpa only [pow_one] using hP
  have hlogc : Real.log c ≤ α * Real.log L := by
    have h := Real.log_le_log hc0 hcα
    rw [had, Real.log_rpow hL0] at h
    exact h
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  -- the conductor size
  have hlogQ1 : 1 ≤ Real.log Q := hb1.trans hQlo
  have hQ0 : (Q : ℝ) ≠ 0 := by
    intro h
    rw [h, Real.log_zero] at hlogQ1
    linarith only [hlogQ1]
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hlogR : Real.log ((M * Q : ℕ) : ℝ) = Real.log M + Real.log Q := by
    push_cast
    exact Real.log_mul hM0 hQ0
  have hlogM0 : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
  have hR : 1 + Real.log ((M * Q : ℕ) : ℝ) ≤ 4 * b := by
    rw [hlogR]
    linarith only [hb1, hMhi, hQhi]
  have hR0 : 0 ≤ 1 + Real.log ((M * Q : ℕ) : ℝ) := by
    rw [hlogR]
    linarith only [hlogM0, hlogQ1]
  have hsqrtQ : a * P' ≤ Real.sqrt (Real.log Q) := by
    rw [← hsqrtb]
    exact Real.sqrt_le_sqrt hQlo
  have hsqrtQ0 : 0 < Real.sqrt (Real.log Q) := Real.sqrt_pos.mpr (by linarith only [hlogQ1])
  refine ⟨?_, ?_⟩
  · -- the upward coefficient
    have hB : (linearPrimeStrip c : ℝ) ≤ 4 * a := by
      have h1' : (linearPrimeStrip c : ℝ) < c * Real.exp 1 + 1 := by
        unfold linearPrimeStrip
        exact Nat.ceil_lt_add_one (by positivity)
      have he : Real.exp 1 ≤ 3 := by linarith only [Real.exp_one_lt_d9]
      have h3 : c * Real.exp 1 ≤ c * 3 := mul_le_mul_of_nonneg_left he hc0.le
      linarith only [h1', h3, hcα, hc1]
    have hW : literalMultiplierWidth c ≤ w * (1 + Real.log L) := by
      unfold literalMultiplierWidth
      have hpos : 0 ≤ Real.log (2 * c * Real.exp 1) := by
        refine Real.log_nonneg ?_
        have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        nlinarith only [he, hc1]
      rw [abs_of_nonneg hpos, Real.log_mul (by positivity) (Real.exp_pos 1).ne',
        Real.log_mul (by norm_num) hc0.ne', Real.log_exp]
      have hl2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
      have hm := le_abs_self mertensWindowConstant
      have hexpand : w * (1 + Real.log L) = w + w * Real.log L := by ring
      have hww : α * Real.log L ≤ w * Real.log L := by
        refine mul_le_mul_of_nonneg_right ?_ hlogL0
        rw [hwd]
        linarith only [abs_nonneg mertensWindowConstant]
      rw [hexpand]
      have hw2 : w = 3 + |mertensWindowConstant| + α := hwd
      linarith only [hl2, hm, hww, hlogc, hw2, hα]
    have hW0 : 0 ≤ literalMultiplierWidth c := literalMultiplierWidth_nonneg c
    have hfrac : 1 / Real.sqrt (Real.log Q) + periodBandDivisors Q M / Real.log Q ≤
        2 / Real.sqrt (Real.log Q) := by
      have hq : Real.log Q = Real.sqrt (Real.log Q) * Real.sqrt (Real.log Q) :=
        (Real.mul_self_sqrt (by linarith only [hlogQ1])).symm
      have h1' : (periodBandDivisors Q M : ℝ) / Real.log Q ≤ 1 / Real.sqrt (Real.log Q) := by
        rw [div_le_div_iff₀ (by linarith only [hlogQ1]) hsqrtQ0]
        nlinarith only [hω, hsqrtQ0, hq]
      have e2 : 2 / Real.sqrt (Real.log Q) =
          1 / Real.sqrt (Real.log Q) + 1 / Real.sqrt (Real.log Q) := by ring
      linarith only [h1', e2]
    have hfrac2 : 2 / Real.sqrt (Real.log Q) ≤ 2 / (a * P') :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrtQ
    have hfrac0 : 0 ≤ 1 / Real.sqrt (Real.log Q) + periodBandDivisors Q M / Real.log Q := by
      have : 0 ≤ (periodBandDivisors Q M : ℝ) / Real.log Q :=
        div_nonneg (Nat.cast_nonneg _) (by linarith only [hlogQ1])
      positivity
    calc (linearPrimeStrip c : ℝ) * literalMultiplierWidth c *
          (1 / Real.sqrt (Real.log Q) + periodBandDivisors Q M / Real.log Q)
        ≤ (4 * a) * (w * (1 + Real.log L)) * (2 / (a * P')) :=
          mul_le_mul (mul_le_mul hB hW hW0 (by positivity)) (hfrac.trans hfrac2) hfrac0
            (by positivity)
      _ = 8 * w * (1 + Real.log L) / P' := by
          field_simp
          ring
      _ ≤ ε := by
          rw [div_le_iff₀ hP'0]
          have h := (div_mul_eq_mul_div (8 * w) ε (1 + Real.log L)).symm
          have h2 := (div_le_iff₀ hε).mp (h.trans_le hupP')
          linarith only [h2, mul_comm ε P']
  · -- the overlap, cross and center rates
    unfold chargeChannelRate
    have hsL : Real.sqrt (Real.log N) = a ^ 2 * b * P := by rw [← hLd]; exact hs
    have hsL0 : 0 < a ^ 2 * b * P := by positivity
    rw [hsL, ← hLd, ← hκ'd]
    have hshift : completeWeilPoleShift φ c = c * κ := by
      rw [completeWeilPoleShift, hκd, mul_div_assoc]
    rw [hshift]
    have hc2 : c ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hc0.le hcα 2
    have hlog1 : 1 ≤ 1 + Real.log L := by linarith only [hlogL0]
    -- center
    have hcenter : 144 * (c * κ) * (1 + Real.log ((M * Q : ℕ) : ℝ)) / (a ^ 2 * b * P) ≤
        576 * κ / P := by
      rw [div_le_div_iff₀ hsL0 hP0]
      have h1' : c * (1 + Real.log ((M * Q : ℕ) : ℝ)) ≤ a * (4 * b) :=
        mul_le_mul hcα hR hR0 ha0.le
      have h2' : a ≤ a ^ 2 := le_self_pow₀ ha1 (by norm_num)
      have h3 : a * (4 * b) ≤ a ^ 2 * (4 * b) := mul_le_mul_of_nonneg_right h2' (by positivity)
      have h4 := mul_le_mul_of_nonneg_left (h1'.trans h3)
        (show 0 ≤ 144 * κ * P by positivity)
      nlinarith only [h4]
    -- cross
    have hcross : 23 * κ' * (c ^ 2 / (a ^ 2 * b * P)) ≤ 23 * κ' / P := by
      have h1' : c ^ 2 / (a ^ 2 * b * P) ≤ 1 / P := by
        rw [div_le_div_iff₀ hsL0 hP0]
        have h3 : a ^ 2 ≤ a ^ 2 * b := le_mul_of_one_le_right (by positivity) hb1
        nlinarith only [mul_le_mul_of_nonneg_right (hc2.trans h3) hP0.le]
      have h2' := mul_le_mul_of_nonneg_left h1' (show 0 ≤ 23 * κ' by positivity)
      refine h2'.trans_eq ?_
      ring
    -- overlap
    have hsqrtrate : Real.sqrt ((1 + Real.log c) / L) ≤ (1 + Real.log L) / (a ^ 2 * b * P) := by
      rw [Real.sqrt_div (by linarith only [hlogc0]), hs]
      refine div_le_div_of_nonneg_right ?_ hsL0.le
      have h1' : 1 + Real.log c ≤ (1 + Real.log L) ^ 2 := by
        have hle : Real.log c ≤ Real.log L := Real.log_le_log hc0 (hcα.trans (by
          rw [had]
          calc L ^ α ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [h2, hβ])
            _ = L := Real.rpow_one L))
        nlinarith only [hle, hlog1, hlogL0]
      calc Real.sqrt (1 + Real.log c) ≤ Real.sqrt ((1 + Real.log L) ^ 2) := Real.sqrt_le_sqrt h1'
        _ = 1 + Real.log L := Real.sqrt_sq (by linarith only [hlog1])
    have hover1 : c ^ 2 * (1 + Real.log ((M * Q : ℕ) : ℝ)) * Real.sqrt ((1 + Real.log c) / L) ≤
        4 * (1 + Real.log L) / P := by
      have h0 : 0 ≤ Real.sqrt ((1 + Real.log c) / L) := Real.sqrt_nonneg _
      have h1' : c ^ 2 * (1 + Real.log ((M * Q : ℕ) : ℝ)) ≤ a ^ 2 * (4 * b) :=
        mul_le_mul hc2 hR hR0 (by positivity)
      have h2' := mul_le_mul h1' hsqrtrate h0 (by positivity)
      refine h2'.trans_eq ?_
      field_simp
    -- the terminal scale
    have hover2 : C * (c ^ 2 * ((M * Q : ℕ) : ℝ) * Real.sqrt (L / N)) ≤ ε / 4 := by
      have hN : (N : ℝ) = Real.exp L := by rw [hLd, Real.exp_log hN0]
      have hb4 : 3 * b ≤ L / 4 := by
        have h1' : (12 : ℝ) ≤ L ^ (1 - β) := hr12
        have hsplit : L = L ^ (1 - β) * b := by
          rw [hbd, ← Real.rpow_add hL0]
          norm_num
        nlinarith only [mul_le_mul_of_nonneg_right h1' hb0.le, hsplit]
      have hRle : ((M * Q : ℕ) : ℝ) ≤ Real.exp (L / 4) := by
        have hRpos : (0 : ℝ) < ((M * Q : ℕ) : ℝ) := by
          push_cast
          have hM' : (0 : ℝ) < M := by exact_mod_cast hM
          have hQ' : (0 : ℝ) < Q := lt_of_le_of_ne (Nat.cast_nonneg Q) (Ne.symm hQ0)
          exact mul_pos hM' hQ'
        rw [← Real.exp_log hRpos]
        refine Real.exp_le_exp.mpr ?_
        rw [hlogR]
        linarith only [hMhi, hQhi, hb4]
      have hca : c ^ 2 ≤ L := by
        have hle : c ≤ L ^ (1 / 2 : ℝ) := hcα.trans (by
          rw [had]
          exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [h2, hβ]))
        have h3 := pow_le_pow_left₀ hc0.le hle 2
        have e : (L ^ (1 / 2 : ℝ)) ^ 2 = L := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
          norm_num
        rwa [e] at h3
      have hsqrt : Real.sqrt (L / N) ≤ L * Real.exp (-(L / 2)) := by
        rw [hN, Real.sqrt_le_left (by positivity)]
        have h1' : L / Real.exp L ≤ (L * Real.exp (-(L / 2))) ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]
          have e : ((2 : ℕ) : ℝ) * (-(L / 2)) = -L := by push_cast; ring
          rw [e, Real.exp_neg, div_eq_mul_inv]
          have hLL : L ≤ L ^ 2 := le_self_pow₀ hL1 (by norm_num)
          exact mul_le_mul_of_nonneg_right hLL (by positivity)
        exact h1'
      have hprod : c ^ 2 * ((M * Q : ℕ) : ℝ) * Real.sqrt (L / N) ≤
          L * Real.exp (L / 4) * (L * Real.exp (-(L / 2))) :=
        mul_le_mul (mul_le_mul hca hRle (by positivity) hL0.le) hsqrt (Real.sqrt_nonneg _)
          (by positivity)
      have he : L * Real.exp (L / 4) * (L * Real.exp (-(L / 2))) ≤ L ^ 2 * Real.exp (-(L / 8)) := by
        have h1' : Real.exp (L / 4) * Real.exp (-(L / 2)) ≤ Real.exp (-(L / 8)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith only [hL0])
        have h2' := mul_le_mul_of_nonneg_left h1' (sq_nonneg L)
        refine le_trans (le_of_eq ?_) h2'
        ring
      have h3 := mul_le_mul_of_nonneg_left (hprod.trans he) hC.le
      exact h3.trans htinyN
    -- assembly
    have hsum : 576 * κ / P + 23 * κ' / P + C * (4 * (1 + Real.log L) / P) ≤ ε / 4 := by
      have e : 576 * κ / P + 23 * κ' / P + C * (4 * (1 + Real.log L) / P) =
          (576 * κ + 23 * κ' + 4 * C * (1 + Real.log L)) / P := by
        field_simp
      rw [e, div_le_iff₀ hP0]
      have hnum : 576 * κ + 23 * κ' + 4 * C * (1 + Real.log L) ≤
          (576 * κ + 23 * κ' + 4 * C) * (1 + Real.log L) := by
        have h1' : 576 * κ * 1 ≤ 576 * κ * (1 + Real.log L) :=
          mul_le_mul_of_nonneg_left hlog1 (by positivity)
        have h3 : 23 * κ' * 1 ≤ 23 * κ' * (1 + Real.log L) :=
          mul_le_mul_of_nonneg_left hlog1 (by positivity)
        nlinarith only [h1', h3]
      have hC3 : (576 * κ + 23 * κ' + 4 * C) * (1 + Real.log L) ≤ ε / 4 * P := by
        have h := mul_le_mul_of_nonneg_left hP' (show 0 ≤ ε / 4 by positivity)
        rw [hC₃d] at h
        refine le_trans (le_of_eq ?_) h
        field_simp
      linarith only [hnum, hC3]
    have hoverlap := mul_le_mul_of_nonneg_left hover1 hC.le
    have hq : C * (c ^ 2 * (1 + Real.log ((M * Q : ℕ) : ℝ)) * Real.sqrt ((1 + Real.log c) / L) +
        c ^ 2 * ((M * Q : ℕ) : ℝ) * Real.sqrt (L / N)) =
        C * (c ^ 2 * (1 + Real.log ((M * Q : ℕ) : ℝ)) * Real.sqrt ((1 + Real.log c) / L)) +
          C * (c ^ 2 * ((M * Q : ℕ) : ℝ) * Real.sqrt (L / N)) := by ring
    rw [hq]
    linarith only [hcenter, hcross, hoverlap, hover2, hsum, hε]

/-! ### The Mertens channel -/

/-- The Mertens row multiplier tends to `−γ` as the quotient `N/n` grows. -/
theorem exists_abs_mertensRow_add_gamma_le {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ N n : ℕ, 1 ≤ n → 1 ≤ N → T ≤ (N : ℝ) / n →
      |ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n - Real.log N +
        Real.eulerMascheroniConstant| ≤ ε := by
  obtain ⟨T₀, hT₀⟩ := mem_atTop_sets.mp (tendsto_def.mp
    _root_.RHTower.tendsto_real_sum_vonMangoldt_div_sub_log _ (Metric.closedBall_mem_nhds _ hε))
  refine ⟨max 1 T₀, le_max_left _ _, fun N n hn hN hT => ?_⟩
  have hx : dist ((∑ k ∈ Icc 0 ⌊(N : ℝ) / n⌋₊, ArithmeticFunction.vonMangoldt k / (k : ℝ)) -
      Real.log ((N : ℝ) / n)) (-Real.eulerMascheroniConstant) ≤ ε :=
    hT₀ _ ((le_max_right _ _).trans hT)
  have hsum : ∑ k ∈ Icc 0 (N / n), ArithmeticFunction.vonMangoldt k / (k : ℝ) =
      ArithmeticCouplingTheory.mertensSum (N / n) := by
    unfold ArithmeticCouplingTheory.mertensSum
    symm
    refine sum_subset (fun k hk => mem_Icc.mpr ⟨Nat.zero_le _, (mem_Icc.mp hk).2⟩) fun k hk hk' => ?_
    have hk0 : k = 0 := by
      by_contra h
      exact hk' (mem_Icc.mpr ⟨Nat.pos_of_ne_zero h, (mem_Icc.mp hk).2⟩)
    simp [hk0]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.dist_eq, sub_neg_eq_add, Nat.floor_div_eq_div, hsum, Real.log_div hN0 hn0] at hx
  refine le_trans (le_of_eq ?_) hx
  congr 1
  ring

/-- The uniform ceiling of the centered Mertens row multiplier. -/
def mertensRowCeiling : ℝ := Real.log 8 + 4 + Real.eulerMascheroniConstant

theorem mertensRowCeiling_pos : 0 < mertensRowCeiling := by
  have h8 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  unfold mertensRowCeiling
  linarith only [h8, hγ]

/-- **On orthogonal pairs the Mertens channel is small, uniformly in the conductor.** The identity part `−γ`
drops out; what remains is at most `ε` off the rows `N/n < T`, whose mass is `O(log T / log N)`. -/
theorem abs_mertens_inner_le_of_mem_conductorSubspace {ε T : ℝ} (hε : 0 ≤ ε) (hT : 1 ≤ T)
    (hrow : ∀ N n : ℕ, 1 ≤ n → 1 ≤ N → T ≤ (N : ℝ) / n →
      |ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n - Real.log N +
        Real.eulerMascheroniConstant| ≤ ε)
    {R N : ℕ} (hR : 2 ≤ R) (hRNT : ((R * R : ℕ) + 1 : ℝ) * T ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (F : ℕ → ℝ)
    (hu : packetVector F N ∈ conductorSubspace R N)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex N)) (hort : ⟪packetVector F N, y⟫ = 0) :
    |⟪mertensHorizonRemainder N F, y⟫| ≤
      (ε + mertensRowCeiling * Real.sqrt (2 * (Real.log (2 * T) + 3) / Real.log N)) *
        ‖packetVector F N‖ * ‖y‖ := by
  have hL : 0 < Real.log N := by
    have h0 := Real.log_natCast_nonneg R
    linarith only [hlog, h0]
  obtain ⟨r, hrd⟩ : ∃ r : ℕ → ℝ, r = fun n =>
      ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n - Real.log N +
        Real.eulerMascheroniConstant := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, w = packetVector (fun n => r n * F n) N := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u, u = packetVector F N := ⟨_, rfl⟩
  have hsplit : mertensHorizonRemainder N F = w - Real.eulerMascheroniConstant • u := by
    rw [hwd, hud, hrd]
    ext n
    change (ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n - Real.log N) * F n /
        Real.sqrt n =
      (ArithmeticCouplingTheory.mertensSum (N / n) + Real.log n - Real.log N +
        Real.eulerMascheroniConstant) * F n / Real.sqrt n -
        Real.eulerMascheroniConstant * (F n / Real.sqrt n)
    ring
  rw [← hud] at hort hu ⊢
  have hinner : ⟪mertensHorizonRemainder N F, y⟫ = ⟪w, y⟫ := by
    rw [hsplit, inner_sub_left, real_inner_smul_left, hort, mul_zero, sub_zero]
  rw [hinner]
  have hθ0 : 0 ≤ 2 * (Real.log (2 * T) + 3) / Real.log N := by
    have h2T := Real.log_nonneg (by linarith only [hT] : (1 : ℝ) ≤ 2 * T)
    positivity
  obtain ⟨θ, hθd⟩ : ∃ θ, θ = 2 * (Real.log (2 * T) + 3) / Real.log N := ⟨_, rfl⟩
  rw [← hθd] at hθ0 ⊢
  -- the mass of the top rows
  have htop : ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T), F n ^ 2 / (n : ℝ) ≤
      θ * ‖u‖ ^ 2 := by
    have h := sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hT hRNT hlog hu
    have hcongr : ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
        primeHorizonExtension u n ^ 2 =
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T), F n ^ 2 / (n : ℝ) := by
      refine sum_congr rfl fun n hn => ?_
      have hnI := (mem_filter.mp hn).1
      rw [primeHorizonExtension_coe u ⟨n, hnI⟩, hud]
      change (F n / Real.sqrt n) ^ 2 = _
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [hcongr] at h
    rw [hθd, div_mul_eq_mul_div, le_div_iff₀ hL]
    linarith only [h]
  obtain ⟨S, hSd⟩ : ∃ S, S = ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T),
      F n ^ 2 / (n : ℝ) := ⟨_, rfl⟩
  rw [← hSd] at htop
  have hC := mertensRowCeiling_pos
  have hrowle : ∀ n ∈ Icc 1 N, (r n * F n) ^ 2 / (n : ℝ) ≤
      ε ^ 2 * (F n ^ 2 / (n : ℝ)) +
        (if (N : ℝ) / n < T then mertensRowCeiling ^ 2 * (F n ^ 2 / (n : ℝ)) else 0) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hfrac : 0 ≤ F n ^ 2 / (n : ℝ) := by positivity
    rw [mul_pow, mul_div_assoc]
    split_ifs with hbad
    · have hb := mertens_horizon_row_bound hn
      have hγ := Real.one_half_lt_eulerMascheroniConstant
      have habs : |r n| ≤ mertensRowCeiling := by
        rw [hrd]
        unfold mertensRowCeiling
        refine (abs_add_le _ _).trans (add_le_add hb (le_of_eq ?_))
        exact abs_of_pos (by linarith only [hγ])
      have hsq : r n ^ 2 ≤ mertensRowCeiling ^ 2 := by
        rw [← sq_abs (r n)]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      have h1 := mul_le_mul_of_nonneg_right hsq hfrac
      have h2 : 0 ≤ ε ^ 2 * (F n ^ 2 / (n : ℝ)) := by positivity
      linarith only [h1, h2]
    · have hgood := hrow N n hn1 (hn1.trans hnN) (not_lt.mp hbad)
      have hsq : r n ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs (r n), hrd]
        exact pow_le_pow_left₀ (abs_nonneg _) hgood 2
      have h1 := mul_le_mul_of_nonneg_right hsq hfrac
      linarith only [h1]
  have hw2 : ‖w‖ ^ 2 ≤ (ε ^ 2 + mertensRowCeiling ^ 2 * θ) * ‖u‖ ^ 2 := by
    have hnormu : ‖u‖ ^ 2 = ∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) := by
      rw [hud, packetVector_norm_sq]
    have hsum : ∑ n ∈ Icc 1 N, (ε ^ 2 * (F n ^ 2 / (n : ℝ)) +
        (if (N : ℝ) / n < T then mertensRowCeiling ^ 2 * (F n ^ 2 / (n : ℝ)) else 0)) =
        ε ^ 2 * ‖u‖ ^ 2 + mertensRowCeiling ^ 2 * S := by
      rw [sum_add_distrib, ← mul_sum, ← hnormu, ← sum_filter, ← mul_sum, ← hSd]
    have hle := sum_le_sum hrowle
    rw [hsum, ← packetVector_norm_sq, ← hwd] at hle
    have hS := mul_le_mul_of_nonneg_left htop (sq_nonneg mertensRowCeiling)
    linarith only [hle, hS]
  have hsθ : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ0
  have hsθ0 := Real.sqrt_nonneg θ
  have hwle : ‖w‖ ≤ (ε + mertensRowCeiling * Real.sqrt θ) * ‖u‖ := by
    refine (abs_le_of_sq_le_sq' (hw2.trans ?_) (by positivity)).2
    have hexpand : ((ε + mertensRowCeiling * Real.sqrt θ) * ‖u‖) ^ 2 =
        (ε ^ 2 + 2 * ε * (mertensRowCeiling * Real.sqrt θ) +
          mertensRowCeiling ^ 2 * Real.sqrt θ ^ 2) * ‖u‖ ^ 2 := by ring
    rw [hexpand, hsθ]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h2 : 0 ≤ 2 * ε * (mertensRowCeiling * Real.sqrt θ) := by positivity
    linarith only [h2]
  exact (abs_real_inner_le_norm w y).trans (mul_le_mul_of_nonneg_right hwle (norm_nonneg y))

/-! ### The mixed law on the window -/

/-- **On the window below the eighth root the complete form is its jump pairing.** For gcd-twisted coherent
charges, with vectors orthogonal to `V₁` and to each other, all five channels together cost at most
`ε (V|t| + ‖u‖) ‖y‖`, uniformly in the overlap, the period, the band, the twist and the amplitude. -/
theorem eventually_gcdTwistedCharge_mixed_error_small {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : 0 < ∫ u, φ u ^ 2) {α β ε : ℝ} (hα : 0 < α)
    (h1 : 2 * α < β) (h2 : β + 2 * α < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α → ∀ M Q : ℕ, 0 < M →
      Real.log N ^ β ≤ Real.log Q → Real.log Q ≤ 2 * Real.log N ^ β →
      Real.log M ≤ Real.log N ^ β →
      (periodBandDivisors Q M : ℝ) ≤ Real.sqrt (Real.log Q) →
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
      ε * (V * |t| +
        ‖packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N‖) *
        ‖packetVector G N‖ := by
  obtain ⟨Q₀, K, C, hK, hC, hlaw⟩ := exists_gcdTwistedCharge_four_channels hφ hsupp hφ0 hmass
  have hK1 : 0 < K + 1 := by linarith only [hK]
  obtain ⟨ε', hε'd⟩ : ∃ ε', ε' = ε / (3 * (K + 1)) := ⟨_, rfl⟩
  have hε' : 0 < ε' := by rw [hε'd]; positivity
  have hKε : (K + 1) * ε' = ε / 3 := by rw [hε'd]; field_simp
  obtain ⟨T, hT1, hrow⟩ := exists_abs_mertensRow_add_gamma_le (ε := ε / 3) (by positivity)
  have hβ : 0 < β := by linarith only [h1, hα]
  have hβ1 : β < 1 / 2 := by linarith only [h2, hα]
  have hA0 : 0 ≤ 2 * (Real.log (2 * T) + 3) := by
    have h2T := Real.log_nonneg (by linarith only [hT1] : (1 : ℝ) ≤ 2 * T)
    positivity
  have hCM := mertensRowCeiling_pos
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrat : ∀ᶠ L : ℝ in atTop, (120 : ℝ) ≤ L ^ (1 - β) :=
    (tendsto_rpow_atTop (by linarith only [hβ1])).eventually_ge_atTop 120
  have hfour : ∀ᶠ L : ℝ in atTop, (4 : ℝ) ≤ L ^ (β / 2 - α) :=
    (tendsto_rpow_atTop (by linarith only [h1])).eventually_ge_atTop 4
  have hexpQ : ∀ᶠ L : ℝ in atTop, (Q₀ : ℝ) ≤ Real.exp (L ^ β) :=
    (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hβ)).eventually_ge_atTop _
  have hexp2 : ∀ᶠ L : ℝ in atTop, (24 : ℝ) ≤ Real.exp (L / 2) / (L / 2) ^ 2 :=
    ((Real.tendsto_exp_div_pow_atTop 2).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).eventually_ge_atTop 24
  have hexpT : ∀ᶠ L : ℝ in atTop, 2 * T ≤ Real.exp (L / 2) :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).eventually_ge_atTop _
  filter_upwards [eventually_four_channels_small (φ := φ) C hα h1 h2 hε' hC,
    hLlim.eventually hrat, hLlim.eventually hfour, hLlim.eventually hexpQ, hLlim.eventually hexp2,
    hLlim.eventually hexpT,
    hLlim.eventually_ge_atTop (2 * (Real.log (2 * T) + 3) * (3 * mertensRowCeiling / ε) ^ 2),
    hLlim.eventually_ge_atTop 36] with N hs hr hf hq he ht hth hL36
  intro c hc1 hcα M Q hM hQlo hQhi hMhi hω g t V hV hg G hu1 hy1 hort
  obtain ⟨hup, hrate⟩ := hs c hc1 hcα M Q hM hQlo hQhi hMhi hω
  obtain ⟨L, hLd⟩ : ∃ L, L = Real.log (N : ℝ) := ⟨_, rfl⟩
  rw [← hLd] at hr hf hq he ht hth hL36 hcα hQlo hQhi hMhi
  have hL1 : 1 ≤ L := by linarith only [hL36]
  have hL0 : 0 < L := by linarith only [hL36]
  have hN0 : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hLd
      linarith only [hL0, hLd]
    · exact_mod_cast h
  have hNexp : (N : ℝ) = Real.exp L := by rw [hLd, Real.exp_log hN0]
  have hc0 : 0 < c := by linarith only [hc1]
  obtain ⟨a, had⟩ : ∃ a, a = L ^ α := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b, b = L ^ β := ⟨_, rfl⟩
  rw [← had] at hcα
  rw [← hbd] at hQlo hQhi hMhi hq
  have hb1 : 1 ≤ b := by rw [hbd]; exact Real.one_le_rpow hL1 hβ.le
  have hb0 : 0 < b := by linarith only [hb1]
  have ha0 : 0 < a := by linarith only [hcα, hc1]
  have haL : a ≤ L := by
    rw [had]
    calc L ^ α ≤ L ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [h1, h2])
      _ = L := Real.rpow_one L
  have hcL : c ≤ L := hcα.trans haL
  have hsplit : L = L ^ (1 - β) * b := by
    rw [hbd, ← Real.rpow_add hL0]
    norm_num
  have h120 : 120 * b ≤ L := by
    have h := mul_le_mul_of_nonneg_right hr hb0.le
    rw [← hsplit] at h
    exact h
  -- the band and the period
  have hlogQ1 : 1 ≤ Real.log Q := hb1.trans hQlo
  have hQ0 : (0 : ℝ) < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogQ1
      linarith only [hlogQ1]
    · exact_mod_cast h
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hQlow : Real.exp b ≤ Q := by
    calc Real.exp b ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr hQlo
      _ = Q := Real.exp_log hQ0
  have hQle : (Q : ℝ) ≤ Real.exp (2 * b) := by
    calc (Q : ℝ) = Real.exp (Real.log Q) := (Real.exp_log hQ0).symm
      _ ≤ _ := Real.exp_le_exp.mpr hQhi
  have hMle : (M : ℝ) ≤ Real.exp b := by
    calc (M : ℝ) = Real.exp (Real.log M) := (Real.exp_log hM0).symm
      _ ≤ _ := Real.exp_le_exp.mpr hMhi
  have hQ₀Q : Q₀ ≤ Q := by exact_mod_cast hq.trans hQlow
  have hQ2 : 2 ≤ Q := by
    have h2e : (2 : ℝ) ≤ Real.exp b := by
      have h := Real.add_one_le_exp b
      linarith only [h, hb1]
    exact_mod_cast h2e.trans hQlow
  have hR2 : 2 ≤ M * Q := hQ2.trans (Nat.le_mul_of_pos_left Q hM)
  have hMQ : (M : ℝ) * Q ≤ Real.exp (3 * b) := by
    calc (M : ℝ) * Q ≤ Real.exp b * Real.exp (2 * b) :=
          mul_le_mul hMle hQle hQ0.le (Real.exp_pos _).le
      _ = Real.exp (3 * b) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hMQ0 : 0 ≤ (M : ℝ) * Q := by positivity
  -- polynomial factors against half the exponent
  have h6L : 6 * L ^ 2 ≤ Real.exp (L / 2) := by
    have h := (le_div_iff₀ (by positivity)).mp he
    linarith only [h, sq L]
  have h3L : 3 * L * (L + 1) ≤ Real.exp (L / 2) := by nlinarith only [h6L, hL1]
  have h34L : 34 * L ≤ Real.exp (L / 2) := by nlinarith only [h6L, hL36]
  have hhalf : Real.exp (L / 2) * Real.exp (L / 2) = (N : ℝ) := by
    rw [hNexp, ← Real.exp_add]
    congr 1
    ring
  have hexp6 : Real.exp (6 * b) ≤ Real.exp (L / 2) :=
    Real.exp_le_exp.mpr (by linarith only [h120, hb0])
  have hsq : (((M * Q) * (M * Q) : ℕ) : ℝ) ≤ Real.exp (6 * b) := by
    push_cast
    calc (M : ℝ) * Q * ((M : ℝ) * Q) ≤ Real.exp (3 * b) * Real.exp (3 * b) :=
          mul_le_mul hMQ hMQ hMQ0 (Real.exp_pos _).le
      _ = Real.exp (6 * b) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hone : (1 : ℝ) ≤ Real.exp (6 * b) := Real.one_le_exp (by positivity)
  have hsqone : (((M * Q) * (M * Q) : ℕ) + 1 : ℝ) ≤ 2 * Real.exp (6 * b) := by
    linarith only [hsq, hone]
  have hsqone0 : (0 : ℝ) ≤ (((M * Q) * (M * Q) : ℕ) + 1 : ℝ) := by positivity
  -- the side conditions of the law
  have hB : (linearPrimeStrip c : ℝ) ≤ Real.sqrt (Real.log Q) := by
    have hsqrtb : Real.sqrt b = a * L ^ (β / 2 - α) := by
      rw [Real.sqrt_eq_rpow, had, hbd, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
      congr 1
      ring
    have h4 : 4 * a ≤ Real.sqrt b := by
      rw [hsqrtb]
      nlinarith only [mul_le_mul_of_nonneg_left hf ha0.le]
    have hstrip : (linearPrimeStrip c : ℝ) < c * Real.exp 1 + 1 := by
      unfold linearPrimeStrip
      exact Nat.ceil_lt_add_one (by positivity)
    have he3 : Real.exp 1 ≤ 3 := by linarith only [Real.exp_one_lt_d9]
    have hc3 : c * Real.exp 1 ≤ c * 3 := mul_le_mul_of_nonneg_left he3 hc0.le
    have hmono := Real.sqrt_le_sqrt hQlo
    linarith only [hstrip, hc3, hcα, hc1, h4, hmono]
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by rw [← hLd]; exact hL1
  have hscale : c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈Real.log N⌉₊ ≤ N := by
    rw [← hLd]
    have he3 : Real.exp 1 ≤ 3 := by linarith only [Real.exp_one_lt_d9]
    have hceil : (⌈L⌉₊ : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL0.le).le
    have hQ5 : (Q : ℝ) ^ 5 ≤ Real.exp (2 * b) ^ 5 := pow_le_pow_left₀ hQ0.le hQle 5
    have hE : Real.exp b * Real.exp (2 * b) ^ 5 = Real.exp (11 * b) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    calc c * Real.exp 1 * M * (Q : ℝ) ^ 5 * ⌈L⌉₊
        ≤ L * 3 * Real.exp b * Real.exp (2 * b) ^ 5 * (L + 1) := by
          gcongr
      _ = 3 * L * (L + 1) * Real.exp (11 * b) := by
          rw [← hE]
          ring
      _ ≤ Real.exp (L / 2) * Real.exp (L / 2) :=
          mul_le_mul h3L (Real.exp_le_exp.mpr (by linarith only [h120, hb0]))
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ = N := hhalf
  have hR6 : (M * Q) ^ 6 ≤ N := by
    have h6 : ((M : ℝ) * Q) ^ 6 ≤ Real.exp (18 * b) := by
      calc ((M : ℝ) * Q) ^ 6 ≤ Real.exp (3 * b) ^ 6 := pow_le_pow_left₀ hMQ0 hMQ 6
        _ = Real.exp (18 * b) := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    have hle : ((M : ℝ) * Q) ^ 6 ≤ N := by
      rw [hNexp]
      exact h6.trans (Real.exp_le_exp.mpr (by linarith only [h120, hb0]))
    exact_mod_cast hle
  have hR18 : 18 * (1 + Real.log ((M * Q : ℕ) : ℝ)) ≤ Real.log N := by
    have hlogR : Real.log ((M * Q : ℕ) : ℝ) ≤ 3 * b := by
      push_cast
      rw [Real.log_mul hM0.ne' hQ0.ne']
      linarith only [hMhi, hQhi]
    rw [← hLd]
    linarith only [hlogR, h120, hL36, hb0]
  have hNL : 3 * L ≤ (N : ℝ) := by
    have h1' : Real.exp (L / 2) ≤ (N : ℝ) := by
      rw [hNexp]
      exact Real.exp_le_exp.mpr (by linarith only [hL0])
    linarith only [h34L, h1', hL0]
  have hwidth : c / N ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    linarith only [hcL, hNL]
  have hrowN : (((M * Q) * (M * Q) : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
    have he2 : Real.exp 2 ≤ 8 := by
      have h := Real.exp_one_lt_d9
      have he0 := Real.exp_pos 1
      have hsplit2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [hsplit2]
      nlinarith only [h, he0]
    have hrad : linearNearRowRadius c + 1 ≤ 17 * L := by
      unfold linearNearRowRadius
      have h2c : 2 * c * Real.exp 2 ≤ 2 * L * 8 :=
        mul_le_mul (by linarith only [hcL]) he2 (Real.exp_pos _).le (by positivity)
      linarith only [h2c, hL1]
    calc _ ≤ 2 * Real.exp (6 * b) * (17 * L) :=
          mul_le_mul hsqone hrad (by
            unfold linearNearRowRadius
            positivity) (by positivity)
      _ = Real.exp (6 * b) * (34 * L) := by ring
      _ ≤ Real.exp (L / 2) * Real.exp (L / 2) :=
          mul_le_mul hexp6 h34L (by positivity) (Real.exp_pos _).le
      _ = N := hhalf
  have hRNT : (((M * Q) * (M * Q) : ℕ) + 1 : ℝ) * T ≤ N := by
    calc _ ≤ 2 * Real.exp (6 * b) * T :=
          mul_le_mul_of_nonneg_right hsqone (by linarith only [hT1])
      _ = Real.exp (6 * b) * (2 * T) := by ring
      _ ≤ Real.exp (L / 2) * Real.exp (L / 2) :=
          mul_le_mul hexp6 ht (by linarith only [hT1]) (Real.exp_pos _).le
      _ = N := hhalf
  have hmain := hlaw c hc1 N M Q hQ₀Q hB hM hlog1 hscale hR2 hR6 hR18 hwidth hrowN g t V hV hg G
    hu1 hy1 hort
  have hmert := abs_mertens_inner_le_of_mem_conductorSubspace (ε := ε / 3) (by positivity) hT1 hrow
    hR2 hRNT hR18 _ (packetVector_gcdTwistedCharge_mem g hM t N) _ hort
  -- the Mertens top rows
  have hθ : mertensRowCeiling * Real.sqrt (2 * (Real.log (2 * T) + 3) / Real.log N) ≤ ε / 3 := by
    rw [← hLd]
    have hsq' : 2 * (Real.log (2 * T) + 3) / L ≤ (ε / (3 * mertensRowCeiling)) ^ 2 := by
      rw [div_le_iff₀ hL0]
      have h := mul_le_mul_of_nonneg_left hth (sq_nonneg (ε / (3 * mertensRowCeiling)))
      refine le_trans (le_of_eq ?_) h
      field_simp
    have hs' := Real.sqrt_le_iff.mpr ⟨(by positivity : 0 ≤ ε / (3 * mertensRowCeiling)), hsq'⟩
    have h := mul_le_mul_of_nonneg_left hs' hCM.le
    refine h.trans_eq ?_
    field_simp
  -- assembly
  obtain ⟨U, hU⟩ : ∃ U, U =
      ‖packetVector (fun j => (Real.sqrt (Real.log N))⁻¹ * gcdTwistedCharge g M Q t j) N‖ := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ‖packetVector G N‖ := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by rw [hU]; exact norm_nonneg _
  have hY0 : 0 ≤ Y := by rw [hY]; exact norm_nonneg _
  rw [← hU, ← hY] at hmain hmert ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = 1 / Real.sqrt (Real.log Q) + periodBandDivisors Q M / Real.log Q :=
    ⟨_, rfl⟩
  rw [← hD] at hmain hup
  have hVt : 0 ≤ V * |t| := mul_nonneg hV (abs_nonneg t)
  have hε'3 : ε' ≤ ε / 3 := by nlinarith only [hKε, hK, hε']
  have hKε' : K * ε' ≤ ε / 3 := by nlinarith only [hKε, hε']
  have hupward : K * ((linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c) * |t| * D ≤
      ε / 3 * (V * |t|) := by
    have e : K * ((linearPrimeStrip c : ℝ) * V * literalMultiplierWidth c) * |t| * D =
        K * (V * |t|) * ((linearPrimeStrip c : ℝ) * literalMultiplierWidth c * D) := by ring
    rw [e]
    have h' := mul_le_mul_of_nonneg_left hup (mul_nonneg hK hVt)
    have h'' := mul_le_mul_of_nonneg_right hKε' hVt
    nlinarith only [h', h'']
  have hrateU : chargeChannelRate φ C c (M * Q) N * U ≤ ε / 3 * U :=
    mul_le_mul_of_nonneg_right (hrate.trans hε'3) hU0
  have hfirst := mul_le_mul_of_nonneg_right (add_le_add hupward hrateU) hY0
  have hsecond : (ε / 3 + mertensRowCeiling *
      Real.sqrt (2 * (Real.log (2 * T) + 3) / Real.log N)) * U * Y ≤ 2 * ε / 3 * U * Y := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hU0) hY0
    linarith only [hθ]
  have hpos : 0 ≤ ε * (V * |t|) * Y := by positivity
  nlinarith only [hmain, hmert, hfirst, hsecond, hpos]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
