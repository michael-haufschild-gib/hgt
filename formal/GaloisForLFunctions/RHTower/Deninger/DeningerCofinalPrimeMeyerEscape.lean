import GaloisForLFunctions.RHTower.Deninger.DeningerPairedPrimeGaussianSoninTransport
import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyProduct
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrictEmbedding
import GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier

/-!
# Cofinal prime Green source limits and compact escape

The Mellin evaluation at every complex point is a continuous linear
functional on the original Meyer source topology. Its literal integral is
identified by exponentially weighting the source in Schwartz space and
applying the exactly normalized Fourier evaluation.

Every limit of arbitrarily scalar-renormalized cofinal finite paired prime
sources is zero: each prime periodization kernel is closed, and cofinal
prime tomography separates the original source. The actual Xi-normalized
sources have reading one, so they have no convergent subsequence and escape
every compact subset of the Meyer source. The explicit all-primes-up-to-N
family gives an unconditional instance with no cofinality premise.

During this source escape, every normalized original-prime/cofinal-depth
chain retains precisely the same fixed Sonin operator image. These theorems
do not assert its vanishing or identify the complete original BV boundary
with the fixed physical reader. Damped approximate prime kernels require
a separate residual estimate; the exact-kernel result does not supply it.
-/

open Complex Filter Topology SchwartzMap FourierTransform MeasureTheory
namespace RHTower
noncomputable section

/-- Literal Mellin reading, continuous for the original Meyer topology. -/
def deningerOriginalMeyerMellinCLM (s : ℂ) : DeningerMeyerSource →L[ℂ] ℂ :=
  (deningerSchwartzEval (-s.im / (2 * Real.pi))).comp
    (((FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(ℝ, ℂ)) :
      𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)).comp
      ⟨deningerExpMulSchwartzLM s.re, deningerExpMulSchwartzLM_continuous s.re⟩)

theorem deningerOriginalMeyerMellinCLM_apply (s : ℂ) (h : DeningerMeyerSource) :
    deningerOriginalMeyerMellinCLM s h =
      deningerMeyerStrongLogMellin
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) s := by
  change (𝓕 (deningerExpMulSchwartzLM s.re h)) (-s.im / (2 * Real.pi)) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    deningerMeyerStrongLogMellin]
  apply integral_congr_ae
  filter_upwards with t
  simp only [deningerExpMulSchwartzLM_apply, deningerExpMul_apply,
    smul_eq_mul, deningerMeyerStrongLogMellinJet, pow_zero, one_mul, Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  conv_rhs => rw [← Complex.re_add_im s]
  field_simp [Real.pi_ne_zero]
  ring

/-- C38's actual source in the original topologized Meyer facade. -/
def deningerPairedPrimeMeyerSource (P : List Nat.Primes) : DeningerMeyerSource :=
  DeningerMeyerSource.toSource.symm
    (deningerExpSchwartzOfStrongLogDecay
      (deningerPairedPrimeGaussianSource P).val (deningerPairedPrimeGaussianSource P).property)

theorem deningerPairedPrimeMeyerSource_mellin (P : List Nat.Primes) (s : ℂ) :
    deningerOriginalMeyerMellinCLM s (deningerPairedPrimeMeyerSource P) =
      deningerMeyerStrongLogMellin (deningerPairedPrimeGaussianSource P) s := by
  rw [deningerOriginalMeyerMellinCLM_apply]
  rfl

theorem deningerPairedPrimeMeyerSource_prime_kernel (P : List Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ P) :
    deningerPeriodizationLM ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
      (deningerPairedPrimeMeyerSource P) = 0 := by
  apply (deningerPeriodizationLM_eq_zero_iff _ _).2
  have hmem := (deningerPairedPrimeGreenGaussian_source P).2.1 p hp
  obtain ⟨u, hu⟩ := hmem
  have hexp : DeningerMeyerSource.toSource (deningerPairedPrimeMeyerSource P) ∈
      Set.range (deningerPeriodizationDefect (Real.log (p : ℕ))) := by
    refine ⟨deningerExpSchwartzOfStrongLogDecay u.val u.property, ?_⟩
    rw [← deningerExpSchwartzOfStrongLogDecay_defect, hu]
    rfl
  rw [deningerPeriodization_range_eq_kernel
    (Real.log_pos (by exact_mod_cast p.property.one_lt))] at hexp
  exact hexp

/-- Every source limit of arbitrarily scaled cofinal finite-prime depletion is zero. -/
theorem deningerPairedPrimeMeyerSource_cofinal_limit_zero
    (P : ℕ → List Nat.Primes) (hP : ∀ p : Nat.Primes, ∀ᶠ n in atTop, p ∈ P n)
    (c : ℕ → ℂ) (h : DeningerMeyerSource)
    (hlim : Tendsto (fun n => c n • deningerPairedPrimeMeyerSource (P n)) atTop (nhds h)) : h = 0 := by
  have hper : ∀ p : Nat.Primes,
      deningerPeriodizationLM
        ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩ h = 0 := by
    intro p
    let L : {x : ℝ // 0 < x} :=
      ⟨Real.log (p : ℕ), Real.log_pos (by exact_mod_cast p.property.one_lt)⟩
    apply (deningerPeriodizationLM_isClosed_ker L).mem_of_tendsto hlim
    filter_upwards [hP p] with n hn
    change deningerPeriodizationLM L (c n • deningerPairedPrimeMeyerSource (P n)) = 0
    rw [map_smul, deningerPairedPrimeMeyerSource_prime_kernel (P n) p hn, smul_zero]
  have hz : (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) = 0 := by
    apply deningerCofinalPrimeTomography (DeningerMeyerSource.toSource h).property
      Nat.infinite_setOf_prime (fun _ hp => hp)
    intro p hp
    exact (deningerPeriodizationLM_eq_zero_iff _ h).1 (hper ⟨p, hp⟩)
  apply DeningerMeyerSource.toSource.injective
  apply Subtype.ext
  exact hz

/-- Normalize one retained actual Xi reading of the original source. -/
def deningerPairedPrimeMeyerXiNormalized (P : List Nat.Primes) (rho : XiDivisorSupport) :
    DeningerMeyerSource :=
  (deningerOriginalMeyerMellinCLM rho (deningerPairedPrimeMeyerSource P))⁻¹ •
    deningerPairedPrimeMeyerSource P

theorem deningerPairedPrimeMeyerSource_xi_ne_zero (P : List Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalMeyerMellinCLM rho (deningerPairedPrimeMeyerSource P) ≠ 0 := by
  rw [deningerPairedPrimeMeyerSource_mellin]
  exact (deningerPairedPrimeGreenGaussian_source P).2.2 rho

/-- The literal original-source reading is exactly one at every finite stage. -/
@[simp] theorem deningerPairedPrimeMeyerXiNormalized_reading
    (P : List Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalMeyerMellinCLM rho (deningerPairedPrimeMeyerXiNormalized P rho) = 1 := by
  rw [deningerPairedPrimeMeyerXiNormalized, map_smul, smul_eq_mul,
    inv_mul_cancel₀ (deningerPairedPrimeMeyerSource_xi_ne_zero P rho)]

/-- Retaining a nonzero actual Xi coefficient excludes every original-Meyer source limit. -/
theorem deningerPairedPrimeMeyerXiNormalized_not_tendsto
    (P : ℕ → List Nat.Primes) (hP : ∀ p : Nat.Primes, ∀ᶠ n in atTop, p ∈ P n)
    (rho : XiDivisorSupport) (h : DeningerMeyerSource) :
    ¬ Tendsto (fun n => deningerPairedPrimeMeyerXiNormalized (P n) rho) atTop (nhds h) := by
  intro hlim
  have hz := deningerPairedPrimeMeyerSource_cofinal_limit_zero P hP
    (fun n => (deningerOriginalMeyerMellinCLM rho (deningerPairedPrimeMeyerSource (P n)))⁻¹)
    h hlim
  have hM := ((deningerOriginalMeyerMellinCLM rho).continuous.tendsto h).comp hlim
  rw [hz, map_zero] at hM
  have hone : Tendsto
      (fun n => deningerOriginalMeyerMellinCLM rho (deningerPairedPrimeMeyerXiNormalized (P n) rho))
      atTop (nhds (1 : ℂ)) := by simp
  exact zero_ne_one (tendsto_nhds_unique hM hone)

/-- Actual compact escape, stronger than absence of a limit along the full sequence. -/
theorem deningerPairedPrimeMeyerXiNormalized_escapes_compact
    (P : ℕ → List Nat.Primes) (hP : ∀ p : Nat.Primes, ∀ᶠ n in atTop, p ∈ P n)
    (rho : XiDivisorSupport) (K : Set DeningerMeyerSource) (hK : IsCompact K) :
    ∀ᶠ n in atTop, deningerPairedPrimeMeyerXiNormalized (P n) rho ∉ K := by
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, deningerPairedPrimeMeyerXiNormalized (P n) rho ∈ K := by
    simpa only [not_not] using Filter.not_eventually.mp hnot
  obtain ⟨h, hh, phi, hphi, ht⟩ := hK.isSeqCompact.subseq_of_frequently_in hfreq
  exact deningerPairedPrimeMeyerXiNormalized_not_tendsto (P ∘ phi)
    (fun p => hphi.tendsto_atTop.eventually (hP p)) rho h ht

/-- Explicit prime-prefix family: all original primes are eventually retained. -/
theorem deningerOriginalPrimePrefix_cofinal (p : Nat.Primes) :
    ∀ᶠ n in atTop, p ∈ (GaloisForLFunctions.primesLE n).toList := by
  filter_upwards [eventually_ge_atTop (p : ℕ)] with n hn
  exact Finset.mem_toList.mpr ((GaloisForLFunctions.mem_primesLE n p).2 hn)

/-- Unconditional nonconvergence for the explicit original prime-prefix source family. -/
theorem deningerNormalizedPrimePrefix_no_limit (rho : XiDivisorSupport) :
    ¬ ∃ h : DeningerMeyerSource, Tendsto
      (fun n => deningerPairedPrimeMeyerXiNormalized (GaloisForLFunctions.primesLE n).toList rho)
      atTop (nhds h) := by
  rintro ⟨h, hh⟩
  exact deningerPairedPrimeMeyerXiNormalized_not_tendsto _
    deningerOriginalPrimePrefix_cofinal rho h hh

/-- The explicit normalized source eventually leaves every compact Meyer set. -/
theorem deningerNormalizedPrimePrefix_compact_escape (rho : XiDivisorSupport) :
    ∀ K : Set DeningerMeyerSource, IsCompact K →
      ∀ᶠ n in atTop,
        deningerPairedPrimeMeyerXiNormalized (GaloisForLFunctions.primesLE n).toList rho ∉ K := by
  intro K hK
  exact deningerPairedPrimeMeyerXiNormalized_escapes_compact _
    deningerOriginalPrimePrefix_cofinal rho K hK

/-- Exact physical readout of the same scalar-normalized actual prime/depth chain. -/
theorem deningerPairedPrimeMeyerXiNormalized_physical_readout
    (P : List Nat.Primes) (p : Nat.Primes) (q : XiZeroCopy) (n : ℕ) :
    deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
      (deningerGammaSixCofinalMeyerTateCompletedDifferential
        ((deningerOriginalMeyerMellinCLM q.1 (deningerPairedPrimeMeyerSource P))⁻¹ •
          deningerPairedPrimeGaussianDegreeOneChain P p q n)) =
    (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q)⁻¹ •
      deningerGammaSixCofinalGraphPhysicalTransport (2 * (q.1 : ℂ).re - 1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) := by
  rw [map_smul, map_smul, deningerPairedPrimeGaussian_finite_physical_readout,
    ← mul_smul, deningerPairedPrimeMeyerSource_mellin,
    deningerPairedPrimeGaussianSource_mellin]
  have ha := deningerPairedPrimeXiMultiplier_ne_zero P q
  have hg := DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade_ne_zero q
  change ((deningerPairedPrimeXiMultiplier P (q.1 : ℂ) *
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q)⁻¹ *
      deningerPairedPrimeXiMultiplier P (q.1 : ℂ)) • _ = _
  congr 1
  field_simp

end
end RHTower
