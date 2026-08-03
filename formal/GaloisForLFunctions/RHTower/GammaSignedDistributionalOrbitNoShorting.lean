import GaloisForLFunctions.RHTower.GammaSignedUnconditionalOrbitNoShorting
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Signed distributional Gamma-frequency no-shorting

Ordinary unordered scalar summation is not the only possible meaning of an
infinite Gamma orbit.  This module closes the next precise loophole: passing
to a scalar distribution after the prime/depth carrier has already been
separated into its real modular frequencies.

For an isolated real spectrum, a smooth compactly supported bump can select
one frequency and no other.  Consequently a distribution represented by
coefficient evaluation at every frequency is zero only when every
coefficient is zero.  Canonical cross-prime/depth frequencies are isolated:
after exponentiation they are distinct positive integers.  The actual
cooriented Gamma amplitudes are strictly positive, so they cannot hide a
coefficient.

No summability, evaluation at positive real modular displacement, Xi zero,
computation, or Riemann-hypothesis premise occurs.  The surviving Route-R
object must remain genuinely pre-frequency, use a source ordering whose
scalar test evaluation is discontinuous, or couple to divisor provenance
before frequency separation.
-/

open Complex Function Set Topology
open scoped BigOperators Distributions

namespace RHTower

noncomputable section

/-- Coefficient uniqueness for a scalar distribution on an isolated real
spectrum.  The hypothesis is exactly its action on every smooth compactly
supported real test function; no convergence condition is imposed separately. -/
theorem isolatedSpectrum_coeff_eq_zero
    (lam : ℕ → ℝ) (c : ℕ → ℂ)
    (hdisc : ∀ i, ∃ s : Set ℝ, s ∈ 𝓝 (lam i) ∧
      ∀ j, lam j ∈ s → j = i)
    (hvan : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
      ∑' j : ℕ, c j * (f (lam j) : ℂ) = 0) :
    ∀ i, c i = 0 := by
  intro i
  obtain ⟨s, hs, hsi⟩ := hdisc i
  obtain ⟨f, hfs, hfc, hfd, _hfrange, hfi⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hs
  let phi : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ) :=
    ⟨f, hfd, hfc, fun _ _ => trivial⟩
  have hphi_i : phi (lam i) = 1 := hfi
  have hterm : ∀ j : ℕ,
      c j * (phi (lam j) : ℂ) = if j = i then c i else 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [hphi_i]
    · have hnot : lam j ∉ tsupport f := by
        intro hj
        exact hji (hsi j (hfs hj))
      have hz : f (lam j) = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [phi, hz, hji]
  have hz := hvan phi
  rw [tsum_congr hterm, tsum_ite_eq i] at hz
  exact hz

/-- Every canonical cross-prime/depth logarithmic frequency is isolated
inside the full canonical spectrum. -/
theorem xiGammaEulerCanonicalCrossPrimeFrequency_isolated
    (ij : XiGammaEulerCanonicalCrossPrimeDepthPair) :
    ∃ s : Set ℝ,
      s ∈ 𝓝 (xiGammaEulerCanonicalCrossPrimeFrequency ij) ∧
      ∀ kl, xiGammaEulerCanonicalCrossPrimeFrequency kl ∈ s → kl = ij := by
  let N := xiGammaEulerCanonicalCrossPrimePairNat ij
  let s : Set ℝ :=
    Real.exp ⁻¹' Set.Ioo ((N : ℝ) - 1 / 2) ((N : ℝ) + 1 / 2)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.zero_lt_of_lt
      (xiGammaEulerCanonicalCrossPrimePairNat_six_le ij)
  refine ⟨s, ?_, ?_⟩
  · apply (isOpen_Ioo.preimage Real.continuous_exp).mem_nhds
    change Real.exp (xiGammaEulerCanonicalCrossPrimeFrequency ij) ∈
      Set.Ioo ((N : ℝ) - 1 / 2) ((N : ℝ) + 1 / 2)
    rw [xiGammaEulerCanonicalCrossPrimeFrequency, Real.exp_log hNpos]
    constructor <;> norm_num
  · intro kl hkl
    apply xiGammaEulerCanonicalCrossPrimePairNat_injective
    let M := xiGammaEulerCanonicalCrossPrimePairNat kl
    have hMpos : (0 : ℝ) < M := by
      exact_mod_cast Nat.zero_lt_of_lt
        (xiGammaEulerCanonicalCrossPrimePairNat_six_le kl)
    have hbounds : (N : ℝ) - 1 / 2 < (M : ℝ) ∧
        (M : ℝ) < (N : ℝ) + 1 / 2 := by
      change Real.exp (xiGammaEulerCanonicalCrossPrimeFrequency kl) ∈
        Set.Ioo ((N : ℝ) - 1 / 2) ((N : ℝ) + 1 / 2) at hkl
      rw [xiGammaEulerCanonicalCrossPrimeFrequency, Real.exp_log hMpos] at hkl
      exact hkl
    by_contra hMN
    rcases lt_or_gt_of_ne hMN with hlt | hgt
    · have hstep : M + 1 ≤ N := by omega
      have hstepR : (M : ℝ) + 1 ≤ N := by exact_mod_cast hstep
      linarith [hbounds.1]
    · have hstep : N + 1 ≤ M := by omega
      have hstepR : (N : ℝ) + 1 ≤ M := by exact_mod_cast hstep
      linarith [hbounds.2]

/-- A scalar spectral distribution on any injectively enumerated canonical
cross-prime/depth family is coefficient-faithful. -/
theorem xiGammaEulerCanonicalCrossPrime_distributional_noShorting
    (edge : ℕ → XiGammaEulerCanonicalCrossPrimeDepthPair)
    (hedge : Function.Injective edge) (c : ℕ → ℂ)
    (hvan : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
      ∑' j : ℕ, c j *
        (f (xiGammaEulerCanonicalCrossPrimeFrequency (edge j)) : ℂ) = 0) :
    ∀ i, c i = 0 := by
  apply isolatedSpectrum_coeff_eq_zero
    (fun j => xiGammaEulerCanonicalCrossPrimeFrequency (edge j)) c
  · intro i
    obtain ⟨s, hs, hsep⟩ :=
      xiGammaEulerCanonicalCrossPrimeFrequency_isolated (edge i)
    exact ⟨s, hs, fun j hj => hedge (hsep (edge j) hj)⟩
  · exact hvan

/-- **Distributional Gamma-frequency no-shorting.**  After multiplying by
the actual positive cooriented amplitudes, vanishing against every smooth
compactly supported frequency test still forces every source coefficient to
vanish. -/
theorem xiGammaEulerCanonicalCrossPrimeCooriented_distributional_noShorting
    (edge : ℕ → XiGammaEulerCanonicalCrossPrimeDepthPair)
    (hedge : Function.Injective edge) (c : ℕ → ℂ)
    (hvan : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
      ∑' j : ℕ,
        (c j *
          (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude (edge j) : ℂ)) *
        (f (xiGammaEulerCanonicalCrossPrimeFrequency (edge j)) : ℂ) = 0) :
    ∀ i, c i = 0 := by
  let d : ℕ → ℂ := fun j =>
    c j * (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude (edge j) : ℂ)
  have hd : ∀ i, d i = 0 := by
    apply xiGammaEulerCanonicalCrossPrime_distributional_noShorting edge hedge d
    simpa only [d] using hvan
  intro i
  have hi := hd i
  simp only [d] at hi
  exact (mul_eq_zero.mp hi).resolve_right
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (xiGammaEulerCanonicalCrossPrimeCoorientedAmplitude_pos (edge i))))

end

end RHTower
