import GaloisForLFunctions.HTGeometry.ResolvedChannelWardLaw
import GaloisForLFunctions.RHTower.GammaConductorSchurCapacity
import GaloisForLFunctions.RHTower.PrimeMellinJetDiagonalEnergyNoGo

/-!
# Resolved Euler-channel mixing no-go for positive-log Mellin jets

The source-realization frontier asks an incidence to unbalance inverse-log Cauchy packets into
positive-log Mellin jets while preserving Euler multiplication.  Literal preservation of every
resolved prime channel is too strong: the resolved-channel commutant classification forces such an
incidence to be diagonal, and the resulting positive-log prime energy is not summable.

Therefore a viable source incidence cannot commute with all resolved Euler projections.  Any
surviving construction must carry a non-flat channel connection whose commutator energy is coupled
to the Gamma/polar boundary before the Hilbert norm or Schur trace is closed.
-/

namespace RHTower

open HTGeometry

noncomputable section

/-- A fully resolved Euler incidence commutes with every individual prime-channel projection. -/
def PreservesResolvedPrimeChannels
    (T : (Nat.Primes → ℂ) →ₗ[ℂ] (Nat.Primes → ℂ)) : Prop :=
  PreservesResolvedChannels T

/-- A fully resolved Euler incidence has no off-diagonal prime transfer. -/
theorem preservesResolvedPrimeChannels_cannot_mix
    (T : (Nat.Primes → ℂ) →ₗ[ℂ] (Nat.Primes → ℂ))
    (hT : PreservesResolvedPrimeChannels T)
    {p q : Nat.Primes} (hpq : p ≠ q) (z : ℂ) :
    T (resolvedChannelAtom q z) p = 0 := by
  exact resolvedChannelAtom_offDiagonal_eq_zero T hT hpq z

/-- If a fully resolved prime-channel incidence produces the positive-log Mellin jet on its
forced diagonal, then its weighted output energy is not summable. -/
theorem not_summable_fullyResolvedPrimeChannel_outputEnergy_of_mellinJet
    (T : (Nat.Primes → ℂ) →ₗ[ℂ] (Nat.Primes → ℂ))
    (hT : PreservesResolvedPrimeChannels T) (x : Nat.Primes → ℂ) (r : ℕ)
    (hdiag : ∀ p : Nat.Primes,
      finiteVonMangoldtRealWeight p *
          Complex.normSq (x p * T (resolvedChannelAtom p 1) p) =
        primeMellinJetDiagonalEnergy r p) :
    ¬ Summable (fun p : Nat.Primes =>
      finiteVonMangoldtRealWeight p * Complex.normSq (T x p)) := by
  intro hsum
  apply not_summable_primeMellinJetDiagonalEnergy r
  apply hsum.congr
  intro p
  rw [apply_eq_resolvedDiagonal T hT x p]
  exact hdiag p

/-- **Resolved Euler-channel mixing no-go.** No channel-preserving prime incidence can both
realize a positive-log Mellin jet and have summable weighted output energy. -/
theorem no_summable_fullyResolvedPrimeChannel_mellinJetRealization (r : ℕ) :
    ¬ ∃ (T : (Nat.Primes → ℂ) →ₗ[ℂ] (Nat.Primes → ℂ))
        (x : Nat.Primes → ℂ),
      PreservesResolvedPrimeChannels T ∧
      (∀ p : Nat.Primes,
        finiteVonMangoldtRealWeight p *
            Complex.normSq (x p * T (resolvedChannelAtom p 1) p) =
          primeMellinJetDiagonalEnergy r p) ∧
      Summable (fun p : Nat.Primes =>
        finiteVonMangoldtRealWeight p * Complex.normSq (T x p)) := by
  rintro ⟨T, x, hT, hdiag, hsum⟩
  exact (not_summable_fullyResolvedPrimeChannel_outputEnergy_of_mellinJet
    T hT x r hdiag) hsum

/-- **Gamma Ward--Schur capacity law.** Once accumulated one-prime Schur cost exceeds fixed
conductor capacity, positivity forces a quantitative resolved commutator energy. -/
theorem gammaConductorResolvedWardCapacity_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Nat.Primes) (K : Matrix ι ι ℝ) (B : ℝ)
    (hB : 0 < B) (hdiag : ∀ i, K i i = 1)
    (hquad : ∀ (x : ι → ℝ) (y : ℝ),
      0 ≤ (∑ i, ∑ j, K i j * x i * x j) +
        2 * y * (∑ i, gammaConductorPrimeNormalizedCross (p i) * x i) +
          B * y ^ (2 : ℕ))
    (hcapacity : B ≤ ∑ i, gammaConductorPrimeSchurCost (p i)) :
    2 * ((∑ i, gammaConductorPrimeSchurCost (p i)) / B - 1) ^ (2 : ℕ) ≤
      resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) := by
  let u : ι → ℝ := fun i => gammaConductorPrimeNormalizedCross (p i)
  let S : ℝ := ∑ i, gammaConductorPrimeSchurCost (p i)
  have hSnonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun i _hi => gammaConductorPrimeSchurCost_nonneg (p i)
  have hSpos : 0 < S := lt_of_lt_of_le hB hcapacity
  have hsumu : (∑ i, (u i) ^ (2 : ℕ)) = S := by
    dsimp [u, S]
    apply Finset.sum_congr rfl
    intro i _hi
    exact gammaConductorPrimeNormalizedCross_sq (p i)
  have hcoherence : S ^ (2 : ℕ) / B - S ≤ resolvedChannelWeightedCoherence K u := by
    simpa [S, u, resolvedChannelWeightedCoherence, mul_assoc] using
      gammaConductorOffDiagonalCovarianceEnergy_lower p K B hB hdiag hquad
  have hquot : 1 ≤ S / B := (le_div_iff₀ hB).2 (by
    simpa [S] using hcapacity)
  have hL : 0 ≤ S ^ (2 : ℕ) / B - S := by
    calc
      0 ≤ S * (S / B - 1) :=
        mul_nonneg hSnonneg (sub_nonneg.mpr hquot)
      _ = S ^ (2 : ℕ) / B - S := by ring
  have hward := resolvedChannelWardSchurCapacity_simple_lower
    K u (S ^ (2 : ℕ) / B - S) hL hcoherence
  rw [hsumu] at hward
  have hfactor : S ^ (2 : ℕ) / B - S = S * (S / B - 1) := by ring
  rw [hfactor] at hward
  have hcancel :
      S ^ (2 : ℕ) * (2 * (S / B - 1) ^ (2 : ℕ)) ≤
        S ^ (2 : ℕ) * resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) := by
    calc
      S ^ (2 : ℕ) * (2 * (S / B - 1) ^ (2 : ℕ)) =
          2 * (S * (S / B - 1)) ^ (2 : ℕ) := by ring
      _ ≤ resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) * S ^ (2 : ℕ) :=
        hward
      _ = S ^ (2 : ℕ) * resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) := by
        ring
  exact le_of_mul_le_mul_left hcancel (sq_pos_of_pos hSpos)

/-- **Cofinal Gamma Ward blow-up.** For fixed positive scalar conductor capacity, every energy
threshold is exceeded by some finite prime packet in every positive normalized covariance block. -/
theorem exists_primePacket_gammaConductor_resolvedWardEnergy_gt
    (B M : ℝ) (hB : 0 < B) (hM : 0 ≤ M) :
    ∃ F : Finset Nat.Primes, ∀ (K : Matrix (↑F) (↑F) ℝ),
      (∀ i, K i i = 1) →
      (∀ (x : ↑F → ℝ) (y : ℝ),
        0 ≤ (∑ i, ∑ j, K i j * x i * x j) +
          2 * y * (∑ i : ↑F,
            gammaConductorPrimeNormalizedCross (i : Nat.Primes) * x i) +
            B * y ^ (2 : ℕ)) →
      M < resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) := by
  obtain ⟨F, hF⟩ :=
    exists_finset_gammaConductorPrimeSchurCost_gt (B * (M + 2))
  refine ⟨F, ?_⟩
  intro K hdiag hquad
  let S : ℝ := ∑ i : ↑F, gammaConductorPrimeSchurCost (i : Nat.Primes)
  have hS : B * (M + 2) < S := by
    simpa only [S, Finset.univ_eq_attach, Finset.sum_attach] using hF
  have hcapacity : B ≤ S := by
    nlinarith
  have hward := gammaConductorResolvedWardCapacity_lower
    (fun i : ↑F => (i : Nat.Primes)) K B hB hdiag hquad (by
      simpa only [S] using hcapacity)
  have hquot : M + 2 < S / B := (lt_div_iff₀ hB).2 (by
    nlinarith)
  have hstrict : M < 2 * (S / B - 1) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (S / B - 1)]
  exact hstrict.trans_le (by simpa only [S] using hward)

end

end RHTower
