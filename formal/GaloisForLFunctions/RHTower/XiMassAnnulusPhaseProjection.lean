import GaloisForLFunctions.RHTower.XiMassAnnulusShellSplit

/-!
# The phase projection of a moving annulus

The annulus between two cone slopes is the finite sum of the centered prime atoms with
`e^{κu} < p ≤ e^{λu}`, and each atom is `(log p)` times the damped mass profile at `h = log p`.

Projecting on the fixed unit phase of the shell turns the shell asymptotic into a *lower* bound
for the real part of each atom in the shell:

`Re(ω̄ · atom p) ≥ (log p)·(1 − C/u)·shellModulus(u, log p − κu) ≥ 0`.

Coherence is what makes the shell add rather than cancel.
-/

open Complex Filter Finset MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The annulus between two slopes as a finite atom sum. -/
theorem annulus_eq_atom_sum {a sigma kappa lam u : ℝ} (hkappa : 1 < kappa) (hlam : 1 < lam)
    (hkl : kappa ≤ lam) (hu : 0 ≤ u) :
    xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
        - xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
      = ∑ k ∈ conePrimeIndex ⌊Real.exp (lam * u)⌋₊ \ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
  classical
  have hMM : ⌊Real.exp (kappa * u)⌋₊ ≤ ⌊Real.exp (lam * u)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.2 (by nlinarith))
  have hconeκ : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope kappa) u
      = ∑ k ∈ conePrimeIndex ⌊Real.exp (kappa * u)⌋₊,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
    rw [xiMassCriticalTruePrimeCone_eq_finsetSum, xiMassConeDepthOfSlope_height hkappa,
      conePrimeIndex]
  have hconeLam : xiMassCriticalTruePrimeCone a sigma (xiMassConeDepthOfSlope lam) u
      = ∑ k ∈ conePrimeIndex ⌊Real.exp (lam * u)⌋₊,
          xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) (k + 2) := by
    rw [xiMassCriticalTruePrimeCone_eq_finsetSum, xiMassConeDepthOfSlope_height hlam,
      conePrimeIndex]
  rw [hconeκ, hconeLam, ← Finset.sum_sdiff (conePrimeIndex_subset hMM)]
  ring

/-- Each prime atom is its logarithm times the damped profile. -/
theorem xiMassCenteredPrimeAtom_eq_log_mul {a sigma u : ℝ} {p : ℕ} (hp : p.Prime) :
    xiMassCenteredPrimeAtom a ((sigma : ℂ) + u * I) p
      = ((Real.log p : ℝ) : ℂ) * xiMassCriticalDampedFourierProfile a sigma u (Real.log p) := by
  have hn : p ≠ 0 := hp.pos.ne'
  have hbase := vonMangoldt_mul_dampedProfile_eq_centeredPrimeAtom a sigma u hn
  rw [← hbase, ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- **The phase projection is bounded below by the shell modulus.** -/
theorem re_conj_shellPhase_mul_profile_ge {a sigma kappa u s C : ℝ} (hkappa : 1 < kappa)
    (hu : 0 < u)
    (hbound : ‖xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s‖ ≤ C / u * shellModulus a kappa u s) :
    (1 - C / u) * shellModulus a kappa u s
      ≤ ((starRingEnd ℂ) (shellPhase a sigma kappa)
          * xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)).re := by
  have hphase : (starRingEnd ℂ) (shellPhase a sigma kappa) * shellPhase a sigma kappa = 1 := by
    have hn := norm_shellPhase a sigma kappa
    have := Complex.mul_conj (shellPhase a sigma kappa)
    rw [Complex.normSq_eq_norm_sq, hn] at this
    rw [mul_comm]
    simpa using this
  have hsplit : (starRingEnd ℂ) (shellPhase a sigma kappa)
      * xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
      = ((shellModulus a kappa u s : ℝ) : ℂ)
        + (starRingEnd ℂ) (shellPhase a sigma kappa)
          * (xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
            - shellLeadingDamped a sigma kappa u s) := by
    have hL : (starRingEnd ℂ) (shellPhase a sigma kappa) * shellLeadingDamped a sigma kappa u s
        = ((shellModulus a kappa u s : ℝ) : ℂ) := by
      rw [shellLeadingDamped_eq hkappa hu]
      calc (starRingEnd ℂ) (shellPhase a sigma kappa)
            * (((shellModulus a kappa u s : ℝ) : ℂ) * shellPhase a sigma kappa)
          = ((shellModulus a kappa u s : ℝ) : ℂ)
            * ((starRingEnd ℂ) (shellPhase a sigma kappa) * shellPhase a sigma kappa) := by ring
        _ = ((shellModulus a kappa u s : ℝ) : ℂ) := by rw [hphase, mul_one]
    rw [← hL]
    ring
  rw [hsplit, Complex.add_re]
  simp only [Complex.ofReal_re]
  have hre : -‖(starRingEnd ℂ) (shellPhase a sigma kappa)
      * (xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s)‖
      ≤ ((starRingEnd ℂ) (shellPhase a sigma kappa)
        * (xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
          - shellLeadingDamped a sigma kappa u s)).re := by
    have := Complex.abs_re_le_norm ((starRingEnd ℂ) (shellPhase a sigma kappa)
      * (xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s))
    have habs := abs_le.1 this
    exact habs.1
  have hnorm : ‖(starRingEnd ℂ) (shellPhase a sigma kappa)
      * (xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s)‖
      = ‖xiMassCriticalDampedFourierProfile a sigma u (kappa * u + s)
        - shellLeadingDamped a sigma kappa u s‖ := by
    rw [norm_mul, RCLike.norm_conj, norm_shellPhase, one_mul]
  rw [hnorm] at hre
  nlinarith [hre, hbound]

end

end RHTower
