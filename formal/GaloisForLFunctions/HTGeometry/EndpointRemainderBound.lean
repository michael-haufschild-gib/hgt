import GaloisForLFunctions.HTGeometry.JetsEnvelope
import GaloisForLFunctions.HTGeometry.FacEnvShiftBound

/-!
# The endpoint remainder of a differential polynomial

Chaining the jet envelope, the truncated-domination bound and the shift bound gives, for a fixed
differential polynomial, one pair `(B, cc)` — independent of both the cutoff `R` and the base index
`M` — with

`‖[X^{M+R}] P(S)‖ ≤ (cc · (2^R R!)^r · 𝔞^R) · (M+R+1)^B · facEnv r 𝔞 M`,

where `S` are the jets truncated at height `M`.  Only the constant depends on `R`; the growth in `M`
is the fixed polynomial weight.

This is the numerical hypothesis of the normalised-remainder limit.
-/

open MvPolynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- **The endpoint remainder bound.** -/
theorem exists_endpoint_remainder_bound (hyp : FactorialSlope a α Λ Cc c) (m : ℕ)
    (P : MvPolynomial (Fin (m + 2)) ℂ) :
    ∃ (B : ℕ) (cc : ℝ), 0 ≤ cc ∧ ∀ R M : ℕ, R ≤ M →
      ‖PowerSeries.coeff (M + R)
          (aeval (fun i => lowPart M (formalJetsOver m (PowerSeries.mk a) i)) P)‖
        ≤ (cc * ((((2 ^ R * R.factorial : ℕ)) : ℝ)) ^ α.re * slopeRatio α Λ ^ R)
          * (((M + R : ℕ) : ℝ) + 1) ^ B * facEnv α.re (slopeRatio α Λ) M := by
  classical
  have hr : (0 : ℝ) ≤ α.re := le_of_lt hyp.re_pos
  have h𝔞 : 0 < slopeRatio α Λ := slopeRatio_pos hyp.lam_ne
  obtain ⟨BJ, KJ, hKJ, hjets⟩ := exists_jets_envelope hyp m
  obtain ⟨B', cc', hcc', hdom⟩ :=
    exists_truncDom_aeval (r := α.re) (a := slopeRatio α Λ) hr h𝔞
      (formalJetsOver m (PowerSeries.mk a)) hKJ hjets P
  refine ⟨B', cc', hcc', fun R M hRM => ?_⟩
  have hbase := norm_coeff_le_of_truncDom_shift (r := α.re) (𝔞 := slopeRatio α Λ) hr h𝔞
    (M := M) (R := R) hRM (hdom M)
  refine le_trans hbase (le_of_eq ?_)
  ring

end

end GaloisForLFunctions.HTGeometry
