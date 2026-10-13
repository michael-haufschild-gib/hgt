import GaloisForLFunctions.RHTower.ZetaThreeQuartersReduction
import GaloisForLFunctions.RHTower.DirichletFamilyEndEffects
import GaloisForLFunctions.RHTower.FamilyParityPerturbation

/-!
# The Frobenius norm of the zeta Gram matrix: diagonal part and surplus

For the density `ν_X = μ + Π_X + P_X` of `ζ` the Frobenius norm of the Gram matrix splits exactly
(`trGt2Nu_nuX_split`, `trGtildeSq_eq_split`) as

`tr G̃² = 𝓜[μ,μ] + (1/2π²) 𝒟 + 2𝓜[μ,P_X] + 2𝓜[μ,Π_X] + 𝓜[Π_X,Π_X] + 𝒮`,

where `𝒟 = Σ_n a_n² A⁻(log n, log n)` is the diagonal of the prime pairs (`ppDiag`) and the
**surplus** (`frobSurplus`)

`𝒮 = (1/2π²)(𝒪₁ + 𝒪₂) + 2𝓜[P_X, Π_X] + E(ν_X, ν_X)`

collects the off-diagonal prime pairs `𝒪₁ = Σ_{n≠m} a_n a_m A⁻(log n, log m)` (`ppOffDiag`), the sum
frequencies `𝒪₂ = Σ_{n,m} a_n a_m A⁺(log n, log m)` (`ppSumFreq`), the prime–pole cross term and the
end correction of the grid.  The identity holds at every bandwidth; every term outside `𝒮` has an
unconditional asymptotic evaluation at every bandwidth, and at bandwidth `≤ 1` so does `𝒮`.
-/

open MeasureTheory Real Zeta23 Zeta23.PrimeSide

noncomputable section

namespace RHTower

/-- The diagonal of the prime pairs, `𝒟 = Σ_{n ≤ X} a_n² A⁻(log n, log n)`. -/
def ppDiag (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n)

/-- The off-diagonal prime pairs, `𝒪₁ = Σ_{n ≠ m ≤ X} a_n a_m A⁻(log n, log m)`. -/
def ppOffDiag (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))

/-- The sum frequencies, `𝒪₂ = Σ_{n, m ≤ X} a_n a_m A⁺(log n, log m)`. -/
def ppSumFreq (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)

/-- **The Frobenius surplus**: off-diagonal prime pairs, sum frequencies, the prime–pole cross term
and the end correction. -/
def frobSurplus (p : Setting) (F : LocalFun) : ℝ :=
  (1 / (2 * π ^ 2)) * (ppOffDiag F.Phi p.T p.X + ppSumFreq F.Phi p.T p.X)
    + 2 * Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)
    + endForm p F (Zeta23.nuX p.X) (Zeta23.nuX p.X)

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- **The exact split of the Frobenius norm of the density `ν_X = μ + Π_X + P_X`.** -/
theorem trGt2Nu_nuX_split (hΓ : GammaFacts) (hF : LocalHypsCoreW cϱ p F) (hT : 0 ≤ p.T) :
    trGt2Nu (Zeta23.nuX p.X) p F
      = Mform F.Phi p.T Zeta23.mu Zeta23.mu + (1 / (2 * π ^ 2)) * ppDiag F.Phi p.T p.X
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X)
        + Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X) + frobSurplus p F := by
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hν : Zeta23.nuX p.X = Zeta23.mu + Zeta23.PiX p.X + Zeta23.PX p.X := rfl
  have hE := endForm_self (p := p) (F := F) (Zeta23.nuX p.X)
  have hM : MtotalNu (Zeta23.nuX p.X) p F
      = Mform F.Phi p.T Zeta23.mu Zeta23.mu + Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PX p.X)
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X)
        + 2 * Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)
        + Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X) := by
    unfold MtotalNu
    rw [hν, Mform_trinomial hΦ hF.Phi_even hΓ.smooth.continuous hF.PiX_cont (PX_continuous p.X)]
  have hPP := Mform_PX_PX hT hΦ p.X
  unfold trGt2Nu frobSurplus ppDiag ppOffDiag ppSumFreq
  rw [hPP] at hM
  linarith [hE, hM]

/-- **The same split for the bandwidth-`4/3` Gram matrix of `ζ`.** -/
theorem trGtildeSq_eq_split (hΓ : GammaFacts) {cϱ T : ℝ}
    (hF : LocalHypsCoreW cϱ (params43.toSetting T) (params43.localFun T)) (hT : 0 ≤ T) :
    params43.trGtildeSq T
      = Mform (params43.PhiR T) T Zeta23.mu Zeta23.mu
        + (1 / (2 * π ^ 2)) * ppDiag (params43.PhiR T) T (params43.X T)
        + 2 * Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PX (params43.X T))
        + 2 * Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PiX (params43.X T))
        + Mform (params43.PhiR T) T (Zeta23.PiX (params43.X T)) (Zeta23.PiX (params43.X T))
        + frobSurplus (params43.toSetting T) (params43.localFun T) :=
  trGt2Nu_nuX_split hΓ hF hT

end RHTower
