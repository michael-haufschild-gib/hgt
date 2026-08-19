import GaloisForLFunctions.HTGeometry.ArchimedeanBracketRatio
import GaloisForLFunctions.HTGeometry.ComplexShiftJetQuotientDatum

/-!
# The archimedean monomial valuation theorem

An element of `K_G = ℂ(s)⟨G⟩` is a quotient of polynomials in `G` whose coefficients lie in
`L = ℂ(s)⟨G'/G⟩`, and every nonzero element of `L` is a quotient of polynomials in the digamma jets
at pairwise incongruent shifts.  Dividing numerator and denominator by their lowest coefficient and
by the corresponding power of `G` leaves a bracket ratio tending to one, while the surviving factor
is the ratio of the two lowest coefficients — which has a boundary datum.

Hence every such element is asymptotic to `c·G^k·s^a·(log s)^b` on a vertical line.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

/-- An element of the complex-shifted polygamma field, on a vertical line. -/
def jetFieldQuotLine (nu : Fin r → ℂ) {K : ℕ} (idx : Fin K → Fin r × ℕ)
    (P Q : MvPolynomial (Fin K) (Polynomial ℂ)) (σ t : ℝ) : ℂ :=
  jetFieldPolyFunC nu idx P ((σ : ℂ) + (t : ℂ) * Complex.I)
    / jetFieldPolyFunC nu idx Q ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- **The archimedean monomial valuation theorem.**  A `K_G`-element whose coefficients are
elements of the shifted polygamma field, normalized by the lowest power of `G` and by the boundary
shapes of its two lowest coefficients, converges to a nonzero residue. -/
theorem exists_archimedeanGammaField_boundaryLaw
    {d : ℕ} (lam : Fin d → ℝ) (μ : Fin d → ℂ) (hlam : ∀ j, 0 < lam j) (α : ℝ) (hd : 0 < d)
    {M : ℝ} (hM : 0 < M) {σ : ℝ} (hσpos : 0 < σ) (hσM : σ ≤ M)
    (hσG : ∀ j, 0 < lam j * σ + (μ j).re)
    (nu : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, nu i - nu i' ≠ (n : ℂ))
    {K : ℕ} (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    {P₁ Q₁ P₂ Q₂ : MvPolynomial (Fin K) (Polynomial ℂ)}
    (hP₁ : P₁ ≠ 0) (hQ₁ : Q₁ ≠ 0) (hP₂ : P₂ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    {Nn Nd : ℕ}
    (A : Fin Nn → ℝ → ℂ) (CA : Fin Nn → ℝ) (mA : Fin Nn → ℕ) (ku : Fin Nn → ℕ)
    (hCA : ∀ i, 0 ≤ CA i) (hku : ∀ i, 0 < ku i)
    (hA : ∀ i, ∀ᶠ t : ℝ in atTop, ‖A i t‖ ≤ CA i * t ^ mA i)
    (B : Fin Nd → ℝ → ℂ) (CB : Fin Nd → ℝ) (mB : Fin Nd → ℕ) (kv : Fin Nd → ℕ)
    (hCB : ∀ i, 0 ≤ CB i) (hkv : ∀ i, 0 < kv i)
    (hB : ∀ i, ∀ᶠ t : ℝ in atTop, ‖B i t‖ ≤ CB i * t ^ mB i)
    (u0 v0 : ℕ) :
    ∃ (a₁ b₁ a₂ b₂ : ℤ) (c : ℂ), c ≠ 0 ∧
      Tendsto (fun t : ℝ =>
          ((jetFieldQuotLine nu idx P₁ Q₁ σ t
              * (1 + ∑ i : Fin Nn, A i t * (archimedeanProductLine lam μ α σ t) ^ (ku i))
              * (archimedeanProductLine lam μ α σ t) ^ u0)
            / (jetFieldQuotLine nu idx P₂ Q₂ σ t
              * (1 + ∑ i : Fin Nd, B i t * (archimedeanProductLine lam μ α σ t) ^ (kv i))
              * (archimedeanProductLine lam μ α σ t) ^ v0))
            * ((archimedeanProductLine lam μ α σ t) ^ v0 * gammaShiftShape 0 σ 0 (a₂ : ℝ) b₂ t)
            / ((archimedeanProductLine lam μ α σ t) ^ u0 * gammaShiftShape 0 σ 0 (a₁ : ℝ) b₁ t))
        atTop (nhds c) := by
  obtain ⟨a₁, b₁, c₁, hc₁, hd₁⟩ :=
    exists_hasShiftTubeDatum_jetFieldQuotientC nu hincong idx hinj hP₁ hQ₁ hM
  obtain ⟨a₂, b₂, c₂, hc₂, hd₂⟩ :=
    exists_hasShiftTubeDatum_jetFieldQuotientC nu hincong idx hinj hP₂ hQ₂ hM
  refine ⟨a₁, b₁, a₂, b₂, c₁ / c₂, div_ne_zero hc₁ hc₂, ?_⟩
  have hline₁ := (hd₁.hasShiftDatum hσpos hσM).2
  have hline₂ := (hd₂.hasShiftDatum hσpos hσM).2
  dsimp only at hline₁ hline₂
  exact tendsto_archimedeanQuotient_valuation lam μ hlam hσG α hd
    A CA mA ku hCA hku hA B CB mB kv hCB hkv hB
    (fun t => jetFieldQuotLine nu idx P₁ Q₁ σ t)
    (fun t => jetFieldQuotLine nu idx P₂ Q₂ σ t)
    (fun t => gammaShiftShape 0 σ 0 (a₁ : ℝ) b₁ t)
    (fun t => gammaShiftShape 0 σ 0 (a₂ : ℝ) b₂ t)
    hc₁ hc₂ hline₁ hline₂ u0 v0

end

end GaloisForLFunctions.HTGeometry
