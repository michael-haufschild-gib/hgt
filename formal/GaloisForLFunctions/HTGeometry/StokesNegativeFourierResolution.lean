import GaloisForLFunctions.HTGeometry.StokesNegativeFourierContactTransport
import GaloisForLFunctions.HTGeometry.StokesWeylFourierSource

open scoped PowerSeries

namespace GaloisForLFunctions.IrregularStokes

namespace Characteristic

open FormalUniformizer LaurentFourier WeylFourier

noncomputable section

/-- One exact negative-Fourier step, simultaneously at operator, Laurent-coordinate and contact
levels. -/
def ExactNegativeFourierStep {R beta : ℕ} (c : Characteristic R beta) : Prop :=
  ∃ unit : PowerSeries ℂ, unit.constantCoeff = 1 ∧
    ∃ reparametrization : LaurentSeries ℂ ≃ₐ[ℂ] LaurentSeries ℂ,
      c.nextRamification < R ∧
      c.canonicalLaurent = normalizedIrregularValue R c.nextRamification unit ∧
      (localFourierCoordinate R c.canonicalLaurent).order =
        -(c.nextRamification : ℤ) ∧
      (localFourierReciprocalCoordinate R c.canonicalLaurent).order =
        (c.nextRamification : ℤ) ∧
      localFourierReciprocalCoordinate R c.canonicalLaurent =
        reparametrization
          ((PowerSeries.X ^ c.nextRamification : PowerSeries ℂ) : LaurentSeries ℂ) ∧
      fourier (generalizedAiryOperator R c.nextRamification) =
        (-X) ^ R - D ^ c.nextRamification ∧
      ∀ (ι : Type) (q : ι → LaurentSeries ℂ),
        (∀ i j,
          laurentContactMatrix (fun k => reparametrization.symm (q k)) i j =
            laurentContactMatrix q i j) ∧
        laurentContactHierarchy (fun k => reparametrization.symm (q k)) =
          laurentContactHierarchy q

theorem exactNegativeFourierStep {R beta : ℕ} (c : Characteristic R beta)
    (hc : c.IsAiryTower) : ExactNegativeFourierStep c := by
  obtain ⟨u, hu, phi, hdrop, hform, hcoord, hrecip, hexact, hcontact⟩ :=
    c.airyTower_negativeFourier_contact_transport hc
  exact ⟨u, hu, phi, hdrop, hform, hcoord, hrecip, hexact,
    fourier_generalizedAiryOperator R c.nextRamification, hcontact⟩

/-- An exact finite negative-Fourier resolution follows the actual recursive characteristic tail;
the terminal constructor performs the last drop to rank one. -/
inductive ExactNegativeFourierResolution :
    {R beta : ℕ} → (c : Characteristic R beta) → Type
  | terminal {R beta : ℕ} (hR : 1 < R) (hbeta : 0 < beta)
      (hgcd : Nat.gcd R beta = 1)
      (first : ExactNegativeFourierStep (Characteristic.terminal hR hbeta hgcd)) :
      ExactNegativeFourierResolution (Characteristic.terminal hR hbeta hgcd)
  | step {R E beta gamma : ℕ} (hER : E < R) (hE : 1 < E)
      (hbeta : 0 < beta) (hgcd : Nat.gcd R beta = E) (hgamma : gamma < beta)
      (tail : Characteristic E gamma)
      (first : ExactNegativeFourierStep
        (Characteristic.step hER hE hbeta hgcd hgamma tail))
      (rest : ExactNegativeFourierResolution tail) :
      ExactNegativeFourierResolution
        (Characteristic.step hER hE hbeta hgcd hgamma tail)

def exactNegativeFourierResolution {R beta : ℕ} (c : Characteristic R beta)
    (hc : c.IsAiryTower) : ExactNegativeFourierResolution c := by
  induction c with
  | terminal hR hbeta hgcd =>
      exact .terminal hR hbeta hgcd
        (exactNegativeFourierStep (Characteristic.terminal hR hbeta hgcd) hc)
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      exact .step hER hE hbeta hgcd hgamma tail
        (exactNegativeFourierStep
          (Characteristic.step hER hE hbeta hgcd hgamma tail) hc)
        (ih hc.2)

def ExactNegativeFourierResolution.rankTrace :
    {R beta : ℕ} → {c : Characteristic R beta} →
      ExactNegativeFourierResolution c → List ℕ
  | R, _, _, .terminal .. => [R, 1]
  | R, _, _, .step _ _ _ _ _ _ _ rest => R :: rest.rankTrace

@[simp] theorem exactNegativeFourierResolution_rankTrace
    {R beta : ℕ} {c : Characteristic R beta}
    (resolution : ExactNegativeFourierResolution c) :
    resolution.rankTrace = c.ramificationTrace := by
  induction resolution with
  | terminal => rfl
  | step hER hE hbeta hgcd hgamma tail first rest ih =>
      simp [ExactNegativeFourierResolution.rankTrace, ramificationTrace, ih]

theorem exactNegativeFourierResolution_endsAtOne
    {R beta : ℕ} {c : Characteristic R beta}
    (resolution : ExactNegativeFourierResolution c) :
    resolution.rankTrace.getLast? = some 1 := by
  rw [exactNegativeFourierResolution_rankTrace resolution]
  exact c.ramificationTrace_getLast

/-- **Exact iterated negative-Fourier resolution theorem.**  Every Airy tower has a finite chain of
actual Weyl Fourier identities, exact Laurent uniformizers and hierarchy-preserving contact
reparametrizations, and the rank chain terminates at one. -/
theorem airyTower_exact_negativeFourier_resolution
    {R beta : ℕ} (c : Characteristic R beta) (hc : c.IsAiryTower) :
    ∃ resolution : ExactNegativeFourierResolution c,
      resolution.rankTrace = c.ramificationTrace ∧
      resolution.rankTrace.getLast? = some 1 := by
  let resolution := c.exactNegativeFourierResolution hc
  exact ⟨resolution, exactNegativeFourierResolution_rankTrace resolution,
    exactNegativeFourierResolution_endsAtOne resolution⟩

end
end Characteristic
end GaloisForLFunctions.IrregularStokes
