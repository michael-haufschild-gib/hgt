import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldBlocks
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldApproximation

/-! # Odd sites certified by two-row coefficient boxes -/
open MeasureTheory Filter Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Two coefficient rows with only the odd longitudinal field active. -/
def isolatedFieldBlockCenter (q : ℝ) (b : PathPauliBlockLabel) : ℝ :=
  if b.1=1 ∧ b.2=Sum.inl 2 then q else 0

/-- A box around the isolated field controls every term incident on the odd site. -/
theorem isolated_odd_site_of_block {n j : ℕ} (ω : PathPauliDisorder) (q η : ℝ)
    {s : Fin (n+2)} (hs : s.val=2*j+1)
    (h : ∀ i, |pathPauliBlock ω j i-isolatedFieldBlockCenter q i| ≤ η) :
    isolatedLongitudinalSite (pathPauliDisorderShell ω n) q η s := by
  intro l hI
  rcases l with ⟨v,a⟩ | ⟨e,ab⟩
  · change v=s at hI
    subst v
    change |ω (s.val,.inl a) - (if a=2 ∧ s ∈ Finset.univ then q else 0)| ≤ η
    simpa [pathPauliBlock,isolatedFieldBlockCenter,hs] using h (1,.inl a)
  · change e.castSucc=s ∨ e.succ=s at hI
    change |ω (e.val,.inr ab)-0| ≤ η
    rcases hI with hleft | hright
    · have he : e.val=2*j+1 := (congrArg Fin.val hleft).trans hs
      simpa [pathPauliBlock,isolatedFieldBlockCenter,he] using h (1,.inr ab)
    · have hsucc := (congrArg Fin.val hright).trans hs
      change e.val+1=2*j+1 at hsucc
      have he : e.val=2*j := by omega
      simpa [pathPauliBlock,isolatedFieldBlockCenter,he] using h (0,.inr ab)

end
end GaloisForLFunctions.HTGeometry
