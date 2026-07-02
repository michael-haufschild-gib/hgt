/-
# Tower-section restriction with a floored band bottom (mixed-pair wiring, step B3)

The deep anchor pins the band bottom only from above (`log rlo < G_c(0) + ε`); the mixed-pair
tower needs a FLOOR (`log rlo ≥ G_c(0) + 1`) so the band clears the Green-pinched ball
`closedBall 0 2` containing the connected partner's filled Julia set.  No surgery on the
anchor: a `TowerSection` restricts to any sub-annulus with a raised inner radius, and the
band surjectivity re-derives itself from the section's level identity `G_c(T w) = log‖w‖`.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SectionTower

open Complex Set

namespace Bottcher

/-- Raising the inner radius shrinks the annulus. -/
theorem annulusSet_subset_of_le {rlo rlo' rhi : ℝ} (hlo : rlo ≤ rlo') :
    annulusSet rlo' rhi ⊆ annulusSet rlo rhi := fun _ hw =>
  ⟨lt_of_le_of_lt hlo hw.1, hw.2⟩

/-- **Restriction of a tower section to a raised inner radius.**  Every field restricts along
`annulusSet rlo' rhi ⊆ annulusSet rlo rhi`; the winding certificate restricts its radius
range. -/
def TowerSection.restrict {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {rlo' : ℝ} (hlo : rlo ≤ rlo') : TowerSection c rlo' rhi where
  T := S.T
  an := fun w hw => S.an w (annulusSet_subset_of_le hlo hw)
  level := fun w hw => S.level w (annulusSet_subset_of_le hlo hw)
  odd := fun w hw => S.odd w (annulusSet_subset_of_le hlo hw)
  fe := fun w hw hw2 => S.fe w (annulusSet_subset_of_le hlo hw)
    (annulusSet_subset_of_le hlo hw2)
  inj := S.inj.mono (annulusSet_subset_of_le hlo)
  dne := fun w hw => S.dne w (annulusSet_subset_of_le hlo hw)
  wind := fun r hr1 hr2 => S.wind r (lt_of_le_of_lt hlo hr1) hr2

@[simp]
theorem TowerSection.restrict_T {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {rlo' : ℝ} (hlo : rlo ≤ rlo') : (S.restrict hlo).T = S.T := rfl

/-- **Floored band surjectivity.**  If the original section is band-surjective, the restricted
section is surjective onto the raised band: the witness annulus point recovers its norm from
the level identity. -/
theorem TowerSection.restrict_bandsurj {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    {rlo' : ℝ} (hlo : rlo ≤ rlo') (hpos : 0 < rlo)
    (hsurj : ∀ z : ℂ, Real.log rlo < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ → z ∈ S.T '' annulusSet rlo R₀) :
    ∀ z : ℂ, Real.log rlo' < greenFunctionDyn c z →
      greenFunctionDyn c z < Real.log R₀ →
      z ∈ (S.restrict hlo).T '' annulusSet rlo' R₀ := by
  intro z h1 h2
  have h0 : Real.log rlo < greenFunctionDyn c z :=
    lt_of_le_of_lt (Real.log_le_log hpos hlo) h1
  obtain ⟨w, hw, rfl⟩ := hsurj z h0 h2
  have hlev := S.level w hw
  refine ⟨w, ⟨?_, hw.2⟩, rfl⟩
  by_contra hcon
  push Not at hcon
  have hwpos : 0 < ‖w‖ := lt_trans hpos hw.1
  have h4 : Real.log ‖w‖ ≤ Real.log rlo' := Real.log_le_log hwpos hcon
  rw [hlev] at h1
  linarith

end Bottcher
