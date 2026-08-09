import GaloisForLFunctions.HTGeometry.CoverSchwarz

/-!
# A family of local representatives with a bounded comparison vanishes

The form of the Siegel gain that a chart family actually supplies.  On each chart the function is
only a local holomorphic representative `F i`; what relates the charts is a bound `C` for passing
from the small discs to the large ones.  If the Schwarz gain beats that comparison constant, every
representative vanishes on its small disc.

Unlike the single-function version this is not degenerate on a compact quotient: a globally
periodic entire function is constant by Liouville, whereas local representatives of a meromorphic
function are not, which is exactly why Siegel's argument is stated chartwise.

* **`eqOn_zero_of_family_cover`**.
-/

open Set Metric

namespace GaloisForLFunctions.HTGeometry

/-- **A family of local representatives with a bounded chart comparison vanishes.** -/
theorem eqOn_zero_of_family_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → E) (F : ι → E → ℂ)
    (hF : ∀ i, ContDiff ℂ (⊤ : ℕ∞) (F i))
    {r R C : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 0 < R) {N : ℕ}
    (hvan : ∀ i, ∀ k, k < N → iteratedFDeriv ℂ k (F i) (c i) = 0)
    (hcomp : ∀ M : ℝ, (∀ i, ∀ w : E, ‖w‖ ≤ r → ‖F i (c i + w)‖ ≤ M) →
      ∀ i, ∀ w : E, ‖w‖ ≤ R → ‖F i (c i + w)‖ ≤ C * M)
    (hgain : C * ((r / R) ^ N / (1 - r / R)) < 1) :
    ∀ i, ∀ w : E, ‖w‖ ≤ r → F i (c i + w) = 0 := by
  classical
  set θ : ℝ := (r / R) ^ N / (1 - r / R) with hθdef
  have hq0 : 0 ≤ r / R := by positivity
  have hq1 : r / R < 1 := by rw [div_lt_one hR]; exact hrR
  have hden : 0 < 1 - r / R := by linarith
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  -- the maximum of each representative on its closed small disc
  have hball : IsCompact (closedBall (0 : E) r) := isCompact_closedBall 0 r
  have hbne : (closedBall (0 : E) r).Nonempty := ⟨0, by simpa using hr⟩
  have hmax : ∀ i : ι, ∃ w ∈ closedBall (0 : E) r,
      IsMaxOn (fun w => ‖F i (c i + w)‖) (closedBall (0 : E) r) w := by
    intro i
    refine hball.exists_isMaxOn hbne ?_
    exact (((hF i).continuous.comp (continuous_const.add continuous_id)).norm).continuousOn
  choose w₀ hw₀mem hw₀max using hmax
  obtain ⟨i₁, -, hi₁⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun i => ‖F i (c i + w₀ i)‖)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set M : ℝ := ‖F i₁ (c i₁ + w₀ i₁)‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMbound : ∀ i, ∀ w : E, ‖w‖ ≤ r → ‖F i (c i + w)‖ ≤ M := by
    intro i w hw
    have hwmem : w ∈ closedBall (0 : E) r := by simpa using hw
    have h1 : ‖F i (c i + w)‖ ≤ ‖F i (c i + w₀ i)‖ := hw₀max i hwmem
    exact h1.trans (hi₁ i (Finset.mem_univ i))
  have hbig := hcomp M hMbound
  -- the Schwarz gain on each small disc
  have hsch : ∀ i, ∀ w : E, ‖w‖ ≤ r → ‖F i (c i + w)‖ ≤ C * M * θ := by
    intro i w hw
    have hcov : ∀ z ∈ {z : E | ‖z - c i‖ ≤ r}, ∃ _ : Unit, ‖z - c i‖ ≤ r :=
      fun z hz => ⟨(), hz⟩
    have hres := norm_le_of_cover_schwarz (F := F i) (hF i) (fun _ : Unit => c i) hr hrR hR
      (fun _ => hbig i) (fun _ => hvan i) hcov (c i + w) (by simpa using hw)
    rw [hθdef, ← mul_div_assoc]
    exact hres
  -- the maximum improves itself
  have hstep : M ≤ (C * θ) * M := by
    have := hsch i₁ (w₀ i₁) (by simpa using hw₀mem i₁)
    calc M = ‖F i₁ (c i₁ + w₀ i₁)‖ := hM
      _ ≤ C * M * θ := this
      _ = (C * θ) * M := by ring
  have hMzero : M = 0 := by nlinarith
  intro i w hw
  have := hMbound i w hw
  rw [hMzero] at this
  exact norm_le_zero_iff.mp this

end GaloisForLFunctions.HTGeometry
