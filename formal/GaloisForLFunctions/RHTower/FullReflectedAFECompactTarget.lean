import GaloisForLFunctions.RHTower.ReflectedCompactTargetBranch

open Complex MeasureTheory Filter Topology Finset Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- The complete original reflected AFE reaches every larger-disc holomorphic
target on a compact disc, inside every prescribed moving character cell,
with an arbitrarily small power loss under the original product measure. -/
theorem exists_fullReflectedAFE_prescribedPhase_compactTarget
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hc0 : 1 / 2 < c.re - R) (hc1 : c.re + R < 1)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall c R))
    (P : ℕ) (ω : Omega) {δ ε ρ : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((n ^ 2 : ℕ) : ℝ) (2 * (n ^ 2 : ℕ)),
        m * ((n ^ 2 : ℕ) : ℝ) ^ (-ε) ≤ steinhausMeasure.real
          (steinhausCharacterCell P (steinhausLogPhaseShift ω (-tau)) δ ∩
            reflectedCompactTargetEvent c r f ρ (n ^ 2) tau) := by
  classical
  obtain ⟨e, he, hbranch⟩ := exists_reflectedCompactTarget_branch_mass
    c hr hrR hc0 hc1 P ω hδ hρ (half_pos hε)
  obtain ⟨G, hG, hcatalogue⟩ := exists_finite_reflectedCompactReferenceTarget_catalogue
    c (by linarith) hrR hf hc0 hc1 he
  choose m hm hmass using fun g : G => hbranch g.val (hG g.val g.property)
  have hnonempty : Nonempty G := by
    obtain ⟨N, hN⟩ := hcatalogue.exists
    obtain ⟨g, hg, _⟩ := hN (N : ℝ) ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) N]⟩ ω
    exact ⟨⟨g, hg⟩⟩
  letI : Nonempty G := hnonempty
  obtain ⟨g0, _, hmin⟩ := (Finset.univ : Finset G).exists_min_image m Finset.univ_nonempty
  have hall := Filter.eventually_all.mpr hmass
  have hsquare : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by decide)
  refine ⟨m g0, hm g0, ?_⟩
  filter_upwards [hall, hsquare.eventually hcatalogue, eventually_ge_atTop (1 : ℕ)]
    with n hn hcat hn1
  intro tau htau
  obtain ⟨g, hg, happ⟩ := hcat tau htau (steinhausLogPhaseShift ω (-tau))
  let j : G := ⟨g, hg⟩
  have hj := hn j tau htau f (fun s hs => (happ s hs).le)
  have hNR : (0 : ℝ) < ((n ^ 2 : ℕ) : ℝ) := by positivity
  have hexp : Real.exp (-(2 * (ε / 2) * Real.log (n ^ 2 : ℕ))) =
      ((n ^ 2 : ℕ) : ℝ) ^ (-ε) := by
    rw [Real.rpow_def_of_pos hNR]
    congr 1
    ring
  rw [hexp] at hj
  exact (mul_le_mul_of_nonneg_right (hmin j (mem_univ j))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans hj

end RHTower
