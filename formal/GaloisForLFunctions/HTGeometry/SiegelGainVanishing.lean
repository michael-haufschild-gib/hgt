import GaloisForLFunctions.HTGeometry.SiegelGain

/-!
# A Siegel gain that beats the chart comparison forces vanishing

The closing mechanism.  Suppose a continuous function satisfies, on a finite family of small
polydiscs, a Schwarz gain `θ` relative to its bound on the corresponding large tori, and suppose the
large tori are controlled by the small polydiscs with a comparison constant `C`.  If `C·θ < 1` the
function vanishes on every small polydisc.

The maximum over the compact small polydiscs exists, the comparison carries it to the tori, the gain
carries it back improved by `C·θ`, and a maximum that improves itself is zero.  The comparison
constant is what a periodicity argument supplies — for a periodic function the tori are congruent to
points of the fundamental domain — and the reduced local presentations of a meromorphic function are
what make it finite.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The gain closes.**  A Schwarz gain beating the chart comparison forces vanishing on the small
polydiscs. -/
theorem eqOn_zero_of_siegel_gain (c : ι → (Fin n → ℂ)) (G : (Fin n → ℂ) → ℂ)
    (hG : Continuous G) {r R C θ : ℝ} (hr : 0 ≤ r) (_hθ : 0 ≤ θ)
    (hgain : ∀ M : ℝ, (∀ i : ι, ∀ t : Fin n → ℝ,
        ‖G (torusMap (c i) (fun _ => R) t)‖ ≤ M) →
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ‖G (c i + y)‖ ≤ M * θ)
    (hcomp : ∀ M : ℝ, (∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ‖G (c i + y)‖ ≤ M) →
      ∀ (i : ι) (t : Fin n → ℝ), ‖G (torusMap (c i) (fun _ => R) t)‖ ≤ C * M)
    (hlt : C * θ < 1) :
    ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → G (c i + y) = 0 := by
  classical
  -- the maximum of each local representative on its closed small polydisc
  have hball : IsCompact (closedBall (0 : Fin n → ℂ) r) := isCompact_closedBall 0 r
  have hbne : (closedBall (0 : Fin n → ℂ) r).Nonempty := ⟨0, by simpa using hr⟩
  have hmax : ∀ i : ι, ∃ y ∈ closedBall (0 : Fin n → ℂ) r,
      IsMaxOn (fun y => ‖G (c i + y)‖) (closedBall (0 : Fin n → ℂ) r) y := by
    intro i
    refine hball.exists_isMaxOn hbne ?_
    exact ((hG.comp (continuous_const.add continuous_id)).norm).continuousOn
  choose y₀ hy₀mem hy₀max using hmax
  obtain ⟨i₁, -, hi₁⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun i => ‖G (c i + y₀ i)‖)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set M : ℝ := ‖G (c i₁ + y₀ i₁)‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMbound : ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ‖G (c i + y)‖ ≤ M := by
    intro i y hy
    have hymem : y ∈ closedBall (0 : Fin n → ℂ) r := by simpa using hy
    exact (hy₀max i hymem).trans (hi₁ i (Finset.mem_univ i))
  -- comparison to the tori, then the gain back
  have hbig := hcomp M hMbound
  have hsmall := hgain (C * M) hbig
  have hstep : M ≤ (C * θ) * M := by
    have h := hsmall i₁ (y₀ i₁) (by simpa using hy₀mem i₁)
    calc M = ‖G (c i₁ + y₀ i₁)‖ := hM
      _ ≤ C * M * θ := h
      _ = (C * θ) * M := by ring
  have hMzero : M = 0 := by nlinarith
  intro i y hy
  have := hMbound i y hy
  rw [hMzero] at this
  exact norm_le_zero_iff.mp this

/-- **The gain closes, chartwise.**  The form the Siegel argument actually needs: on each chart the
function is only a local representative, and what relates the charts is the comparison constant. -/
theorem eqOn_zero_of_family_siegel_gain (c : ι → (Fin n → ℂ)) (F : ι → (Fin n → ℂ) → ℂ)
    {r R C θ : ℝ}
    (hF : ∀ i, ContinuousOn (fun y => F i (c i + y)) (closedBall (0 : Fin n → ℂ) r))
    (hr : 0 ≤ r)
    (hgain : ∀ M : ℝ, (∀ i : ι, ∀ t : Fin n → ℝ,
        ‖F i (torusMap (c i) (fun _ => R) t)‖ ≤ M) →
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ‖F i (c i + y)‖ ≤ M * θ)
    (hcomp : ∀ M : ℝ, (∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ‖F i (c i + y)‖ ≤ M) →
      ∀ (i : ι) (t : Fin n → ℝ), ‖F i (torusMap (c i) (fun _ => R) t)‖ ≤ C * M)
    (hlt : C * θ < 1) :
    ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → F i (c i + y) = 0 := by
  classical
  have hball : IsCompact (closedBall (0 : Fin n → ℂ) r) := isCompact_closedBall 0 r
  have hbne : (closedBall (0 : Fin n → ℂ) r).Nonempty := ⟨0, by simpa using hr⟩
  have hmax : ∀ i : ι, ∃ y ∈ closedBall (0 : Fin n → ℂ) r,
      IsMaxOn (fun y => ‖F i (c i + y)‖) (closedBall (0 : Fin n → ℂ) r) y := by
    intro i
    refine hball.exists_isMaxOn hbne ?_
    exact (hF i).norm
  choose y₀ hy₀mem hy₀max using hmax
  obtain ⟨i₁, -, hi₁⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun i => ‖F i (c i + y₀ i)‖)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set M : ℝ := ‖F i₁ (c i₁ + y₀ i₁)‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMbound : ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ‖F i (c i + y)‖ ≤ M := by
    intro i y hy
    have hymem : y ∈ closedBall (0 : Fin n → ℂ) r := by simpa using hy
    exact (hy₀max i hymem).trans (hi₁ i (Finset.mem_univ i))
  have hbig := hcomp M hMbound
  have hsmall := hgain (C * M) hbig
  have hstep : M ≤ (C * θ) * M := by
    have h := hsmall i₁ (y₀ i₁) (by simpa using hy₀mem i₁)
    calc M = ‖F i₁ (c i₁ + y₀ i₁)‖ := hM
      _ ≤ C * M * θ := h
      _ = (C * θ) * M := by ring
  have hMzero : M = 0 := by nlinarith
  intro i y hy
  have := hMbound i y hy
  rw [hMzero] at this
  exact norm_le_zero_iff.mp this

end GaloisForLFunctions.HTGeometry
