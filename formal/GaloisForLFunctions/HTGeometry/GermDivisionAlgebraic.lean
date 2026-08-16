import GaloisForLFunctions.HTGeometry.GermPreparationAlgebraic
import GaloisForLFunctions.HTGeometry.GermWeierstrassDivision

/-!
# Weierstrass division as an identity in the ring of germs

The analytic division on a polydisc, read in the local ring: relative to the distinguished
polynomial of a germ regular in the distinguished coordinate, every germ is a multiple of that
polynomial plus a polynomial of lower degree with coefficients pulled back from the germ ring in
the remaining variables.

Together with the preparation this says the local ring in `n+1` variables is generated over the
local ring in `n` variables, modulo the distinguished polynomial, by the powers of the
distinguished coordinate below its degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

/-- **Weierstrass preparation and division together, as identities of germs.** -/
theorem germ_division_algebraic {f g : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ)) (hg : AnalyticAt ℂ g (0 : Fin (n + 1) → ℂ))
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ (d : ℕ) (α β : ℕ → AnalyticGerm (0 : Fin n → ℂ))
      (q u : AnalyticGerm (0 : Fin (n + 1) → ℂ)),
      IsUnit u ∧ (∀ j, j < d → analyticGermValue (0 : Fin n → ℂ) (α j) = 0) ∧
      analyticGermOf hf
          = (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j) * u ∧
      analyticGermOf hg
          = q * (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j)
            + ∑ j ∈ Finset.range d, germTail n (β j) * germCoord n ^ j := by
  classical
  obtain ⟨r₁, hr₁, hfr⟩ := exists_ball_analyticOnNhd hf
  obtain ⟨r₂, hr₂, hgr⟩ := exists_ball_analyticOnNhd hg
  set r : ℝ := min r₁ r₂ with hrdef
  have hr : 0 < r := lt_min hr₁ hr₂
  have hfd : DifferentiableOn ℂ f (ball (0 : Fin (n + 1) → ℂ) r) :=
    (hfr.mono (ball_subset_ball (min_le_left _ _))).differentiableOn
  have hgd : DifferentiableOn ℂ g (ball (0 : Fin (n + 1) → ℂ) r) :=
    (hgr.mono (ball_subset_ball (min_le_right _ _))).differentiableOn
  obtain ⟨t, δ, d, a, b, q, u, htpos, hδpos, hadiff, hazero, hbdiff, hqdiff, hudiff,
    hprep, hdiv⟩ :=
    HTGeometry.germ_weierstrass_division isOpen_ball (mem_ball_self hr) hfd hgd hreg
  have haA : ∀ j, AnalyticAt ℂ (a j) (0 : Fin n → ℂ) := fun j =>
    HTGeometry.analyticAt_of_differentiableOn isOpen_ball (hadiff j) (mem_ball_self hδpos)
  have hbA : ∀ j, AnalyticAt ℂ (b j) (0 : Fin n → ℂ) := fun j =>
    HTGeometry.analyticAt_of_differentiableOn isOpen_ball (hbdiff j) (mem_ball_self hδpos)
  have hqA : AnalyticAt ℂ q (0 : Fin (n + 1) → ℂ) :=
    HTGeometry.analyticAt_of_differentiableOn (isOpen_prepPolydisc t δ) hqdiff
      (zero_mem_prepPolydisc htpos hδpos)
  have huA : AnalyticAt ℂ u (0 : Fin (n + 1) → ℂ) :=
    HTGeometry.analyticAt_of_differentiableOn (isOpen_prepPolydisc t δ) hudiff
      (zero_mem_prepPolydisc htpos hδpos)
  have hcons0 : (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  have hu0 : u (0 : Fin (n + 1) → ℂ) ≠ 0 := by
    have := (hprep 0 (mem_ball_self hδpos) 0 (by simpa using htpos)).2
    rwa [hcons0] at this
  refine ⟨d, fun j => analyticGermOf (haA j), fun j => analyticGermOf (hbA j),
    analyticGermOf hqA, analyticGermOf huA, ?_, ?_, ?_, ?_⟩
  · rw [isUnit_analyticGerm_iff, analyticGermValue_of huA]
    exact hu0
  · intro j hj
    rw [analyticGermValue_of (haA j)]
    exact hazero j hj
  · refine Subtype.ext ?_
    have hcoe : (((germCoord n ^ d
          + ∑ j ∈ Finset.range d, germTail n (analyticGermOf (haA j)) * germCoord n ^ j)
        * analyticGermOf huA : AnalyticGerm (0 : Fin (n + 1) → ℂ)) :
          Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
        = ((fun w : Fin (n + 1) → ℂ =>
            ((w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j) * u w) :
              (Fin (n + 1) → ℂ) → ℂ) := by
      rw [Subring.coe_mul, coe_germDistinguished haA]
      rfl
    rw [hcoe]
    refine (Germ.coe_eq.mpr ?_).symm
    filter_upwards [(isOpen_prepPolydisc t δ).mem_nhds (zero_mem_prepPolydisc htpos hδpos)]
      with w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hmainw := (hprep (Fin.tail w) hw1 (w 0) hw2).1
    rw [Fin.cons_self_tail] at hmainw
    exact hmainw.symm
  · refine Subtype.ext ?_
    have hcoe : ((analyticGermOf hqA
          * (germCoord n ^ d
            + ∑ j ∈ Finset.range d, germTail n (analyticGermOf (haA j)) * germCoord n ^ j)
          + ∑ j ∈ Finset.range d, germTail n (analyticGermOf (hbA j)) * germCoord n ^ j :
            AnalyticGerm (0 : Fin (n + 1) → ℂ)) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
        = ((fun w : Fin (n + 1) → ℂ =>
            q w * ((w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j)
              + ∑ j ∈ Finset.range d, b j (Fin.tail w) * (w 0) ^ j) :
              (Fin (n + 1) → ℂ) → ℂ) := by
      rw [Subring.coe_add, Subring.coe_mul, coe_germDistinguished haA,
        coe_germPolyTail hbA]
      rfl
    rw [hcoe]
    refine (Germ.coe_eq.mpr ?_).symm
    filter_upwards [(isOpen_prepPolydisc t δ).mem_nhds (zero_mem_prepPolydisc htpos hδpos)]
      with w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hmainw := hdiv (Fin.tail w) hw1 (w 0) hw2
    rw [Fin.cons_self_tail] at hmainw
    exact hmainw.symm

end GaloisForLFunctions.HTGeometry
