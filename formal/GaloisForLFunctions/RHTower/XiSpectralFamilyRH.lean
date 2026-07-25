import GaloisForLFunctions.RHTower.XiSpectralFamilyLift

/-!
# A bounded vertical line makes an admissible family real

The minimal-counterexample wrapper over the interface.  Among the copies with nonzero displacement
take one of least height `g`.  Every copy below `g` is then real, so lifting them all to the real
point `g` changes the trace by two finite sums of bounded modulus, and the lifted family inherits the
line bound.  Its least height is `g`, and the chosen copy lies in its bottom shell -- which the
assembly has already put on the real axis.
-/

open Complex
open scoped BigOperators

namespace RHTower

namespace SpectralFamily

noncomputable section

variable (F : SpectralFamily)

theorem lift_pt_of_le {g H : ℝ} (hH : F.base ≤ H) {q : XiZeroCopy} (hq : g ≤ (F.pt q).re) :
    (F.lift g H hH).pt q = F.pt q := by
  simp [lift, hq]

theorem lift_pt_of_lt {g H : ℝ} (hH : F.base ≤ H) {q : XiZeroCopy} (hq : (F.pt q).re < g) :
    (F.lift g H hH).pt q = ((H : ℝ) : ℂ) := by
  simp [lift, not_le.mpr hq]

/-- **A bounded vertical line makes every displacement vanish.** -/
theorem im_eq_zero_of_line_bound_all {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    ∀ q : XiZeroCopy, (F.pt q).im = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨q₁, hq₁⟩ := hcon
  obtain ⟨qs, hqs, hmin⟩ := F.exists_min_re_of_nonempty
    (s := {q : XiZeroCopy | (F.pt q).im ≠ 0}) ⟨q₁, hq₁⟩
  set g : ℝ := (F.pt qs).re with hgdef
  have hbase : F.base ≤ g := F.base_le qs
  set G : SpectralFamily := F.lift g g hbase with hG
  -- copies below `g` are real
  have hlow : ∀ q, (F.pt q).re < g → (F.pt q).im = 0 := by
    intro q hq
    by_contra hne
    exact absurd (hmin q hne) (not_le.mpr hq)
  -- the lifted family's heights are at least `g`, with equality at `qs`
  have hGre : ∀ q, g ≤ (G.pt q).re := by
    intro q
    by_cases h : g ≤ (F.pt q).re
    · rw [hG, F.lift_pt_of_le hbase h]; exact h
    · rw [hG, F.lift_pt_of_lt hbase (not_le.mp h), Complex.ofReal_re]
  have hGqs : (G.pt qs).re = g := by
    rw [hG, F.lift_pt_of_le hbase (le_refl _)]
  have hGheight : G.bottomHeight = g :=
    le_antisymm (hGqs ▸ G.bottomHeight_le qs) (hGre _)
  -- the lifted trace inherits the line bound
  set s : Finset XiZeroCopy := (F.finite_below g).toFinset with hs
  have hmemcompl : ∀ q : ((s : Set XiZeroCopy)ᶜ : Set XiZeroCopy), g ≤ (F.pt (q : XiZeroCopy)).re := by
    intro q
    have := q.2
    simp only [Set.mem_compl_iff, Finset.mem_coe, hs, Set.Finite.mem_toFinset,
      below, Set.mem_setOf_eq, not_lt] at this
    exact this
  have hline' : ∀ x : ℝ, ‖G.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤
      C + ∑ q ∈ s, (Real.exp (-(σ * g)) + F.weight σ q) := by
    intro x
    set τ : ℂ := (σ : ℂ) + (x : ℂ) * I with hτ
    have hre : (0 : ℝ) < τ.re := by rw [hτ, re_vertical]; exact hσ
    have hFsum : Summable (fun q : XiZeroCopy => F.term τ q) :=
      (F.summable_norm_term hre).of_norm
    have hGsum : Summable (fun q : XiZeroCopy => G.term τ q) :=
      (G.summable_norm_term hre).of_norm
    have hFsplit := hFsum.sum_add_tsum_compl (s := s)
    have hGsplit := hGsum.sum_add_tsum_compl (s := s)
    have hcompl : (∑' q : ((s : Set XiZeroCopy)ᶜ : Set XiZeroCopy), G.term τ (q : XiZeroCopy))
        = ∑' q : ((s : Set XiZeroCopy)ᶜ : Set XiZeroCopy), F.term τ (q : XiZeroCopy) := by
      refine tsum_congr fun q => ?_
      rw [term, term, hG, F.lift_pt_of_le hbase (hmemcompl q)]
    have hdiff : G.traceC τ = F.traceC τ +
        ((∑ q ∈ s, G.term τ q) - ∑ q ∈ s, F.term τ q) := by
      rw [traceC, traceC, ← hGsplit, ← hFsplit, hcompl]
      ring
    have hbound : ∀ q ∈ s, ‖G.term τ q‖ + ‖F.term τ q‖ ≤
        Real.exp (-(σ * g)) + F.weight σ q := by
      intro q hq
      have hlt : (F.pt q).re < g := by
        simpa [hs, Set.Finite.mem_toFinset, below, Set.mem_setOf_eq] using hq
      have h1 : ‖G.term τ q‖ = Real.exp (-(σ * g)) := by
        rw [term, hG, F.lift_pt_of_lt hbase hlt, Complex.norm_exp]
        congr 1
        rw [hτ]
        simp [Complex.mul_re]
      have h2 : ‖F.term τ q‖ = F.weight σ q := by
        rw [norm_term, weight, hτ, re_vertical, im_vertical, hlow q hlt]
        congr 1
        ring
      rw [h1, h2]
    calc ‖G.traceC τ‖
        ≤ ‖F.traceC τ‖ + ‖(∑ q ∈ s, G.term τ q) - ∑ q ∈ s, F.term τ q‖ := by
          rw [hdiff]; exact norm_add_le _ _
      _ ≤ C + ∑ q ∈ s, (Real.exp (-(σ * g)) + F.weight σ q) := by
          refine add_le_add (hline x) ?_
          refine le_trans (norm_sub_le _ _) ?_
          refine le_trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)) ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hbound
  -- the chosen copy sits in the lifted family's bottom shell
  have hshell : qs ∈ G.bottomShell := G.mem_bottomShell.mpr (by rw [hGheight, hGqs])
  have hzero := G.im_eq_zero_of_line_bound hσ hline' qs hshell
  rw [hG, F.lift_pt_of_le hbase (le_refl _)] at hzero
  exact hqs hzero

/-- **The interface criterion, both directions.**  For any admissible family, boundedness of its
trace on some vertical line of the open right half-plane is equivalent to every point being real.

In particular the interface cannot be gamed: no choice of admissible family makes the boundedness
easier than the reality of its points. -/
theorem im_eq_zero_iff_exists_line_bound :
    (∀ q : XiZeroCopy, (F.pt q).im = 0) ↔
      ∃ σ C : ℝ, 0 < σ ∧ ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C := by
  constructor
  · intro him
    refine ⟨1, F.traceReal 1, one_pos, fun x => ?_⟩
    have hre : (0 : ℝ) < (((1 : ℝ) : ℂ) + (x : ℂ) * I).re := by
      rw [re_vertical]; exact one_pos
    have h := F.norm_traceC_le_of_im_eq_zero him hre
    rwa [re_vertical] at h
  · rintro ⟨σ, C, hσ, hline⟩
    exact F.im_eq_zero_of_line_bound_all hσ hline

end

end SpectralFamily

end RHTower
