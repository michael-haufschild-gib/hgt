/-
# Indexing the zero divisor of an entire function with multiplicity

The zero divisor of an entire function `f` is indexed by the sigma type
`Σ w ∈ supp(div f), Fin (mult w)`, so that a canonical product over that index carries exactly the
divisor of `f`, one factor per multiplicity copy, with no enumeration and no choice.

The three facts the construction needs are proved here: the index family is locally finite
(every disc meets it in a finite set, because the divisor of a meromorphic function has finite
support on a compact set), it avoids the origin when `f (0) ≠ 0`, and the fiber over a divisor
point has exactly the multiplicity of that point as its cardinality.
-/
import GaloisForLFunctions.HTGeometry.CountableDivisorConvergenceExponent
import GaloisForLFunctions.HTGeometry.EntireQuotientNormalForm

noncomputable section

open Filter Topology Set Metric

namespace GaloisForLFunctions.EntireZeroDivisor

open GaloisForLFunctions.CountableDivisor

/-- The support of the analytic divisor of an entire function. -/
abbrev ZeroSupport (f : ℂ → ℂ) : Type := ↑(MeromorphicOn.divisor f Set.univ).support

/-- The multiplicity copies of the zero divisor of an entire function. -/
abbrev ZeroCopy (f : ℂ → ℂ) : Type :=
  Σ w : ZeroSupport f, Fin ((MeromorphicOn.divisor f Set.univ) (w : ℂ)).toNat

/-- The divisor point attached to a multiplicity copy. -/
def zeroCopyPoint (f : ℂ → ℂ) : ZeroCopy f → ℂ := fun p => (p.1 : ℂ)

variable {f : ℂ → ℂ}

theorem divisor_univ_eq_analyticOrder (hf : AnalyticOnNhd ℂ f Set.univ) (w : ℂ) :
    (MeromorphicOn.divisor f Set.univ) w = ((analyticOrderAt f w).map (↑)).untop₀ :=
  MeromorphicOn.AnalyticOnNhd.divisor_apply hf (Set.mem_univ w)

theorem finite_zeroSupport_ball (hf : AnalyticOnNhd ℂ f Set.univ) (r : ℝ) :
    {w : ZeroSupport f | ‖(w : ℂ)‖ ≤ r}.Finite := by
  classical
  have hmer : MeromorphicOn f (Metric.closedBall (0 : ℂ) r) :=
    fun z _ => (hf z (Set.mem_univ z)).meromorphicAt
  have hfin : ((MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)).support).Finite :=
    (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)).finiteSupport
      (isCompact_closedBall 0 r)
  refine Set.Finite.of_finite_image (f := fun w : ZeroSupport f => (w : ℂ)) ?_ ?_
  · refine hfin.subset ?_
    rintro _ ⟨w, hw, rfl⟩
    have hmem : (w : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hne : (MeromorphicOn.divisor f Set.univ) (w : ℂ) ≠ 0 := w.2
    refine Function.mem_support.mpr ?_
    rw [MeromorphicOn.divisor_apply hmer hmem,
      ← MeromorphicOn.divisor_apply (fun z _ => (hf z (Set.mem_univ z))
        |>.meromorphicAt) (Set.mem_univ (w : ℂ))]
    exact hne
  · intro x _ y _ hxy
    exact Subtype.ext hxy

theorem locallyFinite_zeroCopyPoint (hf : AnalyticOnNhd ℂ f Set.univ) :
    LocallyFiniteDivisor (zeroCopyPoint f) := by
  intro r
  have hA := finite_zeroSupport_ball hf r
  have heq : {p : ZeroCopy f | ‖zeroCopyPoint f p‖ ≤ r}
      = ⋃ w ∈ {w : ZeroSupport f | ‖(w : ℂ)‖ ≤ r}, Set.range (Sigma.mk w) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_range, zeroCopyPoint]
    constructor
    · intro hp
      exact ⟨p.1, hp, ⟨p.2, rfl⟩⟩
    · rintro ⟨w, hw, ⟨k, rfl⟩⟩
      exact hw
  rw [heq]
  exact hA.biUnion (fun w _ => Set.finite_range _)

theorem zeroCopyPoint_ne_zero (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (p : ZeroCopy f) : zeroCopyPoint f p ≠ 0 := by
  intro h
  have h2 : (MeromorphicOn.divisor f Set.univ) ((p.1 : ℂ)) ≠ 0 := p.1.2
  rw [show ((p.1 : ℂ)) = 0 from h] at h2
  apply h2
  rw [divisor_univ_eq_analyticOrder hf, (hf 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]
  simp

end GaloisForLFunctions.EntireZeroDivisor

namespace GaloisForLFunctions.EntireZeroDivisor

open GaloisForLFunctions.CountableDivisor

variable {f : ℂ → ℂ}

/-- The multiplicity fiber of the zero-copy index over a divisor point. -/
theorem ncard_zeroCopy_fiber (w : ℂ) :
    {p : ZeroCopy f | zeroCopyPoint f p = w}.ncard
      = ((MeromorphicOn.divisor f Set.univ) w).toNat := by
  classical
  by_cases hw : (MeromorphicOn.divisor f Set.univ) w = 0
  · have hempty : {p : ZeroCopy f | zeroCopyPoint f p = w} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      have h2 : (MeromorphicOn.divisor f Set.univ) ((p.1 : ℂ)) ≠ 0 := p.1.2
      rw [show ((p.1 : ℂ)) = w from hp] at h2
      exact h2 hw
    rw [hempty, Set.ncard_empty, hw]
    rfl
  · have hmem : w ∈ (MeromorphicOn.divisor f Set.univ).support := hw
    set n : ℕ := ((MeromorphicOn.divisor f Set.univ) w).toNat with hn
    set g : Fin n → ZeroCopy f := fun k => ⟨⟨w, hmem⟩, k⟩ with hg
    have hinj : Function.Injective g := by
      intro k₁ k₂ h
      simpa [hg, Sigma.mk.injEq] using h
    have hrange : Set.range g = {p : ZeroCopy f | zeroCopyPoint f p = w} := by
      ext p
      simp only [Set.mem_range, Set.mem_setOf_eq, hg]
      constructor
      · rintro ⟨k, rfl⟩
        rfl
      · intro hp
        have hp1 : p.1 = (⟨w, hmem⟩ : ZeroSupport f) := Subtype.ext hp
        refine ⟨Fin.cast (by rw [hp1]) p.2, ?_⟩
        obtain ⟨p1, p2⟩ := p
        cases hp1
        rfl
    rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofInjective g hinj).symm,
      Nat.card_eq_fintype_card, Fintype.card_fin]

theorem genusZeroProductIdx_zero {ι : Type*} (a : ι → ℂ) :
    genusZeroProductIdx a 0 = 1 := by
  rw [genusZeroProductIdx]
  have : ∀ i : ι, (1 : ℂ) - 0 / a i = 1 := by
    intro i
    rw [zero_div, sub_zero]
  rw [tprod_congr this, tprod_one]

end GaloisForLFunctions.EntireZeroDivisor
