import GaloisForLFunctions.HTGeometry.GermPreparationAlgebraic
import GaloisForLFunctions.HTGeometry.SliceDivisionIndependence

/-!
# The germ ring is free of rank `d` over the parameter ring modulo a distinguished polynomial

The independence half of the Weierstrass free-module statement, at the level of germs: if a
multiple of the distinguished polynomial of a regular germ plus a combination of the powers
`1, germCoord, …, germCoord^(d-1)` with coefficients pulled back from the parameter ring vanishes,
then every coefficient and the multiple itself vanish.

Passing from germs to functions costs one shrinking of the polydisc, and that shrinking is where
distinguishedness enters: on the smaller parameter ball all roots of the moving Weierstrass
polynomial have moved inside the smaller disc, so the slice-level independence applies parameter by
parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric
open _root_.HTGeometry (sliceRoots multisetLinearProd)

variable {n : ℕ}

theorem prepPolydisc_subset_ball {t₁ δ₁ r : ℝ} (ht : t₁ ≤ r) (hδ : δ₁ ≤ r) :
    prepPolydisc (n := n) t₁ δ₁ ⊆ ball (0 : Fin (n + 1) → ℂ) r := by
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hw1' : ‖Fin.tail w‖ < δ₁ := by simpa [dist_zero_right] using mem_ball.mp hw1
  have hCle : ‖w‖ ≤ max ‖w 0‖ ‖Fin.tail w‖ := by
    refine (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr ?_
    intro i
    induction i using Fin.cases with
    | zero => exact le_max_left _ _
    | succ j =>
        refine le_trans ?_ (le_max_right _ _)
        show ‖Fin.tail w j‖ ≤ ‖Fin.tail w‖
        exact norm_le_pi_norm _ j
  have hClt : max ‖w 0‖ ‖Fin.tail w‖ < r :=
    max_lt (lt_of_lt_of_le hw2 ht) (lt_of_lt_of_le hw1' hδ)
  rw [mem_ball, dist_zero_right]
  exact lt_of_le_of_lt hCle hClt

/-- **Weierstrass preparation together with the independence of the low-degree part.**  The germ
ring is a free module of rank `d` over the parameter ring modulo the distinguished polynomial. -/
theorem germ_division_independence {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f (0 : Fin (n + 1) → ℂ))
    (hreg : ¬ (fun z : ℂ => f (Fin.cons z (0 : Fin n → ℂ))) =ᶠ[𝓝 (0 : ℂ)] 0) :
    ∃ (d : ℕ) (α : ℕ → AnalyticGerm (0 : Fin n → ℂ)) (u : AnalyticGerm (0 : Fin (n + 1) → ℂ)),
      IsUnit u ∧ (∀ j, j < d → analyticGermValue (0 : Fin n → ℂ) (α j) = 0) ∧
      analyticGermOf hf
          = (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j) * u ∧
      (∀ (q : AnalyticGerm (0 : Fin (n + 1) → ℂ)) (β : ℕ → AnalyticGerm (0 : Fin n → ℂ)),
        q * (germCoord n ^ d + ∑ j ∈ Finset.range d, germTail n (α j) * germCoord n ^ j)
            + ∑ j ∈ Finset.range d, germTail n (β j) * germCoord n ^ j = 0 →
          q = 0 ∧ ∀ j, j < d → β j = 0) := by
  classical
  obtain ⟨r, hr, hfr⟩ := exists_ball_analyticOnNhd hf
  have hfd : DifferentiableOn ℂ f (ball (0 : Fin (n + 1) → ℂ) r) := hfr.differentiableOn
  obtain ⟨t, δ, htpos, hδpos, hdisc2, hdisc, hnez, hadm, hiso⟩ :=
    _root_.HTGeometry.exists_sliceAdmissible_nhds isOpen_ball (mem_ball_self hr) hfd hreg
  have hVopen : IsOpen (ball (0 : Fin n → ℂ) δ) := isOpen_ball
  have hVconn : IsPreconnected (ball (0 : Fin n → ℂ) δ) :=
    (convex_ball (0 : Fin n → ℂ) δ).isPreconnected
  have h0V : (0 : Fin n → ℂ) ∈ ball (0 : Fin n → ℂ) δ := mem_ball_self hδpos
  set d : ℕ := Multiset.card (sliceRoots f t (0 : Fin n → ℂ)) with hd
  have hcard : ∀ y ∈ ball (0 : Fin n → ℂ) δ, Multiset.card (sliceRoots f t y) = d := fun y hy =>
    _root_.HTGeometry.card_sliceRoots_const_of_isPreconnected isOpen_ball hVopen hfd htpos
      hdisc hnez hadm hVconn hy h0V
  set a : ℕ → (Fin n → ℂ) → ℂ :=
    fun j y => (-1) ^ (d - j) * (sliceRoots f t y).esymm (d - j) with ha
  have hadiff : ∀ j, DifferentiableOn ℂ (a j) (ball (0 : Fin n → ℂ) δ) := fun j =>
    (_root_.HTGeometry.differentiableOn_esymm_sliceRoots isOpen_ball hVopen hfd htpos hdisc hnez
      hadm (d - j)).const_mul ((-1 : ℂ) ^ (d - j))
  have haA : ∀ j, AnalyticAt ℂ (a j) (0 : Fin n → ℂ) := fun j =>
    analyticAt_of_differentiableOn isOpen_ball (hadiff j) h0V
  have hazero : ∀ j, j < d → a j (0 : Fin n → ℂ) = 0 := by
    intro j hj
    have hzero : (sliceRoots f t (0 : Fin n → ℂ)).esymm (d - j) = 0 :=
      _root_.HTGeometry.esymm_eq_zero_of_forall_eq_zero
        (_root_.HTGeometry.sliceRoots_eq_zero_of_isolated htpos (hadm _ h0V) hiso) (by omega)
    show (-1 : ℂ) ^ (d - j) * (sliceRoots f t (0 : Fin n → ℂ)).esymm (d - j) = 0
    rw [hzero, mul_zero]
  have hmonic : ∀ y ∈ ball (0 : Fin n → ℂ) δ, ∀ z : ℂ,
      multisetLinearProd (sliceRoots f t y) z
        = z ^ d + ∑ j ∈ Finset.range d, a j y * z ^ j := by
    intro y hy z
    rw [_root_.HTGeometry.multisetLinearProd_eq_monic, hcard y hy]
  -- the preparation on the polydisc
  obtain ⟨-, hudiff, hprep⟩ :=
    _root_.HTGeometry.weierstrass_preparation isOpen_ball hVopen hfd htpos hdisc hnez hadm hVconn
      h0V
  have huA : AnalyticAt ℂ (_root_.HTGeometry.sliceUnit f t) (0 : Fin (n + 1) → ℂ) :=
    analyticAt_of_differentiableOn (isOpen_prepPolydisc t δ) hudiff
      (zero_mem_prepPolydisc htpos hδpos)
  have hcons0 : (Fin.cons (0 : ℂ) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) = 0 := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp
  have hu0 : _root_.HTGeometry.sliceUnit f t (0 : Fin (n + 1) → ℂ) ≠ 0 := by
    have := (hprep 0 h0V 0 (by simpa using htpos)).2
    rwa [hcons0] at this
  refine ⟨d, fun j => analyticGermOf (haA j), analyticGermOf huA, ?_, ?_, ?_, ?_⟩
  · rw [isUnit_analyticGerm_iff, analyticGermValue_of huA]
    exact hu0
  · intro j hj
    rw [analyticGermValue_of (haA j)]
    exact hazero j hj
  · -- the preparation identity as germs
    refine Subtype.ext ?_
    have hcoe : (((germCoord n ^ d
          + ∑ j ∈ Finset.range d, germTail n (analyticGermOf (haA j)) * germCoord n ^ j)
        * analyticGermOf huA : AnalyticGerm (0 : Fin (n + 1) → ℂ)) :
          Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
        = ((fun w : Fin (n + 1) → ℂ =>
            ((w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j)
              * _root_.HTGeometry.sliceUnit f t w) : (Fin (n + 1) → ℂ) → ℂ) := by
      rw [Subring.coe_mul, coe_germDistinguished haA]
      rfl
    rw [hcoe]
    refine (Germ.coe_eq.mpr ?_).symm
    filter_upwards [(isOpen_prepPolydisc t δ).mem_nhds (zero_mem_prepPolydisc htpos hδpos)]
      with w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hmainw := (hprep (Fin.tail w) hw1 (w 0) hw2).1
    rw [_root_.HTGeometry.sliceWeierstrass_cons, hmonic (Fin.tail w) hw1 (w 0),
      Fin.cons_self_tail] at hmainw
    exact hmainw.symm
  -- the independence
  intro q β hrel
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hq0 : q = 0 := by
      rw [hd0] at hrel
      simpa using hrel
    exact ⟨hq0, fun j hj => absurd hj (by omega)⟩
  obtain ⟨Q, hQA, hQeq⟩ := q.2
  choose B hBA hBeq using fun j : ℕ => (β j).2
  have hqeq : q = analyticGermOf hQA := Subtype.ext hQeq.symm
  have hβeq : ∀ j, β j = analyticGermOf (hBA j) := fun j => Subtype.ext (hBeq j).symm
  -- the relation between functions, near the origin
  have hfun : ((fun w : Fin (n + 1) → ℂ =>
      Q w * ((w 0) ^ d + ∑ j ∈ Finset.range d, a j (Fin.tail w) * (w 0) ^ j)
        + ∑ j ∈ Finset.range d, B j (Fin.tail w) * (w 0) ^ j) :
        (Fin (n + 1) → ℂ) → ℂ) =ᶠ[𝓝 (0 : Fin (n + 1) → ℂ)] 0 := by
    have hcoerce := congrArg
      (fun x : AnalyticGerm (0 : Fin (n + 1) → ℂ) => (x : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)) hrel
    simp only at hcoerce
    rw [Subring.coe_add, Subring.coe_mul, hqeq] at hcoerce
    simp only [hβeq] at hcoerce
    rw [coe_germDistinguished haA, coe_germPolyTail hBA, ZeroMemClass.coe_zero] at hcoerce
    exact Germ.coe_eq.mp hcoerce
  obtain ⟨rE, hrE, hEspec⟩ := Metric.eventually_nhds_iff.mp hfun
  obtain ⟨rQ, hrQ, hQball⟩ := exists_ball_analyticOnNhd hQA
  set s : ℝ := min rQ rE with hs
  have hspos : 0 < s := lt_min hrQ hrE
  set t₁ : ℝ := min t (s / 2) with ht₁
  have ht₁pos : 0 < t₁ := lt_min htpos (by linarith)
  have ht₁t : t₁ ≤ t := min_le_left _ _
  obtain ⟨δ₂, hδ₂, hδ₂spec⟩ :=
    exists_param_ball_roots_lt (a := a) hdpos (fun j => (haA j).continuousAt) hazero htpos.le
      ht₁pos
  set δ₁ : ℝ := min (min δ (s / 2)) δ₂ with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min hδpos (by linarith)) hδ₂
  have hsub : prepPolydisc (n := n) t₁ δ₁ ⊆ ball (0 : Fin (n + 1) → ℂ) (s / 2) :=
    prepPolydisc_subset_ball (min_le_right _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have hsball : ∀ w ∈ prepPolydisc (n := n) t₁ δ₁, ‖w‖ < s / 2 := by
    intro w hw
    simpa [dist_zero_right] using mem_ball.mp (hsub hw)
  -- the pointwise relation on the shrunken polydisc
  have hpt : ∀ y : Fin n → ℂ, ‖y‖ < δ₁ → ∀ z : ℂ, ‖z‖ < t₁ →
      Q (Fin.cons z y) * multisetLinearProd (sliceRoots f t y) z
        + ∑ j ∈ Finset.range d, B j y * z ^ j = 0 := by
    intro y hy z hz
    have hmem : (Fin.cons z y : Fin (n + 1) → ℂ) ∈ prepPolydisc (n := n) t₁ δ₁ := by
      refine ⟨?_, ?_⟩
      · rw [Fin.tail_cons, mem_ball, dist_zero_right]
        exact hy
      · rw [Fin.cons_zero]
        exact hz
    have hyV : y ∈ ball (0 : Fin n → ℂ) δ := by
      rw [mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_left _ _))
    have hdist : dist (Fin.cons z y : Fin (n + 1) → ℂ) 0 < rE := by
      rw [dist_zero_right]
      refine lt_of_lt_of_le (hsball _ hmem) ?_
      have : s ≤ rE := min_le_right _ _
      linarith
    have hval := hEspec hdist
    simp only [Pi.zero_apply, Fin.tail_cons, Fin.cons_zero] at hval
    rw [hmonic y hyV z]
    exact hval
  -- roots are small on the shrunken parameter ball
  have hsmall : ∀ y : Fin n → ℂ, ‖y‖ < δ₁ → ∀ ρ ∈ sliceRoots f t y, ‖ρ‖ < t₁ := by
    intro y hy ρ hρ
    have hyV : y ∈ ball (0 : Fin n → ℂ) δ := by
      rw [mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_left _ _))
    have hρt : ‖ρ‖ ≤ t :=
      (_root_.HTGeometry.sliceRoots_norm_lt htpos (hadm y hyV) ρ hρ).le
    have hroot : ρ ^ d + ∑ j ∈ Finset.range d, a j y * ρ ^ j = 0 := by
      rw [← hmonic y hyV ρ]
      exact (_root_.HTGeometry.multisetLinearProd_eq_zero_iff _ ρ).mpr hρ
    exact hδ₂spec y (lt_of_lt_of_le hy (min_le_right _ _)) ρ hρt hroot
  -- apply the slice independence for each parameter
  have hkill : ∀ y : Fin n → ℂ, ‖y‖ < δ₁ →
      (∀ j, j < d → B j y = 0) ∧ ∀ z ∈ ball (0 : ℂ) t₁, Q (Fin.cons z y) = 0 := by
    intro y hy
    have hyV : y ∈ ball (0 : Fin n → ℂ) δ := by
      rw [mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hy (le_trans (min_le_left _ _) (min_le_left _ _))
    refine lowDegree_and_quotient_eq_zero (hsmall y hy) ?_ (hcard y hyV).symm ?_
    · intro z hz
      have hin : (Fin.cons z y : Fin (n + 1) → ℂ) ∈ prepPolydisc (n := n) t₁ δ₁ := by
        refine ⟨?_, ?_⟩
        · rw [Fin.tail_cons, mem_ball, dist_zero_right]
          exact hy
        · rw [Fin.cons_zero]
          simpa [dist_zero_right] using mem_ball.mp hz
      have hsQ : s / 2 ≤ rQ := by
        have hle : s ≤ rQ := min_le_left _ _
        have : 0 < s := hspos
        linarith
      have hmem : (Fin.cons z y : Fin (n + 1) → ℂ) ∈ ball (0 : Fin (n + 1) → ℂ) rQ := by
        rw [mem_ball, dist_zero_right]
        have h2 := hsball _ hin
        linarith
      have hQc : ContinuousAt Q (Fin.cons z y) := (hQball _ hmem).continuousAt
      have hcc : ContinuousAt (fun w : ℂ => (Fin.cons w y : Fin (n + 1) → ℂ)) z :=
        (_root_.HTGeometry.differentiable_consFirst y z).continuousAt
      exact (ContinuousAt.comp (x := z) hQc hcc).continuousWithinAt
    · intro z hz
      exact hpt y hy z (by simpa [dist_zero_right] using mem_ball.mp hz)
  constructor
  · refine Subtype.ext ?_
    rw [hqeq, ZeroMemClass.coe_zero, analyticGermOf_val]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [(isOpen_prepPolydisc t₁ δ₁).mem_nhds (zero_mem_prepPolydisc ht₁pos hδ₁pos)]
      with w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hy : ‖Fin.tail w‖ < δ₁ := by simpa [dist_zero_right] using mem_ball.mp hw1
    have := (hkill (Fin.tail w) hy).2 (w 0) (by
      rw [mem_ball, dist_zero_right]
      exact hw2)
    rwa [Fin.cons_self_tail] at this
  · intro j hj
    refine Subtype.ext ?_
    rw [hβeq j, ZeroMemClass.coe_zero, analyticGermOf_val]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [ball_mem_nhds (0 : Fin n → ℂ) hδ₁pos] with y hy
    exact (hkill y (by simpa [dist_zero_right] using mem_ball.mp hy)).1 j hj

end GaloisForLFunctions.HTGeometry
