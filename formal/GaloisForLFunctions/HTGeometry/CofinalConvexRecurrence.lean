import Mathlib

/-!
# Cofinal convex recurrence of a vector path

A path in a finite-dimensional real normed space whose every nonzero linear observable
becomes strictly negative after every time cannot be confined to any closed half-space
through the origin, even asymptotically. The consequence is much stronger than sign change
of the individual coordinates: the origin is an interior point of the convex hull of every
cofinal tail.

Interiority is proved by compactness of the dual sphere. Finitely many tail points already
make every unit observable strictly negative; a uniform margin then follows, and strict
separation of a small vector from the hull of those finitely many points would contradict
that margin.

Carathéodory's theorem converts interiority into a finite exact statement: at most
`finrank + 1` distinct arbitrarily late times carry a positive probability weight that
annihilates the path exactly.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every nonzero linear observable of the path becomes strictly negative after every time. -/
def CofinalHalfSpaceEscape (V : ℝ → E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, f ≠ 0 → ∀ T : ℝ, ∃ t, T < t ∧ f (V t) < 0

/-- **Cofinal convex recurrence.** The origin is interior to the convex hull of every
cofinal tail of a path that escapes every closed half-space. -/
theorem zero_mem_interior_convexHull_image_Ioi
    {V : ℝ → E} (hV : CofinalHalfSpaceEscape V) (T : ℝ) :
    (0 : E) ∈ interior (convexHull ℝ (V '' Set.Ioi T)) := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hmem : V (T + 1) ∈ V '' Set.Ioi T := ⟨T + 1, by simp, rfl⟩
    have huniv : convexHull ℝ (V '' Set.Ioi T) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x = V (T + 1) := Subsingleton.elim _ _
      exact subset_convexHull ℝ _ (hx ▸ hmem)
    rw [huniv, interior_univ]
    trivial
  · obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
    obtain ⟨f0, hf0norm, -⟩ := exists_dual_vector ℝ x0 (by simpa using hx0)
    have hsphere_ne : (Metric.sphere (0 : E →L[ℝ] ℝ) 1).Nonempty :=
      ⟨f0, by simpa using hf0norm⟩
    have hcover : Metric.sphere (0 : E →L[ℝ] ℝ) 1 ⊆
        ⋃ t ∈ Set.Ioi T, {h : E →L[ℝ] ℝ | h (V t) < 0} := by
      intro h hh
      have hne : h ≠ 0 := by
        intro hzero
        rw [hzero] at hh
        simp at hh
      obtain ⟨t, ht, hlt⟩ := hV h hne T
      exact Set.mem_biUnion ht hlt
    obtain ⟨Ts, hTsub, hTfin, hTcover⟩ :=
      (isCompact_sphere (0 : E →L[ℝ] ℝ) 1).elim_finite_subcover_image
        (fun t _ => isOpen_lt (by fun_prop) continuous_const) hcover
    set P : Finset E := insert (V (T + 1)) (hTfin.toFinset.image V) with hPdef
    have hPne : P.Nonempty := ⟨V (T + 1), Finset.mem_insert_self _ _⟩
    have hPsub : (P : Set E) ⊆ V '' Set.Ioi T := by
      intro x hx
      simp only [hPdef, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image,
        Set.mem_image, Set.Finite.mem_toFinset, Finset.mem_coe] at hx
      rcases hx with rfl | ⟨t, ht, rfl⟩
      · exact ⟨T + 1, by simp, rfl⟩
      · exact ⟨t, hTsub (by simpa using ht), rfl⟩
    have hVTP : V (T + 1) ∈ P := Finset.mem_insert_self _ _
    have hneg : ∀ h ∈ Metric.sphere (0 : E →L[ℝ] ℝ) 1, ∃ x ∈ P, h x < 0 := by
      intro h hh
      obtain ⟨t, ht, hlt⟩ := Set.mem_iUnion₂.mp (hTcover hh)
      refine ⟨V t, ?_, hlt⟩
      refine Finset.mem_insert_of_mem ?_
      exact Finset.mem_image.mpr ⟨t, by simpa using ht, rfl⟩
    set g : (E →L[ℝ] ℝ) → ℝ := fun h => P.inf' hPne (fun x => h x) with hgdef
    have hgcont : Continuous g := by fun_prop
    have hgneg : ∀ h ∈ Metric.sphere (0 : E →L[ℝ] ℝ) 1, g h < 0 := by
      intro h hh
      obtain ⟨x, hxP, hx⟩ := hneg h hh
      exact lt_of_le_of_lt (Finset.inf'_le _ hxP) hx
    obtain ⟨c0, hc0, hc0max⟩ :=
      (isCompact_sphere (0 : E →L[ℝ] ℝ) 1).exists_isMaxOn hsphere_ne hgcont.continuousOn
    set δ : ℝ := -(g c0) with hδdef
    have hδpos : 0 < δ := by
      have := hgneg c0 hc0
      simp only [hδdef]
      linarith
    have hball : Metric.ball (0 : E) δ ⊆ convexHull ℝ (P : Set E) := by
      intro v hv
      by_contra hvD
      obtain ⟨f, u, u', hfD, huu', hfv⟩ :=
        geometric_hahn_banach_compact_closed
          (convex_convexHull ℝ _) (Finite.isCompact_convexHull ℝ P.finite_toSet)
          (convex_singleton v) isClosed_singleton
          (Set.disjoint_singleton_right.mpr hvD)
      have hfvlt : u' < f v := hfv v rfl
      have hbase : f (V (T + 1)) < u := hfD _ (subset_convexHull ℝ _ (by exact_mod_cast hVTP))
      have hfne : f ≠ 0 := by
        intro hf0
        rw [hf0] at hbase hfvlt
        simp only [zero_apply] at hbase hfvlt
        linarith
      have hfnorm : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hfne
      set c : E →L[ℝ] ℝ := ‖f‖⁻¹ • f with hcdef
      have hcnorm : ‖c‖ = 1 := by
        rw [hcdef, norm_smul, norm_inv, norm_norm]
        field_simp
      have hnegc : -c ∈ Metric.sphere (0 : E →L[ℝ] ℝ) 1 := by
        simp only [Metric.mem_sphere, dist_zero_right, norm_neg]
        exact hcnorm
      obtain ⟨x, hxP, hxval⟩ := Finset.exists_mem_eq_inf' hPne (fun y => (-c) y)
      have hgle : g (-c) ≤ -δ := by
        have hmax := hc0max hnegc
        simp only [Set.mem_setOf_eq] at hmax
        simp only [hδdef]
        linarith
      have hxle : (-c) x ≤ -δ := by
        rw [hgdef] at hgle
        simpa [← hxval] using hgle
      have hcx : δ ≤ c x := by
        simp only [neg_apply] at hxle
        linarith
      have hfx : f x < f v := by
        have := hfD _ (subset_convexHull ℝ _ (by exact_mod_cast hxP))
        linarith
      have hcxv : c x < c v := by
        simp only [hcdef, smul_apply, smul_eq_mul]
        exact mul_lt_mul_of_pos_left hfx (by positivity)
      have hcv : c v ≤ ‖v‖ := by
        have h1 : ‖c v‖ ≤ ‖c‖ * ‖v‖ := c.le_opNorm v
        rw [hcnorm, one_mul] at h1
        exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h1)
      have hvlt : ‖v‖ < δ := by simpa [Real.norm_eq_abs, dist_zero_right] using hv
      linarith
    have hsub : convexHull ℝ (P : Set E) ⊆ convexHull ℝ (V '' Set.Ioi T) :=
      convexHull_mono hPsub
    exact mem_interior.mpr
      ⟨Metric.ball 0 δ, hball.trans hsub, Metric.isOpen_ball, Metric.mem_ball_self hδpos⟩

/-- **Exact cofinal positive quadrature.** A path escaping every closed half-space carries,
after every time, at most `finrank + 1` distinct times whose positive probability weights
annihilate it exactly. -/
theorem exists_cofinal_positive_quadrature
    {V : ℝ → E} (hV : CofinalHalfSpaceEscape V) (T : ℝ) :
    ∃ (nodes : Finset ℝ) (w : ℝ → ℝ),
      nodes.Nonempty ∧
      nodes.card ≤ Module.finrank ℝ E + 1 ∧
      (∀ t ∈ nodes, T < t) ∧
      (∀ t ∈ nodes, 0 < w t) ∧
      (∑ t ∈ nodes, w t) = 1 ∧
      (∑ t ∈ nodes, w t • V t) = 0 := by
  classical
  have hmem : (0 : E) ∈ convexHull ℝ (V '' Set.Ioi T) :=
    interior_subset (zero_mem_interior_convexHull_image_Ioi hV T)
  obtain ⟨ι, hfin, z, w', hrange, hai, hwpos, hwsum, hwcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hmem
  have hιne : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hwsum
    exact absurd hwsum (by norm_num)
  have hzinj : Function.Injective z := hai.injective
  have hpre : ∀ i : ι, ∃ t : ℝ, T < t ∧ V t = z i := by
    intro i
    obtain ⟨t, ht, hvt⟩ := hrange (Set.mem_range_self i)
    exact ⟨t, ht, hvt⟩
  choose tt htT htV using hpre
  have httinj : Function.Injective tt := by
    intro i j hij
    apply hzinj
    rw [← htV i, ← htV j, hij]
  set nodes : Finset ℝ := Finset.univ.image tt with hnodes
  set w : ℝ → ℝ := fun s => if s ∈ Set.range tt then w' (Function.invFun tt s) else 0 with hw
  have hwval : ∀ i : ι, w (tt i) = w' i := by
    intro i
    have hmemr : tt i ∈ Set.range tt := ⟨i, rfl⟩
    simp only [hw, if_pos hmemr]
    rw [Function.leftInverse_invFun httinj i]
  have hsum : ∀ (F : ℝ → E), (∑ s ∈ nodes, F s) = ∑ i : ι, F (tt i) := by
    intro F
    rw [hnodes, Finset.sum_image (fun x _ y _ h => httinj h)]
  have hsumR : ∀ (F : ℝ → ℝ), (∑ s ∈ nodes, F s) = ∑ i : ι, F (tt i) := by
    intro F
    rw [hnodes, Finset.sum_image (fun x _ y _ h => httinj h)]
  refine ⟨nodes, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := hιne
    exact ⟨tt i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  · have hcard : nodes.card = Fintype.card ι := by
      rw [hnodes, Finset.card_image_of_injective _ httinj, Finset.card_univ]
    rw [hcard]
    refine le_trans (hai.card_le_finrank_succ) ?_
    exact Nat.add_le_add_right (Submodule.finrank_le _) 1
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact htT i
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    rw [hwval i]
    exact hwpos i
  · rw [hsumR (fun s => w s)]
    simp only [hwval]
    exact hwsum
  · rw [hsum (fun s => w s • V s)]
    simp only [hwval, htV]
    exact hwcomb

end

end GaloisForLFunctions.HTGeometry
