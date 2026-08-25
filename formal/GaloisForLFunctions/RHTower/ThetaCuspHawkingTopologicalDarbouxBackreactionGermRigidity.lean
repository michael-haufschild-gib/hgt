import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalDarbouxAlgebraicallySpecialCrossing

/-!
# Massless-germ rigidity of theta-mirror Starobinsky crossings

For a theta divisor with real coordinate `a`, the two reflected algebraically-special masses
at overtone `n` are positive rational functions with denominators linear in `n`.  Both masses,
and hence their midpoint, converge to zero.  If `a ≠ 1/2`, the two masses are distinct at every
overtone and the product of their forward Starobinsky factors is strictly negative at each
midpoint.  Negative crossing chambers therefore occur in every positive mass neighborhood of
the massless topological black hole.

Consequently the all-mass sign criterion can be replaced by a germ at zero mass.  Equivalently,
any continuous horizon-mass history which starts at zero and reaches one positive value crosses a
negative chamber for every tilted theta fibre.  No monotonicity or lower bound on the absorbed
mass is required.

These results concern the exact analytically continued Darboux--Starobinsky determinant.  A
physical RH proof still requires the nonlinear Einstein--Teukolsky optical identity which makes
its theta-mirror product nonnegative along the absorbed-mass history; ordinary passivity alone
does not give that continuation sign.

**[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Algebraically-special masses of a fixed theta fibre converge to the massless background as
the gravitational overtone tends to infinity. -/
theorem tendsto_d4BMXiThetaMirrorAlgebraicallySpecialMass_atTop_zero
    (q : XiZeroCopy) :
    Tendsto (fun n : ℕ => d4BMXiThetaMirrorAlgebraicallySpecialMass n q)
      atTop (𝓝 0) := by
  unfold d4BMXiThetaMirrorAlgebraicallySpecialMass
  let a : ℝ := (q.1 : ℂ).re
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h4 : Tendsto (fun n : ℕ => (4 : ℝ) * n) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have hshift :
      Tendsto (fun n : ℕ => (4 : ℝ) * n + (3 - a)) atTop atTop :=
    h4.atTop_add tendsto_const_nhds
  have hden :
      Tendsto (fun n : ℕ => 12 * ((4 : ℝ) * n + (3 - a))) atTop atTop :=
    hshift.const_mul_atTop (by norm_num)
  have hdiv := Tendsto.div_atTop
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => a * (1 - a) * (2 - a) * (3 - a)) atTop
      (𝓝 (a * (1 - a) * (2 - a) * (3 - a)))) hden
  simpa [a, sub_eq_add_neg, add_assoc] using hdiv

/-- Midpoints of the two theta-reflected algebraically-special masses converge to zero. -/
theorem tendsto_d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint_atTop_zero
    (q : XiZeroCopy) :
    Tendsto (fun n : ℕ =>
      d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint n q)
      atTop (𝓝 0) := by
  have hq := tendsto_d4BMXiThetaMirrorAlgebraicallySpecialMass_atTop_zero q
  have href := tendsto_d4BMXiThetaMirrorAlgebraicallySpecialMass_atTop_zero
    (xiZeroCopyReflectEquiv q)
  simpa [d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint] using
    (hq.add href).div_const 2

/-- Every tilted theta fibre has a strictly negative Starobinsky crossing product below every
positive mass scale. -/
theorem exists_d4BMXiThetaMirror_negativeCrossing_below
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ n : ℕ, ∃ M : ℝ,
      0 < M ∧ M < delta ∧
        d4BMXiThetaMirrorStarobinskyCrossingProduct n M q < 0 := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1
    (tendsto_d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint_atTop_zero q))
      delta hdelta
  let M := d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint N q
  have hMpos : 0 < M :=
    d4BMXiThetaMirrorAlgebraicallySpecialMassMidpoint_pos N q
  have hdist := hN N le_rfl
  have hMlt : M < delta := by
    simpa [M, Real.dist_eq, abs_of_pos hMpos] using hdist
  exact ⟨N, M, hMpos, hMlt,
    d4BMXiThetaMirrorStarobinskyCrossingProduct_midpoint_neg_of_tilted
      N q htilt⟩

/-- Nonnegativity on an arbitrary positive mass germ is already the critical-line equation for
one theta fibre. -/
theorem d4BMXiThetaMirrorStarobinskyCrossingProduct_nonnegative_germ_iff
    (q : XiZeroCopy) {delta : ℝ} (hdelta : 0 < delta) :
    (∀ n : ℕ, ∀ M : ℝ, 0 ≤ M → M < delta →
      0 ≤ d4BMXiThetaMirrorStarobinskyCrossingProduct n M q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hpass
    by_contra htilt
    obtain ⟨n, M, hMpos, hMlt, hneg⟩ :=
      exists_d4BMXiThetaMirror_negativeCrossing_below q htilt hdelta
    exact (not_lt_of_ge (hpass n M hMpos.le hMlt)) hneg
  · intro hline n M _ _
    exact (d4BMXiThetaMirrorStarobinskyCrossingProduct_nonnegative_all_mass_iff
      n q).2 hline M

/-- All theta-mirror Starobinsky products are nonnegative in one fixed mass neighborhood. -/
def D4BMXiThetaMirrorBackreactionGermPassive (delta : ℝ) : Prop :=
  ∀ q : XiZeroCopy, ∀ n : ℕ, ∀ M : ℝ,
    0 ≤ M → M < delta →
      0 ≤ d4BMXiThetaMirrorStarobinskyCrossingProduct n M q

/-- At every positive mass resolution, theta-mirror Starobinsky germ passivity is equivalent to
the Riemann hypothesis. -/
theorem riemannHypothesis_iff_d4BMXiThetaMirrorBackreactionGermPassive
    {delta : ℝ} (hdelta : 0 < delta) :
    RiemannHypothesis ↔ D4BMXiThetaMirrorBackreactionGermPassive delta := by
  constructor
  · intro hRH q
    apply (d4BMXiThetaMirrorStarobinskyCrossingProduct_nonnegative_germ_iff
      q hdelta).2
    have him := xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q
    rw [xiSpectralPoint_im_eq] at him
    linarith
  · intro hpass
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (d4BMXiThetaMirrorStarobinskyCrossingProduct_nonnegative_germ_iff
        q hdelta).1 (hpass q)
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · rw [xiSpectralPoint_im_eq]
      simp
      linarith

/-- A continuous nontrivial absorbed-mass history crosses a negative Starobinsky chamber in every
tilted theta fibre. -/
theorem exists_d4BMXiThetaMirror_path_negativeCrossing
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (massPath : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn massPath (Icc 0 T))
    (hzero : massPath 0 = 0) (hpositive : 0 < massPath T) :
    ∃ n : ℕ, ∃ t ∈ Icc (0 : ℝ) T,
      d4BMXiThetaMirrorStarobinskyCrossingProduct n (massPath t) q < 0 := by
  obtain ⟨n, M, hMpos, hMlt, hneg⟩ :=
    exists_d4BMXiThetaMirror_negativeCrossing_below q htilt hpositive
  have hMmem : M ∈ Icc (massPath 0) (massPath T) := by
    rw [hzero]
    exact ⟨hMpos.le, hMlt.le⟩
  obtain ⟨t, ht, hMt⟩ := (intermediate_value_Icc hT hcontinuous) hMmem
  exact ⟨n, t, ht, by simpa [hMt] using hneg⟩

/-- If the theta-mirror crossing product stays nonnegative along one continuous nontrivial
absorbed-mass history at every overtone, the fibre lies on the critical line. -/
theorem d4BMXiThetaMirror_re_eq_half_of_path_nonnegative
    (q : XiZeroCopy) (massPath : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn massPath (Icc 0 T))
    (hzero : massPath 0 = 0) (hpositive : 0 < massPath T)
    (hpass : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T,
      0 ≤ d4BMXiThetaMirrorStarobinskyCrossingProduct n (massPath t) q) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra htilt
  obtain ⟨n, t, ht, hneg⟩ := exists_d4BMXiThetaMirror_path_negativeCrossing
    q htilt massPath hT hcontinuous hzero hpositive
  exact (not_lt_of_ge (hpass n t ht)) hneg

end

end RHTower
