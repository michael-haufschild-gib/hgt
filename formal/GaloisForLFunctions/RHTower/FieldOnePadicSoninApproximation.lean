import GaloisForLFunctions.RHTower.FieldOnePadicUnitInvariantL2

/-!
# Exact radial Bruhat approximation of p-adic unit invariants

The Haar radialization of Bruhat functions is again Bruhat.  Combining that
fact with the dense Bruhat embedding and the literal Sonin gap projection gives
radial Bruhat approximants which preserve the physical gap exactly.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal NNReal ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

def fieldOnePadicBruhatRestrict (s : Set ℚ_[p]) (hs : IsClopen s)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  ⟨f.1.indicator hs, f.2.mono (by
    intro x hx
    by_contra hfx
    apply hx
    rw [LocallyConstant.indicator_apply_eq_if]
    split_ifs <;> simp_all)⟩

theorem fieldOnePadicBruhatRestrict_apply
    (s : Set ℚ_[p]) (hs : IsClopen s)
    (f : compactlySupportedLocallyConstant ℚ_[p]) (x : ℚ_[p]) :
    (fieldOnePadicBruhatRestrict p s hs f).1 x =
      s.indicator f.1 x := by
  classical
  change (f.1.indicator hs) x = s.indicator f.1 x
  rw [LocallyConstant.indicator_apply_eq_if]
  rfl

theorem fieldOnePadicBruhatToL2_restrict
    (s : Set ℚ_[p]) (hs : IsClopen s)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicBruhatRestrict p s hs f) =
      fieldOnePadicL2SetProjection p s hs.isOpen.measurableSet
        (fieldOnePadicBruhatToL2Linear p f) := by
  apply Lp.ext
  filter_upwards [fieldOnePadicBruhatToL2_ae p
      (fieldOnePadicBruhatRestrict p s hs f),
    fieldOnePadicL2SetProjection_ae p s hs.isOpen.measurableSet
      (fieldOnePadicBruhatToL2Linear p f),
    fieldOnePadicBruhatToL2_ae p f] with x hres hproj hf
  have hres' :
      ((fieldOnePadicBruhatToL2Linear p
          (fieldOnePadicBruhatRestrict p s hs f) : FieldOnePadicL2 p) :
            ℚ_[p] → ℂ) x =
        (fieldOnePadicBruhatRestrict p s hs f).1 x := by
    exact hres
  have hf' :
      ((fieldOnePadicBruhatToL2Linear p f : FieldOnePadicL2 p) :
            ℚ_[p] → ℂ) x = f.1 x := by
    exact hf
  rw [hres', hproj, fieldOnePadicBruhatRestrict_apply]
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx, hf']

theorem norm_fieldOnePadicL2SetProjection_le
    (s : Set ℚ_[p]) (hs : MeasurableSet s) (f : FieldOnePadicL2 p) :
    ‖fieldOnePadicL2SetProjection p s hs f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).indicator hs).toLp
    (s.indicator fun x => f x)‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_indicator_le fun x => f x)

theorem dist_fieldOnePadicL2SetProjection_le
    (s : Set ℚ_[p]) (hs : MeasurableSet s)
    (f g : FieldOnePadicL2 p) :
    dist (fieldOnePadicL2SetProjection p s hs f)
        (fieldOnePadicL2SetProjection p s hs g) ≤ dist f g := by
  simp only [dist_eq_norm, ← map_sub]
  exact norm_fieldOnePadicL2SetProjection_le p s hs (f - g)

theorem fieldOnePadicL2SetProjection_compl_eq_self_of_eq_zero
    (s : Set ℚ_[p]) (hs : MeasurableSet s) (f : FieldOnePadicL2 p)
    (hf : fieldOnePadicL2SetProjection p s hs f = 0) :
    fieldOnePadicL2SetProjection p sᶜ hs.compl f = f := by
  apply Lp.ext
  filter_upwards [fieldOnePadicL2SetProjection_ae p sᶜ hs.compl f,
    fieldOnePadicL2SetProjection_ae p s hs f,
    Lp.coeFn_zero ℂ 2 (fieldOnePadicUnitBallNormalizedHaar p)]
    with x hcompl hin hzero
  have hz : s.indicator (fun x => f x) x = 0 := by
    rw [← hin, hf, hzero]
    rfl
  rw [hcompl]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_notMem (by simpa using hx)]
    have := hz
    rw [Set.indicator_of_mem hx] at this
    exact this.symm
  · rw [Set.indicator_of_mem (by simpa using hx)]

def fieldOnePadicSoninBruhatGapCut
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicBruhatRestrict p (fieldOnePadicSoninInnerBall p)ᶜ
    (fieldOnePadicSoninBallSet_isClopen p (-1)).compl f

theorem fieldOnePadicSoninBruhatGapCut_zero
    (f : compactlySupportedLocallyConstant ℚ_[p])
    {x : ℚ_[p]} (hx : x ∈ fieldOnePadicSoninInnerBall p) :
    (fieldOnePadicSoninBruhatGapCut p f).1 x = 0 := by
  rw [fieldOnePadicSoninBruhatGapCut,
    fieldOnePadicBruhatRestrict_apply,
    Set.indicator_of_notMem (by simpa using hx)]

theorem fieldOnePadicBruhatToL2_soninGapCut
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicSoninBruhatGapCut p f) =
      fieldOnePadicL2SetProjection p
        (fieldOnePadicSoninInnerBall p)ᶜ
        (fieldOnePadicSoninInnerBall_measurable p).compl
        (fieldOnePadicBruhatToL2Linear p f) := by
  exact fieldOnePadicBruhatToL2_restrict p _ _ f

theorem exists_radial_bruhat_gap_approx
    {f : FieldOnePadicL2 p}
    (hunit : f ∈ FieldOnePadicUnitInvariantL2 p)
    (hgap : fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p) f = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : compactlySupportedLocallyConstant ℚ_[p],
      (∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
        g.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = g.1 x) ∧
      (∀ x ∈ fieldOnePadicSoninInnerBall p, g.1 x = 0) ∧
      dist f (fieldOnePadicBruhatToL2Linear p g) < ε := by
  obtain ⟨h, hh⟩ :=
    (fieldOnePadicBruhatToL2Linear_denseRange p).exists_dist_lt f hε
  let hcut := fieldOnePadicSoninBruhatGapCut p h
  let g := fieldOnePadicRadializeBruhat p hcut
  refine ⟨g, ?_, ?_, ?_⟩
  · intro u x
    exact fieldOnePadicRadializeBruhat_unitInvariant p hcut u x
  · intro x hx
    rw [fieldOnePadicRadializeBruhat_apply]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun u => by
      change hcut.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = 0
      change (fieldOnePadicSoninBruhatGapCut p h).1
        ((((u : ℤ_[p]) : ℚ_[p])) * x) = 0
      apply fieldOnePadicSoninBruhatGapCut_zero p h
      change (((u : ℤ_[p]) : ℚ_[p])) * x ∈
        fieldOnePadicSoninBallSet p (-1)
      rcases eq_or_ne x 0 with rfl | hx0
      · refine ⟨(0 : ℤ_[p]), ?_⟩
        simp
      rw [fieldOnePadicSoninBallSet_mem_iff_valuation p (-1)
        (mul_ne_zero (PadicInt.coe_ne_zero.mpr (Units.ne_zero u)) hx0)]
      change x ∈ fieldOnePadicSoninBallSet p (-1) at hx
      have hv := (fieldOnePadicSoninBallSet_mem_iff_valuation p (-1) hx0).mp hx
      rw [Padic.valuation_mul]
      · rw [fieldOnePadic_valuation_coe_unit]
        omega
      · exact PadicInt.coe_ne_zero.mpr (Units.ne_zero u)
      · exact hx0
  · change dist f (fieldOnePadicBruhatToL2Linear p
      (fieldOnePadicRadializeBruhat p hcut)) < ε
    rw [← fieldOnePadicUnitAverageL2_bruhat]
    rw [dist_comm]
    apply lt_of_le_of_lt
      (dist_fieldOnePadicUnitAverageL2_le_of_invariant p
        (fieldOnePadicBruhatToL2Linear p hcut) hunit)
    rw [fieldOnePadicBruhatToL2_soninGapCut]
    have hfcompl := fieldOnePadicL2SetProjection_compl_eq_self_of_eq_zero
      p (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p) f hgap
    rw [dist_comm, ← hfcompl]
    exact lt_of_le_of_lt
      (dist_fieldOnePadicL2SetProjection_le p _ _ f
        (fieldOnePadicBruhatToL2Linear p h)) hh

end

end GaloisForLFunctions.RHTower
