import GaloisForLFunctions.HTGeometry.CofinalGenerativeAdmission
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac

namespace GaloisForLFunctions.HTGeometry

open Finset Filter MeasureTheory Set
open _root_.HTGeometry
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The actual real `ell^1` sequence space used by the three-cone law. -/
abbrev AdmissionL1 := lp (fun _ : ℕ => ℝ) 1

theorem admissionL1_summable (f : AdmissionL1) : Summable fun n => f n := by
  have h := lp.hasSum_norm (E := fun _ : ℕ => ℝ) (p := 1) (by norm_num) f
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  exact Summable.of_norm ⟨‖f‖, h⟩

theorem admissionL1_norm_tsum_le (f : AdmissionL1) : |∑' n, f n| ≤ ‖f‖ := by
  have h := lp.hasSum_norm (E := fun _ : ℕ => ℝ) (p := 1) (by norm_num) f
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  calc
    |∑' n, f n| = ‖∑' n, f n‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm (admissionL1_summable f).norm
    _ = ‖f‖ := h.tsum_eq

/-- Continuous total-mass functional on real `ell^1`. -/
noncomputable def admissionL1Mass : AdmissionL1 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∑' n, f n
      map_add' := fun f g => by
        rw [← Summable.tsum_add (admissionL1_summable f) (admissionL1_summable g)]
        exact tsum_congr fun n => by simp
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun n => by simp }
    1 fun f => by simpa [Real.norm_eq_abs] using admissionL1_norm_tsum_le f

/-- Continuous evaluation of one `ell^1` coordinate. -/
noncomputable def admissionL1Coordinate (n : ℕ) : AdmissionL1 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => f n
      map_add' := fun f g => by simp
      map_smul' := fun c f => by simp }
    1 fun f => by
      simpa [Real.norm_eq_abs] using
        (lp.norm_apply_le_norm (p := (1 : ℝ≥0∞)) (by norm_num) f n)

@[simp] theorem admissionL1Coordinate_apply (n : ℕ) (f : AdmissionL1) :
    admissionL1Coordinate n f = f n := rfl

@[simp] theorem admissionL1Coordinate_single (n i : ℕ) (c : ℝ) :
    admissionL1Coordinate n (lp.single 1 i c) = if i = n then c else 0 := by
  rw [admissionL1Coordinate_apply, lp.single_apply]
  by_cases h : i = n
  · subst i
    simp
  · simp [h]

@[simp] theorem admissionL1Mass_single (n : ℕ) (c : ℝ) :
    admissionL1Mass (lp.single 1 n c) = c := by
  change (∑' k, (lp.single (E := fun _ : ℕ => ℝ) 1 n c) k) = c
  rw [tsum_eq_single n]
  · simp [lp.single_apply]
  · intro k hk
    simp [lp.single_apply, hk]

/-- A mass-zero direction admitting one global straight perturbation. -/
def l1RadialCone (w : AdmissionL1) : Set AdmissionL1 :=
  {h | admissionL1Mass h = 0 ∧ StraightAdmitted w h}

/-- Mass-zero directions pointing inward on every absent coordinate. -/
def l1ContingentCone (w : AdmissionL1) : Set AdmissionL1 :=
  {h | admissionL1Mass h = 0 ∧ ContingentlyLegal w h}

theorem l1RadialCone_subset_contingentCone (w : AdmissionL1) :
    l1RadialCone w ⊆ l1ContingentCone w := by
  rintro h ⟨hmass, hadm⟩
  exact ⟨hmass,
    contingentlyLegal_of_finitelyAdmitted (finitelyAdmitted_of_straightAdmitted hadm)⟩

theorem isClosed_l1ContingentCone (w : AdmissionL1) : IsClosed (l1ContingentCone w) := by
  have hmass : IsClosed {h : AdmissionL1 | admissionL1Mass h = 0} :=
    admissionL1Mass.isClosed_ker
  have hcoord : IsClosed {h : AdmissionL1 | ContingentlyLegal w h} := by
    have hi : IsClosed (⋂ n : ℕ, {h : AdmissionL1 | w n = 0 → 0 ≤ h n}) := by
      apply isClosed_iInter
      intro n
      by_cases hwn : w n = 0
      · have heq : {h : AdmissionL1 | w n = 0 → 0 ≤ h n} =
            {h : AdmissionL1 | 0 ≤ admissionL1Coordinate n h} := by
          ext h
          simp [hwn]
        rw [heq]
        exact isClosed_le continuous_const (admissionL1Coordinate n).continuous
      · have hall : {h : AdmissionL1 | w n = 0 → 0 ≤ h n} = Set.univ := by
          ext h
          simp [hwn]
        rw [hall]
        exact isClosed_univ
    have heq : {h : AdmissionL1 | ContingentlyLegal w h} =
        ⋂ n : ℕ, {h : AdmissionL1 | w n = 0 → 0 ≤ h n} := by
      ext h
      simp only [ContingentlyLegal, Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact hi
  exact hmass.inter hcoord

/-- Finite-support contingent directions have one common positive admission scale. -/
theorem straightAdmitted_of_finite_support {w h : ℕ → ℝ}
    (hw : ∀ n, 0 ≤ w n) (hcont : ContingentlyLegal w h)
    (F : Finset ℕ) (hsupport : ∀ n ∉ F, h n = 0) :
    StraightAdmitted w h := by
  obtain ⟨ε, hε, hF⟩ :=
    finitelyAdmitted_of_contingentlyLegal hw hcont F
  refine ⟨ε, hε, ?_⟩
  intro n
  by_cases hn : n ∈ F
  · exact hF n hn
  · rw [hsupport n hn, mul_zero, add_zero]
    exact hw n

/-- Finite truncation corrected at an occupied anchor to conserve total mass. -/
noncomputable def admissionCenteredTrunc (h : AdmissionL1) (j N : ℕ) : AdmissionL1 :=
  (∑ n ∈ Finset.range N, lp.single 1 n (h n)) -
    lp.single 1 j (∑ n ∈ Finset.range N, h n)

theorem admissionL1Coordinate_trunc (h : AdmissionL1) (N n : ℕ) :
    admissionL1Coordinate n
      (∑ i ∈ Finset.range N, lp.single 1 i (h i) : AdmissionL1) =
      if n ∈ Finset.range N then h n else 0 := by
  simp only [map_sum, admissionL1Coordinate_single]
  by_cases hn : n ∈ Finset.range N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [hbn]
    · exact fun hbad => (hbad hn).elim
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≠ n := fun h => hn (h ▸ hi)
    simp [hin]

@[simp] theorem admissionL1Mass_centeredTrunc (h : AdmissionL1) (j N : ℕ) :
    admissionL1Mass (admissionCenteredTrunc h j N) = 0 := by
  simp [admissionCenteredTrunc, map_sub, map_sum]

theorem admissionCenteredTrunc_support (h : AdmissionL1) (j N n : ℕ)
    (hn : n ∉ Finset.range N ∪ {j}) :
    admissionCenteredTrunc h j N n = 0 := by
  have hnN : n ∉ Finset.range N := fun hmem => hn (Finset.mem_union_left _ hmem)
  have hnj : n ≠ j := by
    intro hj
    subst n
    exact hn (by simp)
  change admissionL1Coordinate n (admissionCenteredTrunc h j N) = 0
  rw [admissionCenteredTrunc, map_sub, admissionL1Coordinate_trunc, if_neg hnN]
  simp [hnj]

theorem admissionCenteredTrunc_contingentlyLegal
    {w h : AdmissionL1} (hcont : ContingentlyLegal w h)
    {j : ℕ} (hwj : 0 < w j) (N : ℕ) :
    ContingentlyLegal w (admissionCenteredTrunc h j N) := by
  intro n hwn
  have hnj : n ≠ j := by
    intro h
    subst n
    exact hwj.ne' hwn
  by_cases hn : n ∈ Finset.range N
  · change 0 ≤ admissionL1Coordinate n (admissionCenteredTrunc h j N)
    rw [admissionCenteredTrunc, map_sub, admissionL1Coordinate_trunc, if_pos hn]
    simpa [hnj] using hcont n hwn
  · change 0 ≤ admissionL1Coordinate n (admissionCenteredTrunc h j N)
    rw [admissionCenteredTrunc, map_sub, admissionL1Coordinate_trunc, if_neg hn]
    simp [hnj]

theorem admissionCenteredTrunc_mem_radialCone
    {w h : AdmissionL1} (hw : ∀ n, 0 ≤ w n)
    (hcont : ContingentlyLegal w h) {j : ℕ} (hwj : 0 < w j) (N : ℕ) :
    admissionCenteredTrunc h j N ∈ l1RadialCone w := by
  refine ⟨admissionL1Mass_centeredTrunc h j N, ?_⟩
  exact straightAdmitted_of_finite_support hw
    (admissionCenteredTrunc_contingentlyLegal hcont hwj N)
    (Finset.range N ∪ {j}) (admissionCenteredTrunc_support h j N)

theorem tendsto_admissionCenteredTrunc
    {h : AdmissionL1} (hmass : admissionL1Mass h = 0) (j : ℕ) :
    Tendsto (fun N => admissionCenteredTrunc h j N) atTop (nhds h) := by
  have htrunc : Tendsto
      (fun N => ∑ n ∈ Finset.range N, lp.single 1 n (h n)) atTop (nhds h) :=
    (lp.hasSum_single (p := (1 : ℝ≥0∞)) (by norm_num) h).tendsto_sum_nat
  change (∑' n, h n) = 0 at hmass
  have hpartial : Tendsto (fun N => ∑ n ∈ Finset.range N, h n) atTop (nhds 0) := by
    simpa [hmass] using
      (admissionL1_summable h).hasSum.tendsto_sum_nat
  have hsingle : Tendsto
      (fun N => lp.single (E := fun _ : ℕ => ℝ) 1 j
        (∑ n ∈ Finset.range N, h n)) atTop (nhds 0) := by
    have hrewrite : (fun N => lp.single (E := fun _ : ℕ => ℝ) 1 j
        (∑ n ∈ Finset.range N, h n)) =
        fun N => (∑ n ∈ Finset.range N, h n) •
          lp.single (E := fun _ : ℕ => ℝ) (1 : ℝ≥0∞) j (1 : ℝ) := by
      funext N
      apply lp.ext
      funext n
      change admissionL1Coordinate n
          (lp.single (E := fun _ : ℕ => ℝ) 1 j (∑ n ∈ Finset.range N, h n)) =
        admissionL1Coordinate n
          ((∑ n ∈ Finset.range N, h n) •
            lp.single (E := fun _ : ℕ => ℝ) (1 : ℝ≥0∞) j (1 : ℝ))
      rw [map_smul]
      by_cases hn : j = n <;> simp [hn]
    rw [hrewrite]
    simpa using hpartial.smul_const
      (lp.single (E := fun _ : ℕ => ℝ) (1 : ℝ≥0∞) j (1 : ℝ))
  simpa [admissionCenteredTrunc] using htrunc.sub hsingle

theorem exists_positive_coordinate_of_mass_one
    {w : AdmissionL1} (hw : ∀ n, 0 ≤ w n) (hmass : admissionL1Mass w = 1) :
    ∃ j, 0 < w j := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ n, w n = 0 := fun n => le_antisymm (hnone n) (hw n)
  have : admissionL1Mass w = 0 := by
    change (∑' n, w n) = 0
    simp [hzero]
  linarith

/-- Exact `ell^1` closure identity in `(CAG.7)`. -/
theorem closure_l1RadialCone_eq_contingentCone
    {w : AdmissionL1} (hw : ∀ n, 0 ≤ w n) (hmass : admissionL1Mass w = 1) :
    closure (l1RadialCone w) = l1ContingentCone w := by
  apply Set.Subset.antisymm
  · exact closure_minimal (l1RadialCone_subset_contingentCone w)
      (isClosed_l1ContingentCone w)
  · intro h hh
    obtain ⟨j, hwj⟩ := exists_positive_coordinate_of_mass_one hw hmass
    rw [mem_closure_iff_seq_limit]
    exact ⟨fun N => admissionCenteredTrunc h j N,
      fun N => admissionCenteredTrunc_mem_radialCone hw hh.2 hwj N,
      tendsto_admissionCenteredTrunc hh.1 j⟩

/-! ## Coefficient faithfulness of complete oscillatory history -/

/-- Positive mass carried by one coefficient. -/
def admissionPositivePart (h : ℕ → ℝ) (n : ℕ) : ℝ := max (h n) 0

/-- Negative mass carried by one coefficient. -/
def admissionNegativePart (h : ℕ → ℝ) (n : ℕ) : ℝ := max (-h n) 0

theorem admissionPositivePart_nonneg (h : ℕ → ℝ) (n : ℕ) :
    0 ≤ admissionPositivePart h n := le_max_right _ _

theorem admissionNegativePart_nonneg (h : ℕ → ℝ) (n : ℕ) :
    0 ≤ admissionNegativePart h n := le_max_right _ _

theorem admission_positive_sub_negative (h : ℕ → ℝ) (n : ℕ) :
    admissionPositivePart h n - admissionNegativePart h n = h n := by
  simp only [admissionPositivePart, admissionNegativePart]
  rcases le_total 0 (h n) with hh | hh
  · rw [max_eq_left hh, max_eq_right (neg_nonpos.mpr hh)]
    simp
  · rw [max_eq_right hh, max_eq_left (neg_nonneg.mpr hh)]
    simp

theorem admissionL1_abs_summable (h : AdmissionL1) : Summable fun n => |h n| := by
  have hs := lp.hasSum_norm (E := fun _ : ℕ => ℝ) (p := 1) (by norm_num) h
  simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] at hs
  exact hs.summable

theorem admissionPositivePart_summable (h : AdmissionL1) :
    Summable (admissionPositivePart h) := by
  exact Summable.of_nonneg_of_le
    (admissionPositivePart_nonneg h)
    (fun n => max_le (le_abs_self _) (abs_nonneg _))
    (admissionL1_abs_summable h)

theorem admissionNegativePart_summable (h : AdmissionL1) :
    Summable (admissionNegativePart h) := by
  exact Summable.of_nonneg_of_le
    (admissionNegativePart_nonneg h)
    (fun n => max_le (neg_le_abs _) (abs_nonneg _))
    (admissionL1_abs_summable h)

/-- Complete phase history `sum h_n exp(-i t lambda_n)` from `(CAG.10)`. -/
noncomputable def admissionFourierHistory (lambda : ℕ → ℝ) (h : AdmissionL1) (t : ℝ) : ℂ :=
  ∑' n, (h n : ℂ) * Complex.exp ((((lambda n) * (-t) : ℝ) : ℂ) * Complex.I)

theorem summable_admissionPart_phase
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (lambda : ℕ → ℝ) (t : ℝ) :
    Summable fun n => (a n : ℂ) *
      Complex.exp ((((lambda n) * (-t) : ℝ) : ℂ) * Complex.I) := by
  apply Summable.of_norm
  have hnorm : (fun n => ‖(a n : ℂ) *
      Complex.exp ((((lambda n) * (-t) : ℝ) : ℂ) * Complex.I)‖) = a := by
    funext n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha n), Complex.norm_exp]
    simp
  rw [hnorm]
  exact hsum

theorem admissionFourierHistory_positive_sub_negative
    (lambda : ℕ → ℝ) (h : AdmissionL1) (t : ℝ) :
    admissionFourierHistory lambda h t =
      ∑' n, (admissionPositivePart h n : ℂ) *
        Complex.exp ((((lambda n) * (-t) : ℝ) : ℂ) * Complex.I) -
      ∑' n, (admissionNegativePart h n : ℂ) *
        Complex.exp ((((lambda n) * (-t) : ℝ) : ℂ) * Complex.I) := by
  have hp := summable_admissionPart_phase (admissionPositivePart h)
    (admissionPositivePart_nonneg h) (admissionPositivePart_summable h) lambda t
  have hn := summable_admissionPart_phase (admissionNegativePart h)
    (admissionNegativePart_nonneg h) (admissionNegativePart_summable h) lambda t
  rw [admissionFourierHistory, ← hp.tsum_sub hn]
  apply tsum_congr
  intro n
  rw [← sub_mul, ← Complex.ofReal_sub, admission_positive_sub_negative]

theorem charFun_countableWeightedDirac_eq_phase
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (lambda : ℕ → ℝ) (t : ℝ) :
    charFun (countableWeightedDirac a lambda) (-t) =
      ∑' n, (a n : ℂ) *
        Complex.exp ((((lambda n) * (-t) : ℝ) : ℂ) * Complex.I) := by
  rw [charFun_apply]
  have hint : Integrable
      (fun x : ℝ => Complex.exp (((inner ℝ x (-t) : ℝ) : ℂ) * Complex.I))
      (countableWeightedDirac a lambda) := by
    apply integrable_complex_countableWeightedDirac ha
    simpa [Complex.norm_exp] using hsum
  rw [integral_complex_countableWeightedDirac ha hint]
  apply tsum_congr
  intro n
  congr 2
  simp
  ring

/-- Distinct frequencies make complete phase history coefficient-faithful. -/
theorem admissionFourierHistory_eq_zero_iff
    {lambda : ℕ → ℝ} (hlambda : Function.Injective lambda) (h : AdmissionL1) :
    (∀ t : ℝ, admissionFourierHistory lambda h t = 0) ↔ h = 0 := by
  constructor
  · intro hzero
    let hp := admissionPositivePart h
    let hn := admissionNegativePart h
    let mup := countableWeightedDirac hp lambda
    let mun := countableWeightedDirac hn lambda
    letI : IsFiniteMeasure mup := by
      refine ⟨?_⟩
      rw [countableWeightedDirac_univ_ofReal
        (admissionPositivePart_nonneg h) (admissionPositivePart_summable h)]
      exact ENNReal.ofReal_lt_top
    letI : IsFiniteMeasure mun := by
      refine ⟨?_⟩
      rw [countableWeightedDirac_univ_ofReal
        (admissionNegativePart_nonneg h) (admissionNegativePart_summable h)]
      exact ENNReal.ofReal_lt_top
    have hmeasure : mup = mun := by
      apply Measure.ext_of_charFun
      funext t
      rw [show t = -(-t) by ring]
      rw [charFun_countableWeightedDirac_eq_phase hp
          (admissionPositivePart_nonneg h) (admissionPositivePart_summable h) lambda (-t),
        charFun_countableWeightedDirac_eq_phase hn
          (admissionNegativePart_nonneg h) (admissionNegativePart_summable h) lambda (-t)]
      have hdecomp := admissionFourierHistory_positive_sub_negative lambda h (-t)
      rw [hzero (-t)] at hdecomp
      exact sub_eq_zero.mp hdecomp.symm
    apply lp.ext
    funext n
    have hatom := congrArg (fun mu : Measure ℝ => mu.real {lambda n}) hmeasure
    dsimp only [mup, mun, hp, hn] at hatom
    rw [countableWeightedDirac_real_singleton (admissionPositivePart h) hlambda
        (admissionPositivePart_nonneg h) n,
      countableWeightedDirac_real_singleton (admissionNegativePart h) hlambda
        (admissionNegativePart_nonneg h) n] at hatom
    have hdecomp := admission_positive_sub_negative h n
    rw [hatom, sub_self] at hdecomp
    simpa using hdecomp.symm
  · rintro rfl t
    simp [admissionFourierHistory]

theorem admissionFourierHistory_zero_coefficients
    {lambda : ℕ → ℝ} (hlambda : Function.Injective lambda) {h : AdmissionL1}
    (hzero : ∀ t : ℝ, admissionFourierHistory lambda h t = 0) :
    ∀ n, h n = 0 := by
  have hh : h = 0 := (admissionFourierHistory_eq_zero_iff hlambda h).1 hzero
  simp [hh]

end

end GaloisForLFunctions.HTGeometry
