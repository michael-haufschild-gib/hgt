import GaloisForLFunctions.HTGeometry.MultiplicativeThetaDivisor
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm
import GaloisForLFunctions.HTGeometry.TateThetaGauge

/-!
# Exact Tate-theta divisor with multiplicity
-/

open Complex Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A shifted theta factor is analytic on the punctured plane. -/
theorem analyticAt_multiplicativeTheta_rootShift
    (r : TateQuarterNome) (a : ℤ) {x : ℂ} (hx : x ≠ 0) :
    AnalyticAt ℂ
      (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ a * z)) x := by
  have hscale : (r.root : ℂ) ^ a ≠ 0 := zpow_ne_zero a r.root_complex_ne_zero
  have harg : (r.root : ℂ) ^ a * x ≠ 0 := mul_ne_zero hscale hx
  exact (analyticAt_multiplicativeTheta r.nome harg).comp_of_eq
    (analyticAt_const.mul analyticAt_id) rfl

/-- A shifted theta zero has multiplicity exactly one. -/
theorem analyticOrderAt_multiplicativeTheta_rootShift_eq_one
    (r : TateQuarterNome) (a : ℤ) {x : ℂ} (hx : x ≠ 0)
    (hzero : multiplicativeTheta r.nome ((r.root : ℂ) ^ a * x) = 0) :
    analyticOrderAt
      (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ a * z)) x = 1 := by
  have hscale : (r.root : ℂ) ^ a ≠ 0 := zpow_ne_zero a r.root_complex_ne_zero
  have harg : (r.root : ℂ) ^ a * x ≠ 0 := mul_ne_zero hscale hx
  have htheta := analyticAt_multiplicativeTheta r.nome harg
  have horder := analyticOrderAt_multiplicativeTheta_eq_one
    r.nome r.nome_ne_zero harg hzero
  have htheta' : AnalyticAt ℂ (multiplicativeTheta r.nome)
      ((r.root : ℂ) ^ a * x + 0) := by simpa using htheta
  have horder' : analyticOrderAt (multiplicativeTheta r.nome)
      ((r.root : ℂ) ^ a * x + 0) = 1 := by simpa using horder
  have h := analyticOrderAt_comp_affine (f := multiplicativeTheta r.nome)
    (μ := (r.root : ℂ) ^ a) (ν := 0) (z := x) hscale htheta' horder'
  simpa only [add_zero, Nat.cast_one] using h

/-- A nonvanishing shifted theta factor has order zero. -/
theorem analyticOrderAt_multiplicativeTheta_rootShift_eq_zero
    (r : TateQuarterNome) (a : ℤ) {x : ℂ} (hx : x ≠ 0)
    (hne : multiplicativeTheta r.nome ((r.root : ℂ) ^ a * x) ≠ 0) :
    analyticOrderAt
      (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ a * z)) x = 0 :=
  (analyticAt_multiplicativeTheta_rootShift r a hx).analyticOrderAt_eq_zero.mpr hne

/-- On the zero orbit, both numerator theta factors vanish. -/
theorem tateThetaZeroOrbit_iff_both_numerator_factors_zero
    (r : TateQuarterNome) (x : ℂ) :
    tateThetaZeroOrbit r x ↔
      multiplicativeTheta r.nome ((r.root : ℂ) ^ (-1 : ℤ) * x) = 0 ∧
      multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * x) = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    constructor
    · rw [multiplicativeTheta_rootShift_eq_zero_iff]
      exact ⟨k, by convert hk using 1 <;> ring⟩
    · rw [multiplicativeTheta_rootShift_eq_zero_iff]
      exact ⟨k + 1, by convert hk using 1 <;> ring⟩
  · rintro ⟨hminus, hthree⟩
    exact (tateThetaNumerator_eq_zero_iff r x).mp (mul_eq_zero.mpr (Or.inl hminus))

/-- On the pole orbit, the denominator theta factor vanishes. -/
theorem tateThetaPoleOrbit_iff_denominator_factor_zero
    (r : TateQuarterNome) (x : ℂ) :
    tateThetaPoleOrbit r x ↔
      multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * x) = 0 := by
  exact (tateThetaDenominator_eq_zero_iff r x).symm

/-- Numerator of the Tate-theta gauge as an analytic function on `ℂˣ`. -/
def tateThetaGaugeNumerator (r : TateQuarterNome) (x : ℂ) : ℂ :=
  -(r.root : ℂ) *
    multiplicativeTheta r.nome ((r.root : ℂ) ^ (-1 : ℤ) * x) *
    multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * x)

/-- Denominator of the Tate-theta gauge. -/
def tateThetaGaugeDenominator (r : TateQuarterNome) (x : ℂ) : ℂ :=
  multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * x) ^ 2

theorem tateThetaGauge_eq_numerator_div_denominator (r : TateQuarterNome) :
    tateThetaGauge r = tateThetaGaugeNumerator r / tateThetaGaugeDenominator r := by
  funext x
  rfl

theorem analyticAt_tateThetaGaugeNumerator
    (r : TateQuarterNome) {x : ℂ} (hx : x ≠ 0) :
    AnalyticAt ℂ (tateThetaGaugeNumerator r) x := by
  exact (analyticAt_const.mul
    (analyticAt_multiplicativeTheta_rootShift r (-1) hx)).mul
      (analyticAt_multiplicativeTheta_rootShift r 3 hx)

theorem analyticAt_tateThetaGaugeDenominator
    (r : TateQuarterNome) {x : ℂ} (hx : x ≠ 0) :
    AnalyticAt ℂ (tateThetaGaugeDenominator r) x :=
  (analyticAt_multiplicativeTheta_rootShift r 1 hx).pow 2

/-- The numerator has exact order two on the zero orbit. -/
theorem analyticOrderAt_tateThetaGaugeNumerator_zeroOrbit
    (r : TateQuarterNome) {x : ℂ} (hx : tateThetaZeroOrbit r x) :
    analyticOrderAt (tateThetaGaugeNumerator r) x = 2 := by
  obtain ⟨k, hk⟩ := hx
  have hx0 : x ≠ 0 := by
    rw [hk]
    exact zpow_ne_zero _ r.root_complex_ne_zero
  have hboth := (tateThetaZeroOrbit_iff_both_numerator_factors_zero r x).mp ⟨k, hk⟩
  have hminusAn := analyticAt_multiplicativeTheta_rootShift r (-1) hx0
  have hthreeAn := analyticAt_multiplicativeTheta_rootShift r 3 hx0
  have hminusOrder := analyticOrderAt_multiplicativeTheta_rootShift_eq_one
    r (-1) hx0 hboth.1
  have hthreeOrder := analyticOrderAt_multiplicativeTheta_rootShift_eq_one
    r 3 hx0 hboth.2
  have hconst : AnalyticAt ℂ (fun _ : ℂ => -(r.root : ℂ)) x := analyticAt_const
  change analyticOrderAt
      (((fun _ : ℂ => -(r.root : ℂ)) *
        (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (-1 : ℤ) * z))) *
        (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * z))) x = 2
  rw [analyticOrderAt_mul (hconst.mul hminusAn) hthreeAn,
    analyticOrderAt_mul hconst hminusAn,
    hconst.analyticOrderAt_eq_zero.mpr (neg_ne_zero.mpr r.root_complex_ne_zero),
    hminusOrder, hthreeOrder]
  norm_num

/-- The denominator has exact order two on the pole orbit. -/
theorem analyticOrderAt_tateThetaGaugeDenominator_poleOrbit
    (r : TateQuarterNome) {x : ℂ} (hx : tateThetaPoleOrbit r x) :
    analyticOrderAt (tateThetaGaugeDenominator r) x = 2 := by
  obtain ⟨k, hk⟩ := hx
  have hx0 : x ≠ 0 := by
    rw [hk]
    exact zpow_ne_zero _ r.root_complex_ne_zero
  have hzero := (tateThetaPoleOrbit_iff_denominator_factor_zero r x).mp ⟨k, hk⟩
  have han := analyticAt_multiplicativeTheta_rootShift r 1 hx0
  have hord := analyticOrderAt_multiplicativeTheta_rootShift_eq_one r 1 hx0 hzero
  unfold tateThetaGaugeDenominator
  have hfun : (fun z : ℂ =>
      multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * z) ^ 2) =
      (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * z)) *
      (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * z)) := by
    funext z
    simp only [Pi.mul_apply, pow_two]
  rw [hfun, analyticOrderAt_mul han han, hord]
  norm_num

/-- Away from the zero orbit, the numerator has order zero. -/
theorem analyticOrderAt_tateThetaGaugeNumerator_off_zeroOrbit
    (r : TateQuarterNome) {x : ℂ} (hx0 : x ≠ 0) (hoff : ¬tateThetaZeroOrbit r x) :
    analyticOrderAt (tateThetaGaugeNumerator r) x = 0 := by
  have hprodNe :
      multiplicativeTheta r.nome ((r.root : ℂ) ^ (-1 : ℤ) * x) *
        multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * x) ≠ 0 := by
    intro hzero
    exact hoff ((tateThetaNumerator_eq_zero_iff r x).mp hzero)
  obtain ⟨hminusNe, hthreeNe⟩ := mul_ne_zero_iff.mp hprodNe
  have hminusAn := analyticAt_multiplicativeTheta_rootShift r (-1) hx0
  have hthreeAn := analyticAt_multiplicativeTheta_rootShift r 3 hx0
  have hminusOrder := analyticOrderAt_multiplicativeTheta_rootShift_eq_zero
    r (-1) hx0 hminusNe
  have hthreeOrder := analyticOrderAt_multiplicativeTheta_rootShift_eq_zero
    r 3 hx0 hthreeNe
  have hconst : AnalyticAt ℂ (fun _ : ℂ => -(r.root : ℂ)) x := analyticAt_const
  change analyticOrderAt
      (((fun _ : ℂ => -(r.root : ℂ)) *
        (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (-1 : ℤ) * z))) *
        (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * z))) x = 0
  rw [analyticOrderAt_mul (hconst.mul hminusAn) hthreeAn,
    analyticOrderAt_mul hconst hminusAn,
    hconst.analyticOrderAt_eq_zero.mpr (neg_ne_zero.mpr r.root_complex_ne_zero),
    hminusOrder, hthreeOrder]
  norm_num

/-- Away from the pole orbit, the denominator has order zero. -/
theorem analyticOrderAt_tateThetaGaugeDenominator_off_poleOrbit
    (r : TateQuarterNome) {x : ℂ} (hx0 : x ≠ 0) (hoff : ¬tateThetaPoleOrbit r x) :
    analyticOrderAt (tateThetaGaugeDenominator r) x = 0 := by
  have hne : multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * x) ≠ 0 := by
    intro hzero
    exact hoff ((tateThetaDenominator_eq_zero_iff r x).mp hzero)
  have han := analyticAt_multiplicativeTheta_rootShift r 1 hx0
  have hord := analyticOrderAt_multiplicativeTheta_rootShift_eq_zero r 1 hx0 hne
  unfold tateThetaGaugeDenominator
  have hfun : (fun z : ℂ =>
      multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * z) ^ 2) =
      (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * z)) *
      (fun z : ℂ => multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * z)) := by
    funext z
    simp only [Pi.mul_apply, pow_two]
  rw [hfun, analyticOrderAt_mul han han, hord]
  norm_num

/-- Exact order `+2` on every representative of the zero orbit. -/
theorem meromorphicOrderAt_tateThetaGauge_zeroOrbit
    (r : TateQuarterNome) {x : ℂ} (hx : tateThetaZeroOrbit r x) :
    meromorphicOrderAt (tateThetaGauge r) x = ((2 : ℤ) : WithTop ℤ) := by
  obtain ⟨k, hk⟩ := hx
  have hx0 : x ≠ 0 := by
    rw [hk]
    exact zpow_ne_zero _ r.root_complex_ne_zero
  have hzero : tateThetaZeroOrbit r x := ⟨k, hk⟩
  have hpole : ¬tateThetaPoleOrbit r x := fun hpole =>
    tateThetaZeroOrbit_disjoint_poleOrbit r x ⟨hzero, hpole⟩
  have hnumAn := analyticAt_tateThetaGaugeNumerator r hx0
  have hdenAn := analyticAt_tateThetaGaugeDenominator r hx0
  rw [tateThetaGauge_eq_numerator_div_denominator,
    meromorphicOrderAt_div hnumAn.meromorphicAt hdenAn.meromorphicAt,
    hnumAn.meromorphicOrderAt_eq,
    analyticOrderAt_tateThetaGaugeNumerator_zeroOrbit r hzero,
    hdenAn.meromorphicOrderAt_eq,
    analyticOrderAt_tateThetaGaugeDenominator_off_poleOrbit r hx0 hpole]
  norm_num

/-- Exact order `-2` on every representative of the pole orbit. -/
theorem meromorphicOrderAt_tateThetaGauge_poleOrbit
    (r : TateQuarterNome) {x : ℂ} (hx : tateThetaPoleOrbit r x) :
    meromorphicOrderAt (tateThetaGauge r) x = ((-2 : ℤ) : WithTop ℤ) := by
  obtain ⟨k, hk⟩ := hx
  have hx0 : x ≠ 0 := by
    rw [hk]
    exact zpow_ne_zero _ r.root_complex_ne_zero
  have hpole : tateThetaPoleOrbit r x := ⟨k, hk⟩
  have hzero : ¬tateThetaZeroOrbit r x := fun hzero =>
    tateThetaZeroOrbit_disjoint_poleOrbit r x ⟨hzero, hpole⟩
  have hnumAn := analyticAt_tateThetaGaugeNumerator r hx0
  have hdenAn := analyticAt_tateThetaGaugeDenominator r hx0
  rw [tateThetaGauge_eq_numerator_div_denominator,
    meromorphicOrderAt_div hnumAn.meromorphicAt hdenAn.meromorphicAt,
    hnumAn.meromorphicOrderAt_eq,
    analyticOrderAt_tateThetaGaugeNumerator_off_zeroOrbit r hx0 hzero,
    hdenAn.meromorphicOrderAt_eq,
    analyticOrderAt_tateThetaGaugeDenominator_poleOrbit r hpole]
  norm_num

/-- The Tate-theta gauge is a unit away from its two divisor orbits. -/
theorem meromorphicOrderAt_tateThetaGauge_off_orbits
    (r : TateQuarterNome) {x : ℂ} (hx0 : x ≠ 0)
    (hzero : ¬tateThetaZeroOrbit r x) (hpole : ¬tateThetaPoleOrbit r x) :
    meromorphicOrderAt (tateThetaGauge r) x = 0 := by
  have hnumAn := analyticAt_tateThetaGaugeNumerator r hx0
  have hdenAn := analyticAt_tateThetaGaugeDenominator r hx0
  rw [tateThetaGauge_eq_numerator_div_denominator,
    meromorphicOrderAt_div hnumAn.meromorphicAt hdenAn.meromorphicAt,
    hnumAn.meromorphicOrderAt_eq,
    analyticOrderAt_tateThetaGaugeNumerator_off_zeroOrbit r hx0 hzero,
    hdenAn.meromorphicOrderAt_eq,
    analyticOrderAt_tateThetaGaugeDenominator_off_poleOrbit r hx0 hpole]
  norm_num

/-- Divisor multiplicity on `ℂˣ`, representing `2[r]-2[r³]` on `ℂˣ/q^ℤ`. -/
def tateThetaDivisorMultiplicity (r : TateQuarterNome) (x : ℂ) : WithTop ℤ :=
  by
    classical
    exact if tateThetaZeroOrbit r x then 2 else if tateThetaPoleOrbit r x then -2 else 0

/-- **Exact divisor.** Unconditionally, at every point of `ℂˣ`, the meromorphic order of the
Tate-theta gauge is `2` on `[r]`, `-2` on `[r³]`, and zero elsewhere. -/
theorem meromorphicOrderAt_tateThetaGauge_exact
    (r : TateQuarterNome) (x : {z : ℂ // z ≠ 0}) :
    meromorphicOrderAt (tateThetaGauge r) x = tateThetaDivisorMultiplicity r x := by
  classical
  rw [tateThetaDivisorMultiplicity]
  by_cases hzero : tateThetaZeroOrbit r x
  · rw [if_pos hzero]
    exact meromorphicOrderAt_tateThetaGauge_zeroOrbit r hzero
  · rw [if_neg hzero]
    by_cases hpole : tateThetaPoleOrbit r x
    · rw [if_pos hpole]
      exact meromorphicOrderAt_tateThetaGauge_poleOrbit r hpole
    · rw [if_neg hpole]
      exact meromorphicOrderAt_tateThetaGauge_off_orbits r x.property hzero hpole

end

end GaloisForLFunctions.HTGeometry
