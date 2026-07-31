import GaloisForLFunctions.RHTower.HypertranscendentalQuartetWardIndex

/-!
# Finite hypertranscendental divisor packets and Ward quantization

Every finite packet of centered FE--Schwarz quartets may be inserted into
completed Xi by one nonzero polynomial gauge.  The surgery preserves
hypertranscendence, entire regularity, the functional equation, Schwarz
symmetry, and positivity of the gauge on the real axis.  Its Ward mass is
exactly `8π` times packet cardinality.
-/

open Complex MeasureTheory Real
open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Polynomial gauge for an arbitrary finite family of centered quartets. -/
def finiteQuartetPolynomial {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) : Polynomial ℂ :=
  ∏ i, centeredQuartetPolynomial (a i) (b i)

/-- Pointwise finite quartet gauge. -/
def finiteQuartetGauge {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (s : ℂ) : ℂ :=
  ∏ i, centeredQuartetGauge (a i) (b i) s

/-- Completed Xi after insertion of a finite family of quartets. -/
def finiteQuartetGaugedXi {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (s : ℂ) : ℂ :=
  finiteQuartetGauge a b s * xi s

theorem finiteQuartetPolynomial_eval {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (s : ℂ) :
    Polynomial.eval s (finiteQuartetPolynomial a b) =
      finiteQuartetGauge a b s := by
  classical
  simp only [finiteQuartetPolynomial, finiteQuartetGauge,
    Polynomial.eval_prod, centeredQuartetPolynomial_eval]

theorem finiteQuartetPolynomial_ne_zero {ι : Type*} [Fintype ι]
    {a b : ι → ℝ} (hb : ∀ i, 0 < b i) :
    finiteQuartetPolynomial a b ≠ 0 := by
  classical
  unfold finiteQuartetPolynomial
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    centeredQuartetPolynomial_ne_zero (hb i)

/-- Every finite centered-quartet surgery preserves completed-Xi
hypertranscendence. -/
theorem finiteQuartetGaugedXi_hypertranscendental
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hb : ∀ i, 0 < b i) :
    Hypertranscendental (finiteQuartetGaugedXi a b) := by
  have hxiSmooth : ContDiff ℂ (⊤ : ℕ∞) xi :=
    xi_analyticOnNhd_univ.contDiff
  have hfun :
      finiteQuartetGaugedXi a b =
        fun s : ℂ =>
          Polynomial.eval s (finiteQuartetPolynomial a b) * xi s := by
    funext s
    rw [finiteQuartetGaugedXi, finiteQuartetPolynomial_eval]
  rw [hfun]
  exact
    hypertranscendental_mul_polynomial hxiSmooth
      (finiteQuartetPolynomial_ne_zero hb) xi_hypertranscendental

theorem finiteQuartetGauge_one_sub
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (s : ℂ) :
    finiteQuartetGauge a b (1 - s) =
      finiteQuartetGauge a b s := by
  classical
  unfold finiteQuartetGauge
  apply Finset.prod_congr rfl
  intro i _
  exact centeredQuartetGauge_one_sub (a i) (b i) s

theorem finiteQuartetGauge_conj
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (s : ℂ) :
    finiteQuartetGauge a b ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (finiteQuartetGauge a b s) := by
  classical
  unfold finiteQuartetGauge
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact centeredQuartetGauge_conj (a i) (b i) s

theorem finiteQuartetGauge_real_pos
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hb : ∀ i, 0 < b i) (σ : ℝ) :
    0 < (finiteQuartetGauge a b (σ : ℂ)).re := by
  classical
  unfold finiteQuartetGauge
  simp_rw [centeredQuartetGauge_ofReal]
  rw [← ofReal_prod, ofReal_re]
  apply Finset.prod_pos
  intro i _
  exact mul_pos
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hb i)))
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hb i)))

/-- Total endpoint source weight of a finite quartet packet. -/
def finiteQuartetEndpointSourceWeight
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  ∑ i, quartetEndpointSourceWeight (a i) (b i)

theorem finiteQuartetEndpointSourceWeight_nonneg
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1 / 2)
    (hb : ∀ i, 0 < b i) :
    0 ≤ finiteQuartetEndpointSourceWeight a b := by
  classical
  unfold finiteQuartetEndpointSourceWeight
  exact Finset.sum_nonneg fun i _ =>
    (quartetEndpointSourceWeight_pos (ha0 i) (ha1 i) (hb i)).le

theorem finiteQuartetEndpointSourceWeight_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {a b : ι → ℝ}
    (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1 / 2)
    (hb : ∀ i, 0 < b i) :
    0 < finiteQuartetEndpointSourceWeight a b := by
  classical
  unfold finiteQuartetEndpointSourceWeight
  exact Finset.sum_pos (fun i _ =>
    quartetEndpointSourceWeight_pos (ha0 i) (ha1 i) (hb i))
    Finset.univ_nonempty

/-- **Finite source conservation law.**  Logarithmic source responses add:
the endpoint response of the product gauge is exactly minus twice the total
packet weight. -/
theorem finiteQuartetGauge_logDeriv_zero_eq_neg_two_weight
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hb : ∀ i, 0 < b i) :
    logDeriv (finiteQuartetGauge a b) 0 =
      (((-2) * finiteQuartetEndpointSourceWeight a b : ℝ) : ℂ) := by
  classical
  have hne : ∀ i ∈ Finset.univ,
      centeredQuartetGauge (a i) (b i) 0 ≠ 0 := by
    intro i _ hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (ne_of_gt
      (centeredQuartetGauge_real_pos (a := a i) (σ := 0) (hb i))) hre
  have hdiff : ∀ i ∈ Finset.univ,
      DifferentiableAt ℂ (centeredQuartetGauge (a i) (b i)) 0 := by
    intro i _
    unfold centeredQuartetGauge
    fun_prop
  have hprod := logDeriv_prod (x := (0 : ℂ))
    (f := fun i => centeredQuartetGauge (a i) (b i)) hne hdiff
  change logDeriv
      (fun s : ℂ => ∏ i, centeredQuartetGauge (a i) (b i) s) 0 = _
  rw [hprod]
  simp_rw [centeredQuartetGauge_logDeriv_zero_eq_neg_two_weight]
  unfold finiteQuartetEndpointSourceWeight
  push_cast
  rw [Finset.mul_sum]

/-- Source-weighted mass of a finite packet of universal `8π` Ward quanta. -/
def finiteQuartetSourceWeightedWardMass
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) : ℝ :=
  ∑ i, quartetSourceWeightedWardMass (a i) (b i)

theorem finiteQuartetSourceWeightedWardMass_eq_eightPi_weight
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    finiteQuartetSourceWeightedWardMass a b =
      (8 * π) * finiteQuartetEndpointSourceWeight a b := by
  classical
  unfold finiteQuartetSourceWeightedWardMass
  unfold quartetSourceWeightedWardMass finiteQuartetEndpointSourceWeight
  rw [Finset.mul_sum]

/-- **Finite source/Ward conservation.**  The total source-weighted Ward
mass of any finite quartet surgery is exactly the logarithmic response of
the complete polynomial gauge. -/
theorem finiteQuartetSourceWeightedWardMass_eq_logDeriv
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hb : ∀ i, 0 < b i) :
    finiteQuartetSourceWeightedWardMass a b =
      -4 * π * (logDeriv (finiteQuartetGauge a b) 0).re := by
  rw [finiteQuartetGauge_logDeriv_zero_eq_neg_two_weight hb]
  simp only [ofReal_re]
  rw [finiteQuartetSourceWeightedWardMass_eq_eightPi_weight]
  ring

theorem finiteQuartetGaugedXi_analyticAt
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (s : ℂ) :
    AnalyticAt ℂ (finiteQuartetGaugedXi a b) s := by
  change AnalyticAt ℂ
    (fun z => finiteQuartetGauge a b z * xi z) s
  apply AnalyticAt.mul
  · have hfun : finiteQuartetGauge a b =
        fun z => Polynomial.eval z (finiteQuartetPolynomial a b) := by
      funext z
      exact (finiteQuartetPolynomial_eval a b z).symm
    rw [hfun]
    exact (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ)
      (finiteQuartetPolynomial a b)) s (Set.mem_univ s)
  · exact xi_analyticOnNhd_univ s (Set.mem_univ s)

theorem finiteQuartetGaugedXi_one_sub
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (s : ℂ) :
    finiteQuartetGaugedXi a b (1 - s) =
      finiteQuartetGaugedXi a b s := by
  rw [finiteQuartetGaugedXi, finiteQuartetGaugedXi,
    finiteQuartetGauge_one_sub, xi_one_sub]

theorem finiteQuartetGaugedXi_conj
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (s : ℂ) :
    finiteQuartetGaugedXi a b ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (finiteQuartetGaugedXi a b s) := by
  rw [finiteQuartetGaugedXi, finiteQuartetGaugedXi,
    finiteQuartetGauge_conj, xi_conj, map_mul]

theorem finiteQuartetGaugedXi_quartetPoint
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) (i : ι) :
    finiteQuartetGaugedXi a b (quartetPoint (a i) (b i)) = 0 := by
  classical
  rw [finiteQuartetGaugedXi]
  have hgauge : finiteQuartetGauge a b (quartetPoint (a i) (b i)) = 0 := by
    unfold finiteQuartetGauge
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact centeredQuartetGauge_quartetPoint (a i) (b i)
  rw [hgauge, zero_mul]

theorem finiteQuartetGaugedXi_real_anchor_ne_zero
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (hb : ∀ i, 0 < b i) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    finiteQuartetGaugedXi a b (σ : ℂ) ≠ 0 := by
  apply mul_ne_zero
  · intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (ne_of_gt (finiteQuartetGauge_real_pos hb σ)) hre
  · intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.zero_re] at hre
    exact (ne_of_gt (xi_pos_on_real_anchor hσ0 hσ1)) hre

/-- Total Ward mass of a finite quartet packet. -/
def finiteQuartetWardMass {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) : ENNReal :=
  ∑ i, ∫⁻ t : ℝ,
    ENNReal.ofReal (quartetWardInfinitesimalDensity (a i) (b i) t)

/-- **Finite-packet Ward index theorem.**  Ward mass counts centered
FE--Schwarz quartets with multiplicity in exact quanta of `8π`. -/
theorem finiteQuartetWardMass_eq_card_nsmul_eightPi
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 < a i + 1 / 2) :
    finiteQuartetWardMass a b =
      Fintype.card ι • ENNReal.ofReal (8 * π) := by
  classical
  unfold finiteQuartetWardMass
  simp_rw [lintegral_quartetWardInfinitesimalDensity (ha _)]
  simp

/-- **Finite hypertranscendental divisor/Ward law.**  Arbitrary finite
off-critical divisor packets remain invisible to differential algebra and
the elementary completed symmetries, while their exact Ward index is
`8π` times packet cardinality. -/
theorem hypertranscendental_finiteQuartetWardIndex_law
    {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha0 : ∀ i, 0 < a i) (ha1 : ∀ i, a i < 1 / 2)
    (hb : ∀ i, 0 < b i) :
    Hypertranscendental (finiteQuartetGaugedXi a b) ∧
    (∀ s, AnalyticAt ℂ (finiteQuartetGaugedXi a b) s) ∧
    (∀ s, finiteQuartetGaugedXi a b (1 - s) =
      finiteQuartetGaugedXi a b s) ∧
    (∀ s, finiteQuartetGaugedXi a b ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (finiteQuartetGaugedXi a b s)) ∧
    (∀ σ : ℝ, 0 < σ → σ < 1 →
      finiteQuartetGaugedXi a b (σ : ℂ) ≠ 0) ∧
    (∀ i, (quartetPoint (a i) (b i)).re ≠ 1 / 2 ∧
      (quartetPoint (a i) (b i)).re < 1 ∧
      finiteQuartetGaugedXi a b (quartetPoint (a i) (b i)) = 0) ∧
    finiteQuartetWardMass a b =
      Fintype.card ι • ENNReal.ofReal (8 * π) := by
  refine ⟨
    finiteQuartetGaugedXi_hypertranscendental hb,
    finiteQuartetGaugedXi_analyticAt a b,
    finiteQuartetGaugedXi_one_sub a b,
    finiteQuartetGaugedXi_conj a b,
    fun _ hσ0 hσ1 =>
      finiteQuartetGaugedXi_real_anchor_ne_zero hb hσ0 hσ1,
    fun i => ⟨quartetPoint_off_critical (ne_of_gt (ha0 i)),
      by
        simp only [quartetPoint, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, I_re, I_im, Complex.ofReal_im]
        norm_num
        linarith [ha1 i],
      finiteQuartetGaugedXi_quartetPoint a b i⟩,
    finiteQuartetWardMass_eq_card_nsmul_eightPi
      (fun i => by linarith [ha0 i])⟩

end RHTower
