import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionDensityRatio
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMoments
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceRigidity

/-!
# Complete infinite paired-eta half-tilt and literal finite restrictions

The actual logarithmic measure retains every interval of the paired-eta source.
Its two independent half-tilts are normalized by the square of the literal mass.
Raw and probability difference densities identify the corresponding measure maps;
every moment is genuinely integrable and remains tied to its raw double integral.

The positive half-line gives the exact reference density `exp (-|x|/2)`. Finite
sources are literal restrictions of the complete measure. Removing source
coordinates gives a full product-loss bound, including pairs with both coordinates
removed. Fixed-order limits follow from domination; no order or clock limit is
interchanged. Complex moment-generating functions are identified only in their
integrability strip, with no source-zero, functional-equation or RH premise.
-/

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ENNReal ComplexConjugate
namespace RHTower
noncomputable section

def liClockPairedEtaInfinitePartitionNormalizer : ℝ :=
  ∫u:ℝ, Real.exp (-u/2) ∂pairedEtaLogMeasure

def liClockPairedEtaHalfLineLogMeasure : Measure ℝ := volume.restrict (Ioi 0)
instance liClockPairedEtaHalfLineLogMeasure.instSFinite : SFinite liClockPairedEtaHalfLineLogMeasure := by
  unfold liClockPairedEtaHalfLineLogMeasure
  infer_instance
instance pairedEtaLogMeasure.instSFinite : SFinite pairedEtaLogMeasure := by
  unfold pairedEtaLogMeasure
  infer_instance

def liClockPairedEtaHalfLinePartitionNormalizer : ℝ :=
  ∫u:ℝ, Real.exp (-u/2) ∂liClockPairedEtaHalfLineLogMeasure

def liClockPairedEtaInfinitePartitionHalfTiltWeight (u:ℝ) : ℝ :=
  pairedEtaLogSupport.indicator (fun v:ℝ=>Real.exp (-v/2)) u

def liClockPairedEtaHalfLineHalfTiltWeight (u:ℝ) : ℝ :=
  (Ioi 0).indicator (fun v:ℝ=>Real.exp (-v/2)) u

def liClockPairedEtaInfiniteSymmetrizedMeasure : Measure (ℝ×ℝ) :=
  (pairedEtaLogMeasure.prod pairedEtaLogMeasure).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2)

def liClockPairedEtaHalfLineSymmetrizedMeasure : Measure (ℝ×ℝ) :=
  (liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure).tilted
    (fun p:ℝ×ℝ=>-(p.1+p.2)/2)

def liClockPairedEtaInfiniteSymmetrizedEvenMoment (j:ℕ) : ℝ :=
  ∫p:ℝ×ℝ,(p.1-p.2)^(2*j) ∂liClockPairedEtaInfiniteSymmetrizedMeasure

def liClockPairedEtaHalfLineSymmetrizedEvenMoment (j:ℕ) : ℝ :=
  ∫p:ℝ×ℝ,(p.1-p.2)^(2*j) ∂liClockPairedEtaHalfLineSymmetrizedMeasure

def liClockPairedEtaInfinitePartitionRawDifferenceDensity (x:ℝ) : ℝ :=
  ∫v:ℝ,liClockPairedEtaInfinitePartitionHalfTiltWeight (v+x)*liClockPairedEtaInfinitePartitionHalfTiltWeight v

def liClockPairedEtaHalfLineRawDifferenceDensity (x:ℝ) : ℝ :=
  ∫v:ℝ,liClockPairedEtaHalfLineHalfTiltWeight (v+x)*liClockPairedEtaHalfLineHalfTiltWeight v

def liClockPairedEtaInfinitePartitionDifferenceDensity (x:ℝ) : ℝ :=
  liClockPairedEtaInfinitePartitionRawDifferenceDensity x/liClockPairedEtaInfinitePartitionNormalizer^2

def liClockPairedEtaHalfLineDifferenceDensity (x:ℝ) : ℝ :=
  liClockPairedEtaHalfLineRawDifferenceDensity x/liClockPairedEtaHalfLinePartitionNormalizer^2

def liClockPairedEtaInfinitePartitionComparisonLimit : ℝ :=
  2*Real.log 2/liClockPairedEtaInfinitePartitionNormalizer^2

private lemma halfLine_rexp_integrable {a:ℝ} (ha:0<a) :
    Integrable (fun u:ℝ=>Real.exp (-a*u)) liClockPairedEtaHalfLineLogMeasure := by
  simpa only [IntegrableOn,liClockPairedEtaHalfLineLogMeasure,neg_mul] using integrableOn_exp_mul_Ioi (a:= -a) (by linarith) 0

theorem integrable_rexp_neg_mul_pairedEtaLogMeasure {a:ℝ} (ha:0<a) :
    Integrable (fun u:ℝ=>Real.exp (-a*u)) pairedEtaLogMeasure := by
  exact (halfLine_rexp_integrable ha).mono_measure pairedEtaLogMeasure_le_volume_restrict_Ioi_zero

private lemma infinite_half_integrable : Integrable (fun u:ℝ=>Real.exp (-u/2)) pairedEtaLogMeasure := by
  convert integrable_rexp_neg_mul_pairedEtaLogMeasure (a:=1/2) (by norm_num) using 1
  funext u; congr 1; ring

private lemma halfLine_half_integrable :
    Integrable (fun u:ℝ=>Real.exp (-u/2)) liClockPairedEtaHalfLineLogMeasure := by
  convert halfLine_rexp_integrable (a:=1/2) (by norm_num) using 1
  funext u; congr 1; ring

theorem liClockPairedEtaHalfLinePartitionNormalizer_eq_two :
    liClockPairedEtaHalfLinePartitionNormalizer=2 := by
  unfold liClockPairedEtaHalfLinePartitionNormalizer liClockPairedEtaHalfLineLogMeasure
  convert integral_exp_mul_Ioi (a:= -(1/2:ℝ)) (by norm_num) 0 using 1 <;> norm_num
  congr 1; funext u; congr 1; ring

private lemma joint_factor (p:ℝ×ℝ) :
    Real.exp (-(p.1+p.2)/2)=Real.exp (-p.1/2)*Real.exp (-p.2/2) := by
  rw [←Real.exp_add]; congr 1; ring

private lemma joint_integrable {ν:Measure ℝ} [SFinite ν]
    (h:Integrable (fun u:ℝ=>Real.exp (-u/2)) ν) :
    Integrable (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)) (ν.prod ν) := by
  convert h.mul_prod h using 1
  funext p; exact joint_factor p

private lemma joint_integral (ν:Measure ℝ) [SFinite ν] :
    (∫p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2) ∂ν.prod ν)=
      (∫u:ℝ,Real.exp (-u/2) ∂ν)^2 := by
  simp_rw [joint_factor]
  simpa only [pow_two] using integral_prod_mul (μ:=ν) (ν:=ν)
    (fun u:ℝ=>Real.exp (-u/2)) (fun u:ℝ=>Real.exp (-u/2))

theorem liClockPairedEtaInfiniteJointWeight_integral :
    (∫p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2) ∂pairedEtaLogMeasure.prod pairedEtaLogMeasure)=
      liClockPairedEtaInfinitePartitionNormalizer^2 := joint_integral pairedEtaLogMeasure

theorem liClockPairedEtaHalfLineJointWeight_integral :
    (∫p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2)
      ∂liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure)=
      liClockPairedEtaHalfLinePartitionNormalizer^2 := joint_integral liClockPairedEtaHalfLineLogMeasure

private lemma firstMeasure_le : liClockPairedEtaContiguousLogMeasure (Real.log 2)≤pairedEtaLogMeasure := by
  exact Measure.restrict_mono_set volume Ioc_zero_log_two_subset_pairedEtaLogSupport

theorem liClockPairedEtaInfinitePartitionNormalizer_ge_firstInterval :
    liClockPairedEtaContiguousPartitionNormalizer (Real.log 2)≤liClockPairedEtaInfinitePartitionNormalizer := by
  exact integral_mono_measure firstMeasure_le (Eventually.of_forall fun u=>(Real.exp_pos (-u/2)).le) infinite_half_integrable

theorem liClockPairedEtaInfinitePartitionNormalizer_pos : 0<liClockPairedEtaInfinitePartitionNormalizer :=
  (liClockPairedEtaContiguousPartitionNormalizer_pos (Real.log_pos (by norm_num))).trans_le
    liClockPairedEtaInfinitePartitionNormalizer_ge_firstInterval

private lemma tilted_probability {ν:Measure ℝ} [SFinite ν]
    (h:Integrable (fun u:ℝ=>Real.exp (-u/2)) ν)
    (hp:0<(∫u:ℝ,Real.exp (-u/2) ∂ν)) :
    IsProbabilityMeasure ((ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2)) := by
  have hn:NeZero (ν.prod ν) := by
    constructor
    intro hz
    have hpos:0<(∫p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2) ∂ν.prod ν) := by
      rw [joint_integral]; exact sq_pos_of_pos hp
    rw [hz,integral_zero_measure] at hpos
    exact (lt_irrefl _ hpos)
  exact isProbabilityMeasure_tilted (joint_integrable h)

theorem liClockPairedEtaInfiniteSymmetrizedMeasure_isProbability :
    IsProbabilityMeasure liClockPairedEtaInfiniteSymmetrizedMeasure :=
  tilted_probability infinite_half_integrable liClockPairedEtaInfinitePartitionNormalizer_pos

theorem liClockPairedEtaHalfLineSymmetrizedMeasure_isProbability :
    IsProbabilityMeasure liClockPairedEtaHalfLineSymmetrizedMeasure :=
  tilted_probability halfLine_half_integrable (by change 0<liClockPairedEtaHalfLinePartitionNormalizer; rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two]; norm_num)

private lemma sym_exp_integrable {ν:Measure ℝ} [SFinite ν]
    (hν:ν≤liClockPairedEtaHalfLineLogMeasure) {v:ℝ} (hv:|v|<1/2) :
    Integrable (fun p:ℝ×ℝ=>Real.exp (v*(p.1-p.2)))
      ((ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2)) := by
  have hhalf:=halfLine_half_integrable.mono_measure hν
  rw [integrable_tilted_iff (joint_integrable hhalf)]
  have hp:= (halfLine_rexp_integrable (a:=1/2-v) (by linarith [(abs_lt.mp hv).2])).mono_measure hν
  have hm:= (halfLine_rexp_integrable (a:=1/2+v) (by linarith [(abs_lt.mp hv).1])).mono_measure hν
  convert hp.mul_prod hm using 1
  funext p
  simp only [smul_eq_mul]
  rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

private lemma sym_interior {ν:Measure ℝ} [SFinite ν]
    (hν:ν≤liClockPairedEtaHalfLineLogMeasure) {z:ℂ} (hz:|z.re|<1/2) :
    z.re∈interior (integrableExpSet (fun p:ℝ×ℝ=>p.1-p.2)
      ((ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2))) := by
  have hsub : Ioo (-(1/2:ℝ)) (1/2) ⊆ integrableExpSet (fun p:ℝ×ℝ=>p.1-p.2)
      ((ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2)) := by
    intro v hv
    exact sym_exp_integrable hν (abs_lt.mpr hv)
  exact (interior_maximal hsub isOpen_Ioo) (abs_lt.mp hz)

theorem integrable_liClockPairedEtaInfiniteSymmetrizedEvenMoment (j:ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) liClockPairedEtaInfiniteSymmetrizedMeasure := by
  have h:=integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (sym_interior (ν:=pairedEtaLogMeasure) pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
      (z:=0) (by norm_num)) (2*j)
  simpa only [liClockPairedEtaInfiniteSymmetrizedMeasure,liClockPairedEtaHalfLineSymmetrizedMeasure,Complex.zero_re,zero_mul,Real.exp_zero,mul_one] using h

theorem integrable_liClockPairedEtaHalfLineSymmetrizedEvenMoment (j:ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) liClockPairedEtaHalfLineSymmetrizedMeasure := by
  have h:=integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (sym_interior (ν:=liClockPairedEtaHalfLineLogMeasure) le_rfl (z:=0) (by norm_num)) (2*j)
  simpa only [liClockPairedEtaInfiniteSymmetrizedMeasure,liClockPairedEtaHalfLineSymmetrizedMeasure,Complex.zero_re,zero_mul,Real.exp_zero,mul_one] using h

private def halfWeight (S:Set ℝ) (u:ℝ) : ℝ := S.indicator (fun v:ℝ=>Real.exp (-v/2)) u

private lemma halfWeight_measurable {S:Set ℝ} (hS:MeasurableSet S) : Measurable (halfWeight S) :=
  (show Measurable (fun v:ℝ=>Real.exp (-v/2)) by fun_prop).indicator hS

private lemma halfWeight_nonneg (S:Set ℝ) (u:ℝ) : 0≤halfWeight S u := by
  by_cases hu:u∈S <;> simp [halfWeight,hu,(Real.exp_pos _).le]

private lemma halfWeight_le_one {S:Set ℝ} (hS:S⊆Ioi 0) (u:ℝ) : halfWeight S u≤1 := by
  by_cases hu:u∈S
  · simp only [halfWeight,indicator_of_mem hu]
    have hu0:0<u := hS hu
    exact Real.exp_le_one_iff.mpr (by linarith)
  · simp [halfWeight,hu]

private lemma halfWeight_mono {S T:Set ℝ} (hST:S⊆T) (u:ℝ) : halfWeight S u≤halfWeight T u := by
  by_cases hu:u∈S
  · simp [halfWeight,hu,hST hu]
  · simp only [halfWeight,indicator_of_notMem hu]
    exact halfWeight_nonneg T u

private lemma halfWeight_integrable {S:Set ℝ} (hS:MeasurableSet S) (hS0:S⊆Ioi 0) :
    Integrable (halfWeight S) := by
  unfold halfWeight
  rw [integrable_indicator_iff hS]
  exact halfLine_half_integrable.mono_measure (Measure.restrict_mono_set volume hS0)

private lemma halfWeight_prod_integrable {S:Set ℝ} (hS:MeasurableSet S) (hS0:S⊆Ioi 0) (x:ℝ) :
    Integrable (fun v:ℝ=>halfWeight S (v+x)*halfWeight S v) := by
  apply (halfWeight_integrable hS hS0).mono' (by
    exact ((halfWeight_measurable hS).comp (measurable_id.add_const x)).mul (halfWeight_measurable hS) |>.aestronglyMeasurable)
  filter_upwards [] with v
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (halfWeight_nonneg S _) (halfWeight_nonneg S _))]
  exact mul_le_of_le_one_left (halfWeight_nonneg S _) (halfWeight_le_one hS0 _)

private lemma halfWeight_raw_measurable {S:Set ℝ} (hS:MeasurableSet S) :
    Measurable (fun x:ℝ=>∫v:ℝ,halfWeight S (v+x)*halfWeight S v) := by
  have hm : Measurable (fun p:ℝ×ℝ=>halfWeight S (p.2+p.1)*halfWeight S p.2) :=
    ((halfWeight_measurable hS).comp (measurable_snd.add measurable_fst)).mul
      ((halfWeight_measurable hS).comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_liClockPairedEtaInfinitePartitionHalfTiltWeight :
    Measurable liClockPairedEtaInfinitePartitionHalfTiltWeight :=
  halfWeight_measurable measurableSet_pairedEtaLogSupport

theorem measurable_liClockPairedEtaHalfLineHalfTiltWeight :
    Measurable liClockPairedEtaHalfLineHalfTiltWeight := halfWeight_measurable measurableSet_Ioi

theorem integrable_liClockPairedEtaInfinitePartitionHalfTiltWeight :
    Integrable liClockPairedEtaInfinitePartitionHalfTiltWeight :=
  halfWeight_integrable measurableSet_pairedEtaLogSupport pairedEtaLogSupport_subset_Ioi_zero

theorem integrable_liClockPairedEtaHalfLineHalfTiltWeight :
    Integrable liClockPairedEtaHalfLineHalfTiltWeight := halfWeight_integrable measurableSet_Ioi le_rfl

theorem liClockPairedEtaInfinitePartitionHalfTiltWeight_nonneg (u:ℝ) :
    0≤liClockPairedEtaInfinitePartitionHalfTiltWeight u := halfWeight_nonneg _ _

theorem liClockPairedEtaHalfLineHalfTiltWeight_nonneg (u:ℝ) :
    0≤liClockPairedEtaHalfLineHalfTiltWeight u := halfWeight_nonneg _ _

theorem liClockPairedEtaInfinitePartitionHalfTiltWeight_le_halfLine (u:ℝ) :
    liClockPairedEtaInfinitePartitionHalfTiltWeight u≤liClockPairedEtaHalfLineHalfTiltWeight u :=
  halfWeight_mono pairedEtaLogSupport_subset_Ioi_zero u

theorem integrable_liClockPairedEtaInfinitePartitionTranslatedProduct (x:ℝ) :
    Integrable (fun v:ℝ=>liClockPairedEtaInfinitePartitionHalfTiltWeight (v+x)*liClockPairedEtaInfinitePartitionHalfTiltWeight v) :=
  halfWeight_prod_integrable measurableSet_pairedEtaLogSupport pairedEtaLogSupport_subset_Ioi_zero x

theorem integrable_liClockPairedEtaHalfLineTranslatedProduct (x:ℝ) :
    Integrable (fun v:ℝ=>liClockPairedEtaHalfLineHalfTiltWeight (v+x)*liClockPairedEtaHalfLineHalfTiltWeight v) :=
  halfWeight_prod_integrable measurableSet_Ioi le_rfl x

theorem measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity :
    Measurable liClockPairedEtaInfinitePartitionRawDifferenceDensity :=
  halfWeight_raw_measurable measurableSet_pairedEtaLogSupport

theorem measurable_liClockPairedEtaHalfLineRawDifferenceDensity :
    Measurable liClockPairedEtaHalfLineRawDifferenceDensity := halfWeight_raw_measurable measurableSet_Ioi

private lemma raw_even (f:ℝ→ℝ) (x:ℝ) :
    (∫v:ℝ,f (v-x)*f v)=∫v:ℝ,f (v+x)*f v := by
  calc
    _ = ∫v:ℝ,f v*f (v+x) := by
      have h:=integral_add_right_eq_self (μ:=volume) (fun v:ℝ=>f (v-x)*f v) x
      simpa only [add_sub_cancel_right] using h.symm
    _ = _ := by apply integral_congr_ae; filter_upwards [] with v; exact mul_comm _ _

theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_even (x:ℝ) :
    liClockPairedEtaInfinitePartitionRawDifferenceDensity (-x)=liClockPairedEtaInfinitePartitionRawDifferenceDensity x := by
  simpa only [liClockPairedEtaInfinitePartitionRawDifferenceDensity,sub_eq_add_neg] using
    raw_even liClockPairedEtaInfinitePartitionHalfTiltWeight x

theorem liClockPairedEtaHalfLineRawDifferenceDensity_even (x:ℝ) :
    liClockPairedEtaHalfLineRawDifferenceDensity (-x)=liClockPairedEtaHalfLineRawDifferenceDensity x := by
  simpa only [liClockPairedEtaHalfLineRawDifferenceDensity,sub_eq_add_neg] using
    raw_even liClockPairedEtaHalfLineHalfTiltWeight x

theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg (x:ℝ) :
    0≤liClockPairedEtaInfinitePartitionRawDifferenceDensity x :=
  integral_nonneg (fun v=>mul_nonneg (liClockPairedEtaInfinitePartitionHalfTiltWeight_nonneg (v+x))
    (liClockPairedEtaInfinitePartitionHalfTiltWeight_nonneg v))

theorem liClockPairedEtaHalfLineRawDifferenceDensity_nonneg (x:ℝ) :
    0≤liClockPairedEtaHalfLineRawDifferenceDensity x :=
  integral_nonneg (fun v=>mul_nonneg (liClockPairedEtaHalfLineHalfTiltWeight_nonneg (v+x))
    (liClockPairedEtaHalfLineHalfTiltWeight_nonneg v))

theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_le_halfLine (x:ℝ) :
    liClockPairedEtaInfinitePartitionRawDifferenceDensity x≤liClockPairedEtaHalfLineRawDifferenceDensity x := by
  apply integral_mono (integrable_liClockPairedEtaInfinitePartitionTranslatedProduct x)
    (integrable_liClockPairedEtaHalfLineTranslatedProduct x)
  intro v
  exact mul_le_mul (liClockPairedEtaInfinitePartitionHalfTiltWeight_le_halfLine _)
    (liClockPairedEtaInfinitePartitionHalfTiltWeight_le_halfLine _)
    (liClockPairedEtaInfinitePartitionHalfTiltWeight_nonneg _)
    (liClockPairedEtaHalfLineHalfTiltWeight_nonneg _)

private lemma halfLine_prod_eq {x:ℝ} (hx:0≤x) (v:ℝ) :
    liClockPairedEtaHalfLineHalfTiltWeight (v+x)*liClockPairedEtaHalfLineHalfTiltWeight v =
      (Ioi 0).indicator (fun v:ℝ=>Real.exp (-x/2)*Real.exp (-v)) v := by
  by_cases hv:v∈Ioi 0
  · have hv0:0<v := hv
    have hvx:v+x∈Ioi 0 := by change 0<v+x; linarith
    simp only [liClockPairedEtaHalfLineHalfTiltWeight,indicator_of_mem hv,indicator_of_mem hvx]
    rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
  · simp [liClockPairedEtaHalfLineHalfTiltWeight,hv]

private lemma halfLine_raw_nonneg_eq {x:ℝ} (hx:0≤x) :
    liClockPairedEtaHalfLineRawDifferenceDensity x=Real.exp (-x/2) := by
  simp_rw [liClockPairedEtaHalfLineRawDifferenceDensity,halfLine_prod_eq hx]
  rw [integral_indicator measurableSet_Ioi,integral_const_mul]
  have hi:(∫v:ℝ in Ioi 0,Real.exp (-v))=1 := by
    simpa using integral_exp_mul_Ioi (a:= -1) (by norm_num) 0
  rw [hi,mul_one]

theorem liClockPairedEtaHalfLineRawDifferenceDensity_eq (x:ℝ) :
    liClockPairedEtaHalfLineRawDifferenceDensity x=Real.exp (-|x|/2) := by
  by_cases hx:0≤x
  · rw [halfLine_raw_nonneg_eq hx,abs_of_nonneg hx]
  · have hn:0≤-x := by linarith
    rw [←liClockPairedEtaHalfLineRawDifferenceDensity_even x,halfLine_raw_nonneg_eq hn,abs_of_neg (lt_of_not_ge hx)]


private theorem map_sub_prod_density (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map (fun p : ℝ × ℝ => p.1-p.2)
      ((volume.withDensity f).prod (volume.withDensity g)) =
      volume.withDensity (fun x : ℝ => ∫⁻ v : ℝ, f (v+x)*g v) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ (by fun_prop),prod_withDensity hf hg,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hshift := (measurePreserving_add_prod (volume:Measure ℝ) volume).lintegral_comp
    (f:=fun p : ℝ×ℝ => (f p.1*g p.2)*φ (p.1-p.2)) (by fun_prop)
  have hm : Measurable (fun x : ℝ => ∫⁻ v : ℝ,f (v+x)*g v) :=
    (show Measurable (fun p : ℝ×ℝ=>f (p.2+p.1)*g p.2) by fun_prop).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hφ]
  simp only [Pi.mul_apply]
  rw [← hshift]
  simp only [add_sub_cancel_right]
  rw [lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [← lintegral_mul_const'' _ (by fun_prop)]
  apply lintegral_congr
  intro v
  rw [add_comm]


private theorem rawWeight_measure (S : Set ℝ) (hS : MeasurableSet S) :
    volume.withDensity (fun u=>ENNReal.ofReal (S.indicator (fun v:ℝ=>Real.exp (-v/2)) u)) =
      (volume.restrict S).withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2))) := by
  rw [← withDensity_indicator hS]
  congr 1
  funext u
  by_cases hu:u∈S <;> simp [hu]

private theorem rawProd_weight (ν : Measure ℝ) [SFinite ν] :
    (ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2)))).prod
      (ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2)))) =
      (ν.prod ν).withDensity (fun p:ℝ×ℝ=>ENNReal.ofReal (Real.exp (-(p.1+p.2)/2))) := by
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

private theorem tilted_eq_scaled_raw (ν : Measure ℝ) [SFinite ν] (Z : ℝ)
    (hZ : 0<Z)
    (hnorm : (∫p:ℝ×ℝ,Real.exp (-(p.1+p.2)/2) ∂ν.prod ν)=Z^2) :
    (ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2) =
      ENNReal.ofReal (1/Z^2) • ((ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2)))).prod
        (ν.withDensity (fun u=>ENNReal.ofReal (Real.exp (-u/2))))) := by
  rw [rawProd_weight,Measure.tilted,hnorm,← withDensity_smul _ (by fun_prop)]
  congr 1
  funext p
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring


private lemma raw_density_map {S:Set ℝ} (hS:MeasurableSet S) (hS0:S⊆Ioi 0) :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2)
      ((volume.withDensity (fun u=>ENNReal.ofReal (halfWeight S u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (halfWeight S u)))) =
      volume.withDensity (fun x=>ENNReal.ofReal (∫v:ℝ,halfWeight S (v+x)*halfWeight S v)) := by
  rw [map_sub_prod_density _ _ (halfWeight_measurable hS).ennreal_ofReal (halfWeight_measurable hS).ennreal_ofReal]
  congr 1
  funext x
  rw [ofReal_integral_eq_lintegral_ofReal (halfWeight_prod_integrable hS hS0 x)
    (Eventually.of_forall fun v=>mul_nonneg (halfWeight_nonneg S _) (halfWeight_nonneg S _))]
  apply lintegral_congr
  intro v
  exact (ENNReal.ofReal_mul (halfWeight_nonneg S _)).symm

theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_map :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2)
      ((volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaInfinitePartitionHalfTiltWeight u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaInfinitePartitionHalfTiltWeight u)))) =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaInfinitePartitionRawDifferenceDensity x)) :=
  raw_density_map measurableSet_pairedEtaLogSupport pairedEtaLogSupport_subset_Ioi_zero

theorem liClockPairedEtaHalfLineRawDifferenceDensity_map :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2)
      ((volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaHalfLineHalfTiltWeight u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (liClockPairedEtaHalfLineHalfTiltWeight u)))) =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaHalfLineRawDifferenceDensity x)) :=
  raw_density_map measurableSet_Ioi le_rfl

private lemma normalized_density_map {S:Set ℝ} (hS:MeasurableSet S) (hS0:S⊆Ioi 0)
    {Z:ℝ} (hZ:0<Z) (hnorm:(∫u:ℝ,Real.exp (-u/2) ∂volume.restrict S)=Z) :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2)
      (((volume.restrict S).prod (volume.restrict S)).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2)) =
      volume.withDensity (fun x=>ENNReal.ofReal ((∫v:ℝ,halfWeight S (v+x)*halfWeight S v)/Z^2)) := by
  rw [tilted_eq_scaled_raw _ Z hZ (by rw [joint_integral,hnorm]),←rawWeight_measure S hS]
  change Measure.map (fun p:ℝ×ℝ=>p.1-p.2)
    (ENNReal.ofReal (1/Z^2) •
      ((volume.withDensity (fun u=>ENNReal.ofReal (halfWeight S u))).prod
        (volume.withDensity (fun u=>ENNReal.ofReal (halfWeight S u))))) = _
  rw [Measure.map_smul,raw_density_map hS hS0,
    ←withDensity_smul _ (halfWeight_raw_measurable hS).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem liClockPairedEtaInfinitePartitionDifferenceDensity_map :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaInfiniteSymmetrizedMeasure =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaInfinitePartitionDifferenceDensity x)) :=
  normalized_density_map measurableSet_pairedEtaLogSupport pairedEtaLogSupport_subset_Ioi_zero
    liClockPairedEtaInfinitePartitionNormalizer_pos rfl

theorem liClockPairedEtaHalfLineDifferenceDensity_map :
    Measure.map (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaHalfLineSymmetrizedMeasure =
      volume.withDensity (fun x=>ENNReal.ofReal (liClockPairedEtaHalfLineDifferenceDensity x)) :=
  normalized_density_map measurableSet_Ioi le_rfl
    (by rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two]; norm_num) rfl

private lemma raw_moment_integrable {ν:Measure ℝ} [SFinite ν]
    (h:Integrable (fun u:ℝ=>Real.exp (-u/2)) ν) (j:ℕ)
    (hj:Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) ((ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2))) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)) (ν.prod ν) := by
  have hi:=(integrable_tilted_iff (joint_integrable h) _).mp hj
  simpa only [smul_eq_mul,mul_comm] using hi

theorem integrable_liClockPairedEtaInfiniteRawEvenMoment (j:ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))
      (pairedEtaLogMeasure.prod pairedEtaLogMeasure) :=
  raw_moment_integrable infinite_half_integrable j (integrable_liClockPairedEtaInfiniteSymmetrizedEvenMoment j)

theorem integrable_liClockPairedEtaHalfLineRawEvenMoment (j:ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))
      (liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure) :=
  raw_moment_integrable halfLine_half_integrable j (integrable_liClockPairedEtaHalfLineSymmetrizedEvenMoment j)

private lemma normalized_moment_eq (ν:Measure ℝ) [SFinite ν] (j:ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j) ∂(ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2)) =
      (∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2) ∂ν.prod ν)/
        (∫u:ℝ,Real.exp (-u/2) ∂ν)^2 := by
  rw [integral_tilted,joint_integral]
  simp only [smul_eq_mul]
  have heq:(fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)/(∫u:ℝ,Real.exp (-u/2) ∂ν)^2*(p.1-p.2)^(2*j))=
      (fun p:ℝ×ℝ=>((p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))/(∫u:ℝ,Real.exp (-u/2) ∂ν)^2) := by
    funext p; ring
  rw [heq,integral_div]

theorem liClockPairedEtaInfiniteSymmetrizedEvenMoment_eq_double_integral (j:ℕ) :
    liClockPairedEtaInfiniteSymmetrizedEvenMoment j =
      (∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2) ∂pairedEtaLogMeasure.prod pairedEtaLogMeasure)/
        liClockPairedEtaInfinitePartitionNormalizer^2 := normalized_moment_eq pairedEtaLogMeasure j

theorem liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq_double_integral (j:ℕ) :
    liClockPairedEtaHalfLineSymmetrizedEvenMoment j =
      (∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
        ∂liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure)/
        liClockPairedEtaHalfLinePartitionNormalizer^2 := normalized_moment_eq liClockPairedEtaHalfLineLogMeasure j

private lemma integrable_density_power (μ:Measure (ℝ×ℝ)) (g:ℝ→ℝ)
    (hg:Measurable g) (hgn:∀x,0≤g x)
    (hmap:Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ=volume.withDensity (fun x=>ENNReal.ofReal (g x))) (j:ℕ)
    (hj:Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) μ) :
    Integrable (fun x:ℝ=>x^(2*j)*g x) := by
  have hi:Integrable (fun x:ℝ=>x^(2*j)) (Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hj
  rw [hmap] at hi
  have hi':=(integrable_withDensity_iff_integrable_smul' hg.ennreal_ofReal
    (Eventually.of_forall fun x=>ENNReal.ofReal_lt_top)).mp hi
  simpa only [ENNReal.toReal_ofReal (hgn _),smul_eq_mul,mul_comm] using hi'

private lemma integral_density_power (μ:Measure (ℝ×ℝ)) (g:ℝ→ℝ)
    (hg:Measurable g) (hgn:∀x,0≤g x)
    (hmap:Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ=volume.withDensity (fun x=>ENNReal.ofReal (g x))) (j:ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j) ∂μ)=∫x:ℝ,x^(2*j)*g x := by
  rw [←integral_map (by fun_prop:AEMeasurable (fun p:ℝ×ℝ=>p.1-p.2) μ)
    (by fun_prop:AEStronglyMeasurable (fun x:ℝ=>x^(2*j)) (Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ)),hmap,
    integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (Eventually.of_forall fun x=>ENNReal.ofReal_lt_top) (fun x:ℝ=>x^(2*j))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hgn x),smul_eq_mul,mul_comm]


private lemma density_moment_eq {μ:Measure (ℝ×ℝ)} {g:ℝ→ℝ} {Z:ℝ}
    (hg:Measurable g) (hgn:∀x,0≤g x) (hZ:0<Z)
    (hmap:Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ=volume.withDensity (fun x=>ENNReal.ofReal (g x/Z^2))) (j:ℕ) :
    (∫x:ℝ,x^(2*j)*g x)=Z^2*(∫p:ℝ×ℝ,(p.1-p.2)^(2*j) ∂μ) := by
  have hi:=integral_density_power μ (fun x=>g x/Z^2) (hg.div_const _)
    (fun x=>div_nonneg (hgn x) (sq_nonneg _)) hmap j
  have he:(fun x:ℝ=>x^(2*j)*(g x/Z^2))=fun x=>x^(2*j)*g x/Z^2 := by funext x; ring
  rw [he,integral_div] at hi
  exact ((eq_div_iff (pow_ne_zero _ hZ.ne')).mp hi).symm.trans (by ring)

private lemma density_moment_integrable {μ:Measure (ℝ×ℝ)} {g:ℝ→ℝ} {Z:ℝ}
    (hg:Measurable g) (hgn:∀x,0≤g x) (hZ:0<Z)
    (hmap:Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ=volume.withDensity (fun x=>ENNReal.ofReal (g x/Z^2))) (j:ℕ)
    (hj:Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) μ) :
    Integrable (fun x:ℝ=>x^(2*j)*g x) := by
  have hi:=(integrable_density_power μ (fun x=>g x/Z^2) (hg.div_const _)
    (fun x=>div_nonneg (hgn x) (sq_nonneg _)) hmap j hj).mul_const (Z^2)
  apply hi.congr
  filter_upwards [] with x
  field_simp

theorem integrable_pow_mul_liClockPairedEtaInfinitePartitionRawDifferenceDensity (j:ℕ) :
    Integrable (fun x:ℝ=>x^(2*j)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x) :=
  density_moment_integrable measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
    liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg liClockPairedEtaInfinitePartitionNormalizer_pos
    liClockPairedEtaInfinitePartitionDifferenceDensity_map j (integrable_liClockPairedEtaInfiniteSymmetrizedEvenMoment j)

theorem integrable_pow_mul_liClockPairedEtaHalfLineRawDifferenceDensity (j:ℕ) :
    Integrable (fun x:ℝ=>x^(2*j)*liClockPairedEtaHalfLineRawDifferenceDensity x) :=
  density_moment_integrable measurable_liClockPairedEtaHalfLineRawDifferenceDensity
    liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
    (by rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two]; norm_num)
    liClockPairedEtaHalfLineDifferenceDensity_map j (integrable_liClockPairedEtaHalfLineSymmetrizedEvenMoment j)

theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_moment (j:ℕ) :
    (∫x:ℝ,x^(2*j)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x)=
      liClockPairedEtaInfinitePartitionNormalizer^2*liClockPairedEtaInfiniteSymmetrizedEvenMoment j :=
  density_moment_eq measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity
    liClockPairedEtaInfinitePartitionRawDifferenceDensity_nonneg liClockPairedEtaInfinitePartitionNormalizer_pos
    liClockPairedEtaInfinitePartitionDifferenceDensity_map j

theorem liClockPairedEtaHalfLineRawDifferenceDensity_moment (j:ℕ) :
    (∫x:ℝ,x^(2*j)*liClockPairedEtaHalfLineRawDifferenceDensity x)=
      liClockPairedEtaHalfLinePartitionNormalizer^2*liClockPairedEtaHalfLineSymmetrizedEvenMoment j :=
  density_moment_eq measurable_liClockPairedEtaHalfLineRawDifferenceDensity
    liClockPairedEtaHalfLineRawDifferenceDensity_nonneg
    (by rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two]; norm_num)
    liClockPairedEtaHalfLineDifferenceDensity_map j

theorem liClockPairedEtaInfiniteSymmetrizedEvenMoment_zero :
    liClockPairedEtaInfiniteSymmetrizedEvenMoment 0=1 := by
  letI:=liClockPairedEtaInfiniteSymmetrizedMeasure_isProbability
  simp [liClockPairedEtaInfiniteSymmetrizedEvenMoment]

theorem liClockPairedEtaHalfLineSymmetrizedEvenMoment_zero :
    liClockPairedEtaHalfLineSymmetrizedEvenMoment 0=1 := by
  letI:=liClockPairedEtaHalfLineSymmetrizedMeasure_isProbability
  simp [liClockPairedEtaHalfLineSymmetrizedEvenMoment]

theorem liClockPairedEtaInfiniteSymmetrizedEvenMoment_pos (j:ℕ) :
    0<liClockPairedEtaInfiniteSymmetrizedEvenMoment j := by
  rw [liClockPairedEtaInfiniteSymmetrizedEvenMoment_eq_double_integral]
  apply div_pos _ (sq_pos_of_pos liClockPairedEtaInfinitePartitionNormalizer_pos)
  have hle:=integral_mono_measure (Measure.prod_mono firstMeasure_le firstMeasure_le)
    (Eventually.of_forall fun p:ℝ×ℝ=>mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) j) (Real.exp_pos _).le)
    (integrable_liClockPairedEtaInfiniteRawEvenMoment j)
  have hfirst:0<(∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
      ∂(liClockPairedEtaContiguousLogMeasure (Real.log 2)).prod (liClockPairedEtaContiguousLogMeasure (Real.log 2))) := by
    have hid:=liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral (Real.log 2) j
    exact (div_pos_iff.mp ((liClockPairedEtaContiguousSymmetrizedEvenMoment_pos (Real.log_pos (by norm_num)) j).trans_eq hid)).resolve_right
      (fun h=> (sq_nonneg _).not_gt h.2) |>.1
  exact hfirst.trans_le hle

theorem liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos (j:ℕ) :
    0<liClockPairedEtaHalfLineSymmetrizedEvenMoment j := by
  have hle:=integral_mono (integrable_pow_mul_liClockPairedEtaInfinitePartitionRawDifferenceDensity j)
    (integrable_pow_mul_liClockPairedEtaHalfLineRawDifferenceDensity j)
    (fun x=>mul_le_mul_of_nonneg_left (liClockPairedEtaInfinitePartitionRawDifferenceDensity_le_halfLine x)
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) j))
  rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_moment,liClockPairedEtaHalfLineRawDifferenceDensity_moment,
    liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at hle
  nlinarith [liClockPairedEtaInfiniteSymmetrizedEvenMoment_pos j,
    sq_pos_of_pos liClockPairedEtaInfinitePartitionNormalizer_pos]


private lemma firstNormalizer_eq :
    liClockPairedEtaContiguousPartitionNormalizer (Real.log 2)=2-Real.sqrt 2 := by
  rw [liClockPairedEtaContiguousPartitionNormalizer_eq (Real.log_pos (by norm_num)).le]
  have he:Real.exp (Real.log 2/2)=Real.sqrt 2 := by
    rw [←Real.log_sqrt (by norm_num:0≤(2:ℝ)),Real.exp_log (Real.sqrt_pos.mpr (by norm_num))]
  have hen:Real.exp (-Real.log 2/2)=1/Real.sqrt 2 := by
    rw [show -Real.log 2/2=-(Real.log 2/2) by ring,Real.exp_neg,he]
    simp only [one_div]
  rw [hen]
  have hs:=Real.sq_sqrt (by norm_num:0≤(2:ℝ))
  have hp:Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp
  nlinarith

theorem liClockPairedEtaInfinitePartitionNormalizer_ge_first :
    2-Real.sqrt 2≤liClockPairedEtaInfinitePartitionNormalizer := by
  simpa only [firstNormalizer_eq] using liClockPairedEtaInfinitePartitionNormalizer_ge_firstInterval

theorem liClockPairedEtaPartitionLogSupport_subset_infinite (N:ℕ) :
    liClockPairedEtaPartitionLogSupport N⊆pairedEtaLogSupport := by
  intro u hu
  simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion] at hu
  obtain ⟨n,hn,hu⟩:=hu
  exact mem_iUnion.mpr ⟨n,hu⟩

theorem liClockPairedEtaPartitionLogSupport_eq_infinite_inter {N:ℕ} (hN:0<N) :
    liClockPairedEtaPartitionLogSupport N=pairedEtaLogSupport∩Ioc 0 (Real.log (2*(N:ℝ))) := by
  apply subset_antisymm
  · exact subset_inter (liClockPairedEtaPartitionLogSupport_subset_infinite N)
      (liClockPairedEtaPartitionLogSupport_subset_Ioc N)
  · intro u hu
    obtain ⟨n,hn⟩:=mem_iUnion.mp hu.1
    have hnN:n<N := by
      by_contra hnN
      have hcast:(N:ℝ)≤(n:ℝ) := by exact_mod_cast (show N≤n by omega)
      have hlog:Real.log (2*(N:ℝ))<Real.log (2*(n:ℝ)+1) :=
        Real.log_lt_log (by exact_mod_cast (show 0<2*N by omega)) (by linarith)
      exact (not_lt_of_ge hu.2.2) (hlog.trans hn.1)
    simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion]
    exact ⟨n,Finset.mem_range.mpr hnN,hn⟩

theorem pairedEtaFiniteLogMeasure_eq_infinite_restrict {N:ℕ} (hN:0<N) :
    pairedEtaFiniteLogMeasure N=pairedEtaLogMeasure.restrict (Ioc 0 (Real.log (2*(N:ℝ)))) := by
  rw [pairedEtaFiniteLogMeasure_eq_restrict_union,liClockPairedEtaPartitionLogSupport_eq_infinite_inter hN,
    pairedEtaLogMeasure,Measure.restrict_restrict measurableSet_Ioc,inter_comm]

theorem pairedEtaFiniteLogMeasure_le_infinite (N:ℕ) : pairedEtaFiniteLogMeasure N≤pairedEtaLogMeasure := by
  rw [pairedEtaFiniteLogMeasure_eq_restrict_union]
  exact Measure.restrict_mono_set volume (liClockPairedEtaPartitionLogSupport_subset_infinite N)

theorem pairedEtaFiniteLogMeasure_prod_le_infinite (N:ℕ) :
    (pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)≤pairedEtaLogMeasure.prod pairedEtaLogMeasure :=
  Measure.prod_mono (pairedEtaFiniteLogMeasure_le_infinite N) (pairedEtaFiniteLogMeasure_le_infinite N)

private lemma firstMeasure_le_finite {N:ℕ} (hN:0<N) :
    liClockPairedEtaContiguousLogMeasure (Real.log 2)≤pairedEtaFiniteLogMeasure N := by
  rw [pairedEtaFiniteLogMeasure_eq_restrict_union]
  apply Measure.restrict_mono_set volume
  intro u hu
  simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion]
  refine ⟨0,Finset.mem_range.mpr hN,?_⟩
  simpa using hu

theorem liClockPairedEtaPartitionNormalizer_ge_first {N:ℕ} (hN:0<N) :
    2-Real.sqrt 2≤liClockPairedEtaPartitionNormalizer N := by
  have h:=integral_mono_measure (firstMeasure_le_finite hN) (Eventually.of_forall fun u=>(Real.exp_pos _).le)
    (show Integrable (fun u:ℝ=>Real.exp (-u/2)) (pairedEtaFiniteLogMeasure N) from
      infinite_half_integrable.mono_measure (pairedEtaFiniteLogMeasure_le_infinite N))
  change liClockPairedEtaContiguousPartitionNormalizer (Real.log 2)≤liClockPairedEtaPartitionNormalizer N at h
  rwa [firstNormalizer_eq] at h

theorem liClockPairedEtaContiguousPartitionNormalizer_ge_first {N:ℕ} (hN:0<N) :
    2-Real.sqrt 2≤liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ))) :=
  (liClockPairedEtaPartitionNormalizer_ge_first hN).trans (liClockPairedEtaPartitionNormalizer_le_contiguous N)

theorem liClockPairedEtaInfinitePartitionHalfTiltWeight_integral :
    (∫u:ℝ,liClockPairedEtaInfinitePartitionHalfTiltWeight u)=liClockPairedEtaInfinitePartitionNormalizer := by
  change (∫u:ℝ,pairedEtaLogSupport.indicator (fun v:ℝ=>Real.exp (-v/2)) u)=_
  rw [integral_indicator measurableSet_pairedEtaLogSupport]
  rfl

theorem liClockPairedEtaHalfLineHalfTiltWeight_integral :
    (∫u:ℝ,liClockPairedEtaHalfLineHalfTiltWeight u)=liClockPairedEtaHalfLinePartitionNormalizer := by
  change (∫u:ℝ,(Ioi 0).indicator (fun v:ℝ=>Real.exp (-v/2)) u)=_
  rw [integral_indicator measurableSet_Ioi]
  rfl

private lemma finiteHalfWeight_integral (N:ℕ) :
    (∫u:ℝ,liClockPairedEtaPartitionHalfTiltWeight N u)=liClockPairedEtaPartitionNormalizer N := by
  change (∫u:ℝ,(liClockPairedEtaPartitionLogSupport N).indicator (fun v:ℝ=>Real.exp (-v/2)) u)=_
  rw [integral_indicator (measurableSet_liClockPairedEtaPartitionLogSupport N),
    ←pairedEtaFiniteLogMeasure_eq_restrict_union]
  rfl

private lemma finiteHalfWeight_integrable (N:ℕ) : Integrable (liClockPairedEtaPartitionHalfTiltWeight N) :=
  halfWeight_integrable (measurableSet_liClockPairedEtaPartitionLogSupport N)
    ((liClockPairedEtaPartitionLogSupport_subset_infinite N).trans pairedEtaLogSupport_subset_Ioi_zero)

theorem liClockPairedEtaPartitionNormalizer_le_infinite (N:ℕ) :
    liClockPairedEtaPartitionNormalizer N≤liClockPairedEtaInfinitePartitionNormalizer :=
  integral_mono_measure (pairedEtaFiniteLogMeasure_le_infinite N)
    (Eventually.of_forall fun u=>(Real.exp_pos (-u/2)).le) infinite_half_integrable

private lemma truncatedWeight_deficit {S:Set ℝ} (hS:S⊆Ioi 0) (L u:ℝ) :
    0≤halfWeight S u-halfWeight (S∩Ioc 0 L) u ∧
      halfWeight S u-halfWeight (S∩Ioc 0 L) u≤(Ioi L).indicator (fun u:ℝ=>Real.exp (-u/2)) u := by
  by_cases hu:u∈S
  · have hu0:0<u:=hS hu
    by_cases huL:u≤L
    · have hmem:u∈S∩Ioc 0 L:=⟨hu,hu0,huL⟩
      simp only [halfWeight,indicator_of_mem hu,indicator_of_mem hmem,sub_self]
      exact ⟨le_rfl,by exact indicator_nonneg (fun _ _=>(Real.exp_pos _).le) _⟩
    · have hmem:u∉S∩Ioc 0 L:=by intro hm; exact huL hm.2.2
      have ht:u∈Ioi L:=lt_of_not_ge huL
      simp [halfWeight,hu,hmem,ht,(Real.exp_pos _).le]
  · have hmem:u∉S∩Ioc 0 L:=by intro hm; exact hu hm.1
    simp only [halfWeight,indicator_of_notMem hu,indicator_of_notMem hmem,sub_self]
    exact ⟨le_rfl,by exact indicator_nonneg (fun _ _=>(Real.exp_pos _).le) _⟩

theorem liClockPairedEtaInfinitePartitionNormalizer_sub_finite_le {N:ℕ} (hN:0<N) :
    0≤liClockPairedEtaInfinitePartitionNormalizer-liClockPairedEtaPartitionNormalizer N ∧
      liClockPairedEtaInfinitePartitionNormalizer-liClockPairedEtaPartitionNormalizer N≤
        2*Real.exp (-Real.log (2*(N:ℝ))/2) := by
  have hT:Integrable ((Ioi (Real.log (2*(N:ℝ)))).indicator (fun u:ℝ=>Real.exp (-u/2))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    apply (integrableOn_exp_mul_Ioi (a:= -(1/2:ℝ)) (by norm_num) (Real.log (2*(N:ℝ)))).congr
    filter_upwards [] with u
    congr 1; ring
  have hle:=integral_mono (integrable_liClockPairedEtaInfinitePartitionHalfTiltWeight.sub (finiteHalfWeight_integrable N)) hT
    (fun u=>by simpa only [Pi.sub_apply,halfWeight,liClockPairedEtaInfinitePartitionHalfTiltWeight,liClockPairedEtaPartitionHalfTiltWeight,
      liClockPairedEtaPartitionLogSupport_eq_infinite_inter hN] using
      (truncatedWeight_deficit pairedEtaLogSupport_subset_Ioi_zero (Real.log (2*(N:ℝ))) u).2)
  change (∫u:ℝ,liClockPairedEtaInfinitePartitionHalfTiltWeight u-liClockPairedEtaPartitionHalfTiltWeight N u)≤_ at hle
  rw [integral_sub integrable_liClockPairedEtaInfinitePartitionHalfTiltWeight (finiteHalfWeight_integrable N),
    liClockPairedEtaInfinitePartitionHalfTiltWeight_integral,finiteHalfWeight_integral,
    integral_indicator measurableSet_Ioi] at hle
  have hi:(∫u:ℝ in Ioi (Real.log (2*(N:ℝ))),Real.exp (-u/2))=2*Real.exp (-Real.log (2*(N:ℝ))/2) := by
    calc
      _=(∫u:ℝ in Ioi (Real.log (2*(N:ℝ))),Real.exp (-(1/2:ℝ)*u)) := by
        apply integral_congr_ae
        filter_upwards [] with u
        congr 1; ring
      _= -Real.exp (-(1/2:ℝ)*Real.log (2*(N:ℝ)))/(-(1/2:ℝ)) := integral_exp_mul_Ioi (by norm_num) _
      _=_ := by
        rw [show -(1/2:ℝ)*Real.log (2*(N:ℝ))= -Real.log (2*(N:ℝ))/2 by ring]
        ring
  exact ⟨sub_nonneg.mpr (liClockPairedEtaPartitionNormalizer_le_infinite N),hle.trans_eq hi⟩

theorem liClockPairedEtaHalfLinePartitionNormalizer_sub_contiguous {L:ℝ} (hL:0≤L) :
    liClockPairedEtaHalfLinePartitionNormalizer-liClockPairedEtaContiguousPartitionNormalizer L=2*Real.exp (-L/2) := by
  rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two,liClockPairedEtaContiguousPartitionNormalizer_eq hL]
  ring


private lemma missingGap_disjoint : Disjoint pairedEtaLogSupport (Ioc (Real.log 2) (Real.log 3)) := by
  apply Set.disjoint_left.mpr
  intro u hu hg
  obtain ⟨n,hu⟩:=mem_iUnion.mp hu
  by_cases hn:n=0
  · subst n
    simp only [pairedEtaLogInterval,Nat.cast_zero,mul_zero,zero_add,Real.log_one] at hu
    linarith [hu.2,hg.1]
  · have hn1:(1:ℝ)≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
    have hl:Real.log 3≤Real.log (2*(n:ℝ)+1) := Real.log_le_log (by norm_num) (by linarith)
    exact (not_lt_of_ge hg.2) (hl.trans_lt hu.1)

theorem liClockPairedEtaInfinitePartitionNormalizer_lt_two :
    liClockPairedEtaInfinitePartitionNormalizer<2 := by
  let gap:Set ℝ:=Ioc (Real.log 2) (Real.log 3)
  have hg:gap⊆Ioi 0 := by intro u hu; exact (Real.log_pos (by norm_num)).trans hu.1
  have hmeas:pairedEtaLogMeasure+volume.restrict gap≤liClockPairedEtaHalfLineLogMeasure := by
    rw [pairedEtaLogMeasure,←Measure.restrict_union missingGap_disjoint measurableSet_Ioc]
    exact Measure.restrict_mono_set volume (union_subset pairedEtaLogSupport_subset_Ioi_zero hg)
  have hab:Real.log 2<Real.log 3:=Real.log_lt_log (by norm_num) (by norm_num)
  have hgap:NeZero (volume.restrict gap:Measure ℝ) := by
    constructor
    intro hz
    have hu:=congrArg (fun m:Measure ℝ=>m univ) hz
    simp only [gap,Measure.restrict_apply_univ,Real.volume_Ioc,Measure.coe_zero,Pi.zero_apply] at hu
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hu
  letI:=hgap
  have hgi:Integrable (fun u:ℝ=>Real.exp (-u/2)) (volume.restrict gap) :=
    ((show Continuous (fun u:ℝ=>Real.exp (-u/2)) by fun_prop).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hpos:=integral_exp_pos hgi
  have hle:=integral_mono_measure hmeas (Eventually.of_forall fun u=>(Real.exp_pos (-u/2)).le) halfLine_half_integrable
  rw [integral_add_measure infinite_half_integrable hgi] at hle
  change liClockPairedEtaInfinitePartitionNormalizer+_≤liClockPairedEtaHalfLinePartitionNormalizer at hle
  rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at hle
  linarith

theorem pairedEtaLaplacePartition_half_eq_liClockPairedEtaInfinitePartitionNormalizer :
    pairedEtaLaplacePartition (1/2:ℂ)=(liClockPairedEtaInfinitePartitionNormalizer:ℂ) := by
  rw [←integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by norm_num)]
  calc
    _=∫u:ℝ,(Real.exp (-u/2):ℂ) ∂pairedEtaLogMeasure := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    _=_:=integral_complex_ofReal

private lemma complexHalfLineLaplace_eq {s:ℂ} (hs:0<s.re) :
    (∫u:ℝ,Complex.exp (-s*u) ∂liClockPairedEtaHalfLineLogMeasure)=1/s := by
  have h:=integral_exp_mul_complex_Ioi (a:= -s) (by simpa using hs) 0
  simpa only [liClockPairedEtaHalfLineLogMeasure,neg_mul,mul_zero,Complex.exp_zero,Complex.ofReal_zero,neg_div_neg_eq,one_div] using h

private lemma sym_mgf_integral (ν:Measure ℝ) [SFinite ν] (z:ℂ) :
    complexMGF (fun p:ℝ×ℝ=>p.1-p.2) ((ν.prod ν).tilted (fun p:ℝ×ℝ=>-(p.1+p.2)/2)) z =
      (∫u:ℝ,Complex.exp (-(1/2-z)*(u:ℂ)) ∂ν)*
      (∫u:ℝ,Complex.exp (-(1/2+z)*(u:ℂ)) ∂ν)/((∫u:ℝ,Real.exp (-u/2) ∂ν : ℝ):ℂ)^2 := by
  rw [complexMGF,integral_tilted,joint_integral]
  have heq:(fun p:ℝ×ℝ=>(Real.exp (-(p.1+p.2)/2)/(∫u:ℝ,Real.exp (-u/2) ∂ν)^2) •
      Complex.exp (z*((p.1-p.2:ℝ):ℂ))) =
      fun p:ℝ×ℝ=>(Complex.exp (-(1/2-z)*(p.1:ℂ))*Complex.exp (-(1/2+z)*(p.2:ℂ)))/
        ((∫u:ℝ,Real.exp (-u/2) ∂ν : ℝ):ℂ)^2 := by
    funext p
    rw [RCLike.real_smul_eq_coe_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_ofNat,Complex.ofReal_exp]
    rw [div_mul_eq_mul_div]; congr 1
    rw [←Complex.exp_add,←Complex.exp_add]; congr 1; ring
  rw [heq,integral_div]
  congr 1
  exact integral_prod_mul (fun u:ℝ=>Complex.exp (-(1/2-z)*(u:ℂ))) (fun u:ℝ=>Complex.exp (-(1/2+z)*(u:ℂ)))

theorem liClockPairedEtaInfiniteSymmetrizedMeasure_complexMGF_eq_source {z:ℂ} (hz:|z.re|<1/2) :
    complexMGF (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaInfiniteSymmetrizedMeasure z =
      pairedEtaLaplacePartition (1/2-z)*pairedEtaLaplacePartition (1/2+z)/
        (liClockPairedEtaInfinitePartitionNormalizer:ℂ)^2 := by
  change complexMGF _ ((pairedEtaLogMeasure.prod pairedEtaLogMeasure).tilted _) z=_
  rw [sym_mgf_integral,integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by
    simp only [Complex.sub_re]; norm_num; linarith [(abs_lt.mp hz).2]),
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (by
      simp only [Complex.add_re]; norm_num; linarith [(abs_lt.mp hz).1])]
  rfl

theorem liClockPairedEtaHalfLineSymmetrizedMeasure_complexMGF_eq_source {z:ℂ} (hz:|z.re|<1/2) :
    complexMGF (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaHalfLineSymmetrizedMeasure z=1/(1-4*z^2) := by
  change complexMGF _ ((liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure).tilted _) z=_
  rw [sym_mgf_integral,complexHalfLineLaplace_eq (by
    simp only [Complex.sub_re]; norm_num; linarith [(abs_lt.mp hz).2]),
    complexHalfLineLaplace_eq (by
      simp only [Complex.add_re]; norm_num; linarith [(abs_lt.mp hz).1])]
  change (1/(1/2-z))*(1/(1/2+z))/(liClockPairedEtaHalfLinePartitionNormalizer:ℂ)^2=_
  rw [liClockPairedEtaHalfLinePartitionNormalizer_eq_two]
  rw [show 1-4*z^2=4*(1/2-z)*(1/2+z) by ring]
  simp only [div_eq_mul_inv,mul_inv]
  norm_num
  ring

theorem analyticAt_liClockPairedEtaInfiniteSymmetrizedMeasure_complexMGF {z:ℂ} (hz:|z.re|<1/2) :
    AnalyticAt ℂ (complexMGF (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaInfiniteSymmetrizedMeasure) z :=
  analyticAt_complexMGF (sym_interior (ν:=pairedEtaLogMeasure) pairedEtaLogMeasure_le_volume_restrict_Ioi_zero hz)

theorem analyticAt_liClockPairedEtaHalfLineSymmetrizedMeasure_complexMGF {z:ℂ} (hz:|z.re|<1/2) :
    AnalyticAt ℂ (complexMGF (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaHalfLineSymmetrizedMeasure) z :=
  analyticAt_complexMGF (sym_interior (ν:=liClockPairedEtaHalfLineLogMeasure) le_rfl hz)

theorem iteratedDeriv_liClockPairedEtaInfiniteSymmetrizedMeasure_complexMGF {z:ℂ} (hz:|z.re|<1/2) (n:ℕ) :
    iteratedDeriv n (complexMGF (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaInfiniteSymmetrizedMeasure) z=
      ∫p:ℝ×ℝ,((p.1-p.2:ℝ):ℂ)^n*Complex.exp (z*((p.1-p.2:ℝ):ℂ)) ∂liClockPairedEtaInfiniteSymmetrizedMeasure :=
  iteratedDeriv_complexMGF (sym_interior (ν:=pairedEtaLogMeasure) pairedEtaLogMeasure_le_volume_restrict_Ioi_zero hz) n

theorem iteratedDeriv_liClockPairedEtaHalfLineSymmetrizedMeasure_complexMGF {z:ℂ} (hz:|z.re|<1/2) (n:ℕ) :
    iteratedDeriv n (complexMGF (fun p:ℝ×ℝ=>p.1-p.2) liClockPairedEtaHalfLineSymmetrizedMeasure) z=
      ∫p:ℝ×ℝ,((p.1-p.2:ℝ):ℂ)^n*Complex.exp (z*((p.1-p.2:ℝ):ℂ)) ∂liClockPairedEtaHalfLineSymmetrizedMeasure :=
  iteratedDeriv_complexMGF (sym_interior (ν:=liClockPairedEtaHalfLineLogMeasure) le_rfl hz) n


private lemma halfWeight_inter (S J:Set ℝ) (u:ℝ) :
    halfWeight (S∩J) u=J.indicator (halfWeight S) u := by
  by_cases huS:u∈S <;> by_cases huJ:u∈J <;> simp [halfWeight,huS,huJ]

private lemma product_truncation_deficit {S:Set ℝ} (hS:S⊆Ioi 0) (J:Set ℝ) (u v:ℝ) :
    0≤halfWeight S u*halfWeight S v-halfWeight (S∩J) u*halfWeight (S∩J) v ∧
      halfWeight S u*halfWeight S v-halfWeight (S∩J) u*halfWeight (S∩J) v≤
      halfWeight (Ioi 0) u*halfWeight (Ioi 0) v-
        halfWeight (Ioi 0∩J) u*halfWeight (Ioi 0∩J) v := by
  have hpos:0≤halfWeight S u*halfWeight S v:=mul_nonneg (halfWeight_nonneg S _) (halfWeight_nonneg S _)
  have hle:halfWeight S u*halfWeight S v≤halfWeight (Ioi 0) u*halfWeight (Ioi 0) v:=
    mul_le_mul (halfWeight_mono hS u) (halfWeight_mono hS v) (halfWeight_nonneg S _) (halfWeight_nonneg _ _)
  simp only [halfWeight_inter]
  by_cases hu:u∈J <;> by_cases hv:v∈J <;>
    simp [hu,hv] <;> exact ⟨hpos,hle⟩

private lemma contiguousHalfWeight_eq (L u:ℝ) :
    liClockPairedEtaContiguousHalfTiltWeight L u=halfWeight (Ioi 0∩Ioc 0 L) u := by
  have hi:Ioi (0:ℝ)∩Ioc 0 L=Ioc 0 L:=inter_eq_right.mpr (fun _ h=>h.1)
  rw [hi]
  rfl

private lemma finiteTranslatedProduct_integrable (N:ℕ) (x:ℝ) :
    Integrable (fun v:ℝ=>liClockPairedEtaPartitionHalfTiltWeight N (v+x)*liClockPairedEtaPartitionHalfTiltWeight N v) :=
  halfWeight_prod_integrable (measurableSet_liClockPairedEtaPartitionLogSupport N)
    ((liClockPairedEtaPartitionLogSupport_subset_infinite N).trans pairedEtaLogSupport_subset_Ioi_zero) x

private lemma contiguousTranslatedProduct_integrable (L x:ℝ) :
    Integrable (fun v:ℝ=>liClockPairedEtaContiguousHalfTiltWeight L (v+x)*liClockPairedEtaContiguousHalfTiltWeight L v) :=
  halfWeight_prod_integrable measurableSet_Ioc (fun _ h=>h.1) x

theorem liClockPairedEtaInfinitePartitionRawDifferenceDensity_sub_finite_le {N:ℕ} (hN:0<N) (x:ℝ) :
    0≤liClockPairedEtaInfinitePartitionRawDifferenceDensity x-liClockPairedEtaPartitionRawDifferenceDensity N x ∧
      liClockPairedEtaInfinitePartitionRawDifferenceDensity x-liClockPairedEtaPartitionRawDifferenceDensity N x≤
        liClockPairedEtaHalfLineRawDifferenceDensity x-
          liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x := by
  let L:=Real.log (2*(N:ℝ))
  have hpoint (v:ℝ):
      0≤liClockPairedEtaInfinitePartitionHalfTiltWeight (v+x)*liClockPairedEtaInfinitePartitionHalfTiltWeight v-
        liClockPairedEtaPartitionHalfTiltWeight N (v+x)*liClockPairedEtaPartitionHalfTiltWeight N v ∧
      liClockPairedEtaInfinitePartitionHalfTiltWeight (v+x)*liClockPairedEtaInfinitePartitionHalfTiltWeight v-
        liClockPairedEtaPartitionHalfTiltWeight N (v+x)*liClockPairedEtaPartitionHalfTiltWeight N v≤
      liClockPairedEtaHalfLineHalfTiltWeight (v+x)*liClockPairedEtaHalfLineHalfTiltWeight v-
        liClockPairedEtaContiguousHalfTiltWeight L (v+x)*liClockPairedEtaContiguousHalfTiltWeight L v := by
    simpa only [liClockPairedEtaInfinitePartitionHalfTiltWeight,liClockPairedEtaPartitionHalfTiltWeight,
      liClockPairedEtaPartitionLogSupport_eq_infinite_inter hN,liClockPairedEtaHalfLineHalfTiltWeight,
      contiguousHalfWeight_eq,halfWeight,L] using
      product_truncation_deficit pairedEtaLogSupport_subset_Ioi_zero (Ioc 0 L) (v+x) v
  have hnon:0≤(∫v:ℝ,liClockPairedEtaInfinitePartitionHalfTiltWeight (v+x)*liClockPairedEtaInfinitePartitionHalfTiltWeight v-
      liClockPairedEtaPartitionHalfTiltWeight N (v+x)*liClockPairedEtaPartitionHalfTiltWeight N v) :=
    integral_nonneg (fun v=>(hpoint v).1)
  have hle:=integral_mono
    ((integrable_liClockPairedEtaInfinitePartitionTranslatedProduct x).sub (finiteTranslatedProduct_integrable N x))
    ((integrable_liClockPairedEtaHalfLineTranslatedProduct x).sub (contiguousTranslatedProduct_integrable L x))
    (fun v=>(hpoint v).2)
  change (∫v:ℝ,liClockPairedEtaInfinitePartitionHalfTiltWeight (v+x)*liClockPairedEtaInfinitePartitionHalfTiltWeight v-
      liClockPairedEtaPartitionHalfTiltWeight N (v+x)*liClockPairedEtaPartitionHalfTiltWeight N v)≤
    (∫v:ℝ,liClockPairedEtaHalfLineHalfTiltWeight (v+x)*liClockPairedEtaHalfLineHalfTiltWeight v-
      liClockPairedEtaContiguousHalfTiltWeight L (v+x)*liClockPairedEtaContiguousHalfTiltWeight L v) at hle
  rw [integral_sub (integrable_liClockPairedEtaInfinitePartitionTranslatedProduct x) (finiteTranslatedProduct_integrable N x)] at hnon hle
  rw [integral_sub (integrable_liClockPairedEtaHalfLineTranslatedProduct x) (contiguousTranslatedProduct_integrable L x)] at hle
  exact ⟨hnon,hle⟩

theorem liClockPairedEtaHalfLineRawDifferenceDensity_sub_contiguous (L x:ℝ) :
    liClockPairedEtaHalfLineRawDifferenceDensity x-liClockPairedEtaContiguousRawDifferenceDensity L x=
      if |x|<L then Real.exp (|x|/2-L) else Real.exp (-|x|/2) := by
  have hreplace:liClockPairedEtaContiguousRawDifferenceDensity L x=
      liClockPairedEtaContiguousRawDifferenceDensity L |x| := by
    by_cases hx:0≤x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx),liClockPairedEtaContiguousRawDifferenceDensity_even]
  rw [liClockPairedEtaHalfLineRawDifferenceDensity_eq]
  by_cases hxL:|x|<L
  · rw [if_pos hxL,hreplace,liClockPairedEtaContiguousRawDifferenceDensity_eq_of_nonneg (abs_nonneg _) hxL]
    calc
      _=Real.exp (-|x|/2)*Real.exp (|x|-L):=by ring
      _=_:=by rw [←Real.exp_add]; congr 1; ring
  · rw [if_neg hxL,liClockPairedEtaContiguousRawDifferenceDensity_zero_of_le_abs (le_of_not_gt hxL),sub_zero]


theorem tendsto_liClockPairedEtaPartitionLogEndpoint :
    Tendsto (fun N:ℕ=>Real.log (2*(N:ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num:0<(2:ℝ)))

private lemma eventually_finiteWeight_eq (u:ℝ) :
    ∀ᶠN:ℕ in atTop,liClockPairedEtaPartitionHalfTiltWeight N u=liClockPairedEtaInfinitePartitionHalfTiltWeight u := by
  by_cases hu:u∈pairedEtaLogSupport
  · obtain ⟨n,hn⟩:=mem_iUnion.mp hu
    filter_upwards [eventually_ge_atTop (n+1)] with N hN
    have hmem:u∈liClockPairedEtaPartitionLogSupport N := by
      simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion]
      exact ⟨n,Finset.mem_range.mpr (by omega),hn⟩
    simp only [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaInfinitePartitionHalfTiltWeight,
      indicator_of_mem hmem,indicator_of_mem hu]
  · filter_upwards [] with N
    have hmem:u∉liClockPairedEtaPartitionLogSupport N:=fun h=>hu (liClockPairedEtaPartitionLogSupport_subset_infinite N h)
    simp only [liClockPairedEtaPartitionHalfTiltWeight,liClockPairedEtaInfinitePartitionHalfTiltWeight,
      indicator_of_notMem hmem,indicator_of_notMem hu]

private lemma eventually_contiguousWeight_eq (u:ℝ) :
    ∀ᶠN:ℕ in atTop,liClockPairedEtaContiguousHalfTiltWeight (Real.log (2*(N:ℝ))) u=liClockPairedEtaHalfLineHalfTiltWeight u := by
  by_cases hu:0<u
  · filter_upwards [tendsto_liClockPairedEtaPartitionLogEndpoint.eventually (eventually_ge_atTop u)] with N hN
    have hm:u∈Ioc 0 (Real.log (2*(N:ℝ))) :=⟨hu,hN⟩
    change halfWeight (Ioc 0 (Real.log (2*(N:ℝ)))) u=halfWeight (Ioi 0) u
    simp [halfWeight,hm,hu]
  · filter_upwards [] with N
    change halfWeight (Ioc 0 (Real.log (2*(N:ℝ)))) u=halfWeight (Ioi 0) u
    have hm:u∉Ioc 0 (Real.log (2*(N:ℝ))) :=fun h=>hu h.1
    simp [halfWeight,hm,hu]

private lemma halfLineWeight_le_one (u:ℝ) : liClockPairedEtaHalfLineHalfTiltWeight u≤1 :=
  halfWeight_le_one le_rfl u

private lemma finiteWeight_le_halfLine (N:ℕ) (u:ℝ) :
    liClockPairedEtaPartitionHalfTiltWeight N u≤liClockPairedEtaHalfLineHalfTiltWeight u :=
  halfWeight_mono ((liClockPairedEtaPartitionLogSupport_subset_infinite N).trans pairedEtaLogSupport_subset_Ioi_zero) u

private lemma contiguousWeight_le_halfLine (L u:ℝ) :
    liClockPairedEtaContiguousHalfTiltWeight L u≤liClockPairedEtaHalfLineHalfTiltWeight u :=
  halfWeight_mono (fun _ h=>h.1) u

private lemma raw_density_tendsto {fN:ℕ→ℝ→ℝ} {f:ℝ→ℝ}
    (hmeas:∀N,Measurable (fN N)) (hnon:∀N u,0≤fN N u)
    (hle:∀N u,fN N u≤liClockPairedEtaHalfLineHalfTiltWeight u)
    (heq:∀u,∀ᶠN in atTop,fN N u=f u) (x:ℝ) :
    Tendsto (fun N:ℕ=>∫v:ℝ,fN N (v+x)*fN N v) atTop (nhds (∫v:ℝ,f (v+x)*f v)) := by
  apply tendsto_integral_of_dominated_convergence liClockPairedEtaHalfLineHalfTiltWeight
    (fun N=>by exact ((hmeas N).comp (measurable_id.add_const x)).mul (hmeas N) |>.aestronglyMeasurable)
    integrable_liClockPairedEtaHalfLineHalfTiltWeight
  · intro N
    filter_upwards [] with v
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hnon N _) (hnon N _))]
    exact (mul_le_of_le_one_left (hnon N _) ((hle N _).trans (halfLineWeight_le_one _))).trans (hle N _)
  · filter_upwards [] with v
    apply tendsto_const_nhds.congr'
    filter_upwards [heq (v+x),heq v] with N h1 h2
    rw [h1,h2]

theorem tendsto_liClockPairedEtaInfinitePartitionRawDifferenceDensity (x:ℝ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaPartitionRawDifferenceDensity N x) atTop
      (nhds (liClockPairedEtaInfinitePartitionRawDifferenceDensity x)) :=
  raw_density_tendsto (fun N=>halfWeight_measurable (measurableSet_liClockPairedEtaPartitionLogSupport N))
    (fun N u=>halfWeight_nonneg (liClockPairedEtaPartitionLogSupport N) u) finiteWeight_le_halfLine eventually_finiteWeight_eq x

theorem tendsto_liClockPairedEtaHalfLineRawDifferenceDensity (x:ℝ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x) atTop
      (nhds (liClockPairedEtaHalfLineRawDifferenceDensity x)) :=
  raw_density_tendsto (fun _=>halfWeight_measurable measurableSet_Ioc)
    (fun N u=>halfWeight_nonneg (Ioc 0 (Real.log (2*(N:ℝ)))) u) (fun N=>contiguousWeight_le_halfLine (Real.log (2*(N:ℝ)))) eventually_contiguousWeight_eq x

private lemma normalizer_tendsto {fN:ℕ→ℝ→ℝ} {f:ℝ→ℝ}
    (hmeas:∀N,Measurable (fN N)) (hnon:∀N u,0≤fN N u)
    (hle:∀N u,fN N u≤liClockPairedEtaHalfLineHalfTiltWeight u)
    (heq:∀u,∀ᶠN in atTop,fN N u=f u) :
    Tendsto (fun N:ℕ=>∫u:ℝ,fN N u) atTop (nhds (∫u:ℝ,f u)) := by
  apply tendsto_integral_of_dominated_convergence liClockPairedEtaHalfLineHalfTiltWeight
    (fun N=>(hmeas N).aestronglyMeasurable) integrable_liClockPairedEtaHalfLineHalfTiltWeight
  · intro N
    exact Eventually.of_forall (fun u=>by rw [Real.norm_eq_abs,abs_of_nonneg (hnon N u)]; exact hle N u)
  · exact Eventually.of_forall (fun u=>tendsto_const_nhds.congr' ((heq u).mono (fun N h=>h.symm)))

theorem tendsto_liClockPairedEtaInfinitePartitionNormalizer :
    Tendsto liClockPairedEtaPartitionNormalizer atTop (nhds liClockPairedEtaInfinitePartitionNormalizer) := by
  have h:=normalizer_tendsto (fN:=liClockPairedEtaPartitionHalfTiltWeight) (f:=liClockPairedEtaInfinitePartitionHalfTiltWeight)
    (fun N=>halfWeight_measurable (measurableSet_liClockPairedEtaPartitionLogSupport N))
    (fun N u=>halfWeight_nonneg (liClockPairedEtaPartitionLogSupport N) u) finiteWeight_le_halfLine eventually_finiteWeight_eq
  simpa only [finiteHalfWeight_integral,liClockPairedEtaInfinitePartitionHalfTiltWeight_integral] using h

theorem tendsto_liClockPairedEtaHalfLinePartitionNormalizer :
    Tendsto (fun N:ℕ=>liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))) atTop (nhds 2) := by
  have h:=normalizer_tendsto (fN:=fun N=>liClockPairedEtaContiguousHalfTiltWeight (Real.log (2*(N:ℝ))))
    (f:=liClockPairedEtaHalfLineHalfTiltWeight) (fun _=>halfWeight_measurable measurableSet_Ioc)
    (fun N u=>halfWeight_nonneg (Ioc 0 (Real.log (2*(N:ℝ)))) u) (fun N=>contiguousWeight_le_halfLine (Real.log (2*(N:ℝ)))) eventually_contiguousWeight_eq
  have he(L:ℝ):(∫u:ℝ,liClockPairedEtaContiguousHalfTiltWeight L u)=liClockPairedEtaContiguousPartitionNormalizer L := by
    change (∫u:ℝ,(Ioc 0 L).indicator (fun v:ℝ=>Real.exp (-v/2)) u)=_
    rw [integral_indicator measurableSet_Ioc]
    rfl
  simpa only [he,liClockPairedEtaHalfLineHalfTiltWeight_integral,liClockPairedEtaHalfLinePartitionNormalizer_eq_two] using h


private lemma first_mass_pos : 0<2-Real.sqrt 2 := by
  nlinarith [Real.sqrt_nonneg (2:ℝ),Real.sq_sqrt (by norm_num:0≤(2:ℝ))]

theorem liClockPairedEtaPartitionRawDifferenceDensity_le_halfLine (N:ℕ) (x:ℝ) :
    liClockPairedEtaPartitionRawDifferenceDensity N x≤liClockPairedEtaHalfLineRawDifferenceDensity x := by
  exact integral_mono (finiteTranslatedProduct_integrable N x) (integrable_liClockPairedEtaHalfLineTranslatedProduct x)
    (fun v=>mul_le_mul (finiteWeight_le_halfLine N _) (finiteWeight_le_halfLine N _)
      (halfWeight_nonneg _ _) (liClockPairedEtaHalfLineHalfTiltWeight_nonneg _))

theorem liClockPairedEtaContiguousRawDifferenceDensity_le_halfLine (L x:ℝ) :
    liClockPairedEtaContiguousRawDifferenceDensity L x≤liClockPairedEtaHalfLineRawDifferenceDensity x := by
  exact integral_mono (contiguousTranslatedProduct_integrable L x) (integrable_liClockPairedEtaHalfLineTranslatedProduct x)
    (fun v=>mul_le_mul (contiguousWeight_le_halfLine L _) (contiguousWeight_le_halfLine L _)
      (halfWeight_nonneg _ _) (liClockPairedEtaHalfLineHalfTiltWeight_nonneg _))

private lemma raw_moment_tendsto {gN:ℕ→ℝ→ℝ} {g:ℝ→ℝ}
    (hmeas:∀N,Measurable (gN N)) (hnon:∀N x,0≤gN N x)
    (hle:∀N x,gN N x≤liClockPairedEtaHalfLineRawDifferenceDensity x)
    (hlim:∀x,Tendsto (fun N:ℕ=>gN N x) atTop (nhds (g x))) (j:ℕ) :
    Tendsto (fun N:ℕ=>∫x:ℝ,x^(2*j)*gN N x) atTop (nhds (∫x:ℝ,x^(2*j)*g x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x:ℝ=>x^(2*j)*liClockPairedEtaHalfLineRawDifferenceDensity x)
    (fun N=>by exact (show Measurable (fun x:ℝ=>x^(2*j)) by fun_prop).mul (hmeas N) |>.aestronglyMeasurable)
    (integrable_pow_mul_liClockPairedEtaHalfLineRawDifferenceDensity j)
  · intro N
    filter_upwards [] with x
    have hx:0≤x^(2*j) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) j
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (hnon N x))]
    exact mul_le_mul_of_nonneg_left (hle N x) hx
  · exact Eventually.of_forall (fun x=>tendsto_const_nhds.mul (hlim x))

theorem tendsto_liClockPairedEtaInfiniteSymmetrizedEvenMoment (j:ℕ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaSymmetrizedEvenMoment N j) atTop
      (nhds (liClockPairedEtaInfiniteSymmetrizedEvenMoment j)) := by
  have hraw:=raw_moment_tendsto (fun N=>(continuous_liClockPairedEtaPartitionRawDifferenceDensity N).measurable)
    liClockPairedEtaPartitionRawDifferenceDensity_nonneg liClockPairedEtaPartitionRawDifferenceDensity_le_halfLine
    tendsto_liClockPairedEtaInfinitePartitionRawDifferenceDensity j
  have h:=hraw.div (tendsto_liClockPairedEtaInfinitePartitionNormalizer.pow 2)
    (pow_ne_zero _ liClockPairedEtaInfinitePartitionNormalizer_pos.ne')
  have hn:(∫x:ℝ,x^(2*j)*liClockPairedEtaInfinitePartitionRawDifferenceDensity x)/
      liClockPairedEtaInfinitePartitionNormalizer^2=liClockPairedEtaInfiniteSymmetrizedEvenMoment j := by
    rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_moment]
    field_simp [liClockPairedEtaInfinitePartitionNormalizer_pos.ne']
  rw [hn] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  change (∫x:ℝ,x^(2*j)*liClockPairedEtaPartitionRawDifferenceDensity N x)/liClockPairedEtaPartitionNormalizer N^2=_
  rw [liClockPairedEtaPartitionRawDifferenceDensity_moment (by omega:0<N) j]
  field_simp [(liClockPairedEtaPartitionNormalizer_pos (by omega:0<N)).ne']

theorem tendsto_liClockPairedEtaHalfLineSymmetrizedEvenMoment (j:ℕ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j) atTop
      (nhds (liClockPairedEtaHalfLineSymmetrizedEvenMoment j)) := by
  have hraw:=raw_moment_tendsto (fun N=>(continuous_liClockPairedEtaContiguousRawDifferenceDensity _).measurable)
    (fun N=>liClockPairedEtaContiguousRawDifferenceDensity_nonneg (Real.log (2*(N:ℝ))))
    (fun N=>liClockPairedEtaContiguousRawDifferenceDensity_le_halfLine (Real.log (2*(N:ℝ))))
    tendsto_liClockPairedEtaHalfLineRawDifferenceDensity j
  have h:=hraw.div (tendsto_liClockPairedEtaHalfLinePartitionNormalizer.pow 2) (by norm_num: (2:ℝ)^2≠0)
  have hn:(∫x:ℝ,x^(2*j)*liClockPairedEtaHalfLineRawDifferenceDensity x)/(2:ℝ)^2=
      liClockPairedEtaHalfLineSymmetrizedEvenMoment j := by
    rw [liClockPairedEtaHalfLineRawDifferenceDensity_moment,liClockPairedEtaHalfLinePartitionNormalizer_eq_two]
    ring
  rw [hn] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hL:0<Real.log (2*(N:ℝ)) := by
    apply Real.log_pos
    have hc:(1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    linarith
  change (∫x:ℝ,x^(2*j)*liClockPairedEtaContiguousRawDifferenceDensity (Real.log (2*(N:ℝ))) x)/
    liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2=_
  rw [liClockPairedEtaContiguousRawDifferenceDensity_moment hL j]
  field_simp [(liClockPairedEtaContiguousPartitionNormalizer_pos hL).ne']

theorem liClockPairedEtaInfiniteSymmetrizedEvenMoment_le_halfLine (j:ℕ) :
    liClockPairedEtaInfiniteSymmetrizedEvenMoment j≤
      (4/liClockPairedEtaInfinitePartitionNormalizer^2)*liClockPairedEtaHalfLineSymmetrizedEvenMoment j := by
  have hle:=integral_mono (integrable_pow_mul_liClockPairedEtaInfinitePartitionRawDifferenceDensity j)
    (integrable_pow_mul_liClockPairedEtaHalfLineRawDifferenceDensity j)
    (fun x=>mul_le_mul_of_nonneg_left (liClockPairedEtaInfinitePartitionRawDifferenceDensity_le_halfLine x)
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) j))
  rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_moment,liClockPairedEtaHalfLineRawDifferenceDensity_moment,
    liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at hle
  norm_num at hle
  have h:liClockPairedEtaInfiniteSymmetrizedEvenMoment j≤
      (4*liClockPairedEtaHalfLineSymmetrizedEvenMoment j)/liClockPairedEtaInfinitePartitionNormalizer^2 :=
    (le_div_iff₀ (sq_pos_of_pos liClockPairedEtaInfinitePartitionNormalizer_pos)).mpr (by simpa [mul_comm] using hle)
  convert h using 1
  ring

private lemma finite_moment_uniform {a:ℝ} (ha:2-Real.sqrt 2≤a) {d e:ℝ}
    (he:0≤e) (hle:a^2*d≤4*e) : d≤(4/(2-Real.sqrt 2)^2)*e := by
  have hap:0<a:=first_mass_pos.trans_le ha
  have hd:d≤4*e/a^2 := (le_div_iff₀ (sq_pos_of_pos hap)).mpr (by simpa [mul_comm] using hle)
  have hsq:(2-Real.sqrt 2)^2≤a^2 := by nlinarith [first_mass_pos]
  have hdiv:4*e/a^2≤4*e/(2-Real.sqrt 2)^2:=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos first_mass_pos) hsq
  exact hd.trans (hdiv.trans_eq (by ring))

theorem liClockPairedEtaSymmetrizedEvenMoment_le_halfLine_uniform {N:ℕ} (hN:0<N) (j:ℕ) :
    liClockPairedEtaSymmetrizedEvenMoment N j≤
      (4/(2-Real.sqrt 2)^2)*liClockPairedEtaHalfLineSymmetrizedEvenMoment j := by
  apply finite_moment_uniform (liClockPairedEtaPartitionNormalizer_ge_first hN)
    (liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos j).le
  have hle:=integral_mono (integrable_pow_mul_liClockPairedEtaPartitionRawDifferenceDensity N j)
    (integrable_pow_mul_liClockPairedEtaHalfLineRawDifferenceDensity j)
    (fun x=>mul_le_mul_of_nonneg_left (liClockPairedEtaPartitionRawDifferenceDensity_le_halfLine N x)
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) j))
  rw [liClockPairedEtaPartitionRawDifferenceDensity_moment hN,
    liClockPairedEtaHalfLineRawDifferenceDensity_moment,liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at hle
  norm_num at hle
  exact hle

theorem liClockPairedEtaContiguousSymmetrizedEvenMoment_le_halfLine_uniform {N:ℕ} (hN:0<N) (j:ℕ) :
    liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j≤
      (4/(2-Real.sqrt 2)^2)*liClockPairedEtaHalfLineSymmetrizedEvenMoment j := by
  apply finite_moment_uniform (liClockPairedEtaContiguousPartitionNormalizer_ge_first hN)
    (liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos j).le
  have hL:0<Real.log (2*(N:ℝ)) := by
    apply Real.log_pos
    have hc:(1:ℝ)≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
    linarith
  have hle:=integral_mono (integrable_pow_mul_liClockPairedEtaContiguousRawDifferenceDensity _ j)
    (integrable_pow_mul_liClockPairedEtaHalfLineRawDifferenceDensity j)
    (fun x=>mul_le_mul_of_nonneg_left (liClockPairedEtaContiguousRawDifferenceDensity_le_halfLine (Real.log (2*(N:ℝ))) x)
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) j))
  rw [liClockPairedEtaContiguousRawDifferenceDensity_moment hL,
    liClockPairedEtaHalfLineRawDifferenceDensity_moment,liClockPairedEtaHalfLinePartitionNormalizer_eq_two] at hle
  norm_num at hle
  exact hle


theorem integrable_rexp_neg_mul_liClockPairedEtaHalfLineLogMeasure {a:ℝ} (ha:0<a) :
    Integrable (fun u:ℝ=>Real.exp (-a*u)) liClockPairedEtaHalfLineLogMeasure := halfLine_rexp_integrable ha

theorem integrable_liClockPairedEtaInfiniteJointWeight :
    Integrable (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)) (pairedEtaLogMeasure.prod pairedEtaLogMeasure) :=
  joint_integrable infinite_half_integrable

theorem integrable_liClockPairedEtaHalfLineJointWeight :
    Integrable (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2))
      (liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure) :=
  joint_integrable halfLine_half_integrable

theorem integrable_liClockPairedEtaInfiniteSymmetrizedComplexMoment {z:ℂ} (hz:|z.re|<1/2) (n:ℕ) :
    Integrable (fun p:ℝ×ℝ=>((p.1-p.2:ℝ):ℂ)^n*Complex.exp (z*((p.1-p.2:ℝ):ℂ)))
      liClockPairedEtaInfiniteSymmetrizedMeasure :=
  integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (sym_interior (ν:=pairedEtaLogMeasure) pairedEtaLogMeasure_le_volume_restrict_Ioi_zero hz) n

theorem integrable_liClockPairedEtaHalfLineSymmetrizedComplexMoment {z:ℂ} (hz:|z.re|<1/2) (n:ℕ) :
    Integrable (fun p:ℝ×ℝ=>((p.1-p.2:ℝ):ℂ)^n*Complex.exp (z*((p.1-p.2:ℝ):ℂ)))
      liClockPairedEtaHalfLineSymmetrizedMeasure :=
  integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (sym_interior (ν:=liClockPairedEtaHalfLineLogMeasure) le_rfl hz) n


end
end RHTower
