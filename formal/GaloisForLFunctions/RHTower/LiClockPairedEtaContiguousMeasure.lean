import GaloisForLFunctions.RHTower.LiClockPairedEtaFinitePartitionVolterra
import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousSource

/-!
# Literal contiguous half-tilt and complete actual-source comparison

The comparison source is Lebesgue restriction to `(0,L]`. Its independent product
is tilted by `-(u+v)/2` and normalized by the square of its literal partition value.
Every even difference moment and every Borel degree is retained. Positivity and
probability assertions require `L>0`; the transform identity retains the filled value
at zero and requires `L≥0` because the interval integral is oriented.

The actual finite eta measure remains the full disjoint logarithmic interval union.
Its restriction and product domination are proved before normalization. Missing gap
mass gives strict normalizer comparison for `N≥2`; `N=1` has exact equality. No
cumulant-clock sign, actual-gap substitution, growing-`N` estimate or RH premise enters.
-/

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate
namespace RHTower
noncomputable section

/-- Literal contiguous comparison source, with no interval-union substitution. -/
def liClockPairedEtaContiguousLogMeasure (L : ℝ) : Measure ℝ :=
  volume.restrict (Ioc 0 L)

instance liClockPairedEtaContiguousLogMeasure.instSFinite (L : ℝ) :
    SFinite (liClockPairedEtaContiguousLogMeasure L) := by
  unfold liClockPairedEtaContiguousLogMeasure
  infer_instance

/-- Literal positive half-tilt mass of the contiguous comparison interval. -/
def liClockPairedEtaContiguousPartitionNormalizer (L : ℝ) : ℝ :=
  ∫u:ℝ, Real.exp (-u/2) ∂liClockPairedEtaContiguousLogMeasure L

/-- Full independent product half-tilt; both normalizers are retained. -/
def liClockPairedEtaContiguousSymmetrizedMeasure (L : ℝ) : Measure (ℝ×ℝ) :=
  ((liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)).tilted
    (fun p:ℝ×ℝ=>-(p.1+p.2)/2)

/-- Every even difference moment of the normalized product source. -/
def liClockPairedEtaContiguousSymmetrizedEvenMoment (L : ℝ) (j : ℕ) : ℝ :=
  ∫p:ℝ×ℝ, (p.1-p.2)^(2*j) ∂liClockPairedEtaContiguousSymmetrizedMeasure L

/-- Complete Borel coefficient with two even factorials. -/
def liClockPairedEtaContiguousBorelCoefficient (L : ℝ) (j : ℕ) : ℝ :=
  liClockPairedEtaContiguousSymmetrizedEvenMoment L j / ((2*j).factorial:ℝ)^2

/-- Full real Borel kernel of the comparison difference measure. -/
def liClockPairedEtaContiguousBorelKernel (L t : ℝ) : ℝ :=
  ∑'j, liClockPairedEtaContiguousBorelCoefficient L j * t^(2*j)

/-- Entire-clock complex version of the full comparison Borel kernel. -/
def liClockPairedEtaContiguousBorelKernelComplex (L : ℝ) (z : ℂ) : ℂ :=
  ∑'j, (liClockPairedEtaContiguousBorelCoefficient L j:ℂ) * z^(2*j)

theorem integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure (L sigma : ℝ) :
    Integrable (fun u:ℝ=>Real.exp (-sigma*u)) (liClockPairedEtaContiguousLogMeasure L) := by
  exact ((show Continuous (fun u:ℝ=>Real.exp (-sigma*u)) by fun_prop).continuousOn.integrableOn_Icc).mono_set
    Ioc_subset_Icc_self

theorem integrable_cexp_neg_mul_liClockPairedEtaContiguousLogMeasure (L : ℝ) (s : ℂ) :
    Integrable (fun u:ℝ=>Complex.exp (-s*u)) (liClockPairedEtaContiguousLogMeasure L) := by
  exact ((show Continuous (fun u:ℝ=>Complex.exp (-s*u)) by fun_prop).continuousOn.integrableOn_Icc).mono_set
    Ioc_subset_Icc_self

theorem liClockPairedEtaContiguousPartition_eq_integral_logMeasure {L : ℝ}
    (hL : 0≤L) (s : ℂ) :
    liClockPairedEtaContiguousPartition L s =
      ∫u:ℝ, Complex.exp (-s*u) ∂liClockPairedEtaContiguousLogMeasure L := by
  exact intervalIntegral.integral_of_le hL

theorem liClockPairedEtaContiguousPartition_half_eq_normalizer {L : ℝ} (hL : 0≤L) :
    liClockPairedEtaContiguousPartition L (1/2:ℂ) =
      (liClockPairedEtaContiguousPartitionNormalizer L:ℂ) := by
  rw [liClockPairedEtaContiguousPartition_eq_integral_logMeasure hL]
  calc
    _ = ∫u:ℝ, (Real.exp (-u/2):ℂ) ∂liClockPairedEtaContiguousLogMeasure L := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    _ = _ := integral_complex_ofReal

theorem liClockPairedEtaContiguousPartitionNormalizer_pos {L : ℝ} (hL : 0<L) :
    0<liClockPairedEtaContiguousPartitionNormalizer L := by
  have hmeasure : NeZero (liClockPairedEtaContiguousLogMeasure L) := by
    constructor
    intro hz
    have hu := congrArg (fun m:Measure ℝ=>m univ) hz
    simp only [liClockPairedEtaContiguousLogMeasure, Measure.restrict_apply_univ,
      Real.volume_Ioc, sub_zero] at hu
    simp only [Measure.coe_zero, Pi.zero_apply] at hu
    exact (ENNReal.ofReal_pos.mpr hL).ne' hu
  letI := hmeasure
  apply integral_exp_pos
  convert integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2) using 1
  funext u
  congr 1
  ring

private lemma contiguous_joint_weight_factor (p : ℝ×ℝ) :
    Real.exp (-(p.1+p.2)/2)=Real.exp (-p.1/2)*Real.exp (-p.2/2) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma contiguous_joint_weight_integrable (L : ℝ) :
    Integrable (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2))
      ((liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) := by
  have h := (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2)).mul_prod
    (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2))
  convert h using 1
  funext p
  rw [contiguous_joint_weight_factor]
  congr 1 <;> congr 1 <;> ring

theorem liClockPairedEtaContiguousJointWeight_integral (L : ℝ) :
    (∫p:ℝ×ℝ, Real.exp (-(p.1+p.2)/2)
      ∂(liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) =
      liClockPairedEtaContiguousPartitionNormalizer L^2 := by
  simp_rw [contiguous_joint_weight_factor]
  simpa only [liClockPairedEtaContiguousPartitionNormalizer, pow_two] using
    integral_prod_mul (μ:=liClockPairedEtaContiguousLogMeasure L)
      (ν:=liClockPairedEtaContiguousLogMeasure L)
      (fun u:ℝ=>Real.exp (-u/2)) (fun v:ℝ=>Real.exp (-v/2))

theorem liClockPairedEtaContiguousSymmetrizedMeasure_isProbability {L : ℝ} (hL : 0<L) :
    IsProbabilityMeasure (liClockPairedEtaContiguousSymmetrizedMeasure L) := by
  have hn : NeZero ((liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) := by
    constructor
    intro hz
    have hp : 0<(∫p:ℝ×ℝ, Real.exp (-(p.1+p.2)/2)
      ∂(liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) := by
      rw [liClockPairedEtaContiguousJointWeight_integral]
      exact sq_pos_of_pos (liClockPairedEtaContiguousPartitionNormalizer_pos hL)
    rw [hz, integral_zero_measure] at hp
    exact (lt_irrefl _ hp)
  exact isProbabilityMeasure_tilted (contiguous_joint_weight_integrable L)

private lemma contiguous_sym_exp_integrable (L v : ℝ) :
    Integrable (fun p:ℝ×ℝ=>Real.exp (v*(p.1-p.2))) (liClockPairedEtaContiguousSymmetrizedMeasure L) := by
  rw [liClockPairedEtaContiguousSymmetrizedMeasure, integrable_tilted_iff (contiguous_joint_weight_integrable L)]
  have h := (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2-v)).mul_prod
    (integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure L (1/2+v))
  convert h using 1
  funext p
  simp only [smul_eq_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private lemma contiguous_sym_interior (L : ℝ) (z : ℂ) :
    z.re∈interior (integrableExpSet (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure L)) := by
  have hu : integrableExpSet (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure L)=univ := by
    ext v
    simp only [mem_univ, iff_true]
    exact contiguous_sym_exp_integrable L v
  rw [hu, interior_univ]
  trivial

theorem integrable_liClockPairedEtaContiguousSymmetrizedEvenMoment (L : ℝ) (j : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) (liClockPairedEtaContiguousSymmetrizedMeasure L) := by
  have h := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (by simpa only [Complex.zero_re] using contiguous_sym_interior L (0:ℂ)) (2*j)
  simpa only [zero_mul,Real.exp_zero,mul_one] using h

theorem integrable_liClockPairedEtaContiguousRawEvenMoment (L : ℝ) (j : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))
      ((liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) := by
  have h := (integrable_tilted_iff (contiguous_joint_weight_integrable L) _).mp
    (integrable_liClockPairedEtaContiguousSymmetrizedEvenMoment L j)
  simpa only [smul_eq_mul,mul_comm] using h

theorem liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral (L : ℝ) (j : ℕ) :
    liClockPairedEtaContiguousSymmetrizedEvenMoment L j =
      (∫p:ℝ×ℝ, (p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
        ∂(liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) /
        liClockPairedEtaContiguousPartitionNormalizer L^2 := by
  rw [liClockPairedEtaContiguousSymmetrizedEvenMoment,liClockPairedEtaContiguousSymmetrizedMeasure,
    integral_tilted,liClockPairedEtaContiguousJointWeight_integral]
  simp only [smul_eq_mul]
  have heq : (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)/liClockPairedEtaContiguousPartitionNormalizer L^2 *
      (p.1-p.2)^(2*j)) =
    (fun p:ℝ×ℝ=>((p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))/liClockPairedEtaContiguousPartitionNormalizer L^2) := by
    funext p
    ring
  rw [heq,integral_div]

theorem liClockPairedEtaContiguousLogMeasure_support (L : ℝ) :
    ∀ᵐu ∂liClockPairedEtaContiguousLogMeasure L, 0≤u ∧ u≤L := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact ⟨hu.1.le,hu.2⟩

theorem liClockPairedEtaContiguousSymmetrizedMeasure_support (L : ℝ) :
    ∀ᵐp ∂liClockPairedEtaContiguousSymmetrizedMeasure L, |p.1-p.2|≤L := by
  apply Measure.AbsolutelyContinuous.ae_le (tilted_absolutelyContinuous _ _)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [liClockPairedEtaContiguousLogMeasure_support L] with u hu
  filter_upwards [liClockPairedEtaContiguousLogMeasure_support L] with v hv
  rw [abs_le]
  constructor <;> linarith

theorem liClockPairedEtaContiguousSymmetrizedEvenMoment_zero {L : ℝ} (hL : 0<L) :
    liClockPairedEtaContiguousSymmetrizedEvenMoment L 0=1 := by
  letI := liClockPairedEtaContiguousSymmetrizedMeasure_isProbability hL
  simp [liClockPairedEtaContiguousSymmetrizedEvenMoment]

theorem liClockPairedEtaContiguousSymmetrizedEvenMoment_le_power {L : ℝ} (hL : 0<L) (j : ℕ) :
    liClockPairedEtaContiguousSymmetrizedEvenMoment L j≤L^(2*j) := by
  letI := liClockPairedEtaContiguousSymmetrizedMeasure_isProbability hL
  have hle : ∀ᵐp ∂liClockPairedEtaContiguousSymmetrizedMeasure L, (p.1-p.2)^(2*j)≤L^(2*j) := by
    filter_upwards [liClockPairedEtaContiguousSymmetrizedMeasure_support L] with p hp
    calc
      _≤|p.1-p.2|^(2*j) := le_abs_self _ |>.trans_eq (abs_pow _ _)
      _≤_ := pow_le_pow_left₀ (abs_nonneg _) hp _
  have hm := integral_mono_ae (integrable_liClockPairedEtaContiguousSymmetrizedEvenMoment L j)
    (integrable_const _) hle
  simpa only [liClockPairedEtaContiguousSymmetrizedEvenMoment,integral_const,probReal_univ,one_smul] using hm

theorem liClockPairedEtaContiguousSymmetrizedEvenMoment_pos {L : ℝ} (hL : 0<L) (j : ℕ) :
    0<liClockPairedEtaContiguousSymmetrizedEvenMoment L j := by
  let a : Set ℝ := Ioc 0 (L/3)
  let b : Set ℝ := Ioc (2*L/3) L
  let rect : Set (ℝ×ℝ) := a ×ˢ b
  have ha : a⊆Ioc 0 L := by intro x hx; exact ⟨hx.1,hx.2.trans (by linarith)⟩
  have hb : b⊆Ioc 0 L := by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩
  have hfirsta : (liClockPairedEtaContiguousLogMeasure L) a=ENNReal.ofReal (L/3) := by
    rw [liClockPairedEtaContiguousLogMeasure,Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr ha,Real.volume_Ioc]
    simp
  have hfirstb : (liClockPairedEtaContiguousLogMeasure L) b=ENNReal.ofReal (L/3) := by
    rw [liClockPairedEtaContiguousLogMeasure,Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr hb,Real.volume_Ioc]
    congr 1
    ring
  have hrawpos : 0<((liClockPairedEtaContiguousLogMeasure L).prod (liClockPairedEtaContiguousLogMeasure L)) rect := by
    rw [Measure.prod_prod,hfirsta,hfirstb]
    positivity
  have htiltpos : 0<(liClockPairedEtaContiguousSymmetrizedMeasure L) rect := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have hrawzero := absolutelyContinuous_tilted (contiguous_joint_weight_integrable L) hz
    exact hrawpos.ne' hrawzero
  have hsub : rect⊆Function.support (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) := by
    intro p hp
    have huv : p.1<p.2 := by linarith [hp.1.2,hp.2.1]
    exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_lt huv))
  apply (integral_pos_iff_support_of_nonneg (fun p=>by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) j) (integrable_liClockPairedEtaContiguousSymmetrizedEvenMoment L j)).2
  exact htiltpos.trans_le (measure_mono hsub)


theorem liClockPairedEtaContiguousSymmetrizedMeasure_complexMGF_eq_source {L : ℝ}
    (hL : 0≤L) (z : ℂ) :
    complexMGF (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaContiguousSymmetrizedMeasure L) z =
      liClockPairedEtaContiguousPartition L (1/2-z)*liClockPairedEtaContiguousPartition L (1/2+z) /
        (liClockPairedEtaContiguousPartitionNormalizer L:ℂ)^2 := by
  rw [complexMGF,liClockPairedEtaContiguousSymmetrizedMeasure,integral_tilted,
    liClockPairedEtaContiguousJointWeight_integral]
  have heq : (fun p:ℝ×ℝ => (Real.exp (-(p.1+p.2)/2) / liClockPairedEtaContiguousPartitionNormalizer L^2) •
      Complex.exp (z * ((p.1-p.2:ℝ):ℂ))) =
    (fun p:ℝ×ℝ => (Complex.exp (-(1/2-z)*(p.1:ℂ))*Complex.exp (-(1/2+z)*(p.2:ℂ))) /
      ((liClockPairedEtaContiguousPartitionNormalizer L:ℂ)^2)) := by
    funext p
    rw [RCLike.real_smul_eq_coe_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_ofNat,Complex.ofReal_exp]
    rw [div_mul_eq_mul_div]
    congr 1
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    ring
  rw [heq,integral_div]
  congr 1
  rw [liClockPairedEtaContiguousPartition_eq_integral_logMeasure hL,
    liClockPairedEtaContiguousPartition_eq_integral_logMeasure hL]
  exact integral_prod_mul (fun u:ℝ=>Complex.exp (-(1/2-z)*(u:ℂ)))
    (fun v:ℝ=>Complex.exp (-(1/2+z)*(v:ℂ)))

/-- The complete actual eta logarithmic interval union. -/
def liClockPairedEtaPartitionLogSupport (N : ℕ) : Set ℝ :=
  ⋃n∈Finset.range N, Ioc (Real.log (2*(n:ℝ)+1)) (Real.log (2*(n:ℝ)+2))

theorem measurableSet_liClockPairedEtaPartitionLogSupport (N : ℕ) :
    MeasurableSet (liClockPairedEtaPartitionLogSupport N) := by
  unfold liClockPairedEtaPartitionLogSupport
  measurability

theorem liClockPairedEtaPartitionLogIntervals_pairwiseDisjoint :
    Pairwise (fun n m:ℕ=>Disjoint
      (Ioc (Real.log (2*(n:ℝ)+1)) (Real.log (2*(n:ℝ)+2)))
      (Ioc (Real.log (2*(m:ℝ)+1)) (Real.log (2*(m:ℝ)+2)))) := by
  intro n m hnm
  have hle {n m:ℕ} (hnm : n < m) : Real.log (2*(n:ℝ)+2)≤Real.log (2*(m:ℝ)+1) := by
    apply Real.log_le_log (by positivity)
    have hn : (n:ℝ)+1≤(m:ℝ) := by exact_mod_cast (show n+1 ≤ m by omega)
    linarith
  rcases lt_or_gt_of_ne hnm with h | h
  · exact Ioc_disjoint_Ioc_of_le (hle h)
  · exact (Ioc_disjoint_Ioc_of_le (hle h)).symm

theorem liClockPairedEtaPartitionLogSupport_subset_Ioc (N : ℕ) :
    liClockPairedEtaPartitionLogSupport N⊆Ioc 0 (Real.log (2*(N:ℝ))) := by
  intro u hu
  simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion] at hu
  obtain ⟨n,hn,hu⟩ := hu
  have hlo : 0≤Real.log (2*(n:ℝ)+1) := Real.log_nonneg (by linarith [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n])
  have hhi : Real.log (2*(n:ℝ)+2)≤Real.log (2*(N:ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show 2*n+2≤2*N by have := Finset.mem_range.mp hn; omega)
  exact ⟨hlo.trans_lt hu.1,hu.2.trans hhi⟩

theorem pairedEtaFiniteLogMeasure_eq_restrict_union (N : ℕ) :
    pairedEtaFiniteLogMeasure N=volume.restrict (liClockPairedEtaPartitionLogSupport N) := by
  unfold pairedEtaFiniteLogMeasure liClockPairedEtaPartitionLogSupport
  rw [Measure.restrict_biUnion_finset
    (fun _ _ _ _ h=>liClockPairedEtaPartitionLogIntervals_pairwiseDisjoint h)
    (fun _=>measurableSet_Ioc),Measure.sum_fintype]
  exact (Finset.sum_coe_sort (Finset.range N) (fun n:ℕ=>volume.restrict
    (Ioc (Real.log (2*(n:ℝ)+1)) (Real.log (2*(n:ℝ)+2))))).symm

theorem pairedEtaFiniteLogMeasure_le_contiguous (N : ℕ) :
    pairedEtaFiniteLogMeasure N≤liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ))) := by
  rw [pairedEtaFiniteLogMeasure_eq_restrict_union]
  exact Measure.restrict_mono_set volume (liClockPairedEtaPartitionLogSupport_subset_Ioc N)

theorem pairedEtaFiniteLogMeasure_prod_le_contiguous (N : ℕ) :
    (pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)≤
      (liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ)))).prod
        (liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ)))) :=
  Measure.prod_mono (pairedEtaFiniteLogMeasure_le_contiguous N) (pairedEtaFiniteLogMeasure_le_contiguous N)

theorem liClockPairedEtaPartitionNormalizer_le_contiguous (N : ℕ) :
    liClockPairedEtaPartitionNormalizer N≤
      liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ))) := by
  exact integral_mono_measure (pairedEtaFiniteLogMeasure_le_contiguous N)
    (Eventually.of_forall fun u=> (Real.exp_pos _).le)
    (by convert integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ))) (1/2) using 1
        funext u; congr 1; ring)

theorem liClockPairedEtaRawEvenMoment_le_contiguous (N j : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
      ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N))≤
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
      ∂(liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ)))).prod
        (liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ))))) := by
  exact integral_mono_measure (pairedEtaFiniteLogMeasure_prod_le_contiguous N)
    (Eventually.of_forall fun p=> mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) j)
      (Real.exp_pos _).le)
    (integrable_liClockPairedEtaContiguousRawEvenMoment _ j)

theorem liClockPairedEtaSymmetrizedEvenMoment_le_contiguous {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaSymmetrizedEvenMoment N j≤
      (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ))) /
        liClockPairedEtaPartitionNormalizer N)^2 *
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) j := by
  have hL : 0<Real.log (2*(N:ℝ)) := Real.log_pos (by
    have hcast : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    linarith)
  have hZA := liClockPairedEtaPartitionNormalizer_pos hN
  have hZU := liClockPairedEtaContiguousPartitionNormalizer_pos hL
  rw [liClockPairedEtaSymmetrizedEvenMoment_eq_double_integral,
    liClockPairedEtaContiguousSymmetrizedEvenMoment_eq_double_integral]
  have hraw := liClockPairedEtaRawEvenMoment_le_contiguous N j
  have hZA0 : liClockPairedEtaPartitionNormalizer N≠0 := hZA.ne'
  have hZU0 : liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))≠0 := hZU.ne'
  have heq : (liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ))) /
      liClockPairedEtaPartitionNormalizer N)^2 *
      ((∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
        ∂(liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ)))).prod
          (liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ))))) /
        liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ)))^2) =
      (∫p:ℝ×ℝ,(p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
        ∂(liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ)))).prod
          (liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ))))) /
        liClockPairedEtaPartitionNormalizer N^2 := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hraw (sq_nonneg _)


theorem liClockPairedEtaContiguousBorelCoefficient_pos {L : ℝ} (hL : 0<L) (j : ℕ) :
    0<liClockPairedEtaContiguousBorelCoefficient L j :=
  div_pos (liClockPairedEtaContiguousSymmetrizedEvenMoment_pos hL j) (by positivity)

theorem liClockPairedEtaContiguousBorelCoefficient_le {L : ℝ} (hL : 0<L) (j : ℕ) :
    liClockPairedEtaContiguousBorelCoefficient L j≤(L^2)^j/(j.factorial:ℝ) := by
  have hf : (j.factorial:ℝ)≤((2*j).factorial:ℝ)^2 := by
    have h1 : (j.factorial:ℝ)≤((2*j).factorial:ℝ) := by
      exact_mod_cast Nat.factorial_le (show j≤2*j by omega)
    have h2 : (1:ℝ)≤((2*j).factorial:ℝ) := by
      exact_mod_cast Nat.factorial_le (Nat.zero_le (2*j))
    nlinarith
  unfold liClockPairedEtaContiguousBorelCoefficient
  calc
    _≤L^(2*j)/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right (liClockPairedEtaContiguousSymmetrizedEvenMoment_le_power hL j) (sq_nonneg _)
    _≤L^(2*j)/(j.factorial:ℝ) :=
      div_le_div_of_nonneg_left (by rw [pow_mul]; positivity) (by positivity) hf
    _=_ := by rw [pow_mul]

private theorem contiguous_borelTerm_norm_le {L T : ℝ} (hL : 0<L)
    {z : ℂ} (hz : ‖z‖≤T) (j : ℕ) :
    ‖(liClockPairedEtaContiguousBorelCoefficient L j:ℂ)*z^(2*j)‖≤
      (L^2*T^2)^j/(j.factorial:ℝ) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (liClockPairedEtaContiguousBorelCoefficient_pos hL j),norm_pow]
  calc
    _≤((L^2)^j/(j.factorial:ℝ))*T^(2*j) :=
      mul_le_mul (liClockPairedEtaContiguousBorelCoefficient_le hL j)
        (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _=_ := by rw [mul_pow,← pow_mul]; ring

theorem summable_norm_liClockPairedEtaContiguousBorelTermComplex {L : ℝ} (hL : 0<L) (z : ℂ) :
    Summable (fun j=>‖(liClockPairedEtaContiguousBorelCoefficient L j:ℂ)*z^(2*j)‖) :=
  (Real.summable_pow_div_factorial (L^2*‖z‖^2)).of_nonneg_of_le
    (fun _=>norm_nonneg _) (contiguous_borelTerm_norm_le hL (le_refl ‖z‖))

theorem summable_liClockPairedEtaContiguousBorelTerm {L : ℝ} (hL : 0<L) (t : ℝ) :
    Summable (fun j=>liClockPairedEtaContiguousBorelCoefficient L j*t^(2*j)) := by
  have h := (summable_norm_liClockPairedEtaContiguousBorelTermComplex hL (t:ℂ)).of_norm
  have hr := (Complex.hasSum_re h.hasSum).summable
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using hr

theorem hasSumUniformlyOn_liClockPairedEtaContiguousBorelTermComplex {L T : ℝ}
    (hL : 0<L) (_hT : 0≤T) :
    HasSumUniformlyOn (fun j (z:ℂ)=>(liClockPairedEtaContiguousBorelCoefficient L j:ℂ)*z^(2*j))
      (liClockPairedEtaContiguousBorelKernelComplex L) (closedBall 0 T) := by
  exact HasSumUniformlyOn.of_norm_le_summable
    (Real.summable_pow_div_factorial (L^2*T^2))
    (fun j z hz=>contiguous_borelTerm_norm_le hL
      (by simpa only [mem_closedBall,dist_zero_right] using hz) j)

theorem liClockPairedEtaContiguousBorelKernelComplex_ofReal {L : ℝ} (_hL : 0<L) (t : ℝ) :
    liClockPairedEtaContiguousBorelKernelComplex L (t:ℂ)=
      (liClockPairedEtaContiguousBorelKernel L t:ℂ) := by
  unfold liClockPairedEtaContiguousBorelKernelComplex liClockPairedEtaContiguousBorelKernel
  simp_rw [← Complex.ofReal_pow,← Complex.ofReal_mul]
  exact (Complex.ofReal_tsum _).symm

theorem liClockPairedEtaContiguousBorelKernel_eq_tsum (L t : ℝ) :
    liClockPairedEtaContiguousBorelKernel L t=∑'j,
      liClockPairedEtaContiguousSymmetrizedEvenMoment L j*t^(2*j)/((2*j).factorial:ℝ)^2 := by
  apply tsum_congr
  intro j
  unfold liClockPairedEtaContiguousBorelCoefficient
  ring

theorem liClockPairedEtaContiguousBorelKernel_ge_one {L : ℝ} (hL : 0<L) (t : ℝ) :
    1≤liClockPairedEtaContiguousBorelKernel L t := by
  have h := (summable_liClockPairedEtaContiguousBorelTerm hL t).le_tsum 0 (fun j _=>by
    rw [pow_mul]
    exact mul_nonneg (liClockPairedEtaContiguousBorelCoefficient_pos hL j).le (pow_nonneg (sq_nonneg t) j))
  simpa [liClockPairedEtaContiguousBorelCoefficient,liClockPairedEtaContiguousSymmetrizedEvenMoment_zero hL,
    liClockPairedEtaContiguousBorelKernel] using h

theorem liClockPairedEtaContiguousBorelKernel_pos {L : ℝ} (hL : 0<L) (t : ℝ) :
    0<liClockPairedEtaContiguousBorelKernel L t :=
  lt_of_lt_of_le zero_lt_one (liClockPairedEtaContiguousBorelKernel_ge_one hL t)


theorem summableLocallyUniformlyOn_liClockPairedEtaContiguousBorelTermComplex {L : ℝ}
    (hL : 0<L) :
    SummableLocallyUniformlyOn (fun j (z:ℂ)=>(liClockPairedEtaContiguousBorelCoefficient L j:ℂ)*z^(2*j)) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K hK hKc
  obtain ⟨C,hC⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  let T : ℝ := max C 0
  refine ⟨_,Real.summable_pow_div_factorial (L^2*T^2),?_⟩
  intro j z hz
  exact contiguous_borelTerm_norm_le hL ((hC ⟨z,hz,rfl⟩).trans (le_max_left _ _)) j

theorem pairedEtaFiniteLogMeasure_one_eq_contiguous :
    pairedEtaFiniteLogMeasure 1=liClockPairedEtaContiguousLogMeasure (Real.log 2) := by
  simp [pairedEtaFiniteLogMeasure,liClockPairedEtaContiguousLogMeasure]

theorem liClockPairedEtaPartitionNormalizer_one_eq_contiguous :
    liClockPairedEtaPartitionNormalizer 1=liClockPairedEtaContiguousPartitionNormalizer (Real.log 2) := by
  rw [liClockPairedEtaPartitionNormalizer,liClockPairedEtaContiguousPartitionNormalizer,
    pairedEtaFiniteLogMeasure_one_eq_contiguous]

theorem liClockPairedEtaSymmetrizedMeasure_one_eq_contiguous :
    liClockPairedEtaSymmetrizedMeasure 1=liClockPairedEtaContiguousSymmetrizedMeasure (Real.log 2) := by
  rw [liClockPairedEtaSymmetrizedMeasure,liClockPairedEtaContiguousSymmetrizedMeasure,
    pairedEtaFiniteLogMeasure_one_eq_contiguous]

theorem liClockPairedEtaSymmetrizedEvenMoment_one_eq_contiguous (j : ℕ) :
    liClockPairedEtaSymmetrizedEvenMoment 1 j=
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log 2) j := by
  rw [liClockPairedEtaSymmetrizedEvenMoment,liClockPairedEtaContiguousSymmetrizedEvenMoment,
    liClockPairedEtaSymmetrizedMeasure_one_eq_contiguous]

theorem liClockPairedEtaBorelKernel_one_eq_contiguous (t : ℝ) :
    liClockPairedEtaPartitionBorelKernel 1 t=liClockPairedEtaContiguousBorelKernel (Real.log 2) t := by
  rw [liClockPairedEtaPartitionBorelKernel_eq_tsum,liClockPairedEtaContiguousBorelKernel_eq_tsum]
  simp_rw [liClockPairedEtaSymmetrizedEvenMoment_one_eq_contiguous]

private theorem contiguous_missingGap_disjoint (N : ℕ) :
    Disjoint (liClockPairedEtaPartitionLogSupport N) (Ioc (Real.log 2) (Real.log 3)) := by
  apply disjoint_left.mpr
  intro u hu hg
  simp only [liClockPairedEtaPartitionLogSupport,mem_iUnion] at hu
  obtain ⟨n,hn,hu⟩ := hu
  by_cases hn0 : n=0
  · subst n
    simp only [Nat.cast_zero,mul_zero,zero_add,Real.log_one] at hu
    linarith [hu.2,hg.1]
  · have hn1 : (1:ℝ)≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
    have hl : Real.log 3≤Real.log (2*(n:ℝ)+1) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [hu.1,hg.2]

private theorem contiguous_missingGap_integral_pos :
    0<(∫u:ℝ,Real.exp (-u/2) ∂volume.restrict (Ioc (Real.log 2) (Real.log 3))) := by
  have hab : Real.log 2<Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hm : NeZero (volume.restrict (Ioc (Real.log 2) (Real.log 3)):Measure ℝ) := by
    constructor
    intro hz
    have hu := congrArg (fun m:Measure ℝ=>m univ) hz
    simp only [Measure.restrict_apply_univ,Real.volume_Ioc,Measure.coe_zero,Pi.zero_apply] at hu
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hu
  letI := hm
  exact integral_exp_pos (((show Continuous (fun u:ℝ=>Real.exp (-u/2)) by fun_prop).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)

theorem liClockPairedEtaPartitionNormalizer_lt_contiguous {N : ℕ} (hN : 2≤N) :
    liClockPairedEtaPartitionNormalizer N<
      liClockPairedEtaContiguousPartitionNormalizer (Real.log (2*(N:ℝ))) := by
  let gap : Set ℝ := Ioc (Real.log 2) (Real.log 3)
  have hgap : gap⊆Ioc 0 (Real.log (2*(N:ℝ))) := by
    intro u hu
    have hlo : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hn2 : (2:ℝ)≤(N:ℝ) := by exact_mod_cast hN
    have hhi : Real.log 3≤Real.log (2*(N:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    exact ⟨hlo.trans hu.1,hu.2.trans hhi⟩
  have hmeas : pairedEtaFiniteLogMeasure N+volume.restrict gap≤
      liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ))) := by
    rw [pairedEtaFiniteLogMeasure_eq_restrict_union,← Measure.restrict_union
      (contiguous_missingGap_disjoint N) measurableSet_Ioc]
    exact Measure.restrict_mono_set volume (union_subset (liClockPairedEtaPartitionLogSupport_subset_Ioc N) hgap)
  have hU : Integrable (fun u:ℝ=>Real.exp (-u/2))
      (liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ)))) := by
    convert integrable_rexp_neg_mul_liClockPairedEtaContiguousLogMeasure (Real.log (2*(N:ℝ))) (1/2) using 1
    funext u
    congr 1
    ring
  have hA : Integrable (fun u:ℝ=>Real.exp (-u/2)) (pairedEtaFiniteLogMeasure N) := by
    convert integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure N (1/2) using 1
    funext u
    congr 1
    ring
  have hg : Integrable (fun u:ℝ=>Real.exp (-u/2)) (volume.restrict gap) :=
    ((show Continuous (fun u:ℝ=>Real.exp (-u/2)) by fun_prop).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hle := integral_mono_measure hmeas (Eventually.of_forall fun u=>(Real.exp_pos _).le) hU
  rw [integral_add_measure hA hg] at hle
  exact lt_of_lt_of_le (lt_add_of_pos_right _ contiguous_missingGap_integral_pos) hle


theorem continuous_liClockPairedEtaContiguousBorelKernelComplex {L : ℝ} (hL : 0<L) :
    Continuous (liClockPairedEtaContiguousBorelKernelComplex L) := by
  apply continuousOn_univ.mp
  exact (summableLocallyUniformlyOn_liClockPairedEtaContiguousBorelTermComplex hL).hasSumLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange.continuousOn
    (Frequently.of_forall fun n=>by
      exact (continuous_finsetSum _ (fun j _=>continuous_const.mul (continuous_id.pow (2*j)))).continuousOn)

theorem continuous_liClockPairedEtaContiguousBorelKernel {L : ℝ} (hL : 0<L) :
    Continuous (liClockPairedEtaContiguousBorelKernel L) := by
  have heq : liClockPairedEtaContiguousBorelKernel L=
      fun t:ℝ=>(liClockPairedEtaContiguousBorelKernelComplex L (t:ℂ)).re := by
    funext t
    rw [liClockPairedEtaContiguousBorelKernelComplex_ofReal hL,Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp ((continuous_liClockPairedEtaContiguousBorelKernelComplex hL).comp Complex.continuous_ofReal)

theorem liClockPairedEtaContiguousBorelKernel_mono {L a b : ℝ} (hL : 0<L)
    (ha : 0≤a) (hab : a≤b) :
    liClockPairedEtaContiguousBorelKernel L a≤liClockPairedEtaContiguousBorelKernel L b := by
  exact (summable_liClockPairedEtaContiguousBorelTerm hL a).tsum_le_tsum
    (fun j=>mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _)
      (liClockPairedEtaContiguousBorelCoefficient_pos hL j).le)
    (summable_liClockPairedEtaContiguousBorelTerm hL b)

theorem liClockPairedEtaContiguousPartitionNormalizer_eq {L : ℝ} (hL : 0≤L) :
    liClockPairedEtaContiguousPartitionNormalizer L=2*(1-Real.exp (-L/2)) := by
  have h := liClockPairedEtaContiguousPartition_eq_div (L:=L) (s:=(1/2:ℂ)) (by norm_num)
  rw [liClockPairedEtaContiguousPartition_half_eq_normalizer hL] at h
  have he : -(L:ℂ)*(1/2:ℂ)=((-L/2:ℝ):ℂ) := by push_cast; ring
  rw [he,← Complex.ofReal_exp] at h
  apply Complex.ofReal_injective
  calc
    (liClockPairedEtaContiguousPartitionNormalizer L:ℂ) =
      (1-(Real.exp (-L/2):ℂ))/(1/2:ℂ) := h
    _ = ((2*(1-Real.exp (-L/2)):ℝ):ℂ) := by push_cast; ring

end
end RHTower
