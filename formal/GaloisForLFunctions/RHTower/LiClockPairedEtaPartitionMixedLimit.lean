import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionMixedSource
import GaloisForLFunctions.RHTower.LiClockPairedEtaInfinitePartitionBorel
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas


/-!
# Complete mixed-partition source and derivative limits

The actual infinite arithmetic partition is paired with the half-line reference
partition. Full binomial moments retain both marginal normalizers. Factorial
bounds admit the entire mixed Borel series and its literal source integral;
holomorphic local uniform convergence gives every fixed derivative limit.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Complex Metric
open scoped BigOperators ENNReal
noncomputable section
namespace RHTower

/- Product of the actual infinite symmetrized arithmetic measure and the half-line reference measure. -/
def liClockPairedEtaInfinitePartitionMixedMeasure :
    Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  liClockPairedEtaInfiniteSymmetrizedMeasure.prod
    liClockPairedEtaHalfLineSymmetrizedMeasure

/- Complete even moment of the sum of the two coordinate differences. -/
def liClockPairedEtaInfinitePartitionMixedEvenMoment (j : ℕ) : ℝ :=
  ∫ p : (ℝ × ℝ) × (ℝ × ℝ),
    ((p.1.1-p.1.2)+(p.2.1-p.2.2))^(2*j)
    ∂liClockPairedEtaInfinitePartitionMixedMeasure

/- Complex extension of the literal finite mixed Borel kernel. -/
def liClockPairedEtaPartitionMixedBorelKernelComplex (N : ℕ) (z : ℂ) : ℂ :=
  ∑' j : ℕ, (liClockPairedEtaPartitionMixedEvenMoment N j : ℂ)*z^(2*j)/
    ((2*j).factorial : ℂ)^2

/- Entire Borel series of the complete infinite mixed moments. -/
def liClockPairedEtaInfinitePartitionMixedBorelKernelComplex (z : ℂ) : ℂ :=
  ∑' j : ℕ, (liClockPairedEtaInfinitePartitionMixedEvenMoment j : ℂ)*z^(2*j)/
    ((2*j).factorial : ℂ)^2

/- Real Borel series of the complete infinite mixed moments. -/
def liClockPairedEtaInfinitePartitionMixedBorelKernel (t : ℝ) : ℝ :=
  ∑' j : ℕ, liClockPairedEtaInfinitePartitionMixedEvenMoment j*t^(2*j)/
    ((2*j).factorial : ℝ)^2

/- Normalized actual even moment divided by the half-line reference even moment. -/
def liClockPairedEtaInfinitePartitionMomentRatio (j : ℕ) : ℝ :=
  liClockPairedEtaInfiniteSymmetrizedEvenMoment j /
    liClockPairedEtaHalfLineSymmetrizedEvenMoment j

/- Complete finite prefix of the normalized marginal moment ratios. -/
def liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix (j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (j+1), liClockPairedEtaInfinitePartitionMomentRatio a

private abbrev mlX (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℝ := p.1.1-p.1.2
private abbrev mlY (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℝ := p.2.1-p.2.2
private abbrev mlW (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℝ := mlX p+mlY p

/- Both marginal normalizations are retained in the mixed probability measure. -/
theorem liClockPairedEtaInfinitePartitionMixedMeasure_isProbability :
    IsProbabilityMeasure liClockPairedEtaInfinitePartitionMixedMeasure := by
  letI := liClockPairedEtaInfiniteSymmetrizedMeasure_isProbability
  letI := liClockPairedEtaHalfLineSymmetrizedMeasure_isProbability
  unfold liClockPairedEtaInfinitePartitionMixedMeasure
  infer_instance

private theorem ml_actual_power_integrable (n : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^n) liClockPairedEtaInfiniteSymmetrizedMeasure := by
  have hc : Integrable (fun p:ℝ×ℝ=>((p.1-p.2:ℝ):ℂ)^n) liClockPairedEtaInfiniteSymmetrizedMeasure := by
    simpa only [zero_mul,Complex.exp_zero,mul_one] using
      integrable_liClockPairedEtaInfiniteSymmetrizedComplexMoment (z:=0) (by norm_num) n
  have h := Complex.reCLM.integrable_comp hc
  simpa only [Complex.reCLM_apply,←Complex.ofReal_pow,Complex.ofReal_re] using h

private theorem ml_reference_power_integrable (n : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^n) liClockPairedEtaHalfLineSymmetrizedMeasure := by
  have hc : Integrable (fun p:ℝ×ℝ=>((p.1-p.2:ℝ):ℂ)^n) liClockPairedEtaHalfLineSymmetrizedMeasure := by
    simpa only [zero_mul,Complex.exp_zero,mul_one] using
      integrable_liClockPairedEtaHalfLineSymmetrizedComplexMoment (z:=0) (by norm_num) n
  have h := Complex.reCLM.integrable_comp hc
  simpa only [Complex.reCLM_apply,←Complex.ofReal_pow,Complex.ofReal_re] using h

private theorem ml_monomial_integrable (p q : ℕ) :
    Integrable (fun z:(ℝ×ℝ)×(ℝ×ℝ)=>mlX z^p*mlY z^q)
      liClockPairedEtaInfinitePartitionMixedMeasure :=
  (ml_actual_power_integrable p).mul_prod (ml_reference_power_integrable q)

private theorem ml_mixed_monomial_integral (p q : ℕ) :
    (∫z:(ℝ×ℝ)×(ℝ×ℝ),mlX z^p*mlY z^q
      ∂liClockPairedEtaInfinitePartitionMixedMeasure) =
    (∫u:ℝ×ℝ,(u.1-u.2)^p∂liClockPairedEtaInfiniteSymmetrizedMeasure)*
    (∫v:ℝ×ℝ,(v.1-v.2)^q∂liClockPairedEtaHalfLineSymmetrizedMeasure) := by
  letI := liClockPairedEtaInfiniteSymmetrizedMeasure_isProbability
  letI := liClockPairedEtaHalfLineSymmetrizedMeasure_isProbability
  unfold liClockPairedEtaInfinitePartitionMixedMeasure
  exact integral_prod_mul (fun u:ℝ×ℝ=>(u.1-u.2)^p)
    (fun v:ℝ×ℝ=>(v.1-v.2)^q)

private theorem ml_power_integrable (m : ℕ) :
    Integrable (fun z:(ℝ×ℝ)×(ℝ×ℝ)=>mlW z^m)
      liClockPairedEtaInfinitePartitionMixedMeasure := by
  have hpoly (z:(ℝ×ℝ)×(ℝ×ℝ)) : mlW z^m=
      ∑k∈Finset.range (m+1),(m.choose k:ℝ)*(mlX z^k*mlY z^(m-k)) := by
    dsimp [mlW]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hpoly]
  exact integrable_finsetSum _ (fun k hk => (ml_monomial_integrable k (m-k)).const_mul _)

/- Every complete mixed even power is genuinely integrable. -/
theorem integrable_liClockPairedEtaInfinitePartitionMixedEvenMoment (j : ℕ) :
    Integrable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      ((p.1.1-p.1.2)+(p.2.1-p.2.2))^(2*j))
      liClockPairedEtaInfinitePartitionMixedMeasure := ml_power_integrable (2*j)

private theorem ml_even_density_neg_map (g : ℝ→ℝ) (hg : Measurable g)
    (he : ∀x, g (-x)=g x) :
    Measure.map (fun x:ℝ=>-x)
      (volume.withDensity (fun x=>ENNReal.ofReal (g x))) =
      volume.withDensity (fun x=>ENNReal.ofReal (g x)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ (by fun_prop)]
  have hφneg : Measurable (fun x:ℝ=>φ (-x)) := hφ.comp measurable_neg
  rw [lintegral_withDensity_eq_lintegral_mul _ hg.ennreal_ofReal hφneg,
    lintegral_withDensity_eq_lintegral_mul _ hg.ennreal_ofReal hφ]
  have hn := (Measure.measurePreserving_neg (volume:Measure ℝ)).lintegral_comp
    (f:=fun x:ℝ=>ENNReal.ofReal (g x)*φ x) (by fun_prop)
  simp only [Pi.mul_apply]
  rw [←hn]
  apply lintegral_congr
  intro x
  exact congrArg (fun a:ℝ=>ENNReal.ofReal a*φ (-x)) (he x).symm

private theorem ml_odd_from_even_density (μ : Measure (ℝ×ℝ)) (g : ℝ→ℝ)
    (hg : Measurable g) (he : ∀x, g (-x)=g x)
    (hmap : Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ=
      volume.withDensity (fun x=>ENNReal.ofReal (g x))) (j : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)∂μ)=0 := by
  let ν := Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ
  have hn : Measure.map (fun x:ℝ=>-x) ν=ν := by
    change Measure.map (fun x:ℝ=>-x) (Measure.map _ μ)=Measure.map _ μ
    rw [hmap]
    exact ml_even_density_neg_map g hg he
  have hi : (∫x:ℝ,x^(2*j+1)∂ν)=(∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)∂μ) :=
    integral_map (by fun_prop) (by fun_prop)
  have hneg : (∫x:ℝ,(-x)^(2*j+1)∂ν)=(∫x:ℝ,x^(2*j+1)∂ν) := by
    have h := integral_map (μ:=ν) (φ:=fun x:ℝ=>-x) (f:=fun x:ℝ=>x^(2*j+1))
      (by fun_prop) (by fun_prop)
    rw [hn] at h
    exact h.symm
  have hp (x : ℝ) : (-x)^(2*j+1)=-(x^(2*j+1)) := by
    rw [neg_pow,pow_add,pow_mul]
    norm_num
  simp_rw [hp] at hneg
  rw [integral_neg] at hneg
  linarith

private theorem ml_actual_odd_moment (j : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)∂liClockPairedEtaInfiniteSymmetrizedMeasure)=0 := by
  apply ml_odd_from_even_density _ liClockPairedEtaInfinitePartitionDifferenceDensity
    (measurable_liClockPairedEtaInfinitePartitionRawDifferenceDensity.div_const _) _
    liClockPairedEtaInfinitePartitionDifferenceDensity_map
  intro x
  dsimp [liClockPairedEtaInfinitePartitionDifferenceDensity]
  rw [liClockPairedEtaInfinitePartitionRawDifferenceDensity_even]

private theorem ml_reference_odd_moment (j : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)∂liClockPairedEtaHalfLineSymmetrizedMeasure)=0 := by
  apply ml_odd_from_even_density _ liClockPairedEtaHalfLineDifferenceDensity
    (measurable_liClockPairedEtaHalfLineRawDifferenceDensity.div_const _) _
    liClockPairedEtaHalfLineDifferenceDensity_map
  intro x
  dsimp [liClockPairedEtaHalfLineDifferenceDensity]
  rw [liClockPairedEtaHalfLineRawDifferenceDensity_even]

private theorem ml_even_index_sum (n : ℕ) (f : ℕ→ℝ)
    (hodd : ∀k∈Finset.range (2*n+1), Odd k→f k=0) :
    (∑k∈Finset.range (2*n+1),f k)=∑a∈Finset.range (n+1),f (2*a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 2*(n+1)+1=(2*n+1)+1+1 := by omega
    rw [hp,Finset.sum_range_succ,Finset.sum_range_succ]
    have ho : f (2*n+1)=0 := hodd _ (Finset.mem_range.mpr (by omega)) ⟨n,by omega⟩
    have hi := ih (by
      intro k hk ho
      exact hodd k (Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)) ho)
    rw [hi,ho,add_zero]
    rw [Finset.sum_range_succ (n:=n+1)]
    have he : (2*n+1)+1=2*(n+1) := by omega
    simp only [he]

private theorem ml_mixed_power_integral (m : ℕ) :
    (∫z:(ℝ×ℝ)×(ℝ×ℝ),mlW z^m∂liClockPairedEtaInfinitePartitionMixedMeasure)=
      ∑k∈Finset.range (m+1),(m.choose k:ℝ)*
        (∫u:ℝ×ℝ,(u.1-u.2)^k∂liClockPairedEtaInfiniteSymmetrizedMeasure)*
        (∫v:ℝ×ℝ,(v.1-v.2)^(m-k)
          ∂liClockPairedEtaHalfLineSymmetrizedMeasure) := by
  have hpoly (z:(ℝ×ℝ)×(ℝ×ℝ)) : mlW z^m=
      ∑k∈Finset.range (m+1),(m.choose k:ℝ)*(mlX z^k*mlY z^(m-k)) := by
    dsimp [mlW]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hpoly]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul,ml_mixed_monomial_integral]
    ring
  · intro k hk
    exact (ml_monomial_integrable k (m-k)).const_mul _

private theorem ml_marginal_odd_zero (k : ℕ) (hk : Odd k) :
    (∫u:ℝ×ℝ,(u.1-u.2)^k∂liClockPairedEtaInfiniteSymmetrizedMeasure)=0 := by
  obtain ⟨r,hr⟩ := hk
  have he : k=2*r+1 := by omega
  rw [he]
  exact ml_actual_odd_moment r

/- Full binomial identity after both odd marginal moment families vanish. -/
theorem liClockPairedEtaInfinitePartitionMixedEvenMoment_eq_sum (j : ℕ) :
    liClockPairedEtaInfinitePartitionMixedEvenMoment j =
      ∑a∈Finset.range (j+1), (Nat.choose (2*j) (2*a):ℝ)*
        liClockPairedEtaInfiniteSymmetrizedEvenMoment a*
        liClockPairedEtaHalfLineSymmetrizedEvenMoment (j-a) := by
  change (∫z:(ℝ×ℝ)×(ℝ×ℝ),mlW z^(2*j)
    ∂liClockPairedEtaInfinitePartitionMixedMeasure)=_
  rw [ml_mixed_power_integral]
  rw [ml_even_index_sum j _ (by
    intro k hk ho
    rw [ml_marginal_odd_zero k ho]
    ring)]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  have he : 2*j-2*a=2*(j-a) := by omega
  simp only [he,liClockPairedEtaInfiniteSymmetrizedEvenMoment,
    liClockPairedEtaHalfLineSymmetrizedEvenMoment]


private abbrev mlRawMeasure : Measure ((ℝ×ℝ)×(ℝ×ℝ)) :=
  (RiemannGaussian.pairedEtaLogMeasure.prod RiemannGaussian.pairedEtaLogMeasure).prod
    (liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure)

private theorem ml_actual_raw_power_integrable (n : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^n*Real.exp (-(p.1+p.2)/2))
      (RiemannGaussian.pairedEtaLogMeasure.prod RiemannGaussian.pairedEtaLogMeasure) := by
  have h := (integrable_tilted_iff integrable_liClockPairedEtaInfiniteJointWeight _).mp
    (ml_actual_power_integrable n)
  simpa only [smul_eq_mul,mul_comm] using h

private theorem ml_reference_raw_power_integrable (n : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^n*Real.exp (-(p.1+p.2)/2))
      (liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure) := by
  have h := (integrable_tilted_iff integrable_liClockPairedEtaHalfLineJointWeight _).mp
    (ml_reference_power_integrable n)
  simpa only [smul_eq_mul,mul_comm] using h

private theorem ml_actual_power_normalization (n : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^n∂liClockPairedEtaInfiniteSymmetrizedMeasure)=
      (∫p:ℝ×ℝ,(p.1-p.2)^n*Real.exp (-(p.1+p.2)/2)
        ∂(RiemannGaussian.pairedEtaLogMeasure.prod RiemannGaussian.pairedEtaLogMeasure))/
      liClockPairedEtaInfinitePartitionNormalizer^2 := by
  rw [liClockPairedEtaInfiniteSymmetrizedMeasure,integral_tilted,
    liClockPairedEtaInfiniteJointWeight_integral]
  simp only [smul_eq_mul]
  have he : (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)/
      liClockPairedEtaInfinitePartitionNormalizer^2*(p.1-p.2)^n)=
      (fun p:ℝ×ℝ=>((p.1-p.2)^n*Real.exp (-(p.1+p.2)/2))/
        liClockPairedEtaInfinitePartitionNormalizer^2) := by funext p; ring
  rw [he,integral_div]

private theorem ml_reference_power_normalization (n : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^n∂liClockPairedEtaHalfLineSymmetrizedMeasure)=
      (∫p:ℝ×ℝ,(p.1-p.2)^n*Real.exp (-(p.1+p.2)/2)
        ∂liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure)/
      liClockPairedEtaHalfLinePartitionNormalizer^2 := by
  rw [liClockPairedEtaHalfLineSymmetrizedMeasure,integral_tilted,
    liClockPairedEtaHalfLineJointWeight_integral]
  simp only [smul_eq_mul]
  have he : (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)/
      liClockPairedEtaHalfLinePartitionNormalizer^2*(p.1-p.2)^n)=
      (fun p:ℝ×ℝ=>((p.1-p.2)^n*Real.exp (-(p.1+p.2)/2))/
        liClockPairedEtaHalfLinePartitionNormalizer^2) := by funext p; ring
  rw [he,integral_div]

private theorem ml_raw_polynomial (m : ℕ) (p : (ℝ×ℝ)×(ℝ×ℝ)) :
    mlW p^m*Real.exp (-(p.1.1+p.1.2+p.2.1+p.2.2)/2)=
      ∑k∈Finset.range (m+1),(m.choose k:ℝ)*
        ((p.1.1-p.1.2)^k*Real.exp (-(p.1.1+p.1.2)/2))*
        ((p.2.1-p.2.2)^(m-k)*Real.exp (-(p.2.1+p.2.2)/2)) := by
  have he : Real.exp (-(p.1.1+p.1.2+p.2.1+p.2.2)/2)=
      Real.exp (-(p.1.1+p.1.2)/2)*Real.exp (-(p.2.1+p.2.2)/2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he]
  dsimp [mlW,mlX,mlY]
  rw [add_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem ml_raw_power_integrable (m : ℕ) :
    Integrable (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>mlW p^m*
      Real.exp (-(p.1.1+p.1.2+p.2.1+p.2.2)/2)) mlRawMeasure := by
  simp_rw [ml_raw_polynomial]
  apply integrable_finsetSum
  intro k hk
  have hi := ((ml_actual_raw_power_integrable k).mul_prod
    (ml_reference_raw_power_integrable (m-k))).const_mul (m.choose k:ℝ)
  exact hi.congr (Eventually.of_forall (fun p=>by dsimp; ring))

private theorem ml_raw_power_integral (m : ℕ) :
    (∫p:(ℝ×ℝ)×(ℝ×ℝ),mlW p^m*Real.exp (-(p.1.1+p.1.2+p.2.1+p.2.2)/2)
      ∂mlRawMeasure)=
      ∑k∈Finset.range (m+1),(m.choose k:ℝ)*
        (∫u:ℝ×ℝ,(u.1-u.2)^k*Real.exp (-(u.1+u.2)/2)
          ∂(RiemannGaussian.pairedEtaLogMeasure.prod RiemannGaussian.pairedEtaLogMeasure))*
        (∫v:ℝ×ℝ,(v.1-v.2)^(m-k)*Real.exp (-(v.1+v.2)/2)
          ∂liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure) := by
  simp_rw [ml_raw_polynomial]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have he : (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>(m.choose k:ℝ)*
        ((p.1.1-p.1.2)^k*Real.exp (-(p.1.1+p.1.2)/2))*
        ((p.2.1-p.2.2)^(m-k)*Real.exp (-(p.2.1+p.2.2)/2)))=
        (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>(m.choose k:ℝ)*
          (((p.1.1-p.1.2)^k*Real.exp (-(p.1.1+p.1.2)/2))*
          ((p.2.1-p.2.2)^(m-k)*Real.exp (-(p.2.1+p.2.2)/2)))) := by
      funext p; ring
    rw [he,integral_const_mul]
    change (m.choose k:ℝ)*(∫p:(ℝ×ℝ)×(ℝ×ℝ),
      ((p.1.1-p.1.2)^k*Real.exp (-(p.1.1+p.1.2)/2))*
      ((p.2.1-p.2.2)^(m-k)*Real.exp (-(p.2.1+p.2.2)/2))
      ∂mlRawMeasure)=_
    have hprod := integral_prod_mul
      (μ:=RiemannGaussian.pairedEtaLogMeasure.prod RiemannGaussian.pairedEtaLogMeasure)
      (ν:=liClockPairedEtaHalfLineLogMeasure.prod liClockPairedEtaHalfLineLogMeasure)
      (fun u:ℝ×ℝ=>(u.1-u.2)^k*Real.exp (-(u.1+u.2)/2))
      (fun v:ℝ×ℝ=>(v.1-v.2)^(m-k)*Real.exp (-(v.1+v.2)/2))
    rw [hprod]
    ring
  · intro k hk
    have hi := ((ml_actual_raw_power_integrable k).mul_prod
      (ml_reference_raw_power_integrable (m-k))).const_mul (m.choose k:ℝ)
    exact hi.congr (Eventually.of_forall (fun p=>by dsimp; ring))

private theorem ml_raw_normalization (j : ℕ) :
    liClockPairedEtaInfinitePartitionMixedEvenMoment j=
      (∫p:(ℝ×ℝ)×(ℝ×ℝ),mlW p^(2*j)*
        Real.exp (-(p.1.1+p.1.2+p.2.1+p.2.2)/2)∂mlRawMeasure)/
        (liClockPairedEtaInfinitePartitionNormalizer^2*
          liClockPairedEtaHalfLinePartitionNormalizer^2) := by
  change (∫p:(ℝ×ℝ)×(ℝ×ℝ),mlW p^(2*j)
    ∂liClockPairedEtaInfinitePartitionMixedMeasure)=_
  rw [ml_mixed_power_integral,ml_raw_power_integral,Finset.sum_div]
  simp_rw [ml_actual_power_normalization,ml_reference_power_normalization]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem ml_ratio_mul (j : ℕ) :
    liClockPairedEtaInfinitePartitionMomentRatio j*
      liClockPairedEtaHalfLineSymmetrizedEvenMoment j=
      liClockPairedEtaInfiniteSymmetrizedEvenMoment j := by
  unfold liClockPairedEtaInfinitePartitionMomentRatio
  exact div_mul_cancel₀ _ (liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos j).ne'

private theorem ml_factorial_binomial {j a : ℕ} (ha : a ≤ j) :
    (Nat.choose (2*j) (2*a):ℝ)*((2*a).factorial:ℝ)*
      ((2*(j-a)).factorial:ℝ)=((2*j).factorial:ℝ) := by
  have he : 2*j-2*a=2*(j-a) := by omega
  have h := Nat.choose_mul_factorial_mul_factorial (show 2*a ≤ 2*j by omega)
  rw [he] at h
  exact_mod_cast h

/- Exactly one factorial remains after the complete mixed binomial sum is normalized. -/
theorem liClockPairedEtaInfinitePartitionMixedEvenMoment_eq_factorial_prefix (j : ℕ) :
    liClockPairedEtaInfinitePartitionMixedEvenMoment j =
      ((2*j).factorial:ℝ)*(4:ℝ)^j*
        liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix j := by
  rw [liClockPairedEtaInfinitePartitionMixedEvenMoment_eq_sum]
  unfold liClockPairedEtaInfinitePartitionMixedMomentRatioPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  rw [←ml_ratio_mul a,liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq a,
    liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq (j-a)]
  have hp : (4:ℝ)^a*4^(j-a)=4^j := by
    rw [←pow_add,Nat.add_sub_of_le ha']
  calc
    _ = ((Nat.choose (2*j) (2*a):ℝ)*((2*a).factorial:ℝ)*
        ((2*(j-a)).factorial:ℝ))*(4^a*4^(j-a))*
        liClockPairedEtaInfinitePartitionMomentRatio a := by ring
    _ = _ := by rw [ml_factorial_binomial ha',hp]

/- Each fixed finite mixed even moment converges to its full infinite source moment. -/
theorem tendsto_liClockPairedEtaPartitionMixedEvenMoment (j : ℕ) :
    Tendsto (fun N:ℕ=>liClockPairedEtaPartitionMixedEvenMoment N j) atTop
      (nhds (liClockPairedEtaInfinitePartitionMixedEvenMoment j)) := by
  rw [liClockPairedEtaInfinitePartitionMixedEvenMoment_eq_sum]
  have h := tendsto_finsetSum (Finset.range (j+1)) (fun a ha =>
    ((show Tendsto (fun _:ℕ=>(Nat.choose (2*j) (2*a):ℝ)) atTop
      (nhds (Nat.choose (2*j) (2*a):ℝ)) from tendsto_const_nhds).mul
      (tendsto_liClockPairedEtaInfiniteSymmetrizedEvenMoment a)).mul
      (tendsto_liClockPairedEtaHalfLineSymmetrizedEvenMoment (j-a)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (liClockPairedEtaPartitionMixedEvenMoment_eq_sum (by omega:0<N) j).symm

/- Every normalized marginal moment ratio is strictly positive. -/
theorem liClockPairedEtaInfinitePartitionMomentRatio_pos (j : ℕ) :
    0<liClockPairedEtaInfinitePartitionMomentRatio j :=
  div_pos (liClockPairedEtaInfiniteSymmetrizedEvenMoment_pos j)
    (liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos j)

/- The complete mixed degree-zero moment equals the probability mass. -/
theorem liClockPairedEtaInfinitePartitionMixedEvenMoment_zero :
    liClockPairedEtaInfinitePartitionMixedEvenMoment 0=1 := by
  letI := liClockPairedEtaInfinitePartitionMixedMeasure_isProbability
  simp [liClockPairedEtaInfinitePartitionMixedEvenMoment]

private def mlK : ℝ := 4/(2-Real.sqrt 2)^2

private theorem mlK_nonneg : 0 ≤ mlK := by unfold mlK; positivity

private theorem ml_mixed_nonneg (j : ℕ) :
    0 ≤ liClockPairedEtaInfinitePartitionMixedEvenMoment j := by
  apply integral_nonneg
  intro p
  change 0 ≤ ((p.1.1-p.1.2)+(p.2.1-p.2.2))^(2*j)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) j

private theorem ml_finite_nonneg (N j : ℕ) :
    0 ≤ liClockPairedEtaPartitionMixedEvenMoment N j := by
  apply integral_nonneg
  intro p
  change 0 ≤ ((p.1.1-p.1.2)+(p.2.1-p.2.2))^(2*j)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) j

private theorem ml_reference_binomial {j a : ℕ} (ha : a ≤ j) :
    (Nat.choose (2*j) (2*a):ℝ)*liClockPairedEtaHalfLineSymmetrizedEvenMoment a*
      liClockPairedEtaHalfLineSymmetrizedEvenMoment (j-a)=
      ((2*j).factorial:ℝ)*4^j := by
  rw [liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq a,
    liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq (j-a)]
  have hp : (4:ℝ)^a*4^(j-a)=4^j := by rw [←pow_add,Nat.add_sub_of_le ha]
  calc
    _ = ((Nat.choose (2*j) (2*a):ℝ)*((2*a).factorial:ℝ)*
      ((2*(j-a)).factorial:ℝ))*(4^a*4^(j-a)) := by ring
    _ = _ := by rw [ml_factorial_binomial ha,hp]

private theorem ml_finite_moment_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaPartitionMixedEvenMoment N j ≤
      mlK^2*(j+1)*((2*j).factorial:ℝ)*4^j := by
  have hL : 0<Real.log (2*(N:ℝ)) := by
    apply Real.log_pos
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [liClockPairedEtaPartitionMixedEvenMoment_eq_sum hN]
  calc
    _  ≤  ∑a∈Finset.range (j+1),mlK^2*((2*j).factorial:ℝ)*4^j := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have hd := liClockPairedEtaSymmetrizedEvenMoment_le_halfLine_uniform hN a
      have hu := liClockPairedEtaContiguousSymmetrizedEvenMoment_le_halfLine_uniform hN (j-a)
      calc
        _  ≤  (Nat.choose (2*j) (2*a):ℝ)*(mlK*liClockPairedEtaHalfLineSymmetrizedEvenMoment a)*
          (mlK*liClockPairedEtaHalfLineSymmetrizedEvenMoment (j-a)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)) hu
            (liClockPairedEtaContiguousSymmetrizedEvenMoment_pos hL (j-a)).le
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg mlK_nonneg
              (liClockPairedEtaHalfLineSymmetrizedEvenMoment_pos a).le))
        _ = mlK^2*((Nat.choose (2*j) (2*a):ℝ)*
          liClockPairedEtaHalfLineSymmetrizedEvenMoment a*
          liClockPairedEtaHalfLineSymmetrizedEvenMoment (j-a)) := by ring
        _ = _ := by rw [ml_reference_binomial ha']; ring
    _ = _ := by simp; ring

private theorem ml_mixed_moment_bound (j : ℕ) :
    liClockPairedEtaInfinitePartitionMixedEvenMoment j ≤
      mlK^2*(j+1)*((2*j).factorial:ℝ)*4^j := by
  apply le_of_tendsto (tendsto_liClockPairedEtaPartitionMixedEvenMoment j)
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact ml_finite_moment_bound (by omega:0<N) j

private theorem ml_index_bound (j : ℕ) : (j:ℝ)+1 ≤ (4:ℝ)^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith

private theorem ml_normalized_bound {d : ℝ} (j : ℕ) (hd : 0 ≤ d)
    (hb : d ≤ mlK^2*(j+1)*((2*j).factorial:ℝ)*4^j) :
    |d/((2*j).factorial:ℝ)^2| ≤ mlK^2*4^(2*j)/((2*j).factorial:ℝ) := by
  have hf : (0:ℝ)<((2*j).factorial:ℝ) := by positivity
  rw [abs_of_nonneg (div_nonneg hd (sq_nonneg _))]
  have he : d ≤ mlK^2*((2*j).factorial:ℝ)*4^(2*j) := by
    calc
      _  ≤  mlK^2*(j+1)*((2*j).factorial:ℝ)*4^j := hb
      _  ≤  mlK^2*4^j*((2*j).factorial:ℝ)*4^j := by gcongr; exact ml_index_bound j
      _ = _ := by rw [show 2*j=j+j by omega,pow_add]; ring
  calc
    _ ≤ (mlK^2*((2*j).factorial:ℝ)*4^(2*j))/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right he (sq_nonneg _)
    _ = _ := by field_simp [hf.ne']

private def mlCoeff (j : ℕ) : ℝ :=
  liClockPairedEtaInfinitePartitionMixedEvenMoment j/((2*j).factorial:ℝ)^2

private def mlCoeffN (N j : ℕ) : ℝ :=
  liClockPairedEtaPartitionMixedEvenMoment N j/((2*j).factorial:ℝ)^2

private theorem ml_coeff_bound (j : ℕ) :
    |mlCoeff j| ≤ mlK^2*4^(2*j)/((2*j).factorial:ℝ) :=
  ml_normalized_bound j (ml_mixed_nonneg j) (ml_mixed_moment_bound j)

private theorem ml_coeffN_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    |mlCoeffN N j| ≤ mlK^2*4^(2*j)/((2*j).factorial:ℝ) :=
  ml_normalized_bound j (ml_finite_nonneg N j) (ml_finite_moment_bound hN j)

private theorem ml_coeff_limit (j : ℕ) :
    Tendsto (fun N:ℕ=>mlCoeffN N j) atTop (nhds (mlCoeff j)) :=
  (tendsto_liClockPairedEtaPartitionMixedEvenMoment j).div_const _

private def mlCoefficientSeries (a : ℕ→ℝ) (z : ℂ) : ℂ :=
  ∑'j:ℕ,(a j:ℂ)*z^(2*j)

private theorem ml_seriesTerm_norm_le {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ T) (j : ℕ) :
    ‖(a j:ℂ)*z^(2*j)‖ ≤ K*((R*T)^(2*j)/((2*j).factorial:ℝ)) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
  calc
    _  ≤  (K*R^(2*j)/((2*j).factorial:ℝ))*T^(2*j) :=
      mul_le_mul (ha j) (pow_le_pow_left₀ (norm_nonneg z) hz _)
        (pow_nonneg (norm_nonneg z) _) (div_nonneg (mul_nonneg hK (by
          rw [pow_mul]; positivity)) (Nat.cast_nonneg _))
    _ = _ := by rw [mul_pow]; ring

private theorem ml_series_summable_norm {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    Summable (fun j:ℕ=>‖(a j:ℂ)*z^(2*j)‖) := by
  exact ((Real.hasSum_cosh (R*‖z‖)).summable.mul_left K).of_nonneg_of_le
    (fun _=>norm_nonneg _) (ml_seriesTerm_norm_le hK ha (le_refl _) )

private theorem ml_series_norm_le {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    ‖mlCoefficientSeries a z‖ ≤ K*Real.cosh (R*‖z‖) := by
  calc
    _  ≤  ∑'j:ℕ,‖(a j:ℂ)*z^(2*j)‖ :=
      norm_tsum_le_tsum_norm (ml_series_summable_norm hK ha z)
    _  ≤  ∑'j:ℕ,K*((R*‖z‖)^(2*j)/((2*j).factorial:ℝ)) :=
      (ml_series_summable_norm hK ha z).tsum_le_tsum
        (ml_seriesTerm_norm_le hK ha (le_refl _))
        ((Real.hasSum_cosh (R*‖z‖)).summable.mul_left K)
    _ = _ := by rw [tsum_mul_left,← (Real.hasSum_cosh _).tsum_eq]

private theorem ml_series_uniform {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>(a j:ℂ)*z^(2*j))
      (mlCoefficientSeries a) (closedBall 0 T) := by
  exact HasSumUniformlyOn.of_norm_le_summable
    ((Real.hasSum_cosh (R*T)).summable.mul_left K)
    (fun j z hz=>ml_seriesTerm_norm_le hK ha
      (by simpa only [mem_closedBall,dist_zero_right] using hz) j)

private theorem ml_series_locallyUniform {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) :
    SummableLocallyUniformlyOn (fun j:ℕ=>fun z:ℂ=>(a j:ℂ)*z^(2*j)) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro S hS hSc
  obtain ⟨T,hT⟩ := hSc.bddAbove_image continuous_norm.continuousOn
  refine ⟨_,(Real.hasSum_cosh (R*T)).summable.mul_left K,?_⟩
  intro j z hz
  exact ml_seriesTerm_norm_le hK ha (hT ⟨z,hz,rfl⟩) j

private theorem ml_series_analyticAt {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (z : ℂ) :
    AnalyticAt ℂ (mlCoefficientSeries a) z := by
  let T : ℝ := ‖z‖+1
  have hd : DifferentiableOn ℂ (mlCoefficientSeries a) (ball 0 T) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((Real.hasSum_cosh (R*T)).summable.mul_left K) ?_ isOpen_ball ?_
    · intro j
      fun_prop
    · intro j w hw
      exact ml_seriesTerm_norm_le hK ha
        (le_of_lt (by simpa only [mem_ball,dist_zero_right] using hw)) j
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simp [T]))

private theorem ml_series_ofReal (a : ℕ→ℝ) (t : ℝ) :
    mlCoefficientSeries a (t:ℂ)=(∑'j:ℕ,a j*t^(2*j):ℝ) := by
  unfold mlCoefficientSeries
  simp_rw [← Complex.ofReal_pow,← Complex.ofReal_mul]
  exact (Complex.ofReal_tsum _).symm

private theorem ml_series_realSummable {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ)) (t : ℝ) :
    Summable (fun j:ℕ=>a j*t^(2*j)) := by
  have h := (ml_series_summable_norm hK ha (t:ℂ)).of_norm
  have hre := h.mapL Complex.reCLM
  simpa only [← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.reCLM_apply,Complex.ofReal_re] using hre

private theorem ml_series_ge_one {a : ℕ→ℝ} {K R : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    (ha0 : a 0=1) (haPos : ∀j,0 ≤ a j) (t : ℝ) :
    1 ≤ ∑'j:ℕ,a j*t^(2*j) := by
  have h := (ml_series_realSummable hK ha t).le_tsum 0
    (fun j _=>mul_nonneg (haPos j) (by rw [pow_mul]; positivity))
  simpa only [ha0,mul_zero,pow_zero,mul_one] using h

private theorem ml_series_error_tendsto
    {aN : ℕ→ℕ→ℝ} {a : ℕ→ℝ} {K R T : ℝ}
    (_hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    (haN : ∀ᶠN:ℕ in atTop,∀j,|aN N j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    (hlim : ∀j,Tendsto (fun N:ℕ=>aN N j) atTop (nhds (a j))) :
    Tendsto (fun N:ℕ=>∑'j:ℕ,|aN N j-a j| * T^(2*j)) atTop (nhds 0) := by
  have hs : Summable (fun j:ℕ=>2*K*((R*T)^(2*j)/((2*j).factorial:ℝ))) :=
    (Real.hasSum_cosh (R*T)).summable.mul_left (2*K)
  have ht (j:ℕ) : Tendsto (fun N:ℕ=>|aN N j-a j| * T^(2*j)) atTop (nhds 0) := by
    simpa only [sub_self,abs_zero,zero_mul] using ((hlim j).sub_const (a j)).abs.mul_const (T^(2*j))
  have hb : ∀ᶠN:ℕ in atTop,∀j,
      ‖|aN N j-a j| * T^(2*j)‖ ≤ 2*K*((R*T)^(2*j)/((2*j).factorial:ℝ)) := by
    filter_upwards [haN] with N hN
    intro j
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) ((even_two_mul j).pow_nonneg T))]
    calc
      _  ≤  (|aN N j|+|a j|)*T^(2*j) :=
        mul_le_mul_of_nonneg_right (by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (aN N j) 0 (a j)) ((even_two_mul j).pow_nonneg T)
      _  ≤  (K*R^(2*j)/((2*j).factorial:ℝ)+K*R^(2*j)/((2*j).factorial:ℝ))*T^(2*j) :=
        mul_le_mul_of_nonneg_right (add_le_add (hN j) (ha j)) ((even_two_mul j).pow_nonneg T)
      _ = _ := by rw [mul_pow]; ring
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs ht hb

private theorem ml_series_error_bound
    {aN a : ℕ→ℝ} {K R T : ℝ} (hK : 0 ≤ K)
    (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    (haN : ∀j,|aN j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    {z : ℂ} (hz : ‖z‖ ≤ T) :
    ‖mlCoefficientSeries aN z-mlCoefficientSeries a z‖ ≤
      ∑'j:ℕ,|aN j-a j| * T^(2*j) := by
  have hdiff (j:ℕ) : |aN j-a j| ≤ (2*K)*R^(2*j)/((2*j).factorial:ℝ) := by
    calc
      _  ≤  |aN j|+|a j| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (aN j) 0 (a j)
      _  ≤  K*R^(2*j)/((2*j).factorial:ℝ)+K*R^(2*j)/((2*j).factorial:ℝ) := add_le_add (haN j) (ha j)
      _ = _ := by ring
  have hs := (ml_series_summable_norm hK haN z).of_norm
  have ht := (ml_series_summable_norm hK ha z).of_norm
  have hu : Summable (fun j:ℕ=>|aN j-a j| * T^(2*j)) :=
    ((Real.hasSum_cosh (R*T)).summable.mul_left (2*K)).of_nonneg_of_le
      (fun j=>mul_nonneg (abs_nonneg _) ((even_two_mul j).pow_nonneg T))
      (fun j=>by
        exact (mul_le_mul_of_nonneg_right (hdiff j) ((even_two_mul j).pow_nonneg T)).trans_eq (by rw [mul_pow]; ring))
  unfold mlCoefficientSeries
  rw [← hs.tsum_sub ht]
  calc
    _  ≤  ∑'j:ℕ,‖(aN j:ℂ)*z^(2*j)-(a j:ℂ)*z^(2*j)‖ :=
      norm_tsum_le_tsum_norm (hs.sub ht).norm
    _  ≤  _ := (hs.sub ht).norm.tsum_le_tsum (fun j=>by
      rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (abs_nonneg _)) hu

private theorem ml_series_tendstoUniformlyOn
    {aN : ℕ→ℕ→ℝ} {a : ℕ→ℝ} {K R T : ℝ}
    (hK : 0 ≤ K) (ha : ∀j,|a j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    (haN : ∀ᶠN:ℕ in atTop,∀j,|aN N j| ≤ K*R^(2*j)/((2*j).factorial:ℝ))
    (hlim : ∀j,Tendsto (fun N:ℕ=>aN N j) atTop (nhds (a j))) :
    TendstoUniformlyOn (fun N:ℕ=>mlCoefficientSeries (aN N))
      (mlCoefficientSeries a) atTop (closedBall 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := ml_series_error_tendsto hK ha haN hlim (T:=T)
  filter_upwards [haN,he.eventually (gt_mem_nhds hε)] with N hN hE
  intro z hz
  rw [dist_eq_norm, norm_sub_rev]
  exact (ml_series_error_bound hK ha hN
    (by simpa only [mem_closedBall,dist_zero_right] using hz)).trans_lt hE


private theorem ml_kernel_term (j : ℕ) (z : ℂ) :
    (liClockPairedEtaInfinitePartitionMixedEvenMoment j:ℂ)*z^(2*j)/
      ((2*j).factorial:ℂ)^2=(mlCoeff j:ℂ)*z^(2*j) := by
  simp only [mlCoeff,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

private theorem ml_kernelN_term (N j : ℕ) (z : ℂ) :
    (liClockPairedEtaPartitionMixedEvenMoment N j:ℂ)*z^(2*j)/
      ((2*j).factorial:ℂ)^2=(mlCoeffN N j:ℂ)*z^(2*j) := by
  simp only [mlCoeffN,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

private theorem ml_kernel_eq_series :
    liClockPairedEtaInfinitePartitionMixedBorelKernelComplex=mlCoefficientSeries mlCoeff := by
  funext z
  unfold liClockPairedEtaInfinitePartitionMixedBorelKernelComplex mlCoefficientSeries
  exact tsum_congr (fun j=>ml_kernel_term j z)

private theorem ml_kernelN_eq_series (N : ℕ) :
    liClockPairedEtaPartitionMixedBorelKernelComplex N=mlCoefficientSeries (mlCoeffN N) := by
  funext z
  unfold liClockPairedEtaPartitionMixedBorelKernelComplex mlCoefficientSeries
  exact tsum_congr (fun j=>ml_kernelN_term N j z)

private theorem ml_kernel_real_eq_series (t : ℝ) :
    liClockPairedEtaInfinitePartitionMixedBorelKernel t=∑'j,mlCoeff j*t^(2*j) := by
  unfold liClockPairedEtaInfinitePartitionMixedBorelKernel
  apply tsum_congr
  intro j
  dsimp [mlCoeff]
  ring

private theorem ml_kernelN_real_eq_series (N : ℕ) (t : ℝ) :
    liClockPairedEtaPartitionMixedBorelKernel N t=∑'j,mlCoeffN N j*t^(2*j) := by
  unfold liClockPairedEtaPartitionMixedBorelKernel
  apply tsum_congr
  intro j
  dsimp [mlCoeffN]
  ring

/- The full complex mixed Borel series converges absolutely at every clock. -/
theorem summable_norm_liClockPairedEtaInfinitePartitionMixedBorelTerm (z : ℂ) :
    Summable (fun j:ℕ=>‖(liClockPairedEtaInfinitePartitionMixedEvenMoment j:ℂ)*z^(2*j)/
      ((2*j).factorial:ℂ)^2‖) := by
  simp_rw [ml_kernel_term]
  exact ml_series_summable_norm (sq_nonneg mlK) ml_coeff_bound z

/- Full complex partial sums converge uniformly on each fixed closed ball. -/
theorem hasSumUniformlyOn_liClockPairedEtaInfinitePartitionMixedBorelKernelComplex
    (T : ℝ) (_hT : 0 ≤ T) :
    HasSumUniformlyOn (fun j:ℕ=>fun z:ℂ=>
      (liClockPairedEtaInfinitePartitionMixedEvenMoment j:ℂ)*z^(2*j)/
        ((2*j).factorial:ℂ)^2)
      liClockPairedEtaInfinitePartitionMixedBorelKernelComplex (Metric.closedBall 0 T) := by
  simp_rw [ml_kernel_term]
  rw [ml_kernel_eq_series]
  exact ml_series_uniform (sq_nonneg mlK) ml_coeff_bound

/- The infinite mixed factorial series is entire. -/
theorem analyticAt_liClockPairedEtaInfinitePartitionMixedBorelKernelComplex (z : ℂ) :
    AnalyticAt ℂ liClockPairedEtaInfinitePartitionMixedBorelKernelComplex z := by
  rw [ml_kernel_eq_series]
  exact ml_series_analyticAt (sq_nonneg mlK) ml_coeff_bound z

/- Every positive finite prefix has an entire mixed factorial series. -/
theorem analyticAt_liClockPairedEtaPartitionMixedBorelKernelComplex {N : ℕ}
    (hN : 0<N) (z : ℂ) :
    AnalyticAt ℂ (liClockPairedEtaPartitionMixedBorelKernelComplex N) z := by
  rw [ml_kernelN_eq_series]
  exact ml_series_analyticAt (sq_nonneg mlK) (ml_coeffN_bound hN) z

/- The finite complex extension restricts to the literal real mixed kernel, including the zero prefix. -/
theorem liClockPairedEtaPartitionMixedBorelKernelComplex_ofReal (N : ℕ) (t : ℝ) :
    liClockPairedEtaPartitionMixedBorelKernelComplex N (t:ℂ)=
      (liClockPairedEtaPartitionMixedBorelKernel N t:ℂ) := by
  rw [ml_kernelN_eq_series,ml_series_ofReal,ml_kernelN_real_eq_series]

/- The infinite complex extension restricts to the literal real mixed kernel. -/
theorem liClockPairedEtaInfinitePartitionMixedBorelKernelComplex_ofReal (t : ℝ) :
    liClockPairedEtaInfinitePartitionMixedBorelKernelComplex (t:ℂ)=
      (liClockPairedEtaInfinitePartitionMixedBorelKernel t:ℂ) := by
  rw [ml_kernel_eq_series,ml_series_ofReal,ml_kernel_real_eq_series]

/- The infinite mixed kernel equals one at clock zero. -/
theorem liClockPairedEtaInfinitePartitionMixedBorelKernel_zero :
    liClockPairedEtaInfinitePartitionMixedBorelKernel 0=1 := by
  unfold liClockPairedEtaInfinitePartitionMixedBorelKernel
  rw [tsum_eq_single 0]
  · simp only [mul_zero,Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one,one_pow,div_one,
      liClockPairedEtaInfinitePartitionMixedEvenMoment_zero]
  · intro j hj
    have he : 2*j≠0 := by omega
    simp only [zero_pow he,mul_zero,zero_div]

/- Nonnegative even source coefficients retain the degree-zero term at every real clock. -/
theorem one_le_liClockPairedEtaInfinitePartitionMixedBorelKernel (t : ℝ) :
    1 ≤ liClockPairedEtaInfinitePartitionMixedBorelKernel t := by
  rw [ml_kernel_real_eq_series]
  apply ml_series_ge_one (sq_nonneg mlK) ml_coeff_bound
  · simp [mlCoeff,liClockPairedEtaInfinitePartitionMixedEvenMoment_zero]
  · intro j
    exact div_nonneg (ml_mixed_nonneg j) (sq_nonneg _)

private theorem ml_entire_smooth {f : ℂ→ℂ} (hf : ∀z,AnalyticAt ℂ f z) :
    ContDiff ℂ ⊤ f :=
  AnalyticOnNhd.contDiff (fun z _=>hf z)

/- The literal infinite real mixed kernel is smooth. -/
theorem contDiff_liClockPairedEtaInfinitePartitionMixedBorelKernel :
    ContDiff ℝ ⊤ liClockPairedEtaInfinitePartitionMixedBorelKernel := by
  have h := (ml_entire_smooth analyticAt_liClockPairedEtaInfinitePartitionMixedBorelKernelComplex).real_of_complex
  have he : (fun t:ℝ=>(liClockPairedEtaInfinitePartitionMixedBorelKernelComplex (t:ℂ)).re)=
      liClockPairedEtaInfinitePartitionMixedBorelKernel := by
    funext t
    rw [liClockPairedEtaInfinitePartitionMixedBorelKernelComplex_ofReal,Complex.ofReal_re]
  rw [he] at h
  exact h

private theorem ml_local_uniform :
    TendstoLocallyUniformlyOn liClockPairedEtaPartitionMixedBorelKernelComplex
      liClockPairedEtaInfinitePartitionMixedBorelKernelComplex atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro S _hS hSc
  obtain ⟨T,hT⟩ := hSc.bddAbove_image continuous_norm.continuousOn
  have hB : S⊆Metric.closedBall (0:ℂ) T := by
    intro z hz
    simpa only [Metric.mem_closedBall,dist_zero_right] using hT ⟨z,hz,rfl⟩
  have hEq : liClockPairedEtaPartitionMixedBorelKernelComplex=
      (fun N:ℕ=>mlCoefficientSeries (mlCoeffN N)) :=
    funext (fun N=>ml_kernelN_eq_series N)
  rw [hEq,ml_kernel_eq_series]
  apply (ml_series_tendstoUniformlyOn (sq_nonneg mlK)
    ml_coeff_bound (T:=T) _ ml_coeff_limit).mono hB
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact ml_coeffN_bound (by omega:0<N)

private theorem ml_local_uniform_iterated (m : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N:ℕ=>iteratedDeriv m (liClockPairedEtaPartitionMixedBorelKernelComplex N))
      (iteratedDeriv m liClockPairedEtaInfinitePartitionMixedBorelKernelComplex)
      atTop Set.univ := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using ml_local_uniform
  | succ m ih =>
    have hd : ∀ᶠN:ℕ in atTop,
        DifferentiableOn ℂ (iteratedDeriv m (liClockPairedEtaPartitionMixedBorelKernelComplex N)) Set.univ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact ((ml_entire_smooth (analyticAt_liClockPairedEtaPartitionMixedBorelKernelComplex
        (by omega:0<N))).differentiable_iteratedDeriv m (by simp)).differentiableOn
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv hd isOpen_univ

/- Every fixed complex derivative order converges uniformly on every fixed closed ball. -/
theorem tendstoUniformlyOn_liClockPairedEtaPartitionMixedBorelKernelComplex_iteratedDeriv
    (m : ℕ) (T : ℝ) (_hT : 0 ≤ T) :
    TendstoUniformlyOn
      (fun N:ℕ=>fun z:ℂ=>iteratedDeriv m (liClockPairedEtaPartitionMixedBorelKernelComplex N) z)
      (fun z:ℂ=>iteratedDeriv m liClockPairedEtaInfinitePartitionMixedBorelKernelComplex z)
      atTop (Metric.closedBall (0:ℂ) T) :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
    (ml_local_uniform_iterated m) _ (Set.subset_univ _) (isCompact_closedBall _ _)

private theorem ml_iteratedDeriv_re {f : ℂ→ℂ} {g : ℝ→ℝ}
    (hf : ∀z,AnalyticAt ℂ f z) (he : ∀t:ℝ,(f (t:ℂ)).re=g t) (m : ℕ) (t : ℝ) :
    iteratedDeriv m g t=(iteratedDeriv m f (t:ℂ)).re := by
  induction m generalizing t with
  | zero => simpa only [iteratedDeriv_zero] using (he t).symm
  | succ m ih =>
    rw [iteratedDeriv_succ,iteratedDeriv_succ]
    have hg : iteratedDeriv m g=(fun t:ℝ=>(iteratedDeriv m f (t:ℂ)).re) := funext ih
    rw [hg]
    exact (((ml_entire_smooth hf).differentiable_iteratedDeriv m
      (by simp)).differentiableAt.hasDerivAt.real_of_complex).deriv

/- Every fixed real derivative order converges uniformly on every fixed closed interval ball. -/
theorem tendstoUniformlyOn_liClockPairedEtaPartitionMixedBorelKernel_iteratedDeriv
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    TendstoUniformlyOn
      (fun N:ℕ=>fun t:ℝ=>iteratedDeriv m (liClockPairedEtaPartitionMixedBorelKernel N) t)
      (fun t:ℝ=>iteratedDeriv m liClockPairedEtaInfinitePartitionMixedBorelKernel t)
      atTop (Metric.closedBall (0:ℝ) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc := tendstoUniformlyOn_liClockPairedEtaPartitionMixedBorelKernelComplex_iteratedDeriv m T hT
  rw [Metric.tendstoUniformlyOn_iff] at hc
  filter_upwards [hc ε hε,eventually_ge_atTop 1] with N hN hn
  intro t ht
  have hi := ml_iteratedDeriv_re (g:=liClockPairedEtaInfinitePartitionMixedBorelKernel)
    analyticAt_liClockPairedEtaInfinitePartitionMixedBorelKernelComplex
    (fun t=>by rw [liClockPairedEtaInfinitePartitionMixedBorelKernelComplex_ofReal,Complex.ofReal_re]) m t
  have hf := ml_iteratedDeriv_re (g:=liClockPairedEtaPartitionMixedBorelKernel N)
    (analyticAt_liClockPairedEtaPartitionMixedBorelKernelComplex (by omega:0<N))
    (fun t=>by rw [liClockPairedEtaPartitionMixedBorelKernelComplex_ofReal,Complex.ofReal_re]) m t
  rw [hi,hf,Real.dist_eq]
  calc
    _  ≤  ‖iteratedDeriv m liClockPairedEtaInfinitePartitionMixedBorelKernelComplex (t:ℂ)-
      iteratedDeriv m (liClockPairedEtaPartitionMixedBorelKernelComplex N) (t:ℂ)‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm
        (iteratedDeriv m liClockPairedEtaInfinitePartitionMixedBorelKernelComplex (t:ℂ)-
          iteratedDeriv m (liClockPairedEtaPartitionMixedBorelKernelComplex N) (t:ℂ))
    _ < ε := by
      simpa only [dist_eq_norm] using hN (t:ℂ) (by
        simpa only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
          using ht)

private theorem ml_kernel_pointwise_hasSum (t : ℝ) (p : (ℝ×ℝ)×(ℝ×ℝ)) :
    HasSum (fun j:ℕ=>mlW p^(2*j)*t^(2*j)/((2*j).factorial:ℝ)^2)
      (liClockCriticalEvenKernel (t*mlW p)) := by
  have hs : Summable (fun n:ℕ=>(t*mlW p)^n/(n.factorial:ℝ)^2) := by
    apply Complex.summable_ofReal.mp
    simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
      using (summable_norm_liClockCriticalScalarTermComplex ((t*mlW p:ℝ):ℂ)).of_norm
  have he : HasSum (fun j:ℕ=>(t*mlW p)^(2*j)/((2*j).factorial:ℝ)^2)
      (∑'j,(t*mlW p)^(2*j)/((2*j).factorial:ℝ)^2) :=
    (hs.comp_injective (fun x y h=>by omega)).hasSum
  change HasSum _ (∑'j,(t*mlW p)^(2*j)/((2*j).factorial:ℝ)^2)
  apply he.congr_fun
  intro j
  rw [mul_pow]
  ring

private theorem ml_kernel_integrable (t : ℝ) :
    Integrable (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>liClockCriticalEvenKernel (t*mlW p))
      liClockPairedEtaInfinitePartitionMixedMeasure := by
  let f : ℕ→((ℝ×ℝ)×(ℝ×ℝ))→ℝ := fun j p=>
    mlW p^(2*j)*t^(2*j)/((2*j).factorial:ℝ)^2
  have hf : ∀j p,0 ≤ f j p := by
    intro j p
    dsimp [f]
    rw [pow_mul,pow_mul]
    positivity
  have hfi (j : ℕ) : Integrable (f j) liClockPairedEtaInfinitePartitionMixedMeasure :=
    ((ml_power_integrable (2*j)).mul_const _).div_const _
  have hs (p) := ml_kernel_pointwise_hasSum t p
  have hn (j : ℕ) : (∫p,‖f j p‖∂liClockPairedEtaInfinitePartitionMixedMeasure)=
      mlCoeff j*t^(2*j) := by
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hf j _)]
    dsimp [f,mlCoeff]
    rw [integral_div,integral_mul_const]
    unfold liClockPairedEtaInfinitePartitionMixedEvenMoment
    ring
  have hsum : Summable (fun j:ℕ=>∫p,‖f j p‖∂liClockPairedEtaInfinitePartitionMixedMeasure) := by
    simp_rw [hn]
    exact ml_series_realSummable (sq_nonneg mlK) ml_coeff_bound t
  refine ⟨((continuous_liClockCriticalEvenKernel.comp
    (by fun_prop : Continuous (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>t*mlW p))).aestronglyMeasurable),?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hp (p) : ENNReal.ofReal ‖liClockCriticalEvenKernel (t*mlW p)‖=
      ∑'j,ENNReal.ofReal ‖f j p‖ := by
    have hk : 0 ≤ liClockCriticalEvenKernel (t*mlW p) := by
      rw [←(hs p).tsum_eq]
      exact tsum_nonneg (fun j=>hf j p)
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hf _ p)]
    rw [abs_of_nonneg hk,←(hs p).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun j=>hf j p) (hs p).summable
  calc
    (∫⁻p,ENNReal.ofReal ‖liClockCriticalEvenKernel (t*mlW p)‖
      ∂liClockPairedEtaInfinitePartitionMixedMeasure) =
        ∫⁻p,∑'j,ENNReal.ofReal ‖f j p‖∂liClockPairedEtaInfinitePartitionMixedMeasure :=
      lintegral_congr hp
    _ = ∑'j,∫⁻p,ENNReal.ofReal ‖f j p‖∂liClockPairedEtaInfinitePartitionMixedMeasure :=
      lintegral_tsum (fun j=>(hfi j).norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    _ = ∑'j,ENNReal.ofReal (∫p,‖f j p‖∂liClockPairedEtaInfinitePartitionMixedMeasure) := by
      apply tsum_congr
      intro j
      exact (ofReal_integral_eq_lintegral_ofReal (hfi j).norm
        (Eventually.of_forall (fun p=>norm_nonneg (f j p)))).symm
    _ < ∞ := hsum.tsum_ofReal_lt_top

/- Genuine integrability and full source equality for the complete mixed critical-kernel integral. -/
theorem liClockPairedEtaInfinitePartitionMixedBorelKernel_eq_source (t : ℝ) :
    Integrable (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>
      liClockCriticalEvenKernel (t*((p.1.1-p.1.2)+(p.2.1-p.2.2))))
      liClockPairedEtaInfinitePartitionMixedMeasure ∧
    liClockPairedEtaInfinitePartitionMixedBorelKernel t=
      ∫p:(ℝ×ℝ)×(ℝ×ℝ),liClockCriticalEvenKernel
        (t*((p.1.1-p.1.2)+(p.2.1-p.2.2)))
        ∂liClockPairedEtaInfinitePartitionMixedMeasure := by
  refine ⟨ml_kernel_integrable t,?_⟩
  let f : ℕ→((ℝ×ℝ)×(ℝ×ℝ))→ℝ := fun j p=>
    mlW p^(2*j)*t^(2*j)/((2*j).factorial:ℝ)^2
  have hi (j : ℕ) : Integrable (f j) liClockPairedEtaInfinitePartitionMixedMeasure :=
    ((ml_power_integrable (2*j)).mul_const _).div_const _
  have hn (j : ℕ) : (∫p,‖f j p‖∂liClockPairedEtaInfinitePartitionMixedMeasure)=
      mlCoeff j*t^(2*j) := by
    have hf (p) : 0 ≤ f j p := by dsimp [f]; rw [pow_mul,pow_mul]; positivity
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hf _)]
    dsimp [f,mlCoeff]
    rw [integral_div,integral_mul_const]
    unfold liClockPairedEtaInfinitePartitionMixedEvenMoment
    ring
  have hsum : Summable (fun j:ℕ=>∫p,‖f j p‖∂liClockPairedEtaInfinitePartitionMixedMeasure) := by
    simp_rw [hn]
    exact ml_series_realSummable (sq_nonneg mlK) ml_coeff_bound t
  calc
    _ = ∑'j,∫p,f j p∂liClockPairedEtaInfinitePartitionMixedMeasure := by
      unfold liClockPairedEtaInfinitePartitionMixedBorelKernel
      apply tsum_congr
      intro j
      dsimp [f]
      rw [integral_div,integral_mul_const]
      rfl
    _ = ∫p,∑'j,f j p∂liClockPairedEtaInfinitePartitionMixedMeasure :=
      integral_tsum_of_summable_integral_norm hi hsum
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p=>(ml_kernel_pointwise_hasSum t p).tsum_eq)

end RHTower
