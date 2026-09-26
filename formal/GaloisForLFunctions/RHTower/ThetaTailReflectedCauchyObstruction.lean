import GaloisForLFunctions.RHTower.ThetaTailReflectedBoundaryObstruction
import GaloisForLFunctions.HTGeometry.CaratheodoryKernelPositive

/-!
# No positive reflected Cauchy reserve for the complete theta tail

For every real threshold and every c>0, a finite real packet makes
`K_Phi - c Phi(x)Phi(y)/(q(x)+q(y))` negative, where
`q(x)=exp(2x)+exp(-2x)`. The proof retains the complete theta source.

A charged-cusp diagonal defect is projected onto one complex Cauchy feature.
Analytic locality transfers it to every real tail; real/imaginary splitting
then supplies real coefficients. Positivity of the unsubtracted kernel and
RH remain undecided.

Positive survivors include the exact complex boundary admissibility test
and a quantitative charged-cusp floor for admissible Cauchy rates.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace RHTower.ThetaCuspBoundaryAudit
open DominatedL2Sections Set Filter Topology

theorem psd_finite_projection_bound {X ι : Type*} {K : X → X → ℂ}
    (hK : IsPSDKernel K) (S : Finset ι) (u : ι → X) (d : ι → ℂ) (p : X) :
    ‖∑ i ∈ S, d i*K (u i) p‖^2 ≤
      (K p p).re*(∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*K (u i) (u j)).re := by
  letI : Fact (IsPSDKernel K) := ⟨hK⟩
  let v : KernelHilbert K := ∑ i ∈ S, d i • KernelHilbert.vector K (u i)
  let w : KernelHilbert K := KernelHilbert.vector K p
  have he : inner ℂ w v = ∑ i ∈ S, d i*K (u i) p := by
    simp only [v, w, inner_sum, inner_smul_right, KernelHilbert.inner_vector]
  have hv : (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*K (u i) (u j)).re = ‖v‖^2 := by
    have h : inner ℂ v v = ∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*K (u i) (u j) := by
      dsimp only [v]
      rw [sum_inner]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_smul_left, inner_smul_right, KernelHilbert.inner_vector]
      simp only [Complex.star_def]
      ring
    rw [← h, inner_self_eq_norm_sq_to_K]
    rw [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hw : (K p p).re = ‖w‖^2 := by
    rw [← KernelHilbert.inner_vector (K := K) p p, inner_self_eq_norm_sq_to_K]
    rw [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← he, hv, hw]
  calc
    _ ≤ (‖w‖*‖v‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm w v) 2
    _ = _ := by ring

def halfPlaneCauchy (u v : {z : ℂ // 0 < z.re}) : ℂ :=
  1/(u.val+conj v.val)

theorem halfPlaneCauchy_psd : IsPSDKernel halfPlaneCauchy := by
  have h := isPSDKernel_halfPlaneCaratheodory (F := fun _ : ℂ => ((1/2:ℝ):ℂ))
    (fun u hu => differentiableAt_const _) (fun u hu => by norm_num)
  apply h.congr
  intro u v
  simp only [Complex.conj_ofReal, ← Complex.ofReal_add]
  norm_num [halfPlaneCauchy]

theorem complex_cauchy_projection_bound {ι : Type*} (S : Finset ι)
    (u : ι → ℂ) (hu : ∀ i, 0 < (u i).re) (d : ι → ℂ) {B : ℂ} (hB : 0 < B.re) :
    2*B.re*‖∑ i ∈ S, d i/(u i+B)‖^2 ≤
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i/(u i+conj (u j))).re := by
  let U : ι → {z : ℂ // 0 < z.re} := fun i => ⟨u i, hu i⟩
  let p : {z : ℂ // 0 < z.re} := ⟨conj B, by simpa using hB⟩
  have h := psd_finite_projection_bound halfPlaneCauchy_psd S U d p
  have hp : (halfPlaneCauchy p p).re = 1/(2*B.re) := by
    dsimp [halfPlaneCauchy, p]
    rw [show conj B+conj (conj B) = ((2*B.re:ℝ):ℂ) by
      rw [Complex.conj_conj, add_comm, Complex.add_conj]]
    simp
  rw [hp] at h
  simp only [halfPlaneCauchy, U, p, Complex.conj_conj, mul_one_div] at h
  have hn := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*B.re by positivity)
  have he : 2*B.re*(1/(2*B.re))=1 := by field_simp
  rwa [← mul_assoc, he, one_mul] at hn


abbrev ScalarAugmented := SourceAugmented

def scalarSection (f : ℂ → ℂ) (z : ℂ) : ScalarAugmented :=
  WithLp.toLp 2 (completeThetaSource.section z, f z)

theorem scalarSection_analytic_inner (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f thetaCuspStrip) (v : ScalarAugmented) :
    AnalyticOnNhd ℂ (fun z => inner ℂ v (scalarSection f z)) thetaCuspStrip := by
  have h := (completeThetaSource.analytic_inner v.fst).add
    (hf.mul (analyticOnNhd_const (v := star v.snd)))
  apply AnalyticOnNhd.congr isOpen_thetaCuspStrip h
  intro z hz
  change inner ℂ v.fst (completeThetaSource.section z)+f z*star v.snd = _
  rw [WithLp.prod_inner_apply]
  rfl

def scalarRealization (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f thetaCuspStrip) (c : ℝ) :=
  compressedClosedSpanRealization thetaCuspStrip (scalarSection f)
    (scalarDifferenceForm c) isPreconnected_thetaCuspStrip
    isOpen_thetaCuspStrip (scalarSection_analytic_inner f hf)
    (scalarDifferenceForm_hermitian c)

theorem scalarRealization_kernel (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f thetaCuspStrip)
    (c : ℝ) {z w : ℂ} (hz : z ∈ thetaCuspStrip) (hw : w ∈ thetaCuspStrip) :
    (scalarRealization f hf c).kernel z w = completeThetaSource.realization.kernel z w-
      (2*c:ℂ)*f z*star (f w) := by
  rw [show (scalarRealization f hf c).kernel z w = inner ℂ (scalarSection f w)
      (scalarDifferenceForm c (scalarSection f z)) from
    compressedClosedSpanRealization_kernel_eq thetaCuspStrip (scalarSection f)
      (scalarDifferenceForm c) isPreconnected_thetaCuspStrip
      isOpen_thetaCuspStrip (scalarSection_analytic_inner f hf)
      (scalarDifferenceForm_hermitian c) hz hw]
  rw [scalarDifferenceForm_apply, WithLp.prod_inner_apply]
  change inner ℂ (completeThetaSource.section w) (differenceForm (completeThetaSource.section z))+
    inner ℂ (f w) (-(2*c:ℂ)*f z) = _
  rw [← completeThetaSource.realization_kernel hz hw, RCLike.inner_apply]
  simp only [Complex.star_def]
  ring

def scalarTailSamples (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f thetaCuspStrip) (c a : ℝ) :
    (scalarRealization f hf c).toAnalyticTotalSectionFamily.AccumulationSet where
  nodes := (completeThetaSource.tailAccumulationSet a).nodes
  nodes_subset := (completeThetaSource.tailAccumulationSet a).nodes_subset
  point := (completeThetaSource.tailAccumulationSet a).point
  point_mem_domain := (completeThetaSource.tailAccumulationSet a).point_mem_domain
  frequently_nodes := (completeThetaSource.tailAccumulationSet a).frequently_nodes

def poleFeature (B : ℂ) (z : ℂ) : ℂ := thetaCuspStripSource z/(reflectedRate z+B)

theorem poleFeature_analytic {B : ℂ} (hB : 0 < B.re) :
    AnalyticOnNhd ℂ (poleFeature B) thetaCuspStrip := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_thetaCuspStrip
  apply differentiableOn_thetaCuspStripSource.div
  · unfold reflectedRate
    fun_prop
  · intro z hz he
    have hr := congrArg Complex.re he
    have hp := reflectedRate_re_pos hz
    simp only [Complex.add_re, Complex.zero_re] at hr
    linarith only [hr, hp, hB]

theorem poleFeature_matched_norm_sq {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    ‖poleFeature (conj (reflectedRate z)) z‖^2 =
      ‖thetaCuspStripSource z‖^2/(4*(reflectedRate z).re^2) := by
  have hq := reflectedRate_re_pos hz
  rw [poleFeature, Complex.add_conj, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2*(reflectedRate z).re), div_pow]
  congr 1
  ring


def realReflectedRate (x : ℝ) : ℝ := Real.exp (2*x)+Real.exp (-2*x)

def reflectedReference (x y : ℝ) : ℝ :=
  thetaCuspFullSource x*thetaCuspFullSource y/(realReflectedRate x+realReflectedRate y)

theorem reflectedRate_ofReal (x : ℝ) : reflectedRate (x:ℂ) = (realReflectedRate x:ℂ) := by
  simp [reflectedRate, realReflectedRate, Complex.ofReal_exp]

theorem realReflectedRate_pos (x : ℝ) : 0 < realReflectedRate x := by
  unfold realReflectedRate
  positivity

theorem finite_feature_energy {ι : Type*} (S : Finset ι) (d f : ι → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*f i*star (f j)).re =
      ‖∑ i ∈ S, d i*f i‖^2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*f i*star (f j)) =
      conj (∑ i ∈ S, d i*f i)*(∑ i ∈ S, d i*f i) := by
    rw [map_sum, Finset.sum_mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Complex.star_def]
    ring
  rw [he, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem source_projection_bound {ι : Type*} (S : Finset ι) (x : ι → ℝ) (d : ι → ℂ)
    {B : ℂ} (hB : 0 < B.re) :
    2*B.re*‖∑ i ∈ S, d i*poleFeature B (x i:ℂ)‖^2 ≤
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*(reflectedReference (x i) (x j):ℂ)).re := by
  have h := complex_cauchy_projection_bound S (fun i => (realReflectedRate (x i):ℂ))
    (fun i => realReflectedRate_pos (x i)) (fun i => d i*(thetaCuspFullSource (x i):ℂ)) hB
  have hf : ∀ i, d i*(thetaCuspFullSource (x i):ℂ)/((realReflectedRate (x i):ℂ)+B) =
      d i*poleFeature B (x i:ℂ) := by
    intro i
    rw [poleFeature, thetaCuspStripSource_ofReal, reflectedRate_ofReal]
    ring
  simp_rw [hf] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, reflectedReference]
  push_cast
  ring


theorem scalarRealization_diagonal (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f thetaCuspStrip)
    (c : ℝ) {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    ((scalarRealization f hf c).kernel z z).re =
      (completeThetaSource.realization.kernel z z).re-2*c*‖f z‖^2 := by
  rw [scalarRealization_kernel f hf c hz hz, Complex.sub_re]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem finite_scalar_subtraction_energy {ι : Type*} (S : Finset ι) (d f : ι → ℂ)
    (K : ι → ι → ℂ) (c : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*(K i j-(2*c:ℂ)*f i*star (f j))).re =
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*K i j).re-
        2*c*‖∑ i ∈ S, d i*f i‖^2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*(K i j-(2*c:ℂ)*f i*star (f j))) =
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*K i j)-
        (2*c:ℂ)*(∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*f i*star (f j)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, Complex.sub_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero]
  rw [finite_feature_energy]

theorem negative_scalar_tail_packet (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f thetaCuspStrip)
    (c a : ℝ) {z : ℂ} (hz : z ∈ thetaCuspStrip)
    (hneg : (completeThetaSource.realization.kernel z z).re-2*c*‖f z‖^2 < 0) :
    ∃ (S : Finset (Complex.ofReal '' Ioi a)) (d : (Complex.ofReal '' Ioi a) → ℂ),
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*thetaTailFirstMomentKernel i.val.re j.val.re:ℝ):ℂ)).re-
        2*c*‖∑ i ∈ S, d i*f i.val‖^2 < 0 := by
  have hd : (inner ℂ ((scalarRealization f hf c).kernelSection z)
      ((scalarRealization f hf c).form ((scalarRealization f hf c).kernelSection z))).re < 0 := by
    change ((scalarRealization f hf c).kernel z z).re < 0
    rw [scalarRealization_diagonal f hf c hz]
    exact hneg
  obtain ⟨d, hd⟩ := (scalarRealization f hf c).exists_negative_packet_on_accumulationSet
    (scalarTailSamples f hf c a) hd
  change (∑ i ∈ d.support, ∑ j ∈ d.support,
    star (d j)*d i*(scalarRealization f hf c).kernel i j).re < 0 at hd
  have hk (u v : Complex.ofReal '' Ioi a) :
      (scalarRealization f hf c).kernel u v =
        ((2*thetaTailFirstMomentKernel u.val.re v.val.re:ℝ):ℂ)-
          (2*c:ℂ)*f u.val*star (f v.val) := by
    have hu := (completeThetaSource.tailAccumulationSet a).nodes_subset u.property
    have hv := (completeThetaSource.tailAccumulationSet a).nodes_subset v.property
    rw [scalarRealization_kernel f hf c hu hv]
    obtain ⟨r, hr, he⟩ := u.property
    obtain ⟨s, hs, he'⟩ := v.property
    rw [← he, ← he', Complex.ofReal_re, Complex.ofReal_re,
      completeThetaSource_realization_kernel]
  simp_rw [hk] at hd
  rw [finite_scalar_subtraction_energy] at hd
  exact ⟨d.support, d, hd⟩


theorem finite_real_subtraction_energy {ι : Type*} (S : Finset ι) (d : ι → ℂ)
    (K H : ι → ι → ℝ) (c : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*(K i j-c*H i j):ℝ):ℂ)).re =
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*K i j:ℝ):ℂ)).re-
        2*c*(∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*(H i j:ℂ)).re := by
  have he : (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*(K i j-c*H i j):ℝ):ℂ)) =
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*K i j:ℝ):ℂ))-
        (2*c:ℂ)*(∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*(H i j:ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  rw [he, Complex.sub_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero]

theorem negative_reflected_tail_packet {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ∃ (S : Finset (Complex.ofReal '' Ioi a)) (b : (Complex.ofReal '' Ioi a) → ℝ),
      ∑ i ∈ S, ∑ j ∈ S, b i*b j*(thetaTailFirstMomentKernel i.val.re j.val.re-
        c*reflectedReference i.val.re j.val.re) < 0 := by
  obtain ⟨z, hz, hneg⟩ := exists_negative_reflected_comparison_diagonal hc
  let B := conj (reflectedRate z)
  have hB : 0 < B.re := by simpa [B] using reflectedRate_re_pos hz
  have hq := reflectedRate_re_pos hz
  have hscale : 2*(2*c*B.re)*‖poleFeature B z‖^2 =
      c*‖thetaCuspStripSource z‖^2/(reflectedRate z).re := by
    dsimp only [B]
    rw [Complex.conj_re, poleFeature_matched_norm_sq hz]
    field_simp
    ring
  have hscalar : (completeThetaSource.realization.kernel z z).re-
      2*(2*c*B.re)*‖poleFeature B z‖^2 < 0 := by rw [hscale]; exact hneg
  obtain ⟨S, d, hd⟩ := negative_scalar_tail_packet (poleFeature B) (poleFeature_analytic hB)
    (2*c*B.re) a hz hscalar
  have hreal (i : Complex.ofReal '' Ioi a) : (i.val.re:ℂ)=i.val := by
    obtain ⟨x, hx, he⟩ := i.property
    rw [← he, Complex.ofReal_re]
  have hproj := source_projection_bound S (fun i => i.val.re) d hB
  simp_rw [hreal] at hproj
  have hle := mul_le_mul_of_nonneg_left hproj (show 0 ≤ 2*c by positivity)
  have hneg' :
      (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*((2*thetaTailFirstMomentKernel i.val.re j.val.re:ℝ):ℂ)).re-
        2*c*(∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*(reflectedReference i.val.re j.val.re:ℂ)).re < 0 := by
    nlinarith only [hd, hle]
  have hp : (∑ i ∈ S, ∑ j ∈ S, star (d j)*d i*
      ((2*(thetaTailFirstMomentKernel i.val.re j.val.re-
        c*reflectedReference i.val.re j.val.re):ℝ):ℂ)).re < 0 := by
    rw [finite_real_subtraction_energy]
    exact hneg'
  obtain ⟨b, hb⟩ := real_packet_of_negative_complex_packet S
    (fun i j => thetaTailFirstMomentKernel i.val.re j.val.re-
      c*reflectedReference i.val.re j.val.re) d hp
  exact ⟨S, b, hb⟩


/-- Any scalar comparison valid on a real tail must obey every complex strip
boundary test. This retains the actual full-source realization. -/
theorem scalar_boundary_admissibility (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f thetaCuspStrip) (c a : ℝ)
    (hpack : ∀ (S : Finset (Complex.ofReal '' Ioi a)) (d : (Complex.ofReal '' Ioi a) → ℂ),
      2*c*‖∑ i ∈ S, d i*f i.val‖^2 ≤
        (∑ i ∈ S, ∑ j ∈ S,
          star (d j)*d i*((2*thetaTailFirstMomentKernel i.val.re j.val.re:ℝ):ℂ)).re)
    {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    2*c*‖f z‖^2 ≤ (completeThetaSource.realization.kernel z z).re := by
  by_contra h
  have hn : (completeThetaSource.realization.kernel z z).re-2*c*‖f z‖^2 < 0 := by
    linarith only [lt_of_not_ge h]
  obtain ⟨S, d, hd⟩ := negative_scalar_tail_packet f hf c a hz hn
  exact (not_lt_of_ge (sub_nonneg.mpr (hpack S d))) hd

/-- A source Cauchy comparison cannot have rates approaching zero at the
charged points: its necessary complex diagonal bound imposes this positive floor. -/
theorem chargedPoint_boundary_rate_floor {c u : ℝ} (hc : 0 < c) (hu : 0 < u)
    (N : ℕ) (hN : 0 < N)
    (hcomp : c*‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2 ≤
      u*(completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
        (chargedPoint (1/(N:ℝ)^2))).re) :
    c*(12*Real.pi^2*Real.exp (-4*Real.pi))^2/(24*486^2) ≤ u := by
  let A := 12*Real.pi^2*Real.exp (-4*Real.pi)
  let D : ℝ := 24*486^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by norm_num [D]
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hp := chargedPoint_source_lower N hN
  have hp2 : A^2*(N:ℝ)^10 ≤ ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ A*(N:ℝ)^5) hp 2
    simpa only [mul_pow, ← pow_mul] using h
  have hk := chargedPoint_kernel_diagonal_upper N hN
  have hle := ((mul_le_mul_of_nonneg_left hp2 hc.le).trans hcomp).trans
    (mul_le_mul_of_nonneg_left hk hu.le)
  have he : (c*A^2)*(N:ℝ)^10 ≤ (u*D)*(N:ℝ)^10 := by
    change c*(A^2*(N:ℝ)^10) ≤ u*(D*(N:ℝ)^10) at hle
    simpa only [mul_assoc] using hle
  have hcancel := (mul_le_mul_iff_left₀ (show 0 < (N:ℝ)^10 by positivity)).mp he
  change c*A^2/D ≤ u
  rw [div_le_iff₀ hD]
  exact hcancel

/-- No positive reflection-compatible Cauchy reserve survives at every rank
on any real tail. This does not assert negativity of the unsubtracted kernel. -/
theorem exists_finite_negative_reflected_reserve {c : ℝ} (hc : 0 < c) (a : ℝ) :
    ∃ (n : ℕ) (x b : Fin n → ℝ), (∀ i, a < x i) ∧
      (∑ i, ∑ j, b i*b j*(thetaTailFirstMomentKernel (x i) (x j)-
        c*reflectedReference (x i) (x j))) < 0 := by
  classical
  obtain ⟨S, b, hb⟩ := negative_reflected_tail_packet hc a
  let K := fun x y => thetaTailFirstMomentKernel x y-c*reflectedReference x y
  let e := S.equivFin.symm
  let t : Fin S.card → ℝ := fun i => (e i).val.val.re
  let d : Fin S.card → ℝ := fun i => b (e i).val
  refine ⟨S.card, t, d, ?_, ?_⟩
  · intro i
    obtain ⟨r, hr, he⟩ := (e i).val.property
    change a < (e i).val.val.re
    rw [← he, Complex.ofReal_re]
    exact hr
  · have hi (z : Complex.ofReal '' Ioi a) :
        (∑ j, b z*d j*K z.val.re (t j)) =
          ∑ w ∈ S, b z*b w*K z.val.re w.val.re := by
      dsimp [d, t, e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun w : S => b z*b w.val*K z.val.re w.val.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun w => b z*b w*K z.val.re w.val.re)]
    have he : (∑ i, ∑ j, d i*d j*K (t i) (t j)) =
        ∑ z ∈ S, ∑ w ∈ S, b z*b w*K z.val.re w.val.re := by
      change (∑ i, ∑ j, b (e i).val*d j*K (e i).val.val.re (t j)) = _
      simp_rw [hi]
      dsimp [e]
      rw [Equiv.sum_comp S.equivFin.symm
        (fun z : S => ∑ w ∈ S, b z.val*b w*K z.val.val.re w.val.re),
        Finset.univ_eq_attach,
        Finset.sum_attach S (fun z => ∑ w ∈ S, b z*b w*K z.val.re w.val.re)]
    exact he ▸ hb

end RHTower.ThetaCuspBoundaryAudit
