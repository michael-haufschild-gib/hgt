import GaloisForLFunctions.HTGeometry.SchwartzSecantEnergy
import GaloisForLFunctions.RHTower.ThetaGeometricBoundaryEnergy
import GaloisForLFunctions.RHTower.ThetaTailKernelGeometricDeficitSplit
import GaloisForLFunctions.RHTower.ThetaTailCommonTranslationLoewnerNoGo

/-!
# Positive-node geometric reserve obstruction

The full theta tail kernel minus any positive multiple of its geometric part
has a strictly negative two-point quadratic form on positive real nodes.
The polynomial source channels have bounded confluent secants; the geometric
channel has unbounded secant energy. Moving-cut continuity makes both nodes
strictly positive.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open scoped SchwartzMap
open GaloisForLFunctions.HTGeometry.SchwartzSecantEnergy
namespace RHTower.ThetaGeometricBoundaryAudit

def sourceChannel (c : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => ((t+c:ℝ):ℂ)) thetaCuspSchwartz

lemma sourceChannel_apply (c t : ℝ) :
    sourceChannel c t = (((t+c)*thetaCuspFullSource t:ℝ):ℂ) := by
  have hg : (fun t : ℝ => ((t+c:ℝ):ℂ)).HasTemperateGrowth := by fun_prop
  rw [sourceChannel, SchwartzMap.smulLeftCLM_apply_apply hg,
    thetaCuspSchwartz_apply, smul_eq_mul, Complex.ofReal_mul]

lemma sourceChannel_secant_energy_tendsto (c : ℝ) :
    Tendsto (fun h : ℝ => ∫ t in Ioi (0:ℝ),
      (((t+h+c)*thetaCuspFullSource (t+h)-(t+c)*thetaCuspFullSource t)/h)^2)
      (𝓝[≠] 0) (𝓝 (∫ t in Ioi (0:ℝ), ‖deriv (sourceChannel c) t‖^2)) := by
  convert! schwartz_secant_energy_tendsto (sourceChannel c) using 1
  ext h
  simp only [sourceChannel_apply, ← Complex.ofReal_sub, ← Complex.ofReal_div,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma sourceChannel_secant_bounded (c : ℝ) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ h ∈ Ioo 0 δ,
      (∫ t in Ioi (0:ℝ),
        (((t+h+c)*thetaCuspFullSource (t+h)-(t+c)*thetaCuspFullSource t)/h)^2) < C := by
  have ht := (sourceChannel_secant_energy_tendsto c).mono_left (nhdsGT_le_nhdsNE 0)
  obtain ⟨δ, hδ, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (ht.eventually_lt_const (lt_add_one (∫ t in Ioi (0:ℝ), ‖deriv (sourceChannel c) t‖^2)))
  exact ⟨_, δ, hδ, fun h hh => hb hh⟩

def sourceChannelReal (c : ℝ) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t+c) thetaCuspSchwartzReal

lemma sourceChannelReal_apply (c t : ℝ) :
    sourceChannelReal c t = (t+c)*thetaCuspFullSource t := by
  have hg : (fun t : ℝ => t+c).HasTemperateGrowth := by fun_prop
  rw [sourceChannelReal, SchwartzMap.smulLeftCLM_apply_apply hg,
    thetaCuspSchwartzReal_apply, smul_eq_mul]

lemma sourceChannelReal_shift_memLp (c x : ℝ) :
    MemLp (fun t => (t+x+c)*thetaCuspFullSource (t+x)) 2 volume := by
  have h := (SchwartzMap.translateCLM ℝ x (sourceChannelReal c)).memLp 2 volume
  convert! h using 1
  ext t
  exact (sourceChannelReal_apply c (t+x)).symm

lemma sourceChannelReal_product_integrable (c x y : ℝ) :
    Integrable (fun t => ((t+x+c)*thetaCuspFullSource (t+x))*
      ((t+y+c)*thetaCuspFullSource (t+y))) :=
  (sourceChannelReal_shift_memLp c x).integrable_mul (sourceChannelReal_shift_memLp c y)


def geometricSource (t : ℝ) : ℝ := Real.sqrt t*thetaCuspFullSource t

lemma geometricSource_continuous : Continuous geometricSource :=
  Real.continuous_sqrt.mul thetaCuspSchwartzReal.continuous

lemma geometricSource_shift_memLp (x : ℝ) :
    MemLp (fun t => geometricSource (t+x)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (geometricSource_continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable).mpr
  exact sqrt_source_sq_integrable.comp_add_right x

lemma geometricSource_product_integrable (x y : ℝ) :
    Integrable (fun t => geometricSource (t+x)*geometricSource (t+y)) :=
  (geometricSource_shift_memLp x).integrable_mul (geometricSource_shift_memLp y)

def geometricGram (x y : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), geometricSource (t+x)*geometricSource (t+y)

lemma geometricKernel_eq_gram {x y : ℝ} (hx : 0 ≤ x) (_hy : 0 ≤ y) :
    thetaTailGeometricKernel x y = geometricGram x y := by
  unfold thetaTailGeometricKernel geometricGram
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hxt : 0 ≤ x+t := add_nonneg hx ht.le
  dsimp only
  rw [Real.sqrt_mul hxt]
  simp only [geometricSource, add_comm t x, add_comm t y]
  ring

lemma geometricGram_secant (h : ℝ) :
    (geometricGram h h-2*geometricGram h 0+geometricGram 0 0)/h^2 =
      ∫ t in Ioi (0:ℝ), ((geometricSource (t+h)-geometricSource t)/h)^2 := by
  have haa := (geometricSource_product_integrable h h).integrableOn (s := Ioi (0:ℝ))
  have hab : IntegrableOn (fun t => geometricSource (t+h)*geometricSource t) (Ioi (0:ℝ)) := by
    simpa only [add_zero] using (geometricSource_product_integrable h 0).integrableOn (s := Ioi (0:ℝ))
  have hbb : IntegrableOn (fun t => geometricSource t*geometricSource t) (Ioi (0:ℝ)) := by
    simpa only [add_zero] using (geometricSource_product_integrable 0 0).integrableOn (s := Ioi (0:ℝ))
  have hsub : IntegrableOn (fun t => geometricSource (t+h)*geometricSource (t+h)-
      2*(geometricSource (t+h)*geometricSource t)) (Ioi (0:ℝ)) := haa.sub (hab.const_mul 2)
  have hp : (∫ t in Ioi (0:ℝ), (geometricSource (t+h)-geometricSource t)^2) =
      geometricGram h h-2*geometricGram h 0+geometricGram 0 0 := by
    calc
      _ = ∫ t in Ioi (0:ℝ),
          (geometricSource (t+h)*geometricSource (t+h)-
            2*(geometricSource (t+h)*geometricSource t))+geometricSource t*geometricSource t := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = _ := by
        rw [integral_add hsub hbb,
          integral_sub haa (hab.const_mul 2), integral_const_mul]
        simp only [geometricGram, add_zero]
  rw [← hp]
  simp only [div_pow, integral_div]


def sourceChannelGram (c x y : ℝ) : ℝ :=
  ∫ t in Ioi (0:ℝ), ((t+x+c)*thetaCuspFullSource (t+x))*
    ((t+y+c)*thetaCuspFullSource (t+y))

lemma sourceChannelGram_secant (c h : ℝ) :
    (sourceChannelGram c h h-2*sourceChannelGram c h 0+sourceChannelGram c 0 0)/h^2 =
      ∫ t in Ioi (0:ℝ),
        (((t+h+c)*thetaCuspFullSource (t+h)-(t+c)*thetaCuspFullSource t)/h)^2 := by
  let a : ℝ → ℝ := fun t => (t+h+c)*thetaCuspFullSource (t+h)
  let b : ℝ → ℝ := fun t => (t+c)*thetaCuspFullSource t
  have haa : IntegrableOn (fun t => a t*a t) (Ioi (0:ℝ)) :=
    (sourceChannelReal_product_integrable c h h).integrableOn
  have hab : IntegrableOn (fun t => a t*b t) (Ioi (0:ℝ)) := by
    simpa only [add_zero] using (sourceChannelReal_product_integrable c h 0).integrableOn
  have hbb : IntegrableOn (fun t => b t*b t) (Ioi (0:ℝ)) := by
    simpa only [add_zero] using (sourceChannelReal_product_integrable c 0 0).integrableOn
  have hsub : IntegrableOn (fun t => a t*a t-2*(a t*b t)) (Ioi (0:ℝ)) :=
    haa.sub (hab.const_mul 2)
  have hp : (∫ t in Ioi (0:ℝ), (a t-b t)^2) =
      sourceChannelGram c h h-2*sourceChannelGram c h 0+sourceChannelGram c 0 0 := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (a t*a t-2*(a t*b t))+b t*b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = _ := by
        rw [integral_add hsub hbb,
          integral_sub haa (hab.const_mul 2), integral_const_mul]
        simp only [sourceChannelGram, a, b, add_zero]
  rw [← hp]
  simp only [div_pow, integral_div, a, b]

lemma kernel_eq_sourceChannelGram (x y : ℝ) :
    thetaTailFirstMomentKernel x y =
      (1/2:ℝ)*(sourceChannelGram 1 x y-sourceChannelGram (-1) x y) := by
  rw [thetaTailFirstMomentKernel_eq_kreinDifference (c := 1) zero_lt_one]
  unfold sourceChannelGram
  rw [← integral_sub (sourceChannelReal_product_integrable 1 x y).integrableOn
    (sourceChannelReal_product_integrable (-1) x y).integrableOn]
  simp only [mul_one]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [thetaTailKreinPlus, thetaTailKreinMinus, sub_eq_add_neg,
    add_comm x s, add_comm y s]

lemma kernel_secant_eq (h : ℝ) :
    (thetaTailFirstMomentKernel h h-2*thetaTailFirstMomentKernel h 0+
      thetaTailFirstMomentKernel 0 0)/h^2 = (1/2:ℝ)*
      ((∫ t in Ioi (0:ℝ),
        (((t+h+1)*thetaCuspFullSource (t+h)-(t+1)*thetaCuspFullSource t)/h)^2)-
       (∫ t in Ioi (0:ℝ),
        (((t+h+(-1))*thetaCuspFullSource (t+h)-(t+(-1))*thetaCuspFullSource t)/h)^2)) := by
  rw [kernel_eq_sourceChannelGram, kernel_eq_sourceChannelGram, kernel_eq_sourceChannelGram,
    ← sourceChannelGram_secant, ← sourceChannelGram_secant]
  ring

lemma kernel_secant_tendsto :
    Tendsto (fun h : ℝ =>
      (thetaTailFirstMomentKernel h h-2*thetaTailFirstMomentKernel h 0+
        thetaTailFirstMomentKernel 0 0)/h^2) (𝓝[≠] 0)
      (𝓝 ((1/2:ℝ)*((∫ t in Ioi (0:ℝ), ‖deriv (sourceChannel 1) t‖^2)-
        (∫ t in Ioi (0:ℝ), ‖deriv (sourceChannel (-1)) t‖^2)))) := by
  have ht := ((sourceChannel_secant_energy_tendsto 1).sub
    (sourceChannel_secant_energy_tendsto (-1))).const_mul (1/2:ℝ)
  exact ht.congr (fun h => (kernel_secant_eq h).symm)

lemma kernel_secant_bounded :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ h ∈ Ioo 0 δ,
      (thetaTailFirstMomentKernel h h-2*thetaTailFirstMomentKernel h 0+
        thetaTailFirstMomentKernel 0 0)/h^2 < C := by
  have ht := kernel_secant_tendsto.mono_left (nhdsGT_le_nhdsNE 0)
  obtain ⟨δ, hδ, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (ht.eventually_lt_const (lt_add_one _))
  exact ⟨_, δ, hδ, fun h hh => hb hh⟩

lemma exists_negative_boundary_geometric_reserve {ε : ℝ} (hε : 0 < ε) :
    ∃ h > 0,
      (thetaTailFirstMomentKernel h h-ε*thetaTailGeometricKernel h h)-
        2*(thetaTailFirstMomentKernel h 0-ε*thetaTailGeometricKernel h 0)+
        (thetaTailFirstMomentKernel 0 0-ε*thetaTailGeometricKernel 0 0) < 0 := by
  obtain ⟨C, δ, hδ, hK⟩ := kernel_secant_bounded
  obtain ⟨h, hh, hG⟩ := exists_large_geometric_secant (C/ε) hδ
  refine ⟨h, hh.1, ?_⟩
  have hgq : C/ε < (thetaTailGeometricKernel h h-2*thetaTailGeometricKernel h 0+
      thetaTailGeometricKernel 0 0)/h^2 := by
    rw [geometricKernel_eq_gram hh.1.le hh.1.le,
      geometricKernel_eq_gram hh.1.le le_rfl, geometricKernel_eq_gram le_rfl le_rfl,
      geometricGram_secant]
    exact hG
  have hstrict := (div_lt_iff₀ hε).mp hgq
  have hquot :
      (thetaTailFirstMomentKernel h h-2*thetaTailFirstMomentKernel h 0+
        thetaTailFirstMomentKernel 0 0)/h^2-
      ε*((thetaTailGeometricKernel h h-2*thetaTailGeometricKernel h 0+
        thetaTailGeometricKernel 0 0)/h^2) < 0 := by
    apply sub_neg.mpr
    exact (hK h hh).trans (by simpa only [mul_comm] using hstrict)
  have heq :
      ((thetaTailFirstMomentKernel h h-ε*thetaTailGeometricKernel h h)-
        2*(thetaTailFirstMomentKernel h 0-ε*thetaTailGeometricKernel h 0)+
        (thetaTailFirstMomentKernel 0 0-ε*thetaTailGeometricKernel 0 0))/h^2 =
      (thetaTailFirstMomentKernel h h-2*thetaTailFirstMomentKernel h 0+
        thetaTailFirstMomentKernel 0 0)/h^2-
      ε*((thetaTailGeometricKernel h h-2*thetaTailGeometricKernel h 0+
        thetaTailGeometricKernel 0 0)/h^2) := by ring
  rw [← heq] at hquot
  simpa only [zero_mul] using (div_lt_iff₀ (sq_pos_of_pos hh.1)).mp hquot


lemma geometricGram_commonShift_eq_tail (a x y : ℝ) :
    geometricGram (x+a) (y+a) =
      ∫ t in Ioi a, geometricSource (t+x)*geometricSource (t+y) := by
  unfold geometricGram
  rw [← setIntegral_Ioi_zero_comp_add_right
    (fun t => geometricSource (t+x)*geometricSource (t+y)) a]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [show t+(x+a) = t+a+x by ring, show t+(y+a) = t+a+y by ring]

lemma continuous_geometricGram_commonShift (x y : ℝ) :
    Continuous (fun a => geometricGram (x+a) (y+a)) := by
  simpa only [geometricGram_commonShift_eq_tail] using
    continuous_tail (geometricSource_product_integrable x y)

lemma continuous_kernel_commonShift (x y : ℝ) :
    Continuous (fun a => thetaTailFirstMomentKernel (x+a) (y+a)) :=
  continuous_iff_continuousAt.mpr fun a =>
    (hasDerivAt_thetaTailFirstMomentKernel_commonShift a x y).continuousAt

lemma exists_negative_positive_geometric_reserve {ε : ℝ} (hε : 0 < ε) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      (thetaTailFirstMomentKernel x x-ε*thetaTailGeometricKernel x x)-
        2*(thetaTailFirstMomentKernel x y-ε*thetaTailGeometricKernel x y)+
        (thetaTailFirstMomentKernel y y-ε*thetaTailGeometricKernel y y) < 0 := by
  obtain ⟨h, hh, hneg⟩ := exists_negative_boundary_geometric_reserve hε
  let q : ℝ → ℝ := fun a =>
    (thetaTailFirstMomentKernel (h+a) (h+a)-ε*geometricGram (h+a) (h+a))-
      2*(thetaTailFirstMomentKernel (h+a) (0+a)-ε*geometricGram (h+a) (0+a))+
      (thetaTailFirstMomentKernel (0+a) (0+a)-ε*geometricGram (0+a) (0+a))
  have hc : Continuous q :=
    ((continuous_kernel_commonShift h h).sub
      ((continuous_geometricGram_commonShift h h).const_mul ε)).sub
      (((continuous_kernel_commonShift h 0).sub
        ((continuous_geometricGram_commonShift h 0).const_mul ε)).const_mul 2) |>.add
      ((continuous_kernel_commonShift 0 0).sub
        ((continuous_geometricGram_commonShift 0 0).const_mul ε))
  have hq : q 0 < 0 := by
    dsimp [q]
    simpa only [add_zero, geometricKernel_eq_gram hh.le hh.le,
      geometricKernel_eq_gram hh.le le_rfl, geometricKernel_eq_gram le_rfl le_rfl] using hneg
  have he : ∀ᶠ a in 𝓝[>] (0:ℝ), q a < 0 :=
    (hc.continuousAt.tendsto.eventually (Iio_mem_nhds hq)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ a : ℝ in 𝓝[>] (0:ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, hqa⟩ := (hp.and he).exists
  have hha : 0 < h+a := add_pos hh ha
  refine ⟨h+a, a, hha, ha, ?_⟩
  rw [geometricKernel_eq_gram hha.le hha.le,
    geometricKernel_eq_gram hha.le ha.le, geometricKernel_eq_gram ha.le ha.le]
  simpa only [q, zero_add] using hqa

/-- Every positive geometric subtraction has a finite real negative packet on positive nodes. -/
lemma exists_negative_positive_packet {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Fin 2 → ℝ, (∀ i, 0 < x i) ∧ ∃ b : Fin 2 → ℝ,
      (∑ i, ∑ j, b i*b j*(thetaTailFirstMomentKernel (x i) (x j)-
        ε*thetaTailGeometricKernel (x i) (x j))) < 0 := by
  obtain ⟨p, q, hp, hq, hneg⟩ := exists_negative_positive_geometric_reserve hε
  refine ⟨![p, q], ?_, ![1, -1], ?_⟩
  · intro i
    fin_cases i
    · exact hp
    · exact hq
  · norm_num only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      one_mul, mul_one, neg_mul, neg_neg]
    rw [thetaTailFirstMomentKernel_comm q p, thetaTailGeometricKernel_comm q p]
    linarith only [hneg]

end RHTower.ThetaGeometricBoundaryAudit
