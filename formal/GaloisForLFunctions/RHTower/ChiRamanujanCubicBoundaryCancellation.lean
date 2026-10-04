import GaloisForLFunctions.RHTower.ChiRamanujanCubicIntersectionMass
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform cancellation in the actual BAG critical cubic source

Second derivatives on compact parameter/frequency boxes control the literal reflected
axis and mixed numerators. The bounds retain the complete moving zeta/Euler source and
both contractions. They provide the cancellations needed for the finite-part and mixed-PV
boundary limits; no physical prime-source transfer is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace RHTower.BAGTrace

private theorem norm_rectangular_difference_le
    {f : (Fin 3 → ℝ) → ℂ} {S : Set (Fin 3 → ℝ)} {C : ℝ}
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hdf : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hb : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C)
    (hS : Convex ℝ S) (x h k : Fin 3 → ℝ)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, x+t•k ∈ S ∧ x+t•k+h ∈ S) :
    ‖f (x+k+h)-f (x+k)-f (x+h)+f x‖ ≤ C*‖h‖*‖k‖ := by
  let g : ℝ → ℂ := fun t => f (x+t•k+h)-f (x+t•k)
  let d : ℝ → ℂ := fun t => (fderiv ℝ f (x+t•k+h)-fderiv ℝ f (x+t•k)) k
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (d t) t := by
    have hpath : HasDerivAt (fun s : ℝ => x+s•k) k t := by
      simpa using ((hasDerivAt_id t).smul_const k).const_add x
    have ha := (hf _ (hp t ht).2).hasFDerivAt.comp_hasDerivAt t (hpath.add_const h)
    have hb' := (hf _ (hp t ht).1).hasFDerivAt.comp_hasDerivAt t hpath
    convert ha.sub hb' using 1 <;> rfl
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖d t‖ ≤ C*‖h‖*‖k‖ := by
    have hdiff := hS.norm_image_sub_le_of_norm_fderiv_le hdf hb (hp t ht).1 (hp t ht).2
    simp only [add_sub_cancel_left] at hdiff
    exact (ContinuousLinearMap.le_opNorm _ k).trans
      (mul_le_mul_of_nonneg_right hdiff (norm_nonneg k))
  have hres := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hg t ht).hasDerivWithinAt) hd
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simp only [g, one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one] at hres
  convert hres using 1
  congr 1
  abel

/-- The closed parameter/frequency box used for actual critical boundary tests. -/
def cubicCriticalBox (R : ℝ) : Set (Fin 3 → ℝ) := Icc ![1,-R,-R] ![2,R,R]

private theorem criticalBox_sigma {R : ℝ} {w : Fin 3 → ℝ} (hw : w ∈ cubicCriticalBox R) :
    1 ≤ w 0 := hw.1 0

private theorem criticalBox_mem {R σ u v : ℝ} (hσ : σ ∈ Icc (1 : ℝ) 2)
    (hu : u ∈ Icc (-R) R) (hv : v ∈ Icc (-R) R) :
    ![σ,u,v] ∈ cubicCriticalBox R := by
  constructor <;> intro i <;> fin_cases i <;> simp_all

private theorem criticalBox_convex (R : ℝ) : Convex ℝ (cubicCriticalBox R) := convex_Icc _ _

private theorem criticalBox_compact (R : ℝ) : IsCompact (cubicCriticalBox R) := isCompact_Icc

/-- Actual complete cubic source tested against a smooth profile. -/
def cubicTestedSource (Φ : ℝ × ℝ → ℂ) (w : Fin 3 → ℝ) : ℂ :=
  realCubicSource (w 0) (w 1) (w 2) * Φ (w 1,w 2)

/-- First literal finite-part numerator, including its moving contraction. -/
def cubicTestedAxisNumerator (Φ : ℝ × ℝ → ℂ) (w : Fin 3 → ℝ) : ℂ :=
  (realCubicSource (w 0) (w 1) (w 2)-realAxisSource (w 0) (w 1))*Φ (w 1,w 2)

private theorem contDiff_testEmbedding : ContDiff ℝ ∞ (fun w : Fin 3 → ℝ => (w 1,w 2)) :=
  (contDiff_apply ℝ ℝ 1).prodMk (contDiff_apply ℝ ℝ 2)

private theorem contDiff_axisEmbedding : ContDiff ℝ ∞ (fun w : Fin 3 → ℝ => ![w 0,w 1]) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> exact contDiff_apply ℝ ℝ _

theorem contDiffAt_cubicTestedSource {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {w : Fin 3 → ℝ} (hσ : 1 ≤ w 0) : ContDiffAt ℝ ∞ (cubicTestedSource Φ) w :=
  (contDiffAt_realCubicSource hσ).mul (hΦ.comp contDiff_testEmbedding).contDiffAt

theorem contDiffAt_cubicTestedAxisNumerator {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    {w : Fin 3 → ℝ} (hσ : 1 ≤ w 0) : ContDiffAt ℝ ∞ (cubicTestedAxisNumerator Φ) w := by
  have ha := (contDiffAt_realAxisSource (w := ![w 0,w 1]) hσ).comp w
    contDiff_axisEmbedding.contDiffAt
  exact ((contDiffAt_realCubicSource hσ).sub ha).mul
    (hΦ.comp contDiff_testEmbedding).contDiffAt

private theorem compact_second_derivative_bound {f : (Fin 3 → ℝ) → ℂ} {R : ℝ}
    (hf : ∀ w ∈ cubicCriticalBox R, ContDiffAt ℝ ∞ f w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ cubicCriticalBox R, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ C := by
  have hc : ContinuousOn (fun w => ‖fderiv ℝ (fderiv ℝ f) w‖) (cubicCriticalBox R) := by
    intro w hw
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) w := (hf w hw).fderiv_right (by simp)
    exact (hd.continuousAt_fderiv (by simp)).norm.continuousWithinAt
  obtain ⟨C,hC⟩ := (criticalBox_compact R).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
  have h := hC w hw
  change |‖fderiv ℝ (fderiv ℝ f) w‖| ≤ C at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))


private theorem norm_u_vector_le {u : ℝ} (hu : 0 ≤ u) : ‖(![0,u,0] : Fin 3 → ℝ)‖ ≤ u := by
  apply (pi_norm_le_iff_of_nonneg hu).2
  intro i
  fin_cases i <;> simp [Real.norm_eq_abs, abs_of_nonneg hu, hu]

private theorem norm_v_vector_le {v : ℝ} (hv : 0 ≤ v) : ‖(![0,0,v] : Fin 3 → ℝ)‖ ≤ v := by
  apply (pi_norm_le_iff_of_nonneg hv).2
  intro i
  fin_cases i <;> simp [Real.norm_eq_abs, abs_of_nonneg hv, hv]

private theorem norm_mixed_difference_on_box {f : (Fin 3 → ℝ) → ℂ} {R C : ℝ}
    (hf : ∀ w ∈ cubicCriticalBox R, ContDiffAt ℝ ∞ f w) (hC : 0 ≤ C)
    (hb : ∀ w ∈ cubicCriticalBox R, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ C)
    {σ u v : ℝ} (hσ : σ ∈ Icc (1 : ℝ) 2) (hu : u ∈ Icc (0 : ℝ) R)
    (hv : v ∈ Icc (0 : ℝ) R) :
    ‖f ![σ,u,v]-f ![σ,-u,v]-f ![σ,u,-v]+f ![σ,-u,-v]‖ ≤ (4*C)*u*v := by
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ![σ,-u,-v]+t•![0,0,2*v] ∈ cubicCriticalBox R ∧
      ![σ,-u,-v]+t•![0,0,2*v]+![0,2*u,0] ∈ cubicCriticalBox R := by
    have hv' : -v+t*(2*v) ∈ Icc (-R) R := by
      constructor
      · nlinarith [hv.2, mul_nonneg ht.1 hv.1]
      · nlinarith [hv.2, mul_nonneg (sub_nonneg.mpr ht.2) hv.1]
    have e1 : (![σ,-u,-v]+t•![0,0,2*v] : Fin 3 → ℝ) = ![σ,-u,-v+t*(2*v)] := by
      ext i; fin_cases i <;> simp
    have e2 : (![σ,-u,-v]+t•![0,0,2*v]+![0,2*u,0] : Fin 3 → ℝ) = ![σ,u,-v+t*(2*v)] := by
      ext i; fin_cases i <;> simp
      all_goals ring
    rw [e2,e1]
    exact ⟨criticalBox_mem hσ ⟨by linarith [hu.1,hu.2],by linarith [hu.1,hu.2]⟩ hv',
      criticalBox_mem hσ ⟨by linarith [hu.1,hu.2],hu.2⟩ hv'⟩
  have h := norm_rectangular_difference_le
    (fun w hw => (hf w hw).differentiableAt (by simp))
    (fun w hw => ((hf w hw).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    hb (criticalBox_convex R) ![σ,-u,-v] ![0,2*u,0] ![0,0,2*v] hpath
  have e1 : (![σ,-u,-v]+![0,0,2*v]+![0,2*u,0] : Fin 3 → ℝ) = ![σ,u,v] := by
    ext i; fin_cases i <;> simp <;> ring
  have e2 : (![σ,-u,-v]+![0,0,2*v] : Fin 3 → ℝ) = ![σ,-u,v] := by
    ext i; fin_cases i <;> simp
    ring
  have e3 : (![σ,-u,-v]+![0,2*u,0] : Fin 3 → ℝ) = ![σ,u,-v] := by
    ext i; fin_cases i <;> simp
    ring
  rw [e1,e2,e3] at h
  refine h.trans ?_
  calc C*‖(![0,2*u,0] : Fin 3 → ℝ)‖*‖(![0,0,2*v] : Fin 3 → ℝ)‖
      ≤ C*(2*u)*(2*v) := by
        have huN := norm_u_vector_le (u := 2*u) (mul_nonneg zero_le_two hu.1)
        have hvN := norm_v_vector_le (v := 2*v) (mul_nonneg zero_le_two hv.1)
        exact mul_le_mul (mul_le_mul_of_nonneg_left huN hC) hvN
          (norm_nonneg _) (mul_nonneg hC (mul_nonneg zero_le_two hu.1))
    _ = (4*C)*u*v := by ring

/-- Literal four-reflection numerator of the complete tested cubic source. -/
def cubicMixedDifference (Φ : ℝ × ℝ → ℂ) (σ : ℝ) (w : ℝ × ℝ) : ℂ :=
  cubicTestedSource Φ ![σ,w.1,w.2]-cubicTestedSource Φ ![σ,-w.1,w.2]-
    cubicTestedSource Φ ![σ,w.1,-w.2]+cubicTestedSource Φ ![σ,-w.1,-w.2]

/-- Simultaneous axis cancellation of the actual moving source, uniform on compact boxes. -/
theorem exists_bound_cubicMixedDifference {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (0 : ℝ) R,
      ∀ v ∈ Icc (0 : ℝ) R, ‖cubicMixedDifference Φ σ (u,v)‖ ≤ C*u*v := by
  have hf := fun w (hw : w ∈ cubicCriticalBox R) =>
    contDiffAt_cubicTestedSource hΦ (criticalBox_sigma hw)
  obtain ⟨C,hC,hb⟩ := compact_second_derivative_bound hf
  refine ⟨4*C, by positivity, fun σ hσ u hu v hv => ?_⟩
  exact norm_mixed_difference_on_box hf hC hb hσ hu hv


private theorem norm_axis_difference_on_box {f : (Fin 3 → ℝ) → ℂ} {R C : ℝ}
    (hf : ∀ w ∈ cubicCriticalBox R, ContDiffAt ℝ ∞ f w) (hC : 0 ≤ C)
    (hb : ∀ w ∈ cubicCriticalBox R, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ C)
    {σ u v : ℝ} (hσ : σ ∈ Icc (1 : ℝ) 2) (hu : u ∈ Icc (0 : ℝ) R)
    (hv : v ∈ Icc (-R) R) (hf0 : f ![σ,0,v] = 0) :
    ‖f ![σ,u,v]+f ![σ,-u,v]‖ ≤ C*u^2 := by
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ![σ,-u,v]+t•![0,u,0] ∈ cubicCriticalBox R ∧
      ![σ,-u,v]+t•![0,u,0]+![0,u,0] ∈ cubicCriticalBox R := by
    have htu0 : 0 ≤ t*u := mul_nonneg ht.1 hu.1
    have htu1 : t*u ≤ u := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hu.1]
    have e1 : (![σ,-u,v]+t•![0,u,0] : Fin 3 → ℝ) = ![σ,-u+t*u,v] := by
      ext i; fin_cases i <;> simp
    have e2 : (![σ,-u,v]+t•![0,u,0]+![0,u,0] : Fin 3 → ℝ) = ![σ,t*u,v] := by
      ext i; fin_cases i <;> simp
    rw [e2,e1]
    exact ⟨criticalBox_mem hσ ⟨by linarith [hu.2],by linarith [hu.1,hu.2]⟩ hv,
      criticalBox_mem hσ ⟨by linarith [hu.1,hu.2],by linarith [hu.2]⟩ hv⟩
  have h := norm_rectangular_difference_le
    (fun w hw => (hf w hw).differentiableAt (by simp))
    (fun w hw => ((hf w hw).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    hb (criticalBox_convex R) ![σ,-u,v] ![0,u,0] ![0,u,0] hpath
  have e1 : (![σ,-u,v]+![0,u,0]+![0,u,0] : Fin 3 → ℝ) = ![σ,u,v] := by
    ext i; fin_cases i <;> simp
  have e2 : (![σ,-u,v]+![0,u,0] : Fin 3 → ℝ) = ![σ,0,v] := by
    ext i; fin_cases i <;> simp
  rw [e1,e2,hf0,sub_zero,sub_zero] at h
  refine h.trans ?_
  have huN := norm_u_vector_le hu.1
  calc C*‖(![0,u,0] : Fin 3 → ℝ)‖*‖(![0,u,0] : Fin 3 → ℝ)‖
      ≤ C*u*u := mul_le_mul (mul_le_mul_of_nonneg_left huN hC) huN
        (norm_nonneg _) (mul_nonneg hC hu.1)
    _ = C*u^2 := by ring

/-- Reflected first finite-part numerator of the actual complete source. -/
def cubicAxisDifference (Φ : ℝ × ℝ → ℂ) (σ : ℝ) (w : ℝ × ℝ) : ℂ :=
  cubicTestedAxisNumerator Φ ![σ,w.1,w.2]+cubicTestedAxisNumerator Φ ![σ,-w.1,w.2]

/-- The literal contraction subtraction cancels the remaining linear singularity after
reflection, uniformly while sigma approaches one. -/
theorem exists_bound_cubicAxisDifference {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (0 : ℝ) R,
      ∀ v ∈ Icc (-R) R, ‖cubicAxisDifference Φ σ (u,v)‖ ≤ C*u^2 := by
  have hf := fun w (hw : w ∈ cubicCriticalBox R) =>
    contDiffAt_cubicTestedAxisNumerator hΦ (criticalBox_sigma hw)
  obtain ⟨C,hC,hb⟩ := compact_second_derivative_bound hf
  refine ⟨C,hC, fun σ hσ u hu v hv => ?_⟩
  apply norm_axis_difference_on_box hf hC hb hσ hu hv
  change (realCubicSource σ 0 v-realAxisSource σ 0)*Φ (0,v)=0
  rw [realCubicSource_axis_left hσ.1,zero_mul]


private theorem cubicRegularFactor_swap (z U V : ℂ) :
    cubicRegularFactor z U V = cubicRegularFactor z V U := by
  unfold cubicRegularFactor cubicMixedNumerator
  congr 1
  apply congrArg₂ (fun a b : ℂ => a/b) <;> ring

theorem cubicEulerCorrection_swap (σ α β : ℂ) :
    cubicEulerCorrection σ α β = cubicEulerCorrection σ β α := by
  apply tprod_congr
  intro p
  exact cubicRegularFactor_swap _ _ _

theorem regularCubicSource_swap (σ α β : ℂ) :
    regularCubicSource σ α β = regularCubicSource σ β α := by
  unfold regularCubicSource
  rw [cubicEulerCorrection_swap σ α β,
    show β-α = -(α-β) by ring, residuePair_neg]
  ring

theorem realCubicSource_swap (σ u v : ℝ) : realCubicSource σ u v = realCubicSource σ v u :=
  regularCubicSource_swap _ _ _

/-- The second actual finite-part numerator has the corresponding uniform cancellation.
This follows from source symmetry, not an assumed symmetry of the test. -/
theorem exists_bound_cubicOtherAxisDifference {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1 : ℝ) 2, ∀ u ∈ Icc (-R) R,
      ∀ v ∈ Icc (0 : ℝ) R,
      ‖(realCubicSource σ u v-realAxisSource σ v)*Φ (u,v)+
        (realCubicSource σ u (-v)-realAxisSource σ (-v))*Φ (u,-v)‖ ≤ C*v^2 := by
  have hs : ContDiff ℝ ∞ (fun w : ℝ × ℝ => Φ (w.2,w.1)) :=
    hΦ.comp (contDiff_snd.prodMk contDiff_fst)
  obtain ⟨C,hC,hb⟩ := exists_bound_cubicAxisDifference hs R
  refine ⟨C,hC, fun σ hσ u hu v hv => ?_⟩
  have h := hb σ hσ v hv u hu
  dsimp [cubicAxisDifference, cubicTestedAxisNumerator] at h
  rw [realCubicSource_swap σ v u,realCubicSource_swap σ (-v) u] at h
  exact h

end RHTower.BAGTrace
