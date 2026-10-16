import GaloisForLFunctions.RHTower.EvenSectorScalarizationMoments

/-!
# Positive smooth correction of a finite arithmetic defect

The signed coordinate rays are actual smooth even pole-free sources. Their
positive hull repairs any finitely supported trace. On each fixed coordinate
set the correction profile and energy vanish as the defect tends to zero.
-/

open Complex MeasureTheory Set Finsupp Filter Topology Zeta23
open scoped ContDiff
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided SeparatedBump

theorem contDiff_evenPolarProfile_infty (j : ℕ) : ContDiff ℝ ∞ (evenPolarProfile j) :=
  (nodeBump j).contDiff.sub (contDiff_const.mul
    (((nodeBump j).contDiff.comp (contDiff_id.sub contDiff_const)).add
      ((nodeBump j).contDiff.comp (contDiff_id.add contDiff_const))))

theorem contDiff_oddPolarProfile_infty (j : ℕ) : ContDiff ℝ ∞ (oddPolarProfile j) := by
  have h₁ : ∀ c : ℝ,ContDiff ℝ ∞ (fun v => nodeBump j (v-c)) :=
    fun _ => (nodeBump j).contDiff.comp (contDiff_id.sub contDiff_const)
  have h₂ : ∀ c : ℝ,ContDiff ℝ ∞ (fun v => nodeBump j (v+c)) :=
    fun _ => (nodeBump j).contDiff.comp (contDiff_id.add contDiff_const)
  exact (((h₁ _).sub (h₂ _)).sub (contDiff_const.mul ((h₁ _).sub (h₂ _)))).div_const _

theorem contDiff_bumpSum_infty {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {N : ℕ} (a x : Fin N → ℝ) : ContDiff ℝ ∞ (bumpSum φ a x) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (hφ.comp (contDiff_id.sub contDiff_const))

def smoothPolarPlus (j : ℕ) : SmoothEvenPolarTestFn :=
  ⟨evenPolarNodeTest j,Complex.ofRealCLM.contDiff.comp
    (contDiff_bumpSum_infty (contDiff_evenPolarProfile_infty j)
      ![1,1] ![Real.log j/2,-(Real.log j/2)])⟩

def smoothPolarMinus (j : ℕ) : SmoothEvenPolarTestFn :=
  ⟨evenPolarMinusTest j,Complex.ofRealCLM.contDiff.comp
    (contDiff_bumpSum_infty (contDiff_oddPolarProfile_infty j)
      ![1,-1] ![Real.log j/2,-(Real.log j/2)])⟩

theorem exists_smooth_coordinate_mixtures (j : LogIndex) :
    ∃ p m : SmoothEvenPolarTestFn →₀ ℝ,
      (∀ f,0 ≤ p f) ∧ (∀ f,0 ≤ m f) ∧
      smoothMixtureTrace p=Finsupp.single j 1 ∧
      smoothMixtureTrace m=Finsupp.single j (-1) := by
  classical
  have hj : 0<Real.sqrt (j:ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<j.1 by omega))
  let km := 2*(∫ u,oddPolarProfile j u^2)/Real.sqrt j
  let kp := 2*(∫ u,evenPolarProfile j u^2)/Real.sqrt j
  have hm : 0<km := div_pos (mul_pos two_pos (integral_oddPolarProfile_sq_pos j)) hj
  have hp : 0<kp := div_pos (mul_pos two_pos (lt_of_lt_of_le
    (by have := integral_narrowBump_sq_pos 0; have := nodeScale_pos j; positivity)
    (le_integral_evenPolarProfile_sq j))) hj
  refine ⟨Finsupp.single (smoothPolarPlus j) kp⁻¹,
    Finsupp.single (smoothPolarMinus j) km⁻¹,?_,?_,?_,?_⟩
  · intro f
    simp only [Finsupp.single_apply]
    split_ifs <;> positivity
  · intro f
    simp only [Finsupp.single_apply]
    split_ifs <;> positivity
  · rw [smoothMixtureTrace,linearCombination_single]
    change kp⁻¹ • logVector (evenPolarNode j).1=_
    rw [logVector_evenPolarNode,Finsupp.smul_single,smul_eq_mul]
    change Finsupp.single j (kp⁻¹*kp)=Finsupp.single j 1
    rw [inv_mul_cancel₀ hp.ne']
  · rw [smoothMixtureTrace,linearCombination_single]
    change km⁻¹ • logVector (evenPolarMinusTest j).1=_
    rw [logVector_evenPolarMinusTest,Finsupp.smul_single,smul_eq_mul]
    change Finsupp.single j (km⁻¹*(-km))=Finsupp.single j (-1)
    rw [mul_neg,inv_mul_cancel₀ hm.ne']

def positiveCoordinate (j : LogIndex) : SmoothEvenPolarTestFn →₀ ℝ :=
  (exists_smooth_coordinate_mixtures j).choose

def negativeCoordinate (j : LogIndex) : SmoothEvenPolarTestFn →₀ ℝ :=
  (exists_smooth_coordinate_mixtures j).choose_spec.choose

theorem coordinate_spec (j : LogIndex) :
    (∀ f,0 ≤ positiveCoordinate j f) ∧ (∀ f,0 ≤ negativeCoordinate j f) ∧
    smoothMixtureTrace (positiveCoordinate j)=Finsupp.single j 1 ∧
    smoothMixtureTrace (negativeCoordinate j)=Finsupp.single j (-1) :=
  (exists_smooth_coordinate_mixtures j).choose_spec.choose_spec

/-- Correct a finite trace using only nonnegative coefficients of smooth rows. -/
def smoothTraceRepair (s : Finset LogIndex) (v : LogIndex →₀ ℝ) :
    SmoothEvenPolarTestFn →₀ ℝ :=
  ∑ j ∈ s,((max (v j) 0) • positiveCoordinate j+
    (max (-v j) 0) • negativeCoordinate j)

theorem smoothTraceRepair_nonneg (s : Finset LogIndex) (v : LogIndex →₀ ℝ)
    (f : SmoothEvenPolarTestFn) : 0 ≤ smoothTraceRepair s v f := by
  classical
  simp only [smoothTraceRepair,Finsupp.finsetSum_apply,Finsupp.add_apply,
    Finsupp.smul_apply,smul_eq_mul]
  exact Finset.sum_nonneg fun j _ => add_nonneg
    (mul_nonneg (le_max_right _ _) ((coordinate_spec j).1 f))
    (mul_nonneg (le_max_right _ _) ((coordinate_spec j).2.1 f))

theorem smoothTraceRepair_trace (s : Finset LogIndex) (v : LogIndex →₀ ℝ)
    (hv : v.support ⊆ s) : smoothMixtureTrace (smoothTraceRepair s v)=v := by
  classical
  unfold smoothTraceRepair
  simp only [map_sum,map_add,map_smul,(coordinate_spec _).2.2.1,
    (coordinate_spec _).2.2.2,Finsupp.smul_single,smul_eq_mul,mul_one,mul_neg_one,
    ← Finsupp.single_add]
  have hm (r : ℝ) : max r 0 + -max (-r) 0=r := by
    rcases le_total 0 r with hr | hr
    · rw [max_eq_left hr,max_eq_right (by linarith)]; ring
    · rw [max_eq_right hr,max_eq_left (by linarith)]; ring
  simp_rw [hm]
  exact (Finsupp.sum_of_support_subset v hv (fun j r => Finsupp.single j r)
    (fun _ _ => Finsupp.single_zero _)).symm.trans (Finsupp.sum_single v)

/-- Every linear observable of a fixed finite correction tends to zero.
No sign condition is imposed on the observable, including the energy. -/
theorem smoothTraceRepair_observable_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : (SmoothEvenPolarTestFn →₀ ℝ) →ₗ[ℝ] E)
    (s : Finset LogIndex) (v : ℕ → LogIndex →₀ ℝ)
    (hv : ∀ j ∈ s,Tendsto (fun n => v n j) atTop (𝓝 0)) :
    Tendsto (fun n => L (smoothTraceRepair s (v n))) atTop (𝓝 0) := by
  classical
  simp only [smoothTraceRepair,map_sum,map_add,map_smul]
  have hh (j : LogIndex) (hj : j ∈ s) :
      Tendsto (fun n => (max (v n j) 0) • L (positiveCoordinate j)+
        (max (-v n j) 0) • L (negativeCoordinate j)) atTop (𝓝 0) := by
    have hp := ((hv j hj).max (tendsto_const_nhds (x := (0 : ℝ)))).smul_const
      (L (positiveCoordinate j))
    have hm := ((hv j hj).neg.max (tendsto_const_nhds (x := (0 : ℝ)))).smul_const
      (L (negativeCoordinate j))
    simpa only [neg_zero,max_self,zero_smul,zero_add] using hp.add hm
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum s hh

end RHTower.EvenSector
