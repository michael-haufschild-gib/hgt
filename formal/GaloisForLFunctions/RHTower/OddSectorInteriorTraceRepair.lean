import GaloisForLFunctions.RHTower.OddSectorInteriorTraceCoordinates
import GaloisForLFunctions.RHTower.OddSectorEnergyCompletion

/-!
# Exact positive arithmetic repair without aperture enlargement

On the finite set of active integer lags, fixed smooth odd coordinate sources
repair every trace defect. The repair is positive and tends to zero in every
linear observable when the defect tends to zero. Purification converts each
repaired mixture to one source in the same strict interior.
-/

open Complex MeasureTheory Set Finsupp Filter Topology Zeta23
open scoped NNReal
noncomputable section
namespace RHTower.OddSector
open WeilOneSided EvenSector WeilSpectral

def interiorTrace {a : SuzukiPositiveAperture} (f : InteriorWindowedSmoothOddTestFn a) :
    LogIndex →₀ ℝ := logVector f.1.1.1

def interiorProfile {a : SuzukiPositiveAperture} (f : InteriorWindowedSmoothOddTestFn a) :
    ℝ → ℂ := EF.weilTest f.1.1.1.1 f.1.1.1.1

def interiorEnergy {a : SuzukiPositiveAperture} (f : InteriorWindowedSmoothOddTestFn a) : ℝ :=
  nativeProfileEnergy (interiorProfile f)

def mixtureTrace (a : SuzukiPositiveAperture) :
    (InteriorWindowedSmoothOddTestFn a →₀ ℝ) →ₗ[ℝ] (LogIndex →₀ ℝ) :=
  linearCombination ℝ interiorTrace

def mixtureProfile (a : SuzukiPositiveAperture) :
    (InteriorWindowedSmoothOddTestFn a →₀ ℝ) →ₗ[ℝ] (ℝ → ℂ) :=
  linearCombination ℝ interiorProfile

def mixtureEnergy (a : SuzukiPositiveAperture) :
    (InteriorWindowedSmoothOddTestFn a →₀ ℝ) →ₗ[ℝ] ℝ :=
  linearCombination ℝ interiorEnergy

/-- Purification preserves the entire profile, arithmetic trace and literal energy. -/
theorem exists_interior_purification_moments (a : SuzukiPositiveAperture)
    (c : InteriorWindowedSmoothOddTestFn a →₀ ℝ) (hc : ∀ f, 0 ≤ c f) :
    ∃ f : InteriorWindowedSmoothOddTestFn a,
      interiorProfile f = mixtureProfile a c ∧
      interiorTrace f = mixtureTrace a c ∧ interiorEnergy f = mixtureEnergy a c := by
  classical
  let e := (Fintype.equivFin c.support).symm
  let F : Fin c.support.card → InteriorWindowedSmoothOddTestFn a := fun i => (e i).1
  let b : Fin c.support.card → ℝ≥0 := fun i => ⟨c (F i),hc (F i)⟩
  obtain ⟨f,hf⟩ := exists_interior_window_purification a F b
  have hP : interiorProfile f = mixtureProfile a c := by
    rw [interiorProfile,hf]
    change (fun x => ∑ i, (c (F i) : ℂ)*interiorProfile (F i) x) = _
    funext x
    have he := e.sum_comp (fun i : c.support => (c i.1 : ℂ)*interiorProfile i.1 x)
    simpa only [F,mixtureProfile,linearCombination_apply,Finsupp.sum,Finset.sum_apply,
      Pi.smul_apply,Complex.real_smul,Finset.univ_eq_attach,Finset.sum_attach] using he
  refine ⟨f,hP,?_,?_⟩
  · ext j
    change logValue f.1.1.1.1 j = _
    unfold logValue
    change (interiorProfile f (Real.log j)+interiorProfile f (-Real.log j)).re/Real.sqrt j = _
    rw [hP]
    simp only [mixtureProfile,mixtureTrace,linearCombination_apply,Finsupp.sum,
      Finset.sum_apply,Finsupp.finsetSum_apply,Pi.smul_apply,Finsupp.smul_apply,
      Complex.real_smul,smul_eq_mul,interiorTrace,logVector_apply,logValue,
      interiorProfile,← Finset.sum_add_distrib,Complex.re_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
    ring
  · let lam : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n
    have hp : mixtureProfile a c =
        ∑ g ∈ c.support, (c g : ℂ) • interiorProfile g := by
      simp only [mixtureProfile,linearCombination_apply,Finsupp.sum]
      rfl
    change (weilFullFunctional lam (interiorProfile f)).re = _
    rw [hP,hp,weilFullFunctional_sum lam _ (fun g _ =>
      (admissible_weilTest g.1.1.1.2.1 g.1.1.1.2.2).smul _)]
    simp only [weilFullFunctional_smul,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,mixtureEnergy,linearCombination_apply,
      Finsupp.sum,smul_eq_mul,interiorEnergy,nativeProfileEnergy,lam,interiorProfile]

/-- Active lags exclude the diameter itself. -/
def apertureNodes (a : SuzukiPositiveAperture) : Finset LogIndex :=
  (Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊).subtype (fun n => 2 ≤ n) |>.filter
    (fun j => Real.log (j : ℕ) < 2*a.1)

theorem mem_apertureNodes (a : SuzukiPositiveAperture) (j : LogIndex) :
    j ∈ apertureNodes a ↔ Real.log (j : ℕ) < 2*a.1 := by
  classical
  simp only [apertureNodes,Finset.mem_filter,Finset.mem_subtype,Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro hj
    refine ⟨⟨j.2,?_⟩,hj⟩
    apply (Nat.le_floor_iff (Real.exp_nonneg _)).2
    exact (Real.lt_exp_iff_log_lt (by exact_mod_cast (show 0 < j.1 by omega))).2 hj |>.le

theorem interiorTrace_support_subset {a : SuzukiPositiveAperture}
    (f : InteriorWindowedSmoothOddTestFn a) : (interiorTrace f).support ⊆ apertureNodes a := by
  classical
  intro j hj
  rw [mem_apertureNodes]
  by_contra hn
  have hlag : 2*a.1 ≤ Real.log (j : ℕ) := le_of_not_gt hn
  have hz (y : ℝ) (hy : 2*a.1 ≤ |y|) : interiorProfile f y = 0 := by
    unfold interiorProfile EF.weilTest convolution EF.tilde
    apply integral_eq_zero_of_ae
    filter_upwards with t
    simp only [ContinuousLinearMap.mul_apply',neg_sub]
    by_cases ht : f.1.1.1.1 t=0
    · rw [ht,zero_mul]
    · have hs := f.2 (subset_tsupport _ ht)
      have hfz : f.1.1.1.1 (t-y)=0 := by
        by_contra hh
        have hs' := f.2 (subset_tsupport _ hh)
        have hab : |y| < 2*a.1 := abs_lt.mpr ⟨by linarith [hs.1,hs'.2],
          by linarith [hs.2,hs'.1]⟩
        linarith
      rw [hfz,map_zero,mul_zero]
  apply Finsupp.mem_support_iff.mp hj
  change logValue f.1.1.1.1 j = 0
  unfold logValue
  change (interiorProfile f (Real.log j)+interiorProfile f (-Real.log j)).re/Real.sqrt j=0
  rw [hz _ (hlag.trans (le_abs_self _)),hz _ (by rw [abs_neg]; exact hlag.trans (le_abs_self _))]
  simp

private theorem coordinate_exists (a : SuzukiPositiveAperture) (j : apertureNodes a) :
    ∃ p m : InteriorWindowedSmoothOddTestFn a →₀ ℝ,
      (∀ f,0 ≤ p f) ∧ (∀ f,0 ≤ m f) ∧
      mixtureTrace a p=Finsupp.single j.1 1 ∧
      mixtureTrace a m=Finsupp.single j.1 (-1) := by
  classical
  obtain ⟨p,m,kp,km,hp,hm,hpt,hmt⟩ := exists_interior_signed_coordinates a j.1
    ((mem_apertureNodes a j.1).mp j.2)
  refine ⟨Finsupp.single p kp⁻¹,Finsupp.single m km⁻¹,?_,?_,?_,?_⟩
  · intro f; simp only [Finsupp.single_apply]; split_ifs <;> positivity
  · intro f; simp only [Finsupp.single_apply]; split_ifs <;> positivity
  · rw [mixtureTrace,linearCombination_single]
    change kp⁻¹ • logVector p.1.1.1 = _
    rw [hpt,Finsupp.smul_single,smul_eq_mul,inv_mul_cancel₀ hp.ne']
  · rw [mixtureTrace,linearCombination_single]
    change km⁻¹ • logVector m.1.1.1 = _
    rw [hmt,Finsupp.smul_single,smul_eq_mul,mul_neg,inv_mul_cancel₀ hm.ne']

def positiveCoordinate (a : SuzukiPositiveAperture) (j : apertureNodes a) :
    InteriorWindowedSmoothOddTestFn a →₀ ℝ := (coordinate_exists a j).choose

def negativeCoordinate (a : SuzukiPositiveAperture) (j : apertureNodes a) :
    InteriorWindowedSmoothOddTestFn a →₀ ℝ := (coordinate_exists a j).choose_spec.choose

theorem coordinate_spec (a : SuzukiPositiveAperture) (j : apertureNodes a) :
    (∀ f,0 ≤ positiveCoordinate a j f) ∧ (∀ f,0 ≤ negativeCoordinate a j f) ∧
    mixtureTrace a (positiveCoordinate a j)=Finsupp.single j.1 1 ∧
    mixtureTrace a (negativeCoordinate a j)=Finsupp.single j.1 (-1) :=
  (coordinate_exists a j).choose_spec.choose_spec

def traceRepair (a : SuzukiPositiveAperture) (v : LogIndex →₀ ℝ) :
    InteriorWindowedSmoothOddTestFn a →₀ ℝ :=
  ∑ j : apertureNodes a, max (v j.1) 0 • positiveCoordinate a j +
    max (-v j.1) 0 • negativeCoordinate a j

theorem traceRepair_nonneg (a : SuzukiPositiveAperture) (v : LogIndex →₀ ℝ)
    (f : InteriorWindowedSmoothOddTestFn a) : 0 ≤ traceRepair a v f := by
  classical
  simp only [traceRepair,Finsupp.finsetSum_apply,Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
  exact Finset.sum_nonneg fun j _ => add_nonneg
    (mul_nonneg (le_max_right _ _) ((coordinate_spec a j).1 f))
    (mul_nonneg (le_max_right _ _) ((coordinate_spec a j).2.1 f))

theorem traceRepair_trace (a : SuzukiPositiveAperture) (v : LogIndex →₀ ℝ)
    (hv : v.support ⊆ apertureNodes a) : mixtureTrace a (traceRepair a v)=v := by
  classical
  simp only [traceRepair,map_sum,map_add,map_smul,(coordinate_spec _ _).2.2.1,
    (coordinate_spec _ _).2.2.2,Finsupp.smul_single,smul_eq_mul,mul_one,mul_neg_one,
    ← Finsupp.single_add]
  have hm (r : ℝ) : max r 0 + -max (-r) 0 = r := by
    rcases le_total 0 r with hr | hr
    · rw [max_eq_left hr,max_eq_right (by linarith)]; ring
    · rw [max_eq_right hr,max_eq_left (by linarith)]; ring
  simp_rw [hm]
  rw [Finset.univ_eq_attach,Finset.sum_attach]
  exact (Finsupp.sum_of_support_subset v hv (fun j r => Finsupp.single j r)
    (fun _ _ => Finsupp.single_zero _)).symm.trans (Finsupp.sum_single v)

/-- Finite exact repairs vanish in every linear observable, including energy. -/
theorem traceRepair_observable_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : SuzukiPositiveAperture) (L : (InteriorWindowedSmoothOddTestFn a →₀ ℝ) →ₗ[ℝ] E)
    (v : ℕ → LogIndex →₀ ℝ) (hv : ∀ j,Tendsto (fun n => v n j) atTop (𝓝 0)) :
    Tendsto (fun n => L (traceRepair a (v n))) atTop (𝓝 0) := by
  simp only [traceRepair,map_sum,map_add,map_smul]
  have hh (j : apertureNodes a) :
      Tendsto (fun n => max (v n j.1) 0 • L (positiveCoordinate a j) +
        max (-v n j.1) 0 • L (negativeCoordinate a j)) atTop (𝓝 0) := by
    have hp := ((hv j.1).max (tendsto_const_nhds (x := (0 : ℝ)))).smul_const
      (L (positiveCoordinate a j))
    have hm := ((hv j.1).neg.max (tendsto_const_nhds (x := (0 : ℝ)))).smul_const
      (L (negativeCoordinate a j))
    simpa only [neg_zero,max_self,zero_smul,zero_add] using hp.add hm
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hh j)

end RHTower.OddSector
