import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth

/-! # Finite-prefix disorder tails at the first robust crossing -/
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
open LocalPatches
noncomputable section

/-- Almost-sure eventual membership implies convergence of the single-prefix
probabilities, even for overlapping prefixes of one infinite chain. -/
private theorem measureReal_tendsto_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ℕ → Set Ω) (hm : ∀ k, MeasurableSet (A k))
    (h : ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, x ∈ A k) : Tendsto (fun k => μ.real (A k)) atTop (𝓝 1) := by
  let f (k : ℕ) := (A k).indicator (1 : Ω → ℝ)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (1:ℝ)) := by
    filter_upwards [h] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun k hk => (indicator_of_mem hk _).symm)
  have hbound (k : ℕ) : ∀ᵐ x ∂μ, ‖f k x‖ ≤ 1 := by
    filter_upwards with x
    by_cases hx : x ∈ A k <;> simp [f,hx]
  have hc := tendsto_integral_of_dominated_convergence (μ := μ) (F := f) (fun _ => (1:ℝ))
    (fun k => (measurable_const.indicator (hm k)).aestronglyMeasurable)
    (integrable_const _) hbound hlim
  have he (k : ℕ) : (∫ x, f k x ∂μ) = μ.real (A k) := integral_indicator_one (hm k)
  simpa only [he,integral_const,probReal_univ,one_smul] using hc

/-- For each confidence level p < 1, all sufficiently large Gaussian prefixes
have joint survival probability greater than p/a^m at a times the physical
travel width, for every dilation a ≥ 1 and every half-budget return. Here m
is the number of independent coefficients in the prefix. -/
theorem gaussian_first_passage_joint_tail_floor (p : ℝ) (hp : p < 1) :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let B := localCrossingWidth N
      let m := Fintype.card (ChainLabel N)
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∀ s ≤ P/2, ∀ a : ℝ, 1 ≤ a →
        p < a^m * μ.real {x | a*B < crossingOrigin (k+1) P (9/80) x ∧ a*B < crossingWait (k+1) P s x} := by
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let B (k : ℕ) := localCrossingWidth (k+3)
  let E (k : ℕ) : Set (PrefixIndex (k+1) → ℝ) :=
    {x | B k < crossingOrigin (k+1) (P k) (9/80) x ∧ B k < crossingWait (k+1) (P k) (P k/2) x}
  let x (k : ℕ) (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  have hm (k : ℕ) : MeasurableSet (E k) :=
    (measurableSet_lt measurable_const (measurable_crossingOrigin _ _ _)).inter
      (measurableSet_lt measurable_const (measurable_crossingWait _ _ _))
  have hgood : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, x k ω ∈ E k := by
    filter_upwards [gaussian_first_crossing_local_width] with ω hω
    filter_upwards [hω] with k hk
    obtain ⟨σ,hσ,hcross,hprior,hvisit⟩ := hk
    let u := pathPauliDisorderShell ω (k+1)
    have hgen : numberedGenerator (k+1) (x k ω) = pathHamiltonian u := numberedGenerator_shell u
    have hd (t : ℝ) : pathGateDistance (k+1) (P k) (x k ω) t =
        orbitCircuitDistance ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ (P k) t := by
      rw [pathGateDistance,hgen]; rfl
    have hB : 0 < B k := by dsimp [B,localCrossingWidth]; positivity
    have ho := crossingOrigin_eq_of_first (hB.trans hσ).le ((hd σ).trans hcross)
      (fun t ht => (hd t).trans_lt (hprior t ht))
    obtain ⟨v,hv,hmin⟩ := hvisit (P k/2) le_rfl
    have ht : firstCircuitVisit (prefixGenerator (k+1) (x k ω)) (P k/2) σ = v := by
      unfold firstCircuitVisit
      change sInf {t | σ ≤ t ∧ HasProjectiveCircuitApproximation _ _ _ (unitaryEvolution (numberedGenerator _ _) t)} = v
      rw [hgen]
      exact hmin.csInf_eq
    refine ⟨ho.symm ▸ hσ,?_⟩
    change B k < firstCircuitVisit _ _ _ - _
    rw [ho,ht]
    linarith only [hv]
  have hmp (k : ℕ) := gaussian_pauli_prefix_coordinates_law (k+1)
  have hc := measureReal_tendsto_one pathPauliDisorderLaw (fun k => x k ⁻¹' E k)
    (fun k => (hm k).preimage (hmp k).measurable) hgood
  filter_upwards [hc.eventually_const_lt hp] with k hk
  intro N _ _ m μ s hs a ha
  have hmeasure : pathPauliDisorderLaw.real (x k ⁻¹' E k) = μ.real (E k) :=
    congrArg ENNReal.toReal ((hmp k).measure_preimage (hm k).nullMeasurableSet)
  have hbase : p < μ.real (E k) := hk.trans_eq hmeasure
  have hsub : E k ⊆ {y | B k < crossingOrigin (k+1) (P k) (9/80) y ∧ B k < crossingWait (k+1) (P k) s y} :=
    fun y hy => ⟨hy.1,hy.2.trans_le (crossingWait_antitone hs y)⟩
  exact (hbase.trans_le (measureReal_mono hsub)).trans_le
    (gaussian_joint_first_passage_tail (k+1) (P k) s (B k) (B k) ha)

/-- A uniform polynomial survival floor rules out integrability even at the
boundary exponent. Under integrability the moment over each receding tail
would tend to zero. -/
theorem not_integrable_boundary_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (J : X → ℝ) (hJ : Measurable J)
    (m : ℕ) {B p : ℝ} (hB : 0 < B) (hp : 0 < p)
    (htail : ∀ a : ℝ, 1 ≤ a → p < a^m * μ.real {x | a*B < J x}) :
    ¬ Integrable (fun x => |J x|^m) μ := by
  intro hint
  let f := fun x => |J x|^m
  let a := fun l : ℕ => (l:ℝ)+1
  let S := fun l : ℕ => {x | a l*B < J x}
  have hS (l : ℕ) : MeasurableSet (S l) := measurableSet_lt measurable_const hJ
  have hlim (x : X) : Tendsto (fun l => (S l).indicator f x) atTop (𝓝 0) := by
    obtain ⟨k,hk⟩ := exists_nat_gt (J x/B)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with l hl
    have hkl : (k:ℝ) ≤ l := by exact_mod_cast hl
    have hlt : J x < a l*B := (div_lt_iff₀ hB).mp (by dsimp [a]; linarith only [hk,hkl])
    exact (indicator_of_notMem (show x ∉ S l from hlt.asymm) f).symm
  have hc := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun l => (S l).indicator f)
    (f := fun _ => (0:ℝ)) f (fun l => (hint.indicator (hS l)).aestronglyMeasurable) hint
    (fun l => ae_of_all _ fun x => by
      by_cases hx : x ∈ S l
      · rw [indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      · rw [indicator_of_notMem hx,norm_zero]
        exact pow_nonneg (abs_nonneg _) _)
    (ae_of_all _ hlim)
  have ht := hc.eventually_lt_const (show (∫ _ : X, (0:ℝ) ∂μ) < B^m*p by
    rw [integral_zero]; exact mul_pos (pow_pos hB m) hp)
  obtain ⟨l,hl⟩ := ht.exists
  rw [integral_indicator (hS l)] at hl
  have ha : 1 ≤ a l := by dsimp [a]; linarith only [Nat.cast_nonneg (α := ℝ) l]
  have hprice := (mul_lt_mul_of_pos_left (htail (a l) ha) (pow_pos hB m))
  have hfloor : (a l*B)^m * μ.real (S l) ≤ ∫ x in S l, f x ∂μ := by
    have h := setIntegral_mono_on (μ := μ) (s := S l)
      (integrableOn_const (C := (a l*B)^m) (measure_ne_top _ _)) hint.integrableOn (hS l)
      (fun x hx => pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans ha) hB.le)
        ((le_of_lt hx).trans (le_abs_self (J x))) m)
    simpa only [setIntegral_const,smul_eq_mul,mul_comm (μ.real (S l))] using h
  rw [mul_pow] at hfloor
  change B^m*p < B^m*((a l)^m*μ.real (S l)) at hprice
  linarith only [hprice,hfloor,hl]

/-- For all sufficiently large prefixes, even the smaller of the onset time
and first subsequent waiting time has infinite absolute moment of order
equal to the number of Gaussian coefficients. -/
theorem gaussian_first_passage_critical_moment :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let m := Fintype.card (ChainLabel N)
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∀ s ≤ P/2, ¬ Integrable (fun x =>
        |min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P s x)|^m) μ := by
  filter_upwards [gaussian_first_passage_joint_tail_floor (1/2) (by norm_num)] with k hk
  intro N P m μ s hs
  apply not_integrable_boundary_moment μ _
    ((measurable_crossingOrigin _ _ _).min (measurable_crossingWait _ _ _))
    m (B := localCrossingWidth N) (by unfold localCrossingWidth; positivity) (p := 1/2) (by norm_num)
  intro a ha
  simpa only [lt_min_iff] using hk s hs a ha

#print axioms gaussian_first_passage_critical_moment
#print axioms gaussian_first_passage_joint_tail_floor
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
