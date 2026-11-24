import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Travel
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.BoxMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitTails
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # A size-independent eighteenth-moment obstruction for the actual first excursion -/
open Filter MeasureTheory ProbabilityTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open PrescribedTimes
noncomputable section

/-- All couplings except the specified interactions lie in the given bulk set. -/
def retainedSector {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (bulk : Set ℝ) : Set (ι → ℝ) :=
  univ.pi fun i => if i ∈ S then univ else bulk

theorem measurable_retainedSector {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) {bulk : Set ℝ} (hb : MeasurableSet bulk) :
    MeasurableSet (retainedSector S bulk) := by
  apply MeasurableSet.pi (Set.to_countable _)
  intro i _
  split <;> first | exact MeasurableSet.univ | exact hb

private theorem box_cut {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ι}
    {δ : ℝ} {bulk : Set ℝ} {x : ι → ℝ} (hx : x ∈ coefficientBox S δ bulk) {i} (hi : i ∈ S) :
    |x i| ≤ δ := by
  have h := hx i (mem_univ i)
  change x i ∈ (if i ∈ S then Icc (-δ) δ else bulk) at h
  exact abs_le.mpr (by simpa only [if_pos hi,mem_Icc] using h)

private theorem box_sector {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (δ : ℝ) (bulk : Set ℝ) : coefficientBox S δ bulk ⊆ retainedSector S bulk := by
  intro x hx i _
  have h := hx i (mem_univ i)
  change x i ∈ (if i ∈ S then Icc (-δ) δ else bulk) at h
  change x i ∈ (if i ∈ S then univ else bulk)
  by_cases hi : i ∈ S
  · rw [if_pos hi]; exact mem_univ _
  · simpa only [if_neg hi] using h

private theorem real_indicator_tail {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q : Set X) (J : X → ℝ) (A : ℝ) :
    μ.real {x | x ∈ Q ∧ A < J x} ≤ μ.real {x | A < Q.indicator J x} := by
  refine measureReal_mono (μ := μ) ?_ (measure_ne_top _ _)
  rintro x ⟨h,hx⟩
  change A < Q.indicator J x
  exact (indicator_of_mem h J).symm ▸ hx

/-- Two fixed balanced cuts on each sufficiently long prefix delay both
physical clocks whenever all eighteen cut coefficients are small. -/
theorem gaussian_two_cut_travel :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      ∃ a b : Fin (k+2), a < b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
        let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
        ∀ T : ℝ, 0 < T → (∀ i ∈ cutSet a b, |x i| ≤ 1/(1800*T)) → ∀ s ≤ P/2,
          T < min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P s x) := by
  have hent := (tendsto_add_atTop_nat 3).eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hent,eventually_ge_atTop 192] with k hentropy hlarge
  intro N P
  obtain ⟨a,b,hab,hL,hM,hR,hcost⟩ := exists_affordable_cuts (k+1) (by omega)
  refine ⟨a,b,hab,?_⟩
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hg
  intro x T hT hw s hs
  let u := pathPauliDisorderShell ω (k+1)
  let d := 2^N-1
  let e : (Fin N → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hd : 0 < (2:ℕ)^N := by positivity
                  dsimp [d]; omega))
  have hpass := weak_first_passage u e ((hg k).comp_equiv e.symm) hentropy hab hL hM hR hcost hT hw
  exact lt_min hpass.1 (hpass.2 s hs)

private theorem gaussian_box_survival {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {ν : Measure Ω} (x : Ω → ι → ℝ)
    (hmp : MeasurePreserving x ν (Measure.pi fun _ : ι => gaussianReal 0 1))
    (S : Finset ι) (hS : S.card = 18) (J : (ι → ℝ) → ℝ) (hJ : Measurable J)
    (hg : ∀ᵐ ω ∂ν, ∀ T : ℝ, 0 < T → (∀ i ∈ S, |x ω i| ≤ 1/(1800*T)) → T < J (x ω))
    {bulk : Set ℝ} (hbulk : MeasurableSet bulk) (v : ℝ) (hv : 1 ≤ v) :
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    (2*gaussianDensityFloor)^18 * (gaussianReal 0 1).real bulk^Sᶜ.card ≤
      v^18*μ.real {y | y ∈ retainedSector S bulk ∧ v*(1/1800) < J y} := by
  intro μ
  let c := (2*gaussianDensityFloor)^18 * (gaussianReal 0 1).real bulk^Sᶜ.card
  let T := v*(1/1800)
  let δ := v⁻¹
  have hvpos := zero_lt_one.trans_le hv
  have hT : 0 < T := mul_pos hvpos (by norm_num)
  have hδ : δ = 1/(1800*T) := by rw [show 1800*T=v by dsimp [T]; ring,one_div]
  let E := coefficientBox S δ bulk
  let F := {y | y ∈ retainedSector S bulk ∧ T < J y}
  have hE : MeasurableSet E := by
    apply MeasurableSet.pi (Set.to_countable _)
    intro i _
    split <;> first | exact measurableSet_Icc | exact hbulk
  have hF : MeasurableSet F := (measurable_retainedSector S hbulk).inter (measurableSet_lt measurable_const hJ)
  have hsub : x ⁻¹' E ≤ᵐ[ν] x ⁻¹' F := by
    filter_upwards [hg] with ω hh
    change x ω ∈ coefficientBox S δ bulk → x ω ∈ F
    intro hbox
    have hw (i : ι) (hi : i ∈ S) : |x ω i| ≤ 1/(1800*T) :=
      (box_cut (S := S) (x := x ω) (δ := δ) (bulk := bulk) (i := i) hbox hi).trans_eq hδ
    exact ⟨box_sector S δ bulk hbox,hh T hT hw⟩
  have he : ν (x ⁻¹' E) = μ E := hmp.measure_preimage hE.nullMeasurableSet
  have hf : ν (x ⁻¹' F) = μ F := hmp.measure_preimage hF.nullMeasurableSet
  have hmeasure : μ.real E ≤ μ.real F := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    rw [←he,←hf]
    exact measure_mono_ae hsub
  have hfloor := coefficientBox_floor S bulk (inv_nonneg.mpr hvpos.le) ((inv_le_one₀ hvpos).mpr hv)
  rw [hS] at hfloor
  change c*δ^18 ≤ μ.real E at hfloor
  change c ≤ v^18*μ.real F
  calc
    c = v^18*(c*δ^18) := by dsimp only [δ]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hfloor.trans hmeasure) (pow_nonneg hvpos.le _)

/-- Two balanced cuts supply an eighteenth-power survival floor on any sector
specified by the retained coefficients. It holds at every time
scale and for every half-budget return on each sufficiently large prefix. -/
theorem gaussian_two_weak_bonds_joint_survival :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∃ a b : Fin (k+2), a < b ∧ ∀ bulk : Set ℝ, MeasurableSet bulk → ∀ s ≤ P/2, ∀ v : ℝ, 1 ≤ v →
        (2*gaussianDensityFloor)^18 * (gaussianReal 0 1).real bulk^(cutSet a b)ᶜ.card ≤
          v^18 * μ.real {x | x ∈ retainedSector (cutSet a b) bulk ∧
          v*(1/1800) < min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P s x)} := by
  filter_upwards [gaussian_two_cut_travel] with k htravel
  intro N P μ
  obtain ⟨a,b,hab,hgood⟩ := htravel
  refine ⟨a,b,hab,?_⟩
  intro bulk hbulk s hs v hv
  let J := fun x => min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P s x)
  let x := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  have hJ : Measurable J := (measurable_crossingOrigin _ _ _).min (measurable_crossingWait _ _ _)
  apply gaussian_box_survival x (gaussian_pauli_prefix_coordinates_law (k+1))
    (cutSet a b) (cutSet_card hab) J hJ _ hbulk v hv
  filter_upwards [hgood] with ω hh
  exact fun T hT hw => hh T hT hw s hs

/-- The unrestricted Gaussian tail has a single positive constant for all
sufficiently long chains, all half-budget returns, and all T ≥ 1. -/
theorem gaussian_uniform_first_excursion_tail :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∀ T : ℝ, 1 ≤ T → c ≤ T^18 * μ.real {x |
        T < crossingOrigin (k+1) P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait (k+1) P s x} := by
  refine ⟨(2*gaussianDensityFloor)^18/(1800:ℝ)^18,
    div_pos (pow_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) _) (by positivity),?_⟩
  filter_upwards [gaussian_two_weak_bonds_joint_survival] with k hk
  intro P μ T hT
  obtain ⟨a,b,_,hsectors⟩ := hk
  have h := hsectors univ MeasurableSet.univ (P/2) le_rfl (1800*T) (by linarith only [hT])
  rw [probReal_univ,one_pow,mul_one,show 1800*T*(1/1800)=T by ring] at h
  let J := fun x => min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P (P/2) x)
  let F := {x | T < crossingOrigin (k+1) P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait (k+1) P s x}
  have hm : μ.real {x | x ∈ retainedSector (cutSet a b) univ ∧ T < J x} ≤ μ.real F := by
    refine measureReal_mono (μ := μ) ?_ (measure_ne_top _ _)
    rintro x ⟨_,hx⟩
    obtain ⟨hσ,hΔ⟩ := lt_min_iff.mp hx
    exact ⟨hσ,fun s hs => hΔ.trans_le (crossingWait_antitone hs x)⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ)<1800^18)).mpr
  calc
    _ ≤ (1800*T)^18 * μ.real F := h.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = _ := by rw [mul_pow]; ring

/-- At any proposed onset deadline u^N, the disorder failure probability is
at least c u^(−18N), uniformly in u ≥ 1 and in all sufficiently long chains. -/
theorem gaussian_exponential_onset_failure_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∀ u : ℝ, 1 ≤ u → c ≤ u^(18*N) * μ.real {x | u^N < crossingOrigin (k+1) P (9/80) x} := by
  obtain ⟨c,hc,h⟩ := gaussian_uniform_first_excursion_tail
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with k hk
  intro N P μ u hu
  have hlate := hk (u^N) (one_le_pow₀ hu)
  rw [Nat.mul_comm 18 N,pow_mul]
  exact hlate.trans (mul_le_mul_of_nonneg_left (measureReal_mono fun _ hx => hx.1) (by positivity))

/-- Infinite eighteenth absolute moment persists with every retained coupling
bounded between one and two. The exponent counts the two erased nine-component
bonds and is independent of the chain length. -/
theorem gaussian_two_weak_bonds_moment :
    ∀ᶠ k : ℕ in atTop,
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
      ∃ a b : Fin (k+2), a < b ∧ ∀ s ≤ P/2,
        let J := fun x => min (crossingOrigin (k+1) P (9/80) x) (crossingWait (k+1) P s x)
        ¬ Integrable (fun x => |(retainedSector (cutSet a b) (Icc 1 2)).indicator J x|^18) μ := by
  filter_upwards [gaussian_two_weak_bonds_joint_survival] with k hk
  intro P μ
  obtain ⟨a,b,hab,hsectors⟩ := hk
  let c := (2*gaussianDensityFloor)^18 * (gaussianReal 0 1).real (Icc 1 2)^(cutSet a b)ᶜ.card
  have hp : 0 < (gaussianReal 0 1).real (Icc 1 2) :=
    ENNReal.toReal_pos (gaussianReal_Icc_pos (by norm_num : (1:ℝ)<2)).ne' (measure_ne_top _ _)
  have hc : 0 < c := mul_pos (pow_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) _) (pow_pos hp _)
  have hfloor := hsectors (Icc 1 2) measurableSet_Icc
  refine ⟨a,b,hab,fun s hs => ?_⟩
  intro J
  let Q := retainedSector (cutSet a b) (Icc 1 2)
  have hJ : Measurable J := (measurable_crossingOrigin _ _ _).min (measurable_crossingWait _ _ _)
  apply not_integrable_boundary_moment μ (Q.indicator J) (hJ.indicator (measurable_retainedSector _ measurableSet_Icc))
    18 (B := 1/1800) (by norm_num) (p := c/2) (half_pos hc)
  intro v hv
  have htail := real_indicator_tail μ Q J (v*(1/1800))
  exact ((half_lt_self hc).trans_le (hfloor s hs v hv)).trans_le
    (mul_le_mul_of_nonneg_left htail (pow_nonneg (zero_le_one.trans hv) _))

#print axioms gaussian_two_weak_bonds_joint_survival
#print axioms gaussian_uniform_first_excursion_tail
#print axioms gaussian_exponential_onset_failure_floor
#print axioms gaussian_two_weak_bonds_moment
end
end GaloisForLFunctions.HTGeometry.WeakBonds
