import GaloisForLFunctions.HTGeometry.PrefixUltrametricLocalization
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFormationCalibrations

/-!
# Exact Feller formation of all depths from singular full-support laws

Let `q₀ ≠ q₁` be full-support laws on the two-letter alphabet `{0, 1}` with its discrete metric and
let `μᵢ = qᵢ^{⊗ℕ}` on binary sequences with the prefix ultrametric `d_θ`.  The deterministic prefix
kernel `K_d(x, ·) = δ_{(x_0, …, x_{d-1})}` is locally constant, it forms `qᵢ^{⊗d}` exactly from
`μᵢ`, both `μᵢ` have full support, `μ₀ ⊥ μ₁`, and

`α(K_d) = θ^{-(d-1)}`.

So exact Feller formation from full-support singular laws exists at every depth, and its
resolution amplification escapes exponentially.

Singularity comes from the prefix total variations: `TV(μ₀^{<N}, μ₁^{<N}) ≥ 1 - a^N → 1`, where
`a < 1` is the Hellinger affinity of `q₀` and `q₁`, and prefix decision sets whose errors are
summable separate the two laws by the Borel–Cantelli lemma.
-/

open MeasureTheory Set Filter Topology PiNat ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Prefix decisions force singularity -/

section PrefixSingularity

theorem measureReal_hahnPositiveSet_le {Z : Type*} [MeasurableSpace Z] (P Q : Measure Z)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    P.real (hahnPositiveSet P Q) ≤ 1 - measurableHahnTV P Q ∧
      Q.real (hahnPositiveSet P Q)ᶜ ≤ 1 - measurableHahnTV P Q := by
  have hB := measurableSet_hahnPositiveSet P Q
  have h := hahnEffectCurrent_hahnPositiveSet P Q
  rw [hahnEffectCurrent, integral_indicator_const (1 : ℝ) hB,
    integral_indicator_const (1 : ℝ) hB] at h
  simp only [smul_eq_mul, mul_one] at h
  rw [probReal_compl_eq_one_sub hB]
  have h0 := measureReal_nonneg (μ := P) (s := hahnPositiveSet P Q)
  have h1 : Q.real (hahnPositiveSet P Q) ≤ 1 :=
    (measureReal_mono (subset_univ _)).trans (by simp)
  constructor <;> linarith

theorem measurableHahnTV_le_one {Z : Type*} [MeasurableSpace Z] (P Q : Measure Z)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : measurableHahnTV P Q ≤ 1 := by
  have h := (measureReal_hahnPositiveSet_le P Q).1
  have h0 := measureReal_nonneg (μ := P) (s := hahnPositiveSet P Q)
  linarith

/-- If the total variation of the observed laws tends to one along a sequence of observers, the
laws are mutually singular. -/
theorem mutuallySingular_of_tendsto_measurableHahnTV {Ω : Type*} [MeasurableSpace Ω]
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] {P Q : Measure Ω} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {π : ∀ n, Ω → Y n} (hπ : ∀ n, Measurable (π n))
    (h : Tendsto (fun n => measurableHahnTV (P.map (π n)) (Q.map (π n))) atTop (𝓝 1)) :
    P ⟂ₘ Q := by
  haveI : ∀ n, IsProbabilityMeasure (P.map (π n)) := fun n =>
    Measure.isProbabilityMeasure_map (hπ n).aemeasurable
  haveI : ∀ n, IsProbabilityMeasure (Q.map (π n)) := fun n =>
    Measure.isProbabilityMeasure_map (hπ n).aemeasurable
  have hk : ∀ k : ℕ, ∃ n, 1 - measurableHahnTV (P.map (π n)) (Q.map (π n)) ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    have h' : Tendsto (fun n => 1 - measurableHahnTV (P.map (π n)) (Q.map (π n))) atTop
        (𝓝 0) := by
      simpa using h.const_sub 1
    exact (h'.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < (1 / 2) ^ k))).exists
  choose n hn using hk
  set C : ℕ → Set Ω := fun k =>
    π (n k) ⁻¹' hahnPositiveSet (P.map (π (n k))) (Q.map (π (n k))) with hCdef
  have hCm : ∀ k, MeasurableSet (C k) := fun k => hπ _ (measurableSet_hahnPositiveSet _ _)
  have hP : ∀ k, P (C k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    have hb := (measureReal_hahnPositiveSet_le (P.map (π (n k))) (Q.map (π (n k)))).1
    rw [map_measureReal_apply (hπ _) (measurableSet_hahnPositiveSet _ _)] at hb
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hb.trans (hn k))
  have hQ : ∀ k, Q (C k)ᶜ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    have hb := (measureReal_hahnPositiveSet_le (P.map (π (n k))) (Q.map (π (n k)))).2
    rw [map_measureReal_apply (hπ _) (measurableSet_hahnPositiveSet _ _).compl,
      preimage_compl] at hb
    rw [← ofReal_measureReal (measure_ne_top Q _)]
    exact ENNReal.ofReal_le_ofReal (hb.trans (hn k))
  have hsum : ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have h0 : P (limsup C atTop) = 0 :=
    measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hP))
  have h1 : Q (limsup (fun k => (C k)ᶜ) atTop) = 0 :=
    measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hQ))
  refine ⟨limsup C atTop, MeasurableSet.measurableSet_limsup hCm, h0, measure_mono_null ?_ h1⟩
  intro x hx
  rw [mem_compl_iff, mem_limsup_iff_frequently_mem, not_frequently] at hx
  rw [mem_limsup_iff_frequently_mem]
  exact hx.frequently

end PrefixSingularity

/-! ## The two-letter alphabet -/

/-- The two-letter alphabet `{0, 1}`. -/
def BinaryLetter : Type := Bool

namespace BinaryLetter

instance : Fintype BinaryLetter := inferInstanceAs (Fintype Bool)

instance : DecidableEq BinaryLetter := inferInstanceAs (DecidableEq Bool)

instance : Nonempty BinaryLetter := ⟨(false : Bool)⟩

/-- The letter `0`. -/
def zero : BinaryLetter := (false : Bool)

/-- The letter `1`. -/
def one : BinaryLetter := (true : Bool)

theorem one_ne_zero : one ≠ zero := by decide

/-- The discrete metric: distinct letters are at distance one. -/
def letterDist (a b : BinaryLetter) : ℝ := if a = b then 0 else 1

theorem letterDist_triangle (a b c : BinaryLetter) :
    letterDist a c ≤ letterDist a b + letterDist b c := by
  unfold letterDist
  split_ifs <;> simp_all

instance : MetricSpace BinaryLetter :=
  @MetricSpace.ofDistTopology BinaryLetter ⊥ letterDist (fun a => by simp [letterDist])
    (fun a b => by
      unfold letterDist
      split_ifs <;> simp_all)
    letterDist_triangle
    (fun s => by
      refine ⟨fun _ x hx => ⟨1, one_pos, fun y hy => ?_⟩, fun _ => ?_⟩
      · unfold letterDist at hy
        split_ifs at hy with hxy
        · exact hxy ▸ hx
        · norm_num at hy
      · letI : TopologicalSpace BinaryLetter := ⊥
        haveI : DiscreteTopology BinaryLetter := ⟨rfl⟩
        exact isOpen_discrete s)
    (fun a b h => by
      unfold letterDist at h
      split_ifs at h with hab
      · exact hab
      · norm_num at h)

theorem dist_eq (a b : BinaryLetter) : dist a b = if a = b then 0 else 1 := rfl

theorem dist_le_one (a b : BinaryLetter) : dist a b ≤ 1 := by
  rw [dist_eq]
  split_ifs <;> norm_num

instance : DiscreteTopology BinaryLetter := ⟨rfl⟩

instance : MeasurableSpace BinaryLetter := ⊤

instance : MeasurableSingletonClass BinaryLetter := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : BorelSpace BinaryLetter := ⟨borel_eq_top_of_discrete.symm⟩

theorem isOpenPosMeasure_of_ne_zero (q : Measure BinaryLetter) (hq : ∀ b, q {b} ≠ 0) :
    q.IsOpenPosMeasure :=
  ⟨fun _ _ ⟨b, hb⟩ => fun h0 => hq b (measure_mono_null (singleton_subset_iff.mpr hb) h0)⟩

end BinaryLetter

/-! ## The prefix kernel -/

section PrefixKernel

variable (θ : ℝ)

/-- Binary sequences with the prefix ultrametric `d_θ`. -/
abbrev BinarySequence : Type := PrefixSpace θ fun _ : ℕ => BinaryLetter

variable {θ}

/-- The first `d` letters of a binary sequence. -/
def prefixWord (d : ℕ) (x : BinarySequence θ) : Fin d → BinaryLetter := fun i => x i

theorem measurable_prefixWord (d : ℕ) : Measurable (prefixWord (θ := θ) d) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)

variable (θ)

/-- **(RP.21).**  The deterministic prefix kernel `K_d(x, ·) = δ_{(x_0, …, x_{d-1})}`. -/
def prefixWordKernel (d : ℕ) : Kernel (BinarySequence θ) (Fin d → BinaryLetter) :=
  Kernel.deterministic (prefixWord d) (measurable_prefixWord d)

instance (d : ℕ) : IsMarkovKernel (prefixWordKernel θ d) := by
  unfold prefixWordKernel
  infer_instance

variable {θ}

theorem kernelPullback_prefixWordKernel (d : ℕ) (f : (Fin d → BinaryLetter) → ℝ) :
    kernelPullback (prefixWordKernel θ d) f = f ∘ prefixWord d := by
  funext x
  rw [kernelPullback, prefixWordKernel, Kernel.deterministic_apply, integral_dirac]
  rfl

theorem continuous_prefixWord [Fact (0 < θ)] [Fact (θ < 1)] (d : ℕ) :
    Continuous (prefixWord (θ := θ) d) := by
  have h : @Continuous (∀ n : ℕ, BinaryLetter) (Fin d → BinaryLetter) Pi.topologicalSpace _
      (fun x i => x i) := continuous_pi fun i => continuous_apply (i : ℕ)
  exact h

/-- The prefix kernel is Feller in the strongest sense: every effect pulls back to a locally
constant, hence continuous, function. -/
theorem continuous_kernelPullback_prefixWordKernel [Fact (0 < θ)] [Fact (θ < 1)] (d : ℕ)
    (f : (Fin d → BinaryLetter) → ℝ) :
    Continuous (kernelPullback (prefixWordKernel θ d) f) := by
  rw [kernelPullback_prefixWordKernel]
  exact continuous_of_discreteTopology.comp (continuous_prefixWord d)

theorem map_prefixWord_prefixProductLaw (q : Measure BinaryLetter) [IsProbabilityMeasure q]
    (d : ℕ) :
    (prefixProductLaw θ fun _ => q).map (prefixWord d) = Measure.pi fun _ : Fin d => q := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_prefixWord d) (MeasurableSet.univ_pi hs)]
  set t : ℕ → Set BinaryLetter := fun n => if h : n < d then s ⟨n, h⟩ else univ with htdef
  have hpre : prefixWord (θ := θ) d ⁻¹' univ.pi s = ((Finset.range d : Finset ℕ) : Set ℕ).pi t := by
    ext x
    simp only [mem_preimage, prefixWord, Finset.coe_range, Set.mem_pi]
    constructor
    · intro hx n hn
      have hn' : n < d := hn
      simpa [htdef, hn'] using hx ⟨n, hn'⟩
    · intro hx i
      simpa [htdef, i.2] using hx i i.2
  rw [hpre]
  refine (Measure.infinitePi_pi (fun _ : ℕ => q) fun i _ => MeasurableSet.of_discrete).trans ?_
  rw [← Fin.prod_univ_eq_prod_range (fun n => q (t n)) d]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [htdef]

/-- **Theorem 6.1 (3).**  `K_d` forms `q^{⊗d}` exactly from `q^{⊗ℕ}`. -/
theorem isExactFormation_prefixWordKernel (q : Measure BinaryLetter) [IsProbabilityMeasure q]
    (d : ℕ) : IsExactFormation (prefixProductLaw θ fun _ => q) (prefixWordKernel θ d) q := by
  intro y
  have hmeas : MeasurableSet (prefixWord (θ := θ) d ⁻¹' {y}) :=
    measurable_prefixWord d (measurableSet_singleton y)
  have hK : ∀ x : BinarySequence θ, ((prefixWordKernel θ d x) {y}).toReal
      = (prefixWord d ⁻¹' {y}).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    rw [prefixWordKernel, Kernel.deterministic_apply,
      Measure.dirac_apply' _ (measurableSet_singleton y)]
    by_cases hx : prefixWord d x = y
    · simp [hx]
    · simp [hx]
  simp_rw [hK]
  rw [integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one,
    ← map_prefixWord_prefixProductLaw q d,
    map_measureReal_apply (measurable_prefixWord d) (measurableSet_singleton y)]

/-- **Theorem 6.1 (1).**  A full-support letter law has a full-support sequence law. -/
theorem isOpenPosMeasure_prefixProductLaw [Fact (0 < θ)] [Fact (θ < 1)] (q : Measure BinaryLetter)
    [IsProbabilityMeasure q]
    (hq : ∀ b, q {b} ≠ 0) : (prefixProductLaw θ fun _ => q).IsOpenPosMeasure := by
  haveI := BinaryLetter.isOpenPosMeasure_of_ne_zero q hq
  have h := isOpenPosMeasure_infinitePi (fun _ : ℕ => q)
  exact h

/-- **Theorem 6.1 (2).**  Distinct letter laws give mutually singular sequence laws. -/
theorem prefixProductLaw_mutuallySingular {q₀ q₁ : Measure BinaryLetter}
    [IsProbabilityMeasure q₀] [IsProbabilityMeasure q₁] (hne : q₀ ≠ q₁) :
    (prefixProductLaw θ fun _ => q₀) ⟂ₘ (prefixProductLaw θ fun _ => q₁) := by
  classical
  set a := hellingerAffinity q₀ q₁ with ha
  have ha0 : 0 ≤ a := by
    rw [ha, hellingerAffinity]
    exact tsum_nonneg fun _ => Real.sqrt_nonneg _
  have ha1 : a < 1 := lt_of_le_of_ne (hellingerAffinity_le_one q₀ q₁)
    fun h => hne (eq_of_hellingerAffinity_eq_one q₀ q₁ h)
  have hmap : ∀ (q : Measure BinaryLetter) [IsProbabilityMeasure q] (N : ℕ),
      (prefixProductLaw θ fun _ => q).map (prefixObserver N)
        = Measure.pi fun _ : Finset.range N => q := fun q _ N =>
    Measure.infinitePi_map_restrict (fun _ => q)
  refine mutuallySingular_of_tendsto_measurableHahnTV measurable_prefixObserver ?_
  simp only [hmap q₀, hmap q₁]
  have hlow : ∀ N : ℕ, 1 - a ^ N ≤ measurableHahnTV (Measure.pi fun _ : Finset.range N => q₀)
      (Measure.pi fun _ : Finset.range N => q₁) := by
    intro N
    have h := one_sub_measurableHahnTV_le_hellingerAffinity
      (Measure.pi fun _ : Finset.range N => q₀) (Measure.pi fun _ : Finset.range N => q₁)
    rw [hellingerAffinity_pi_dep, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
      Finset.card_range] at h
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow
    fun N => measurableHahnTV_le_one _ _
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_sub (1 : ℝ)

variable [Fact (0 < θ)] [Fact (θ < 1)]

/-- Deterministic kernels along `C`-Lipschitz maps have amplification at most `C`. -/
theorem resolutionAmplification_deterministic_le {X Z : Type*} [MetricSpace X]
    [MeasurableSpace X] [MetricSpace Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {h : X → Z} {C : ℝ≥0} (hh : LipschitzWith C h) (hmeas : Measurable h) :
    resolutionAmplification (Kernel.deterministic h hmeas) ≤ C := by
  have hpull : ∀ f : Z → ℝ, kernelPullback (Kernel.deterministic h hmeas) f = f ∘ h := by
    intro f
    funext x
    rw [kernelPullback, Kernel.deterministic_apply, integral_dirac]
    rfl
  refine iSup₂_le fun f _ => iSup_le fun hfin => ?_
  rw [hpull]
  refine ENNReal.div_le_of_le_mul ?_
  have hcomp : LipschitzWith ((lipNorm f).toNNReal * C) (f ∘ h) :=
    (lipschitzWith_of_lipNorm_lt_top hfin).comp hh
  refine (lipNorm_le hcomp).trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hfin.ne, mul_comm]

theorem lipschitzWith_prefixWord {d : ℕ} (hd : 1 ≤ d) :
    LipschitzWith ((θ ^ (d - 1))⁻¹).toNNReal (prefixWord (θ := θ) d) := by
  have hθ0 : 0 < θ := Fact.out
  have hθ1 : θ < 1 := Fact.out
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr (pow_nonneg hθ0.le _))]
  by_cases hw : prefixWord d x = prefixWord d y
  · rw [hw, dist_self]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hθ0.le _)) dist_nonneg
  obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hw (funext h)
  have hxy : x ≠ y := fun h => hi (h ▸ rfl)
  have hfd : firstDiff x y ≤ d - 1 := by
    have : firstDiff x y ≤ i := by
      by_contra h
      exact hi (apply_eq_of_lt_firstDiff (not_le.mp h))
    omega
  have hdist : θ ^ (d - 1) ≤ dist x y := by
    rw [PrefixSpace.dist_eq, prefixDist_eq_of_ne hxy]
    exact pow_le_pow_of_le_one hθ0.le hθ1.le hfd
  have hw1 : dist (prefixWord d x) (prefixWord d y) ≤ 1 :=
    (dist_pi_le_iff zero_le_one).mpr fun _ => BinaryLetter.dist_le_one _ _
  calc dist (prefixWord d x) (prefixWord d y) ≤ 1 := hw1
    _ = (θ ^ (d - 1))⁻¹ * θ ^ (d - 1) := (inv_mul_cancel₀ (pow_pos hθ0 _).ne').symm
    _ ≤ (θ ^ (d - 1))⁻¹ * dist x y :=
        mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr (pow_nonneg hθ0.le _))

/-- **Theorem 6.1 (4), (RP.22).**  `α(K_d) = θ^{-(d-1)}`. -/
theorem resolutionAmplification_prefixWordKernel {d : ℕ} (hd : 1 ≤ d) :
    resolutionAmplification (prefixWordKernel θ d) = ENNReal.ofReal ((θ ^ (d - 1))⁻¹) := by
  classical
  have hθ0 : 0 < θ := Fact.out
  have hθ1 : θ < 1 := Fact.out
  refine le_antisymm (resolutionAmplification_deterministic_le (lipschitzWith_prefixWord hd)
    (measurable_prefixWord d)) ?_
  set i₀ : Fin d := ⟨d - 1, by omega⟩ with hi₀
  set f : (Fin d → BinaryLetter) → ℝ := fun w => dist (w i₀) BinaryLetter.zero with hfdef
  have hflip : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun w w' => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    exact (abs_dist_sub_le _ _ _).trans (dist_le_pi_dist w w' i₀)
  have hfle : lipNorm f ≤ 1 := by simpa using lipNorm_le hflip
  have hffin : lipNorm f < ⊤ := hfle.trans_lt ENNReal.one_lt_top
  have hfge : ((1 : ℝ≥0) : ℝ≥0∞) ≤ lipNorm f := by
    set w₀ : Fin d → BinaryLetter := fun _ => BinaryLetter.zero
    have hne : Function.update w₀ i₀ BinaryLetter.one ≠ w₀ := fun h => by
      have := congrFun h i₀
      simp only [Function.update_self] at this
      exact BinaryLetter.one_ne_zero this
    refine le_lipNorm_of_abs_sub hne ?_
    rw [NNReal.coe_one, one_mul]
    have hd1 : dist (Function.update w₀ i₀ BinaryLetter.one) w₀ ≤ 1 :=
      (dist_pi_le_iff zero_le_one).mpr fun _ => BinaryLetter.dist_le_one _ _
    refine hd1.trans (le_of_eq ?_)
    simp [hfdef, w₀, BinaryLetter.dist_eq, BinaryLetter.one_ne_zero]
  have hfpos : 0 < lipNorm f := lt_of_lt_of_le (by simp) hfge
  set x₀ : BinarySequence θ := fun _ => BinaryLetter.zero
  set x₁ : BinarySequence θ := Function.update (fun _ : ℕ => BinaryLetter.zero) (d - 1)
    BinaryLetter.one
  have hx : x₁ ≠ x₀ := fun h => by
    have := congrFun h (d - 1)
    simp [x₁, x₀, BinaryLetter.one_ne_zero] at this
  have hcyl : x₁ ∈ cylinder (E := fun _ : ℕ => BinaryLetter) x₀ (d - 1) :=
    mem_cylinder_iff.2 fun i hi => by simp [x₁, x₀, Function.update_of_ne (Nat.ne_of_lt hi)]
  have hdist : dist x₁ x₀ ≤ θ ^ (d - 1) := by
    rw [PrefixSpace.dist_eq]
    exact (mem_cylinder_iff_prefixDist_le hθ0 hθ1).mp hcyl
  have hpull : ((((θ ^ (d - 1))⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞)
      ≤ lipNorm (kernelPullback (prefixWordKernel θ d) f) := by
    refine le_lipNorm_of_abs_sub hx ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (pow_nonneg hθ0.le _)),
      kernelPullback_prefixWordKernel]
    have hval : |(f ∘ prefixWord d) x₁ - (f ∘ prefixWord d) x₀| = 1 := by
      simp [hfdef, prefixWord, x₁, x₀, hi₀, BinaryLetter.dist_eq, BinaryLetter.one_ne_zero]
    rw [hval]
    calc (θ ^ (d - 1))⁻¹ * dist x₁ x₀ ≤ (θ ^ (d - 1))⁻¹ * θ ^ (d - 1) :=
          mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr (pow_nonneg hθ0.le _))
      _ = 1 := inv_mul_cancel₀ (pow_pos hθ0 _).ne'
  have hratio : lipNorm (kernelPullback (prefixWordKernel θ d) f) / lipNorm f
      ≤ resolutionAmplification (prefixWordKernel θ d) :=
    le_iSup₂_of_le (f := fun (g : (Fin d → BinaryLetter) → ℝ) (_ : 0 < lipNorm g) =>
      ⨆ (_ : lipNorm g < ⊤), lipNorm (kernelPullback (prefixWordKernel θ d) g) / lipNorm g)
      f hfpos (le_iSup_of_le hffin le_rfl)
  refine le_trans ?_ hratio
  calc ENNReal.ofReal ((θ ^ (d - 1))⁻¹)
      ≤ lipNorm (kernelPullback (prefixWordKernel θ d) f) := hpull
    _ = lipNorm (kernelPullback (prefixWordKernel θ d) f) / 1 := (div_one _).symm
    _ ≤ lipNorm (kernelPullback (prefixWordKernel θ d) f) / lipNorm f :=
        ENNReal.div_le_div_left hfle _

/-- The amplification of the prefix kernels escapes: `α(K_d) → ∞`. -/
theorem tendsto_resolutionAmplification_prefixWordKernel :
    Tendsto (fun d => resolutionAmplification (prefixWordKernel θ d)) atTop (𝓝 ⊤) := by
  have hθ0 : 0 < θ := Fact.out
  have hθ1 : θ < 1 := Fact.out
  have hev : (fun d => ENNReal.ofReal ((θ ^ (d - 1))⁻¹))
      =ᶠ[atTop] fun d => resolutionAmplification (prefixWordKernel θ d) :=
    (eventually_ge_atTop 1).mono fun d hd => (resolutionAmplification_prefixWordKernel hd).symm
  refine Tendsto.congr' hev (ENNReal.tendsto_ofReal_atTop.comp ?_)
  have h1 : Tendsto (fun d : ℕ => d - 1) atTop atTop := tendsto_sub_atTop_nat 1
  have h2 : Tendsto (fun n : ℕ => (θ ^ n)⁻¹) atTop atTop := by
    simp_rw [← inv_pow]
    exact tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hθ0 |>.mpr hθ1)
  exact h2.comp h1

/-- **Theorem 6.1.**  Exact Feller formation of every depth from full-support singular laws, with
exactly exponential resolution escape. -/
theorem prefixBernoulli_fellerEscape {q₀ q₁ : Measure BinaryLetter} [IsProbabilityMeasure q₀]
    [IsProbabilityMeasure q₁] (h₀ : ∀ b, q₀ {b} ≠ 0) (h₁ : ∀ b, q₁ {b} ≠ 0) (hne : q₀ ≠ q₁)
    {d : ℕ} (hd : 1 ≤ d) :
    (prefixProductLaw θ fun _ => q₀).IsOpenPosMeasure ∧
      (prefixProductLaw θ fun _ => q₁).IsOpenPosMeasure ∧
      (prefixProductLaw θ fun _ => q₀) ⟂ₘ (prefixProductLaw θ fun _ => q₁) ∧
      (∀ f, Continuous (kernelPullback (prefixWordKernel θ d) f)) ∧
      IsExactFormation (prefixProductLaw θ fun _ => q₀) (prefixWordKernel θ d) q₀ ∧
      IsExactFormation (prefixProductLaw θ fun _ => q₁) (prefixWordKernel θ d) q₁ ∧
      resolutionAmplification (prefixWordKernel θ d) = ENNReal.ofReal ((θ ^ (d - 1))⁻¹) :=
  ⟨isOpenPosMeasure_prefixProductLaw q₀ h₀, isOpenPosMeasure_prefixProductLaw q₁ h₁,
    prefixProductLaw_mutuallySingular hne, continuous_kernelPullback_prefixWordKernel d,
    isExactFormation_prefixWordKernel q₀ d, isExactFormation_prefixWordKernel q₁ d,
    resolutionAmplification_prefixWordKernel hd⟩

end PrefixKernel

end GaloisForLFunctions.HTGeometry
