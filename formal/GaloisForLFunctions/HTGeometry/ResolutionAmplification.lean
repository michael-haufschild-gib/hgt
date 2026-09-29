import GaloisForLFunctions.HTGeometry.ResolutionPriceCurve

/-!
# Resolution amplification of Markov kernels

For a Markov kernel `K : X ⇝ Z` between metric spaces the effect pullback is
`K^* f(x) = ∫ f dK(x, ·)`, and its resolution amplification is the extended operator seminorm

`α(K) = sup_{0 < Lip f < ∞} Lip(K^* f) / Lip(f) ∈ [0, ∞]`.

Amplifications multiply under composition, `α(L ∘ K) ≤ α(K) α(L)`: if `α(K) = 0` all transition
laws of `K` coincide, because bounded Lipschitz functions determine finite Borel measures;
otherwise the Lipschitz pullback bounds chain.  A deterministic isometric kernel has amplification
one.  An exact depth-`d` formation into a target in which distinct points are at distance at least
one pulls a Neyman–Pearson event back to an effect with contrast `TV(p₀^{⊗d}, p₁^{⊗d})` and
Lipschitz constant between `𝓡_μ(TV)` and `α(K_d)`, so `α(K_d) ≥ 𝓡_μ(1 - A^d)`; for full-support
laws on a compact space and `0 < A < 1` every all-depth exact formation has `α(K_d) → ∞`, in
every metric compatible with the topology.
-/

open MeasureTheory Set Filter Topology Metric ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Lipschitz functions determine finite measures -/

section Determine

variable {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- The Lipschitz approximants `max 0 (1 - (n+1) d(x, F))` of the indicator of a closed set. -/
def closedApprox (F : Set Z) (n : ℕ) (x : Z) : ℝ := max 0 (1 - ((n : ℝ) + 1) * infDist x F)

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem closedApprox_mem (F : Set Z) (n : ℕ) (x : Z) : closedApprox F n x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (by
    have : 0 ≤ ((n : ℝ) + 1) * infDist x F := mul_nonneg (by positivity) infDist_nonneg
    linarith)⟩

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem lipschitzWith_closedApprox (F : Set Z) (n : ℕ) :
    LipschitzWith (⟨(n : ℝ) + 1, by positivity⟩ : ℝ≥0) (closedApprox F n) := by
  have h1 : LipschitzWith (⟨(n : ℝ) + 1, by positivity⟩ : ℝ≥0)
      (fun x => 1 - ((n : ℝ) + 1) * infDist x F) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := (lipschitz_infDist_pt F).dist_le_mul x y
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at h
    change dist _ _ ≤ ((n : ℝ) + 1) * dist x y
    rw [Real.dist_eq]
    calc |1 - ((n : ℝ) + 1) * infDist x F - (1 - ((n : ℝ) + 1) * infDist y F)|
        = ((n : ℝ) + 1) * |infDist x F - infDist y F| := by
          rw [show 1 - ((n : ℝ) + 1) * infDist x F - (1 - ((n : ℝ) + 1) * infDist y F)
            = -(((n : ℝ) + 1) * (infDist x F - infDist y F)) by ring, abs_neg, abs_mul,
            abs_of_pos (by positivity)]
      _ ≤ ((n : ℝ) + 1) * dist x y := mul_le_mul_of_nonneg_left h (by positivity)
  exact h1.const_max 0

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem tendsto_closedApprox {F : Set Z} (hF : IsClosed F) (hne : F.Nonempty) (x : Z) :
    Tendsto (fun n => closedApprox F n x) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ F
  · rw [indicator_of_mem hx]
    refine tendsto_const_nhds.congr fun n => ?_
    simp [closedApprox, infDist_zero_of_mem hx]
  · rw [indicator_of_notMem hx]
    have hpos : 0 < infDist x F := by
      rcases (infDist_nonneg (x := x) (s := F)).lt_or_eq with h | h
      · exact h
      · exact absurd ((hF.mem_iff_infDist_zero hne).mpr h.symm) hx
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist x F)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : 1 / infDist x F < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hpos] at hn'
    simp only [closedApprox]
    rw [max_eq_left (by linarith)]

/-- **Bounded Lipschitz test functions determine finite Borel measures.** -/
theorem measure_eq_of_integral_lipschitz_eq {μ ν : Measure Z} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ f : Z → ℝ, (∃ K : ℝ≥0, LipschitzWith K f) → (∀ z, f z ∈ Icc (0 : ℝ) 1) →
      ∫ z, f z ∂μ = ∫ z, f z ∂ν) : μ = ν := by
  have hclosed : ∀ F : Set Z, IsClosed F → μ F = ν F := by
    intro F hF
    rcases F.eq_empty_or_nonempty with hemp | hne
    · simp [hemp]
    have hlim : ∀ (ρ : Measure Z) [IsFiniteMeasure ρ],
        Tendsto (fun n => ∫ z, closedApprox F n z ∂ρ) atTop (𝓝 (ρ.real F)) := by
      intro ρ _
      have h := tendsto_integral_of_dominated_convergence (μ := ρ) (fun _ => (1 : ℝ))
        (fun n => (lipschitzWith_closedApprox F n).continuous.aestronglyMeasurable)
        (integrable_const 1)
        (fun n => Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (closedApprox_mem F n z).1]
          exact (closedApprox_mem F n z).2)
        (Eventually.of_forall fun z => tendsto_closedApprox hF hne z)
      rwa [integral_indicator_const _ hF.measurableSet, smul_eq_mul, mul_one] at h
    have hμ := hlim μ
    have hν := hlim ν
    simp_rw [h _ ⟨_, lipschitzWith_closedApprox F _⟩ (closedApprox_mem F _)] at hμ
    have := tendsto_nhds_unique hμ hν
    rw [Measure.real_def, Measure.real_def] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ F) (measure_ne_top ν F)).mp this
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F hF => hclosed F hF
  · exact hclosed _ isClosed_univ
  · rw [BorelSpace.measurable_eq (α := Z), borel_eq_generateFrom_isClosed]

end Determine

/-! ## Amplification -/

section Amplification

variable {X Z W : Type*} [MetricSpace X] [MeasurableSpace X] [MetricSpace Z] [MeasurableSpace Z]
  [MetricSpace W] [MeasurableSpace W]

/-- **(RP.7).**  The effect pullback `K^* f(x) = ∫ f dK(x, ·)`. -/
def kernelPullback (K : Kernel X Z) (f : Z → ℝ) (x : X) : ℝ := ∫ z, f z ∂(K x)

/-- **(RP.8).**  The resolution amplification `α(K)`. -/
def resolutionAmplification (K : Kernel X Z) : ℝ≥0∞ :=
  ⨆ (f : Z → ℝ) (_ : 0 < lipNorm f) (_ : lipNorm f < ⊤), lipNorm (kernelPullback K f) / lipNorm f

omit [MetricSpace X] [MetricSpace Z] in
theorem kernelPullback_const (K : Kernel X Z) [IsMarkovKernel K] (c : ℝ) :
    kernelPullback K (fun _ => c) = fun _ => c := by
  funext x
  simp [kernelPullback]

/-- `Lip(K^* f) ≤ α(K) Lip(f)` for every Lipschitz `f`. -/
theorem lipNorm_kernelPullback_le (K : Kernel X Z) [IsMarkovKernel K] {f : Z → ℝ}
    (hf : lipNorm f < ⊤) :
    lipNorm (kernelPullback K f) ≤ resolutionAmplification K * lipNorm f := by
  rcases eq_or_ne (lipNorm f) 0 with hzero | hne
  swap
  · have hpos : 0 < lipNorm f := pos_iff_ne_zero.mpr hne
    have h : lipNorm (kernelPullback K f) / lipNorm f ≤ resolutionAmplification K :=
      le_iSup₂_of_le (f := fun (g : Z → ℝ) (_ : 0 < lipNorm g) =>
        ⨆ (_ : lipNorm g < ⊤), lipNorm (kernelPullback K g) / lipNorm g) f hpos
        (le_iSup_of_le hf le_rfl)
    exact (ENNReal.div_le_iff hpos.ne' hf.ne).mp h
  · have hK0 : LipschitzWith 0 (kernelPullback K f) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      obtain ⟨z₀⟩ := nonempty_of_isProbabilityMeasure (K x)
      have hfc : f = fun _ => f z₀ := funext fun z => eq_of_lipNorm_eq_zero hzero z z₀
      rw [hfc, kernelPullback_const]
      simp
    rw [hzero, mul_zero]
    exact (lipNorm_le hK0).trans (by simp)

/-- Zero amplification forces all transition laws to coincide. -/
theorem kernel_eq_of_resolutionAmplification_eq_zero [BorelSpace Z] (K : Kernel X Z)
    [IsMarkovKernel K] (hK : resolutionAmplification K = 0) (x x' : X) : K x = K x' := by
  refine measure_eq_of_integral_lipschitz_eq fun f ⟨L, hL⟩ hf => ?_
  have hfin : lipNorm f < ⊤ := (lipNorm_le hL).trans_lt ENNReal.coe_lt_top
  have h := lipNorm_kernelPullback_le K hfin
  rw [hK, zero_mul] at h
  exact eq_of_lipNorm_eq_zero (le_antisymm h bot_le) x x'

theorem integrable_of_lipNorm_lt_top [CompactSpace Z] [BorelSpace Z] {f : Z → ℝ}
    (hf : lipNorm f < ⊤) (μ : Measure Z) [IsFiniteMeasure μ] : Integrable f μ :=
  (lipschitzWith_of_lipNorm_lt_top hf).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Theorem 3.1 (RP.10).**  Amplifications multiply under composition of Markov kernels. -/
theorem resolutionAmplification_comp [BorelSpace Z] [CompactSpace W] [BorelSpace W]
    (K : Kernel X Z) (L : Kernel Z W) [IsMarkovKernel K] [IsMarkovKernel L] :
    resolutionAmplification (L.comp K)
      ≤ resolutionAmplification K * resolutionAmplification L := by
  refine iSup₂_le fun f hpos => iSup_le fun hfin => ?_
  have hcomp : kernelPullback (L.comp K) f = kernelPullback K (kernelPullback L f) := by
    funext x
    exact Kernel.integral_comp (integrable_of_lipNorm_lt_top hfin _)
  rw [hcomp]
  by_cases hK0 : resolutionAmplification K = 0
  · have hconst : lipNorm (kernelPullback K (kernelPullback L f)) = 0 := by
      refine le_antisymm ((lipNorm_le (K := 0) ?_).trans (by simp)) bot_le
      refine LipschitzWith.of_dist_le_mul fun x x' => ?_
      simp [kernelPullback, kernel_eq_of_resolutionAmplification_eq_zero K hK0 x x']
    rw [hconst, ENNReal.zero_div]
    exact bot_le
  by_cases hLf : lipNorm (kernelPullback L f) = ⊤
  · have hLtop : resolutionAmplification L = ⊤ := by
      refine eq_top_iff.mpr ?_
      have h : lipNorm (kernelPullback L f) / lipNorm f ≤ resolutionAmplification L :=
        le_iSup₂_of_le (f := fun (g : W → ℝ) (_ : 0 < lipNorm g) =>
          ⨆ (_ : lipNorm g < ⊤), lipNorm (kernelPullback L g) / lipNorm g) f hpos
          (le_iSup_of_le hfin le_rfl)
      rwa [hLf, ENNReal.top_div_of_ne_top hfin.ne] at h
    rw [hLtop, ENNReal.mul_top hK0]
    exact le_top
  have h1 := lipNorm_kernelPullback_le K (lt_top_iff_ne_top.mpr hLf)
  have h2 := lipNorm_kernelPullback_le L hfin
  refine ENNReal.div_le_of_le_mul ?_
  calc lipNorm (kernelPullback K (kernelPullback L f))
      ≤ resolutionAmplification K * lipNorm (kernelPullback L f) := h1
    _ ≤ resolutionAmplification K * (resolutionAmplification L * lipNorm f) := by gcongr
    _ = resolutionAmplification K * resolutionAmplification L * lipNorm f := by ring

omit [MeasurableSpace X] in
theorem le_lipNorm_of_abs_sub {f : X → ℝ} {x y : X} (hxy : x ≠ y) {c : ℝ≥0}
    (h : (c : ℝ) * dist x y ≤ |f x - f y|) : (c : ℝ≥0∞) ≤ lipNorm f := by
  refine le_iInf₂ fun K hK => ?_
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have h2 := hK.dist_le_mul x y
  rw [Real.dist_eq] at h2
  have : (c : ℝ) ≤ K := le_of_mul_le_mul_right (h.trans h2) hd
  exact_mod_cast this

/-- **Theorem 3.1.**  A deterministic isometric kernel has amplification one. -/
theorem resolutionAmplification_deterministic_isometry [BorelSpace Z] {h : X → Z}
    (hh : Isometry h) (hmeas : Measurable h) {x₀ x₁ : X} (hne : x₀ ≠ x₁) :
    resolutionAmplification (Kernel.deterministic h hmeas) = 1 := by
  have hpull : ∀ f : Z → ℝ, kernelPullback (Kernel.deterministic h hmeas) f = f ∘ h := by
    intro f
    funext x
    rw [kernelPullback, Kernel.deterministic_apply, integral_dirac]
    rfl
  apply le_antisymm
  · refine iSup₂_le fun f hpos => iSup_le fun hfin => ?_
    rw [hpull]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    have hlip := lipschitzWith_of_lipNorm_lt_top hfin
    have hcomp : LipschitzWith (lipNorm f).toNNReal (f ∘ h) := by
      simpa using hlip.comp hh.lipschitz
    exact (lipNorm_le hcomp).trans (by rw [ENNReal.coe_toNNReal hfin.ne])
  · set f : Z → ℝ := fun z => dist z (h x₀) with hfdef
    have hflip : LipschitzWith 1 f := LipschitzWith.dist_left (h x₀)
    have hfle : lipNorm f ≤ 1 := by simpa using lipNorm_le hflip
    have hcomp1 : ((1 : ℝ≥0) : ℝ≥0∞) ≤ lipNorm (f ∘ h) := by
      refine le_lipNorm_of_abs_sub hne.symm (f := f ∘ h) ?_
      simp only [Function.comp_apply, hfdef, hh.dist_eq, dist_self, sub_zero, NNReal.coe_one,
        one_mul]
      exact le_abs_self _
    have hfpos : 0 < lipNorm f := by
      have hcomp : LipschitzWith (lipNorm f).toNNReal (f ∘ h) := by
        simpa using (lipschitzWith_of_lipNorm_lt_top (hfle.trans_lt ENNReal.one_lt_top)).comp
          hh.lipschitz
      have := hcomp1.trans (lipNorm_le hcomp)
      rw [ENNReal.coe_toNNReal (hfle.trans_lt ENNReal.one_lt_top).ne] at this
      exact lt_of_lt_of_le (by simp) this
    have hratio : lipNorm (kernelPullback (Kernel.deterministic h hmeas) f) / lipNorm f
        ≤ resolutionAmplification (Kernel.deterministic h hmeas) :=
      le_iSup₂_of_le (f := fun (g : Z → ℝ) (_ : 0 < lipNorm g) =>
        ⨆ (_ : lipNorm g < ⊤), lipNorm (kernelPullback (Kernel.deterministic h hmeas) g)
          / lipNorm g) f hfpos (le_iSup_of_le (hfle.trans_lt ENNReal.one_lt_top) le_rfl)
    refine le_trans ?_ hratio
    rw [hpull]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hfpos.ne') (Or.inl (hfle.trans_lt
      ENNReal.one_lt_top).ne), one_mul]
    exact hfle.trans (by simpa using hcomp1)

end Amplification

/-! ## The resolution-price formation law -/

section FormationLaw

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {Y : Type*} [Fintype Y] [MetricSpace Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]

omit [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] in
/-- In a target whose distinct points are at distance at least one, every event indicator is
one-Lipschitz. -/
theorem lipschitzWith_indicator_pi {d : ℕ} (hsep : ∀ y y' : Y, y ≠ y' → 1 ≤ dist y y')
    (B : Set (Fin d → Y)) : LipschitzWith 1 (B.indicator fun _ => (1 : ℝ)) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [NNReal.coe_one, one_mul]
  by_cases hzz : z = z'
  · rw [hzz, dist_self, dist_self]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hzz
  have h1 : 1 ≤ dist z z' := (hsep _ _ hi).trans (dist_le_pi_dist z z' i)
  have h2 : dist (B.indicator (fun _ => (1 : ℝ)) z) (B.indicator (fun _ => (1 : ℝ)) z') ≤ 1 := by
    rw [Real.dist_eq]
    by_cases hz : z ∈ B <;> by_cases hz' : z' ∈ B <;> simp [hz, hz']
  linarith

omit [MetricSpace X] [Fintype Y] [MetricSpace Y] [MeasurableSingletonClass Y] in
theorem formationEffect_eq_kernelPullback {d : ℕ} (K : Kernel X (Fin d → Y)) [IsMarkovKernel K]
    {B : Set (Fin d → Y)} (hB : MeasurableSet B) :
    formationEffect K B = kernelPullback K (B.indicator fun _ => (1 : ℝ)) := by
  funext x
  rw [formationEffect, kernelPullback, integral_indicator_const _ hB, smul_eq_mul, mul_one,
    Measure.real_def]

/-- **Theorem 4.1 (RP.13).**  The formed effect carries the target total variation, and its
Lipschitz constant lies between the resolution price of that contrast and `α(K_d)`. -/
theorem formation_resolutionPrice_law (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hsep : ∀ y y' : Y, y ≠ y' → 1 ≤ dist y y') (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] {d : ℕ} (K : Kernel X (Fin d → Y))
    [IsMarkovKernel K] (h₀ : IsExactFormation P K p₀) (h₁ : IsExactFormation Q K p₁)
    {B : Set (Fin d → Y)} (hNP : IsNeymanPearson p₀ p₁ B) :
    hahnEffectCurrent P Q (formationEffect K B)
        = measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁) ∧
      lipNorm (formationEffect K B) ≤ resolutionAmplification K ∧
      lipschitzResolutionPrice P Q
          (measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁))
        ≤ lipNorm (formationEffect K B) := by
  obtain ⟨hB, hNPv⟩ := hNP
  have hcur := (hahnEffectCurrent_formation P Q p₀ p₁ K h₀ h₁ hB hNPv).1
  refine ⟨hcur, ?_, ?_⟩
  · rw [formationEffect_eq_kernelPullback K hB]
    have hlip := lipschitzWith_indicator_pi hsep B
    have hfin : lipNorm (B.indicator fun _ => (1 : ℝ)) < ⊤ :=
      (lipNorm_le hlip).trans_lt ENNReal.coe_lt_top
    refine (lipNorm_kernelPullback_le K hfin).trans ?_
    calc resolutionAmplification K * lipNorm (B.indicator fun _ => (1 : ℝ))
        ≤ resolutionAmplification K * 1 := by
          gcongr
          simpa using lipNorm_le hlip
      _ = resolutionAmplification K := mul_one _
  · exact lipschitzResolutionPrice_le P Q (formationEffect_mem K B) hcur.ge

/-- **(RP.14).**  `α(K_d) ≥ 𝓡_μ(1 - A^d)`. -/
theorem resolutionPrice_le_resolutionAmplification (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hsep : ∀ y y' : Y, y ≠ y' → 1 ≤ dist y y') (p₀ p₁ : Measure Y)
    [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] {d : ℕ} (K : Kernel X (Fin d → Y))
    [IsMarkovKernel K] (h₀ : IsExactFormation P K p₀) (h₁ : IsExactFormation Q K p₁)
    {B : Set (Fin d → Y)} (hNP : IsNeymanPearson p₀ p₁ B) :
    lipschitzResolutionPrice P Q (1 - hellingerAffinity p₀ p₁ ^ d)
      ≤ resolutionAmplification K := by
  obtain ⟨-, h2, h3⟩ := formation_resolutionPrice_law P Q hsep p₀ p₁ K h₀ h₁ hNP
  exact (lipschitzResolutionPrice_mono P Q (one_sub_hellingerAffinity_pow_le p₀ p₁ d)).trans
    (h3.trans h2)

/-- **(RP.15), Corollary 4.2.**  For full-support laws on a compact space and `0 < A < 1`, every
all-depth exact formation has diverging amplification, in whatever compatible metric `X`
carries. -/
theorem tendsto_resolutionAmplification [BorelSpace X] [CompactSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [P.IsOpenPosMeasure] [Q.IsOpenPosMeasure]
    (hsep : ∀ y y' : Y, y ≠ y' → 1 ≤ dist y y') (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀]
    [IsProbabilityMeasure p₁] (hA0 : 0 < hellingerAffinity p₀ p₁)
    (hA1 : hellingerAffinity p₀ p₁ < 1) (K : ∀ d : ℕ, Kernel X (Fin d → Y))
    [∀ d, IsMarkovKernel (K d)] (h₀ : ∀ d, IsExactFormation P (K d) p₀)
    (h₁ : ∀ d, IsExactFormation Q (K d) p₁) (B : ∀ d : ℕ, Set (Fin d → Y))
    (hNP : ∀ d, IsNeymanPearson p₀ p₁ (B d)) :
    Tendsto (fun d => resolutionAmplification (K d)) atTop (𝓝 ⊤) := by
  have hlim : Tendsto (fun d : ℕ => 1 - hellingerAffinity p₀ p₁ ^ d) atTop (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun d => ?_⟩
    · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hA0.le hA1).const_sub 1
      simpa using h
    · have : 0 < hellingerAffinity p₀ p₁ ^ d := pow_pos hA0 d
      simp only [mem_Iio]
      linarith
  have hprice := (tendsto_lipschitzResolutionPrice_one P Q).comp hlim
  exact tendsto_nhds_top_mono hprice (Eventually.of_forall fun d =>
    resolutionPrice_le_resolutionAmplification P Q hsep p₀ p₁ (K d) (h₀ d) (h₁ d) (hNP d))

end FormationLaw

end GaloisForLFunctions.HTGeometry
