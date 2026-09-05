import GaloisForLFunctions.RHTower.WallFirstBoundarySquareIntegrable
import GaloisForLFunctions.RHTower.BlockSliceFrequencyWeight

/-!
# The first boundary term after multiplication by the frequency

Multiplication by the frequency is physical differentiation.  On a block slice it replaces the
profile by its *weighted corrected* derivative `e^{-Ls}(g′ − s g)`, so the Laplace amplitude picks
up one power of `s`; the accretive floor pays for it, turning `1/μ` into `1/μ + 4/μ²`.

That is the exact mechanism behind the card's remark that the leading nonhomogeneous boundary term
is square integrable after multiplication by the frequency *precisely* under the residual condition
`(43)`: the condition is what supplies the block's derivative energy, and the resolvent contributes
only the harmless extra power of the floor.

A profile vanishing off a closed block has a derivative vanishing there too — the complement is
open — so no separate support hypothesis on the derivative is needed.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

omit [CompleteSpace X] in
/-- A profile vanishing off a closed block has a derivative vanishing there too. -/
theorem deriv_vanishes_off_block {g g' : ℝ → X} {m : ℝ} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    ∀ L : ℝ, L ∉ Icc m (m + 1) → g' L = 0 := by
  intro L hL
  have hopen : IsOpen (Icc m (m + 1))ᶜ := isClosed_Icc.isOpen_compl
  have hev : g =ᶠ[nhds L] (fun _ : ℝ => (0 : X)) := by
    filter_upwards [hopen.mem_nhds hL] with y hy
    exact hsupp y hy
  have h0 : HasDerivAt g 0 L := (hasDerivAt_const L (0 : X)).congr_of_eventuallyEq hev
  exact (hg L).unique h0

/-- The frequency-weighted cut slice. -/
def freqCutSlice (g : ℝ → X) (A : Set ℝ) (x s : ℝ) : X := x • cutSlice g A x s

omit [CompleteSpace X] in
theorem freqCutSlice_eq_zero {g : ℝ → X} {A : Set ℝ} (s : ℝ) {x : ℝ} (hx : x ∉ A) :
    freqCutSlice g A x s = 0 := by
  rw [freqCutSlice, cutSlice, Set.indicator_of_notMem hx, smul_zero]

omit [CompleteSpace X] in
theorem norm_freqCutSlice_le {g g' : ℝ → X} {A : Set ℝ} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    {s : ℝ} (hint : Integrable (blockWeighted g s))
    (hdint : Integrable (blockWeighted (fun M => g' M - s • g M) s)) (x : ℝ) :
    ‖freqCutSlice g A x s‖ ≤ ‖blockSlice (fun M => g' M - s • g M) s x‖ := by
  rw [freqCutSlice, norm_smul, Real.norm_eq_abs, cutSlice]
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    exact le_of_eq (norm_freq_smul_blockSlice_eq hg hint hdint x)
  · rw [Set.indicator_of_notMem hx, norm_zero, mul_zero]
    exact norm_nonneg _

/-- The corrected derivative profile of a block. -/
def blockCorrectedDeriv (g g' : ℝ → X) (s : ℝ) : ℝ → X := fun M => g' M - s • g M

omit [CompleteSpace X] in
theorem blockCorrectedDeriv_supp {g g' : ℝ → X} {m s : ℝ}
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hsupp' : ∀ L : ℝ, L ∉ Icc m (m + 1) → g' L = 0) :
    ∀ L : ℝ, L ∉ Icc m (m + 1) → blockCorrectedDeriv g g' s L = 0 := by
  intro L hL
  rw [blockCorrectedDeriv, hsupp L hL, hsupp' L hL, smul_zero, sub_zero]

omit [CompleteSpace X] in
theorem memLp_blockCorrectedDeriv {g g' : ℝ → X} {s : ℝ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hg'2 : MemLp g' 2 (volume : Measure ℝ)) :
    MemLp (blockCorrectedDeriv g g' s) 2 (volume : Measure ℝ) :=
  hg'2.sub (hg2.const_smul s)

omit [CompleteSpace X] in
/-- **The corrected derivative costs an affine amount of energy.** -/
theorem integral_norm_sq_blockCorrectedDeriv_le {g g' : ℝ → X} {s : ℝ} (hs : 0 ≤ s)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hg'2 : MemLp g' 2 (volume : Measure ℝ)) :
    (2 * Real.pi) * ∫ L : ℝ, ‖blockCorrectedDeriv g g' s L‖ ^ 2
      ≤ (Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2)
          + Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2) * s) ^ 2 := by
  have hgsq : Integrable (fun L : ℝ => ‖g L‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).mp hg2
  have hg'sq : Integrable (fun L : ℝ => ‖g' L‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hg'2.aestronglyMeasurable).mp hg'2
  have hhsq : Integrable (fun L : ℝ => ‖blockCorrectedDeriv g g' s L‖ ^ 2)
      (volume : Measure ℝ) := by
    have hh := memLp_blockCorrectedDeriv (s := s) hg2 hg'2
    exact (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  have hmaj : Integrable (fun L : ℝ => 2 * (‖g' L‖ ^ 2 + s ^ 2 * ‖g L‖ ^ 2))
      (volume : Measure ℝ) := (hg'sq.add (hgsq.const_mul (s ^ 2))).const_mul 2
  have hpt : ∀ L : ℝ, ‖blockCorrectedDeriv g g' s L‖ ^ 2
      ≤ 2 * (‖g' L‖ ^ 2 + s ^ 2 * ‖g L‖ ^ 2) := by
    intro L
    have htri : ‖blockCorrectedDeriv g g' s L‖ ≤ ‖g' L‖ + s * ‖g L‖ := by
      rw [blockCorrectedDeriv]
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, Real.norm_of_nonneg hs]
    have hnn : (0 : ℝ) ≤ ‖blockCorrectedDeriv g g' s L‖ := norm_nonneg _
    nlinarith [norm_nonneg (g L), norm_nonneg (g' L), sq_nonneg (‖g' L‖ - s * ‖g L‖)]
  have hint := integral_mono hhsq hmaj hpt
  rw [integral_const_mul, integral_add hg'sq (hgsq.const_mul (s ^ 2)),
    integral_const_mul] at hint
  have hA : (0 : ℝ) ≤ ∫ L : ℝ, ‖g' L‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hB : (0 : ℝ) ≤ ∫ L : ℝ, ‖g L‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq₀ : Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2) ^ 2
      = 4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hsq₁ : Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2) ^ 2
      = 4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hcross : (0 : ℝ) ≤ 2 * s * (Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2)
      * Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2)) := by
    have := Real.sqrt_nonneg (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2)
    have := Real.sqrt_nonneg (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2)
    positivity
  nlinarith [hint, hsq₀, hsq₁, hcross]

/-- **The frequency-weighted slice has an affine amplitude.** -/
theorem lintegral_sq_freqCutSlice_le {g g' : ℝ → X} {A : Set ℝ} {m s : ℝ} (hs : 0 < s)
    (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hg'2 : MemLp g' 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫⁻ x : ℝ, ‖freqCutSlice g A x s‖ₑ ^ 2)
      ≤ ENNReal.ofReal (Real.exp (-(2 * s * m)))
        * ENNReal.ofReal ((Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2)
            + Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2) * s) ^ 2) := by
  have hsupp' := deriv_vanishes_off_block hg hsupp
  have hh2 : MemLp (blockCorrectedDeriv g g' s) 2 (volume : Measure ℝ) :=
    memLp_blockCorrectedDeriv hg2 hg'2
  have hhsupp := blockCorrectedDeriv_supp (s := s) hsupp hsupp'
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hh1 : Integrable (blockCorrectedDeriv g g' s) := integrable_zeroExtension hh2 hhsupp
  have hint : Integrable (blockWeighted g s) := integrable_blockWeighted hs.le hg1 hsupp
  have hdint : Integrable (blockWeighted (blockCorrectedDeriv g g' s) s) :=
    integrable_blockWeighted hs.le hh1 hhsupp
  have hpt : ∀ x : ℝ, ‖freqCutSlice g A x s‖ₑ ^ 2
      ≤ ‖blockSlice (blockCorrectedDeriv g g' s) s x‖ₑ ^ 2 := by
    intro x
    refine pow_le_pow_left' ?_ 2
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_freqCutSlice_le hg hint hdint x)
  have hwsq : Integrable
      (fun x : ℝ => ‖blockSlice (blockCorrectedDeriv g g' s) s x‖ ^ 2) (volume : Measure ℝ) := by
    have hw1 : Integrable (blockWeighted (blockCorrectedDeriv g g' s) s) := hdint
    have hw2 : MemLp (blockWeighted (blockCorrectedDeriv g g' s) s) 2 (volume : Measure ℝ) :=
      memLp_blockWeighted hs.le hh2 hhsupp
    exact integrable_norm_sq_vectorAngularTransform hw1 hw2
  have hslice := integral_norm_sq_blockSlice_le (g := blockCorrectedDeriv g g' s) hs.le hh2 hhsupp
  have henergy := integral_norm_sq_blockCorrectedDeriv_le (g := g) (g' := g') hs.le hg2 hg'2
  calc (∫⁻ x : ℝ, ‖freqCutSlice g A x s‖ₑ ^ 2)
      ≤ ∫⁻ x : ℝ, ‖blockSlice (blockCorrectedDeriv g g' s) s x‖ₑ ^ 2 := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ x : ℝ, ‖blockSlice (blockCorrectedDeriv g g' s) s x‖ ^ 2) :=
        lintegral_enorm_sq_eq_ofReal_integral hwsq
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * s * m))
          * ((Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2)
            + Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2) * s) ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal (hslice.trans ?_)
        exact mul_le_mul_of_nonneg_left henergy (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (-(2 * s * m)))
          * ENNReal.ofReal ((Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2)
            + Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2) * s) ^ 2) :=
        ENNReal.ofReal_mul (Real.exp_pos _).le

/-- The frequency-weighted semigroup integrand is measurable. -/
theorem measurable_semigroup_freqCutSlice {g : ℝ → X} (hgm : StronglyMeasurable g)
    {A : Set ℝ} (hA : MeasurableSet A) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Measurable (Function.uncurry fun x s : ℝ =>
      ‖accretiveSemigroup (wallGenerator T σ x) s (freqCutSlice g A x s)‖ₑ) := by
  have hbase := measurable_semigroup_cutSlice (T := T) hgm hA hσ0 hσ1
  have habs : Measurable fun p : ℝ × ℝ => ENNReal.ofReal |p.1| := by fun_prop
  have heq : (Function.uncurry fun x s : ℝ =>
      ‖accretiveSemigroup (wallGenerator T σ x) s (freqCutSlice g A x s)‖ₑ)
      = fun p : ℝ × ℝ => ENNReal.ofReal |p.1|
        * (Function.uncurry fun x s : ℝ =>
            ‖accretiveSemigroup (wallGenerator T σ x) s (cutSlice g A x s)‖ₑ) p := by
    funext p
    show ‖accretiveSemigroup (wallGenerator T σ p.1) p.2 (freqCutSlice g A p.1 p.2)‖ₑ
      = ENNReal.ofReal |p.1| * ‖accretiveSemigroup (wallGenerator T σ p.1) p.2
        (cutSlice g A p.1 p.2)‖ₑ
    show ‖accretiveSemigroup (wallGenerator T σ p.1) p.2 (p.1 • cutSlice g A p.1 p.2)‖ₑ
      = ENNReal.ofReal |p.1| * ‖accretiveSemigroup (wallGenerator T σ p.1) p.2
        (cutSlice g A p.1 p.2)‖ₑ
    rw [← Complex.coe_smul, map_smul, enorm_smul, ← ofReal_norm]
    simp [Real.norm_eq_abs]
  rw [heq]
  exact habs.mul hbase

/-- **The frequency-weighted first boundary term.**  Multiplication by the frequency is physical
differentiation, so the estimate costs the block's derivative energy and one more power of the
floor. -/
theorem lintegral_sq_freqFirstBoundary_le {σ m μ₀ : ℝ} {A : Set ℝ} {g g' : ℝ → X}
    (hA : MeasurableSet A) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgm : StronglyMeasurable g)
    (hg'2 : MemLp g' 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hfloor : ∀ x ∈ A, μ₀ - m ≤ wallFloor T σ x) :
    (∫⁻ x : ℝ, ‖A.indicator (fun y : ℝ => y • firstBoundary T g σ y) x‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2) / μ₀
          + 4 * Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2) / μ₀ ^ 2) := by
  have hgap : 0 < (μ₀ - m) + m := by linarith
  have hB : ∀ x ∈ A, ∀ u : X,
      (μ₀ - m) * ‖u‖ ^ 2 ≤ (inner ℂ (wallGenerator T σ x u) u).re := by
    intro x hx u
    have hbase := re_inner_wallGenerator_ge (T := T) hσ0 hσ1 x u
    have hfl := hfloor x hx
    nlinarith [sq_nonneg ‖u‖, hbase, hfl]
  have hcutsupp : ∀ s : ℝ, ∀ x, x ∉ A → freqCutSlice g A x s = 0 :=
    fun s x hx => freqCutSlice_eq_zero s hx
  have hΦ : ∀ x : ℝ, ‖A.indicator (fun y : ℝ => y • firstBoundary T g σ y) x‖ₑ
      ≤ ∫⁻ s in Ioi (0 : ℝ),
          ‖accretiveSemigroup (wallGenerator T σ x) s (freqCutSlice g A x s)‖ₑ := by
    intro x
    by_cases hx : x ∈ A
    · have hfl : μ₀ ≤ wallFloor T σ x + m := by
        have := hfloor x hx
        linarith
      rw [Set.indicator_of_mem hx, firstBoundary_eq_laplace hσ0 hσ1 hμ hg2 hsupp hfl]
      have hpull : x • ∫ s in Ioi (0 : ℝ),
            accretiveSemigroup (wallGenerator T σ x) s (blockSlice g s x)
          = ∫ s in Ioi (0 : ℝ),
            accretiveSemigroup (wallGenerator T σ x) s (freqCutSlice g A x s) := by
        rw [← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        show x • accretiveSemigroup (wallGenerator T σ x) s (blockSlice g s x)
          = accretiveSemigroup (wallGenerator T σ x) s (x • cutSlice g A x s)
        rw [cutSlice, Set.indicator_of_mem hx]
        simp only [← Complex.coe_smul, map_smul]
      rw [hpull]
      exact enorm_integral_le_lintegral_enorm _
    · rw [Set.indicator_of_notMem hx]
      simp
  have hslice : ∀ s : ℝ, 0 < s →
      (∫⁻ x : ℝ, ‖freqCutSlice g A x s‖ₑ ^ 2)
        ≤ ENNReal.ofReal (Real.exp (-(2 * s * m)))
          * ENNReal.ofReal ((Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g' L‖ ^ 2)
            + Real.sqrt (4 * Real.pi * ∫ L : ℝ, ‖g L‖ ^ 2) * s) ^ 2) :=
    fun s hs => lintegral_sq_freqCutSlice_le hs hg hg2 hg'2 hsupp
  have hfin := lintegral_sq_blockLaplace_linear_le hB hgap
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hcutsupp
    (measurable_semigroup_freqCutSlice hgm hA hσ0 hσ1) hΦ hslice
  have hsum : μ₀ - m + m = μ₀ := by ring
  rwa [hsum] at hfin

end GaloisForLFunctions.RHTower
