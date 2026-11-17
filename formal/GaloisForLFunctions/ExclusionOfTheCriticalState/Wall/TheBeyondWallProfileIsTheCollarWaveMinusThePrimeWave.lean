import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheProfileBeyondTheWallInPrimeForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.SignedWindowCriticality.TheCollarHankelForm

/-!
# Beyond the wall the state is the collar wave minus the prime wave

The Lévy density `ω(x) = Σ_{k ≥ 0} e^{−(2k + ½)x}` has its first mode at the Gamma pole; the other
exponents are the centred trivial zeros `σ_k = −(2(k + 1) + ½)` of `ζ`. Right of the wall the archimedean
head of a profile `F ∈ H` is therefore its positive charge plus the **trivial-zero wave**

  `T F(x) = Σ_k μ_{σ_k}(F) e^{σ_k x}`,   `μ_σ(F) = ∫ F(u) e^{−σu} du = L F(−σ)`

(`levyHeadProfile_eq_trivialZeroWave`), and the prime form of the profile beyond the wall becomes
(`beyondWallProfile_trivialZeroForm`)

  `−a F⁺(x) = T F(x) − L F(−½) e^{x/2} + Σ_n Λ(n) n^{−½} F(x − log n)`:

trivial zeros, the pole of `ζ`, the primes. The first two terms are the collar kernel
`κ(x) = 2cosh(x/2) − ω(x)` of the window tower acting on `F` (`collarWave_eq`), so

  `a F⁺ = κ * F − Σ_n Λ(n) n^{−½} F(· − log n)`   (`beyondWallProfile_collarForm`).

**Mirror pairing.** Paired with the mirror image `F(2m − x)` of the profile at distance `2m > 0` beyond
the wall, the collar wave gives the collar Hankel form
`𝓗_m(F) = e^m μ_{½}(F)² − Σ_k e^{2mσ_k} μ_{σ_k}(F)²` (`integral_collarWave_mul_reflect`), so

  `a ∫_{x>0} F⁺(x) F(2m − x) dx = 𝓗_m(F) − ∫_{x>0} (Σ_n Λ(n) n^{−½} F(x − log n)) F(2m − x) dx`

(`beyondWallProfile_mirrorPairing`): the archimedean side of the wall enters only through the Hankel
form, one pole square against the squares of the trivial zeros.

Mechanism. On `u < 0 < x` the kernel expands as `κ(x − u) = e^{(x−u)/2} − Σ_k e^{σ_k (x − u)}`; the trivial
weights `e^{−σ_k u}` are at most one on the support of `F`, so every interchange of sum and integral is
dominated by `‖F‖₁ Σ_k e^{σ_k x}`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry
  CanonicalSystemOfTheWindowTower SignedWindowCriticality

/-! ### Termwise integration -/

/-- A pointwise summable series of a.e.-measurable functions with an integrable majorant of its sum
is integrable. -/
theorem integrable_tsum_of_le {μ : Measure ℝ} {B : ℕ → ℝ → ℝ}
    (hB : ∀ k, AEStronglyMeasurable (B k) μ) (hs : ∀ x, Summable fun k => B k x) {g : ℝ → ℝ}
    (hg : Integrable g μ) (hle : ∀ x, ‖∑' k, B k x‖ ≤ g x) :
    Integrable (fun x => ∑' k, B k x) μ := by
  refine hg.mono' ?_ (Eventually.of_forall hle)
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => ∑ k ∈ Finset.range n, B k x)
    (fun n => (Finset.aestronglyMeasurable_sum (Finset.range n) fun k _ => hB k).congr
      (Eventually.of_forall fun x => Finset.sum_apply x _ _))
    (Eventually.of_forall fun x => (hs x).hasSum.tendsto_sum_nat)

/-- Integration of `A − Σ_k B_k` term by term. -/
theorem integral_sub_tsum {μ : Measure ℝ} {A : ℝ → ℝ} {B : ℕ → ℝ → ℝ} (hA : Integrable A μ)
    (hB : ∀ k, Integrable (B k) μ) (hBs : Summable fun k => ∫ x, ‖B k x‖ ∂μ)
    (hs : ∀ x, Summable fun k => B k x) {g : ℝ → ℝ} (hg : Integrable g μ)
    (hle : ∀ x, ‖∑' k, B k x‖ ≤ g x) :
    ∫ x, (A x - ∑' k, B k x) ∂μ = ∫ x, A x ∂μ - ∑' k, ∫ x, B k x ∂μ := by
  rw [integral_sub hA (integrable_tsum_of_le (fun k => (hB k).1) hs hg hle),
    integral_tsum_of_summable_integral_norm hB hBs]

/-! ### Moments of a profile -/

/-- A profile of the domain tilted by `e^{cu}`, `c > −4`, is integrable. -/
theorem integrable_mul_exp_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {c : ℝ}
    (hc : -4 < c) : Integrable fun u => F u * Real.exp (c * u) :=
  (integrable_abs_mul_exp_of_domain hF hc).mono'
    (hF.meas.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])

theorem integrable_leftMomentIntegrand {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ}
    (hσ : σ < 4) : Integrable fun u => F u * Real.exp (-(σ * u)) := by
  simpa only [neg_mul] using integrable_mul_exp_of_domain hF (c := -σ) (by linarith)

/-- The moment `μ_σ(F)` is the transform at `−σ`. -/
theorem laplace_ofReal_eq_leftMoment (F : ℝ → ℝ) (σ : ℝ) :
    negativeHalfLineLaplace (cx F) ((-σ : ℝ) : ℂ) = (leftMoment F σ : ℂ) := by
  rw [negativeHalfLineLaplace_ofReal]
  unfold leftMoment
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [neg_mul]

/-- The trivial weights `e^{−σ_k u}` are at most one on the support of a profile. -/
theorem abs_leftMomentIntegrand_trivial_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (k : ℕ) (u : ℝ) : |F u * Real.exp (-(trivialExponent k * u))| ≤ |F u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [hF.support u hu, zero_mul, abs_zero]
  · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-(trivialExponent k * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [neg_trivialExponent_pos k])
    calc |F u| * Real.exp (-(trivialExponent k * u)) ≤ |F u| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |F u| := mul_one _

theorem abs_leftMoment_trivial_le_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (k : ℕ) : |leftMoment F (trivialExponent k)| ≤ ∫ u, |F u| := by
  unfold leftMoment
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hF.integrable.abs
    (Eventually.of_forall fun u => abs_leftMomentIntegrand_trivial_le hF k u)

/-! ### The trivial-zero wave -/

/-- The **trivial-zero wave** `T F(x) = Σ_k μ_{σ_k}(F) e^{σ_k x}` of a profile, right of the wall. -/
def trivialZeroWave (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, leftMoment F (trivialExponent k) * Real.exp (trivialExponent k * x)

theorem summable_trivialZeroWave {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {x : ℝ}
    (hx : 0 < x) : Summable fun k : ℕ =>
      leftMoment F (trivialExponent k) * Real.exp (trivialExponent k * x) := by
  refine Summable.of_norm_bounded ((hasSum_trivialExponent hx).summable.mul_left (∫ u, |F u|))
    fun k => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (abs_leftMoment_trivial_le_of_domain hF k) (Real.exp_pos _).le

/-- **The Lévy head is the positive charge plus the trivial-zero wave.** For `x > 0`,
`J⁺(x) = L F(½) e^{−x/2} + T F(x)`. -/
theorem levyHeadProfile_eq_trivialZeroWave {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {x : ℝ} (hx : 0 < x) :
    levyHeadProfile F x = negativeHalfLineLaplace (cx F) (1 / 2) * (Real.exp (-(x / 2)) : ℂ) +
      (trivialZeroWave F x : ℂ) := by
  have h1 := (hasSum_nat_add_iff' 1).mpr (hasSum_levyHeadProfile hF hx)
  have h2 : HasSum (fun k : ℕ => cexp (-(2 * ((k + 1 : ℕ) : ℂ) + 1 / 2) * (x : ℂ)) *
      negativeHalfLineLaplace (cx F) (2 * ((k + 1 : ℕ) : ℂ) + 1 / 2)) (trivialZeroWave F x : ℂ) := by
    refine (Complex.ofRealCLM.hasSum (summable_trivialZeroWave hF hx).hasSum).congr_fun
      fun k => ?_
    have e : ((-trivialExponent k : ℝ) : ℂ) = 2 * ((k + 1 : ℕ) : ℂ) + 1 / 2 := by
      unfold trivialExponent; push_cast; ring
    rw [← e, laplace_ofReal_eq_leftMoment, Complex.ofRealCLM_apply, Complex.ofReal_mul,
      Complex.ofReal_exp, mul_comm]
    congr 2
    push_cast
    ring
  have h := h1.unique h2
  rw [Finset.sum_range_one] at h
  simp only [Nat.cast_zero, mul_zero, zero_add] at h
  have e0 : cexp (-(1 / 2) * (x : ℂ)) = (Real.exp (-(x / 2)) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [e0] at h
  linear_combination h

/-- **The profile beyond the wall in trivial-zero form.** For almost every `x > 0`,
`−a F⁺(x) = T F(x) − L F(−½) e^{x/2} + Σ_n Λ(n) n^{−½} F(x − log n)`, the prime series absolutely
convergent. -/
theorem beyondWallProfile_trivialZeroForm {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      Summable (fun n : ℕ => (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) ∧
      -(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x =
        (trivialZeroWave F x : ℂ) -
          negativeHalfLineLaplace (cx F) (-(1 / 2)) * (Real.exp (x / 2) : ℂ) +
          ∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ) := by
  filter_upwards [beyondWallProfile_primeForm hW hF, ae_restrict_mem measurableSet_Ioi]
    with x hx hx0
  refine ⟨hx.1, ?_⟩
  rw [hx.2, levyHeadProfile_eq_trivialZeroWave hF hx0]
  ring

/-! ### The collar wave -/

/-- The collar kernel `κ = 2cosh(·/2) − ω` acting on a profile: `(κ * F)(x) = ∫ F(u) κ(x − u) du`. -/
def collarWave (F : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, F u * collarKernel (x - u)

/-- **The collar wave is the pole mode minus the trivial-zero wave.** For `x > 0`,
`(κ * F)(x) = μ_{½}(F) e^{x/2} − T F(x)`. -/
theorem collarWave_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {x : ℝ} (hx : 0 < x) :
    collarWave F x = leftMoment F (1 / 2) * Real.exp (1 / 2 * x) - trivialZeroWave F x := by
  have hT := (hasSum_trivialExponent hx).summable
  -- on `u < 0 < x`: `κ(x − u) = e^{(x−u)/2} − Σ_k e^{σ_k (x − u)}`
  have hpt : ∀ u, F u * collarKernel (x - u) =
      Real.exp (1 / 2 * x) * (F u * Real.exp (-(1 / 2 * u))) -
        ∑' k : ℕ, Real.exp (trivialExponent k * x) *
          (F u * Real.exp (-(trivialExponent k * u))) := by
    intro u
    rcases le_or_gt 0 u with hu | hu
    · simp [hF.support u hu]
    · have hκ := (hasSum_collarKernel (show 0 < x - u by linarith)).tsum_eq
      rw [show collarKernel (x - u) = Real.exp ((x - u) / 2) -
          ∑' k : ℕ, Real.exp (-(2 * ((k : ℝ) + 1) + 1 / 2) * (x - u)) by rw [hκ]; ring,
        mul_sub, ← tsum_mul_left]
      congr 1
      · rw [show (x - u) / 2 = 1 / 2 * x + -(1 / 2 * u) by ring, Real.exp_add]; ring
      · refine tsum_congr fun k => ?_
        rw [show -(2 * ((k : ℝ) + 1) + 1 / 2) * (x - u) =
          trivialExponent k * x + -(trivialExponent k * u) by unfold trivialExponent; ring,
          Real.exp_add]
        ring
  have hbound : ∀ k u, ‖Real.exp (trivialExponent k * x) *
      (F u * Real.exp (-(trivialExponent k * u)))‖ ≤ Real.exp (trivialExponent k * x) * |F u| :=
    fun k u => by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_leftMomentIntegrand_trivial_le hF k u)
        (Real.exp_pos _).le
  have hI : ∀ k : ℕ, Integrable fun u => Real.exp (trivialExponent k * x) *
      (F u * Real.exp (-(trivialExponent k * u))) := fun k =>
    (integrable_leftMomentIntegrand hF (by linarith [neg_trivialExponent_pos k])).const_mul _
  have hIs : Summable fun k : ℕ => ∫ u, ‖Real.exp (trivialExponent k * x) *
      (F u * Real.exp (-(trivialExponent k * u)))‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun u => norm_nonneg _)
      (fun k => ?_) (hT.mul_right (∫ u, |F u|))
    rw [← integral_const_mul]
    exact integral_mono (hI k).norm (hF.integrable.abs.const_mul _) (hbound k)
  have hs : ∀ u, Summable fun k : ℕ => Real.exp (trivialExponent k * x) *
      (F u * Real.exp (-(trivialExponent k * u))) := fun u =>
    Summable.of_norm_bounded (hT.mul_right |F u|) fun k => hbound k u
  have hle : ∀ u, ‖∑' k : ℕ, Real.exp (trivialExponent k * x) *
      (F u * Real.exp (-(trivialExponent k * u)))‖ ≤
        (∑' k : ℕ, Real.exp (trivialExponent k * x)) * |F u| := fun u => by
    rw [← tsum_mul_right]
    exact (norm_tsum_le_tsum_norm (Summable.of_norm_bounded (hT.mul_right |F u|)
      fun k => (norm_norm (_ : ℝ)).le.trans (hbound k u))).trans
      (Summable.tsum_le_tsum (fun k => hbound k u)
        (Summable.of_norm_bounded (hT.mul_right |F u|)
          fun k => (norm_norm (_ : ℝ)).le.trans (hbound k u)) (hT.mul_right _))
  have hmain := integral_sub_tsum
    ((integrable_leftMomentIntegrand hF (σ := 1 / 2) (by norm_num)).const_mul
      (Real.exp (1 / 2 * x))) hI hIs hs (hF.integrable.abs.const_mul _) hle
  unfold collarWave trivialZeroWave
  rw [integral_congr_ae (Eventually.of_forall hpt), hmain, integral_const_mul]
  unfold leftMoment
  congr 1
  · ring
  · refine tsum_congr fun k => ?_
    rw [integral_const_mul]
    ring

/-- **Beyond the wall the state is the collar wave minus the prime wave.** For almost every
`x > 0`, `a F⁺(x) = (κ * F)(x) − Σ_n Λ(n) n^{−½} F(x − log n)`. -/
theorem beyondWallProfile_collarForm {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      (criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF x =
        (collarWave F x : ℂ) - ∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ) := by
  filter_upwards [beyondWallProfile_trivialZeroForm hW hF, ae_restrict_mem measurableSet_Ioi]
    with x hx hx0
  have hL : negativeHalfLineLaplace (cx F) (-(1 / 2)) = (leftMoment F (1 / 2) : ℂ) := by
    rw [← laplace_ofReal_eq_leftMoment]; congr 1; push_cast; ring
  have hE : (Real.exp (x / 2) : ℂ) = (Real.exp (1 / 2 * x) : ℂ) := by
    rw [show x / 2 = 1 / 2 * x by ring]
  rw [collarWave_eq hF hx0]
  push_cast
  rw [hL, hE] at hx
  push_cast at hx
  linear_combination -hx.2

/-! ### The mirror pairing -/

/-- Beyond the mirror point the trivial weights are at most `e^{2mσ_k}`. -/
theorem abs_reflect_mul_exp_trivial_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (m : ℝ) (k : ℕ) (x : ℝ) :
    |F (2 * m - x) * Real.exp (trivialExponent k * x)| ≤
      Real.exp (2 * m * trivialExponent k) * |F (2 * m - x)| := by
  rcases le_or_gt 0 (2 * m - x) with h | h
  · rw [hF.support _ h, zero_mul, abs_zero, mul_zero]
  · rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    nlinarith [neg_trivialExponent_pos k]

/-- A reflected tilted profile is integrable: `F(2m − x) e^{σx} = e^{2mσ} (F e^{−σ·})(2m − x)`. -/
theorem integrable_reflect_mul_exp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (m : ℝ)
    {σ : ℝ} (hσ : σ < 4) : Integrable fun x => F (2 * m - x) * Real.exp (σ * x) := by
  refine (((integrable_leftMomentIntegrand hF hσ).comp_sub_left (2 * m)).const_mul
    (Real.exp (2 * m * σ))).congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- The collar wave against the mirror image of the profile, written as pole mode minus
trivial-zero modes. -/
theorem collarWave_mul_reflect_eq {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {m : ℝ}
    (hm : 0 < m) (x : ℝ) :
    collarWave F x * F (2 * m - x) =
      leftMoment F (1 / 2) * (F (2 * m - x) * Real.exp (1 / 2 * x)) -
        ∑' k : ℕ, leftMoment F (trivialExponent k) *
          (F (2 * m - x) * Real.exp (trivialExponent k * x)) := by
  rcases le_or_gt 0 (2 * m - x) with h | h
  · simp [hF.support _ h]
  · rw [collarWave_eq hF (by linarith), trivialZeroWave, sub_mul, ← tsum_mul_right]
    congr 1
    · ring
    · exact tsum_congr fun k => by ring

/-- **The collar wave pairs with the mirror image through the collar Hankel form.** For `m > 0`,
`∫_{x>0} (κ * F)(x) F(2m − x) dx = e^m μ_{½}(F)² − Σ_k e^{2mσ_k} μ_{σ_k}(F)² = 𝓗_m(F)`. -/
theorem integral_collarWave_mul_reflect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {m : ℝ} (hm : 0 < m) :
    Integrable (fun x => collarWave F x * F (2 * m - x)) ∧
      ∫ x in Ioi (0 : ℝ), collarWave F x * F (2 * m - x) = collarHankel m F := by
  have hT := (hasSum_trivialExponent (show 0 < 2 * m by linarith)).summable
  set M : ℝ := ∫ u, |F u|
  have hM : ∀ k, |leftMoment F (trivialExponent k)| ≤ M := abs_leftMoment_trivial_le_of_domain hF
  have hbound : ∀ k x, ‖leftMoment F (trivialExponent k) *
      (F (2 * m - x) * Real.exp (trivialExponent k * x))‖ ≤
        M * |F (2 * m - x)| * Real.exp (trivialExponent k * (2 * m)) := fun k x => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      show trivialExponent k * (2 * m) = 2 * m * trivialExponent k by ring, mul_assoc]
    exact mul_le_mul (hM k) ((abs_reflect_mul_exp_trivial_le hF m k x).trans_eq (mul_comm _ _))
      (abs_nonneg _) ((abs_nonneg _).trans (hM k))
  have hI : ∀ k : ℕ, Integrable fun x => leftMoment F (trivialExponent k) *
      (F (2 * m - x) * Real.exp (trivialExponent k * x)) := fun k =>
    (integrable_reflect_mul_exp hF m (by linarith [neg_trivialExponent_pos k])).const_mul _
  have hFr : Integrable fun x => |F (2 * m - x)| := hF.integrable.abs.comp_sub_left (2 * m)
  have hFr' : ∫ x, |F (2 * m - x)| = M := integral_sub_left_eq_self (μ := volume) (fun u => |F u|) (2 * m)
  have hIs : Summable fun k : ℕ => ∫ x, ‖leftMoment F (trivialExponent k) *
      (F (2 * m - x) * Real.exp (trivialExponent k * x))‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _)
      (fun k => ?_) (hT.mul_left (M * M))
    calc ∫ x, ‖leftMoment F (trivialExponent k) *
          (F (2 * m - x) * Real.exp (trivialExponent k * x))‖
        ≤ ∫ x, M * |F (2 * m - x)| * Real.exp (trivialExponent k * (2 * m)) :=
          integral_mono (hI k).norm ((hFr.const_mul M).mul_const _) (hbound k)
      _ = M * M * Real.exp (trivialExponent k * (2 * m)) := by
          rw [integral_mul_const, integral_const_mul, hFr']
  have hs : ∀ x, Summable fun k : ℕ => leftMoment F (trivialExponent k) *
      (F (2 * m - x) * Real.exp (trivialExponent k * x)) := fun x =>
    Summable.of_norm_bounded (hT.mul_left (M * |F (2 * m - x)|)) fun k => hbound k x
  have hle : ∀ x, ‖∑' k : ℕ, leftMoment F (trivialExponent k) *
      (F (2 * m - x) * Real.exp (trivialExponent k * x))‖ ≤
        M * |F (2 * m - x)| * ∑' k : ℕ, Real.exp (trivialExponent k * (2 * m)) := fun x => by
    rw [← tsum_mul_left]
    have hn : Summable fun k : ℕ => ‖leftMoment F (trivialExponent k) *
        (F (2 * m - x) * Real.exp (trivialExponent k * x))‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound k x)
        (hT.mul_left (M * |F (2 * m - x)|))
    exact (norm_tsum_le_tsum_norm hn).trans
      (Summable.tsum_le_tsum (fun k => hbound k x) hn (hT.mul_left _))
  have hA : Integrable fun x => leftMoment F (1 / 2) * (F (2 * m - x) * Real.exp (1 / 2 * x)) :=
    (integrable_reflect_mul_exp hF m (by norm_num)).const_mul _
  have hmaj : Integrable fun x => M * |F (2 * m - x)| *
      ∑' k : ℕ, Real.exp (trivialExponent k * (2 * m)) := (hFr.const_mul M).mul_const _
  have hint : Integrable fun x => collarWave F x * F (2 * m - x) :=
    (hA.sub (integrable_tsum_of_le (fun k => (hI k).1) hs hmaj hle)).congr
      (Eventually.of_forall fun x => (collarWave_mul_reflect_eq hF hm x).symm)
  refine ⟨hint, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hF.support _ (by linarith [show x ≤ 0 from not_lt.mp hx]), mul_zero],
    integral_congr_ae (Eventually.of_forall (collarWave_mul_reflect_eq hF hm)),
    integral_sub_tsum hA hI hIs hs hmaj hle, integral_const_mul]
  have hR : ∀ σ : ℝ, ∫ x, F (2 * m - x) * Real.exp (σ * x) =
      Real.exp (2 * m * σ) * leftMoment F σ := fun σ => rightMoment_collarReflect m σ F
  rw [hR, collarHankel]
  congr 1
  · rw [show 2 * m * (1 / 2 : ℝ) = m by ring]; ring
  · refine tsum_congr fun k => ?_
    rw [integral_const_mul, hR]
    ring

/-- The mirror image `x ↦ e^x F(2m − x)` is square-integrable: its square is
`e^{4m} (F² e^{−2u})(2m − x)`. -/
theorem integrable_sq_exp_mul_reflect {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (m : ℝ) : Integrable fun x => (Real.exp x * F (2 * m - x)) ^ 2 := by
  have h1 : Integrable fun u => F u ^ 2 * Real.exp (-(2 * u)) := by
    refine hF.exponential.mono' ((hF.meas.pow_const 2).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    rcases le_or_gt 0 u with hu | hu
    · rw [hF.support u hu]; simp
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)
  refine ((h1.comp_sub_left (2 * m)).const_mul (Real.exp (4 * m))).congr
    (Eventually.of_forall fun x => ?_)
  have e : Real.exp x ^ 2 = Real.exp (4 * m) * Real.exp (-(2 * (2 * m - x))) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  simp only
  rw [mul_pow, e]
  ring

/-- The profile beyond the wall is integrable against the mirror image of the profile. -/
theorem integrableOn_beyondWallProfile_mul_reflect (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (m : ℝ) :
    IntegrableOn (fun x => beyondWallProfile W₀ hF x * (F (2 * m - x) : ℂ)) (Ioi (0 : ℝ)) := by
  have hU : IntegrableOn (fun x => ‖(unitLeftDatum W₀ hF : ℝ → ℂ) x‖ ^ (2 : ℕ)) (Ioi (0 : ℝ)) :=
    integrableOn_norm_sq_of_memLp (Lp.memLp (unitLeftDatum W₀ hF))
  refine ((hU.add (integrable_sq_exp_mul_reflect hF m).integrableOn).div_const 2).mono'
    ((aestronglyMeasurable_beyondWallProfile W₀ hF).mul
      (Complex.measurable_ofReal.comp
        (hF.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simp only [beyondWallProfile]
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hsq : (Real.exp x * F (2 * m - x)) ^ 2 = (Real.exp x * |F (2 * m - x)|) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  show Real.exp x * ‖(unitLeftDatum W₀ hF : ℝ → ℂ) x‖ * |F (2 * m - x)| ≤
    (‖(unitLeftDatum W₀ hF : ℝ → ℂ) x‖ ^ 2 + (Real.exp x * F (2 * m - x)) ^ 2) / 2
  rw [hsq]
  nlinarith [sq_nonneg (‖(unitLeftDatum W₀ hF : ℝ → ℂ) x‖ - Real.exp x * |F (2 * m - x)|)]

/-- **The mirror pairing of the profile beyond the wall.** For `m > 0`,
`a ∫_{x>0} F⁺(x) F(2m − x) dx = 𝓗_m(F) − ∫_{x>0} (Σ_n Λ(n) n^{−½} F(x − log n)) F(2m − x) dx`, the
prime pairing absolutely integrable: the archimedean side of the wall enters only through the collar
Hankel form. -/
theorem beyondWallProfile_mirrorPairing {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun x => (∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) *
        (F (2 * m - x) : ℂ)) (Ioi (0 : ℝ)) ∧
      (criticalAliasCoefficient W₀ : ℂ) *
          ∫ x in Ioi (0 : ℝ), beyondWallProfile W₀ hF x * (F (2 * m - x) : ℂ) =
        (collarHankel m F : ℂ) -
          ∫ x in Ioi (0 : ℝ), (∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) *
            (F (2 * m - x) : ℂ) := by
  obtain ⟨hc, hci⟩ := integral_collarWave_mul_reflect hF hm
  have hI1 := integrableOn_beyondWallProfile_mul_reflect W₀ hF m
  have hI2 : IntegrableOn (fun x => ((collarWave F x * F (2 * m - x) : ℝ) : ℂ)) (Ioi (0 : ℝ)) :=
    hc.integrableOn.ofReal
  have hae : (fun x => (∑' n : ℕ, (primeAtom n : ℂ) * (F (x - Real.log n) : ℂ)) *
      (F (2 * m - x) : ℂ)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x => ((collarWave F x * F (2 * m - x) : ℝ) : ℂ) -
        (criticalAliasCoefficient W₀ : ℂ) * (beyondWallProfile W₀ hF x * (F (2 * m - x) : ℂ)) := by
    filter_upwards [beyondWallProfile_collarForm hW hF] with x hx
    push_cast
    linear_combination (F (2 * m - x) : ℂ) * hx
  refine ⟨(hI2.sub (hI1.const_mul _)).congr_fun_ae hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub hI2 (hI1.const_mul _), integral_const_mul,
    integral_complex_ofReal, hci]
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
