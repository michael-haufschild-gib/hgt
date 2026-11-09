import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheModularMapIsPositionRigid
import GaloisForLFunctions.RHTower.FiniteOffLineLandau

/-!
# The dual side of a seed has no sign

Read the response `a_F(y)` of a seed at small height `y` as the black-hole (S-dual, high-temperature) side of
the modular map. A confined seed is a positive object, and one could hope that its positivity survives on the
dual side as a sign of the remainder `a_F(y) − c_F`. This module shows that such a sign would carry exactly
the information of a rate: a **one-sided** bound

  `a_F(y) − c_F ≤ C y^α` on `(0, 1]`,  `c_F = ∫_𝒟 F / (2ξ(2))`,

for a real seed already forces `Λ_F(s₀) = 0` at every zero `s₀` of `ξ(2s)` with `Re s₀ > 1 − α`, as the two-sided
bound does (`seedTransform_eq_zero_of_oneSided`). So positivity on the dual side is not a weaker input than
universal damping; at `α > ¾` it is excluded for every seed that sees a critical resonance
(`not_oneSided_of_seen`), and the remainder of such a seed changes sign at the universal scale.

**Analytic structure.** Write `N(u)` for the Eisenstein numerator, so that `E*(u) = N(u)/((1 + 2u)2u)` and
`N(u)/ξ(1 + 2u)` is the Eisenstein function. Then
* `N_F(s) = ∫_𝒟 F · N(s − ½)` is holomorphic off `s = 1` (`differentiableOn_numeratorTransform`), and the
  response transform is `N_F(s)/ξ(2s)` (`numeratorTransform_eq_mul_seedTransform`): it is regular at `s = ½`;
* the polar numerator `(2u − 1) N(u)` is entire and equals `1` at `u = ½` (`polarNumerator_half`), so
  `P_F(s) = 2(s − 1) N_F(s)` is entire with `P_F(1) = ∫_𝒟 F` (`polarTransform_one`): the only real singularity of
  the response transform is the simple pole at `s = 1` with residue `c_F`.

**Proof of the main theorem.** With `y = e^{−v/(2α)}` the nonnegative function `C y^α − (a_F(y) − c_F)` becomes a
Laplace integrand of the shape of Landau's theorem (`RHTower.exists_differentiable_extension_of_le_exp`), whose
transform is analytic at every real point; Landau extends it to `Re s > 1 − α`. Multiplying by `ξ(2s)` and using
the identity theorem on a quarter plane transports `N_F(s) = (extension + c_F/(s − 1) + tail)·ξ(2s)` to the
zeros of `ξ(2s)`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open UpperHalfPlane (ofComplex)

variable {F : ℍ → ℂ}

/-! ### The numerator and the polar numerator -/

/-- `(2u − 1)` times the Eisenstein numerator, written without the pole at `u = ½`. -/
def polarNumerator (u : ℂ) (x Y : ℝ) : ℂ :=
  (2 * u - 1) * ((Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u)) + (1 + 2 * u) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u) +
    (2 * u - 1) * ((1 + 2 * u) * (2 * u)) * eisTail u x Y

theorem polarNumerator_eq {u : ℂ} (hu : u ≠ 1 / 2) (x Y : ℝ) :
    polarNumerator u x Y = (2 * u - 1) * eisensteinNumerator u x Y := by
  have h : 2 * u - 1 ≠ 0 := fun h => hu (by linear_combination h / 2)
  unfold polarNumerator eisensteinNumerator
  field_simp

theorem xi_one : xi 1 = 1 / 2 := by unfold xi; simp

theorem xi_zero : xi 0 = 1 / 2 := by unfold xi; simp

/-- **The residue of the numerator at `u = ½` is one.** -/
theorem polarNumerator_half (x : ℝ) {Y : ℝ} (hY : 0 < Y) : polarNumerator (1 / 2) x Y = 1 := by
  have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.2 hY.ne'
  unfold polarNumerator
  rw [show (2 : ℂ) * (1 / 2) - 1 = 0 by norm_num, show (2 : ℂ) * (1 / 2) = 1 by norm_num,
    show (1 / 2 : ℂ) - 1 / 2 = 0 by norm_num, cpow_zero, xi_one]
  norm_num

/-- **The numerator vanishes at `u = 0`**: `E*` is regular there. -/
theorem eisensteinNumerator_zero (x Y : ℝ) : eisensteinNumerator 0 x Y = 0 := by
  unfold eisensteinNumerator
  simp only [mul_zero, add_zero, zero_sub, sub_zero, zero_mul, xi_zero, xi_one]
  ring

theorem differentiableAt_polarNumerator (x : ℝ) {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    DifferentiableAt ℂ (fun v => polarNumerator v x Y) u := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 + v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 + v) u).const_cpow (Or.inl hYC)
  have h2 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 - v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 - v) u).const_cpow (Or.inl hYC)
  have hx1 : DifferentiableAt ℂ (fun v : ℂ => xi (1 + 2 * v)) u := differentiable_xi_shift u
  have hx2 : DifferentiableAt ℂ (fun v : ℂ => xi (2 * v)) u :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) u
  unfold polarNumerator
  exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) u).mul (h1.mul hx1)).add
    (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) u).mul hx2).mul h2)).add
    ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => (2 * v - 1) * ((1 + 2 * v) * (2 * v))) u).mul
      (differentiableAt_eisTail x hY u))

/-- The two kernels and their growth on compact parameter sets. -/
theorem exists_kernel_bound {K : Set ℂ} (hK : IsCompact K) (hKU : ∀ u ∈ K, u ≠ 1 / 2) :
    ∃ α β a : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ a ∧ ∀ u ∈ K, ∀ (x Y : ℝ), 1 / 2 ≤ Y →
      ‖eisensteinNumerator u x Y‖ ≤ α * Y ^ a + β := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, 0, 0, le_rfl, le_rfl, le_rfl, fun u hu => by simp [hE] at hu⟩
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (Complex.continuous_re.continuousOn (s := K))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ hne.some_mem)
  set a := A + 1 / 2
  have hcont1 : ContinuousOn (fun u : ℂ => xi (1 + 2 * u)) K :=
    (differentiable_xi_shift).continuous.continuousOn
  have hcont2 : ContinuousOn (fun u : ℂ => (1 + 2 * u) / (2 * u - 1) * xi (2 * u)) K := by
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu => ?_)
      ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)).continuous.continuousOn)
    intro h; exact hKU u hu (by linear_combination h / 2)
  have hcont3 : ContinuousOn (fun u : ℂ => (1 + 2 * u) * (2 * u)) K := by fun_prop
  obtain ⟨K₁, hK₁⟩ := hK.exists_bound_of_continuousOn hcont1
  obtain ⟨K₂, hK₂⟩ := hK.exists_bound_of_continuousOn hcont2
  obtain ⟨K₃, hK₃⟩ := hK.exists_bound_of_continuousOn hcont3
  obtain ⟨Ct, hCt0, hCt⟩ := CuspRSC.norm_weightedTail_le hA0
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ _ hne.some_mem)
  have hK₂0 : 0 ≤ K₂ := (norm_nonneg _).trans (hK₂ _ hne.some_mem)
  have hK₃0 : 0 ≤ K₃ := (norm_nonneg _).trans (hK₃ _ hne.some_mem)
  refine ⟨K₁ + K₂, (K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct), a, by positivity, by positivity,
    by positivity, fun u hu x Y hY => ?_⟩
  have hre : |u.re| ≤ A := by simpa [Real.norm_eq_abs] using hA u hu
  have hre' := abs_le.1 hre
  have hw1 : |(1 / 2 + u).re| ≤ a := by
    have : (1 / 2 + u).re = 1 / 2 + u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hw2 : |(1 / 2 - u).re| ≤ a := by
    have : (1 / 2 - u).re = 1 / 2 - u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hP1 := CuspRSC.norm_cpow_le hY (by positivity) hw1
  have hP2 := CuspRSC.norm_cpow_le hY (by positivity) hw2
  have hT : ‖eisTail u x Y‖ ≤ 2 * Ct := by
    unfold eisTail
    refine (norm_add_le _ _).trans ?_
    linarith [hCt u false x Y hre hY, hCt u true x Y hre hY]
  unfold eisensteinNumerator
  have e1 : ‖(Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u)‖ ≤ (Y ^ a + 2 ^ a) * K₁ := by
    rw [norm_mul]; exact mul_le_mul hP1 (hK₁ u hu) (norm_nonneg _) (by positivity)
  have e2 : ‖(1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)‖ ≤ K₂ * (Y ^ a + 2 ^ a) := by
    rw [norm_mul]; exact mul_le_mul (hK₂ u hu) hP2 (norm_nonneg _) hK₂0
  have e3 : ‖(1 + 2 * u) * (2 * u) * eisTail u x Y‖ ≤ K₃ * (2 * Ct) := by
    rw [norm_mul]; exact mul_le_mul (hK₃ u hu) hT (norm_nonneg _) hK₃0
  calc _ ≤ ‖(Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u)‖ +
        ‖(1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)‖ +
        ‖(1 + 2 * u) * (2 * u) * eisTail u x Y‖ := norm_add₃_le
    _ ≤ (Y ^ a + 2 ^ a) * K₁ + K₂ * (Y ^ a + 2 ^ a) + K₃ * (2 * Ct) := by linarith
    _ = (K₁ + K₂) * Y ^ a + ((K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct)) := by ring

theorem exists_polar_bound {K : Set ℂ} (hK : IsCompact K) :
    ∃ α β a : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ a ∧ ∀ u ∈ K, ∀ (x Y : ℝ), 1 / 2 ≤ Y →
      ‖polarNumerator u x Y‖ ≤ α * Y ^ a + β := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, 0, 0, le_rfl, le_rfl, le_rfl, fun u hu => by simp [hE] at hu⟩
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (Complex.continuous_re.continuousOn (s := K))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ hne.some_mem)
  set a := A + 1 / 2
  have hcont1 : ContinuousOn (fun u : ℂ => (2 * u - 1) * xi (1 + 2 * u)) K :=
    ((by fun_prop : Continuous fun u : ℂ => 2 * u - 1).mul differentiable_xi_shift.continuous).continuousOn
  have hcont2 : ContinuousOn (fun u : ℂ => (1 + 2 * u) * xi (2 * u)) K :=
    ((by fun_prop : Continuous fun u : ℂ => 1 + 2 * u).mul
      (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)).continuous).continuousOn
  have hcont3 : ContinuousOn (fun u : ℂ => (2 * u - 1) * ((1 + 2 * u) * (2 * u))) K := by fun_prop
  obtain ⟨K₁, hK₁⟩ := hK.exists_bound_of_continuousOn hcont1
  obtain ⟨K₂, hK₂⟩ := hK.exists_bound_of_continuousOn hcont2
  obtain ⟨K₃, hK₃⟩ := hK.exists_bound_of_continuousOn hcont3
  obtain ⟨Ct, hCt0, hCt⟩ := CuspRSC.norm_weightedTail_le hA0
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ _ hne.some_mem)
  have hK₂0 : 0 ≤ K₂ := (norm_nonneg _).trans (hK₂ _ hne.some_mem)
  have hK₃0 : 0 ≤ K₃ := (norm_nonneg _).trans (hK₃ _ hne.some_mem)
  refine ⟨K₁ + K₂, (K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct), a, by positivity, by positivity,
    by positivity, fun u hu x Y hY => ?_⟩
  have hre : |u.re| ≤ A := by simpa [Real.norm_eq_abs] using hA u hu
  have hre' := abs_le.1 hre
  have hw1 : |(1 / 2 + u).re| ≤ a := by
    have : (1 / 2 + u).re = 1 / 2 + u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hw2 : |(1 / 2 - u).re| ≤ a := by
    have : (1 / 2 - u).re = 1 / 2 - u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hP1 := CuspRSC.norm_cpow_le hY (by positivity) hw1
  have hP2 := CuspRSC.norm_cpow_le hY (by positivity) hw2
  have hT : ‖eisTail u x Y‖ ≤ 2 * Ct := by
    unfold eisTail
    refine (norm_add_le _ _).trans ?_
    linarith [hCt u false x Y hre hY, hCt u true x Y hre hY]
  unfold polarNumerator
  have e1 : ‖(2 * u - 1) * ((Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u))‖ ≤ (Y ^ a + 2 ^ a) * K₁ := by
    rw [show (2 * u - 1) * ((Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u)) =
      (Y : ℂ) ^ (1 / 2 + u) * ((2 * u - 1) * xi (1 + 2 * u)) by ring, norm_mul]
    exact mul_le_mul hP1 (hK₁ u hu) (norm_nonneg _) (by positivity)
  have e2 : ‖(1 + 2 * u) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)‖ ≤ K₂ * (Y ^ a + 2 ^ a) := by
    rw [norm_mul]; exact mul_le_mul (hK₂ u hu) hP2 (norm_nonneg _) hK₂0
  have e3 : ‖(2 * u - 1) * ((1 + 2 * u) * (2 * u)) * eisTail u x Y‖ ≤ K₃ * (2 * Ct) := by
    rw [norm_mul]; exact mul_le_mul (hK₃ u hu) hT (norm_nonneg _) hK₃0
  calc _ ≤ ‖(2 * u - 1) * ((Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u))‖ +
        ‖(1 + 2 * u) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)‖ +
        ‖(2 * u - 1) * ((1 + 2 * u) * (2 * u)) * eisTail u x Y‖ := norm_add₃_le
    _ ≤ (Y ^ a + 2 ^ a) * K₁ + K₂ * (Y ^ a + 2 ^ a) + K₃ * (2 * Ct) := by linarith
    _ = (K₁ + K₂) * Y ^ a + ((K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct)) := by ring

theorem continuous_max_cpow (w : ℂ) : Continuous fun z : ℍ => ((max z.im (1 / 2) : ℝ) : ℂ) ^ w := by
  have hY : Continuous fun z : ℍ => max z.im (1 / 2) := UpperHalfPlane.continuous_im.max continuous_const
  have hpos : ∀ z : ℍ, 0 < max z.im (1 / 2) := fun z => lt_max_of_lt_right (by norm_num)
  exact continuous_iff_continuousAt.2 fun z =>
    (continuousAt_cpow_const (ofReal_mem_slitPlane.2 (hpos z))).comp
      (f := fun z : ℍ => ((max z.im (1 / 2) : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hY).continuousAt

theorem continuous_numerator_max (u : ℂ) :
    Continuous fun z : ℍ => eisensteinNumerator u z.re (max z.im (1 / 2)) := by
  unfold eisensteinNumerator eisTail
  exact (((continuous_max_cpow _).mul continuous_const).add ((continuous_const.mul continuous_const).mul
    (continuous_max_cpow _))).add (continuous_const.mul ((CuspRSC.continuous_weightedTail_max u false).add
      (CuspRSC.continuous_weightedTail_max u true)))

theorem continuous_polarNumerator_max (u : ℂ) :
    Continuous fun z : ℍ => polarNumerator u z.re (max z.im (1 / 2)) := by
  unfold polarNumerator eisTail
  exact ((continuous_const.mul ((continuous_max_cpow _).mul continuous_const)).add
    ((continuous_const.mul continuous_const).mul (continuous_max_cpow _))).add
    (continuous_const.mul ((CuspRSC.continuous_weightedTail_max u false).add
      (CuspRSC.continuous_weightedTail_max u true)))

/-! ### Transforms against analytic kernels -/

/-- **Cauchy domination on `𝒟`.** A seed integrated against a kernel holomorphic in `s` with polynomial growth
in the height, locally uniformly in `s`, gives a holomorphic function. -/
theorem differentiableOn_fd_integral (hF : IsSeed F) {U : Set ℂ} (hU : IsOpen U) {k : ℂ → ℝ → ℝ → ℂ}
    (hk : ∀ z : ℍ, DifferentiableOn ℂ (fun s => k s z.re z.im) U)
    (hkc : ∀ s, Continuous fun z : ℍ => k s z.re (max z.im (1 / 2)))
    (hkb : ∀ s₀ ∈ U, ∃ r > 0, Metric.closedBall s₀ r ⊆ U ∧ ∃ α β a : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ a ∧
      ∀ s ∈ Metric.closedBall s₀ r, ∀ (x Y : ℝ), 1 / 2 ≤ Y → ‖k s x Y‖ ≤ α * Y ^ a + β) :
    DifferentiableOn ℂ (fun s => ∫ z in ModularGroup.fd, F z * k s z.re z.im) U := by
  set Φ : ℍ → ℂ → ℂ := fun z s => ModularGroup.fd.indicator (fun w => F w * k s w.re w.im) z
  have hfd : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  have hint : ∀ s, (∫ z in ModularGroup.fd, F z * k s z.re z.im) = ∫ z, Φ z s := fun s => by
    simp only [Φ]; rw [integral_indicator hfd]
  have hΦ : ∀ z, DifferentiableOn ℂ (Φ z) U := by
    intro z
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [Φ, indicator_of_mem hz]
      exact (differentiableOn_const _).mul (hk z)
    · simp only [Φ, indicator_of_notMem hz]
      exact differentiableOn_const _
  have hmeas : ∀ s ∈ U, AEStronglyMeasurable (fun z => Φ z s) volume := by
    intro s _
    refine ((hF.continuous.mul (hkc s)).aestronglyMeasurable.indicator hfd).congr
      (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [Φ, indicator_of_mem hz, Pi.mul_apply, max_eq_left (CuspRSC.half_lt_im_of_mem_fd hz).le]
    · simp only [Φ, indicator_of_notMem hz]
  refine (RHTower.differentiableOn_integral_of_locally_bounded hU hΦ hmeas fun s₀ hs₀ => ?_).congr
    fun s _ => hint s
  obtain ⟨r, hr, hsub, α, β, a, hα, hβ, ha, hb⟩ := hkb s₀ hs₀
  obtain ⟨B, hB⟩ := hF.exists_bound_on_fd hα hβ ha
  refine ⟨r, hr, hsub, ModularGroup.fd.indicator (fun z => ‖F z‖ * (α * z.im ^ a + β)), ?_, fun z s hs => ?_⟩
  · have hvol : volume ModularGroup.fd ≠ ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_ne_top
    refine (integrable_indicator_iff hfd).2 (Measure.integrableOn_of_bounded (M := B) hvol ?_ ?_)
    · exact (hF.continuous.norm.mul ((continuous_const.mul (UpperHalfPlane.continuous_im.rpow_const
        fun z => Or.inl (ne_of_gt z.im_pos))).add continuous_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hfd] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := z.im_pos; positivity)]
      exact hB z hz
  · by_cases hz : z ∈ ModularGroup.fd
    · simp only [Φ, indicator_of_mem hz]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb s hs z.re z.im (CuspRSC.half_lt_im_of_mem_fd hz).le)
        (norm_nonneg _)
    · simp only [Φ, indicator_of_notMem hz, norm_zero, le_refl]

/-- `N_F(s) = ∫_𝒟 F · N(s − ½)`, the transform against the Eisenstein numerator. -/
def numeratorTransform (F : ℍ → ℂ) (s : ℂ) : ℂ :=
  ∫ z in ModularGroup.fd, F z * eisensteinNumerator (s - 1 / 2) z.re z.im

/-- `P_F(s) = ∫_𝒟 F · (2u − 1) N(u)`, `u = s − ½`. -/
def polarTransform (F : ℍ → ℂ) (s : ℂ) : ℂ :=
  ∫ z in ModularGroup.fd, F z * polarNumerator (s - 1 / 2) z.re z.im

/-- **`N_F` is holomorphic off `s = 1`.** -/
theorem differentiableOn_numeratorTransform (hF : IsSeed F) :
    DifferentiableOn ℂ (numeratorTransform F) ({1} : Set ℂ)ᶜ := by
  have hk : ∀ z : ℍ, DifferentiableOn ℂ (fun s => eisensteinNumerator (s - 1 / 2) z.re z.im)
      ({1} : Set ℂ)ᶜ := by
    intro z s hs
    have hs1 : s - 1 / 2 ≠ 1 / 2 := fun h => hs (Set.mem_singleton_iff.2 (by linear_combination h))
    exact ((EisAuto.differentiableAt_numerator z.re z.im_pos hs1).comp s
      (differentiableAt_id.sub_const _)).differentiableWithinAt
  refine differentiableOn_fd_integral (k := fun s x Y => eisensteinNumerator (s - 1 / 2) x Y) hF
    isOpen_compl_singleton hk (fun s => continuous_numerator_max _) fun s₀ hs₀ => ?_
  have hne : s₀ ≠ 1 := hs₀
  set r := ‖s₀ - 1‖ / 2
  have hr : 0 < r := by simp only [r]; have := norm_pos_iff.2 (sub_ne_zero.2 hne); positivity
  have hball : ∀ s ∈ Metric.closedBall s₀ r, s ≠ 1 := fun s hs h => by
    rw [Metric.mem_closedBall, dist_eq_norm, h, norm_sub_rev] at hs
    have := norm_pos_iff.2 (sub_ne_zero.2 hne); simp only [r] at hs; linarith
  obtain ⟨α, β, a, hα, hβ, ha, hb⟩ := exists_kernel_bound ((isCompact_closedBall s₀ r).image
    (by fun_prop : Continuous fun s : ℂ => s - 1 / 2)) (by
      rintro u ⟨s, hs, rfl⟩ h; exact hball s hs (by linear_combination h))
  exact ⟨r, hr, fun s hs => hball s hs, α, β, a, hα, hβ, ha, fun s hs => hb _ ⟨s, hs, rfl⟩⟩

/-- **`P_F` is entire.** -/
theorem differentiable_polarTransform (hF : IsSeed F) : Differentiable ℂ (polarTransform F) := by
  have hk : ∀ z : ℍ, DifferentiableOn ℂ (fun s => polarNumerator (s - 1 / 2) z.re z.im) univ := by
    intro z s _
    exact ((differentiableAt_polarNumerator z.re z.im_pos (s - 1 / 2)).comp s
      (differentiableAt_id.sub_const _)).differentiableWithinAt
  have hkb : ∀ s₀ ∈ (univ : Set ℂ), ∃ r > 0, Metric.closedBall s₀ r ⊆ univ ∧ ∃ α β a : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      0 ≤ a ∧ ∀ s ∈ Metric.closedBall s₀ r, ∀ (x Y : ℝ), 1 / 2 ≤ Y →
        ‖polarNumerator (s - 1 / 2) x Y‖ ≤ α * Y ^ a + β := by
    intro s₀ _
    obtain ⟨α, β, a, hα, hβ, ha, hb⟩ := exists_polar_bound ((isCompact_closedBall s₀ 1).image
      (by fun_prop : Continuous fun s : ℂ => s - 1 / 2))
    exact ⟨1, one_pos, subset_univ _, α, β, a, hα, hβ, ha, fun s hs => hb _ ⟨s, hs, rfl⟩⟩
  have h := differentiableOn_fd_integral (k := fun s x Y => polarNumerator (s - 1 / 2) x Y) hF isOpen_univ
    hk (fun s => continuous_polarNumerator_max _) hkb
  exact fun s => (h s (mem_univ s)).differentiableAt (isOpen_univ.mem_nhds (mem_univ s))

theorem integrableOn_kernel (hF : IsSeed F) {k : ℝ → ℝ → ℂ}
    (hkc : Continuous fun z : ℍ => k z.re (max z.im (1 / 2))) {α β a : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hb : ∀ (x Y : ℝ), 1 / 2 ≤ Y → ‖k x Y‖ ≤ α * Y ^ a + β) :
    IntegrableOn (fun z : ℍ => F z * k z.re z.im) ModularGroup.fd := by
  have hfd : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  obtain ⟨B, hB⟩ := hF.exists_bound_on_fd hα hβ ha
  have hvol : volume ModularGroup.fd ≠ ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable (fun z : ℍ => F z * k z.re z.im) (volume.restrict ModularGroup.fd) :=
    (hF.continuous.mul hkc).aestronglyMeasurable.congr ((ae_restrict_iff' hfd).2
      (Eventually.of_forall fun z hz => by
        simp only [Pi.mul_apply, max_eq_left (CuspRSC.half_lt_im_of_mem_fd hz).le]))
  haveI : IsFiniteMeasure (volume.restrict ModularGroup.fd) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hvol⟩
  refine (integrable_const B).mono' hmeas ((ae_restrict_iff' hfd).2 (Eventually.of_forall fun z hz => ?_))
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hb z.re z.im (CuspRSC.half_lt_im_of_mem_fd hz).le)
    (norm_nonneg _)).trans (hB z hz)

/-- `P_F(s) = 2(s − 1) N_F(s)` for `s ≠ 1`. -/
theorem polarTransform_eq {s : ℂ} (hs : s ≠ 1) :
    polarTransform F s = 2 * (s - 1) * numeratorTransform F s := by
  have hs1 : s - 1 / 2 ≠ 1 / 2 := fun h => hs (by linear_combination h)
  unfold polarTransform numeratorTransform
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [polarNumerator_eq hs1]
  ring

/-- **`P_F(1) = ∫_𝒟 F`**: the residue of the response at `s = 1` is fixed by the mass of the seed. -/
theorem polarTransform_one (F : ℍ → ℂ) : polarTransform F 1 = ∫ z in ModularGroup.fd, F z := by
  unfold polarTransform
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, polarNumerator_half z.re z.im_pos, mul_one]

/-- `N_F(s) = 2s(2s − 1) Λ_F(s)` for `s ∉ {0, ½}`. -/
theorem numeratorTransform_eq_mul_seedTransform {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) :
    numeratorTransform F s = 2 * s * (2 * s - 1) * seedTransform F s := by
  have hd : (1 + 2 * (s - 1 / 2)) * (2 * (s - 1 / 2)) ≠ 0 := by
    refine mul_ne_zero (fun h => h0 (by linear_combination h / 2)) (fun h => h1 (by linear_combination h / 2))
  have e : (1 + 2 * (s - 1 / 2)) * (2 * (s - 1 / 2)) = 2 * s * (2 * s - 1) := by ring
  rw [e] at hd
  unfold numeratorTransform seedTransform
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [EisAuto.completedEisenstein, e]
  have h2 : s * 2 - 1 ≠ 0 := fun h => h1 (by linear_combination h / 2)
  have h3 : 2 * s - 1 ≠ 0 := fun h => h1 (by linear_combination h / 2)
  field_simp

/-! ### The mass constant and the pole at `s = 1` -/

theorem xi_two : xi 2 = (Real.pi : ℂ) / 6 := by
  rw [xi_eq_half_mul two_ne_zero (by norm_num)]
  have hζ := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
  rw [riemannZeta_two] at hζ
  have hG : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    rw [Gammaℝ_def, show -(2 : ℂ) / 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num,
      Complex.Gamma_one, mul_one, cpow_neg_one]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h2 : completedRiemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 * Gammaℝ 2 := by
    rw [hζ, div_mul_cancel₀]
    rw [hG]; exact inv_ne_zero hπ
  rw [h2, hG]
  field_simp
  ring

/-- The equidistribution constant `c_F = (3/π) ∫_𝒟 F`. -/
def massConstant (F : ℍ → ℂ) : ℂ := (3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, F z

/-- `g(s) = P_F(s)/(2ξ(2s))`: the response is `g(s)/(s − 1)` near `s = 1`. -/
def polarRatio (F : ℍ → ℂ) (s : ℂ) : ℂ := polarTransform F s / (2 * xi (2 * s))

theorem polarRatio_one : polarRatio F 1 = massConstant F := by
  rw [polarRatio, polarTransform_one, mul_one, xi_two, massConstant]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

theorem differentiableAt_polarRatio (hF : IsSeed F) {s : ℂ} (hs : xi (2 * s) ≠ 0) :
    DifferentiableAt ℂ (polarRatio F) s :=
  (differentiable_polarTransform hF s).div ((differentiableAt_const _).mul
    ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s))
    (mul_ne_zero two_ne_zero hs)

theorem numeratorTransform_div_eq {s : ℂ} (hs : s ≠ 1) :
    numeratorTransform F s / xi (2 * s) = polarRatio F s / (s - 1) := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hN : numeratorTransform F s = polarTransform F s / (2 * (s - 1)) := by
    rw [polarTransform_eq hs]; field_simp
  rw [hN, polarRatio]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ### The response transform -/

/-- **The Mellin transform of the response is `N_F(s)/ξ(2s)` on all of `Re s > 1`.** -/
theorem mellin_response_eq (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) :
    mellin (response F) (s - 1) = numeratorTransform F s / xi (2 * s) := by
  obtain ⟨M, κ, hM, hκ, hb⟩ := norm_response_le hF
  have htop : response F =O[atTop] fun t => Real.exp (-κ * t) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hb y hy
  have hbot : response F =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact (hb y hy).trans (mul_le_of_le_one_right hM (Real.exp_le_one_iff.2 (by nlinarith)))
  have hloc : LocallyIntegrableOn (response F) (Ioi 0) := by
    have h := mellinConvergent_response hF (s := 2) (by norm_num)
    exact (h.congr_fun (fun y _ => by norm_num) measurableSet_Ioi).locallyIntegrableOn
  have hdM : ∀ w : ℂ, 1 < w.re → DifferentiableAt ℂ (fun w => mellin (response F) (w - 1)) w := fun w hw =>
    (mellin_differentiableAt_of_isBigO_rpow_exp hκ hloc htop hbot (by simp; linarith)).comp w
      (differentiableAt_id.sub_const 1)
  have hdR : ∀ w : ℂ, 1 < w.re → DifferentiableAt ℂ (fun w => numeratorTransform F w / xi (2 * w)) w := by
    intro w hw
    have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
    have hxi : xi (2 * w) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
    have hd := (differentiableOn_numeratorTransform hF).differentiableAt (isOpen_compl_singleton.mem_nhds hw1)
    exact hd.div ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) w) hxi
  set W : Set ℂ := {w | 1 < w.re}
  have hW : IsOpen W := isOpen_lt continuous_const continuous_re
  have hWc : IsPreconnected W := (convex_halfSpace_re_gt 1).isPreconnected
  have hfA : AnalyticOnNhd ℂ (fun w => mellin (response F) (w - 1)) W :=
    DifferentiableOn.analyticOnNhd (fun w hw => (hdM w hw).differentiableWithinAt) hW
  have hfB : AnalyticOnNhd ℂ (fun w => numeratorTransform F w / xi (2 * w)) W :=
    DifferentiableOn.analyticOnNhd (fun w hw => (hdR w hw).differentiableWithinAt) hW
  have h2W : (2 + I : ℂ) ∈ W := by simp [W]
  have hev : (fun w => mellin (response F) (w - 1)) =ᶠ[𝓝 (2 + I)]
      fun w => numeratorTransform F w / xi (2 * w) := by
    have hopen : IsOpen ({w : ℂ | 1 < w.re} ∩ {w : ℂ | 0 < w.im}) :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)
    filter_upwards [hopen.mem_nhds (show (2 + I : ℂ) ∈ _ from ⟨by simp, by simp⟩)] with w hw
    have hw0 : w ≠ 0 := fun h => by have := hw.1; rw [h] at this; simp at this; linarith
    have hw12 : w ≠ 1 / 2 := fun h => by have := hw.1; rw [h] at this; norm_num at this
    rw [← responseContinuation_eq_mellin hF hw.1 hw.2.ne', responseContinuation,
      numeratorTransform_eq_mul_seedTransform hw0 hw12]
    ring
  exact hfA.eqOn_of_preconnected_of_eventuallyEq hfB hWc h2W hev hs

/-- The tail `∫_1^∞ a_F(y) y^{s−2} dy`, an entire function. -/
def tailTransform (F : ℍ → ℂ) (s : ℂ) : ℂ := ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ (s - 2) * response F y

theorem tailTransform_eq_mellin (s : ℂ) :
    tailTransform F s = mellin ((Ioi (1 : ℝ)).indicator (response F)) (s - 1) := by
  rw [tailTransform, mellin, ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · have hy0 : y ∈ Ioi (0 : ℝ) := mem_Ioi.2 (lt_trans zero_lt_one hy)
    simp only [indicator_of_mem hy, indicator_of_mem hy0, smul_eq_mul, show s - 1 - 1 = s - 2 by ring]
  · simp only [indicator_of_notMem hy]
    by_cases hy0 : y ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem hy0, indicator_of_notMem hy]
    · simp [indicator_of_notMem hy0]

theorem differentiable_tailTransform (hF : IsSeed F) : Differentiable ℂ (tailTransform F) := by
  obtain ⟨M, κ, hM, hκ, hb⟩ := norm_response_le hF
  intro s
  set f := (Ioi (1 : ℝ)).indicator (response F)
  have htop : f =O[atTop] fun t => Real.exp (-κ * t) := by
    refine IsBigO.of_bound M ?_
    filter_upwards [eventually_gt_atTop 1] with y hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, show f y = response F y from indicator_of_mem hy _]
    exact hb y (lt_trans zero_lt_one hy)
  have hbot : f =O[𝓝[>] 0] (· ^ (-((s - 1).re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    rw [show f y = 0 from indicator_of_notMem (fun h : y ∈ Ioi (1 : ℝ) => (not_lt.2 hy.2.le) h) _]
    simp
  have hloc : LocallyIntegrableOn f (Ioi 0) := by
    have h := (mellinConvergent_response hF (s := 2) (by norm_num))
    have hI : IntegrableOn (response F) (Ioi 0) := h.congr_fun (fun y _ => by norm_num) measurableSet_Ioi
    exact (hI.indicator measurableSet_Ioi).locallyIntegrableOn
  have hd := mellin_differentiableAt_of_isBigO_rpow_exp (s := s - 1) hκ hloc htop hbot (by linarith)
  have heq : tailTransform F = fun w => mellin f (w - 1) := funext fun w => tailTransform_eq_mellin w
  rw [heq]
  exact DifferentiableAt.comp (g := mellin f) (f := fun w : ℂ => w - 1) s hd
    (differentiableAt_id.sub_const 1)

/-- The continuation of `∫_0^1 (a_F(y) − c_F) y^{s−2} dy`. -/
def lowerTransform (F : ℍ → ℂ) (s : ℂ) : ℂ := dslope (polarRatio F) 1 s - tailTransform F s

/-- **The lower transform is analytic at every point where `ξ(2s) ≠ 0`.** -/
theorem analyticAt_lowerTransform (hF : IsSeed F) {s : ℂ} (hs : xi (2 * s) ≠ 0) :
    AnalyticAt ℂ (lowerTransform F) s := by
  have hcont : Continuous fun w : ℂ => xi (2 * w) :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)).continuous
  set U : Set ℂ := {w | xi (2 * w) ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hcont continuous_const
  have hgU : DifferentiableOn ℂ (polarRatio F) U := fun w hw =>
    (differentiableAt_polarRatio hF hw).differentiableWithinAt
  have hT := differentiable_tailTransform hF
  by_cases h1 : s = 1
  · subst h1
    have hmem : U ∈ 𝓝 (1 : ℂ) := hU.mem_nhds hs
    have hd : DifferentiableOn ℂ (dslope (polarRatio F) 1) U := (differentiableOn_dslope hmem).2 hgU
    exact (DifferentiableOn.analyticOnNhd (hd.sub hT.differentiableOn) hU) 1 hs
  · set V : Set ℂ := U ∩ {1}ᶜ
    have hV : IsOpen V := hU.inter isOpen_compl_singleton
    have hd : DifferentiableOn ℂ (dslope (polarRatio F) 1) V := fun w hw =>
      ((differentiableAt_dslope_of_ne hw.2).2 ((hgU w hw.1).differentiableAt (hU.mem_nhds hw.1)))
        |>.differentiableWithinAt
    exact (DifferentiableOn.analyticOnNhd (hd.sub hT.differentiableOn) hV) s ⟨hs, h1⟩

/-- **The lower transform is the Mellin integral of the remainder.** For `Re s > 1`,
`∫_0^1 (a_F(y) − c_F) y^{s−2} dy = lowerTransform F s`. -/
theorem integral_lower_eq (hF : IsSeed F) {s : ℂ} (hs : 1 < s.re) :
    ∫ y in Ioo (0 : ℝ) 1, (y : ℂ) ^ (s - 2) * (response F y - massConstant F) = lowerTransform F s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hM := mellinConvergent_response hF hs
  have hsplit : mellin (response F) (s - 1) = (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 2) * response F y) +
      tailTransform F s := by
    rw [mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hM.mono_set Ioc_subset_Ioi_self) (hM.mono_set (Ioi_subset_Ioi zero_le_one))]
    simp only [smul_eq_mul, show s - 1 - 1 = s - 2 by ring, tailTransform]
  have hc : ∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 2) * massConstant F = massConstant F / (s - 1) := by
    obtain ⟨h1, h2⟩ := hasMellin_one_Ioc (s := s - 1) (by simp; linarith)
    rw [mellin, ← integral_indicator measurableSet_Ioi] at h2
    rw [integral_mul_const, ← integral_indicator measurableSet_Ioc]
    have e : (∫ y, (Ioc (0 : ℝ) 1).indicator (fun y : ℝ => (y : ℂ) ^ (s - 2)) y) = 1 / (s - 1) := by
      rw [← h2]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ Ioc (0 : ℝ) 1
      · simp [indicator_of_mem hy, indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy.1),
          show s - 1 - 1 = s - 2 by ring]
      · by_cases hy0 : y ∈ Ioi (0 : ℝ)
        · simp [indicator_of_notMem hy, indicator_of_mem hy0]
        · simp [indicator_of_notMem hy, indicator_of_notMem hy0]
    rw [e]; ring
  have hint1 : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 2) * response F y) (Ioc 0 1) := by
    refine (hM.mono_set Ioc_subset_Ioi_self).congr_fun (fun y _ => ?_) measurableSet_Ioc
    simp only [smul_eq_mul, show s - 1 - 1 = s - 2 by ring]
  have hint2 : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 2) * massConstant F) (Ioc 0 1) := by
    have := (hasMellin_one_Ioc (s := s - 1) (by simp; linarith)).1
    have hp : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 2)) (Ioc 0 1) :=
      IntegrableOn.congr_fun (this.mono_set Ioc_subset_Ioi_self) (fun y hy => by
        simp [indicator_of_mem hy, show s - 1 - 1 = s - 2 by ring]) measurableSet_Ioc
    exact hp.mul_const (massConstant F)
  rw [← integral_Ioc_eq_integral_Ioo]
  have e : ∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 2) * (response F y - massConstant F) =
      (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 2) * response F y) - massConstant F / (s - 1) := by
    rw [← hc, ← integral_sub hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only; ring
  rw [e, lowerTransform, dslope_of_ne _ hs1, slope_def_field, polarRatio_one]
  have hmel := mellin_response_eq hF hs
  rw [numeratorTransform_div_eq hs1, hsplit] at hmel
  rw [show (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 2) * response F y) =
    polarRatio F s / (s - 1) - tailTransform F s by linear_combination hmel]
  ring

/-- **The response transform is regular at every real point except `s = 1`.** -/
theorem differentiableAt_responseTransform_of_real (hF : IsSeed F) {t : ℝ} (ht : t ≠ 1) :
    DifferentiableAt ℂ (fun s => numeratorTransform F s / xi (2 * s)) t := by
  have ht1 : (t : ℂ) ≠ 1 := fun h => ht (by exact_mod_cast h)
  have hxi : xi (2 * (t : ℂ)) ≠ 0 := by
    rw [show (2 : ℂ) * (t : ℂ) = ((2 * t : ℝ) : ℂ) by push_cast; ring]
    exact xi_ne_zero_of_real _
  exact ((differentiableOn_numeratorTransform hF).differentiableAt
    (isOpen_compl_singleton.mem_nhds ht1)).div
    ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) t) hxi

/-- **The worldline tower is invisible (M1).** The single-image bounce has poles on the lattice `s = ½ − k`,
the normal modes `½ + 2k` of the `Δ = ½` worldline in the variable `2s − 1`. For every seed the response
transform is regular at all of them: the image sum cancels the kinematic tower (with the pole of `ζ` at
`k = 0` and the trivial zeros for `k ≥ 1`). -/
theorem differentiableAt_responseTransform_worldline (hF : IsSeed F) (k : ℕ) :
    DifferentiableAt ℂ (fun s => numeratorTransform F s / xi (2 * s)) (1 / 2 - k) := by
  have h := differentiableAt_responseTransform_of_real hF (t := 1 / 2 - k) (by
    have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)
  simpa using h

/-! ### Landau on the dual side -/

theorem image_exp_neg_mul_Ioi {l : ℝ} (hl : 0 < l) :
    (fun v : ℝ => Real.exp (-(l * v))) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    rw [Real.exp_lt_one_iff]
    have : 0 < l * v := mul_pos hl hv
    linarith
  · rintro ⟨h0, h1⟩
    refine ⟨-Real.log x / l, ?_, ?_⟩
    · exact div_pos (by simpa using Real.log_neg h0 h1) hl
    · show Real.exp (-(l * (-Real.log x / l))) = x
      rw [mul_div_cancel₀ _ hl.ne', neg_neg, Real.exp_log h0]

/-- **Mellin = Laplace under `y = e^{−l v}`.** -/
theorem integral_laplace_eq_mellin {l : ℝ} (hl : 0 < l) (r : ℝ → ℂ) (s : ℂ) :
    ∫ v in Ioi (0 : ℝ), (l : ℂ) * r (Real.exp (-(l * v))) * Complex.exp (-((l : ℂ) * (s - 1)) * v) =
      ∫ y in Ioo (0 : ℝ) 1, (y : ℂ) ^ (s - 2) * r y := by
  have hderiv : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun v : ℝ => Real.exp (-(l * v)))
      (-l * Real.exp (-(l * v))) (Ioi 0) v := by
    intro v _
    have h : HasDerivAt (fun v : ℝ => Real.exp (-(l * v))) (Real.exp (-(l * v)) * -(l * 1)) v :=
      ((hasDerivAt_id' v).const_mul l).neg.exp
    exact h.hasDerivWithinAt.congr_deriv (by ring)
  have hinj : InjOn (fun v : ℝ => Real.exp (-(l * v))) (Ioi 0) := by
    intro x _ y _ hxy
    have := Real.exp_injective hxy
    have : l * x = l * y := by linarith
    exact mul_left_cancel₀ hl.ne' this
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun y : ℝ => (y : ℂ) ^ (s - 2) * r y)
  rw [image_exp_neg_mul_Ioi hl] at hchange
  rw [hchange]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  have hE : (((Real.exp (-(l * v)) : ℝ) : ℂ)) ^ (s - 2) = Complex.exp ((s - 2) * ((-(l * v) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, mul_comm]
  rw [abs_mul, abs_neg, abs_of_pos hl, abs_of_pos (Real.exp_pos _), Complex.real_smul, hE,
    Complex.ofReal_mul, Complex.ofReal_exp]
  rw [show ((l : ℂ) * Complex.exp (((-(l * v) : ℝ) : ℂ))) * (Complex.exp ((s - 2) * ((-(l * v) : ℝ) : ℂ)) *
      r (Real.exp (-(l * v)))) = (l : ℂ) * r (Real.exp (-(l * v))) *
      (Complex.exp (((-(l * v) : ℝ) : ℂ)) * Complex.exp ((s - 2) * ((-(l * v) : ℝ) : ℂ))) by ring,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A real seed has a real response and a real mass constant. -/
theorem im_response_eq_zero (hreal : ∀ z, (F z).im = 0) (y : ℝ) : (response F y).im = 0 := by
  have hF : ∀ z, F z = ((F z).re : ℂ) := fun z => Complex.ext (by simp) (by simp [hreal z])
  rw [response, show (fun x : ℝ => F (ofComplex ⟨x, y⟩)) = fun x => (((F (ofComplex ⟨x, y⟩)).re : ℝ) : ℂ)
    from funext fun x => hF _, integral_complex_ofReal, ofReal_im]

theorem im_massConstant_eq_zero (hreal : ∀ z, (F z).im = 0) : (massConstant F).im = 0 := by
  have hF : ∀ z, F z = ((F z).re : ℂ) := fun z => Complex.ext (by simp) (by simp [hreal z])
  rw [massConstant, show (fun z => F z) = fun z => (((F z).re : ℝ) : ℂ) from funext hF, integral_complex_ofReal,
    show (3 / Real.pi : ℂ) = ((3 / Real.pi : ℝ) : ℂ) by push_cast; ring, ← ofReal_mul, ofReal_im]

/-- The **dual profile** `v ↦ l (a_F(e^{−lv}) − c_F) e^{v/2}`, the remainder in Landau's normalization. -/
def dualProfile (F : ℍ → ℂ) (l v : ℝ) : ℝ :=
  l * (response F (Real.exp (-(l * v))) - massConstant F).re * Real.exp (v / 2)

theorem measurable_dualProfile (hF : IsSeed F) (l : ℝ) : Measurable (dualProfile F l) := by
  have h1 : Continuous fun v : ℝ => Real.exp (-(l * v)) := by fun_prop
  have hcr : Continuous fun v : ℝ => response F (Real.exp (-(l * v))) - massConstant F :=
    ((continuousOn_response hF).comp_continuous h1 fun v => Real.exp_pos _).sub continuous_const
  exact ((continuous_const.mul (Complex.continuous_re.comp hcr)).mul (by fun_prop)).measurable

theorem abs_dualProfile_le (hF : IsSeed F) {l : ℝ} (hl : 0 < l) :
    ∃ K : ℝ, ∀ v, 0 < v → |dualProfile F l v| ≤ K * Real.exp (v / 2) := by
  obtain ⟨M, κ, hM, hκ, hb⟩ := norm_response_le hF
  refine ⟨l * (M + ‖massConstant F‖), fun v _ => ?_⟩
  have hy := Real.exp_pos (-(l * v))
  have hres : ‖response F (Real.exp (-(l * v)))‖ ≤ M :=
    (hb _ hy).trans (mul_le_of_le_one_right hM (Real.exp_le_one_iff.2 (by nlinarith)))
  have hrb : |(response F (Real.exp (-(l * v))) - massConstant F).re| ≤ M + ‖massConstant F‖ := by
    refine (Complex.abs_re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
    linarith
  rw [dualProfile, abs_mul, abs_mul, abs_of_pos hl, abs_of_pos (Real.exp_pos _)]
  calc l * |(response F (Real.exp (-(l * v))) - massConstant F).re| * Real.exp (v / 2)
      ≤ l * (M + ‖massConstant F‖) * Real.exp (v / 2) := by gcongr

theorem dualProfile_le {α C l : ℝ} (hlα : l * α = 1 / 2) (hl : 0 < l)
    (hone : ∀ y : ℝ, 0 < y → y ≤ 1 → (response F y - massConstant F).re ≤ C * y ^ α) :
    ∀ v, 0 ≤ v → dualProfile F l v ≤ (l * C) * Real.exp (0 * v) := by
  intro v hv
  have hy := Real.exp_pos (-(l * v))
  have hy1 : Real.exp (-(l * v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h := hone _ hy hy1
  have hpow : Real.exp (-(l * v)) ^ α = Real.exp (-(v / 2)) := by
    rw [← Real.exp_mul]; congr 1; nlinarith
  rw [hpow] at h
  have hE : Real.exp (-(v / 2)) * Real.exp (v / 2) = 1 := by rw [← Real.exp_add]; simp
  rw [dualProfile, zero_mul, Real.exp_zero, mul_one]
  calc l * (response F (Real.exp (-(l * v))) - massConstant F).re * Real.exp (v / 2)
      ≤ l * (C * Real.exp (-(v / 2))) * Real.exp (v / 2) := by gcongr
    _ = l * C * (Real.exp (-(v / 2)) * Real.exp (v / 2)) := by ring
    _ = l * C := by rw [hE, mul_one]

/-- The Laplace transform of the dual profile is the lower transform at `s = 1 + (z − ½)/l`. -/
theorem integral_dualProfile (hF : IsSeed F) (hreal : ∀ z, (F z).im = 0) {l : ℝ} (hl : 0 < l) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    ∫ v in Ioi (0 : ℝ), (dualProfile F l v : ℂ) * Complex.exp (-z * (v : ℂ)) =
      lowerTransform F (1 + (z - 1 / 2) / l) := by
  set s := 1 + (z - 1 / 2) / l
  have hlC : (l : ℂ) ≠ 0 := ofReal_ne_zero.2 hl.ne'
  have hsre : s.re = 1 + (z.re - 1 / 2) / l := by simp [s, Complex.div_ofReal_re]
  have hs : 1 < s.re := by
    rw [hsre]; have := div_pos (by linarith : 0 < z.re - 1 / 2) hl; linarith
  have hreal' : ∀ y, (((response F y - massConstant F).re : ℝ) : ℂ) = response F y - massConstant F :=
    fun y => Complex.ext (by simp) (by simp [im_response_eq_zero hreal, im_massConstant_eq_zero hreal])
  have hls : (l : ℂ) * (s - 1) = z - 1 / 2 := by simp only [s]; field_simp; ring
  have hpt : ∀ v : ℝ, (dualProfile F l v : ℂ) * Complex.exp (-z * (v : ℂ)) =
      (l : ℂ) * (response F (Real.exp (-(l * v))) - massConstant F) *
        Complex.exp (-((l : ℂ) * (s - 1)) * v) := by
    intro v
    rw [dualProfile, Complex.ofReal_mul, Complex.ofReal_mul, hreal', Complex.ofReal_exp, mul_assoc,
      ← Complex.exp_add, hls]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_laplace_eq_mellin hl (fun y => response F y - massConstant F) s]
  exact integral_lower_eq hF hs

/-- **Landau.** A one-sided bound at rate `y^α` continues the lower transform to `Re s > 1 − α`. -/
theorem exists_lower_extension_of_oneSided (hF : IsSeed F) (hreal : ∀ z, (F z).im = 0) {α C : ℝ}
    (hα : 0 < α) (hone : ∀ y : ℝ, 0 < y → y ≤ 1 → (response F y - massConstant F).re ≤ C * y ^ α) :
    ∃ Gs : ℂ → ℂ, (∀ s : ℂ, 1 - α < s.re → DifferentiableAt ℂ Gs s) ∧
      ∀ s : ℂ, 1 < s.re → Gs s = lowerTransform F s := by
  set l : ℝ := 1 / (2 * α)
  have hl : 0 < l := by positivity
  have hlα : l * α = 1 / 2 := by simp only [l]; field_simp
  obtain ⟨K, hK⟩ := abs_dualProfile_le hF hl
  have hΛ : ∀ t : ℝ, 0 < t → AnalyticAt ℂ (fun z : ℂ => lowerTransform F (1 + (z - 1 / 2) / l)) t := by
    intro t _
    have hxi : xi (2 * (1 + ((t : ℂ) - 1 / 2) / l)) ≠ 0 := by
      rw [show (2 : ℂ) * (1 + ((t : ℂ) - 1 / 2) / l) = ((2 * (1 + (t - 1 / 2) / l) : ℝ) : ℂ) by
        push_cast; ring]
      exact xi_ne_zero_of_real _
    have hg : AnalyticAt ℂ (fun z : ℂ => 1 + (z - 1 / 2) / l) t := by fun_prop
    exact AnalyticAt.comp (g := lowerTransform F) (f := fun z : ℂ => 1 + (z - 1 / 2) / l)
      (analyticAt_lowerTransform hF hxi) hg
  obtain ⟨G, hGd, hGeq⟩ := RHTower.exists_differentiable_extension_of_le_exp (measurable_dualProfile hF l)
    hK le_rfl (by norm_num) (dualProfile_le hlα hl hone) hΛ fun z hz => integral_dualProfile hF hreal hl hz
  refine ⟨fun s => G (1 / 2 + (l : ℂ) * (s - 1)), fun s hs => ?_, fun s hs => ?_⟩
  · have hre : 0 < (1 / 2 + (l : ℂ) * (s - 1)).re := by
      have : (1 / 2 + (l : ℂ) * (s - 1)).re = 1 / 2 + l * (s.re - 1) := by simp
      rw [this]; nlinarith
    exact (hGd _ hre).comp s (by fun_prop)
  · have hre : 1 / 2 < (1 / 2 + (l : ℂ) * (s - 1)).re := by
      have : (1 / 2 + (l : ℂ) * (s - 1)).re = 1 / 2 + l * (s.re - 1) := by simp
      rw [this]; nlinarith
    simp only
    rw [hGeq _ hre]
    have hlC : (l : ℂ) ≠ 0 := ofReal_ne_zero.2 hl.ne'
    congr 1
    field_simp
    ring

/-- `(G(s) + tail(s) + c_F/(s − 1)) ξ(2s) − N_F(s)`: vanishes where `G` is the lower transform. -/
def transportDefect (F : ℍ → ℂ) (Gs : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Gs s + tailTransform F s + massConstant F / (s - 1)) * xi (2 * s) - numeratorTransform F s

theorem differentiableAt_transportDefect (hF : IsSeed F) {Gs : ℂ → ℂ} {s : ℂ} (hG : DifferentiableAt ℂ Gs s)
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (transportDefect F Gs) s := by
  have hxiD : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s)) s :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s
  have hN : DifferentiableAt ℂ (numeratorTransform F) s :=
    (differentiableOn_numeratorTransform hF).differentiableAt (isOpen_compl_singleton.mem_nhds hs1)
  have hc : DifferentiableAt ℂ (fun s : ℂ => massConstant F / (s - 1)) s :=
    (differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.2 hs1)
  have hsum : DifferentiableAt ℂ (fun s => Gs s + tailTransform F s + massConstant F / (s - 1)) s :=
    (hG.add (differentiable_tailTransform hF s)).add hc
  exact (hsum.mul hxiD).sub hN

theorem transportDefect_eq_zero {Gs : ℂ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hGs : Gs s = lowerTransform F s) : transportDefect F Gs s = 0 := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hxi : xi (2 * s) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  have hN := numeratorTransform_div_eq (F := F) hs1
  rw [div_eq_iff hxi] at hN
  have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  rw [transportDefect, hGs, lowerTransform, dslope_of_ne _ hs1, slope_def_field, polarRatio_one, hN]
  field_simp
  ring

/-- **Transport to the zeros.** An extension of the lower transform to `Re s > σ` kills `Λ_F` at every zero
of `ξ(2s)` with `Re s > σ`. -/
theorem seedTransform_eq_zero_of_lower_extension (hF : IsSeed F) {σ : ℝ} {Gs : ℂ → ℂ}
    (hGs : ∀ s : ℂ, σ < s.re → DifferentiableAt ℂ Gs s) (hGs_eq : ∀ s : ℂ, 1 < s.re → Gs s = lowerTransform F s)
    {s₀ : ℂ} (hs₀ : σ < s₀.re) (hz : xi (2 * s₀) = 0) : seedTransform F s₀ = 0 := by
  have him₀ : s₀.im ≠ 0 := by
    intro h
    have e : 2 * s₀ = ((2 * s₀.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
    exact xi_ne_zero_of_real _ (e ▸ hz)
  have key : ∀ W : Set ℂ, IsOpen W → IsPreconnected W → (∀ s ∈ W, σ < s.re ∧ s.im ≠ 0) →
      ∀ z₀ ∈ W, 1 < z₀.re → EqOn (transportDefect F Gs) 0 W := by
    intro W hW hWc hWs z₀ hz₀ hz₀re
    have hfH : AnalyticOnNhd ℂ (transportDefect F Gs) W := DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_transportDefect hF (hGs s (hWs s hs).1)
        (fun h => (hWs s hs).2 (by rw [h]; simp))).differentiableWithinAt) hW
    have hev : transportDefect F Gs =ᶠ[𝓝 z₀] 0 := by
      have hopen : IsOpen ({s : ℂ | 1 < s.re} ∩ W) := (isOpen_lt continuous_const continuous_re).inter hW
      filter_upwards [hopen.mem_nhds ⟨hz₀re, hz₀⟩] with s hs
      exact transportDefect_eq_zero hs.1 (hGs_eq s hs.1)
    exact hfH.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc hz₀ hev
  have hval : transportDefect F Gs s₀ = 0 := by
    rcases lt_or_gt_of_ne him₀ with hneg | hpos
    · have hW : IsOpen {s : ℂ | σ < s.re ∧ s.im < 0} := (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_im continuous_const)
      have hWc : IsPreconnected {s : ℂ | σ < s.re ∧ s.im < 0} :=
        ((convex_halfSpace_re_gt σ).inter (convex_halfSpace_im_lt 0)).isPreconnected
      have hre : (((max σ 1 + 1 : ℝ) : ℂ) - I).re = max σ 1 + 1 := by simp
      exact key _ hW hWc (fun s hs => ⟨hs.1, hs.2.ne⟩) (((max σ 1 + 1 : ℝ) : ℂ) - I)
        ⟨by rw [hre]; linarith [le_max_left σ 1], by simp⟩
        (by rw [hre]; linarith [le_max_right σ 1]) ⟨hs₀, hneg⟩
    · have hW : IsOpen {s : ℂ | σ < s.re ∧ 0 < s.im} := (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_const continuous_im)
      have hWc : IsPreconnected {s : ℂ | σ < s.re ∧ 0 < s.im} :=
        ((convex_halfSpace_re_gt σ).inter (convex_halfSpace_im_gt 0)).isPreconnected
      have hre : (((max σ 1 + 1 : ℝ) : ℂ) + I).re = max σ 1 + 1 := by simp
      exact key _ hW hWc (fun s hs => ⟨hs.1, hs.2.ne'⟩) (((max σ 1 + 1 : ℝ) : ℂ) + I)
        ⟨by rw [hre]; linarith [le_max_left σ 1], by simp⟩
        (by rw [hre]; linarith [le_max_right σ 1]) ⟨hs₀, hpos⟩
  have hN0 : numeratorTransform F s₀ = 0 := by
    rw [transportDefect, hz, mul_zero, zero_sub, neg_eq_zero] at hval
    exact hval
  have h0 : s₀ ≠ 0 := fun h => him₀ (by rw [h]; simp)
  have h12 : s₀ ≠ 1 / 2 := fun h => him₀ (by rw [h]; simp)
  rw [numeratorTransform_eq_mul_seedTransform h0 h12] at hN0
  have hd : 2 * s₀ * (2 * s₀ - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero h0) (fun h => h12 (by linear_combination h / 2))
  exact (mul_eq_zero.1 hN0).resolve_left hd

/-- **One-sided bounds on the dual side are two-sided.** For a real seed, `a_F(y) − c_F ≤ C y^α` on `(0, 1]`
with `α > 0` forces `Λ_F(s₀) = 0` at every zero `s₀` of `ξ(2s)` with `Re s₀ > 1 − α`. -/
theorem seedTransform_eq_zero_of_oneSided (hF : IsSeed F) (hreal : ∀ z, (F z).im = 0) {α C : ℝ}
    (hα : 0 < α) (hone : ∀ y : ℝ, 0 < y → y ≤ 1 → (response F y - massConstant F).re ≤ C * y ^ α)
    {s₀ : ℂ} (hs₀ : 1 - α < s₀.re) (hz : xi (2 * s₀) = 0) : seedTransform F s₀ = 0 := by
  obtain ⟨Gs, hGs, hGs_eq⟩ := exists_lower_extension_of_oneSided hF hreal hα hone
  exact seedTransform_eq_zero_of_lower_extension hF hGs hGs_eq hs₀ hz

/-! ### Both signs -/

theorem response_neg (F : ℍ → ℂ) (y : ℝ) : response (fun z => -F z) y = -response F y := by
  rw [response, response, integral_neg]

theorem massConstant_neg (F : ℍ → ℂ) : massConstant (fun z => -F z) = -massConstant F := by
  rw [massConstant, massConstant, integral_neg]; ring

theorem seedTransform_neg (F : ℍ → ℂ) (s : ℂ) : seedTransform (fun z => -F z) s = -seedTransform F s := by
  rw [seedTransform, seedTransform, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only; ring

theorem IsSeed.neg (hF : IsSeed F) : IsSeed (fun z => -F z) := by
  have h := hF.const_mul (-1)
  simpa [neg_one_mul] using h

/-- **The lower side.** For a real seed, `a_F(y) − c_F ≥ −C y^α` on `(0, 1]` also forces `Λ_F(s₀) = 0` at the
zeros of `ξ(2s)` with `Re s₀ > 1 − α`. -/
theorem seedTransform_eq_zero_of_oneSided_lower (hF : IsSeed F) (hreal : ∀ z, (F z).im = 0) {α C : ℝ}
    (hα : 0 < α) (hone : ∀ y : ℝ, 0 < y → y ≤ 1 → -(C * y ^ α) ≤ (response F y - massConstant F).re)
    {s₀ : ℂ} (hs₀ : 1 - α < s₀.re) (hz : xi (2 * s₀) = 0) : seedTransform F s₀ = 0 := by
  have h := seedTransform_eq_zero_of_oneSided hF.neg (fun z => by simp [hreal z]) hα (C := C)
    (fun y hy hy1 => by
      rw [response_neg, massConstant_neg, show -response F y - -massConstant F =
        -(response F y - massConstant F) by ring, Complex.neg_re]
      linarith [hone y hy hy1]) hs₀ hz
  rw [seedTransform_neg] at h
  exact neg_eq_zero.1 h

/-- **A seen resonance forbids a sign at its scale.** If a real seed sees the resonance `ρ/2` of a zero `ρ` of
`ζ` with `Re ρ > 0`, then for every `α > 1 − Re ρ/2` the remainder `a_F(y) − c_F` is bounded neither above nor
below by `C y^α` on `(0, 1]`: it changes sign beyond every multiple of `y^α`. -/
theorem not_oneSided_of_seen (hF : IsSeed F) (hreal : ∀ z, (F z).im = 0) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hpos : 0 < ρ.re) (hseen : seedTransform F (ρ / 2) ≠ 0) {α : ℝ} (hα : 1 - ρ.re / 2 < α) (C : ℝ) :
    (¬ ∀ y : ℝ, 0 < y → y ≤ 1 → (response F y - massConstant F).re ≤ C * y ^ α) ∧
      ¬ ∀ y : ℝ, 0 < y → y ≤ 1 → -(C * y ^ α) ≤ (response F y - massConstant F).re := by
  have hρ1 : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have hα0 : 0 < α := by linarith
  have hxi : xi (2 * (ρ / 2)) = 0 := by
    rw [show 2 * (ρ / 2) = ρ by ring]
    refine xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.2 ⟨hζ, fun n hn => ?_⟩
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hre : 1 - α < (ρ / 2).re := by simp; linarith
  exact ⟨fun h => hseen (seedTransform_eq_zero_of_oneSided hF hreal hα0 h hre hxi),
    fun h => hseen (seedTransform_eq_zero_of_oneSided_lower hF hreal hα0 h hre hxi)⟩

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
