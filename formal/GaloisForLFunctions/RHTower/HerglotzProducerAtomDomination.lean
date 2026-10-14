import GaloisForLFunctions.RHTower.WeilHerglotzPhaseLockRigidity
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiDivisorContour
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity

/-!
# A Herglotz producer whose quotient by `ξ` stays bounded at the zeros is `Λ`

Let `Φ` be holomorphic on `Re s > ½` with `Re Φ ≥ 0`, equal to
`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{−s}` on `Re s > 1`, and let `G' = ΦG` with
`G(2) = 2Γ_ℝ(2) exp(Σ lam(n) 2^{−n}/log n)`.  Suppose `G = s(s−1)Γ_ℝ(s)ζ(s)A(s)` on `Re s > ½`
(`s ≠ 1`) with `A` holomorphic there.

**Theorem** (`eq_vonMangoldt_of_quotient_rayBounded`).  If `A` is bounded on the horizontal segment
`½ + ε + iγ`, `0 < ε < 1`, at every zero `½ + iγ` of `ξ`, then `lam(n) = Λ(n)` for every `n ≥ 2`,
and the Riemann hypothesis holds.  No condition on the size of `A` away from the zeros and no
reflection identity for `G` is used.

**Proof.**
* `G` has no zero, so `ξ` has none on `Re s > ½`, hence none off the line; and
  `A'/A = Φ − ξ'/ξ` there.
* In the disc chart `w = (s − 3/2)/(s + ½)`, `Re Φ` is the Poisson integral of a finite measure `ν`
  on the circle (`exists_poissonRepresentation_halfPlane`).  The Poisson kernel at the boundary
  point of `½ + iγ` is `(1 + γ²) Re(1/(s − ½ − iγ))`, and `ε` times the kernel is bounded along
  `½ + ε + iγ` by `|s + ½|²`.  So `ε Re Φ(½ + ε + iγ)` tends to the atom `a_γ = (1 + γ²)ν{γ}`
  (dominated convergence), while `ε Re ξ'/ξ(½ + ε + iγ)` tends to the order `m_γ` of the zero.
* If `a_γ < m_γ`, then `d/dε log|A(½ + ε + iγ)| ≤ −c/ε` near `0`, so `|A|` grows like `ε^{−c}`:
  impossible.  Hence `a_γ ≥ m_γ` at every zero.
* On `Re s > 1` the atoms alone give `Re Φ ≥ Σ_γ a_γ Re(1/(s − ½ − iγ)) ≥ Re ξ'/ξ`.  So the cosine
  series `Re Φ − Re ξ'/ξ = Σ (Λ(n) − lam(n)) n^{−σ} cos(t log n)` is nonnegative.  It has mean zero,
  so every coefficient vanishes (`abs_le_four_mul_of_logCosSeries_envelope` with zero envelope).

**Corollary** (`eq_vonMangoldt_of_quotient_continuousOn`).  The same holds when `A` is continuous on
`Re s ≥ ½`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

namespace RHTower.AtomDomination

open GaloisForLFunctions.HTGeometry RHTower.IntegerMassRigidity RHTower.WeilSpectral

/-! ## The disc chart -/

/-- The Cayley chart `s ↦ (2s − 3)/(2s + 1)` of the half-plane `Re s > ½` onto the unit disc. -/
def discPt (s : ℂ) : ℂ := (2 * s - 3) / (2 * s + 1)

/-- The inverse chart `w ↦ ½ + (1 + w)/(1 − w)`. -/
def halfPt (w : ℂ) : ℂ := 1 / 2 + (1 + w) / (1 - w)

/-- The boundary point of the disc corresponding to `½ + iγ`. -/
def bdryPt (γ : ℝ) : ℂ := discPt (1 / 2 + γ * I)

theorem two_mul_add_one_ne_zero {s : ℂ} (hs : 0 < 2 * s.re + 1) : 2 * s + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem normSq_two_mul_add_one_sub (s : ℂ) :
    normSq (2 * s + 1) - normSq (2 * s - 3) = 16 * (s.re - 1 / 2) := by
  rw [normSq_apply, normSq_apply]
  simp
  ring

theorem one_sub_norm_sq_discPt {s : ℂ} (hs : 2 * s + 1 ≠ 0) :
    1 - ‖discPt s‖ ^ 2 = 16 * (s.re - 1 / 2) / ‖2 * s + 1‖ ^ 2 := by
  have hn : normSq (2 * s + 1) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [discPt, norm_div, div_pow]
  simp only [Complex.sq_norm]
  rw [← normSq_two_mul_add_one_sub]
  field_simp

theorem norm_discPt_lt_one {s : ℂ} (hs : 1 / 2 < s.re) : ‖discPt s‖ < 1 := by
  have hne := two_mul_add_one_ne_zero (s := s) (by linarith)
  have h := one_sub_norm_sq_discPt hne
  have hpos : 0 < 16 * (s.re - 1 / 2) / ‖2 * s + 1‖ ^ 2 := by
    have : 0 < ‖2 * s + 1‖ := norm_pos_iff.mpr hne
    have : 0 < s.re - 1 / 2 := by linarith
    positivity
  nlinarith [norm_nonneg (discPt s)]

theorem bdry_two_mul_add_one_ne_zero (γ : ℝ) : 2 * (1 / 2 + γ * I : ℂ) + 1 ≠ 0 :=
  two_mul_add_one_ne_zero (by simp)

theorem norm_bdryPt (γ : ℝ) : ‖bdryPt γ‖ = 1 := by
  have h := one_sub_norm_sq_discPt (bdry_two_mul_add_one_ne_zero γ)
  have hre : ((1 / 2 + γ * I : ℂ)).re - 1 / 2 = 0 := by simp
  rw [hre, mul_zero, zero_div, sub_eq_zero] at h
  unfold bdryPt
  nlinarith [norm_nonneg (discPt (1 / 2 + γ * I))]

theorem halfPt_discPt {s : ℂ} (hs : 2 * s + 1 ≠ 0) : halfPt (discPt s) = s := by
  unfold halfPt discPt
  have e1 : 1 + (2 * s - 3) / (2 * s + 1) = (4 * s - 2) / (2 * s + 1) := by
    rw [eq_div_iff hs, add_mul, div_mul_cancel₀ _ hs]
    ring
  have e2 : 1 - (2 * s - 3) / (2 * s + 1) = 4 / (2 * s + 1) := by
    rw [eq_div_iff hs, sub_mul, div_mul_cancel₀ _ hs]
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hs]
  ring

theorem re_halfPt_gt {w : ℂ} (hw : ‖w‖ < 1) : 1 / 2 < (halfPt w).re := by
  have hw1 : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  have hn : 0 < normSq (1 - w) := normSq_pos.mpr hw1
  have hsq : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [normSq_apply] at this
    nlinarith [norm_nonneg w]
  have key : ((1 + w) / (1 - w)).re = (1 - (w.re ^ 2 + w.im ^ 2)) / normSq (1 - w) := by
    rw [div_re]
    simp only [add_re, one_re, sub_re, add_im, one_im, sub_im]
    field_simp
    ring
  have hpos : 0 < ((1 + w) / (1 - w)).re := by
    rw [key]
    exact div_pos (by linarith) hn
  unfold halfPt
  rw [add_re, show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
  linarith

theorem discPt_sub_discPt {a b : ℂ} (ha : 2 * a + 1 ≠ 0) (hb : 2 * b + 1 ≠ 0) :
    discPt a - discPt b = 8 * (a - b) / ((2 * a + 1) * (2 * b + 1)) := by
  unfold discPt
  rw [div_sub_div _ _ ha hb]
  congr 1
  ring

/-- **The Poisson kernel at a boundary point of the line.**  For `Re s > ½`,
`P(w(s), w(½ + iγ)) = (1 + γ²)(σ − ½)/((σ − ½)² + (t − γ)²)`. -/
theorem poissonKernel_discPt_bdryPt {s : ℂ} (hs : 1 / 2 < s.re) (γ : ℝ) :
    poissonKernel 0 (discPt s) (bdryPt γ) =
      (1 + γ ^ 2) * (s.re - 1 / 2) / ((s.re - 1 / 2) ^ 2 + (s.im - γ) ^ 2) := by
  have hs0 := two_mul_add_one_ne_zero (s := s) (by linarith)
  have hb0 := bdry_two_mul_add_one_ne_zero γ
  have hx : 0 < s.re - 1 / 2 := by linarith
  rw [poissonKernel_def]
  simp only [sub_zero]
  rw [norm_bdryPt, one_pow, one_sub_norm_sq_discPt hs0, bdryPt, discPt_sub_discPt hb0 hs0]
  have hden : ‖(2 * (1 / 2 + γ * I : ℂ) + 1) * (2 * s + 1)‖ ^ 2 =
      4 * (1 + γ ^ 2) * ‖2 * s + 1‖ ^ 2 := by
    have h1 : ‖(2 * (1 / 2 + γ * I : ℂ) + 1)‖ ^ 2 = 4 * (1 + γ ^ 2) := by
      rw [Complex.sq_norm, normSq_apply]
      simp
      ring
    rw [norm_mul, mul_pow, h1]
  have hnum : ‖(8 : ℂ) * ((1 / 2 + γ * I : ℂ) - s)‖ ^ 2 =
      64 * ((s.re - 1 / 2) ^ 2 + (s.im - γ) ^ 2) := by
    rw [norm_mul, mul_pow, Complex.sq_norm ((1 / 2 + γ * I : ℂ) - s), normSq_apply]
    simp
    ring
  rw [norm_div, div_pow, hden, hnum]
  have hN : 0 < ‖2 * s + 1‖ ^ 2 := by
    have : 0 < ‖2 * s + 1‖ := norm_pos_iff.mpr hs0
    positivity
  have hD : 0 < (s.re - 1 / 2) ^ 2 + (s.im - γ) ^ 2 := by positivity
  field_simp
  ring

/-- **The kernel bound along the chart.**  `(σ − ½) P(w(s), ζ) ≤ |2s + 1|²/4` on the circle. -/
theorem mul_poissonKernel_discPt_le {s : ℂ} (hs : 1 / 2 < s.re) (θ : ℝ) :
    (s.re - 1 / 2) * poissonKernel 0 (discPt s) (circleMap 0 1 θ) ≤ ‖2 * s + 1‖ ^ 2 / 4 := by
  have hs0 := two_mul_add_one_ne_zero (s := s) (by linarith)
  have hw := norm_discPt_lt_one hs
  set r := ‖discPt s‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hP := poissonKernel_circleMap_one_le hw θ
  have hkey := one_sub_norm_sq_discPt hs0
  rw [← hr] at hkey hP
  have hx : 0 < s.re - 1 / 2 := by linarith
  have h1r : 0 < 1 - r := by linarith
  have h1r2 : 0 < 1 - r ^ 2 := by nlinarith
  have hN : 0 < ‖2 * s + 1‖ ^ 2 := by
    have : 0 < ‖2 * s + 1‖ := norm_pos_iff.mpr hs0
    positivity
  have hbound : (1 - r ^ 2) / (1 - r) ^ 2 ≤ 4 / (1 - r ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) h1r2]
    nlinarith [mul_pos h1r h1r]
  have hP' : poissonKernel 0 (discPt s) (circleMap 0 1 θ) ≤
      ‖2 * s + 1‖ ^ 2 / (4 * (s.re - 1 / 2)) := by
    refine hP.trans (hbound.trans (le_of_eq ?_))
    rw [hkey]
    field_simp
    ring
  calc (s.re - 1 / 2) * poissonKernel 0 (discPt s) (circleMap 0 1 θ)
      ≤ (s.re - 1 / 2) * (‖2 * s + 1‖ ^ 2 / (4 * (s.re - 1 / 2))) :=
        mul_le_mul_of_nonneg_left hP' hx.le
    _ = ‖2 * s + 1‖ ^ 2 / 4 := by
        rw [mul_div_assoc', mul_comm 4 (s.re - 1 / 2), mul_div_mul_left _ _ hx.ne']

/-! ## The Poisson representation on `Re s > ½` -/

theorem analyticAt_halfPt {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ halfPt w := by
  have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have heq : halfPt = fun z : ℂ => 1 / 2 + (1 + z) / (1 - z) := rfl
  rw [heq]
  exact analyticAt_const.add ((analyticAt_const.add analyticAt_id).div
    (analyticAt_const.sub analyticAt_id) hden)

theorem ne_one_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : w ≠ 1 := by
  rintro rfl
  simp at hw

/-- **The Herglotz representation in the disc chart.**  A holomorphic function with nonnegative
real part on `Re s > ½` has `Re Φ(s) = ∫ P(w(s), e^{iθ}) dν(θ)` for a finite measure `ν`. -/
theorem exists_poissonRepresentation_halfPlane {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hharm : InnerProductSpace.HarmonicOnNhd (fun w => (Φ (halfPt w)).re)
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hΦa : AnalyticAt ℂ Φ (halfPt w) := hΦd.analyticAt (hU.mem_nhds (re_halfPt_gt hw'))
    exact (hΦa.comp (analyticAt_halfPt (ne_one_of_norm_lt_one hw'))).harmonicAt_re
  obtain ⟨ν, hfin, hrep⟩ := exists_poissonRepresentation hharm fun w hw =>
    hΦre _ (re_halfPt_gt (mem_ball_zero_iff.mp hw))
  refine ⟨ν, hfin, fun s hs => ?_⟩
  have hmem : discPt s ∈ Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (norm_discPt_lt_one hs)
  rw [hrep _ hmem, halfPt_discPt (two_mul_add_one_ne_zero (by linarith))]

/-! ## Atoms on the boundary -/

/-- The angles whose circle point is the boundary point of `½ + iγ`. -/
def atomSet (γ : ℝ) : Set ℝ := circleMap 0 1 ⁻¹' {bdryPt γ}

theorem measurableSet_atomSet (γ : ℝ) : MeasurableSet (atomSet γ) :=
  (isClosed_singleton.preimage (continuous_circleMap 0 1)).measurableSet

theorem bdryPt_injective : Function.Injective bdryPt := by
  intro a b h
  have ha := halfPt_discPt (bdry_two_mul_add_one_ne_zero a)
  have hb := halfPt_discPt (bdry_two_mul_add_one_ne_zero b)
  have h' : (1 / 2 + a * I : ℂ) = 1 / 2 + b * I := by
    rw [← ha, ← hb]
    exact congrArg halfPt h
  have := congrArg Complex.im h'
  simpa using this

/-- The point `½ + ε + iγ` on the horizontal ray into `½ + iγ`. -/
def rayPt (γ ε : ℝ) : ℂ := 1 / 2 + ε + γ * I

theorem rayPt_re (γ ε : ℝ) : (rayPt γ ε).re = 1 / 2 + ε := by simp [rayPt]

theorem rayPt_im (γ ε : ℝ) : (rayPt γ ε).im = γ := by simp [rayPt]

theorem norm_two_mul_rayPt_add_one_sq_le {γ ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖2 * rayPt γ ε + 1‖ ^ 2 ≤ 4 * (4 + γ ^ 2) := by
  rw [Complex.sq_norm, normSq_apply]
  simp [rayPt]
  nlinarith

theorem continuous_rayPt (γ : ℝ) : Continuous (rayPt γ) := by
  unfold rayPt
  fun_prop

theorem rayPt_zero (γ : ℝ) : rayPt γ 0 = 1 / 2 + γ * I := by simp [rayPt]

theorem continuousAt_discPt_rayPt (γ : ℝ) : ContinuousAt (fun ε : ℝ => discPt (rayPt γ ε)) 0 := by
  have hne : 2 * rayPt γ 0 + 1 ≠ 0 := by
    rw [rayPt_zero]
    exact bdry_two_mul_add_one_ne_zero γ
  have hc := continuous_rayPt γ
  unfold discPt
  exact ((continuous_const.mul hc).sub continuous_const).continuousAt.div
    ((continuous_const.mul hc).add continuous_const).continuousAt hne

/-- Away from its atom, a boundary point is invisible to `ε P(w(½ + ε + iγ), ·)` as `ε → 0`. -/
theorem tendsto_mul_poissonKernel_rayPt_of_ne {γ : ℝ} {z : ℂ} (hzb : z ≠ bdryPt γ) :
    Tendsto (fun ε : ℝ => ε * poissonKernel 0 (discPt (rayPt γ ε)) z) (𝓝[>] 0) (𝓝 0) := by
  have heq : (fun ε : ℝ => ε * poissonKernel 0 (discPt (rayPt γ ε)) z) = fun ε : ℝ =>
      ε * ((‖z‖ ^ 2 - ‖discPt (rayPt γ ε)‖ ^ 2) / ‖z - discPt (rayPt γ ε)‖ ^ 2) := by
    funext ε
    rw [poissonKernel_def]
    simp only [sub_zero]
  have hw := continuousAt_discPt_rayPt γ
  have hden : ‖z - discPt (rayPt γ 0)‖ ^ 2 ≠ 0 := by
    rw [rayPt_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzb))
  have hcont : ContinuousAt (fun ε : ℝ =>
      ε * ((‖z‖ ^ 2 - ‖discPt (rayPt γ ε)‖ ^ 2) / ‖z - discPt (rayPt γ ε)‖ ^ 2)) 0 :=
    continuousAt_id.mul ((continuousAt_const.sub (hw.norm.pow 2)).div
      ((continuousAt_const.sub hw).norm.pow 2) hden)
  rw [heq]
  have h := hcont.tendsto
  simp only [zero_mul] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Atom extraction along the horizontal ray.**
`ε Re Φ(½ + ε + iγ) → (1 + γ²) ν(atomSet γ)` as `ε → 0⁺`. -/
theorem tendsto_mul_re_rayPt {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re) (γ : ℝ) :
    Tendsto (fun ε : ℝ => ε * (Φ (rayPt γ ε)).re) (𝓝[>] 0)
      (𝓝 ((1 + γ ^ 2) * ν.real (atomSet γ))) := by
  have hre : ∀ ε : ℝ, 0 < ε → 1 / 2 < (rayPt γ ε).re := fun ε hε => by
    rw [rayPt_re]
    linarith
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ θ, ε * poissonKernel 0 (discPt (rayPt γ ε))
      (circleMap 0 1 θ) ∂ν = ε * (Φ (rayPt γ ε)).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_const_mul, hrep _ (hre ε hε)]
  have hval : ∫ θ, (atomSet γ).indicator (fun _ => 1 + γ ^ 2) θ ∂ν =
      (1 + γ ^ 2) * ν.real (atomSet γ) := by
    rw [integral_indicator_const _ (measurableSet_atomSet γ), smul_eq_mul, mul_comm]
  rw [← hval]
  refine Tendsto.congr' heq (tendsto_integral_filter_of_dominated_convergence
    (fun _ => 4 + γ ^ 2) ?_ ?_ (integrable_const _) ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_poissonKernel_circleMap (norm_discPt_lt_one (hre ε hε))).const_mul
      ε).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine ae_of_all _ fun θ => ?_
    have hP0 := poissonKernel_circleMap_one_nonneg (norm_discPt_lt_one (hre ε hε.1)) θ
    have h := mul_poissonKernel_discPt_le (hre ε hε.1) θ
    rw [rayPt_re, show 1 / 2 + ε - 1 / 2 = ε by ring] at h
    have hb := norm_two_mul_rayPt_add_one_sq_le (γ := γ) hε.1.le hε.2.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.1.le hP0)]
    linarith
  · refine ae_of_all _ fun θ => ?_
    by_cases hθ : circleMap 0 1 θ = bdryPt γ
    · have hin : θ ∈ atomSet γ := hθ
      rw [indicator_of_mem hin]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      rw [hθ, poissonKernel_discPt_bdryPt (hre ε hε) γ, rayPt_re, rayPt_im]
      field_simp
      ring
    · have hout : θ ∉ atomSet γ := hθ
      rw [indicator_of_notMem hout]
      exact tendsto_mul_poissonKernel_rayPt_of_ne hθ

/-! ## The residue of `ξ'/ξ` along the ray -/

/-- `ε Re ξ'/ξ(½ + ε + iγ) → ord_{½+iγ} ξ` as `ε → 0⁺`. -/
theorem tendsto_mul_re_logDeriv_xi_rayPt (γ : ℝ) :
    Tendsto (fun ε : ℝ => ε * (logDeriv xi (rayPt γ ε)).re) (𝓝[>] 0)
      (𝓝 (analyticOrderNatAt xi (1 / 2 + γ * I) : ℝ)) := by
  set ρ : ℂ := 1 / 2 + γ * I with hρ
  have hres := RiemannGaussian.AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (xi_differentiable.analyticAt ρ) (xi_orderAt_ne_top ρ)
  have hmap : Tendsto (rayPt γ) (𝓝[>] 0) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (continuous_rayPt γ).tendsto 0
      rw [rayPt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      intro h
      have h' := congrArg Complex.re h
      rw [rayPt_re, hρ] at h'
      simp at h'
      exact (ne_of_gt (show (0 : ℝ) < ε from hε)) h'
  have h := (Complex.continuous_re.tendsto _).comp (hres.comp hmap)
  refine h.congr fun ε => ?_
  simp only [Function.comp, hρ, rayPt]
  rw [show (1 / 2 + (ε : ℂ) + γ * I - (1 / 2 + γ * I)) = (ε : ℂ) by ring, re_ofReal_mul]

/-! ## Bounded rays force full atoms -/

theorem hasDerivAt_log_norm_sq_rayPt {A : ℂ → ℂ} {γ ε : ℝ} (hA : DifferentiableAt ℂ A (rayPt γ ε))
    (hA0 : A (rayPt γ ε) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (‖A (rayPt γ x)‖ ^ 2))
      (2 * (logDeriv A (rayPt γ ε)).re) ε := by
  have hray : HasDerivAt (fun x : ℝ => rayPt γ x) 1 ε := by
    have heq : (fun x : ℝ => rayPt γ x) = fun x : ℝ => (x : ℂ) + (1 / 2 + γ * I) := by
      funext x
      simp only [rayPt]
      ring
    rw [heq]
    simpa using ((hasDerivAt_id ε).ofReal_comp).add_const (1 / 2 + γ * I : ℂ)
  have hg : HasDerivAt (fun x : ℝ => A (rayPt γ x)) (deriv A (rayPt γ ε)) ε := by
    simpa [Function.comp_def] using hA.hasDerivAt.comp ε hray
  have hn := hg.norm_sq
  have hpos : ‖A (rayPt γ ε)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hA0)
  have hlog := hn.log hpos
  convert hlog using 1
  rw [Complex.inner, logDeriv_apply, div_re, Complex.sq_norm]
  simp only [mul_re, conj_re, conj_im]
  field_simp
  ring

/-- **A bounded ray carries the full atom.**  If `A'/A = Φ − ξ'/ξ` along `½ + ε + iγ` and `A` is
bounded there, the atom `(1 + γ²) ν(atomSet γ)` of `Re Φ` is at least the order of `ξ` at
`½ + iγ`. -/
theorem order_le_atom {Φ A : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re) {γ : ℝ}
    (hAd : ∀ ε : ℝ, 0 < ε → DifferentiableAt ℂ A (rayPt γ ε))
    (hA0 : ∀ ε : ℝ, 0 < ε → A (rayPt γ ε) ≠ 0)
    (hlog : ∀ ε : ℝ, 0 < ε →
      logDeriv A (rayPt γ ε) = Φ (rayPt γ ε) - logDeriv xi (rayPt γ ε))
    {C : ℝ} (hC : ∀ ε : ℝ, 0 < ε → ε < 1 → ‖A (rayPt γ ε)‖ ≤ C) :
    (analyticOrderNatAt xi (1 / 2 + γ * I) : ℝ) ≤ (1 + γ ^ 2) * ν.real (atomSet γ) := by
  set m : ℝ := ((analyticOrderNatAt xi (1 / 2 + γ * I) : ℕ) : ℝ) with hm
  set a : ℝ := (1 + γ ^ 2) * ν.real (atomSet γ) with ha
  by_contra hlt
  push Not at hlt
  set c : ℝ := (m - a) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hT := (tendsto_mul_re_rayPt hrep γ).sub (tendsto_mul_re_logDeriv_xi_rayPt γ)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε * (Φ (rayPt γ ε)).re - ε * (logDeriv xi (rayPt γ ε)).re < -c :=
    hT (gt_mem_nhds (by rw [hc]; linarith))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hu0 : 0 < u := hu
  set δ : ℝ := min u 1 with hδ
  have hδ0 : 0 < δ := lt_min hu0 one_pos
  have hδu : δ ≤ u := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set f : ℝ → ℝ := fun x => Real.log (‖A (rayPt γ x)‖ ^ 2) + 2 * c * Real.log x with hf
  have hderiv : ∀ x ∈ Ioo 0 δ,
      HasDerivAt f (2 * (logDeriv A (rayPt γ x)).re + 2 * c * x⁻¹) x := fun x hx =>
    (hasDerivAt_log_norm_sq_rayPt (hAd x hx.1) (hA0 x hx.1)).add
      ((Real.hasDerivAt_log hx.1.ne').const_mul (2 * c))
  have hnonpos : ∀ x ∈ Ioo 0 δ, 2 * (logDeriv A (rayPt γ x)).re + 2 * c * x⁻¹ ≤ 0 := by
    intro x hx
    have hxu : x ∈ Ioo 0 u := ⟨hx.1, hx.2.trans_le hδu⟩
    have h := hsub hxu
    simp only [mem_setOf_eq] at h
    rw [hlog x hx.1, sub_re]
    have hx0 := hx.1
    have : (Φ (rayPt γ x)).re - (logDeriv xi (rayPt γ x)).re < -c / x := by
      rw [lt_div_iff₀ hx0]
      linarith
    have hcx : 2 * c * x⁻¹ = 2 * (c / x) := by ring
    rw [hcx]
    have : -c / x = -(c / x) := by ring
    linarith
  have hanti : AntitoneOn f (Ioo 0 δ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 δ) ?_ ?_ ?_
    · exact HasDerivAt.continuousOn fun x hx => hderiv x hx
    · rw [interior_Ioo]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro x hx
      rw [(hderiv x hx).deriv]
      exact hnonpos x hx
  set x₁ : ℝ := δ / 2 with hx₁
  have hx₁mem : x₁ ∈ Ioo 0 δ := ⟨by positivity, by linarith⟩
  have hApos : 0 < ‖A (rayPt γ x₁)‖ := norm_pos_iff.mpr (hA0 x₁ hx₁mem.1)
  have hCpos : 0 < C := hApos.trans_le (hC x₁ hx₁mem.1 (by linarith))
  set K : ℝ := (2 * Real.log C - f x₁) / (2 * c) with hK
  set x : ℝ := min (x₁ / 2) (Real.exp (-K - 1)) with hxdef
  have hx0 : 0 < x := lt_min (by positivity) (Real.exp_pos _)
  have hxx₁ : x ≤ x₁ := (min_le_left _ _).trans (by linarith)
  have hxmem : x ∈ Ioo 0 δ := ⟨hx0, by linarith [hx₁mem.2]⟩
  have hlogx : Real.log x ≤ -K - 1 := by
    have := Real.log_le_log hx0 (min_le_right (x₁ / 2) (Real.exp (-K - 1)))
    rwa [Real.log_exp] at this
  have hfx : f x₁ ≤ f x := hanti hxmem hx₁mem hxx₁
  have hAx : 0 < ‖A (rayPt γ x)‖ := norm_pos_iff.mpr (hA0 x hxmem.1)
  have hbound : Real.log (‖A (rayPt γ x)‖ ^ 2) ≤ 2 * Real.log C := by
    rw [← Real.log_rpow hCpos, show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Real.log_le_log (by positivity)
      (pow_le_pow_left₀ (norm_nonneg _) (hC x hxmem.1 (by linarith [hxmem.2])) 2)
  have hfx' : f x = Real.log (‖A (rayPt γ x)‖ ^ 2) + 2 * c * Real.log x := rfl
  have hKdef : 2 * c * K = 2 * Real.log C - f x₁ := by
    rw [hK]
    field_simp
  nlinarith

/-! ## The atoms dominate `Re ξ'/ξ` on `Re s > 1` -/

theorem xiDivisorMult_eq (ρ : XiDivisorSupport) :
    xiDivisorMult ρ = analyticOrderNatAt xi (ρ : ℂ) := by
  unfold xiDivisorMult analyticOrderNatAt
  rw [MeromorphicOn.divisor_apply xi_analyticOnNhd_univ.meromorphicOn (Set.mem_univ (ρ : ℂ)),
    (xi_analyticOnNhd_univ (ρ : ℂ) (Set.mem_univ _)).meromorphicOrderAt_eq]
  have hcoe : ((((analyticOrderAt xi (ρ : ℂ)).toNat : ℕ) : ℕ∞)) = analyticOrderAt xi (ρ : ℂ) :=
    ENat.coe_toNat (xi_orderAt_ne_top (ρ : ℂ))
  rw [← hcoe]
  simp

theorem xi_eq_zero_of_divisorSupport (ρ : XiDivisorSupport) : xi (ρ : ℂ) = 0 := by
  have hpos := xiDivisorMult_pos ρ
  rw [xiDivisorMult_eq] at hpos
  by_contra h
  have h0 := ((xi_differentiable.analyticAt (ρ : ℂ)).analyticOrderAt_eq_zero).mpr h
  unfold analyticOrderNatAt at hpos
  rw [h0] at hpos
  simp at hpos

/-- **Weighted atom domination.**  Suppose every zero of `ξ` lies on the line, and let
`0 ≤ w ≤ 1` be a weight on the zeros with `w(ρ)·ord_ρ ξ ≤ (1 + γ²)ν(atomSet γ)` (`γ = Im ρ`).
Then `Σ_q w(q) A_q(σ, t) ≤ Re Φ(σ + it)` on `σ > 1`, where `A_q` are the Poisson terms of the zero
copies. -/
theorem tsum_weighted_copyPoisson_le_re {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hRH : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2) {w : XiDivisorSupport → ℝ}
    (hw0 : ∀ ρ, 0 ≤ w ρ) (hw1 : ∀ ρ, w ρ ≤ 1)
    (hatom : ∀ ρ : XiDivisorSupport,
      w ρ * (xiDivisorMult ρ : ℝ) ≤ (1 + ((ρ : ℂ)).im ^ 2) * ν.real (atomSet ((ρ : ℂ)).im))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ∑' q : XiZeroCopy, w q.1 * copyPoisson σ t q ≤ (Φ ((σ : ℂ) + t * I)).re := by
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs : 1 / 2 < s.re := by rw [hsre]; linarith
  set z := discPt s with hzdef
  have hz : ‖z‖ < 1 := norm_discPt_lt_one hs
  set P : ℝ → ℝ := fun θ => poissonKernel 0 z (circleMap 0 1 θ) with hPdef
  have hP0 : ∀ θ, 0 ≤ P θ := fun θ => poissonKernel_circleMap_one_nonneg hz θ
  have hPint : Integrable P ν := by
    refine (integrable_const ((1 - ‖z‖ ^ 2) / (1 - ‖z‖) ^ 2)).mono'
      (continuous_poissonKernel_circleMap hz).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 θ)]
    exact poissonKernel_circleMap_one_le hz θ
  set x : ℝ := σ - 1 / 2 with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  set A : XiDivisorSupport → ℝ := fun ρ => x / (x ^ 2 + (t - ((ρ : ℂ)).im) ^ 2) with hA
  have hA0 : ∀ ρ, 0 ≤ A ρ := fun ρ => by positivity
  have hcopy : ∀ q : XiZeroCopy, w q.1 * copyPoisson σ t q = w q.1 * A q.1 := by
    intro q
    unfold copyPoisson
    rw [hRH _ (xi_eq_zero_of_divisorSupport q.1)]
  -- the Poisson kernel is constant on an atom set
  have hatomP : ∀ ρ : XiDivisorSupport,
      ∫⁻ θ in atomSet ((ρ : ℂ)).im, ENNReal.ofReal (P θ) ∂ν =
        ν (atomSet ((ρ : ℂ)).im) * ENNReal.ofReal ((1 + ((ρ : ℂ)).im ^ 2) * A ρ) := by
    intro ρ
    rw [setLIntegral_congr_fun (measurableSet_atomSet _)
      (g := fun _ => ENNReal.ofReal ((1 + ((ρ : ℂ)).im ^ 2) * A ρ)), setLIntegral_const,
      mul_comm]
    intro θ hθ
    have hθ' : circleMap 0 1 θ = bdryPt ((ρ : ℂ)).im := hθ
    simp only [hPdef, hθ', hzdef, poissonKernel_discPt_bdryPt hs, hsre, hsim, hA, hx]
    congr 1
    ring
  -- distinct zeros have disjoint atom sets
  have hdisj : Pairwise (Function.onFun Disjoint fun ρ : XiDivisorSupport =>
      atomSet ((ρ : ℂ)).im) := by
    intro ρ ρ' hne
    refine Set.disjoint_left.mpr fun θ h1 h2 => hne ?_
    have h1' : circleMap 0 1 θ = bdryPt ((ρ : ℂ)).im := h1
    have h2' : circleMap 0 1 θ = bdryPt ((ρ' : ℂ)).im := h2
    have him := bdryPt_injective (h1'.symm.trans h2')
    have hre : ((ρ : ℂ)).re = ((ρ' : ℂ)).re := by
      rw [hRH _ (xi_eq_zero_of_divisorSupport ρ), hRH _ (xi_eq_zero_of_divisorSupport ρ')]
    exact Subtype.ext (Complex.ext hre him)
  -- assemble in `ℝ≥0∞`
  have hcpos : ∀ q : XiZeroCopy, 0 ≤ w q.1 * copyPoisson σ t q := fun q =>
    mul_nonneg (hw0 q.1) (copyPoisson_pos hσ.le t q).le
  have hsumm : Summable fun q : XiZeroCopy => w q.1 * copyPoisson σ t q :=
    (summable_copyPoisson hσ t).of_nonneg_of_le hcpos fun q => by
      have := mul_le_mul_of_nonneg_right (hw1 q.1) (copyPoisson_pos hσ.le t q).le
      linarith
  have hkey : ENNReal.ofReal (∑' q : XiZeroCopy, w q.1 * copyPoisson σ t q) ≤
      ENNReal.ofReal ((Φ s).re) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hcpos hsumm, ENNReal.tsum_sigma', ← hrep s hs,
      ofReal_integral_eq_lintegral_ofReal hPint (ae_of_all _ hP0)]
    calc ∑' (ρ : XiDivisorSupport) (i : Fin (Int.toNat
            ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)))),
            ENNReal.ofReal (w ρ * copyPoisson σ t ⟨ρ, i⟩)
        = ∑' ρ : XiDivisorSupport, (xiDivisorMult ρ : ℝ≥0∞) * ENNReal.ofReal (w ρ * A ρ) := by
          refine tsum_congr fun ρ => ?_
          rw [tsum_fintype]
          simp only [fun i => hcopy ⟨ρ, i⟩]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rfl
      _ ≤ ∑' ρ : XiDivisorSupport,
            ν (atomSet ((ρ : ℂ)).im) * ENNReal.ofReal ((1 + ((ρ : ℂ)).im ^ 2) * A ρ) := by
          refine ENNReal.tsum_le_tsum fun ρ => ?_
          have hfin : ν (atomSet ((ρ : ℂ)).im) = ENNReal.ofReal (ν.real (atomSet ((ρ : ℂ)).im)) :=
            (ENNReal.ofReal_toReal (measure_ne_top ν _)).symm
          rw [hfin, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul measureReal_nonneg]
          refine ENNReal.ofReal_le_ofReal ?_
          have h := mul_le_mul_of_nonneg_right (hatom ρ) (hA0 ρ)
          linarith
      _ = ∑' ρ : XiDivisorSupport, ∫⁻ θ in atomSet ((ρ : ℂ)).im, ENNReal.ofReal (P θ) ∂ν :=
          tsum_congr fun ρ => (hatomP ρ).symm
      _ = ∫⁻ θ in ⋃ ρ : XiDivisorSupport, atomSet ((ρ : ℂ)).im, ENNReal.ofReal (P θ) ∂ν :=
          (lintegral_iUnion (fun ρ => measurableSet_atomSet _) hdisj _).symm
      _ ≤ ∫⁻ θ, ENNReal.ofReal (P θ) ∂ν := setLIntegral_le_lintegral _ _
  exact (ENNReal.ofReal_le_ofReal_iff (hΦre s hs)).mp hkey

/-- **Atom domination.**  If every zero of `ξ` lies on the line and every atom of `Re Φ` is at least
the multiplicity of its zero, then `Re ξ'/ξ ≤ Re Φ` on `Re s > 1`. -/
theorem re_logDeriv_xi_le_re {Φ : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hRH : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2)
    (hatom : ∀ ρ : XiDivisorSupport,
      (xiDivisorMult ρ : ℝ) ≤ (1 + ((ρ : ℂ)).im ^ 2) * ν.real (atomSet ((ρ : ℂ)).im))
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (logDeriv xi ((σ : ℂ) + t * I)).re ≤ (Φ ((σ : ℂ) + t * I)).re := by
  have h := tsum_weighted_copyPoisson_le_re hrep hΦre hRH (w := fun _ => 1) (fun _ => zero_le_one)
    (fun _ => le_rfl) (fun ρ => by rw [one_mul]; exact hatom ρ) hσ t
  simp only [one_mul] at h
  rwa [re_logDeriv_xi_eq_tsum_copyPoisson hσ t]

/-! ## The Dirichlet side -/

theorem summable_term_lamTwo {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 1 < s.re) : Summable fun n => LSeries.term (lamTwo lam) s n := by
  refine Summable.of_norm_bounded (hsl s.re hs) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h
  · positivity
  · unfold lamTwo
    split_ifs with h2
    · rw [Complex.norm_real, Real.norm_eq_abs]
    · simp only [norm_zero, zero_div]
      positivity

theorem summable_abs_deviationCoeff_of_summable {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n => |deviationCoeff lam σ n| := by
  have h2 : Summable fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ σ := by
    have := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
    refine (LSeriesSummable_iff_of_re_eq_re (s' := (σ : ℂ)) rfl).mp this |>.norm |>.congr ?_
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · subst h; simp
    · simp
  refine (((hsl σ hσ).add h2)).of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_
  unfold deviationCoeff
  split_ifs with hn
  · have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _), Real.rpow_neg hpos.le, ← div_eq_mul_inv]
    have := abs_sub (ArithmeticFunction.vonMangoldt n : ℝ) (lam n)
    have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hpos _
    rw [← add_div, div_le_div_iff_of_pos_right hp]
    linarith
  · simp only [abs_zero]
    positivity

/-- On `Re s > 1`, `Re Φ − Re ξ'/ξ` is the cosine series of the deviation. -/
theorem re_sub_re_logDeriv_xi_eq {lam : ℕ → ℝ} {Φ : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (Φ ((σ : ℂ) + t * I)).re - (logDeriv xi ((σ : ℂ) + t * I)).re =
      logCosSeries (deviationCoeff lam σ) t := by
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hs : 1 < s.re := by simpa [hsdef] using hσ
  rw [logDeriv_xi_eq_datum hs, hid s hs]
  have hL1 := summable_term_lamTwo hsl hs
  have hL2 : Summable fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hdiff : (zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s) -
      (zetaArchimedeanDatum s + 1 / (s - 1) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) =
      ∑' n, (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n -
        LSeries.term (lamTwo lam) s n) := by
    rw [LSeries, LSeries, hL2.tsum_sub hL1]
    ring
  rw [← Complex.sub_re, hdiff, Complex.re_tsum (hL2.sub hL1), logCosSeries]
  refine tsum_congr fun n => ?_
  rw [Complex.sub_re, LSeries.term_def, LSeries.term_def]
  unfold deviationCoeff lamTwo
  by_cases hn : 2 ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [if_neg hn0, if_neg hn0, if_pos hn, if_pos hn]
    have hcpow : ((n : ℂ) ^ s)⁻¹ = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        cexp (-(((t * Real.log n : ℝ) : ℂ) * I)) := by
      have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log hpos.le]
      rw [← Complex.cpow_neg, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0), hlog,
        Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      rw [hsdef]
      push_cast
      ring
    rw [div_eq_mul_inv, div_eq_mul_inv, hcpow]
    have hre : ∀ c : ℝ, (((c : ℝ) : ℂ) * ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        cexp (-(((t * Real.log n : ℝ) : ℂ) * I)))).re =
        c * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
      intro c
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
        show -(((t * Real.log n : ℝ) : ℂ) * I) = ((-(t * Real.log n) : ℝ) : ℂ) * I by
          push_cast; ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    rw [show ((ArithmeticFunction.vonMangoldt n : ℂ)) =
      (((ArithmeticFunction.vonMangoldt n : ℝ)) : ℂ) from rfl, hre, hre]
    ring
  · rw [if_neg hn]
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · have : n = 0 := by omega
      subst this
      simp
    · have : n = 1 := by omega
      subst this
      simp

/-! ## The quotient -/

/-- **The quotient facts.**  If `G = s(s−1)Γ_ℝ(s)ζ(s)A(s)` on `Re s > ½` (`s ≠ 1`) for a Herglotz
producer `G` and a holomorphic `A`, then every zero of `ξ` lies on the line, `A` has no zero on
`Re s > ½` (`s ≠ 1`), and `A'/A = Φ − ξ'/ξ` there. -/
theorem quotient_facts {lam : ℕ → ℝ} {Φ G A : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s)) :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2) ∧ (∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → A s ≠ 0) ∧
      ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → logDeriv A s = Φ s - logDeriv xi s := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGne : ∀ s : ℂ, 1 / 2 < s.re → G s ≠ 0 := fun s hs =>
    PhaseLockRigidity.G_ne_zero hΦd hGd hG2 hs
  -- `G = 2ξA`
  have hGxi : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → G s = 2 * xi s * A s := by
    intro s hs hs1
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [hGK s hs hs1, xi_eq_half_mul hs0 hs1, riemannZeta_def_of_ne_zero hs0]
    field_simp
  have hxiH : ∀ s : ℂ, 1 / 2 < s.re → xi s ≠ 0 := by
    intro s hs h
    by_cases hs1 : s = 1
    · rw [hs1, xi_one] at h
      norm_num at h
    · exact hGne s hs (by rw [hGxi s hs hs1, h]; ring)
  have hA0 : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → A s ≠ 0 := fun s hs hs1 h =>
    hGne s hs (by rw [hGxi s hs hs1, h, mul_zero])
  refine ⟨fun ρ hρ => ?_, hA0, fun s hs hs1 => ?_⟩
  · rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
    · exact absurd (by rw [xi_one_sub]; exact hρ) (hxiH (1 - ρ) (by simp; linarith))
    · exact h
    · exact absurd hρ (hxiH ρ h)
  · have hev : G =ᶠ[𝓝 s] fun z => 2 * xi z * A z := by
      filter_upwards [inter_mem (hU.mem_nhds hs) (isOpen_ne.mem_nhds hs1)] with z hz
      exact hGxi z hz.1 hz.2
    have hAd' : DifferentiableAt ℂ A s := hAd.differentiableAt (hU.mem_nhds hs)
    have hlogG : logDeriv G s = Φ s := by
      rw [logDeriv_apply, (hGd s hs).deriv, mul_div_assoc, div_self (hGne s hs), mul_one]
    have hprod : logDeriv (fun z => 2 * xi z * A z) s = logDeriv xi s + logDeriv A s := by
      have h1 : (fun z => 2 * xi z * A z) = fun z => 2 * (xi z * A z) := by
        funext z
        ring
      rw [h1, logDeriv_const_mul s (2 : ℂ) two_ne_zero,
        logDeriv_mul s (hxiH s hs) (hA0 s hs hs1) (xi_differentiable s) hAd']
    have hcongr : logDeriv G s = logDeriv (fun z => 2 * xi z * A z) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [hlogG, hprod] at hcongr
    linear_combination -hcongr

/-- **A bounded ray at a zero carries its full atom** (quotient form of `order_le_atom`). -/
theorem atom_of_rayBounded {Φ A : ℂ → ℂ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hrep : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ θ, poissonKernel 0 (discPt s) (circleMap 0 1 θ) ∂ν = (Φ s).re)
    (hRHxi : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hA0 : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → A s ≠ 0)
    (hlogA : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → logDeriv A s = Φ s - logDeriv xi s)
    (ρ : XiDivisorSupport)
    (hray : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ‖A (1 / 2 + ε + ((ρ : ℂ)).im * I)‖ ≤ C) :
    (xiDivisorMult ρ : ℝ) ≤ (1 + ((ρ : ℂ)).im ^ 2) * ν.real (atomSet ((ρ : ℂ)).im) := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  set γ : ℝ := ((ρ : ℂ)).im with hγdef
  have hxiρ := xi_eq_zero_of_divisorSupport ρ
  have hρeq : (ρ : ℂ) = 1 / 2 + γ * I :=
    Complex.ext (by simp [hRHxi _ hxiρ]) (by simp [hγdef])
  have hzero : xi (1 / 2 + γ * I) = 0 := hρeq ▸ hxiρ
  have hγ : γ ≠ 0 := by
    intro h
    exact xi_ne_zero_of_abs_im_le_four (rho := 1 / 2 + γ * I) (by simp [h]) hzero
  obtain ⟨C, hC⟩ := hray
  have hre : ∀ ε : ℝ, 0 < ε → 1 / 2 < (rayPt γ ε).re := fun ε hε => by
    rw [rayPt_re]
    linarith
  have hne : ∀ ε : ℝ, rayPt γ ε ≠ 1 := fun ε h => hγ (by
    have := congrArg Complex.im h
    rwa [rayPt_im, Complex.one_im] at this)
  have hle := order_le_atom hrep (γ := γ)
    (fun ε hε => hAd.differentiableAt (hU.mem_nhds (hre ε hε)))
    (fun ε hε => hA0 _ (hre ε hε) (hne ε)) (fun ε hε => hlogA _ (hre ε hε) (hne ε)) hC
  rw [xiDivisorMult_eq, hρeq]
  exact hle

/-! ## The theorem -/

/-- **A Herglotz producer whose quotient by `ξ` is bounded on the rays into the zeros is `Λ`.**
Let `Re Φ ≥ 0` on `Re s > ½`, `Φ = Γ̃ + 1/(s − 1) − Σ_{n≥2} lam(n)n^{−s}` on `Re s > 1`,
`G' = ΦG`, and `G = s(s−1)Γ_ℝ(s)ζ(s)A(s)` on `Re s > ½` (`s ≠ 1`) with `A` holomorphic there.
If `A` is bounded on `½ + ε + iγ`, `0 < ε < 1`, at every zero `½ + iγ` of `ξ`, then
`lam(n) = Λ(n)` for `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem eq_vonMangoldt_of_quotient_rayBounded {lam : ℕ → ℝ} {Φ G A : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s))
    (hray : ∀ γ : ℝ, xi (1 / 2 + γ * I) = 0 →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ‖A (1 / 2 + ε + γ * I)‖ ≤ C) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  obtain ⟨hRHxi, hA0, hlogA⟩ := quotient_facts hΦd hGd hG2 hAd hGK
  obtain ⟨ν, hfin, hrep⟩ := exists_poissonRepresentation_halfPlane hΦd hΦre
  have hatom : ∀ ρ : XiDivisorSupport,
      (xiDivisorMult ρ : ℝ) ≤ (1 + ((ρ : ℂ)).im ^ 2) * ν.real (atomSet ((ρ : ℂ)).im) := by
    intro ρ
    refine atom_of_rayBounded hrep hRHxi hAd hA0 hlogA ρ (hray _ ?_)
    have hxiρ := xi_eq_zero_of_divisorSupport ρ
    have hρeq : (ρ : ℂ) = 1 / 2 + ((ρ : ℂ)).im * I :=
      Complex.ext (by simp [hRHxi _ hxiρ]) (by simp)
    rwa [← hρeq]
  -- the cosine series of the deviation is nonnegative, so it vanishes
  have hcoeff : ∀ m : ℕ, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
    intro m hm
    have h := abs_le_four_mul_of_logCosSeries_envelope
      (summable_abs_deviationCoeff_of_summable hsl (σ := 2) (by norm_num))
      (by simp [deviationCoeff]) (by simp [deviationCoeff]) (ε := fun _ => 0)
      (fun _ => le_rfl) (fun _ => intervalIntegrable_const) (E := 0) (by simp)
      (fun t _ => by
        rw [← re_sub_re_logDeriv_xi_eq hsl hid (by norm_num) t]
        have := re_logDeriv_xi_le_re hrep hΦre hRHxi hatom (σ := 2) (by norm_num) t
        push_cast at this ⊢
        linarith) hm
    rw [abs_deviationCoeff hm, mul_zero] at h
    have hpos : (0 : ℝ) < (m : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < m)) _
    have h0 : |lam m - ArithmeticFunction.vonMangoldt m| = 0 := by
      have := mul_nonneg (abs_nonneg (lam m - ArithmeticFunction.vonMangoldt m)) hpos.le
      nlinarith
    rw [abs_eq_zero, sub_eq_zero] at h0
    exact h0
  exact ⟨hcoeff, riemannHypothesis_iff_xi_zero_re_eq_half.mpr hRHxi⟩

/-- **A Herglotz producer whose quotient by `ξ` is continuous up to the line is `Λ`.**  This needs
no reflection identity and no growth bound on the quotient. -/
theorem eq_vonMangoldt_of_quotient_continuousOn {lam : ℕ → ℝ} {Φ G A : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re})
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  refine eq_vonMangoldt_of_quotient_rayBounded hsl hΦd hΦre hid hGd hG2 hAd hGK fun γ _ => ?_
  have hK : IsCompact (rayPt γ '' Icc 0 1) := isCompact_Icc.image (continuous_rayPt γ)
  have hsub : rayPt γ '' Icc 0 1 ⊆ {s : ℂ | 1 / 2 ≤ s.re} := by
    rintro _ ⟨ε, hε, rfl⟩
    show 1 / 2 ≤ (rayPt γ ε).re
    rw [rayPt_re]
    linarith [hε.1]
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (hAc.mono hsub)).isBounded.exists_norm_le
  exact ⟨C, fun ε hε0 hε1 => hC _ ⟨rayPt γ ε, ⟨ε, ⟨hε0.le, hε1.le⟩, rfl⟩, rfl⟩⟩

end RHTower.AtomDomination
