import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheModularMapIsPositionRigid

/-!
# One cavity function sees every resonance that a pair of cavity modes sees

The cusp-energy receiver of `BlackHoleRingdown` reads a resonance `ρ/2` only if the completed
Rankin–Selberg function of the cusp form does not vanish there. B109 asks for **one** cavity function
whose energy sees **every** off-line resonance. This module reduces that `∃ g ∀ ρ` statement to the pointwise
`∀ ρ ∃ (j, k)` statement about pairs of cavity modes, and shows the reduction is an equivalence.

**Setting.** A *cavity family* is a sequence of continuous `SL₂(ℤ)`-invariant functions `u_j` under a common
envelope `‖u_j(z)‖ ≤ e^{−κ Im z}` (`IsCavityFamily`); every sequence of Maass cusp forms becomes one after
normalization (`cuspFamily`). For bounded coefficients `x ∈ ℕ →ᵇ ℂ` the **cavity function**
`g_x = Σ_j x_j 2^{−j} u_j` is a seed (`isSeed_cavity`). At a point `s ∉ {0, ½, 1}` put

  `B_s(x, x') = ∫_𝒟 g_x · conj(g_{x'}) · E*(s − ½)`,  `Q_s(x) = B_s(x, x) = Λ_{|g_x|²}(s)`,

and the **pair entries** `b_{jk}(s) = ∫_𝒟 u_j conj(u_k) E*(s − ½)`.

**Theorems.**
* `exists_cavity_seeing` (Baire): if `S` is countable and every `s ∈ S` has a pair with `b_{jk}(s) ≠ 0`, the
  coefficients `x` with `Q_s(x) ≠ 0` for all `s ∈ S` form a dense set; in particular one cavity function sees
  all of `S`.
* `quad_eq_zero_of_pairEntry_eq_zero` (converse): if every pair entry vanishes at `s`, every cavity function is
  blind at `s`.
* `cavity_sees_every_right_zero_iff`: for the right zeros of `ζ`, one cavity function sees every resonance
  `ρ/2` iff every such resonance is seen by some pair of cavity modes.
* `re_le_of_cavity_rate` (complete receiver): for that cavity function a horocycle rate `y^α` of its energy
  forces `Re ρ ≤ 2 − 2α` for every zero `ρ` with `Re ρ > ½`.

**Proof.** `B_s` is sesquilinear and bounded, `|B_s(x, x')| ≤ K ‖x‖ ‖x'‖`, so `Q_s` is continuous and its zero set
is closed. If `Q_s` vanished on a ball around `x₀`, then `Q_s(x₀ ± t h) = Q_s(x₀) ± t·(B(x₀,h) + B(h,x₀)) + t² Q_s(h)`
forces `Q_s(h) = 0` for every `h`, and polarization
`4B(x, y) = Q(x+y) − Q(x−y) + i Q(x+iy) − i Q(x−iy)` kills every pair entry. So each zero set is nowhere dense,
and Baire's theorem in the complete space `ℕ →ᵇ ℂ` gives the dense intersection. For the converse, truncations
of `x` change `g_x` by at most `2^{1−N} ‖x‖ e^{−κ Im z}`, and on truncations `B_s` is a finite combination of pair
entries.
-/

open Complex MeasureTheory Set Filter Topology BoundedContinuousFunction
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open UpperHalfPlane (ofComplex)

/-! ### The pairing with the completed Eisenstein function -/

/-- The integrand `g · conj h · E*(s − ½)` on `𝒟`. -/
def pairIntegrand (s : ℂ) (g h : ℍ → ℂ) (z : ℍ) : ℂ :=
  g z * starRingEnd ℂ (h z) * EisAuto.completedEisenstein (s - 1 / 2) z.re z.im

/-- The pairing `∫_𝒟 g · conj h · E*(s − ½)`. -/
def pairing (s : ℂ) (g h : ℍ → ℂ) : ℂ := ∫ z in ModularGroup.fd, pairIntegrand s g h z

theorem volume_real_fd : (volume : Measure ℍ).real ModularGroup.fd = Real.pi / 3 := by
  rw [measureReal_def, volume_fd_eq, ENNReal.toReal_ofReal (by positivity)]

/-- **The pairing is bounded by the envelopes.** For `s ∉ {0, ½, 1}` and `κ > 0` there is `K` with
`|∫_𝒟 g conj h E*| ≤ K A A'` whenever `‖g‖ ≤ A e^{−κ Im}` and `‖h‖ ≤ A' e^{−κ Im}`. -/
theorem exists_pairing_bound {κ : ℝ} (hκ : 0 < κ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g h : ℍ → ℂ) (A A' : ℝ), Continuous g → Continuous h →
      (∀ z, ‖g z‖ ≤ A * Real.exp (-κ * z.im)) → (∀ z, ‖h z‖ ≤ A' * Real.exp (-κ * z.im)) →
      IntegrableOn (pairIntegrand s g h) ModularGroup.fd ∧ ‖pairing s g h‖ ≤ K * (A * A') := by
  have hKU : ∀ u ∈ ({s - 1 / 2} : Set ℂ), u ≠ 1 / 2 ∧ u ≠ 0 ∧ u ≠ -(1 / 2) := by
    rintro u rfl
    exact ⟨fun h => h2 (by linear_combination h), fun h => h1 (by linear_combination h),
      fun h => h0 (by linear_combination h)⟩
  obtain ⟨α, β, a, hα, hβ, ha, hb⟩ := CuspRSC.exists_completed_bound isCompact_singleton hKU
  obtain ⟨Kc, hKc0, hKc⟩ := exists_rpow_mul_exp_le ha (by positivity : (0 : ℝ) < 2 * κ)
  set C₀ := α * Kc + β
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨C₀ * (Real.pi / 3), by positivity, fun g h A A' hg hh hgA hhA => ?_⟩
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hgA UpperHalfPlane.I)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hA' : 0 ≤ A' := by
    have := (norm_nonneg _).trans (hhA UpperHalfPlane.I)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hfd : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  have hbound : ∀ z ∈ ModularGroup.fd, ‖pairIntegrand s g h z‖ ≤ A * A' * C₀ := by
    intro z hz
    have hy := z.im_pos
    have hE := hb (s - 1 / 2) rfl z.re z.im (CuspRSC.half_lt_im_of_mem_fd hz).le
    rw [pairIntegrand, norm_mul, norm_mul, Complex.norm_conj]
    have e2 : Real.exp (-κ * z.im) * Real.exp (-κ * z.im) = Real.exp (-(2 * κ) * z.im) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖g z‖ * ‖h z‖ * ‖EisAuto.completedEisenstein (s - 1 / 2) z.re z.im‖
        ≤ A * Real.exp (-κ * z.im) * (A' * Real.exp (-κ * z.im)) * (α * z.im ^ a + β) :=
          mul_le_mul (mul_le_mul (hgA z) (hhA z) (norm_nonneg _) (by positivity)) hE (norm_nonneg _)
            (by positivity)
      _ = A * A' * (α * (z.im ^ a * Real.exp (-(2 * κ) * z.im)) + β * Real.exp (-(2 * κ) * z.im)) := by
          rw [← e2]; ring
      _ ≤ A * A' * (α * Kc + β * 1) := by
          gcongr
          · exact hKc _ hy
          · exact Real.exp_le_one_iff.2 (by nlinarith)
      _ = A * A' * C₀ := by ring
  have hmeas : AEStronglyMeasurable (pairIntegrand s g h) (volume.restrict ModularGroup.fd) := by
    have hc : Continuous fun w : ℍ => g w * starRingEnd ℂ (h w) *
        EisAuto.completedEisenstein (s - 1 / 2) w.re (max w.im (1 / 2)) :=
      (hg.mul (Complex.continuous_conj.comp hh)).mul (CuspRSC.continuous_completed_max _)
    refine hc.aestronglyMeasurable.congr ((ae_restrict_iff' hfd).2 (Eventually.of_forall fun z hz => ?_))
    simp only [pairIntegrand, max_eq_left (CuspRSC.half_lt_im_of_mem_fd hz).le]
  have hvol : volume ModularGroup.fd < ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict ModularGroup.fd) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol⟩
  refine ⟨(integrable_const (A * A' * C₀)).mono' hmeas
    ((ae_restrict_iff' hfd).2 (Eventually.of_forall hbound)), ?_⟩
  have := norm_setIntegral_le_of_norm_le_const hvol hbound
  rw [volume_real_fd] at this
  calc ‖pairing s g h‖ ≤ A * A' * C₀ * (Real.pi / 3) := this
    _ = C₀ * (Real.pi / 3) * (A * A') := by ring

/-! ### Cavity families and cavity functions -/

/-- A **cavity family**: continuous invariant functions under one envelope `‖u_j(z)‖ ≤ e^{−κ Im z}`. -/
structure IsCavityFamily (u : ℕ → ℍ → ℂ) (κ : ℝ) : Prop where
  pos : 0 < κ
  invariant : ∀ j (γ : SL(2, ℤ)) (z : ℍ), u j (γ • z) = u j z
  continuous : ∀ j, Continuous (u j)
  envelope : ∀ j z, ‖u j z‖ ≤ Real.exp (-κ * z.im)

variable {u : ℕ → ℍ → ℂ} {κ : ℝ}

/-- The weight `2^{−j}`. -/
def wt (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ j

theorem wt_pos (j : ℕ) : 0 < wt j := by unfold wt; positivity

/-- The **cavity function** `g_x = Σ_j x_j 2^{−j} u_j`. -/
def cavity (u : ℕ → ℍ → ℂ) (x : ℕ →ᵇ ℂ) (z : ℍ) : ℂ := ∑' j, x j * (wt j : ℂ) * u j z

theorem norm_cavityTerm_le (hu : IsCavityFamily u κ) (x : ℕ →ᵇ ℂ) (j : ℕ) (z : ℍ) :
    ‖x j * (wt j : ℂ) * u j z‖ ≤ ‖x‖ * Real.exp (-κ * z.im) * wt j := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wt_pos j).le]
  calc ‖x j‖ * wt j * ‖u j z‖ ≤ ‖x‖ * wt j * Real.exp (-κ * z.im) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (x.norm_coe_le_norm j) (wt_pos j).le) (hu.envelope j z)
          (norm_nonneg _) (by have := wt_pos j; positivity)
    _ = ‖x‖ * Real.exp (-κ * z.im) * wt j := by ring

theorem summable_wt : Summable wt := summable_geometric_two

theorem tsum_wt : ∑' j, wt j = 2 := tsum_geometric_two

theorem summable_cavityTerm (hu : IsCavityFamily u κ) (x : ℕ →ᵇ ℂ) (z : ℍ) :
    Summable fun j => x j * (wt j : ℂ) * u j z :=
  Summable.of_norm_bounded (summable_wt.mul_left (‖x‖ * Real.exp (-κ * z.im)))
    (norm_cavityTerm_le hu x · z)

/-- `‖g_x(z)‖ ≤ 2 ‖x‖ e^{−κ Im z}`. -/
theorem norm_cavity_le (hu : IsCavityFamily u κ) (x : ℕ →ᵇ ℂ) (z : ℍ) :
    ‖cavity u x z‖ ≤ 2 * ‖x‖ * Real.exp (-κ * z.im) := by
  have hs := summable_wt.mul_left (‖x‖ * Real.exp (-κ * z.im))
  calc ‖cavity u x z‖ ≤ ∑' j, ‖x‖ * Real.exp (-κ * z.im) * wt j :=
        tsum_of_norm_bounded hs.hasSum (norm_cavityTerm_le hu x · z)
    _ = ‖x‖ * Real.exp (-κ * z.im) * 2 := by rw [tsum_mul_left, tsum_wt]
    _ = 2 * ‖x‖ * Real.exp (-κ * z.im) := by ring

theorem continuous_cavity (hu : IsCavityFamily u κ) (x : ℕ →ᵇ ℂ) : Continuous (cavity u x) := by
  refine continuous_tsum (fun j => continuous_const.mul (hu.continuous j)) (summable_wt.mul_left ‖x‖)
    fun j z => ?_
  refine (norm_cavityTerm_le hu x j z).trans ?_
  have h1 : Real.exp (-κ * z.im) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hu.pos, z.im_pos])
  have := wt_pos j
  calc ‖x‖ * Real.exp (-κ * z.im) * wt j ≤ ‖x‖ * 1 * wt j := by gcongr
    _ = ‖x‖ * wt j := by ring

/-- **Every cavity function is a seed.** -/
theorem isSeed_cavity (hu : IsCavityFamily u κ) (x : ℕ →ᵇ ℂ) : IsSeed (cavity u x) := by
  refine ⟨fun γ z => ?_, continuous_cavity hu x, ⟨2 * ‖x‖, fun z => ?_⟩,
    ⟨2 * ‖x‖, κ, by positivity, hu.pos, fun z _ => norm_cavity_le hu x z⟩⟩
  · simp only [cavity, hu.invariant]
  · refine (norm_cavity_le hu x z).trans ?_
    have h1 : Real.exp (-κ * z.im) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hu.pos, z.im_pos])
    calc 2 * ‖x‖ * Real.exp (-κ * z.im) ≤ 2 * ‖x‖ * 1 := by gcongr
      _ = 2 * ‖x‖ := mul_one _

theorem cavity_add (hu : IsCavityFamily u κ) (x x' : ℕ →ᵇ ℂ) :
    cavity u (x + x') = fun z => cavity u x z + cavity u x' z := by
  funext z
  simp only [cavity, BoundedContinuousFunction.coe_add, Pi.add_apply, add_mul]
  exact (summable_cavityTerm hu x z).tsum_add (summable_cavityTerm hu x' z)

theorem cavity_smul (x : ℕ →ᵇ ℂ) (c : ℂ) :
    cavity u (c • x) = fun z => c * cavity u x z := by
  funext z
  simp only [cavity, BoundedContinuousFunction.coe_smul, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- The coefficient vector `e_j`. -/
def single (j : ℕ) : ℕ →ᵇ ℂ :=
  ofNormedAddCommGroupDiscrete (fun i => if i = j then (1 : ℂ) else 0) 1 fun i => by
    split_ifs <;> simp

theorem cavity_single (j : ℕ) : cavity u (single j) = fun z => (wt j : ℂ) * u j z := by
  funext z
  rw [cavity, tsum_eq_single j fun i hi => by simp [single, hi]]
  simp [single]

/-! ### The pair form -/

/-- The pair form `B_s(x, x') = ∫_𝒟 g_x conj(g_{x'}) E*(s − ½)`. -/
def pairForm (u : ℕ → ℍ → ℂ) (s : ℂ) (x x' : ℕ →ᵇ ℂ) : ℂ := pairing s (cavity u x) (cavity u x')

/-- The pair entries `b_{jk}(s) = ∫_𝒟 u_j conj(u_k) E*(s − ½)`. -/
def pairEntry (u : ℕ → ℍ → ℂ) (s : ℂ) (j k : ℕ) : ℂ := pairing s (u j) (u k)

/-- The diagonal of the pair form is the completed transform of the energy `|g_x|²`. -/
theorem pairForm_self (x : ℕ →ᵇ ℂ) (s : ℂ) :
    pairForm u s x x = seedTransform (fun z => ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ)) s := by
  unfold pairForm pairing seedTransform pairIntegrand
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

variable {s : ℂ}

section Pair

variable (hu : IsCavityFamily u κ) (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1)
include hu h0 h1 h2

theorem integrableOn_pair (x x' : ℕ →ᵇ ℂ) :
    IntegrableOn (pairIntegrand s (cavity u x) (cavity u x')) ModularGroup.fd := by
  obtain ⟨K, -, hK⟩ := exists_pairing_bound hu.pos h0 h1 h2
  exact (hK _ _ _ _ (continuous_cavity hu x) (continuous_cavity hu x') (norm_cavity_le hu x)
    (norm_cavity_le hu x')).1

theorem exists_pairForm_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x x' : ℕ →ᵇ ℂ, ‖pairForm u s x x'‖ ≤ K * (‖x‖ * ‖x'‖) := by
  obtain ⟨K, hK0, hK⟩ := exists_pairing_bound hu.pos h0 h1 h2
  refine ⟨4 * K, by positivity, fun x x' => ?_⟩
  have := (hK _ _ _ _ (continuous_cavity hu x) (continuous_cavity hu x') (norm_cavity_le hu x)
    (norm_cavity_le hu x')).2
  calc ‖pairForm u s x x'‖ ≤ K * (2 * ‖x‖ * (2 * ‖x'‖)) := this
    _ = 4 * K * (‖x‖ * ‖x'‖) := by ring

theorem pairForm_add_left (x₁ x₂ x' : ℕ →ᵇ ℂ) :
    pairForm u s (x₁ + x₂) x' = pairForm u s x₁ x' + pairForm u s x₂ x' := by
  unfold pairForm pairing
  rw [← integral_add (integrableOn_pair hu h0 h1 h2 x₁ x') (integrableOn_pair hu h0 h1 h2 x₂ x')]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, cavity_add hu]
  ring

theorem pairForm_add_right (x x₁ x₂ : ℕ →ᵇ ℂ) :
    pairForm u s x (x₁ + x₂) = pairForm u s x x₁ + pairForm u s x x₂ := by
  unfold pairForm pairing
  rw [← integral_add (integrableOn_pair hu h0 h1 h2 x x₁) (integrableOn_pair hu h0 h1 h2 x x₂)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, cavity_add hu, map_add]
  ring

omit hu h0 h1 h2 in
theorem pairForm_smul_left (x x' : ℕ →ᵇ ℂ) (c : ℂ) :
    pairForm u s (c • x) x' = c * pairForm u s x x' := by
  unfold pairForm pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, cavity_smul]
  ring

omit hu h0 h1 h2 in
theorem pairForm_smul_right (x x' : ℕ →ᵇ ℂ) (c : ℂ) :
    pairForm u s x (c • x') = starRingEnd ℂ c * pairForm u s x x' := by
  unfold pairForm pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, cavity_smul, map_mul]
  ring

/-- `Q(x + c y) = Q(x) + conj(c) B(x, y) + c B(y, x) + c conj(c) Q(y)`. -/
theorem quad_add_smul (x y : ℕ →ᵇ ℂ) (c : ℂ) :
    pairForm u s (x + c • y) (x + c • y) = pairForm u s x x + starRingEnd ℂ c * pairForm u s x y +
      c * pairForm u s y x + c * starRingEnd ℂ c * pairForm u s y y := by
  rw [pairForm_add_left hu h0 h1 h2, pairForm_add_right hu h0 h1 h2, pairForm_add_right hu h0 h1 h2,
    pairForm_smul_left, pairForm_smul_left, pairForm_smul_right,
    pairForm_smul_right]
  ring

/-- **Polarization**: `4 B(x, y) = Q(x+y) − Q(x−y) + i Q(x+iy) − i Q(x−iy)`. -/
theorem polarization (x y : ℕ →ᵇ ℂ) :
    4 * pairForm u s x y = pairForm u s (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) -
      pairForm u s (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) +
      I * pairForm u s (x + I • y) (x + I • y) - I * pairForm u s (x + (-I) • y) (x + (-I) • y) := by
  rw [quad_add_smul hu h0 h1 h2, quad_add_smul hu h0 h1 h2, quad_add_smul hu h0 h1 h2,
    quad_add_smul hu h0 h1 h2]
  simp only [map_one, map_neg, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `Q_s` is continuous. -/
theorem continuous_quad : Continuous fun x : ℕ →ᵇ ℂ => pairForm u s x x := by
  obtain ⟨K, hK0, hK⟩ := exists_pairForm_bound hu h0 h1 h2
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  set δ := min 1 (ε / (K * (2 * ‖x₀‖ + 1) + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rw [dist_eq_norm] at hx ⊢
  have hdiff : pairForm u s x x - pairForm u s x₀ x₀ =
      pairForm u s (x - x₀) x + pairForm u s x₀ (x - x₀) := by
    have e1 := pairForm_add_left hu h0 h1 h2 (x - x₀) x₀ x
    have e2 := pairForm_add_right hu h0 h1 h2 x₀ (x - x₀) x₀
    rw [sub_add_cancel] at e1 e2
    linear_combination e1 + e2
  have hx1 : ‖x - x₀‖ < 1 := hx.trans_le (min_le_left _ _)
  have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have := norm_sub_norm_le x x₀
    linarith
  rw [hdiff]
  calc ‖pairForm u s (x - x₀) x + pairForm u s x₀ (x - x₀)‖
      ≤ K * (‖x - x₀‖ * ‖x‖) + K * (‖x₀‖ * ‖x - x₀‖) :=
        (norm_add_le _ _).trans (add_le_add (hK _ _) (hK _ _))
    _ = K * ‖x - x₀‖ * (‖x‖ + ‖x₀‖) := by ring
    _ ≤ K * ‖x - x₀‖ * (2 * ‖x₀‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ ‖x - x₀‖ * (K * (2 * ‖x₀‖ + 1) + 1) := by nlinarith [norm_nonneg (x - x₀)]
    _ < ε := by
        have hlt : ‖x - x₀‖ < ε / (K * (2 * ‖x₀‖ + 1) + 1) := hx.trans_le (min_le_right _ _)
        have hpos : 0 < K * (2 * ‖x₀‖ + 1) + 1 := by positivity
        rwa [lt_div_iff₀ hpos] at hlt

omit hu h0 h1 h2 in
theorem pairForm_single (j k : ℕ) :
    pairForm u s (single j) (single k) = (wt j : ℂ) * (wt k : ℂ) * pairEntry u s j k := by
  unfold pairForm pairEntry pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, cavity_single, map_mul, Complex.conj_ofReal]
  ring

/-- **The blind set is nowhere dense**: if a pair sees `s`, the zero set of `Q_s` has empty interior. -/
theorem interior_quad_zero_eq_empty {j k : ℕ} (hjk : pairEntry u s j k ≠ 0) :
    interior {x : ℕ →ᵇ ℂ | pairForm u s x x = 0} = ∅ := by
  by_contra hne
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  have hball' : ∀ x, ‖x - x₀‖ < r → pairForm u s x x = 0 := fun x hx => by
    have hmem := interior_subset (hball (show x ∈ Metric.ball x₀ r by rwa [Metric.mem_ball, dist_eq_norm]))
    simpa using hmem
  have hQ : ∀ h : ℕ →ᵇ ℂ, pairForm u s h h = 0 := by
    intro h
    set t : ℝ := r / (2 * (‖h‖ + 1))
    have ht : 0 < t := by positivity
    have hth : t * ‖h‖ < r := by
      have : t * ‖h‖ ≤ t * (‖h‖ + 1) := by nlinarith [norm_nonneg h]
      have e : t * (‖h‖ + 1) = r / 2 := by
        simp only [t]; field_simp
      linarith
    have hp : pairForm u s (x₀ + (t : ℂ) • h) (x₀ + (t : ℂ) • h) = 0 :=
      hball' _ (by rw [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg ht.le]; exact hth)
    have hm : pairForm u s (x₀ + (-(t : ℂ)) • h) (x₀ + (-(t : ℂ)) • h) = 0 :=
      hball' _ (by
        rw [add_sub_cancel_left, norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht.le]
        exact hth)
    have hc : pairForm u s x₀ x₀ = 0 := hball' _ (by rw [sub_self, norm_zero]; exact hr)
    rw [quad_add_smul hu h0 h1 h2] at hp hm
    simp only [map_neg, Complex.conj_ofReal] at hp hm
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    have h2t : (2 : ℂ) * (t : ℂ) * (t : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero htc) htc
    have : (2 : ℂ) * (t : ℂ) * (t : ℂ) * pairForm u s h h = 0 := by linear_combination hp + hm - 2 * hc
    exact (mul_eq_zero.1 this).resolve_left h2t
  have hB := polarization hu h0 h1 h2 (single j) (single k)
  rw [hQ, hQ, hQ, hQ, pairForm_single] at hB
  have hw : (wt j : ℂ) * (wt k : ℂ) ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.2 (wt_pos j).ne') (ofReal_ne_zero.2 (wt_pos k).ne')
  have : (4 : ℂ) * ((wt j : ℂ) * (wt k : ℂ)) * pairEntry u s j k = 0 := by
    linear_combination hB
  rcases mul_eq_zero.1 this with h | h
  · exact (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hw) h
  · exact hjk h

end Pair

/-- **Baire.** If every point of a countable set `S ⊆ ℂ ∖ {0, ½, 1}` is seen by some pair of cavity modes, the
coefficient vectors whose cavity energy sees every point of `S` are dense. -/
theorem dense_cavity_seeing (hu : IsCavityFamily u κ) {S : Set ℂ} (hS : S.Countable)
    (hS0 : ∀ s ∈ S, s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1) (hpair : ∀ s ∈ S, ∃ j k, pairEntry u s j k ≠ 0) :
    Dense (⋂ s ∈ S, {x : ℕ →ᵇ ℂ | pairForm u s x x ≠ 0}) := by
  refine dense_biInter_of_isOpen (fun s hs => ?_) hS fun s hs => ?_
  · obtain ⟨h0, h1, h2⟩ := hS0 s hs
    exact isOpen_ne_fun (continuous_quad hu h0 h1 h2) continuous_const
  · obtain ⟨h0, h1, h2⟩ := hS0 s hs
    obtain ⟨j, k, hjk⟩ := hpair s hs
    have hint := interior_quad_zero_eq_empty hu h0 h1 h2 hjk
    rw [interior_eq_empty_iff_dense_compl] at hint
    convert hint using 1
    ext x
    simp

/-- **One cavity function sees all of `S`.** -/
theorem exists_cavity_seeing (hu : IsCavityFamily u κ) {S : Set ℂ} (hS : S.Countable)
    (hS0 : ∀ s ∈ S, s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1) (hpair : ∀ s ∈ S, ∃ j k, pairEntry u s j k ≠ 0) :
    ∃ x : ℕ →ᵇ ℂ, ∀ s ∈ S, seedTransform (fun z => ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ)) s ≠ 0 := by
  obtain ⟨x, hx⟩ := (dense_cavity_seeing hu hS hS0 hpair).nonempty
  refine ⟨x, fun s hs => ?_⟩
  rw [← pairForm_self]
  exact Set.mem_iInter₂.1 hx s hs

/-! ### The converse: pairs are necessary -/

/-- The truncation of `x` to its first `N` coordinates. -/
def trunc (N : ℕ) (x : ℕ →ᵇ ℂ) : ℕ →ᵇ ℂ :=
  ofNormedAddCommGroupDiscrete (fun i => if i < N then x i else 0) ‖x‖ fun i => by
    split_ifs
    · exact x.norm_coe_le_norm i
    · simp

theorem tsum_tail_wt (N : ℕ) : ∑' j, (if N ≤ j then wt j else 0) = 2 * (1 / 2 : ℝ) ^ N := by
  have hs : Summable fun j => if N ≤ j then wt j else 0 :=
    Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [(wt_pos j).le])
      (fun j => by split_ifs <;> simp [(wt_pos j).le]) summable_wt
  rw [← hs.sum_add_tsum_nat_add N, Finset.sum_eq_zero fun j hj => by
    simp [not_le.2 (Finset.mem_range.1 hj)]]
  simp only [zero_add, le_add_iff_nonneg_left, zero_le, if_true, wt, pow_add]
  rw [tsum_mul_right, tsum_geometric_two]

/-- The tail `g_x − g_{x_{<N}}` is at most `2^{1−N} ‖x‖ e^{−κ Im z}`. -/
theorem norm_cavity_sub_trunc_le (hu : IsCavityFamily u κ) (x : ℕ →ᵇ ℂ) (N : ℕ) (z : ℍ) :
    ‖cavity u x z - cavity u (trunc N x) z‖ ≤ (2 * (1 / 2 : ℝ) ^ N * ‖x‖) * Real.exp (-κ * z.im) := by
  have e : cavity u x z - cavity u (trunc N x) z =
      ∑' j, (if N ≤ j then x j * (wt j : ℂ) * u j z else 0) := by
    rw [cavity, cavity, ← (summable_cavityTerm hu x z).tsum_sub (summable_cavityTerm hu _ z)]
    refine tsum_congr fun j => ?_
    simp only [trunc, coe_ofNormedAddCommGroupDiscrete]
    by_cases hj : j < N
    · simp [hj, not_le.2 hj]
    · simp [hj, not_lt.1 hj]
  have hbound : ∀ j, ‖(if N ≤ j then x j * (wt j : ℂ) * u j z else 0)‖ ≤
      ‖x‖ * Real.exp (-κ * z.im) * (if N ≤ j then wt j else 0) := fun j => by
    split_ifs
    · exact norm_cavityTerm_le hu x j z
    · simp
  have hs : Summable fun j => ‖x‖ * Real.exp (-κ * z.im) * (if N ≤ j then wt j else 0) :=
    (Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [(wt_pos j).le])
      (fun j => by split_ifs <;> simp [(wt_pos j).le]) summable_wt).mul_left _
  rw [e]
  calc _ ≤ ∑' j, ‖x‖ * Real.exp (-κ * z.im) * (if N ≤ j then wt j else 0) :=
        tsum_of_norm_bounded hs.hasSum hbound
    _ = (2 * (1 / 2 : ℝ) ^ N * ‖x‖) * Real.exp (-κ * z.im) := by
        rw [tsum_mul_left, tsum_tail_wt]; ring

theorem trunc_succ (N : ℕ) (x : ℕ →ᵇ ℂ) : trunc (N + 1) x = trunc N x + x N • single N := by
  ext i
  simp only [trunc, single, coe_ofNormedAddCommGroupDiscrete, BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_smul, Pi.add_apply, smul_eq_mul]
  rcases lt_trichotomy i N with h | h | h
  · simp [h, h.trans (Nat.lt_succ_self N), h.ne]
  · subst h; simp
  · simp [not_lt.2 h.le, not_lt.2 (Nat.succ_le_of_lt h), h.ne']

theorem trunc_zero (x : ℕ →ᵇ ℂ) : trunc 0 x = 0 := by
  ext i; simp [trunc]

/-- Subtraction in the first slot of the pairing, for integrable pieces. -/
theorem pairing_sub_left {s : ℂ} {g g' h : ℍ → ℂ} (hi : IntegrableOn (pairIntegrand s g h) ModularGroup.fd)
    (hi' : IntegrableOn (pairIntegrand s g' h) ModularGroup.fd) :
    pairing s (fun z => g z - g' z) h = pairing s g h - pairing s g' h := by
  unfold pairing
  rw [← integral_sub hi hi']
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand]
  ring

/-- Subtraction in the second slot of the pairing, for integrable pieces. -/
theorem pairing_sub_right {s : ℂ} {g h h' : ℍ → ℂ} (hi : IntegrableOn (pairIntegrand s g h) ModularGroup.fd)
    (hi' : IntegrableOn (pairIntegrand s g h') ModularGroup.fd) :
    pairing s g (fun z => h z - h' z) = pairing s g h - pairing s g h' := by
  unfold pairing
  rw [← integral_sub hi hi']
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, map_sub]
  ring

section Converse

variable (hu : IsCavityFamily u κ) (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1)
include hu h0 h1 h2

/-- On truncations the pair form is a finite combination of pair entries. -/
theorem pairForm_trunc_eq_zero (hb : ∀ j k, pairEntry u s j k = 0) (N M : ℕ) (x x' : ℕ →ᵇ ℂ) :
    pairForm u s (trunc N x) (trunc M x') = 0 := by
  have hsingle : ∀ j k, pairForm u s (single j) (single k) = 0 := fun j k => by
    rw [pairForm_single, hb, mul_zero]
  have hright : ∀ j M, pairForm u s (single j) (trunc M x') = 0 := by
    intro j M
    induction M with
    | zero =>
      rw [trunc_zero, ← zero_smul ℂ (0 : ℕ →ᵇ ℂ), pairForm_smul_right, map_zero, zero_mul]
    | succ M ih =>
      rw [trunc_succ, pairForm_add_right hu h0 h1 h2, pairForm_smul_right, ih, hsingle,
        mul_zero, add_zero]
  induction N with
  | zero => rw [trunc_zero, ← zero_smul ℂ (0 : ℕ →ᵇ ℂ), pairForm_smul_left, zero_mul]
  | succ N ih =>
    rw [trunc_succ, pairForm_add_left hu h0 h1 h2, pairForm_smul_left, ih, hright, mul_zero,
      add_zero]

/-- **Pairs are necessary**: if every pair entry vanishes at `s`, every cavity energy is blind at `s`. -/
theorem quad_eq_zero_of_pairEntry_eq_zero (hb : ∀ j k, pairEntry u s j k = 0) (x : ℕ →ᵇ ℂ) :
    pairForm u s x x = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_pairing_bound hu.pos h0 h1 h2
  have hle : ∀ N : ℕ, ‖pairForm u s x x‖ ≤ 8 * K * ‖x‖ ^ 2 * (1 / 2 : ℝ) ^ N := by
    intro N
    set xN := trunc N x
    set g := cavity u x
    set gN := cavity u xN
    have hxN : ‖xN‖ ≤ ‖x‖ := by
      refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun i => ?_
      simp only [xN, trunc, coe_ofNormedAddCommGroupDiscrete]
      split_ifs
      · exact x.norm_coe_le_norm i
      · simp
    have cg := continuous_cavity hu x
    have cgN := continuous_cavity hu xN
    have cd : Continuous fun z => g z - gN z := cg.sub cgN
    have eg := norm_cavity_le hu x
    have egN := norm_cavity_le hu xN
    have ed := norm_cavity_sub_trunc_le hu x N
    have i1 := (hK _ _ _ _ cg cg eg eg).1
    have i2 := (hK _ _ _ _ cgN cg egN eg).1
    have i3 := (hK _ _ _ _ cgN cgN egN egN).1
    have hzero : pairing s gN gN = 0 := pairForm_trunc_eq_zero hu h0 h1 h2 hb N N x x
    have hsplit : pairForm u s x x = pairing s (fun z => g z - gN z) g + pairing s gN (fun z => g z - gN z) := by
      rw [pairing_sub_left i1 i2, pairing_sub_right i2 i3, hzero]
      unfold pairForm
      ring
    have b1 := (hK _ _ _ _ cd cg ed eg).2
    have b2 := (hK _ _ _ _ cgN cd egN ed).2
    have hr : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
    rw [hsplit]
    calc ‖pairing s (fun z => g z - gN z) g + pairing s gN (fun z => g z - gN z)‖
        ≤ K * (2 * (1 / 2 : ℝ) ^ N * ‖x‖ * (2 * ‖x‖)) + K * (2 * ‖xN‖ * (2 * (1 / 2 : ℝ) ^ N * ‖x‖)) :=
          (norm_add_le _ _).trans (add_le_add b1 b2)
      _ ≤ K * (2 * (1 / 2 : ℝ) ^ N * ‖x‖ * (2 * ‖x‖)) + K * (2 * ‖x‖ * (2 * (1 / 2 : ℝ) ^ N * ‖x‖)) := by
          gcongr
      _ = 8 * K * ‖x‖ ^ 2 * (1 / 2 : ℝ) ^ N := by ring
  have ht : Tendsto (fun N : ℕ => 8 * K * ‖x‖ ^ 2 * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (8 * K * ‖x‖ ^ 2)
  exact norm_le_zero_iff.1 (ge_of_tendsto' ht hle)

end Converse

/-- **B109 for a cavity family, reduced to pairs.** For a countable set `S ⊆ ℂ ∖ {0, ½, 1}`, one cavity
function whose energy sees every point of `S` exists iff every point of `S` is seen by some pair of modes. -/
theorem exists_cavity_seeing_iff (hu : IsCavityFamily u κ) {S : Set ℂ} (hS : S.Countable)
    (hS0 : ∀ s ∈ S, s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1) :
    (∃ x : ℕ →ᵇ ℂ, ∀ s ∈ S, seedTransform (fun z => ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ)) s ≠ 0) ↔
      ∀ s ∈ S, ∃ j k, pairEntry u s j k ≠ 0 := by
  refine ⟨fun ⟨x, hx⟩ s hs => ?_, exists_cavity_seeing hu hS hS0⟩
  by_contra hno
  push Not at hno
  obtain ⟨h0, h1, h2⟩ := hS0 s hs
  exact hx s hs (by rw [← pairForm_self]; exact quad_eq_zero_of_pairEntry_eq_zero hu h0 h1 h2 hno x)

/-! ### The right zeros of `ζ` -/

/-- The resonances `ρ/2` of the zeros of `ζ` right of the critical line. -/
def rightResonances : Set ℂ := (fun ρ => ρ / 2) '' {ρ : ℂ | riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re}

theorem countable_rightResonances : rightResonances.Countable := by
  refine Set.Countable.image ?_ _
  have hx : xi 2 ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
  have han : AnalyticOnNhd ℂ xi Set.univ := fun s _ => xi_differentiable.analyticAt s
  have hdisc := isDiscrete_of_codiscreteWithin (U := Set.univ) (s := xi ⁻¹' {0})
    (han.preimage_zero_mem_codiscrete (x := 2) hx)
  have hcount := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  rw [Set.inter_univ] at hcount
  refine hcount.mono fun ρ hρ => ?_
  refine xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.2 ⟨hρ.1, fun n hn => ?_⟩
  have := congrArg Complex.re hn
  simp at this
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith [hρ.2]

theorem rightResonances_ne {s : ℂ} (hs : s ∈ rightResonances) : s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1 := by
  obtain ⟨ρ, ⟨hζ, hρ⟩, rfl⟩ := hs
  have h1 : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have := congrArg Complex.re h
    simp at this
    linarith

/-- **One cavity function sees every right resonance iff every right resonance is seen by a pair.** -/
theorem cavity_sees_every_right_zero_iff (hu : IsCavityFamily u κ) :
    (∃ x : ℕ →ᵇ ℂ, ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re →
        seedTransform (fun z => ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ)) (ρ / 2) ≠ 0) ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ∃ j k, pairEntry u (ρ / 2) j k ≠ 0 := by
  have h := exists_cavity_seeing_iff hu countable_rightResonances fun s hs => rightResonances_ne hs
  simp only [rightResonances, Set.forall_mem_image, Set.mem_setOf_eq, and_imp] at h
  exact h

/-- **The complete cavity receiver.** If the energy of a cavity function sees every right resonance, a horocycle
rate `y^α` of that energy forces `Re ρ ≤ 2 − 2α` for every zero `ρ` of `ζ` with `Re ρ > ½`. -/
theorem re_le_of_cavity_rate (hu : IsCavityFamily u κ) {x : ℕ →ᵇ ℂ}
    (hsee : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re →
      seedTransform (fun z => ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ)) (ρ / 2) ≠ 0)
    {α : ℝ} {c : ℂ} {C : ℝ}
    (hrate : ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖response (fun z => ((‖cavity u x z‖ ^ 2 : ℝ) : ℂ)) y - c‖ ≤ C * y ^ α)
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) : ρ.re ≤ 2 - 2 * α := by
  by_contra hlt
  push Not at hlt
  exact not_rate_of_seen (isSeed_cavity hu x).normSq hζ (by linarith) (hsee ρ hζ hρ)
    (by linarith) c C hrate

/-! ### Maass cusp forms -/

/-- The normalized cavity family `v_j / M_j` of a sequence of cusp forms. -/
def cuspFamily (v : ℕ → ℍ → ℂ) (M : ℕ → ℝ) (j : ℕ) (z : ℍ) : ℂ := ((M j : ℂ))⁻¹ * v j z

/-- A Maass cusp form lies under `M e^{−π Im z}` on all of `ℍ`. -/
theorem exists_envelope_of_mem_cuspSpace {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℍ, ‖g z‖ ≤ M * Real.exp (-Real.pi * z.im) := by
  obtain ⟨D, hD0, hD⟩ := cuspForm_decay hg
  obtain ⟨B, hB⟩ := HeckeCusp.exists_bound hg
  exact exists_global_exp_bound hB hD0 Real.pi_pos hD

variable {v : ℕ → ℍ → ℂ} {lam : ℕ → ℝ} {M : ℕ → ℝ}

theorem isCavityFamily_cuspFamily (hv : ∀ j, v j ∈ HeckeCusp.cuspSpace (lam j))
    (hM : ∀ j, 0 < M j ∧ ∀ z : ℍ, ‖v j z‖ ≤ M j * Real.exp (-Real.pi * z.im)) :
    IsCavityFamily (cuspFamily v M) Real.pi := by
  refine ⟨Real.pi_pos, fun j γ z => ?_, fun j => continuous_const.mul
    (HeckeCusp.continuous_of_maass (hv j).2.1), fun j z => ?_⟩
  · show ((M j : ℂ))⁻¹ * v j (γ • z) = ((M j : ℂ))⁻¹ * v j z
    rw [(hv j).1]
  · have hMj := (hM j).1
    rw [cuspFamily, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hMj.le]
    calc (M j)⁻¹ * ‖v j z‖ ≤ (M j)⁻¹ * (M j * Real.exp (-Real.pi * z.im)) :=
          mul_le_mul_of_nonneg_left ((hM j).2 z) (inv_nonneg.2 hMj.le)
      _ = Real.exp (-Real.pi * z.im) := by rw [inv_mul_cancel_left₀ hMj.ne']

theorem pairEntry_cuspFamily (s : ℂ) (j k : ℕ) :
    pairEntry (cuspFamily v M) s j k = ((M j : ℂ))⁻¹ * ((M k : ℂ))⁻¹ * pairing s (v j) (v k) := by
  unfold pairEntry pairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [pairIntegrand, cuspFamily, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

/-- **The cavity function of cusp forms is cuspidal**: its horocycle means vanish. -/
theorem response_cavity_cuspFamily_eq_zero (hv : ∀ j, v j ∈ HeckeCusp.cuspSpace (lam j))
    (hM : ∀ j, 0 < M j ∧ ∀ z : ℍ, ‖v j z‖ ≤ M j * Real.exp (-Real.pi * z.im)) (x : ℕ →ᵇ ℂ)
    {y : ℝ} (hy : 0 < y) : response (cavity (cuspFamily v M) x) y = 0 := by
  have hu := isCavityFamily_cuspFamily hv hM
  set f : ℕ → ℝ → ℂ := fun j t => x j * (wt j : ℂ) * cuspFamily v M j (ofComplex ⟨t, y⟩)
  have hcont : ∀ j, Continuous (f j) := by
    intro j
    have hmk : Continuous fun t : ℝ => (⟨t, y⟩ : ℂ) := by
      have : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
        funext t; apply Complex.ext <;> simp
      rw [this]; fun_prop
    have hoc : ContinuousOn (fun w : ℂ => cuspFamily v M j (ofComplex w)) {w : ℂ | 0 < w.im} :=
      (hu.continuous j).comp_continuousOn (UpperHalfPlane.ofComplex.continuousOn.mono fun w hw => by
        simpa [UpperHalfPlane.ofComplex] using hw)
    exact continuous_const.mul (hoc.comp_continuous hmk fun t => hy)
  have hint : ∀ j, Integrable (f j) (volume.restrict (Ico (0 : ℝ) 1)) := fun j =>
    ((hcont j).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  have hnorm : ∀ j, ∫ t in Ico (0 : ℝ) 1, ‖f j t‖ ≤ ‖x‖ * wt j := by
    intro j
    have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖‖f j t‖‖ ≤ ‖x‖ * wt j := fun t _ => by
      rw [norm_norm]
      refine (norm_cavityTerm_le hu x j _).trans ?_
      have h1 : Real.exp (-Real.pi * (ofComplex (⟨t, y⟩ : ℂ)).im) ≤ 1 :=
        Real.exp_le_one_iff.2 (by rw [ofComplex_mk_im hy]; nlinarith [Real.pi_pos])
      have := wt_pos j
      calc ‖x‖ * Real.exp (-Real.pi * (ofComplex (⟨t, y⟩ : ℂ)).im) * wt j ≤ ‖x‖ * 1 * wt j := by gcongr
        _ = ‖x‖ * wt j := by ring
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ico (0 : ℝ) 1) measure_Ico_lt_top hb
    rw [measureReal_def, Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal zero_le_one, mul_one] at h
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans h)
  have hsum : Summable fun j => ∫ t in Ico (0 : ℝ) 1, ‖f j t‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _) hnorm
      (summable_wt.mul_left ‖x‖)
  have hterm : ∀ j, ∫ t in Ico (0 : ℝ) 1, f j t = 0 := by
    intro j
    have hc := (hv j).2.2.2 y hy
    unfold HeckeCusp.constTerm at hc
    show ∫ t in Ico (0 : ℝ) 1, x j * (wt j : ℂ) * (((M j : ℂ))⁻¹ * v j (ofComplex ⟨t, y⟩)) = 0
    rw [integral_const_mul, integral_const_mul]
    have he : ∫ t in Ico (0 : ℝ) 1, v j (ofComplex ⟨t, y⟩) =
        ∫ t in (0 : ℝ)..1, v j (ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point t y)) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      congr 2
      apply Complex.ext <;> simp [GaloisForLFunctions.RHTower.SelbergMaassMean.point]
    rw [he, hc, mul_zero, mul_zero]
  show ∫ t in Ico (0 : ℝ) 1, ∑' j, f j t = 0
  rw [← integral_tsum_of_summable_integral_norm hint hsum, tsum_congr hterm, tsum_zero]

/-- **B109 reduced to pairs, for Maass cusp forms.** For every sequence of Maass cusp forms `v_j` there are
normalizers `M_j > 0` such that a cuspidal cavity function `g = Σ_j x_j 2^{−j} v_j / M_j` whose energy sees every
right resonance exists iff every right resonance `ρ/2` is seen by some pair: `∫_𝒟 v_j conj(v_k) E*(ρ/2 − ½) ≠ 0`. -/
theorem cuspFunction_sees_every_right_zero_iff (hv : ∀ j, v j ∈ HeckeCusp.cuspSpace (lam j)) :
    ∃ M : ℕ → ℝ, (∀ j, 0 < M j) ∧ IsCavityFamily (cuspFamily v M) Real.pi ∧
      ((∃ x : ℕ →ᵇ ℂ, ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re →
          seedTransform (fun z => ((‖cavity (cuspFamily v M) x z‖ ^ 2 : ℝ) : ℂ)) (ρ / 2) ≠ 0) ↔
        ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ∃ j k, pairing (ρ / 2) (v j) (v k) ≠ 0) := by
  choose M hM using fun j => exists_envelope_of_mem_cuspSpace (hv j)
  have hu := isCavityFamily_cuspFamily hv hM
  refine ⟨M, fun j => (hM j).1, hu, ?_⟩
  rw [cavity_sees_every_right_zero_iff hu]
  have hne : ∀ s j k, pairEntry (cuspFamily v M) s j k ≠ 0 ↔ pairing s (v j) (v k) ≠ 0 := by
    intro s j k
    rw [pairEntry_cuspFamily]
    have h1 : ((M j : ℂ))⁻¹ ≠ 0 := inv_ne_zero (ofReal_ne_zero.2 (hM j).1.ne')
    have h2 : ((M k : ℂ))⁻¹ ≠ 0 := inv_ne_zero (ofReal_ne_zero.2 (hM k).1.ne')
    exact ⟨fun h h' => h (by rw [h', mul_zero]), fun h h' => h ((mul_eq_zero.1 h').resolve_left
      (mul_ne_zero h1 h2))⟩
  simp only [hne]

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
