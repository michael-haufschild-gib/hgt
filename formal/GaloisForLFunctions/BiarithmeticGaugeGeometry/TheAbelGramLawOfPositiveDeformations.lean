import GaloisForLFunctions.BiarithmeticGaugeGeometry.TheLandauWronskianDeformationPrinciple
import GaloisForLFunctions.MultiplicativePositivityGeometry.TotalZeroMass

/-!
# The Abel–Gram Law of Positive Deformations

Suppose entire functions `Λ, Λ₀` of finite order everywhere satisfy the Landau–Wronskian relation
`Λ₀'/Λ₀ − Λ'/Λ = 𝓛ν + E` on `Re z > x₀`, away from zeros, with `ν ≥ 0` and `E` Abel-negligible on
the line, `(σ − x₀) E(σ + it) → 0` (for instance holomorphic across it,
`tendsto_sub_mul_of_differentiableOn`). Then the divisor jumps across that line are Abel limits of
the Laplace transform of `ν`, and inherit its positivity.

* **Abel limits (`tendsto_abel_of_rel`).** `(σ − x₀) 𝓛ν(σ + it) → ord_{x₀+it} Λ₀ − ord_{x₀+it} Λ`
  as `σ ↓ x₀`: the left side of the relation, multiplied by `σ − x₀`, tends to the difference of
  orders.
* **Gram law (`jump_isEvenPosDef_of_rel`).** The jump `t ↦ ord_{x₀+it} Λ₀ − ord_{x₀+it} Λ` is even
  positive definite: it is the pointwise limit of `(σ − x₀) ∫ e^{−σu} cos(tu) dν(u)`, and
  `Σ cᵢcⱼ cos((xᵢ − xⱼ)u) = (Σ cᵢ cos xᵢu)² + (Σ cᵢ sin xᵢu)²`.
* **Transfer and capacity (`abs_jump_le_of_rel`, `sum_jump_le_of_rel`).** Every jump is bounded by
  the jump on the real axis; if `Λ₀` has no zero on the line off the real axis, the zeros of `Λ` on
  the line at positive heights have total multiplicity at most half the real jump.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open MultiplicativePositivityGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace complexLaplace_ofReal)

/-- The Laplace transform of a nonnegative measure is dominated on vertical lines by its value on
the real axis. -/
theorem norm_complexLaplace_le (ν : Measure ℝ) (z : ℂ) :
    ‖complexLaplace ν z‖ ≤ laplaceReal ν z.re := by
  unfold complexLaplace laplaceReal
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (ae_of_all _ fun u => ?_)))
  dsimp only
  rw [Complex.norm_exp]
  congr 1
  simp

/-- A function analytic at `w` with finite order there has no zeros in a punctured
neighbourhood. -/
theorem eventually_ne_zero_of_orderAt_ne_top {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w)
    (htop : analyticOrderAt f w ≠ ⊤) : ∀ᶠ z in 𝓝[≠] w, f z ≠ 0 :=
  hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h =>
    htop (analyticOrderAt_eq_top.mpr h)

/-- The horizontal approach `σ ↦ σ + it` from the right of `x₀` reaches `x₀ + it` from the
punctured neighbourhood. -/
theorem tendsto_ofReal_add_mul_I_nhdsGT (x₀ t : ℝ) :
    Tendsto (fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I) (𝓝[>] x₀) (𝓝[≠] ((x₀ : ℂ) + (t : ℂ) * I)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h : Continuous fun σ : ℝ => (σ : ℂ) + (t : ℂ) * I := by fun_prop
    exact (h.tendsto x₀).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero] at hre
    have hσ' : x₀ < σ := hσ
    linarith

/-- A perturbation holomorphic across the line `Re z = x₀` is Abel-negligible there:
`(σ − x₀) E(σ + it) → 0` as `σ ↓ x₀`. -/
theorem tendsto_sub_mul_of_differentiableOn {E : ℂ → ℂ} {x₀ σE : ℝ} (hσE : σE < x₀)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re}) (t : ℝ) :
    Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) * E ((σ : ℂ) + (t : ℂ) * I)) (𝓝[>] x₀) (𝓝 0) := by
  set w : ℂ := (x₀ : ℂ) + (t : ℂ) * I with hw
  have hwE : {s : ℂ | σE < s.re} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show σE < w.re by simpa [hw])
  have h : ContinuousAt (fun z => (z - w) * E z) w :=
    (continuousAt_id.sub continuousAt_const).mul (hE.continuousOn.continuousAt hwE)
  have h' := h.tendsto
  simp only [sub_self, zero_mul] at h'
  refine (h'.comp ((tendsto_ofReal_add_mul_I_nhdsGT x₀ t).mono_right nhdsWithin_le_nhds)).congr
    fun σ => ?_
  simp only [Function.comp_apply, hw]
  push_cast
  ring

/-- **Abel limits across a vertical line.** Under the Landau–Wronskian relation on `Re z > x₀` with
an Abel-negligible perturbation, `(σ − x₀) E(σ + it) → 0`, the Abel limit of `(σ − x₀) 𝓛ν(σ + it)`
as `σ ↓ x₀` is the jump `ord_{x₀+it} Λ₀ − ord_{x₀+it} Λ`. -/
theorem tendsto_abel_of_rel {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (hΛ₀ : Differentiable ℂ Λ₀)
    (htop : ∀ z, analyticOrderAt Λ z ≠ ⊤) (htop₀ : ∀ z, analyticOrderAt Λ₀ z ≠ ⊤)
    {ν : Measure ℝ} {E : ℂ → ℂ} {x₀ : ℝ}
    (hrel : ∀ z : ℂ, x₀ < z.re → Λ z ≠ 0 → Λ₀ z ≠ 0 →
      logDeriv Λ₀ z - logDeriv Λ z = complexLaplace ν z + E z)
    (hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) * E ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] x₀) (𝓝 0)) (t : ℝ) :
    Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) * complexLaplace ν ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] x₀)
      (𝓝 (((analyticOrderAt Λ₀ ((x₀ : ℂ) + (t : ℂ) * I)).toNat : ℂ) -
        (analyticOrderAt Λ ((x₀ : ℂ) + (t : ℂ) * I)).toNat)) := by
  set w : ℂ := (x₀ : ℂ) + (t : ℂ) * I with hw
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (htop w)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (htop₀ w)
  have hΛan : AnalyticAt ℂ Λ w := hΛ.analyticAt w
  have hΛ₀an : AnalyticAt ℂ Λ₀ w := hΛ₀.analyticAt w
  have hmap := tendsto_ofReal_add_mul_I_nhdsGT x₀ t
  have hta := (tendsto_sub_mul_logDeriv hΛan ha.symm).comp hmap
  have htb := (tendsto_sub_mul_logDeriv hΛ₀an hk.symm).comp hmap
  have hlim := (htb.sub hta).sub (hEt t)
  rw [sub_zero] at hlim
  rw [← ha, ← hk, ENat.toNat_coe, ENat.toNat_coe]
  refine hlim.congr' ?_
  filter_upwards [hmap.eventually (eventually_ne_zero_of_orderAt_ne_top hΛan (htop w)),
    hmap.eventually (eventually_ne_zero_of_orderAt_ne_top hΛ₀an (htop₀ w)),
    self_mem_nhdsWithin] with σ h1 h2 h3
  have hσ : x₀ < σ := h3
  have hzre : x₀ < ((σ : ℂ) + (t : ℂ) * I).re := by
    simpa using hσ
  have hr := hrel _ hzre h1 h2
  have hzw : (σ : ℂ) + (t : ℂ) * I - w = ((σ - x₀ : ℝ) : ℂ) := by
    rw [hw]; push_cast; ring
  simp only [Function.comp_apply]
  rw [hzw, ← mul_sub, ← mul_sub, hr]
  ring

/-- **Transfer law across a vertical line.** Every jump is bounded by the jump on the real axis:
`|ord_{x₀+it} Λ₀ − ord_{x₀+it} Λ| ≤ ord_{x₀} Λ₀ − ord_{x₀} Λ`. -/
theorem abs_jump_le_of_rel {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (hΛ₀ : Differentiable ℂ Λ₀)
    (htop : ∀ z, analyticOrderAt Λ z ≠ ⊤) (htop₀ : ∀ z, analyticOrderAt Λ₀ z ≠ ⊤)
    {ν : Measure ℝ} {E : ℂ → ℂ} {x₀ : ℝ}
    (hrel : ∀ z : ℂ, x₀ < z.re → Λ z ≠ 0 → Λ₀ z ≠ 0 →
      logDeriv Λ₀ z - logDeriv Λ z = complexLaplace ν z + E z)
    (hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) * E ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] x₀) (𝓝 0)) (t : ℝ) :
    |((analyticOrderAt Λ₀ ((x₀ : ℂ) + (t : ℂ) * I)).toNat : ℝ) -
        (analyticOrderAt Λ ((x₀ : ℂ) + (t : ℂ) * I)).toNat| ≤
      ((analyticOrderAt Λ₀ (x₀ : ℂ)).toNat : ℝ) - (analyticOrderAt Λ (x₀ : ℂ)).toNat := by
  have ht := tendsto_abel_of_rel hΛ hΛ₀ htop htop₀ hrel hEt t
  have h0 := tendsto_abel_of_rel hΛ hΛ₀ htop htop₀ hrel hEt 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
  -- on the real axis the Abel quantity is `(σ − x₀) 𝓛ν(σ)`
  have h0r := (Complex.continuous_re.tendsto _).comp h0
  simp only [Function.comp_def, complexLaplace_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.sub_re, Complex.natCast_re] at h0r
  have hn := (continuous_norm.tendsto _).comp ht
  have hle : ∀ᶠ σ : ℝ in 𝓝[>] x₀,
      ‖((σ - x₀ : ℝ) : ℂ) * complexLaplace ν ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        (σ - x₀) * laplaceReal ν σ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : x₀ < σ := hσ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    refine mul_le_mul_of_nonneg_left ((norm_complexLaplace_le ν _).trans (le_of_eq ?_))
      (by linarith)
    simp
  have hmain := le_of_tendsto_of_tendsto hn h0r hle
  have hcast : ∀ p q : ℕ, ‖(p : ℂ) - q‖ = |(p : ℝ) - q| := fun p q => by
    rw [show (p : ℂ) - q = (((p : ℝ) - q : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hcast] at hmain
  exact hmain

/-- The cosine transform `t ↦ ∫ e^{−σu} cos(tu) dν` of a nonnegative measure with integrable
kernel is even positive definite. -/
theorem isEvenPosDef_laplace_cos {ν : Measure ℝ} {σ : ℝ}
    (hint : Integrable (fun u : ℝ => Real.exp (-σ * u)) (ν.restrict (Ioi (0 : ℝ)))) :
    IsEvenPosDef fun t : ℝ => ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * Real.cos (t * u) ∂ν where
  even t := by simp only [neg_mul, Real.cos_neg]
  posDef := by
    intro n x c
    have hi0 : ∀ τ : ℝ, Integrable (fun u : ℝ => Real.exp (-σ * u) * Real.cos (τ * u))
        (ν.restrict (Ioi (0 : ℝ))) := fun τ =>
      hint.mono' (by fun_prop : Continuous fun u : ℝ =>
          Real.exp (-σ * u) * Real.cos (τ * u)).aestronglyMeasurable
        (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
          exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _))
    have hi : ∀ i j, Integrable (fun u : ℝ => c i * c j *
        (Real.exp (-σ * u) * Real.cos ((x i - x j) * u))) (ν.restrict (Ioi (0 : ℝ))) :=
      fun i j => (hi0 (x i - x j)).const_mul _
    have h1 : ∀ i, ∑ j, c i * c j *
        ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * Real.cos ((x i - x j) * u) ∂ν =
        ∫ u in Ioi (0 : ℝ), ∑ j, c i * c j *
          (Real.exp (-σ * u) * Real.cos ((x i - x j) * u)) ∂ν := fun i => by
      rw [integral_finsetSum _ fun j _ => hi i j]
      exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
    rw [Finset.sum_congr rfl fun i _ => h1 i,
      ← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    refine integral_nonneg fun u => ?_
    -- `Σᵢⱼ cᵢcⱼ cos((xᵢ − xⱼ)u) = (Σ cᵢ cos xᵢu)² + (Σ cᵢ sin xᵢu)²`
    have hsq : ∑ i, ∑ j, c i * c j * (Real.exp (-σ * u) * Real.cos ((x i - x j) * u)) =
        Real.exp (-σ * u) * ((∑ i, c i * Real.cos (x i * u)) ^ 2 +
          (∑ i, c i * Real.sin (x i * u)) ^ 2) := by
      rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_mul, Real.cos_sub]
      ring
    simp only
    rw [hsq]
    positivity

/-- **Gram law across a vertical line.** Under the Landau–Wronskian relation on `Re z > x₀`, with the
Laplace kernel of `ν` integrable there and `E` holomorphic across the line, the jump
`t ↦ ord_{x₀+it} Λ₀ − ord_{x₀+it} Λ` is even positive definite. -/
theorem jump_isEvenPosDef_of_rel {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hΛ₀ : Differentiable ℂ Λ₀) (htop : ∀ z, analyticOrderAt Λ z ≠ ⊤)
    (htop₀ : ∀ z, analyticOrderAt Λ₀ z ≠ ⊤) {ν : Measure ℝ} {E : ℂ → ℂ} {x₀ : ℝ}
    (hrel : ∀ z : ℂ, x₀ < z.re → Λ z ≠ 0 → Λ₀ z ≠ 0 →
      logDeriv Λ₀ z - logDeriv Λ z = complexLaplace ν z + E z)
    (hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) * E ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] x₀) (𝓝 0))
    (hint : ∀ z : ℂ, x₀ < z.re →
      Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ)))) :
    IsEvenPosDef fun t : ℝ =>
      ((analyticOrderAt Λ₀ ((x₀ : ℂ) + (t : ℂ) * I)).toNat : ℝ) -
        (analyticOrderAt Λ ((x₀ : ℂ) + (t : ℂ) * I)).toNat := by
  -- the real part of `(σ − x₀) 𝓛ν(σ + it)` is `(σ − x₀)` times the cosine transform
  have hre : ∀ σ : ℝ, x₀ < σ → ∀ t : ℝ,
      (((σ - x₀ : ℝ) : ℂ) * complexLaplace ν ((σ : ℂ) + (t : ℂ) * I)).re =
        (σ - x₀) * ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * Real.cos (t * u) ∂ν := by
    intro σ hσ t
    have hz : x₀ < ((σ : ℂ) + (t : ℂ) * I).re := by simpa using hσ
    have h := integral_re (hint _ hz)
    simp only [RCLike.re_to_complex] at h
    rw [Complex.re_ofReal_mul, complexLaplace, ← h]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [Complex.exp_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring_nf
    rw [Real.cos_neg]
  refine isEvenPosDef_of_tendsto (l := 𝓝[>] x₀)
    (F := fun σ t => (σ - x₀) * ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * Real.cos (t * u) ∂ν)
    ?_ fun t => ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : x₀ < σ := hσ
    have hI : Integrable (fun u : ℝ => Real.exp (-σ * u)) (ν.restrict (Ioi (0 : ℝ))) := by
      refine (hint (σ : ℂ) (by simpa using hσ')).norm.congr (ae_of_all _ fun u => ?_)
      dsimp only
      rw [Complex.norm_exp]
      congr 1
      simp
    exact (isEvenPosDef_laplace_cos hI).smul (by linarith)
  · have h := (Complex.continuous_re.tendsto _).comp
      (tendsto_abel_of_rel hΛ hΛ₀ htop htop₀ hrel hEt t)
    simp only [Complex.sub_re, Complex.natCast_re] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact hre σ hσ t

/-- **Line capacity.** If, in addition, `Λ₀` has no zero on the line `Re z = x₀` off the real axis,
the zeros of `Λ` on that line at any finite set of positive heights have total multiplicity at most
half the real jump: `2 Σ_{t ∈ Z} ord_{x₀+it} Λ ≤ ord_{x₀} Λ₀ − ord_{x₀} Λ`. -/
theorem sum_jump_le_of_rel {Λ Λ₀ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hΛ₀ : Differentiable ℂ Λ₀) (htop : ∀ z, analyticOrderAt Λ z ≠ ⊤)
    (htop₀ : ∀ z, analyticOrderAt Λ₀ z ≠ ⊤) {ν : Measure ℝ} {E : ℂ → ℂ} {x₀ : ℝ}
    (hrel : ∀ z : ℂ, x₀ < z.re → Λ z ≠ 0 → Λ₀ z ≠ 0 →
      logDeriv Λ₀ z - logDeriv Λ z = complexLaplace ν z + E z)
    (hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - x₀ : ℝ) : ℂ) * E ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] x₀) (𝓝 0))
    (hint : ∀ z : ℂ, x₀ < z.re →
      Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ))))
    (hline : ∀ t : ℝ, t ≠ 0 → Λ₀ ((x₀ : ℂ) + (t : ℂ) * I) ≠ 0) {Z : Finset ℝ}
    (hZ : ∀ z ∈ Z, 0 < z) :
    2 * ∑ t ∈ Z, ((analyticOrderAt Λ ((x₀ : ℂ) + (t : ℂ) * I)).toNat : ℝ) ≤
      ((analyticOrderAt Λ₀ (x₀ : ℂ)).toNat : ℝ) - (analyticOrderAt Λ (x₀ : ℂ)).toNat := by
  have hD := jump_isEvenPosDef_of_rel hΛ hΛ₀ htop htop₀ hrel hEt hint
  have hzero : ∀ t : ℝ, t ≠ 0 → (analyticOrderAt Λ₀ ((x₀ : ℂ) + (t : ℂ) * I)).toNat = 0 :=
    fun t ht => by
      rw [(hΛ₀.analyticAt _).analyticOrderAt_eq_zero.mpr (hline t ht)]; rfl
  have h := total_zero_mass_le hD (fun u hu => by
    simp only [hzero u hu, Nat.cast_zero, zero_sub, neg_nonpos]
    exact Nat.cast_nonneg _) hZ
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  have hsum : ∑ z ∈ Z, -(((analyticOrderAt Λ₀ ((x₀ : ℂ) + (z : ℂ) * I)).toNat : ℝ) -
      (analyticOrderAt Λ ((x₀ : ℂ) + (z : ℂ) * I)).toNat) =
      ∑ z ∈ Z, ((analyticOrderAt Λ ((x₀ : ℂ) + (z : ℂ) * I)).toNat : ℝ) :=
    Finset.sum_congr rfl fun z hz => by rw [hzero z (hZ z hz).ne']; simp
  rw [hsum] at h
  linarith

end GaloisForLFunctions.BiarithmeticGaugeGeometry
