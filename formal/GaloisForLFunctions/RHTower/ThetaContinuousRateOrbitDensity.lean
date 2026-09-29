import GaloisForLFunctions.RHTower.ThetaCriticalBoundaryMellinCharge
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.RHTower.ThetaGaussianBaseCommutator

/-!
# Continuous Gaussian rates: the orbit is dense and its only annihilator is the flux weight

For `λ > 0` let `φ_λ(x) = 2λ e^{5x/2}(2λe^{2x} − 3) e^{−λe^{2x}}`.  For a logarithmic density `g`
in the rate-Laplace class (`∫ |g|² e^{3x} e^{−2δe^{2x}} < ∞` for all `δ > 0`, which contains
`L²(ℝ)` and the flux weight `e^{x/2}`) put

`T_k(s) = ∫ conj(g(x)) e^{kx} e^{−s e^{2x}} dx`,  `Re s > 0`.

`T_k` is holomorphic with `T_k' = −T_{k+2}`, and the pairing formula
`∫ conj(g) φ_λ = 2λ (2λ T_{9/2}(λ) − 3 T_{5/2}(λ)) = 2λ(−2λ T'_{5/2}(λ) − 3 T_{5/2}(λ))` holds.  If `g`
annihilates `φ_λ` for all `λ` in a nonempty open set `J` of positive rates, the identity theorem
propagates `2s T'_{5/2} + 3T_{5/2} = 0` to the half-plane, so `T_{5/2}(s) = c s^{−3/2}` on the positive
rates.  The half-line pullback `q(u) e^{−u}`, `q(u) = (1/2) u^{1/4} conj(g(log u/2))`, is square
integrable with Laplace transform `T_{5/2}(w+1)`; comparing with `u^{1/2} e^{−u}` and using Laplace
uniqueness gives `g = c e^{x/2}` almost everywhere.  Conversely `e^{x/2}` annihilates every `φ_λ`.

Since `e^{x/2} ∉ L²`, the atoms `{φ_λ : λ ∈ J}` span a dense subspace of `L²(ℝ)`.  For an
involutive isometry `R` the parity projections of a total family are total in the parity sector
`{R v = ε v}`; applied to the reflection `g(x) ↦ g(−x)`, the even and odd projections of the
continuous orbit are dense in their parity sectors.
-/

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The quadratic exponential chart `u = e^{2x}` -/

theorem image_univ_exp_two_mul : (fun x : ℝ => Real.exp (2 * x)) '' univ = Ioi 0 := by
  ext u
  simp only [image_univ, mem_range, mem_Ioi]
  refine ⟨fun ⟨x, hx⟩ => hx ▸ Real.exp_pos _, fun hu => ⟨Real.log u / 2, ?_⟩⟩
  rw [show 2 * (Real.log u / 2) = Real.log u by ring, Real.exp_log hu]

theorem injective_exp_two_mul : Function.Injective (fun x : ℝ => Real.exp (2 * x)) := fun a b h => by
  have := Real.exp_injective h
  linarith

/-- The substitution `u = e^{2x}` on the half-line. -/
theorem setIntegral_Ioi_zero_eq_integral_exp_two_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ u in Ioi (0 : ℝ), f u = ∫ x : ℝ, (2 * Real.exp (2 * x)) • f (Real.exp (2 * x)) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_exp_two_mul x).hasDerivWithinAt) injective_exp_two_mul.injOn f
  rw [image_univ_exp_two_mul, Measure.restrict_univ] at h
  rw [h]
  simp_rw [abs_of_pos (mul_pos two_pos (Real.exp_pos _))]

theorem integrableOn_Ioi_zero_iff_integrable_exp_two_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    IntegrableOn f (Ioi 0) ↔
      Integrable fun x : ℝ => (2 * Real.exp (2 * x)) • f (Real.exp (2 * x)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (hasDerivAt_exp_two_mul x).hasDerivWithinAt) injective_exp_two_mul.injOn f
  rw [image_univ_exp_two_mul, integrableOn_univ] at h
  rw [h]
  simp_rw [abs_of_pos (mul_pos two_pos (Real.exp_pos _))]

/-! ## Gaussian-rate weights -/

theorem integrable_exp_mul_exp_neg_mul_exp_two_mul {b σ : ℝ} (hb : 0 < b) (hσ : 0 < σ) :
    Integrable fun x : ℝ => Real.exp (b * x) * Real.exp (-(σ * Real.exp (2 * x))) := by
  have hf : IntegrableOn (fun u : ℝ => (1 / 2 : ℝ) * (u ^ (b / 2 - 1) * Real.exp (-σ * u ^ (1 : ℝ))))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) le_rfl hσ).const_mul _
  refine ((integrableOn_Ioi_zero_iff_integrable_exp_two_mul _).1 hf).congr
    (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul, Real.rpow_one]
  rw [← Real.exp_mul, show -σ * Real.exp (2 * x) = -(σ * Real.exp (2 * x)) by ring]
  have : Real.exp (2 * x) * Real.exp (2 * x * (b / 2 - 1)) = Real.exp (b * x) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination Real.exp (-(σ * Real.exp (2 * x))) * this

/-- `e^{3x} e^{−2δ e^{2x}} ≤ 1 + 1/(2δ²)`. -/
theorem exp_three_mul_mul_exp_neg_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    Real.exp (3 * x) * Real.exp (-(2 * δ * Real.exp (2 * x))) ≤ 1 + 1 / (2 * δ ^ 2) := by
  set u := Real.exp (2 * x) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have h3 : Real.exp (3 * x) ≤ 1 + u ^ 2 := by
    have h4 : u ^ 2 = Real.exp (4 * x) := by rw [hu, ← Real.exp_nat_mul]; norm_num; ring_nf
    rcases le_or_gt x 0 with h | h
    · have : Real.exp (3 * x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      nlinarith [sq_nonneg u]
    · rw [h4]
      have : Real.exp (3 * x) ≤ Real.exp (4 * x) := Real.exp_le_exp.2 (by linarith)
      linarith
  have hq := Real.quadratic_le_exp_of_nonneg (x := 2 * δ * u) (by positivity)
  have hE := Real.exp_pos (2 * δ * u)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
  have hδ2 : 0 < 2 * δ ^ 2 := by positivity
  calc Real.exp (3 * x) ≤ 1 + u ^ 2 := h3
    _ ≤ (1 + 1 / (2 * δ ^ 2)) * (1 + 2 * δ * u + (2 * δ * u) ^ 2 / 2) := by
      rw [show (1 + 1 / (2 * δ ^ 2)) * (1 + 2 * δ * u + (2 * δ * u) ^ 2 / 2) =
        1 + 2 * δ * u + 2 * δ ^ 2 * u ^ 2 + (1 + 2 * δ * u) / (2 * δ ^ 2) + u ^ 2 by
          field_simp; ring]
      have : 0 ≤ (1 + 2 * δ * u) / (2 * δ ^ 2) := by positivity
      nlinarith [sq_nonneg u]
    _ ≤ (1 + 1 / (2 * δ ^ 2)) * Real.exp (2 * δ * u) := by gcongr

/-! ## The Laplace class and the orbit transform -/

/-- A logarithmic density `g` is in the rate-Laplace class if it is strongly measurable and
`∫ |g|² e^{3x} e^{−2δ e^{2x}} dx < ∞` for every `δ > 0`. -/
structure IsRateLaplaceClass (g : ℝ → ℂ) : Prop where
  stronglyMeasurable : StronglyMeasurable g
  integrable : ∀ δ : ℝ, 0 < δ → Integrable fun x : ℝ =>
    ‖g x‖ ^ 2 * (Real.exp (3 * x) * Real.exp (-(2 * δ * Real.exp (2 * x))))

theorem IsRateLaplaceClass.integrable_norm_mul_rateWeight {g : ℝ → ℂ} (hg : IsRateLaplaceClass g) {a σ : ℝ}
    (ha : 3 / 2 < a) (hσ : 0 < σ) :
    Integrable fun x : ℝ => ‖g x‖ * (Real.exp (a * x) * Real.exp (-(σ * Real.exp (2 * x)))) := by
  set f₁ : ℝ → ℝ := fun x => ‖g x‖ * (Real.exp (3 / 2 * x) * Real.exp (-(σ / 2 * Real.exp (2 * x))))
  set f₂ : ℝ → ℝ := fun x => Real.exp ((a - 3 / 2) * x) * Real.exp (-(σ / 2 * Real.exp (2 * x)))
  have hm₁ : AEStronglyMeasurable f₁ := (hg.stronglyMeasurable.norm.aestronglyMeasurable).mul
    (by fun_prop : Continuous fun x : ℝ =>
      Real.exp (3 / 2 * x) * Real.exp (-(σ / 2 * Real.exp (2 * x)))).aestronglyMeasurable
  have hm₂ : AEStronglyMeasurable f₂ := (by fun_prop : Continuous f₂).aestronglyMeasurable
  have h₁ : MemLp f₁ 2 := by
    refine (memLp_two_iff_integrable_sq_norm hm₁).2 ((hg.integrable (σ / 2) (by linarith)).congr
      (ae_of_all _ fun x => ?_))
    simp only [f₁, Real.norm_eq_abs, abs_mul, abs_norm, abs_of_pos (Real.exp_pos _)]
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * (3 / 2 * x) = 3 * x by ring,
      show 2 * -(σ / 2 * Real.exp (2 * x)) = -(2 * (σ / 2) * Real.exp (2 * x)) by ring]
  have h₂ : MemLp f₂ 2 := by
    refine (memLp_two_iff_integrable_sq_norm hm₂).2
      ((integrable_exp_mul_exp_neg_mul_exp_two_mul (b := 2 * a - 3) (by linarith) hσ).congr
        (ae_of_all _ fun x => ?_))
    simp only [f₂, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  refine (h₁.integrable_mul h₂).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.mul_apply, f₁, f₂]
  have e1 : Real.exp (3 / 2 * x) * Real.exp ((a - 3 / 2) * x) = Real.exp (a * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(σ / 2 * Real.exp (2 * x))) * Real.exp (-(σ / 2 * Real.exp (2 * x))) =
      Real.exp (-(σ * Real.exp (2 * x))) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ‖g x‖ * (Real.exp (3 / 2 * x) * Real.exp (-(σ / 2 * Real.exp (2 * x)))) *
        (Real.exp ((a - 3 / 2) * x) * Real.exp (-(σ / 2 * Real.exp (2 * x))))
      = ‖g x‖ * ((Real.exp (3 / 2 * x) * Real.exp ((a - 3 / 2) * x)) *
        (Real.exp (-(σ / 2 * Real.exp (2 * x))) * Real.exp (-(σ / 2 * Real.exp (2 * x))))) := by ring
    _ = _ := by rw [e1, e2]

/-- The orbit integrand `conj(g(x)) e^{kx} e^{−s e^{2x}}`. -/
def rateOrbitIntegrand (g : ℝ → ℂ) (k : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  conj (g x) * ((Real.exp (k * x) : ℝ) : ℂ) * Complex.exp (-(s * (Real.exp (2 * x) : ℂ)))

/-- The orbit transform `∫ conj(g(x)) e^{kx} e^{−s e^{2x}} dx`. -/
def rateOrbitTransform (g : ℝ → ℂ) (k : ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, rateOrbitIntegrand g k s x

theorem norm_rateOrbitIntegrand (g : ℝ → ℂ) (k : ℝ) (s : ℂ) (x : ℝ) :
    ‖rateOrbitIntegrand g k s x‖ =
      ‖g x‖ * (Real.exp (k * x) * Real.exp (-(s.re * Real.exp (2 * x)))) := by
  rw [rateOrbitIntegrand, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
    Complex.norm_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  ring

theorem IsRateLaplaceClass.integrable_rateOrbitIntegrand {g : ℝ → ℂ} (hg : IsRateLaplaceClass g)
    {k : ℝ} (hk : 3 / 2 < k) {s : ℂ} (hs : 0 < s.re) :
    Integrable (rateOrbitIntegrand g k s) := by
  refine (hg.integrable_norm_mul_rateWeight hk hs).mono' ?_ (ae_of_all _ fun x => (norm_rateOrbitIntegrand g k s x).le)
  unfold rateOrbitIntegrand
  exact ((Complex.continuous_conj.comp_stronglyMeasurable hg.stronglyMeasurable).aestronglyMeasurable.mul
    (by fun_prop : Continuous fun x : ℝ => ((Real.exp (k * x) : ℝ) : ℂ)).aestronglyMeasurable).mul
    (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (-(s * (Real.exp (2 * x) : ℂ)))).aestronglyMeasurable

/-- **The orbit transform is holomorphic**, with `∂_s T_k = −T_{k+2}`. -/
theorem IsRateLaplaceClass.hasDerivAt_rateOrbitTransform {g : ℝ → ℂ} (hg : IsRateLaplaceClass g)
    {k : ℝ} (hk : 3 / 2 < k) {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    HasDerivAt (rateOrbitTransform g k) (-rateOrbitTransform g (k + 2) s₀) s₀ := by
  set σ := s₀.re / 2
  have hσ : 0 < σ := by positivity
  have hball : ∀ s ∈ Metric.ball s₀ σ, σ < s.re := fun s hs => by
    have h := (Complex.abs_re_le_norm (s - s₀)).trans_lt (by rwa [← dist_eq_norm])
    rw [Complex.sub_re] at h
    have := neg_abs_le (s.re - s₀.re)
    simp only [σ] at h ⊢; linarith
  have hmeas : ∀ (k : ℝ) (s : ℂ), AEStronglyMeasurable (rateOrbitIntegrand g k s) := fun k s => by
    unfold rateOrbitIntegrand
    exact ((Complex.continuous_conj.comp_stronglyMeasurable
      hg.stronglyMeasurable).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun x : ℝ => ((Real.exp (k * x) : ℝ) : ℂ)).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (-(s * (Real.exp (2 * x) : ℂ)))).aestronglyMeasurable
  have hderiv : ∀ x : ℝ, ∀ s : ℂ, HasDerivAt (fun s => rateOrbitIntegrand g k s x)
      (-rateOrbitIntegrand g (k + 2) s x) s := fun x s => by
    have h := (((hasDerivAt_id s).mul_const ((Real.exp (2 * x) : ℝ) : ℂ)).neg.cexp).const_mul
      (conj (g x) * ((Real.exp (k * x) : ℝ) : ℂ))
    refine h.congr_deriv ?_
    simp only [rateOrbitIntegrand, id, one_mul, Pi.neg_apply]
    rw [show (k + 2) * x = k * x + 2 * x by ring, Real.exp_add]
    push_cast
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s x => rateOrbitIntegrand g k s x)
    (F' := fun s x => -rateOrbitIntegrand g (k + 2) s x)
    (bound := fun x => ‖g x‖ * (Real.exp ((k + 2) * x) * Real.exp (-(σ * Real.exp (2 * x)))))
    (Metric.ball_mem_nhds s₀ hσ) (Eventually.of_forall (hmeas k))
    (hg.integrable_rateOrbitIntegrand hk hs₀) (hmeas (k + 2) s₀).neg
    (ae_of_all _ fun x s hs => by
      rw [norm_neg, norm_rateOrbitIntegrand]
      gcongr
      exact (hball s hs).le)
    (hg.integrable_norm_mul_rateWeight (by linarith) hσ) (ae_of_all _ fun x s _ => hderiv x s)
  have h3 := h.2
  rw [integral_neg] at h3
  exact h3

theorem IsRateLaplaceClass.differentiableOn_rateOrbitTransform {g : ℝ → ℂ}
    (hg : IsRateLaplaceClass g) {k : ℝ} (hk : 3 / 2 < k) :
    DifferentiableOn ℂ (rateOrbitTransform g k) {s : ℂ | 0 < s.re} := fun _ hs =>
  (hg.hasDerivAt_rateOrbitTransform hk hs).differentiableAt.differentiableWithinAt

/-- **Pairing formula (13).**  `∫ conj(g) φ_λ = 2λ (2λ T_{9/2}(λ) − 3 T_{5/2}(λ))`. -/
theorem IsRateLaplaceClass.integral_conj_mul_rateAtom {g : ℝ → ℂ} (hg : IsRateLaplaceClass g)
    {lam : ℝ} (hlam : 0 < lam) :
    (∫ x : ℝ, conj (g x) * (rateAtom lam x : ℂ)) =
      2 * lam * (2 * lam * rateOrbitTransform g (9 / 2) lam - 3 * rateOrbitTransform g (5 / 2) lam) := by
  have hs : 0 < (lam : ℂ).re := by simpa using hlam
  have h9 := hg.integrable_rateOrbitIntegrand (k := 9 / 2) (by norm_num) hs
  have h5 := hg.integrable_rateOrbitIntegrand (k := 5 / 2) (by norm_num) hs
  have hfun : (fun x : ℝ => conj (g x) * (rateAtom lam x : ℂ)) = fun x =>
      (4 * lam ^ 2 : ℂ) * rateOrbitIntegrand g (9 / 2) lam x -
        (6 * lam : ℂ) * rateOrbitIntegrand g (5 / 2) lam x := by
    funext x
    have e : Real.exp (9 / 2 * x) = Real.exp (5 * x / 2) * Real.exp (2 * x) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [rateOrbitIntegrand, rateAtom, e, show (5 : ℝ) / 2 * x = 5 * x / 2 by ring]
    push_cast
    rw [show -((lam : ℂ) * Complex.exp (2 * (x : ℂ))) = ((-(lam * Real.exp (2 * x)) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [hfun, integral_sub (h9.const_mul _) (h5.const_mul _), integral_const_mul, integral_const_mul]
  simp only [rateOrbitTransform]
  ring

/-! ## Propagation of the annihilation law and the homogeneity ODE -/

/-- A nonempty open set of positive rates accumulates at one of its points in `ℂ`. -/
theorem exists_frequently_ofReal_mem {J : Set ℝ} (hJo : IsOpen J) (hJne : J.Nonempty) :
    ∃ lam₀ ∈ J, ∀ {P : ℂ → Prop}, (∀ lam ∈ J, P (lam : ℂ)) → ∃ᶠ z in 𝓝[≠] (lam₀ : ℂ), P z := by
  obtain ⟨lam₀, hlam₀⟩ := hJne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJo lam₀ hlam₀
  refine ⟨lam₀, hlam₀, fun {P} hP => ?_⟩
  set u : ℕ → ℝ := fun n => lam₀ + ε / (n + 2)
  have hu0 : ∀ n : ℕ, 0 < ε / (n + 2) := fun n => by positivity
  have hmem : ∀ n, u n ∈ J := fun n => hball (by
    rw [Metric.mem_ball, Real.dist_eq, show u n - lam₀ = ε / (n + 2) by simp [u],
      abs_of_pos (hu0 n)]
    exact div_lt_self hε (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  have hlim : Tendsto (fun n => ((u n : ℝ) : ℂ)) atTop (𝓝[≠] (lam₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h : Tendsto u atTop (𝓝 (lam₀ + 0)) :=
        tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      rw [add_zero] at h
      exact (Complex.continuous_ofReal.tendsto _).comp h
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
      have := hu0 n
      simp only [u]; linarith
  exact hlim.frequently (Eventually.of_forall fun n => hP _ (hmem n)).frequently

/-- **Homogeneity of the orbit transform.**  If `g` annihilates `φ_λ` for all `λ` in a nonempty
open set of positive rates, then `3 T_{5/2}(s) = 2s T_{9/2}(s)` on the whole half-plane. -/
theorem IsRateLaplaceClass.three_mul_eq_of_annihilates {g : ℝ → ℂ} (hg : IsRateLaplaceClass g)
    {J : Set ℝ} (hJo : IsOpen J) (hJne : J.Nonempty) (hJpos : J ⊆ Ioi 0)
    (h0 : ∀ lam ∈ J, (∫ x : ℝ, conj (g x) * (rateAtom lam x : ℂ)) = 0) {s : ℂ} (hs : 0 < s.re) :
    3 * rateOrbitTransform g (5 / 2) s = 2 * s * rateOrbitTransform g (9 / 2) s := by
  set H : ℂ → ℂ := fun z => 3 * rateOrbitTransform g (5 / 2) z - 2 * z * rateOrbitTransform g (9 / 2) z
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hH : AnalyticOnNhd ℂ H {s : ℂ | 0 < s.re} :=
    (((hg.differentiableOn_rateOrbitTransform (k := 5 / 2) (by norm_num)).const_mul 3).sub
      ((differentiableOn_id.const_mul 2).mul
        (hg.differentiableOn_rateOrbitTransform (k := 9 / 2) (by norm_num)))).analyticOnNhd hU
  obtain ⟨lam₀, hlam₀, hfreq⟩ := exists_frequently_ofReal_mem hJo hJne
  have hzero : ∀ lam ∈ J, H lam = 0 := fun lam hlam => by
    have hpos : 0 < lam := hJpos hlam
    have hp := hg.integral_conj_mul_rateAtom hpos
    rw [h0 lam hlam] at hp
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    simp only [H]
    have : 2 * (lam : ℂ) * (2 * lam * rateOrbitTransform g (9 / 2) lam -
        3 * rateOrbitTransform g (5 / 2) lam) = 0 := hp.symm
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hl)
    · linear_combination -h
  have hEq := hH.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
    (show 0 < (lam₀ : ℂ).re by simpa using hJpos hlam₀) (hfreq hzero)
  have := hEq hs
  simp only [H, Pi.zero_apply] at this
  linear_combination this

/-- **The orbit transform is homogeneous of degree `−3/2`** on the positive rates:
`T_{5/2}(s) = T_{5/2}(1) s^{−3/2}`. -/
theorem IsRateLaplaceClass.rateOrbitTransform_eq_of_annihilates {g : ℝ → ℂ}
    (hg : IsRateLaplaceClass g) {J : Set ℝ} (hJo : IsOpen J) (hJne : J.Nonempty)
    (hJpos : J ⊆ Ioi 0) (h0 : ∀ lam ∈ J, (∫ x : ℝ, conj (g x) * (rateAtom lam x : ℂ)) = 0)
    {s : ℝ} (hs : 0 < s) :
    rateOrbitTransform g (5 / 2) s =
      rateOrbitTransform g (5 / 2) 1 * ((s ^ (-(3 / 2) : ℝ) : ℝ) : ℂ) := by
  set K : ℝ → ℂ := fun t => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * rateOrbitTransform g (5 / 2) t
  have hK : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt K 0 t := fun t ht => by
    have ht' : 0 < t := ht
    have hT := (hg.hasDerivAt_rateOrbitTransform (k := 5 / 2) (by norm_num)
      (show 0 < (t : ℂ).re by simpa using ht')).comp_ofReal
    have hP := (Real.hasDerivAt_rpow_const (p := 3 / 2) (Or.inl ht'.ne')).ofReal_comp
    have h := hP.mul hT
    refine h.congr_deriv ?_
    have hode := hg.three_mul_eq_of_annihilates hJo hJne hJpos h0
      (show 0 < (t : ℂ).re by simpa using ht')
    have hsplit : t ^ (3 / 2 : ℝ) = t * t ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht', Real.rpow_one]
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, hsplit, show (5 / 2 : ℝ) + 2 = 9 / 2 by norm_num]
    push_cast
    linear_combination (((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) / 2) * hode
  have hconst := IsOpen.is_const_of_deriv_eq_zero (f := K) isOpen_Ioi isPreconnected_Ioi
    (fun t ht => (hK t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hK t ht).deriv) (show s ∈ Ioi (0 : ℝ) from hs) (show (1 : ℝ) ∈ Ioi (0 : ℝ) from mem_Ioi.2 one_pos)
  simp only [K, Real.one_rpow, Complex.ofReal_one, one_mul] at hconst
  have hne : ((s ^ (3 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hs _).ne'
  rw [← hconst, Real.rpow_neg hs.le]
  push_cast
  field_simp

/-! ## The half-line pullback and Laplace uniqueness -/

/-- The damped half-line pullback `q(u) e^{−u} = (1/2) u^{1/4} e^{−u} conj(g(log u / 2))`. -/
def ratePullback (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  (((1 / 2 : ℝ) * u ^ (1 / 4 : ℝ) * Real.exp (-u) : ℝ) : ℂ) * conj (g (Real.log u / 2))

theorem ratePullback_exp_two_mul (g : ℝ → ℂ) (x : ℝ) :
    ratePullback g (Real.exp (2 * x)) =
      (((1 / 2 : ℝ) * Real.exp (x / 2) * Real.exp (-Real.exp (2 * x)) : ℝ) : ℂ) * conj (g x) := by
  rw [ratePullback, Real.log_exp, show 2 * x / 2 = x by ring, ← Real.exp_mul,
    show 2 * x * (1 / 4 : ℝ) = x / 2 by ring]

theorem IsRateLaplaceClass.memLp_ratePullback {g : ℝ → ℂ} (hg : IsRateLaplaceClass g) :
    MemLp (ratePullback g) 2 (volume.restrict (Ioi 0)) := by
  have hm : AEStronglyMeasurable (ratePullback g) (volume.restrict (Ioi 0)) := by
    unfold ratePullback
    refine (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable.mul ?_
    exact (Complex.continuous_conj.comp_stronglyMeasurable
      (hg.stronglyMeasurable.comp_measurable (Real.measurable_log.div_const 2))).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine (integrableOn_Ioi_zero_iff_integrable_exp_two_mul _).2 (((hg.integrable 1 one_pos).const_mul
    (1 / 2)).congr (ae_of_all _ fun x => ?_))
  simp only [smul_eq_mul, ratePullback_exp_two_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul,
    ← Real.exp_nat_mul]
  have e : Real.exp (2 * x) * Real.exp ((2 : ℕ) * (x / 2)) = Real.exp (3 * x) := by
    rw [← Real.exp_add]; push_cast; ring_nf
  have e2 : Real.exp ((2 : ℕ) * -Real.exp (2 * x)) = Real.exp (-(2 * 1 * Real.exp (2 * x))) := by
    push_cast; ring_nf
  rw [e2]
  linear_combination (1 / 2 * ‖g x‖ ^ 2 * Real.exp (-(2 * 1 * Real.exp (2 * x)))) * e.symm

/-- `L[q e^{−u}](w) = T_{5/2}(w + 1)`. -/
theorem laplaceRay_ratePullback (g : ℝ → ℂ) (w : ℂ) :
    GaloisForLFunctions.HTGeometry.laplaceRay (ratePullback g) w =
      rateOrbitTransform g (5 / 2) (w + 1) := by
  rw [GaloisForLFunctions.HTGeometry.laplaceRay, setIntegral_Ioi_zero_eq_integral_exp_two_mul,
    rateOrbitTransform]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [GaloisForLFunctions.HTGeometry.expRay, ratePullback_exp_two_mul, rateOrbitIntegrand,
    Complex.real_smul]
  have e : Complex.exp (2 * (x : ℂ)) * Complex.exp ((x : ℂ) / 2) = Complex.exp (5 / 2 * (x : ℂ)) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : Complex.exp ((-Real.exp (2 * x) : ℝ)) * Complex.exp (-(w * (Real.exp (2 * x) : ℂ))) =
      Complex.exp (-((w + 1) * (Real.exp (2 * x) : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  push_cast at e2 ⊢
  rw [← e, ← e2]
  ring

/-- The comparison profile `u^{1/2} e^{−u}`, the pullback of the flux weight `e^{x/2}`. -/
def halfPowerDamped (u : ℝ) : ℂ := ((u ^ (1 / 2 : ℝ) * Real.exp (-u) : ℝ) : ℂ)

theorem memLp_halfPowerDamped : MemLp halfPowerDamped 2 (volume.restrict (Ioi 0)) := by
  have hm : AEStronglyMeasurable halfPowerDamped (volume.restrict (Ioi 0)) :=
    (Complex.measurable_ofReal.comp (by fun_prop)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 2) (by norm_num) le_rfl
    two_pos
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  have hu' : (0 : ℝ) < u := hu
  simp only [halfPowerDamped, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
  rw [sq_abs, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hu'.le, ← Real.exp_nat_mul]
  norm_num

theorem laplaceRay_halfPowerDamped {w : ℝ} (hw : -1 < w) :
    GaloisForLFunctions.HTGeometry.laplaceRay halfPowerDamped w =
      (((1 + w) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * Complex.Gamma (3 / 2) := by
  have hr : (0 : ℝ) < 1 + w := by linarith
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := 3 / 2) (r := 1 + w) (by norm_num) hr
  rw [GaloisForLFunctions.HTGeometry.laplaceRay]
  rw [one_div_cpow_eq hr, show -(3 / 2 : ℂ) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hr.le] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : (0 : ℝ) < u := hu
  simp only [halfPowerDamped, GaloisForLFunctions.HTGeometry.expRay]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu'.le, Complex.ofReal_exp, mul_assoc,
    ← Complex.exp_add, show (3 / 2 : ℂ) - 1 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  congr 2
  push_cast
  ring

/-- **Generalized annihilators.**  In the rate-Laplace class, a density annihilating `φ_λ` for
all `λ` in a nonempty open set of positive rates is a multiple of the flux weight `e^{x/2}`. -/
theorem IsRateLaplaceClass.exists_ae_eq_const_mul_exp_half {g : ℝ → ℂ} (hg : IsRateLaplaceClass g)
    {J : Set ℝ} (hJo : IsOpen J) (hJne : J.Nonempty) (hJpos : J ⊆ Ioi 0)
    (h0 : ∀ lam ∈ J, (∫ x : ℝ, conj (g x) * (rateAtom lam x : ℂ)) = 0) :
    ∃ c : ℂ, ∀ᵐ x ∂volume, g x = c * Real.exp (x / 2) := by
  set c₀ := rateOrbitTransform g (5 / 2) 1
  have hΓ : Complex.Gamma (3 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  set c₁ := c₀ / Complex.Gamma (3 / 2)
  set ψ : ℝ → ℂ := fun u => ratePullback g u - c₁ * halfPowerDamped u
  have hψ : MemLp ψ 2 (volume.restrict (Ioi 0)) :=
    hg.memLp_ratePullback.sub (memLp_halfPowerDamped.const_mul c₁)
  have hL : ∀ w : ℂ, 0 < w.re → GaloisForLFunctions.HTGeometry.laplaceRay ψ w =
      GaloisForLFunctions.HTGeometry.laplaceRay (ratePullback g) w -
        c₁ * GaloisForLFunctions.HTGeometry.laplaceRay halfPowerDamped w := fun w hw => by
    simp only [GaloisForLFunctions.HTGeometry.laplaceRay, ψ, sub_mul, mul_assoc]
    rw [integral_sub (GaloisForLFunctions.HTGeometry.integrableOn_laplaceRay hg.memLp_ratePullback hw)
      ((GaloisForLFunctions.HTGeometry.integrableOn_laplaceRay memLp_halfPowerDamped hw).const_mul c₁),
      integral_const_mul]
  have hreal : ∀ w : ℝ, 0 < w → GaloisForLFunctions.HTGeometry.laplaceRay ψ w = 0 := fun w hw => by
    rw [hL w (by simpa using hw), laplaceRay_ratePullback, laplaceRay_halfPowerDamped (by linarith),
      show (w : ℂ) + 1 = ((w + 1 : ℝ) : ℂ) by push_cast; ring,
      hg.rateOrbitTransform_eq_of_annihilates hJo hJne hJpos h0 (by linarith : (0 : ℝ) < w + 1)]
    simp only [c₁]
    rw [add_comm w 1]
    field_simp
    ring
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA := (GaloisForLFunctions.HTGeometry.differentiableOn_laplaceRay hψ).analyticOnNhd hU
  obtain ⟨w₀, hw₀, hfreq⟩ := exists_frequently_ofReal_mem (J := Ioi 0) isOpen_Ioi
    ⟨1, mem_Ioi.2 one_pos⟩
  have hEq := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_halfSpace_re_gt 0).isPreconnected
    (show 0 < (w₀ : ℂ).re by simpa using hw₀) (hfreq fun w hw => hreal w hw)
  have hae := GaloisForLFunctions.HTGeometry.ae_eq_zero_of_laplaceRay_eq_zero hψ fun w hw => hEq hw
  -- transfer the half-line vanishing to the logarithmic line
  have hint0 : (∫ u in Ioi (0 : ℝ), ‖ψ u‖ ^ 2) = 0 := by
    refine (setIntegral_congr_ae measurableSet_Ioi ?_).trans (integral_zero _ _)
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hae] with u hu hu'
    simp [hu hu']
  have hsq : IntegrableOn (fun u => ‖ψ u‖ ^ 2) (Ioi 0) :=
    (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).1 hψ
  rw [setIntegral_Ioi_zero_eq_integral_exp_two_mul] at hint0
  have hnn : 0 ≤ fun x : ℝ => (2 * Real.exp (2 * x)) • ‖ψ (Real.exp (2 * x))‖ ^ 2 := fun x => by
    simp only [Pi.zero_apply, smul_eq_mul]; positivity
  have hzero := (integral_eq_zero_iff_of_nonneg hnn
    ((integrableOn_Ioi_zero_iff_integrable_exp_two_mul _).1 hsq)).1 hint0
  refine ⟨conj (2 * c₁), ?_⟩
  filter_upwards [hzero] with x hx
  have hx' : ψ (Real.exp (2 * x)) = 0 := by
    have hpos : 0 < 2 * Real.exp (2 * x) := by positivity
    simp only [Pi.zero_apply, smul_eq_mul] at hx
    have hsq0 : ‖ψ (Real.exp (2 * x))‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hx with h | h
      · linarith
      · exact h
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq0)
  simp only [ψ, ratePullback_exp_two_mul, halfPowerDamped, sub_eq_zero] at hx'
  rw [← Real.exp_mul, show 2 * x * (1 / 2 : ℝ) = x by ring] at hx'
  have hpos : ((1 / 2 : ℝ) * Real.exp (x / 2) * Real.exp (-Real.exp (2 * x)) : ℝ) ≠ 0 := by positivity
  have hconj : conj (g x) = 2 * c₁ * Real.exp (x / 2) := by
    have e : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpos' : (((1 / 2 : ℝ) * Real.exp (x / 2) * Real.exp (-Real.exp (2 * x)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos
    apply mul_left_cancel₀ hpos'
    rw [hx', e]
    push_cast
    ring
  have := congrArg conj hconj
  rw [Complex.conj_conj] at this
  rw [this, map_mul, map_mul, Complex.conj_ofReal, map_ofNat]

/-! ## The flux weight is the only generalized annihilator -/

theorem not_integrable_exp : ¬ Integrable fun x : ℝ => Real.exp x := fun h => by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) :=
    h.integrableOn.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun x hx => by
        rw [Real.norm_eq_abs, abs_one]
        exact Real.one_le_exp (le_of_lt hx)))
  rw [integrableOn_const_iff] at h1
  simp [Real.volume_Ioi] at h1

/-- The flux weight `e^{x/2}` is in the rate-Laplace class. -/
theorem isRateLaplaceClass_exp_half :
    IsRateLaplaceClass fun x : ℝ => ((Real.exp (x / 2) : ℝ) : ℂ) := by
  refine ⟨(by fun_prop : Continuous fun x : ℝ => ((Real.exp (x / 2) : ℝ) : ℂ)).stronglyMeasurable,
    fun δ hδ => ((integrable_exp_mul_exp_neg_mul_exp_two_mul (b := 4) (by norm_num)
      (by positivity : 0 < 2 * δ))).congr (ae_of_all _ fun x => ?_)⟩
  dsimp only
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul,
    ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- `e^{x/2}` annihilates every Gaussian-rate atom, but is not square integrable. -/
theorem integral_exp_half_mul_rateAtom {lam : ℝ} (hlam : 0 < lam) :
    (∫ x : ℝ, conj (((Real.exp (x / 2) : ℝ) : ℂ)) * (rateAtom lam x : ℂ)) = 0 := by
  have h := (integral_exp_mul_rateAtom hlam (a := 1 / 2) (by norm_num)).2
  rw [rateMellin_half] at h
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, show (fun x : ℝ => Real.exp (x / 2) * rateAtom lam x) =
    fun x => Real.exp (1 / 2 * x) * rateAtom lam x by funext x; ring_nf, h, Complex.ofReal_zero]

theorem not_memLp_exp_half : ¬ MemLp (fun x : ℝ => ((Real.exp (x / 2) : ℝ) : ℂ)) 2 := fun h => by
  have hi := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  refine not_integrable_exp (hi.congr (ae_of_all _ fun x => ?_))
  dsimp only
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Generalized annihilators, both directions.**  In the rate-Laplace class the annihilators of
the continuous orbit `{φ_λ : λ ∈ J}` are exactly the multiples of `e^{x/2}`. -/
theorem IsRateLaplaceClass.annihilates_iff {g : ℝ → ℂ} (hg : IsRateLaplaceClass g) {J : Set ℝ}
    (hJo : IsOpen J) (hJne : J.Nonempty) (hJpos : J ⊆ Ioi 0) :
    (∀ lam ∈ J, (∫ x : ℝ, conj (g x) * (rateAtom lam x : ℂ)) = 0) ↔
      ∃ c : ℂ, ∀ᵐ x ∂volume, g x = c * Real.exp (x / 2) := by
  refine ⟨hg.exists_ae_eq_const_mul_exp_half hJo hJne hJpos, fun ⟨c, hc⟩ lam hlam => ?_⟩
  rw [integral_congr_ae (hc.mono fun x hx => by rw [hx])]
  simp_rw [map_mul, mul_assoc]
  rw [integral_const_mul, integral_exp_half_mul_rateAtom (hJpos hlam), mul_zero]

/-! ## Density of the continuous orbit in `L²` -/

theorem integrable_rateAtom_sq {lam : ℝ} (hlam : 0 < lam) :
    Integrable fun x : ℝ => rateAtom lam x ^ 2 := by
  have h9 := integrable_exp_mul_exp_neg_mul_exp_two_mul (b := 9) (by norm_num)
    (by positivity : 0 < 2 * lam)
  have h7 := integrable_exp_mul_exp_neg_mul_exp_two_mul (b := 7) (by norm_num)
    (by positivity : 0 < 2 * lam)
  have h5 := integrable_exp_mul_exp_neg_mul_exp_two_mul (b := 5) (by norm_num)
    (by positivity : 0 < 2 * lam)
  refine (((h9.const_mul (16 * lam ^ 4)).sub (h7.const_mul (48 * lam ^ 3))).add
    (h5.const_mul (36 * lam ^ 2))).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, rateAtom]
  have e9 : Real.exp (9 * x) = Real.exp (5 * x / 2) ^ 2 * Real.exp (2 * x) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have e7 : Real.exp (7 * x) = Real.exp (5 * x / 2) ^ 2 * Real.exp (2 * x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  have e5 : Real.exp (5 * x) = Real.exp (5 * x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have eE : Real.exp (-(2 * lam * Real.exp (2 * x))) = Real.exp (-(lam * Real.exp (2 * x))) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [e9, e7, e5, eE]
  ring

theorem memLp_rateAtom {lam : ℝ} (hlam : 0 < lam) :
    MemLp (fun x : ℝ => (rateAtom lam x : ℂ)) 2 := by
  refine (memLp_two_iff_integrable_sq_norm (Complex.continuous_ofReal.comp
    (continuous_rateAtom lam)).aestronglyMeasurable).2 ((integrable_rateAtom_sq hlam).congr
      (ae_of_all _ fun x => ?_))
  simp [Complex.norm_real, sq_abs]

/-- The Gaussian-rate atom `φ_λ ∈ L²(ℝ)`. -/
def rateAtomLp {lam : ℝ} (hlam : 0 < lam) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_rateAtom hlam).toLp _

/-- Every `L²` density is in the rate-Laplace class. -/
theorem isRateLaplaceClass_Lp (g : Lp ℂ 2 (volume : Measure ℝ)) : IsRateLaplaceClass g := by
  refine ⟨Lp.stronglyMeasurable g, fun δ hδ => ?_⟩
  have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  exact hsq.mul_bdd (by fun_prop : Continuous fun x : ℝ =>
    Real.exp (3 * x) * Real.exp (-(2 * δ * Real.exp (2 * x)))).aestronglyMeasurable
    (c := 1 + 1 / (2 * δ ^ 2)) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact exp_three_mul_mul_exp_neg_le hδ x)

/-- **(12) Continuous dilation erases the arithmetic selector.**  For every nonempty open set `J`
of positive rates, the atoms `{φ_λ : λ ∈ J}` span a dense subspace of `L²(ℝ)`. -/
theorem topologicalClosure_span_rateAtomLp {J : Set ℝ} (hJo : IsOpen J) (hJne : J.Nonempty)
    (hJpos : J ⊆ Ioi 0) :
    (Submodule.span ℂ (range fun lam : J => rateAtomLp (hJpos lam.2))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have h0 : ∀ lam ∈ J, (∫ x : ℝ, conj (g x) * (rateAtom lam x : ℂ)) = 0 := fun lam hlam => by
    have hi := hg _ (Submodule.subset_span ⟨⟨lam, hlam⟩, rfl⟩)
    rw [MeasureTheory.L2.inner_def] at hi
    have hc : (∫ x : ℝ, conj (g x) * (rateAtom lam x : ℂ)) =
        conj (∫ x : ℝ, inner ℂ ((rateAtomLp (hJpos hlam) : ℝ → ℂ) x) (g x)) := by
      rw [← integral_conj]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_rateAtom (hJpos hlam)).coeFn_toLp] with x hx
      simp only [rateAtomLp] at *
      rw [hx, RCLike.inner_apply, map_mul, Complex.conj_conj]
    rw [hc, hi, map_zero]
  obtain ⟨c, hc⟩ := (isRateLaplaceClass_Lp g).exists_ae_eq_const_mul_exp_half hJo hJne hJpos h0
  have hc0 : c = 0 := by
    by_contra hne
    apply not_memLp_exp_half
    have hm : MemLp (fun x => c⁻¹ * (g x)) 2 := (Lp.memLp g).const_mul c⁻¹
    refine hm.ae_eq (hc.mono fun x hx => ?_)
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hc] with x hx
  rw [hx, hc0, zero_mul, Pi.zero_apply]

/-! ## Parity sectors -/

section Parity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The parity projection `P_ε v = (v + ε R v)/2` of an involutive isometry `R`. -/
def parityProjection (R : E →ₗᵢ[ℂ] E) (ε : ℝ) (v : E) : E := (1 / 2 : ℂ) • (v + (ε : ℂ) • R v)

/-- The parity sector `{v : R v = ε v}` of an involutive isometry. -/
def paritySector (R : E →ₗᵢ[ℂ] E) (ε : ℝ) : Submodule ℂ E :=
  LinearMap.ker ((R.toContinuousLinearMap - (ε : ℂ) • ContinuousLinearMap.id ℂ E : E →L[ℂ] E) :
    E →ₗ[ℂ] E)

theorem mem_paritySector {R : E →ₗᵢ[ℂ] E} {ε : ℝ} {v : E} :
    v ∈ paritySector R ε ↔ R v = (ε : ℂ) • v := by
  rw [paritySector, LinearMap.mem_ker]
  change R v - (ε : ℂ) • v = 0 ↔ _
  exact sub_eq_zero

theorem inner_map_involution (R : E →ₗᵢ[ℂ] E) (hR : ∀ v, R (R v) = v) (u w : E) :
    inner ℂ u (R w) = inner ℂ (R u) w := by
  rw [← R.inner_map_map u (R w), hR]

theorem inner_parityProjection (R : E →ₗᵢ[ℂ] E) (hR : ∀ v, R (R v) = v) (ε : ℝ) (u w : E) :
    inner ℂ u (parityProjection R ε w) = inner ℂ (parityProjection R ε u) w := by
  simp only [parityProjection, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_map_involution R hR, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]

theorem parityProjection_mem (R : E →ₗᵢ[ℂ] E) (hR : ∀ v, R (R v) = v) {ε : ℝ} (hε : ε ^ 2 = 1)
    (v : E) : parityProjection R ε v ∈ paritySector R ε := by
  have hε' : (ε : ℂ) * ε = 1 := by exact_mod_cast (by nlinarith : ε * ε = 1)
  rw [mem_paritySector, parityProjection, map_smul, map_add, map_smul, hR,
    smul_comm (ε : ℂ) (1 / 2 : ℂ) (v + (ε : ℂ) • R v), smul_add (ε : ℂ) v, smul_smul, hε', one_smul,
    add_comm (R v)]

theorem parityProjection_of_mem {R : E →ₗᵢ[ℂ] E} {ε : ℝ} (hε : ε ^ 2 = 1) {v : E}
    (hv : v ∈ paritySector R ε) : parityProjection R ε v = v := by
  rw [mem_paritySector] at hv
  rw [parityProjection, hv, smul_smul]
  have hε' : (ε : ℂ) * ε = 1 := by exact_mod_cast (by nlinarith : ε * ε = 1)
  rw [hε', one_smul, ← two_smul ℂ v, smul_smul]
  norm_num

/-- **Parity projections of a total family are total in their sector.**  If `S` spans a dense
subspace and `R` is an involutive isometry, then `P_ε S` spans a dense subspace of the parity
sector `{R v = ε v}`, `ε = ±1`. -/
theorem topologicalClosure_span_parityProjection [CompleteSpace E] (R : E →ₗᵢ[ℂ] E) (hR : ∀ v, R (R v) = v)
    {ε : ℝ} (hε : ε ^ 2 = 1) {S : Set E} (hS : (Submodule.span ℂ S).topologicalClosure = ⊤) :
    (Submodule.span ℂ (parityProjection R ε '' S)).topologicalClosure = paritySector R ε := by
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
      (ContinuousLinearMap.isClosed_ker _)
    rintro _ ⟨v, _, rfl⟩
    exact parityProjection_mem R hR hε v
  · intro v hv
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have hS' := (Submodule.topologicalClosure_eq_top_iff).1 hS
    have hPw : parityProjection R ε w ∈ (Submodule.span ℂ S)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        rw [inner_parityProjection R hR]
        exact hw _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      | zero => exact inner_zero_left _
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
    rw [hS', Submodule.mem_bot] at hPw
    rw [← parityProjection_of_mem hε hv, inner_parityProjection R hR, hPw, inner_zero_left]

end Parity

/-- The parity reflection `(Rg)(x) = g(−x)` on `L²(ℝ)`. -/
def parityReflectionLp : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => -x) (Measure.measurePreserving_neg volume)

theorem coeFn_parityReflectionLp (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (parityReflectionLp g : ℝ → ℂ) =ᵐ[volume] fun x => g (-x) :=
  Lp.coeFn_compMeasurePreserving g _

theorem parityReflectionLp_involutive (g : Lp ℂ 2 (volume : Measure ℝ)) :
    parityReflectionLp (parityReflectionLp g) = g := by
  refine Lp.ext ?_
  have h1 := coeFn_parityReflectionLp (parityReflectionLp g)
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (coeFn_parityReflectionLp g)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  simpa using hx2

/-- Membership in a parity sector of `L²(ℝ)` is the pointwise parity law `g(−x) = ε g(x)`. -/
theorem mem_paritySector_parityReflectionLp {ε : ℝ} {g : Lp ℂ 2 (volume : Measure ℝ)} :
    g ∈ paritySector parityReflectionLp ε ↔ ∀ᵐ x ∂volume, g (-x) = (ε : ℂ) * g x := by
  rw [mem_paritySector]
  constructor
  · intro h
    filter_upwards [coeFn_parityReflectionLp g, Lp.coeFn_smul (ε : ℂ) g,
      (show (parityReflectionLp g : ℝ → ℂ) =ᵐ[volume] ((ε : ℂ) • g : Lp ℂ 2 volume) by rw [h])]
      with x h1 h2 h3
    rw [← h1, h3, h2, Pi.smul_apply, smul_eq_mul]
  · intro h
    refine Lp.ext ?_
    filter_upwards [coeFn_parityReflectionLp g, Lp.coeFn_smul (ε : ℂ) g, h] with x h1 h2 h3
    rw [h1, h2, h3, Pi.smul_apply, smul_eq_mul]

/-- The parity projection of `φ_λ` is `(φ_λ(x) + ε φ_λ(−x))/2`. -/
theorem coeFn_parityProjection_rateAtomLp {lam : ℝ} (hlam : 0 < lam) (ε : ℝ) :
    ((parityProjection parityReflectionLp ε (rateAtomLp hlam) : Lp ℂ 2 (volume : Measure ℝ)) :
      ℝ → ℂ) =ᵐ[volume]
      fun x => (1 / 2 : ℂ) * ((rateAtom lam x : ℂ) + ε * rateAtom lam (-x)) := by
  have hφ := (memLp_rateAtom hlam).coeFn_toLp
  have hφneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    hφ
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (rateAtomLp hlam + (ε : ℂ) • parityReflectionLp
      (rateAtomLp hlam)), Lp.coeFn_add (rateAtomLp hlam) ((ε : ℂ) • parityReflectionLp
      (rateAtomLp hlam)), Lp.coeFn_smul (ε : ℂ) (parityReflectionLp (rateAtomLp hlam)),
    coeFn_parityReflectionLp (rateAtomLp hlam), hφ, hφneg] with x h1 h2 h3 h4 h5 h6
  simp only [rateAtomLp] at *
  rw [parityProjection, h1, Pi.smul_apply, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul, smul_eq_mul]
  simp only [Function.comp] at h6
  rw [h6]

/-- **Parity sectors.**  For `ε = ±1`, the parity projections `(φ_λ(x) + ε φ_λ(−x))/2`, `λ ∈ J`,
span a dense subspace of the parity sector `{g ∈ L²(ℝ) : g(−x) = ε g(x)}`. -/
theorem topologicalClosure_span_parityProjection_rateAtomLp {J : Set ℝ} (hJo : IsOpen J)
    (hJne : J.Nonempty) (hJpos : J ⊆ Ioi 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (Submodule.span ℂ (parityProjection parityReflectionLp ε ''
      range fun lam : J => rateAtomLp (hJpos lam.2))).topologicalClosure =
        paritySector parityReflectionLp ε :=
  topologicalClosure_span_parityProjection parityReflectionLp parityReflectionLp_involutive
    (by rcases hε with rfl | rfl <;> norm_num) (topologicalClosure_span_rateAtomLp hJo hJne hJpos)

end

end RHTower
