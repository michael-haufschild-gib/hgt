import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilRealRootedGroundState

/-!
# Positive quadrature of the restricted Weil form at ground-state zeros

For a positive aperture `a`, let `μ_a` be the polar ground energy and
`E(u, v) = ∫ (S_a − μ_a) f̂_u conj(f̂_v)` the excess form on the CCM form domain
(`excessForm`).  On polar vectors `E(u, u) = Q(u) − μ_a ‖J u‖² ≥ 0`.

**Theorems.**
* Euler–Lagrange identity (`excessForm_eq_zero_of_ground`): a polar ground state `u` satisfies
  `E(v, u) = 0` for every polar vector `v`.
* Zero-quotient orthogonality (`excessForm_zeroQuotient_orthogonal`): if `x₁ ≠ x₂` are real zeros
  of `f̂_u`, the form-domain vectors `h_i` with `f̂_{h_i} = f̂_u/(w − x_i)` satisfy
  `E(h₁, h₂) = 0`.
* Positive quadrature (`quadrature_le`, `exists_realRooted_quadrature`): for distinct real zeros
  `x_i` of `f̂_u` with `f̂_{h_i}(x_i) ≠ 0`, every polar vector `g` satisfies
  `Σ_i ρ_i |f̂_g(x_i)|² ≤ Q(g) − μ_a ‖J g‖²`, `ρ_i = E(h_i, h_i)/|f̂_{h_i}(x_i)|² ≥ 0`.  For a
  real-rooted ground state, the restricted Weil form dominates `μ_a ‖J ·‖²` plus a positive
  sampling form at the real zeros of the ground state: the continuous form of the
  Carathéodory–Fejér–Pisarenko decomposition of a degenerate positive Toeplitz form.

**Proof.**  If `f̂_g(x) = 0`, division (`exists_div`) writes `f̂_g = (w − x) f̂_k` with `k` polar;
since `ξ − x` is real on the line, `E(g, h) = E(k, u) = 0`.  Applied to `g − c_i h_i` with
`c_i = f̂_g(x_i)/f̂_{h_i}(x_i)`, this gives `E(r, h_i) = 0` for `r = g − Σ c_i h_i`, so
`E(g, g) = E(r, r) + Σ |c_i|² E(h_i, h_i) ≥ Σ |c_i|² E(h_i, h_i)`.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate

namespace RHTower.CCMGroundQuadrature

open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround

variable (a : SuzukiPositiveAperture)

/-- The excess symbol `S_a − μ_a`. -/
def excessSymbol (ξ : ℝ) : ℝ := levelSymbol a ξ - ccmRestrictedWeilPolarGroundEnergy a

/-- Evaluation of the Fourier–Laplace transform at `w`, as a linear functional. -/
def evalAt (w : ℂ) : CCMArchimedeanFormDomain a →ₗ[ℂ] ℂ where
  toFun u := unitaryLaplace (timeRep a u) w
  map_add' u v := by
    have h := unitaryLaplace_timeRep_add_smul a u v 1 w
    rw [one_smul, one_mul] at h
    exact h
  map_smul' c u := unitaryLaplace_timeRep_smul a u c w

theorem evalAt_apply (w : ℂ) (u : CCMArchimedeanFormDomain a) :
    evalAt a w u = unitaryLaplace (timeRep a u) w := rfl

theorem polarize (s : ℝ) (x y : ℂ) :
    (s : ℂ) * (x * conj y) = (1 / 4 : ℂ) * (((s * ‖x + 1 * y‖ ^ 2 : ℝ) : ℂ) -
      ((s * ‖x + (-1) * y‖ ^ 2 : ℝ) : ℂ) + I * ((s * ‖x + I * y‖ ^ 2 : ℝ) : ℂ) -
      I * ((s * ‖x + (-I) * y‖ ^ 2 : ℝ) : ℂ)) := by
  apply Complex.ext <;>
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

/-- The excess form `∫ (S_a − μ_a) f̂_u conj(f̂_v)`. -/
def excessForm (u v : CCMArchimedeanFormDomain a) : ℂ :=
  ∫ ξ : ℝ, (excessSymbol a ξ : ℂ) *
    (unitaryLaplace (timeRep a u) ξ * conj (unitaryLaplace (timeRep a v) ξ))

theorem integrable_excessIntegrand (u v : CCMArchimedeanFormDomain a) :
    Integrable fun ξ : ℝ => (excessSymbol a ξ : ℂ) *
      (unitaryLaplace (timeRep a u) ξ * conj (unitaryLaplace (timeRep a v) ξ)) := by
  have h : ∀ c : ℂ, Integrable fun ξ : ℝ => ((excessSymbol a ξ *
      ‖unitaryLaplace (timeRep a u) ξ + c * unitaryLaplace (timeRep a v) ξ‖ ^ 2 : ℝ) : ℂ) := by
    intro c
    refine (integrable_excess a (u + c • v)).ofReal.congr (Eventually.of_forall fun ξ => ?_)
    simp only [unitaryLaplace_timeRep_add_smul, excessSymbol]
    rfl
  refine ((((h 1).sub (h (-1))).add ((h I).const_mul I)).sub
    ((h (-I)).const_mul I)).const_mul (1 / 4 : ℂ) |>.congr (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [polarize]

theorem excessForm_self {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) :
    excessForm a u u = ((ccmRestrictedWeilSourceQuadratic a u -
      ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 : ℝ) : ℂ) := by
  rw [source_sub_eq_integral a u hu, ← integral_complex_ofReal, excessForm]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [excessSymbol, Complex.mul_conj, Complex.sq_norm, Complex.ofReal_mul]

theorem excessForm_add_smul_left (u v w : CCMArchimedeanFormDomain a) (c : ℂ) :
    excessForm a (u + c • v) w = excessForm a u w + c * excessForm a v w := by
  rw [excessForm, excessForm, excessForm, ← integral_const_mul,
    ← integral_add (integrable_excessIntegrand a u w)
      ((integrable_excessIntegrand a v w).const_mul c)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [unitaryLaplace_timeRep_add_smul]
  ring

theorem excessForm_add_smul_right (u v w : CCMArchimedeanFormDomain a) (c : ℂ) :
    excessForm a w (u + c • v) = excessForm a w u + conj c * excessForm a w v := by
  rw [excessForm, excessForm, excessForm, ← integral_const_mul,
    ← integral_add (integrable_excessIntegrand a w u)
      ((integrable_excessIntegrand a w v).const_mul (conj c))]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [unitaryLaplace_timeRep_add_smul, map_add, map_mul]
  ring

theorem excessForm_conj (u v : CCMArchimedeanFormDomain a) :
    conj (excessForm a u v) = excessForm a v u := by
  rw [excessForm, excessForm, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem excessForm_zero_left (w : CCMArchimedeanFormDomain a) : excessForm a 0 w = 0 := by
  have h := excessForm_add_smul_left a 0 0 w 1
  rw [one_smul, add_zero, one_mul] at h
  linear_combination -h

/-- The excess form as a sesquilinear map. -/
def excessSesq : CCMArchimedeanFormDomain a →ₗ[ℂ] CCMArchimedeanFormDomain a →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (excessForm a)
    (fun u v w => by
      have h := excessForm_add_smul_left a u v w 1
      rwa [one_smul, one_mul] at h)
    (fun c u w => by
      have h := excessForm_add_smul_left a 0 u w c
      rw [zero_add, excessForm_zero_left, zero_add] at h
      rw [h, RingHom.id_apply, smul_eq_mul])
    (fun w u v => by
      have h := excessForm_add_smul_right a u v w 1
      rwa [one_smul, map_one, one_mul] at h)
    (fun c w u => by
      have h := excessForm_add_smul_right a 0 u w c
      rw [zero_add] at h
      have h0 : excessForm a w 0 = 0 := by
        rw [← excessForm_conj, excessForm_zero_left, map_zero]
      rw [h, h0, zero_add, smul_eq_mul])

theorem excessSesq_apply (u v : CCMArchimedeanFormDomain a) :
    excessSesq a u v = excessForm a u v := rfl

theorem isPolarConstrained_add_smul {u v : CCMArchimedeanFormDomain a}
    (hu : IsPolarConstrained a u) (hv : IsPolarConstrained a v) (c : ℂ) :
    IsPolarConstrained a (u + c • v) := by
  rw [isPolarConstrained_iff] at hu hv ⊢
  rw [unitaryLaplace_timeRep_add_smul, unitaryLaplace_timeRep_add_smul, hu.1, hu.2, hv.1, hv.2]
  simp

theorem excessForm_self_re_nonneg {v : CCMArchimedeanFormDomain a}
    (hv : IsPolarConstrained a v) : 0 ≤ (excessForm a v v).re := by
  rw [excessForm_self a hv, Complex.ofReal_re]
  linarith [polarGroundEnergy_mul_le a v hv]

theorem excessForm_self_im {v : CCMArchimedeanFormDomain a} (hv : IsPolarConstrained a v) :
    (excessForm a v v).im = 0 := by
  rw [excessForm_self a hv, Complex.ofReal_im]

theorem excessForm_ground {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u) :
    excessForm a u u = 0 := by
  rw [excessForm_self a hu.1, hu.2, sub_self, Complex.ofReal_zero]

/-- **Euler–Lagrange identity.**  A polar ground state is excess-orthogonal to every polar
vector. -/
theorem excessForm_eq_zero_of_ground {u v : CCMArchimedeanFormDomain a}
    (hu : IsPolarGround a u) (hv : IsPolarConstrained a v) : excessForm a v u = 0 := by
  set b := excessForm a v u with hb
  set A := excessForm a v v with hAdef
  have hexp : ∀ c : ℂ, excessForm a (u + c • v) (u + c • v) =
      conj c * conj b + c * b + c * conj c * A := by
    intro c
    rw [excessForm_add_smul_left, excessForm_add_smul_right, excessForm_add_smul_right,
      excessForm_ground a hu, ← excessForm_conj a v u]
    ring
  have hA : A = (A.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hAdef, excessForm_self_im a hv]
  set t : ℝ := 1 / (|A.re| + 1) with htdef
  have ht : 0 < t := by positivity
  have htA : t * A.re < 2 := by
    have h1 : t * A.re ≤ t * |A.re| := mul_le_mul_of_nonneg_left (le_abs_self _) ht.le
    have h2 : t * |A.re| < 1 := by
      rw [htdef, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    linarith
  have key := excessForm_self_re_nonneg a
    (isPolarConstrained_add_smul a hu.1 hv (-(t : ℂ) * conj b))
  rw [hexp, hA] at key
  have hval : (conj (-(t : ℂ) * conj b) * conj b + -(t : ℂ) * conj b * b +
      -(t : ℂ) * conj b * conj (-(t : ℂ) * conj b) * (A.re : ℂ)).re =
      t * Complex.normSq b * (t * A.re - 2) := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hval] at key
  have hN : Complex.normSq b ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : t * Complex.normSq b * (t * A.re - 2) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos ht hpos) (by linarith)
    linarith
  exact Complex.normSq_eq_zero.mp (le_antisymm hN (Complex.normSq_nonneg b))

theorem polarPoint_ne_ofReal {s : ℝ} (hs : s ≠ 0) (x : ℝ) : polarPoint s ≠ (x : ℂ) := by
  intro he
  have h2 : (I * s : ℂ) = (x : ℂ) * (2 * Real.pi) := by
    rw [polarPoint] at he
    rw [← he]
    field_simp
  have := congrArg Complex.im h2
  simp at this
  exact hs this

theorem isPolarConstrained_of_div {u h : CCMArchimedeanFormDomain a}
    (hu : IsPolarConstrained a u) (x : ℝ)
    (hh : ∀ w : ℂ, w ≠ x →
      unitaryLaplace (timeRep a h) w = unitaryLaplace (timeRep a u) w / (w - x)) :
    IsPolarConstrained a h := by
  rw [isPolarConstrained_iff] at hu ⊢
  rw [hh _ (polarPoint_ne_ofReal (by norm_num) x), hh _ (polarPoint_ne_ofReal (by norm_num) x),
    hu.1, hu.2, zero_div, zero_div]
  exact ⟨rfl, rfl⟩

theorem ae_ne_real (x : ℝ) : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ x := by
  rw [ae_iff]
  simp

/-- A polar vector whose transform vanishes at a real zero `x` of the ground state is
excess-orthogonal to the zero quotient `f̂_u/(w − x)`. -/
theorem excessForm_div_eq_zero {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u)
    {x : ℝ} {h : CCMArchimedeanFormDomain a}
    (hh : ∀ w : ℂ, w ≠ x →
      unitaryLaplace (timeRep a h) w = unitaryLaplace (timeRep a u) w / (w - x))
    {g : CCMArchimedeanFormDomain a} (hg : IsPolarConstrained a g)
    (hgx : unitaryLaplace (timeRep a g) x = 0) : excessForm a g h = 0 := by
  obtain ⟨k, hk⟩ := exists_div a g hgx
  have hkpol : IsPolarConstrained a k := isPolarConstrained_of_div a hg x hk
  have heq : excessForm a g h = excessForm a k u := by
    refine integral_congr_ae ((ae_ne_real x).mono fun ξ hξ => ?_)
    have hξc : (ξ : ℂ) ≠ x := by exact_mod_cast hξ
    have hsub : (ξ : ℂ) - x ≠ 0 := sub_ne_zero.mpr hξc
    have hg' : unitaryLaplace (timeRep a g) ξ =
        ((ξ : ℂ) - x) * unitaryLaplace (timeRep a k) ξ := by
      rw [hk _ hξc]
      field_simp
    have hconj : conj ((ξ : ℂ) - x) = (ξ : ℂ) - x := by
      rw [map_sub, Complex.conj_ofReal, Complex.conj_ofReal]
    dsimp only
    rw [hg', hh _ hξc, map_div₀, hconj]
    field_simp
  rw [heq]
  exact excessForm_eq_zero_of_ground a hu hkpol

/-- **Zero-quotient orthogonality.**  For two distinct real zeros of a polar ground state, the
quotients `f̂_u/(w − x₁)` and `f̂_u/(w − x₂)` are excess-orthogonal. -/
theorem excessForm_zeroQuotient_orthogonal {u : CCMArchimedeanFormDomain a}
    (hu : IsPolarGround a u) {x₁ x₂ : ℝ} (hne : x₁ ≠ x₂)
    (hz₂ : unitaryLaplace (timeRep a u) x₂ = 0) {h₁ h₂ : CCMArchimedeanFormDomain a}
    (hh₁ : ∀ w : ℂ, w ≠ x₁ →
      unitaryLaplace (timeRep a h₁) w = unitaryLaplace (timeRep a u) w / (w - x₁))
    (hh₂ : ∀ w : ℂ, w ≠ x₂ →
      unitaryLaplace (timeRep a h₂) w = unitaryLaplace (timeRep a u) w / (w - x₂)) :
    excessForm a h₁ h₂ = 0 := by
  refine excessForm_div_eq_zero a hu hh₂ (isPolarConstrained_of_div a hu.1 x₁ hh₁) ?_
  have hne' : ((x₂ : ℝ) : ℂ) ≠ x₁ := by exact_mod_cast hne.symm
  rw [hh₁ _ hne', hz₂, zero_div]

/-- **Positive quadrature at the zeros of a ground state.**  Let `u` be a polar ground state,
`x_i` finitely many distinct real zeros of `f̂_u`, and `h_i` the zero quotients
`f̂_{h_i} = f̂_u/(w − x_i)` with `f̂_{h_i}(x_i) ≠ 0`.  Then for every polar vector `g`,
`Σ_i ρ_i |f̂_g(x_i)|² ≤ Q(g) − μ_a ‖J g‖²` with weights
`ρ_i = (Q(h_i) − μ_a ‖J h_i‖²)/|f̂_{h_i}(x_i)|² ≥ 0`. -/
theorem quadrature_le {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u) {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (hx : Set.InjOn x s) (h : ι → CCMArchimedeanFormDomain a)
    (hh : ∀ i ∈ s, ∀ w : ℂ, w ≠ x i →
      unitaryLaplace (timeRep a (h i)) w = unitaryLaplace (timeRep a u) w / (w - x i))
    (hzero : ∀ i ∈ s, unitaryLaplace (timeRep a u) (x i) = 0)
    (hval : ∀ i ∈ s, unitaryLaplace (timeRep a (h i)) (x i) ≠ 0)
    {g : CCMArchimedeanFormDomain a} (hg : IsPolarConstrained a g) :
    ∑ i ∈ s, (excessForm a (h i) (h i)).re / ‖unitaryLaplace (timeRep a (h i)) (x i)‖ ^ 2 *
        ‖unitaryLaplace (timeRep a g) (x i)‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a g -
        ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a g‖ ^ 2 := by
  classical
  set c : ι → ℂ := fun i =>
    unitaryLaplace (timeRep a g) (x i) / unitaryLaplace (timeRep a (h i)) (x i) with hcdef
  set q := ∑ i ∈ s, c i • h i with hqdef
  set r := g - q with hrdef
  have hpolh : ∀ i ∈ s, IsPolarConstrained a (h i) :=
    fun i hi => isPolarConstrained_of_div a hu.1 (x i) (hh i hi)
  have hhij : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → unitaryLaplace (timeRep a (h i)) (x j) = 0 := by
    intro i hi j hj hij
    have hne : ((x j : ℝ) : ℂ) ≠ x i := by
      intro he
      exact hij (hx hi hj (by exact_mod_cast he.symm))
    rw [hh i hi _ hne, hzero j hj, zero_div]
  have hevq : ∀ w : ℂ, evalAt a w q = ∑ i ∈ s, c i * unitaryLaplace (timeRep a (h i)) w := by
    intro w
    simp only [hqdef, map_sum, map_smul, evalAt_apply, smul_eq_mul]
  have hpolr : IsPolarConstrained a r := by
    rw [isPolarConstrained_iff]
    have hp : ∀ w, (w = polarPoint (1 / 2) ∨ w = polarPoint (-1 / 2)) →
        unitaryLaplace (timeRep a r) w = 0 := by
      intro w hw
      have hgw : unitaryLaplace (timeRep a g) w = 0 := by
        rcases hw with rfl | rfl
        · exact ((isPolarConstrained_iff a g).mp hg).1
        · exact ((isPolarConstrained_iff a g).mp hg).2
      change evalAt a w (g - q) = 0
      rw [map_sub, hevq, evalAt_apply, hgw, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      rcases hw with rfl | rfl
      · rw [((isPolarConstrained_iff a (h i)).mp (hpolh i hi)).1, mul_zero]
      · rw [((isPolarConstrained_iff a (h i)).mp (hpolh i hi)).2, mul_zero]
    exact ⟨hp _ (Or.inl rfl), hp _ (Or.inr rfl)⟩
  have hrx : ∀ j ∈ s, unitaryLaplace (timeRep a r) (x j) = 0 := by
    intro j hj
    change evalAt a _ (g - q) = 0
    rw [map_sub, hevq, evalAt_apply, Finset.sum_eq_single_of_mem j hj
      (fun i hi hij => by rw [hhij i hi j hj hij, mul_zero])]
    simp only [hcdef]
    field_simp [hval j hj]
    ring
  have hrh : ∀ j ∈ s, excessSesq a r (h j) = 0 :=
    fun j hj => excessForm_div_eq_zero a hu (hh j hj) hpolr (hrx j hj)
  have hrq : excessSesq a r q = 0 := by
    simp only [hqdef, map_sum, map_smulₛₗ, smul_eq_mul]
    exact Finset.sum_eq_zero fun j hj => by rw [hrh j hj, mul_zero]
  have hqr : excessSesq a q r = 0 := by
    rw [excessSesq_apply, ← excessForm_conj, ← excessSesq_apply, hrq, map_zero]
  have hqq : excessSesq a q q = ∑ i ∈ s, c i * conj (c i) * excessForm a (h i) (h i) := by
    simp only [hqdef, map_sum, map_smul, map_smulₛₗ, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by
      rw [excessSesq_apply, excessForm_zeroQuotient_orthogonal a hu (fun e => hji (hx hj hi e))
        (hzero i hi) (hh j hj) (hh i hi), mul_zero])]
    rw [excessSesq_apply]
    ring
  have hgg : excessForm a g g = excessForm a r r +
      ∑ i ∈ s, c i * conj (c i) * excessForm a (h i) (h i) := by
    have hg' : g = r + q := by rw [hrdef, sub_add_cancel]
    rw [← excessSesq_apply, ← excessSesq_apply, ← hqq]
    conv_lhs => rw [hg']
    simp only [map_add, LinearMap.add_apply]
    rw [hrq, hqr]
    ring
  have hre := congrArg Complex.re hgg
  rw [excessForm_self a hg, Complex.ofReal_re, Complex.add_re, Complex.re_sum] at hre
  rw [hre]
  have hsum : ∑ i ∈ s, (c i * conj (c i) * excessForm a (h i) (h i)).re =
      ∑ i ∈ s, (excessForm a (h i) (h i)).re /
        ‖unitaryLaplace (timeRep a (h i)) (x i)‖ ^ 2 *
        ‖unitaryLaplace (timeRep a g) (x i)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, hcdef, norm_div,
      div_pow]
    ring
  rw [hsum]
  linarith [excessForm_self_re_nonneg a hpolr]

/-- **Real-rooted ground states carry a positive quadrature.**  At every aperture there is a
nonzero polar ground state `u` whose transform has only real zeros off `w_{±1/2}`, and for every
finite set `Z` of its real zeros there are weights `ρ ≥ 0` on `Z` with
`Σ_{x∈Z} ρ(x) |f̂_g(x)|² ≤ Q(g) − μ_a ‖J g‖²` for every polar vector `g`. -/
theorem exists_realRooted_quadrature :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarGround a u ∧
      ccmArchimedeanFormToAperture a u ≠ 0 ∧
      (∀ w : ℂ, unitaryLaplace (timeRep a u) w = 0 → w ≠ polarPoint (1 / 2) →
        w ≠ polarPoint (-1 / 2) → w.im = 0) ∧
      ∀ Z : Finset ℝ, (∀ x ∈ Z, unitaryLaplace (timeRep a u) x = 0) →
        ∃ ρ : ℝ → ℝ, (∀ x ∈ Z, 0 ≤ ρ x) ∧ ∀ g : CCMArchimedeanFormDomain a,
          IsPolarConstrained a g →
          ∑ x ∈ Z, ρ x * ‖unitaryLaplace (timeRep a g) x‖ ^ 2 ≤
            ccmRestrictedWeilSourceQuadratic a g -
              ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a g‖ ^ 2 := by
  classical
  obtain ⟨u, hu, hne, hreal⟩ := exists_realRooted_polarGround a
  refine ⟨u, hu, hne, hreal, fun Z hZ => ?_⟩
  have hdiv : ∀ x : ℝ, ∃ h : CCMArchimedeanFormDomain a,
      unitaryLaplace (timeRep a u) x = 0 → ∀ w : ℂ, w ≠ x →
        unitaryLaplace (timeRep a h) w = unitaryLaplace (timeRep a u) w / (w - x) := by
    intro x
    by_cases hx : unitaryLaplace (timeRep a u) x = 0
    · obtain ⟨h, hh⟩ := exists_div a u hx
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose h hh using hdiv
  set ρ : ℝ → ℝ := fun x => if unitaryLaplace (timeRep a (h x)) x = 0 then 0 else
    (excessForm a (h x) (h x)).re / ‖unitaryLaplace (timeRep a (h x)) x‖ ^ 2 with hρ
  refine ⟨ρ, fun x hx => ?_, fun g hg => ?_⟩
  · simp only [hρ]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (excessForm_self_re_nonneg a
        (isPolarConstrained_of_div a hu.1 x (hh x (hZ x hx)))) (by positivity)
  set s := Z.filter fun x => unitaryLaplace (timeRep a (h x)) x ≠ 0
  have hsplit : ∑ x ∈ Z, ρ x * ‖unitaryLaplace (timeRep a g) x‖ ^ 2 =
      ∑ x ∈ s, (excessForm a (h x) (h x)).re / ‖unitaryLaplace (timeRep a (h x)) x‖ ^ 2 *
        ‖unitaryLaplace (timeRep a g) x‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hρ]
    split_ifs with h1 h2 <;> first | rfl | (exact absurd h1 h2) | simp
  rw [hsplit]
  exact quadrature_le a hu s id (Set.injOn_id _) h
    (fun x hx => hh x (hZ x (Finset.mem_filter.mp hx).1))
    (fun x hx => hZ x (Finset.mem_filter.mp hx).1)
    (fun x hx => (Finset.mem_filter.mp hx).2) hg

end RHTower.CCMGroundQuadrature
