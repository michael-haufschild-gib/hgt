import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalBlackHoleQNMIncidence
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay
import GaloisForLFunctions.RHTower.XiWeilDivisorHilbert
import GaloisForLFunctions.HTGeometry.GoldenRuleSelfEnergy

/-!
# Completed-Eisenstein EKG optical incidence at theta-cusp black-hole resonances

For a four-dimensional topological AdS black hole with modular hyperbolic horizon, the quadratic
Einstein--Klein--Gordon stress tensor multiplies horizon Eisenstein modes.  Its angular spectral
resolution therefore uses the regularized Eisenstein multiplication table: residual terms,
discrete Maass modes, and an Eisenstein continuum.  The all-Eisenstein cubic coefficient is the
regularized triple product.

For `E(z, 1/2 + u)`, the full-level formula of Zagier and Michel--Venkatesh is, up to the stated
normalization,

```text
integral^reg E(u1) E(u2) E(u3)
  = product_{epsilon2,epsilon3 = ±1}
      Lambda(1/2 + u1 + epsilon2*u2 + epsilon3*u3)
    / product_j Lambda(1 + 2*uj).
```

Multiplying each external leg by its completed factor cancels the denominator.  This file uses the
canonical entire pole-filled version of the numerator, replacing each meromorphic `Lambda(s)` by
`xi(s) = s(s-1) Lambda(s)/2`, expressed through the corpus function `XiC`.  This changes only the
elementary factors at `0,1`; it preserves nontrivial divisor incidence.

The result is sharp and negative for RH selection.  The completed cubic vertex is invariant under
each Eisenstein Weyl reflection.  At every Xi divisor pole, and for every fixed physical continuum
leg, all but countably many partner frequencies give nonzero cubic coupling.  Thus the same vertex
lights the pole and its analytic shadow zero.  Angular EKG backreaction forces return-path mixing;
it cannot distinguish critical from tilted divisor sectors.

The squared continuum vertex is continuous and integrable by the actual theta/Xi horizontal decay.
The Weisskopf--Wigner boundary theorem then yields an exact finite-discrete plus continuum optical
energy identity, with strictly positive continuum rate at a bright channel.

`[LITERATURE]` Regularized triple-Eisenstein product: Zagier, *The Rankin--Selberg method for
automorphic functions which are not of rapid decay*; Michel--Venkatesh, PMIHES 111 (2010),
Section 4.5; Huang--Li, arXiv:2510.12322, Lemma 4.2.

`[PAPER-PROVED] [LEAN-PROVED] [HAWKING-SPECIFIC] [NO-GO]` This proves angular nonlinear incidence
and its optical self-energy consequence.  It does not invent the missing radial
Einstein--Teukolsky Green coefficients.  Any RH-bearing producer left after this theorem must use
their time-oriented phase/QNM-clock data, not KMS, passivity, or unsigned angular energy.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Entire pole-filled version of one completed-zeta factor `xi(1/2 + u)`. -/
def thetaCuspHawkingCompletedEisensteinXiFactor (u : ℂ) : ℂ := XiC (-Complex.I * u)

/-- The completed factor is invariant under the Eisenstein Weyl reflection `u -> -u`. -/
theorem thetaCuspHawkingCompletedEisensteinXiFactor_neg (u : ℂ) :
    thetaCuspHawkingCompletedEisensteinXiFactor (-u) =
      thetaCuspHawkingCompletedEisensteinXiFactor u := by
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
  have harg : -Complex.I * -u = -(-Complex.I * u) := by ring
  rw [harg, XiC_even]

/-- Entire numerator of the regularized triple-Eisenstein angular vertex. -/
def thetaCuspHawkingCompletedEisensteinCubicVertex (u₁ u₂ u₃ : ℂ) : ℂ :=
  thetaCuspHawkingCompletedEisensteinXiFactor (u₁ + u₂ + u₃) *
    thetaCuspHawkingCompletedEisensteinXiFactor (u₁ - u₂ + u₃) *
    thetaCuspHawkingCompletedEisensteinXiFactor (u₁ + u₂ - u₃) *
    thetaCuspHawkingCompletedEisensteinXiFactor (u₁ - u₂ - u₃)

/-- Weyl reflection of first Eisenstein leg preserves completed vertex. -/
theorem thetaCuspHawkingCompletedEisensteinCubicVertex_neg_one (u₁ u₂ u₃ : ℂ) :
    thetaCuspHawkingCompletedEisensteinCubicVertex (-u₁) u₂ u₃ =
      thetaCuspHawkingCompletedEisensteinCubicVertex u₁ u₂ u₃ := by
  have h1 : thetaCuspHawkingCompletedEisensteinXiFactor (-u₁ + u₂ + u₃) = thetaCuspHawkingCompletedEisensteinXiFactor (u₁ - u₂ - u₃) := by
    rw [show -u₁ + u₂ + u₃ = -(u₁ - u₂ - u₃) by ring, thetaCuspHawkingCompletedEisensteinXiFactor_neg]
  have h2 : thetaCuspHawkingCompletedEisensteinXiFactor (-u₁ - u₂ + u₃) = thetaCuspHawkingCompletedEisensteinXiFactor (u₁ + u₂ - u₃) := by
    rw [show -u₁ - u₂ + u₃ = -(u₁ + u₂ - u₃) by ring, thetaCuspHawkingCompletedEisensteinXiFactor_neg]
  have h3 : thetaCuspHawkingCompletedEisensteinXiFactor (-u₁ + u₂ - u₃) = thetaCuspHawkingCompletedEisensteinXiFactor (u₁ - u₂ + u₃) := by
    rw [show -u₁ + u₂ - u₃ = -(u₁ - u₂ + u₃) by ring, thetaCuspHawkingCompletedEisensteinXiFactor_neg]
  have h4 : thetaCuspHawkingCompletedEisensteinXiFactor (-u₁ - u₂ - u₃) = thetaCuspHawkingCompletedEisensteinXiFactor (u₁ + u₂ + u₃) := by
    rw [show -u₁ - u₂ - u₃ = -(u₁ + u₂ + u₃) by ring, thetaCuspHawkingCompletedEisensteinXiFactor_neg]
  rw [thetaCuspHawkingCompletedEisensteinCubicVertex, thetaCuspHawkingCompletedEisensteinCubicVertex, h1, h2, h3, h4]
  ring

/-- Weyl reflection of second Eisenstein leg permutes four factors. -/
theorem thetaCuspHawkingCompletedEisensteinCubicVertex_neg_two (u₁ u₂ u₃ : ℂ) :
    thetaCuspHawkingCompletedEisensteinCubicVertex u₁ (-u₂) u₃ =
      thetaCuspHawkingCompletedEisensteinCubicVertex u₁ u₂ u₃ := by
  rw [thetaCuspHawkingCompletedEisensteinCubicVertex, thetaCuspHawkingCompletedEisensteinCubicVertex]
  ring

/-- Weyl reflection of third Eisenstein leg permutes four factors. -/
theorem thetaCuspHawkingCompletedEisensteinCubicVertex_neg_three (u₁ u₂ u₃ : ℂ) :
    thetaCuspHawkingCompletedEisensteinCubicVertex u₁ u₂ (-u₃) =
      thetaCuspHawkingCompletedEisensteinCubicVertex u₁ u₂ u₃ := by
  rw [thetaCuspHawkingCompletedEisensteinCubicVertex, thetaCuspHawkingCompletedEisensteinCubicVertex]
  ring

/-- Eisenstein parameter `u = s - 1/2` attached to modular scattering coordinate `z`. -/
def thetaCuspHawkingEisensteinResonanceParameter (z : ℂ) : ℂ :=
  -(1 / 4 : ℂ) + Complex.I * z / 2

/-- Unitary principal-series parameter for physical horizon-continuum frequency. -/
def thetaCuspHawkingEisensteinContinuumParameter (r : ℝ) : ℂ := Complex.I * (r : ℂ)

/-- Completed cubic vertex with one resonance leg and two physical continuum legs. -/
def thetaCuspHawkingCompletedEisensteinPhysicalVertex (z : ℂ) (r t : ℝ) : ℂ :=
  thetaCuspHawkingCompletedEisensteinCubicVertex
    (thetaCuspHawkingEisensteinResonanceParameter z)
    (thetaCuspHawkingEisensteinContinuumParameter r)
    (thetaCuspHawkingEisensteinContinuumParameter t)

/-- Center shared by four physical-line completed-zeta factors. -/
def thetaCuspHawkingCompletedEisensteinVertexCenter (z : ℂ) : ℂ := z / 2 + Complex.I / 4

/-- Resonance-coordinate form of four-factor regularized Eisenstein numerator. -/
theorem thetaCuspHawkingCompletedEisensteinPhysicalVertex_eq (z : ℂ) (r t : ℝ) :
    thetaCuspHawkingCompletedEisensteinPhysicalVertex z r t =
      XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((r + t : ℝ) : ℂ)) *
        XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((-r + t : ℝ) : ℂ)) *
        XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((r - t : ℝ) : ℂ)) *
        XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((-r - t : ℝ) : ℂ)) := by
  have h1 : thetaCuspHawkingCompletedEisensteinXiFactor (thetaCuspHawkingEisensteinResonanceParameter z + thetaCuspHawkingEisensteinContinuumParameter r + thetaCuspHawkingEisensteinContinuumParameter t) =
      XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((r + t : ℝ) : ℂ)) := by
    rw [thetaCuspHawkingCompletedEisensteinXiFactor]
    congr 1
    simp only [thetaCuspHawkingEisensteinResonanceParameter, thetaCuspHawkingEisensteinContinuumParameter, thetaCuspHawkingCompletedEisensteinVertexCenter]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  have h2 : thetaCuspHawkingCompletedEisensteinXiFactor (thetaCuspHawkingEisensteinResonanceParameter z - thetaCuspHawkingEisensteinContinuumParameter r + thetaCuspHawkingEisensteinContinuumParameter t) =
      XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((-r + t : ℝ) : ℂ)) := by
    rw [thetaCuspHawkingCompletedEisensteinXiFactor]
    congr 1
    simp only [thetaCuspHawkingEisensteinResonanceParameter, thetaCuspHawkingEisensteinContinuumParameter, thetaCuspHawkingCompletedEisensteinVertexCenter]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  have h3 : thetaCuspHawkingCompletedEisensteinXiFactor (thetaCuspHawkingEisensteinResonanceParameter z + thetaCuspHawkingEisensteinContinuumParameter r - thetaCuspHawkingEisensteinContinuumParameter t) =
      XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((r - t : ℝ) : ℂ)) := by
    rw [thetaCuspHawkingCompletedEisensteinXiFactor]
    congr 1
    simp only [thetaCuspHawkingEisensteinResonanceParameter, thetaCuspHawkingEisensteinContinuumParameter, thetaCuspHawkingCompletedEisensteinVertexCenter]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  have h4 : thetaCuspHawkingCompletedEisensteinXiFactor (thetaCuspHawkingEisensteinResonanceParameter z - thetaCuspHawkingEisensteinContinuumParameter r - thetaCuspHawkingEisensteinContinuumParameter t) =
      XiC (thetaCuspHawkingCompletedEisensteinVertexCenter z + ((-r - t : ℝ) : ℂ)) := by
    rw [thetaCuspHawkingCompletedEisensteinXiFactor]
    congr 1
    simp only [thetaCuspHawkingEisensteinResonanceParameter, thetaCuspHawkingEisensteinContinuumParameter, thetaCuspHawkingCompletedEisensteinVertexCenter]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  rw [thetaCuspHawkingCompletedEisensteinPhysicalVertex, thetaCuspHawkingCompletedEisensteinCubicVertex, h1, h2, h3, h4]

/-- Pole/zero shadow reflection leaves completed nonlinear angular vertex unchanged. -/
theorem thetaCuspHawkingCompletedEisensteinPhysicalVertex_shadow (z : ℂ) (r t : ℝ) :
    thetaCuspHawkingCompletedEisensteinPhysicalVertex (thetaCuspHawkingOpticalCuspShadow z) r t =
      thetaCuspHawkingCompletedEisensteinPhysicalVertex z r t := by
  have harg : thetaCuspHawkingEisensteinResonanceParameter (thetaCuspHawkingOpticalCuspShadow z) = -thetaCuspHawkingEisensteinResonanceParameter z := by
    unfold thetaCuspHawkingEisensteinResonanceParameter thetaCuspHawkingOpticalCuspShadow
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  rw [thetaCuspHawkingCompletedEisensteinPhysicalVertex, thetaCuspHawkingCompletedEisensteinPhysicalVertex, harg, thetaCuspHawkingCompletedEisensteinCubicVertex_neg_one]

/-- For fixed resonance and one continuum leg, dark partner frequencies are countable. -/
theorem countable_thetaCuspHawkingCompletedEisensteinPhysicalVertex_zeroSet
    (z : ℂ) (t : ℝ) :
    {r : ℝ | thetaCuspHawkingCompletedEisensteinPhysicalVertex z r t = 0}.Countable := by
  let c : ℂ := thetaCuspHawkingCompletedEisensteinVertexCenter z
  let f₁ : ℝ → ℂ := fun r => c + ((r + t : ℝ) : ℂ)
  let f₂ : ℝ → ℂ := fun r => c + ((-r + t : ℝ) : ℂ)
  let f₃ : ℝ → ℂ := fun r => c + ((r - t : ℝ) : ℂ)
  let f₄ : ℝ → ℂ := fun r => c + ((-r - t : ℝ) : ℂ)
  have hinj₁ : Function.Injective f₁ := by
    intro x y h
    have hre := congrArg Complex.re h
    simp [f₁, c, thetaCuspHawkingCompletedEisensteinVertexCenter] at hre
    linarith
  have hinj₂ : Function.Injective f₂ := by
    intro x y h
    have hre := congrArg Complex.re h
    simp [f₂, c, thetaCuspHawkingCompletedEisensteinVertexCenter] at hre
    linarith
  have hinj₃ : Function.Injective f₃ := by
    intro x y h
    have hre := congrArg Complex.re h
    simp [f₃, c, thetaCuspHawkingCompletedEisensteinVertexCenter] at hre
    linarith
  have hinj₄ : Function.Injective f₄ := by
    intro x y h
    have hre := congrArg Complex.re h
    simp [f₄, c, thetaCuspHawkingCompletedEisensteinVertexCenter] at hre
    linarith
  have hcount₁ : (f₁ ⁻¹' {w : ℂ | XiC w = 0}).Countable :=
    XiC_zeroSet_countable.preimage hinj₁
  have hcount₂ : (f₂ ⁻¹' {w : ℂ | XiC w = 0}).Countable :=
    XiC_zeroSet_countable.preimage hinj₂
  have hcount₃ : (f₃ ⁻¹' {w : ℂ | XiC w = 0}).Countable :=
    XiC_zeroSet_countable.preimage hinj₃
  have hcount₄ : (f₄ ⁻¹' {w : ℂ | XiC w = 0}).Countable :=
    XiC_zeroSet_countable.preimage hinj₄
  apply (hcount₁.union (hcount₂.union (hcount₃.union hcount₄))).mono
  intro r hr
  change thetaCuspHawkingCompletedEisensteinPhysicalVertex z r t = 0 at hr
  rw [thetaCuspHawkingCompletedEisensteinPhysicalVertex_eq] at hr
  simp only [mul_eq_zero] at hr
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq]
  rcases hr with (((h1 | h2) | h3) | h4)
  · exact Or.inl (by simpa [f₁, c] using h1)
  · exact Or.inr (Or.inl (by simpa [f₂, c] using h2))
  · exact Or.inr (Or.inr (Or.inl (by simpa [f₃, c] using h3)))
  · exact Or.inr (Or.inr (Or.inr (by simpa [f₄, c] using h4)))

/-- Every resonance has a bright physical Eisenstein-continuum partner. -/
theorem exists_thetaCuspHawkingCompletedEisensteinPhysicalVertex_ne_zero
    (z : ℂ) (t : ℝ) :
    ∃ r : ℝ, thetaCuspHawkingCompletedEisensteinPhysicalVertex z r t ≠ 0 := by
  by_contra h
  push Not at h
  have huniv : {r : ℝ | thetaCuspHawkingCompletedEisensteinPhysicalVertex z r t = 0} = Set.univ :=
    Set.eq_univ_of_forall h
  exact Cardinal.not_countable_real (huniv ▸ countable_thetaCuspHawkingCompletedEisensteinPhysicalVertex_zeroSet z t)

/-- Squared completed-zeta factor on translated physical horizontal line. -/
def thetaCuspHawkingCompletedEisensteinLineNormSq (a c r : ℝ) : ℝ :=
  ‖XiC (((r + c : ℝ) : ℂ) + (a : ℂ) * Complex.I)‖ ^ (2 : ℕ)

/-- Horizontal-line factor is continuous. -/
theorem continuous_thetaCuspHawkingCompletedEisensteinLineNormSq (a c : ℝ) :
    Continuous (thetaCuspHawkingCompletedEisensteinLineNormSq a c) := by
  unfold thetaCuspHawkingCompletedEisensteinLineNormSq
  exact (XiC_differentiable.continuous.comp (by fun_prop)).norm.pow 2

/-- Theta strip decay bounds every translated physical horizontal-line factor. -/
theorem exists_thetaCuspHawkingCompletedEisensteinLineNormSq_bounded
    {a : ℝ} (ha : |a| < 1) (c : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, thetaCuspHawkingCompletedEisensteinLineNormSq a c r ≤ B := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_XiC_horizontal_le (A := |a|) (δ := 0) ha (by norm_num)
      (by nlinarith [Real.pi_pos])
  refine ⟨C ^ (2 : ℕ), sq_nonneg C, fun r => ?_⟩
  have h := hbound (r + c) a (le_rfl)
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h
  rw [thetaCuspHawkingCompletedEisensteinLineNormSq]
  nlinarith [norm_nonneg (XiC ((((r + c : ℝ) : ℂ) + (a : ℂ) * Complex.I)))]

/-- Exponential theta/Xi decay makes each squared horizontal-line factor integrable. -/
theorem integrable_thetaCuspHawkingCompletedEisensteinLineNormSq
    {a : ℝ} (ha : |a| < 1) (c : ℝ) :
    Integrable (thetaCuspHawkingCompletedEisensteinLineNormSq a c) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_XiC_horizontal_le (A := |a|) (δ := 1 / 4) ha (by norm_num)
      (by nlinarith [Real.pi_gt_three])
  have hbase : Integrable (fun x : ℝ => Real.exp (-((1 / 2 : ℝ) * |x|))) :=
    integrable_exp_neg_mul_abs' (by norm_num)
  have hmp : MeasurePreserving (fun r : ℝ => r + c) volume volume :=
    measurePreserving_add_right volume c
  have hshift : Integrable (fun r : ℝ => Real.exp (-((1 / 2 : ℝ) * |r + c|))) :=
    (hmp.integrable_comp hbase.aestronglyMeasurable).mpr hbase
  have hmajor : Integrable
      (fun r : ℝ => C ^ (2 : ℕ) * Real.exp (-((1 / 2 : ℝ) * |r + c|))) :=
    hshift.const_mul _
  apply hmajor.mono' (continuous_thetaCuspHawkingCompletedEisensteinLineNormSq a c).aestronglyMeasurable
  filter_upwards with r
  have hn := hbound (r + c) a (le_rfl)
  have hsq : thetaCuspHawkingCompletedEisensteinLineNormSq a c r ≤
      C ^ (2 : ℕ) * Real.exp (-((1 / 2 : ℝ) * |r + c|)) := by
    rw [thetaCuspHawkingCompletedEisensteinLineNormSq]
    calc
      ‖XiC (((r + c : ℝ) : ℂ) + (a : ℂ) * Complex.I)‖ ^ (2 : ℕ) ≤
          (C * Real.exp (-((1 / 4 : ℝ) * |r + c|))) ^ (2 : ℕ) :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
      _ = C ^ (2 : ℕ) * Real.exp (-((1 / 2 : ℝ) * |r + c|)) := by
        rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
        congr 1
        ring
  have hnon : 0 ≤ thetaCuspHawkingCompletedEisensteinLineNormSq a c r := by
    exact sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  exact hsq

/-- Common horizontal height of four completed-zeta factors in physical variables. -/
def thetaCuspHawkingCompletedEisensteinPhysicalHeight (z : ℂ) : ℝ := z.im / 2 + 1 / 4

/-- Common real center before adding continuum frequencies. -/
def thetaCuspHawkingCompletedEisensteinCenterReal (z : ℂ) : ℝ := z.re / 2

/-- Every Xi divisor puts completed cubic factors strictly inside natural theta strip. -/
theorem abs_thetaCuspHawkingCompletedEisensteinPhysicalHeight_lt_one (q : XiZeroCopy) :
    |thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q)| < 1 := by
  have hstrip := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hstrip ⊢
  constructor <;> simp only [thetaCuspHawkingCompletedEisensteinPhysicalHeight] <;> linarith

/-- Positive continuum spectral density: squared completed angular EKG vertex. -/
def thetaCuspHawkingCompletedEisensteinContinuumDensity (q : XiZeroCopy) (t r : ℝ) : ℝ :=
  ‖thetaCuspHawkingCompletedEisensteinPhysicalVertex (xiSpectralPoint q) r t‖ ^ (2 : ℕ)

/-- Completed angular continuum density is nonnegative. -/
theorem thetaCuspHawkingCompletedEisensteinContinuumDensity_nonneg
    (q : XiZeroCopy) (t r : ℝ) :
    0 ≤ thetaCuspHawkingCompletedEisensteinContinuumDensity q t r := sq_nonneg _

/-- Every divisor has some continuum energy with strictly positive completed coupling density. -/
theorem exists_thetaCuspHawkingCompletedEisensteinContinuumDensity_pos
    (q : XiZeroCopy) (t : ℝ) :
    ∃ r : ℝ, 0 < thetaCuspHawkingCompletedEisensteinContinuumDensity q t r := by
  obtain ⟨r, hr⟩ := exists_thetaCuspHawkingCompletedEisensteinPhysicalVertex_ne_zero (xiSpectralPoint q) t
  refine ⟨r, ?_⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr hr)

/-- Physical continuum density factors into four squared horizontal Xi factors. -/
theorem thetaCuspHawkingCompletedEisensteinContinuumDensity_eq_lineFactors
    (q : XiZeroCopy) (t r : ℝ) :
    thetaCuspHawkingCompletedEisensteinContinuumDensity q t r =
      thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) + t) r *
        thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) + t) (-r) *
        thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) - t) r *
        thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) - t) (-r) := by
  rw [thetaCuspHawkingCompletedEisensteinContinuumDensity, thetaCuspHawkingCompletedEisensteinPhysicalVertex_eq]
  simp only [norm_mul, mul_pow]
  unfold thetaCuspHawkingCompletedEisensteinLineNormSq thetaCuspHawkingCompletedEisensteinPhysicalHeight thetaCuspHawkingCompletedEisensteinCenterReal thetaCuspHawkingCompletedEisensteinVertexCenter
  have h1 : ‖XiC (xiSpectralPoint q / 2 + Complex.I / 4 + ((r + t : ℝ) : ℂ))‖ ^ (2 : ℕ) =
      ‖XiC (((r + ((xiSpectralPoint q).re / 2 + t) : ℝ) : ℂ) +
        (((xiSpectralPoint q).im / 2 + 1 / 4 : ℝ) : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    apply congrArg (fun w : ℂ => ‖XiC w‖ ^ (2 : ℕ))
    apply Complex.ext <;> simp
    all_goals ring_nf
  have h2 : ‖XiC (xiSpectralPoint q / 2 + Complex.I / 4 + ((-r + t : ℝ) : ℂ))‖ ^ (2 : ℕ) =
      ‖XiC (((-r + ((xiSpectralPoint q).re / 2 + t) : ℝ) : ℂ) +
        (((xiSpectralPoint q).im / 2 + 1 / 4 : ℝ) : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    apply congrArg (fun w : ℂ => ‖XiC w‖ ^ (2 : ℕ))
    apply Complex.ext <;> simp
    all_goals ring_nf
  have h3 : ‖XiC (xiSpectralPoint q / 2 + Complex.I / 4 + ((r - t : ℝ) : ℂ))‖ ^ (2 : ℕ) =
      ‖XiC (((r + ((xiSpectralPoint q).re / 2 - t) : ℝ) : ℂ) +
        (((xiSpectralPoint q).im / 2 + 1 / 4 : ℝ) : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    apply congrArg (fun w : ℂ => ‖XiC w‖ ^ (2 : ℕ))
    apply Complex.ext <;> simp
    all_goals ring_nf
  have h4 : ‖XiC (xiSpectralPoint q / 2 + Complex.I / 4 + ((-r - t : ℝ) : ℂ))‖ ^ (2 : ℕ) =
      ‖XiC (((-r + ((xiSpectralPoint q).re / 2 - t) : ℝ) : ℂ) +
        (((xiSpectralPoint q).im / 2 + 1 / 4 : ℝ) : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    apply congrArg (fun w : ℂ => ‖XiC w‖ ^ (2 : ℕ))
    apply Complex.ext <;> simp
    all_goals ring_nf
  rw [h1, h2, h3, h4]

/-- Completed EKG continuum density is continuous in on-shell energy. -/
theorem continuous_thetaCuspHawkingCompletedEisensteinContinuumDensity
    (q : XiZeroCopy) (t : ℝ) :
    Continuous (thetaCuspHawkingCompletedEisensteinContinuumDensity q t) := by
  have hfun : thetaCuspHawkingCompletedEisensteinContinuumDensity q t = fun r : ℝ =>
      thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) + t) r *
        thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) + t) (-r) *
        thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) - t) r *
        thetaCuspHawkingCompletedEisensteinLineNormSq (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
          (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) - t) (-r) := by
    funext r
    exact thetaCuspHawkingCompletedEisensteinContinuumDensity_eq_lineFactors q t r
  rw [hfun]
  have hPlus := continuous_thetaCuspHawkingCompletedEisensteinLineNormSq
    (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
    (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) + t)
  have hMinus := continuous_thetaCuspHawkingCompletedEisensteinLineNormSq
    (thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q))
    (thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) - t)
  exact ((hPlus.mul (hPlus.comp (by fun_prop))).mul hMinus).mul
    (hMinus.comp (by fun_prop))

/-- Completed EKG continuum density is integrable in on-shell energy. -/
theorem integrable_thetaCuspHawkingCompletedEisensteinContinuumDensity
    (q : XiZeroCopy) (t : ℝ) :
    Integrable (thetaCuspHawkingCompletedEisensteinContinuumDensity q t) := by
  let a := thetaCuspHawkingCompletedEisensteinPhysicalHeight (xiSpectralPoint q)
  let cPlus := thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) + t
  let cMinus := thetaCuspHawkingCompletedEisensteinCenterReal (xiSpectralPoint q) - t
  have ha : |a| < 1 := abs_thetaCuspHawkingCompletedEisensteinPhysicalHeight_lt_one q
  have hOne : Integrable (thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus) := integrable_thetaCuspHawkingCompletedEisensteinLineNormSq ha cPlus
  obtain ⟨BPlus, hBPlus, hbPlus⟩ := exists_thetaCuspHawkingCompletedEisensteinLineNormSq_bounded ha cPlus
  obtain ⟨BMinus, hBMinus, hbMinus⟩ := exists_thetaCuspHawkingCompletedEisensteinLineNormSq_bounded ha cMinus
  have hTwo : Integrable (fun r : ℝ => thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus (-r) * thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus r) := by
    apply hOne.bdd_mul ((continuous_thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus).comp (by fun_prop)).aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbPlus (-r)
  have hThree : Integrable (fun r : ℝ =>
      thetaCuspHawkingCompletedEisensteinLineNormSq a cMinus r * (thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus (-r) * thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus r)) := by
    apply hTwo.bdd_mul (continuous_thetaCuspHawkingCompletedEisensteinLineNormSq a cMinus).aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbMinus r
  have hFour : Integrable (fun r : ℝ =>
      thetaCuspHawkingCompletedEisensteinLineNormSq a cMinus (-r) *
        (thetaCuspHawkingCompletedEisensteinLineNormSq a cMinus r * (thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus (-r) * thetaCuspHawkingCompletedEisensteinLineNormSq a cPlus r))) := by
    apply hThree.bdd_mul ((continuous_thetaCuspHawkingCompletedEisensteinLineNormSq a cMinus).comp (by fun_prop)).aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbMinus (-r)
  apply hFour.congr
  filter_upwards with r
  rw [thetaCuspHawkingCompletedEisensteinContinuumDensity_eq_lineFactors]
  simp only [a, cPlus, cMinus]
  ring

/-- Finite discrete QNM/Maass contribution to optical energy. -/
def thetaCuspHawkingEKGDiscreteOpticalEnergy {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) : ℝ :=
  ∑ j ∈ modes, ‖amplitude j‖ ^ (2 : ℕ)

/-- Every finite discrete optical contribution is nonnegative. -/
theorem thetaCuspHawkingEKGDiscreteOpticalEnergy_nonneg {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) :
    0 ≤ thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude := by
  unfold thetaCuspHawkingEKGDiscreteOpticalEnergy
  positivity

/-- Full finite-discrete plus on-shell continuum optical-energy output. -/
def thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) (q : XiZeroCopy) (t E₀ : ℝ) : ℝ :=
  thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude + 2 * Real.pi * thetaCuspHawkingCompletedEisensteinContinuumDensity q t E₀

/-- Exact Weisskopf--Wigner discrete-plus-continuum optical identity. -/
theorem thetaCuspHawkingEKG_discretePlusContinuumOpticalEnergyIdentity {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) (q : XiZeroCopy) (t E₀ : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude -
        2 * (GaloisForLFunctions.HTGeometry.levelSelfEnergy (thetaCuspHawkingCompletedEisensteinContinuumDensity q t) E₀ ε).im)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy modes amplitude q t E₀)) := by
  have hc : ContinuousAt (thetaCuspHawkingCompletedEisensteinContinuumDensity q t) E₀ :=
    (continuous_thetaCuspHawkingCompletedEisensteinContinuumDensity q t).continuousAt
  have hcontinuum := GaloisForLFunctions.HTGeometry.tendsto_levelSelfEnergy_rate
    (E₀ := E₀) (integrable_thetaCuspHawkingCompletedEisensteinContinuumDensity q t) hc
  have hdisc : Filter.Tendsto
      (fun _ : ℝ => thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude)) := tendsto_const_nhds
  have htotal := hdisc.add hcontinuum
  rw [thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy]
  convert htotal using 1
  funext ε
  ring

/-- A bright completed continuum vertex makes total optical energy strictly positive. -/
theorem thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy_pos_of_vertex_ne_zero
    {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) (q : XiZeroCopy) (t E₀ : ℝ)
    (hvertex : thetaCuspHawkingCompletedEisensteinPhysicalVertex (xiSpectralPoint q) E₀ t ≠ 0) :
    0 < thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy modes amplitude q t E₀ := by
  have hd := thetaCuspHawkingEKGDiscreteOpticalEnergy_nonneg modes amplitude
  have hc : 0 < thetaCuspHawkingCompletedEisensteinContinuumDensity q t E₀ := by
    rw [thetaCuspHawkingCompletedEisensteinContinuumDensity]
    exact sq_pos_of_pos (norm_pos_iff.mpr hvertex)
  rw [thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy]
  positivity

/-- **Pole/shadow-zero no-go.** Same bright EKG angular vertex couples both scattering sheets. -/
theorem thetaCuspHawkingXiDivisor_pole_shadowZero_brightCompletedEisensteinVertex
    (q : XiZeroCopy) (t : ℝ) :
    meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering (xiSpectralPoint q) < 0 ∧
      (AnalyticAt ℂ thetaCuspHawkingOpticalCuspScattering
          (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) ∧
        thetaCuspHawkingOpticalCuspScattering
          (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) = 0) ∧
      ∃ r : ℝ,
        thetaCuspHawkingCompletedEisensteinPhysicalVertex (xiSpectralPoint q) r t ≠ 0 ∧
        thetaCuspHawkingCompletedEisensteinPhysicalVertex
          (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) r t ≠ 0 := by
  refine ⟨thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q,
    thetaCuspHawkingOpticalCuspShadow_xiSpectralPoint_isZero q, ?_⟩
  obtain ⟨r, hr⟩ := exists_thetaCuspHawkingCompletedEisensteinPhysicalVertex_ne_zero (xiSpectralPoint q) t
  refine ⟨r, hr, ?_⟩
  rwa [thetaCuspHawkingCompletedEisensteinPhysicalVertex_shadow]

/-- Every Xi scattering pole has a bright positive discrete-plus-continuum optical channel. -/
theorem thetaCuspHawkingXiDivisor_pole_bright_discretePlusContinuumOpticalIdentity
    {ι : Type*}
    (modes : Finset ι) (amplitude : ι → ℂ) (q : XiZeroCopy) (t : ℝ) :
    meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering (xiSpectralPoint q) < 0 ∧
      ∃ E₀ : ℝ,
        0 < thetaCuspHawkingCompletedEisensteinContinuumDensity q t E₀ ∧
        Filter.Tendsto
          (fun ε : ℝ => thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude -
            2 * (GaloisForLFunctions.HTGeometry.levelSelfEnergy
              (thetaCuspHawkingCompletedEisensteinContinuumDensity q t) E₀ ε).im)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds (thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy modes amplitude q t E₀)) ∧
        0 < thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy modes amplitude q t E₀ := by
  refine ⟨thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q, ?_⟩
  obtain ⟨E₀, hE₀⟩ := exists_thetaCuspHawkingCompletedEisensteinPhysicalVertex_ne_zero (xiSpectralPoint q) t
  refine ⟨E₀, ?_, thetaCuspHawkingEKG_discretePlusContinuumOpticalEnergyIdentity modes amplitude q t E₀,
    thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy_pos_of_vertex_ne_zero
      modes amplitude q t E₀ hE₀⟩
  rw [thetaCuspHawkingCompletedEisensteinContinuumDensity]
  exact sq_pos_of_pos (norm_pos_iff.mpr hE₀)

/-- **Full linear-plus-nonlinear incidence packet.**  Xi divisor is scattering pole with analytic
shadow zero; shadow swaps exact topological-black-hole QNM branches; canonical Hawking splitting
is exactly zero tilt; nevertheless completed EKG angular backreaction has a bright positive
discrete-plus-continuum channel on every divisor.  Hence unsigned optical energy does not select
canonical split. -/
theorem thetaCuspHawkingXiDivisor_topologicalBlackHoleQNM_completedEKGOpticalIncidence
    {ι : Type*} (n : ℕ) (modes : Finset ι) (amplitude : ι → ℂ)
    (q : XiZeroCopy) (t : ℝ) :
    meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering (xiSpectralPoint q) < 0 ∧
      AnalyticAt ℂ thetaCuspHawkingOpticalCuspScattering
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) ∧
      thetaCuspHawkingOpticalCuspScattering
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) = 0 ∧
      thetaCuspHawkingTopologicalBlackHoleQNMPlus n
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) =
          thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q) ∧
      (thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting n
          (xiSpectralPoint q) = 1 / 2 ↔
        (xiSpectralPoint q).im = 0) ∧
      ∃ E₀ : ℝ,
        0 < thetaCuspHawkingCompletedEisensteinContinuumDensity q t E₀ ∧
        Filter.Tendsto
          (fun ε : ℝ => thetaCuspHawkingEKGDiscreteOpticalEnergy modes amplitude -
            2 * (GaloisForLFunctions.HTGeometry.levelSelfEnergy
              (thetaCuspHawkingCompletedEisensteinContinuumDensity q t) E₀ ε).im)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds (thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy
            modes amplitude q t E₀)) ∧
        0 < thetaCuspHawkingEKGDiscretePlusContinuumOpticalEnergy
          modes amplitude q t E₀ := by
  rcases thetaCuspHawkingXiDivisor_topologicalBlackHoleQNM_incidence n q with
    ⟨hpole, hanalytic, hzero, hqnm, hsplit⟩
  rcases thetaCuspHawkingXiDivisor_pole_bright_discretePlusContinuumOpticalIdentity
      modes amplitude q t with
    ⟨_hpole, E₀, hdensity, hoptical, hpositive⟩
  exact ⟨hpole, hanalytic, hzero, hqnm, hsplit,
    E₀, hdensity, hoptical, hpositive⟩

end RHTower
