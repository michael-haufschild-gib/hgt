import GaloisForLFunctions.RHTower.XiCTaylorSignedAtomicJetControllability

/-!
# Arbitrary two-atom scalar screens lock to half turns and reflect rigidly

The quarter-turn signed packet is not special.  For two distinct active real source atoms, the
scalar jet equations `G = 1` and `H = iq` force both source phases onto the half-turn lattice.
After mesh normalization, value and derivative equations converge to a projective value ray and
a nonzero charge equation.  Reflecting the centered height changes the two value coefficients by
different positive exponential factors.  One common projective ray at a functional-equation pair
therefore forces centered height zero.

The final theorem applies this mechanism directly to the Xi anisotropic mesh.  Supports may move
with the mesh, but must converge to two distinct positive times and be common to the reflected
fibres.  No quarter-turn spacing or explicit inverse formula is assumed.
-/

open Complex Real

namespace RHTower

noncomputable section

theorem spectralTranslationPhase_re_eq (t : ℝ) (z : ℂ) :
    (spectralTranslationPhase t z).re =
      Real.exp (-t * z.im) * Real.cos (t * z.re) := by
  rw [spectralTranslationPhase, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

theorem spectralTranslationPhase_im_eq (t : ℝ) (z : ℂ) :
    (spectralTranslationPhase t z).im =
      Real.exp (-t * z.im) * Real.sin (t * z.re) := by
  rw [spectralTranslationPhase, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]

/-- Literal completion carried by two real signed source atoms at arbitrary source times. -/
def signedTwoAtomCompletion
    (t₁ t₂ a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  (a₁ : ℂ) * (1 - spectralTranslationPhase t₁ z) +
  (a₂ : ℂ) * (1 - spectralTranslationPhase t₂ z)

/-- First spectral derivative of the arbitrary two-atom completion. -/
def signedTwoAtomCompletionDerivative
    (t₁ t₂ a₁ a₂ : ℝ) (z : ℂ) : ℂ :=
  (a₁ : ℂ) * (-((t₁ : ℂ) * I) * spectralTranslationPhase t₁ z) +
  (a₂ : ℂ) * (-((t₂ : ℂ) * I) * spectralTranslationPhase t₂ z)

theorem signedTwoAtomCompletion_im
    (t₁ t₂ a₁ a₂ : ℝ) (z : ℂ) :
    (signedTwoAtomCompletion t₁ t₂ a₁ a₂ z).im =
      -(a₁ * Real.exp (-t₁ * z.im) * Real.sin (t₁ * z.re) +
        a₂ * Real.exp (-t₂ * z.im) * Real.sin (t₂ * z.re)) := by
  simp [signedTwoAtomCompletion, Complex.mul_im,
    spectralTranslationPhase_im_eq]
  ring

theorem signedTwoAtomCompletionDerivative_re
    (t₁ t₂ a₁ a₂ : ℝ) (z : ℂ) :
    (signedTwoAtomCompletionDerivative t₁ t₂ a₁ a₂ z).re =
      a₁ * t₁ * Real.exp (-t₁ * z.im) * Real.sin (t₁ * z.re) +
        a₂ * t₂ * Real.exp (-t₂ * z.im) * Real.sin (t₂ * z.re) := by
  simp [signedTwoAtomCompletionDerivative, Complex.mul_re, Complex.mul_im,
    spectralTranslationPhase_re_eq, spectralTranslationPhase_im_eq]
  ring

/-- Two distinct active atoms carrying a scalar horizontal jet must both have real phase.
Equivalently, both source phases lie on the half-turn lattice. -/
theorem signedTwoAtomScalarJet_forces_halfTurns
    {t₁ t₂ a₁ a₂ u y q : ℝ}
    (ht : t₁ ≠ t₂) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hG : signedTwoAtomCompletion t₁ t₂ a₁ a₂ ⟨u, y⟩ = 1)
    (hH : signedTwoAtomCompletionDerivative t₁ t₂ a₁ a₂ ⟨u, y⟩ =
      I * (q : ℂ)) :
    Real.sin (t₁ * u) = 0 ∧ Real.sin (t₂ * u) = 0 := by
  have hGim := congrArg Complex.im hG
  have hHre := congrArg Complex.re hH
  rw [signedTwoAtomCompletion_im] at hGim
  rw [signedTwoAtomCompletionDerivative_re] at hHre
  norm_num at hGim hHre
  have hGsum :
      a₁ * Real.exp (-(t₁ * y)) * Real.sin (t₁ * u) +
        a₂ * Real.exp (-(t₂ * y)) * Real.sin (t₂ * u) = 0 := by
    linear_combination -hGim
  have hHsum :
      a₁ * t₁ * Real.exp (-(t₁ * y)) * Real.sin (t₁ * u) +
        a₂ * t₂ * Real.exp (-(t₂ * y)) * Real.sin (t₂ * u) = 0 := by
    linear_combination hHre
  have hsin₁prod :
      (a₁ * Real.exp (-(t₁ * y)) * (t₁ - t₂)) *
        Real.sin (t₁ * u) = 0 := by
    linear_combination hHsum - t₂ * hGsum
  have hcoeff₁ :
      a₁ * Real.exp (-(t₁ * y)) * (t₁ - t₂) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero ha₁ (Real.exp_pos _).ne')
      (sub_ne_zero.mpr ht)
  have hsin₁ : Real.sin (t₁ * u) = 0 :=
    (mul_eq_zero.mp hsin₁prod).resolve_left hcoeff₁
  have hsin₂prod :
      (a₂ * Real.exp (-(t₂ * y))) * Real.sin (t₂ * u) = 0 := by
    simpa [hsin₁] using hGsum
  have hcoeff₂ : a₂ * Real.exp (-(t₂ * y)) ≠ 0 :=
    mul_ne_zero ha₂ (Real.exp_pos _).ne'
  exact ⟨hsin₁, (mul_eq_zero.mp hsin₂prod).resolve_left hcoeff₂⟩

/-- Real value coefficient of one source atom at `u + iy`. -/
def signedTwoAtomValueCoefficient (t u y : ℝ) : ℝ :=
  1 - Real.exp (-(t * y)) * Real.cos (t * u)

/-- Imaginary derivative coefficient of one source atom at `u + iy`. -/
def signedTwoAtomDerivativeCoefficient (t u y : ℝ) : ℝ :=
  -t * Real.exp (-(t * y)) * Real.cos (t * u)

theorem signedTwoAtomCompletion_re
    (t₁ t₂ a₁ a₂ : ℝ) (z : ℂ) :
    (signedTwoAtomCompletion t₁ t₂ a₁ a₂ z).re =
      a₁ * signedTwoAtomValueCoefficient t₁ z.re z.im +
        a₂ * signedTwoAtomValueCoefficient t₂ z.re z.im := by
  simp [signedTwoAtomCompletion, signedTwoAtomValueCoefficient,
    Complex.mul_re, spectralTranslationPhase_re_eq]

theorem signedTwoAtomCompletionDerivative_im
    (t₁ t₂ a₁ a₂ : ℝ) (z : ℂ) :
    (signedTwoAtomCompletionDerivative t₁ t₂ a₁ a₂ z).im =
      a₁ * signedTwoAtomDerivativeCoefficient t₁ z.re z.im +
        a₂ * signedTwoAtomDerivativeCoefficient t₂ z.re z.im := by
  simp [signedTwoAtomCompletionDerivative, signedTwoAtomDerivativeCoefficient,
    Complex.mul_re, Complex.mul_im, spectralTranslationPhase_re_eq,
    spectralTranslationPhase_im_eq]
  ring

/-- Finite-mesh value fingerprint for arbitrary two-atom scalar screens. -/
theorem signedTwoAtomScaledValueFingerprint
    {δ t₁ t₂ a₁ a₂ u y : ℝ}
    (hG : signedTwoAtomCompletion t₁ t₂ a₁ a₂ ⟨u, y⟩ = 1) :
    (δ * a₁) * signedTwoAtomValueCoefficient t₁ u y +
      (δ * a₂) * signedTwoAtomValueCoefficient t₂ u y = δ := by
  have hGre := congrArg Complex.re hG
  rw [signedTwoAtomCompletion_re] at hGre
  norm_num at hGre
  linear_combination δ * hGre

/-- Finite-mesh derivative fingerprint.  Its limit is the screened divisor charge. -/
theorem signedTwoAtomScaledDerivativeFingerprint
    {δ t₁ t₂ a₁ a₂ u y q : ℝ}
    (hH : signedTwoAtomCompletionDerivative t₁ t₂ a₁ a₂ ⟨u, y⟩ =
      I * (q : ℂ)) :
    (δ * a₁) * signedTwoAtomDerivativeCoefficient t₁ u y +
      (δ * a₂) * signedTwoAtomDerivativeCoefficient t₂ u y = δ * q := by
  have hHim := congrArg Complex.im hH
  rw [signedTwoAtomCompletionDerivative_im] at hHim
  norm_num at hHim
  linear_combination δ * hHim

theorem tendsto_signedTwoAtomValueCoefficient
    {t u y : ℕ → ℝ} {t₀ u₀ y₀ : ℝ}
    (ht : Filter.Tendsto t Filter.atTop (nhds t₀))
    (hu : Filter.Tendsto u Filter.atTop (nhds u₀))
    (hy : Filter.Tendsto y Filter.atTop (nhds y₀)) :
    Filter.Tendsto
      (fun n => signedTwoAtomValueCoefficient (t n) (u n) (y n))
      Filter.atTop
      (nhds (signedTwoAtomValueCoefficient t₀ u₀ y₀)) := by
  have hexp : Filter.Tendsto
      (fun n => Real.exp (-((t n) * (y n))))
      Filter.atTop (nhds (Real.exp (-(t₀ * y₀)))) :=
    (Real.continuous_exp.tendsto _).comp (ht.mul hy).neg
  have hcos : Filter.Tendsto
      (fun n => Real.cos ((t n) * (u n)))
      Filter.atTop (nhds (Real.cos (t₀ * u₀))) :=
    (Real.continuous_cos.tendsto _).comp (ht.mul hu)
  simpa only [signedTwoAtomValueCoefficient] using
    tendsto_const_nhds.sub (hexp.mul hcos)

theorem tendsto_signedTwoAtomDerivativeCoefficient
    {t u y : ℕ → ℝ} {t₀ u₀ y₀ : ℝ}
    (ht : Filter.Tendsto t Filter.atTop (nhds t₀))
    (hu : Filter.Tendsto u Filter.atTop (nhds u₀))
    (hy : Filter.Tendsto y Filter.atTop (nhds y₀)) :
    Filter.Tendsto
      (fun n => signedTwoAtomDerivativeCoefficient (t n) (u n) (y n))
      Filter.atTop
      (nhds (signedTwoAtomDerivativeCoefficient t₀ u₀ y₀)) := by
  have hexp : Filter.Tendsto
      (fun n => Real.exp (-((t n) * (y n))))
      Filter.atTop (nhds (Real.exp (-(t₀ * y₀)))) :=
    (Real.continuous_exp.tendsto _).comp (ht.mul hy).neg
  have hcos : Filter.Tendsto
      (fun n => Real.cos ((t n) * (u n)))
      Filter.atTop (nhds (Real.cos (t₀ * u₀))) :=
    (Real.continuous_cos.tendsto _).comp (ht.mul hu)
  simpa only [signedTwoAtomDerivativeCoefficient] using
    (ht.neg.mul hexp).mul hcos

/-- Any convergent normalized two-atom screen has both an exact limiting value ray and an exact
limiting charge equation. -/
theorem tendsto_signedTwoAtomFingerprints
    {δ t₁ t₂ u y a₁ a₂ q : ℕ → ℝ}
    {t₁₀ t₂₀ u₀ y₀ b₁ b₂ m : ℝ}
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (ht₁ : Filter.Tendsto t₁ Filter.atTop (nhds t₁₀))
    (ht₂ : Filter.Tendsto t₂ Filter.atTop (nhds t₂₀))
    (hu : Filter.Tendsto u Filter.atTop (nhds u₀))
    (hy : Filter.Tendsto y Filter.atTop (nhds y₀))
    (hb₁ : Filter.Tendsto (fun n => δ n * a₁ n)
      Filter.atTop (nhds b₁))
    (hb₂ : Filter.Tendsto (fun n => δ n * a₂ n)
      Filter.atTop (nhds b₂))
    (hq : Filter.Tendsto (fun n => δ n * q n)
      Filter.atTop (nhds m))
    (hG : ∀ n,
      signedTwoAtomCompletion (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨u n, y n⟩ = 1)
    (hH : ∀ n,
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨u n, y n⟩ = I * ((q n : ℝ) : ℂ)) :
    signedTwoAtomValueCoefficient t₁₀ u₀ y₀ * b₁ +
        signedTwoAtomValueCoefficient t₂₀ u₀ y₀ * b₂ = 0 ∧
      signedTwoAtomDerivativeCoefficient t₁₀ u₀ y₀ * b₁ +
        signedTwoAtomDerivativeCoefficient t₂₀ u₀ y₀ * b₂ = m := by
  have hg₁ := tendsto_signedTwoAtomValueCoefficient ht₁ hu hy
  have hg₂ := tendsto_signedTwoAtomValueCoefficient ht₂ hu hy
  have hd₁ := tendsto_signedTwoAtomDerivativeCoefficient ht₁ hu hy
  have hd₂ := tendsto_signedTwoAtomDerivativeCoefficient ht₂ hu hy
  have hvalueLeft := (hb₁.mul hg₁).add (hb₂.mul hg₂)
  have hderivLeft := (hb₁.mul hd₁).add (hb₂.mul hd₂)
  have hvalueLeft' : Filter.Tendsto
      (fun n =>
        (δ n * a₁ n) * signedTwoAtomValueCoefficient (t₁ n) (u n) (y n) +
          (δ n * a₂ n) *
            signedTwoAtomValueCoefficient (t₂ n) (u n) (y n))
      Filter.atTop
      (nhds (signedTwoAtomValueCoefficient t₁₀ u₀ y₀ * b₁ +
        signedTwoAtomValueCoefficient t₂₀ u₀ y₀ * b₂)) := by
    simpa only [mul_comm] using hvalueLeft
  have hderivLeft' : Filter.Tendsto
      (fun n =>
        (δ n * a₁ n) *
            signedTwoAtomDerivativeCoefficient (t₁ n) (u n) (y n) +
          (δ n * a₂ n) *
            signedTwoAtomDerivativeCoefficient (t₂ n) (u n) (y n))
      Filter.atTop
      (nhds (signedTwoAtomDerivativeCoefficient t₁₀ u₀ y₀ * b₁ +
        signedTwoAtomDerivativeCoefficient t₂₀ u₀ y₀ * b₂)) := by
    simpa only [mul_comm] using hderivLeft
  have hvalueEq :
      (fun n =>
        (δ n * a₁ n) * signedTwoAtomValueCoefficient (t₁ n) (u n) (y n) +
          (δ n * a₂ n) *
            signedTwoAtomValueCoefficient (t₂ n) (u n) (y n)) = δ := by
    funext n
    exact signedTwoAtomScaledValueFingerprint (hG n)
  have hderivEq :
      (fun n =>
        (δ n * a₁ n) *
            signedTwoAtomDerivativeCoefficient (t₁ n) (u n) (y n) +
          (δ n * a₂ n) *
            signedTwoAtomDerivativeCoefficient (t₂ n) (u n) (y n)) =
        (fun n => δ n * q n) := by
    funext n
    exact signedTwoAtomScaledDerivativeFingerprint (hH n)
  constructor
  · have hzero := hδ
    rw [← hvalueEq] at hzero
    exact tendsto_nhds_unique hvalueLeft' hzero
  · rw [← hderivEq] at hq
    exact tendsto_nhds_unique hderivLeft' hq

/-- Nonzero limiting divisor charge forces a nonzero normalized source ray. -/
theorem signedTwoAtomNormalizedPair_ne_zero_of_charge
    {t₁ t₂ u y b₁ b₂ m : ℝ}
    (hm : m ≠ 0)
    (hcharge : signedTwoAtomDerivativeCoefficient t₁ u y * b₁ +
      signedTwoAtomDerivativeCoefficient t₂ u y * b₂ = m) :
    b₁ ≠ 0 ∨ b₂ ≠ 0 := by
  by_contra hpair
  have hb₁ : b₁ = 0 := by
    by_contra hb₁
    exact hpair (Or.inl hb₁)
  have hb₂ : b₂ = 0 := by
    by_contra hb₂
    exact hpair (Or.inr hb₂)
  rw [hb₁, hb₂, mul_zero, mul_zero, add_zero] at hcharge
  exact hm hcharge.symm

/-- Phase locking survives convergent moving support. -/
theorem tendsto_signedTwoAtomScalarPhaseLock
    {t₁ t₂ u y a₁ a₂ q : ℕ → ℝ} {t₁₀ t₂₀ u₀ : ℝ}
    (ht₁ : Filter.Tendsto t₁ Filter.atTop (nhds t₁₀))
    (ht₂ : Filter.Tendsto t₂ Filter.atTop (nhds t₂₀))
    (hu : Filter.Tendsto u Filter.atTop (nhds u₀))
    (ht : ∀ n, t₁ n ≠ t₂ n)
    (ha₁ : ∀ n, a₁ n ≠ 0) (ha₂ : ∀ n, a₂ n ≠ 0)
    (hG : ∀ n,
      signedTwoAtomCompletion (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨u n, y n⟩ = 1)
    (hH : ∀ n,
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨u n, y n⟩ = I * ((q n : ℝ) : ℂ)) :
    Real.sin (t₁₀ * u₀) = 0 ∧ Real.sin (t₂₀ * u₀) = 0 := by
  have hlock (n : ℕ) :
      Real.sin (t₁ n * u n) = 0 ∧
        Real.sin (t₂ n * u n) = 0 :=
    signedTwoAtomScalarJet_forces_halfTurns
      (ht n) (ha₁ n) (ha₂ n) (hG n) (hH n)
  have hsin₁ : Filter.Tendsto
      (fun n => Real.sin (t₁ n * u n))
      Filter.atTop (nhds (Real.sin (t₁₀ * u₀))) :=
    (Real.continuous_sin.tendsto _).comp (ht₁.mul hu)
  have hsin₂ : Filter.Tendsto
      (fun n => Real.sin (t₂ n * u n))
      Filter.atTop (nhds (Real.sin (t₂₀ * u₀))) :=
    (Real.continuous_sin.tendsto _).comp (ht₂.mul hu)
  have hzero₁ : Filter.Tendsto
      (fun n => Real.sin (t₁ n * u n))
      Filter.atTop (nhds 0) := by
    simpa only [fun n => (hlock n).1] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  have hzero₂ : Filter.Tendsto
      (fun n => Real.sin (t₂ n * u n))
      Filter.atTop (nhds 0) := by
    simpa only [fun n => (hlock n).2] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  exact ⟨tendsto_nhds_unique hsin₁ hzero₁,
    tendsto_nhds_unique hsin₂ hzero₂⟩

theorem cos_sq_one_of_sin_eq_zero
    {x : ℝ} (hsin : Real.sin x = 0) :
    Real.cos x ^ 2 = 1 := by
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- Exact change of a half-turn value coefficient under centered reflection `y ↦ -y`. -/
theorem signedTwoAtomValueCoefficient_reflection
    {t u y : ℝ} (hsin : Real.sin (t * u) = 0) :
    signedTwoAtomValueCoefficient t u (-y) =
      -Real.cos (t * u) * Real.exp (t * y) *
        signedTwoAtomValueCoefficient t u y := by
  have hcos := cos_sq_one_of_sin_eq_zero hsin
  have hexp :
      Real.exp (t * y) * Real.exp (-(t * y)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [signedTwoAtomValueCoefficient]
  rw [show -(t * -y) = t * y by ring]
  nlinarith

/-- Away from the centered line, a positive-time half-turn value coefficient cannot vanish. -/
theorem signedTwoAtomValueCoefficient_ne_zero
    {t u y : ℝ} (ht : 0 < t) (hy : y ≠ 0)
    (hsin : Real.sin (t * u) = 0) :
    signedTwoAtomValueCoefficient t u y ≠ 0 := by
  intro hg
  have hcos := cos_sq_one_of_sin_eq_zero hsin
  have hpc :
      Real.exp (-(t * y)) * Real.cos (t * u) = 1 :=
    (sub_eq_zero.mp hg).symm
  have hp_sq : Real.exp (-(t * y)) ^ 2 = 1 := by
    have hsquare := congrArg (fun x : ℝ => x ^ 2) hpc
    nlinarith
  have hp : Real.exp (-(t * y)) = 1 := by
    nlinarith [Real.exp_pos (-(t * y))]
  have harg : -(t * y) = 0 :=
    (Real.exp_eq_one_iff (-(t * y))).mp hp
  apply hy
  nlinarith

/-- Two nonzero normalized half-turn charge rays at reflected heights can be projectively equal
only at centered height zero. -/
theorem signedTwoAtomReflectionProjectiveFingerprint_rigid
    {t₁ t₂ u y b₁ b₂ c₁ c₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ht : t₁ ≠ t₂)
    (hsin₁ : Real.sin (t₁ * u) = 0)
    (hsin₂ : Real.sin (t₂ * u) = 0)
    (hb : b₁ ≠ 0 ∨ b₂ ≠ 0)
    (hc : c₁ ≠ 0 ∨ c₂ ≠ 0)
    (hray : signedTwoAtomValueCoefficient t₁ u y * b₁ +
      signedTwoAtomValueCoefficient t₂ u y * b₂ = 0)
    (hmat : signedTwoAtomValueCoefficient t₁ u (-y) * c₁ +
      signedTwoAtomValueCoefficient t₂ u (-y) * c₂ = 0)
    (hprojective : b₁ * c₂ = c₁ * b₂) :
    y = 0 := by
  by_contra hy
  have hg₁ : signedTwoAtomValueCoefficient t₁ u y ≠ 0 :=
    signedTwoAtomValueCoefficient_ne_zero ht₁ hy hsin₁
  have hg₂ : signedTwoAtomValueCoefficient t₂ u y ≠ 0 :=
    signedTwoAtomValueCoefficient_ne_zero ht₂ hy hsin₂
  have hb₁ : b₁ ≠ 0 := by
    intro hb₁
    have hb₂ : b₂ = 0 := by
      rw [hb₁, mul_zero, zero_add] at hray
      exact (mul_eq_zero.mp hray).resolve_left hg₂
    exact hb.elim (fun h => h hb₁) (fun h => h hb₂)
  have hb₂ : b₂ ≠ 0 := by
    intro hb₂
    have hb₁ : b₁ = 0 := by
      rw [hb₂, mul_zero, add_zero] at hray
      exact (mul_eq_zero.mp hray).resolve_left hg₁
    exact hb.elim (fun h => h hb₁) (fun h => h hb₂)
  have hc₁ : c₁ ≠ 0 := by
    intro hc₁
    have hc₂ : c₂ = 0 := by
      rw [hc₁, zero_mul] at hprojective
      exact (mul_eq_zero.mp hprojective).resolve_left hb₁
    exact hc.elim (fun h => h hc₁) (fun h => h hc₂)
  have hc₂ : c₂ ≠ 0 := by
    intro hc₂
    have hc₁ : c₁ = 0 := by
      rw [hc₂, mul_zero] at hprojective
      exact (mul_eq_zero.mp hprojective.symm).resolve_right hb₂
    exact hc.elim (fun h => h hc₁) (fun h => h hc₂)
  have hrowProjective :
      signedTwoAtomValueCoefficient t₁ u y *
          signedTwoAtomValueCoefficient t₂ u (-y) =
        signedTwoAtomValueCoefficient t₁ u (-y) *
          signedTwoAtomValueCoefficient t₂ u y := by
    have hbrow :
        signedTwoAtomValueCoefficient t₁ u y * b₁ =
          -(signedTwoAtomValueCoefficient t₂ u y * b₂) := by
      linarith
    have hcrow :
        signedTwoAtomValueCoefficient t₂ u (-y) * c₂ =
          -(signedTwoAtomValueCoefficient t₁ u (-y) * c₁) := by
      linarith
    have hbc : b₁ * c₂ ≠ 0 := mul_ne_zero hb₁ hc₂
    apply mul_left_cancel₀ hbc
    calc
      (b₁ * c₂) *
          (signedTwoAtomValueCoefficient t₁ u y *
            signedTwoAtomValueCoefficient t₂ u (-y)) =
          (signedTwoAtomValueCoefficient t₁ u y * b₁) *
            (signedTwoAtomValueCoefficient t₂ u (-y) * c₂) := by ring
      _ = (-(signedTwoAtomValueCoefficient t₂ u y * b₂)) *
            (-(signedTwoAtomValueCoefficient t₁ u (-y) * c₁)) := by
              rw [hbrow, hcrow]
      _ = (b₁ * c₂) *
          (signedTwoAtomValueCoefficient t₁ u (-y) *
            signedTwoAtomValueCoefficient t₂ u y) := by
            rw [hprojective]
            ring
  rw [signedTwoAtomValueCoefficient_reflection hsin₁,
    signedTwoAtomValueCoefficient_reflection hsin₂] at hrowProjective
  have hfactor :
      (Real.cos (t₁ * u) * Real.exp (t₁ * y) -
        Real.cos (t₂ * u) * Real.exp (t₂ * y)) *
        (signedTwoAtomValueCoefficient t₁ u y *
          signedTwoAtomValueCoefficient t₂ u y) = 0 := by
    linear_combination hrowProjective
  have hcosExp :
      Real.cos (t₁ * u) * Real.exp (t₁ * y) =
        Real.cos (t₂ * u) * Real.exp (t₂ * y) := by
    have hzero :=
      (mul_eq_zero.mp hfactor).resolve_right (mul_ne_zero hg₁ hg₂)
    linarith
  have hcos₁ := cos_sq_one_of_sin_eq_zero hsin₁
  have hcos₂ := cos_sq_one_of_sin_eq_zero hsin₂
  have hexpSq :
      Real.exp (t₁ * y) ^ 2 = Real.exp (t₂ * y) ^ 2 := by
    have hsquare := congrArg (fun x : ℝ => x ^ 2) hcosExp
    nlinarith
  have hexp :
      Real.exp (t₁ * y) = Real.exp (t₂ * y) := by
    nlinarith [Real.exp_pos (t₁ * y), Real.exp_pos (t₂ * y)]
  have hargs : t₁ * y = t₂ * y := Real.exp_injective hexp
  exact hy (by
    have : (t₁ - t₂) * y = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht))

/-- Full moving-support theorem.  Two common convergent source times, exact nonzero scalar charges
at reflected heights, and projectively coherent normalized weights force centered height zero. -/
theorem signedTwoAtomCrossMeshReflection_rigid
    {δ δm t₁ t₂ u um y ym a₁ a₂ c₁ c₂ q qm : ℕ → ℝ}
    {t₁₀ t₂₀ u₀ y₀ b₁ b₂ d₁ d₂ m mm : ℝ}
    (ht₁pos : 0 < t₁₀) (ht₂pos : 0 < t₂₀) (htlim : t₁₀ ≠ t₂₀)
    (hm : m ≠ 0) (hmm : mm ≠ 0)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδm : Filter.Tendsto δm Filter.atTop (nhds 0))
    (ht₁ : Filter.Tendsto t₁ Filter.atTop (nhds t₁₀))
    (ht₂ : Filter.Tendsto t₂ Filter.atTop (nhds t₂₀))
    (hu : Filter.Tendsto u Filter.atTop (nhds u₀))
    (hum : Filter.Tendsto um Filter.atTop (nhds u₀))
    (hy : Filter.Tendsto y Filter.atTop (nhds y₀))
    (hym : Filter.Tendsto ym Filter.atTop (nhds (-y₀)))
    (hb₁ : Filter.Tendsto (fun n => δ n * a₁ n)
      Filter.atTop (nhds b₁))
    (hb₂ : Filter.Tendsto (fun n => δ n * a₂ n)
      Filter.atTop (nhds b₂))
    (hd₁ : Filter.Tendsto (fun n => δm n * c₁ n)
      Filter.atTop (nhds d₁))
    (hd₂ : Filter.Tendsto (fun n => δm n * c₂ n)
      Filter.atTop (nhds d₂))
    (hq : Filter.Tendsto (fun n => δ n * q n)
      Filter.atTop (nhds m))
    (hqm : Filter.Tendsto (fun n => δm n * qm n)
      Filter.atTop (nhds mm))
    (ht : ∀ n, t₁ n ≠ t₂ n)
    (ha₁ : ∀ n, a₁ n ≠ 0) (ha₂ : ∀ n, a₂ n ≠ 0)
    (hG : ∀ n,
      signedTwoAtomCompletion (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨u n, y n⟩ = 1)
    (hH : ∀ n,
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨u n, y n⟩ = I * ((q n : ℝ) : ℂ))
    (hGm : ∀ n,
      signedTwoAtomCompletion (t₁ n) (t₂ n) (c₁ n) (c₂ n)
        ⟨um n, ym n⟩ = 1)
    (hHm : ∀ n,
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (c₁ n) (c₂ n)
        ⟨um n, ym n⟩ = I * ((qm n : ℝ) : ℂ))
    (hprojective : b₁ * d₂ = d₁ * b₂) :
    y₀ = 0 := by
  obtain ⟨hsin₁, hsin₂⟩ :=
    tendsto_signedTwoAtomScalarPhaseLock
      ht₁ ht₂ hu ht ha₁ ha₂ hG hH
  obtain ⟨hray, hcharge⟩ :=
    tendsto_signedTwoAtomFingerprints hδ ht₁ ht₂ hu hy
      hb₁ hb₂ hq hG hH
  obtain ⟨hraym, hchargem⟩ :=
    tendsto_signedTwoAtomFingerprints hδm ht₁ ht₂ hum hym
      hd₁ hd₂ hqm hGm hHm
  have hb : b₁ ≠ 0 ∨ b₂ ≠ 0 :=
    signedTwoAtomNormalizedPair_ne_zero_of_charge hm hcharge
  have hd : d₁ ≠ 0 ∨ d₂ ≠ 0 :=
    signedTwoAtomNormalizedPair_ne_zero_of_charge hmm hchargem
  exact signedTwoAtomReflectionProjectiveFingerprint_rigid
    ht₁pos ht₂pos htlim hsin₁ hsin₂ hb hd
    hray hraym hprojective

/-- Xi specialization: arbitrary convergent common two-atom support geometry is incompatible with
an off-critical-line reflection-coherent nonzero scalar screen. -/
theorem xiReflectionCoherent_signedTwoAtom_profile_forces_criticalLine
    {sigma : ℂ}
    {t₁ t₂ a₁ a₂ c₁ c₂ q qm : ℕ → ℝ}
    {t₁₀ t₂₀ b₁ b₂ d₁ d₂ m mm : ℝ}
    (ht₁pos : 0 < t₁₀) (ht₂pos : 0 < t₂₀) (htlim : t₁₀ ≠ t₂₀)
    (hm : m ≠ 0) (hmm : mm ≠ 0)
    (ht₁ : Filter.Tendsto t₁ Filter.atTop (nhds t₁₀))
    (ht₂ : Filter.Tendsto t₂ Filter.atTop (nhds t₂₀))
    (hb₁ : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep sigma n * a₁ n)
      Filter.atTop (nhds b₁))
    (hb₂ : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep sigma n * a₂ n)
      Filter.atTop (nhds b₂))
    (hd₁ : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma) n * c₁ n)
      Filter.atTop (nhds d₁))
    (hd₂ : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma) n * c₂ n)
      Filter.atTop (nhds d₂))
    (hq : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep sigma n * q n)
      Filter.atTop (nhds m))
    (hqm : Filter.Tendsto
      (fun n => xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma) n * qm n)
      Filter.atTop (nhds mm))
    (ht : ∀ n, t₁ n ≠ t₂ n)
    (ha₁ : ∀ n, a₁ n ≠ 0) (ha₂ : ∀ n, a₂ n ≠ 0)
    (hG : ∀ n,
      signedTwoAtomCompletion (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        (xiCTaylorAnisotropicCenteredPoint sigma n) = 1)
    (hH : ∀ n,
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        (xiCTaylorAnisotropicCenteredPoint sigma n) =
          I * ((q n : ℝ) : ℂ))
    (hGm : ∀ n,
      signedTwoAtomCompletion (t₁ n) (t₂ n) (c₁ n) (c₂ n)
        (xiCTaylorAnisotropicCenteredPoint
          (1 - starRingEnd ℂ sigma) n) = 1)
    (hHm : ∀ n,
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (c₁ n) (c₂ n)
        (xiCTaylorAnisotropicCenteredPoint
          (1 - starRingEnd ℂ sigma) n) =
            I * ((qm n : ℝ) : ℂ))
    (hprojective : b₁ * d₂ = d₁ * b₂) :
    sigma.re = 1 / 2 := by
  let z : ℕ → ℂ := xiCTaylorAnisotropicCenteredPoint sigma
  let zm : ℕ → ℂ :=
    xiCTaylorAnisotropicCenteredPoint (1 - starRingEnd ℂ sigma)
  have hz := tendsto_xiCTaylorAnisotropicCenteredPoint sigma
  have hzm :=
    tendsto_xiCTaylorAnisotropicCenteredPoint
      (1 - starRingEnd ℂ sigma)
  have hu : Filter.Tendsto (fun n => (z n).re)
      Filter.atTop (nhds sigma.im) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hz
    simpa [Function.comp_def, z, xiCTaylorCenteredPoint_re] using h
  have hum : Filter.Tendsto (fun n => (zm n).re)
      Filter.atTop (nhds sigma.im) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hzm
    simpa [Function.comp_def, zm, xiCTaylorCenteredPoint_re] using h
  have hy : Filter.Tendsto (fun n => (z n).im)
      Filter.atTop (nhds (1 / 2 - sigma.re)) := by
    have h := Complex.continuous_im.continuousAt.tendsto.comp hz
    simpa [Function.comp_def, z, xiCTaylorCenteredPoint_im] using h
  have hym : Filter.Tendsto (fun n => (zm n).im)
      Filter.atTop (nhds (-(1 / 2 - sigma.re))) := by
    have h := Complex.continuous_im.continuousAt.tendsto.comp hzm
    have h' : Filter.Tendsto (fun n => (zm n).im)
        Filter.atTop
        (nhds ((xiCTaylorCenteredPoint
          (1 - starRingEnd ℂ sigma)).im)) := by
      simpa [Function.comp_def, zm] using h
    convert h' using 1
    simp [xiCTaylorCenteredPoint_im]
    ring
  have hG' (n : ℕ) :
      signedTwoAtomCompletion (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨(z n).re, (z n).im⟩ = 1 := by
    simpa only [z, Complex.eta] using hG n
  have hH' (n : ℕ) :
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (a₁ n) (a₂ n)
        ⟨(z n).re, (z n).im⟩ = I * ((q n : ℝ) : ℂ) := by
    simpa only [z, Complex.eta] using hH n
  have hGm' (n : ℕ) :
      signedTwoAtomCompletion (t₁ n) (t₂ n) (c₁ n) (c₂ n)
        ⟨(zm n).re, (zm n).im⟩ = 1 := by
    simpa only [zm, Complex.eta] using hGm n
  have hHm' (n : ℕ) :
      signedTwoAtomCompletionDerivative (t₁ n) (t₂ n) (c₁ n) (c₂ n)
        ⟨(zm n).re, (zm n).im⟩ = I * ((qm n : ℝ) : ℂ) := by
    simpa only [zm, Complex.eta] using hHm n
  have hcenter :=
    signedTwoAtomCrossMeshReflection_rigid
      ht₁pos ht₂pos htlim hm hmm
      (tendsto_xiTaylorAnisotropicHorizontalStep sigma)
      (tendsto_xiTaylorAnisotropicHorizontalStep
        (1 - starRingEnd ℂ sigma))
      ht₁ ht₂ hu hum hy hym
      hb₁ hb₂ hd₁ hd₂ hq hqm ht ha₁ ha₂
      hG' hH' hGm' hHm' hprojective
  linarith

end

end RHTower
