import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The weighted formal adjoint of the Hedenmalm pair

In the weighted space `H_k = L²(ℝ, k⁻¹ dx)` the differential expression `D = -i ∂_x` has weighted
formal adjoint

`L = k D k⁻¹ = D + i k'/k`.

On compactly supported differentiable data this is a single integration by parts: the function
`f ḡ / k` has compact support, so its derivative integrates to zero, and the three terms of that
derivative are exactly the difference of the two sides of the weighted pairing.

Multiplication by the half density `k^{1/2}` conjugates the plain derivative into the derivative
shifted by half the logarithmic derivative of the source; that identity is the pointwise calculus
at the end.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile

/-! ### The logarithmic derivative of the source -/

/-- The derivative of the theta source. -/
def sourceDeriv (x : ℝ) : ℝ := deriv thetaCuspFullSource x

theorem hasDerivAt_thetaCuspFullSource (x : ℝ) :
    HasDerivAt thetaCuspFullSource (sourceDeriv x) x :=
  (contDiff_thetaCuspFullSource.differentiable (by simp) x).hasDerivAt

theorem continuous_sourceDeriv : Continuous sourceDeriv :=
  contDiff_thetaCuspFullSource.continuous_deriv (by simp)

/-- The logarithmic derivative `a = k'/k` of the theta source. -/
def sourceLogDeriv (x : ℝ) : ℝ := sourceDeriv x / thetaCuspFullSource x

theorem continuous_sourceLogDeriv : Continuous sourceLogDeriv :=
  continuous_sourceDeriv.div contDiff_thetaCuspFullSource.continuous
    fun x => (thetaCuspFullSource_pos x).ne'

/-! ### The complexified weight -/

/-- The complexified source weight. -/
def sourceWeightC (x : ℝ) : ℂ := ((thetaCuspFullSource x : ℝ) : ℂ)

theorem sourceWeightC_ne_zero (x : ℝ) : sourceWeightC x ≠ 0 := by
  rw [sourceWeightC]
  exact_mod_cast (thetaCuspFullSource_pos x).ne'

theorem continuous_sourceWeightC : Continuous sourceWeightC :=
  Complex.continuous_ofReal.comp contDiff_thetaCuspFullSource.continuous

theorem hasDerivAt_sourceWeightC (x : ℝ) :
    HasDerivAt sourceWeightC ((sourceDeriv x : ℝ) : ℂ) x :=
  (hasDerivAt_thetaCuspFullSource x).ofReal_comp

/-! ### The weighted pairing -/

theorem integral_weighted_symmetry_core {f g f' g' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfc' : Continuous f') (hgc' : Continuous g')
    (hfs : HasCompactSupport f) (hfs' : HasCompactSupport f') :
    (∫ x, (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x)
      = ∫ x, f x * (starRingEnd ℂ) (-Complex.I * g' x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x := by
  have hinv : Continuous fun x : ℝ => (sourceWeightC x)⁻¹ :=
    continuous_sourceWeightC.inv₀ sourceWeightC_ne_zero
  set F : ℝ → ℂ := fun x => f x * (starRingEnd ℂ) (g x) * (sourceWeightC x)⁻¹ with hF
  set F' : ℝ → ℂ := fun x =>
    (f' x * (starRingEnd ℂ) (g x) + f x * (starRingEnd ℂ) (g' x)) * (sourceWeightC x)⁻¹
      + f x * (starRingEnd ℂ) (g x) * (-((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x ^ (2 : ℕ)) with hF'
  have hderiv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have h1 : HasDerivAt (fun t => f t * (starRingEnd ℂ) (g t))
        (f' x * (starRingEnd ℂ) (g x) + f x * (starRingEnd ℂ) (g' x)) x := (hf x).mul (hg x).star
    have h2 : HasDerivAt (fun t => (sourceWeightC t)⁻¹)
        (-((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x ^ (2 : ℕ)) x :=
      (hasDerivAt_sourceWeightC x).inv (sourceWeightC_ne_zero x)
    exact h1.mul h2
  have hF'cont : Continuous F' := by
    rw [hF']
    refine Continuous.add ?_ ?_
    · exact ((hfc'.mul (Complex.continuous_conj.comp hgc)).add
        (hfc.mul (Complex.continuous_conj.comp hgc'))).mul hinv
    · refine (hfc.mul (Complex.continuous_conj.comp hgc)).mul ?_
      exact (Complex.continuous_ofReal.comp continuous_sourceDeriv).neg.div
        (continuous_sourceWeightC.pow 2) fun x => pow_ne_zero 2 (sourceWeightC_ne_zero x)
  have hFs : HasCompactSupport F := by
    rw [hF]
    exact (hfs.mul_right).mul_right
  have hFeq : deriv F = F' := funext fun x => (hderiv x).deriv
  have hFs' : HasCompactSupport F' := hFeq ▸ hFs.deriv
  have hzeroInf := hFs.is_zero_at_infty
  rw [cocompact_eq_atBot_atTop] at hzeroInf
  have hzero : (∫ x, F' x) = 0 := by
    have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv
      (hF'cont.integrable_of_hasCompactSupport hFs')
      (hzeroInf.mono_left le_sup_left) (hzeroInf.mono_left le_sup_right)
    simpa using h
  have hLcont : Continuous
      (fun x => (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x) :=
    ((continuous_const.mul hfc').mul (Complex.continuous_conj.comp hgc)).div
      continuous_sourceWeightC sourceWeightC_ne_zero
  have hLs : HasCompactSupport
      (fun x => (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x) := by
    have hrw : (fun x => (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x)
        = fun x => ((-Complex.I * f' x) * (starRingEnd ℂ) (g x)) * (sourceWeightC x)⁻¹ := by
      funext x
      rw [div_eq_mul_inv]
    rw [hrw]
    have h1 : HasCompactSupport (fun x => -Complex.I * f' x) := hfs'.mul_left
    exact (h1.mul_right).mul_right
  have hRcont : Continuous
      (fun x => f x * (starRingEnd ℂ) (-Complex.I * g' x
        + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x) := by
    refine Continuous.div (hfc.mul (Complex.continuous_conj.comp ?_)) continuous_sourceWeightC
      sourceWeightC_ne_zero
    exact (continuous_const.mul hgc').add
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_sourceLogDeriv)).mul hgc)
  have hRs : HasCompactSupport
      (fun x => f x * (starRingEnd ℂ) (-Complex.I * g' x
        + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x) := by
    have hrw : (fun x => f x * (starRingEnd ℂ) (-Complex.I * g' x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x)
        = fun x => (f x * (starRingEnd ℂ) (-Complex.I * g' x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x)) * (sourceWeightC x)⁻¹ := by
      funext x
      rw [div_eq_mul_inv]
    rw [hrw]
    exact (hfs.mul_right).mul_right
  have hpt : ∀ x, (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x
      - f x * (starRingEnd ℂ) (-Complex.I * g' x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x
      = -Complex.I * F' x := by
    intro x
    have hK := sourceWeightC_ne_zero x
    have ha : ((sourceLogDeriv x : ℝ) : ℂ) = ((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x := by
      rw [sourceLogDeriv, sourceWeightC, Complex.ofReal_div]
    have hconj : (starRingEnd ℂ) (-Complex.I * g' x
        + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x)
        = Complex.I * (starRingEnd ℂ) (g' x)
          - Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * (starRingEnd ℂ) (g x) := by
      simp only [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj, ha, hF']
    field_simp
    ring
  have hsub := MeasureTheory.integral_sub
    (hLcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hLs)
    (hRcont.integrable_of_hasCompactSupport (μ := (volume : Measure ℝ)) hRs)
  rw [← sub_eq_zero, ← hsub, integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, hzero, mul_zero]


/-- **The weighted formal symmetry of the Hedenmalm pair.**  For `f` in the compactly supported
`C¹` core and any `C¹` function `g`,

`⟨D f, g⟩_{H_k} = ⟨f, L g⟩_{H_k}`,  with `L = D + i k'/k`. -/
theorem integral_weighted_symmetry {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfs : HasCompactSupport f) :
    (∫ x, (-Complex.I * deriv f x) * (starRingEnd ℂ) (g x) / sourceWeightC x)
      = ∫ x, f x * (starRingEnd ℂ) (-Complex.I * deriv g x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x :=
  integral_weighted_symmetry_core
    (fun x => (hf.differentiable (by simp) x).hasDerivAt)
    (fun x => (hg.differentiable (by simp) x).hasDerivAt)
    hf.continuous hg.continuous
    (hf.continuous_deriv (by simp)) (hg.continuous_deriv (by simp))
    hfs hfs.deriv


/-! ### The formal Witten positivity -/

/-- **The second-order bulk is the energy form on the core.**  The weighted symmetry with `g = D f`
turns `⟨f, L D f⟩_{H_k}` into `⟨D f, D f⟩_{H_k}`, the nonnegative energy.  This is the formal
content of `L D = A^* A ≥ 0`. -/
theorem integral_weighted_witten {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f) :
    (∫ x, (-Complex.I * deriv f x) * (starRingEnd ℂ) (-Complex.I * deriv f x)
        / sourceWeightC x)
      = ∫ x, f x * (starRingEnd ℂ) (-Complex.I * deriv (fun t => -Complex.I * deriv f t) x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * (-Complex.I * deriv f x))
        / sourceWeightC x := by
  have hderiv : ContDiff ℝ 1 (deriv f) := ((contDiff_succ_iff_deriv).mp hf).2.2
  have hg : ContDiff ℝ 1 (fun t : ℝ => -Complex.I * deriv f t) := contDiff_const.mul hderiv
  exact integral_weighted_symmetry (hf.of_le (by norm_num)) hg hfs

/-- The energy form is real and nonnegative. -/
theorem integral_weighted_energy_nonneg (f' : ℝ → ℂ) :
    (∫ x, (-Complex.I * f' x) * (starRingEnd ℂ) (-Complex.I * f' x) / sourceWeightC x)
      = ((∫ x, ‖f' x‖ ^ (2 : ℕ) / thetaCuspFullSource x : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hk : ((thetaCuspFullSource x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (thetaCuspFullSource_pos x).ne'
  have hzz : (-Complex.I * f' x) * (starRingEnd ℂ) (-Complex.I * f' x)
      = ((‖f' x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (E := ℂ) (-Complex.I * f' x)
    rw [RCLike.inner_apply'] at h
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul] at h
    rw [mul_comm]
    push_cast
    exact h
  show (-Complex.I * f' x) * (starRingEnd ℂ) (-Complex.I * f' x)
      / ((thetaCuspFullSource x : ℝ) : ℂ)
    = ((‖f' x‖ ^ (2 : ℕ) / thetaCuspFullSource x : ℝ) : ℂ)
  rw [hzz, Complex.ofReal_div]



/-! ### The supersymmetric Dirac operator on the core -/

/-- The weighted pairing `⟨u, v⟩_{H_k} = ∫ u conj(v) / k`. -/
def weightedPair (u v : ℝ → ℂ) : ℂ :=
  ∫ x, u x * (starRingEnd ℂ) (v x) / sourceWeightC x

/-- The differential expression `D = -i ∂`. -/
def sourceD (f : ℝ → ℂ) (x : ℝ) : ℂ := -Complex.I * deriv f x

/-- The weighted formal adjoint `L = D + i k'/k`. -/
def sourceL (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * deriv g x + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x

theorem weightedPair_D_left {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfs : HasCompactSupport f) :
    weightedPair (sourceD f) g = weightedPair f (sourceL g) :=
  integral_weighted_symmetry hf hg hfs

/-- The conjugate form of the symmetry: `⟨L g, f⟩ = ⟨g, D f⟩`. -/
theorem conj_weightedPair_integrand (a b : ℂ) (x : ℝ) :
    (starRingEnd ℂ) (a * (starRingEnd ℂ) b / sourceWeightC x)
      = b * (starRingEnd ℂ) a / sourceWeightC x := by
  show (starRingEnd ℂ) (a * (starRingEnd ℂ) b / ((thetaCuspFullSource x : ℝ) : ℂ))
    = b * (starRingEnd ℂ) a / ((thetaCuspFullSource x : ℝ) : ℂ)
  rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- The conjugate form of the symmetry: `⟨L g, f⟩ = ⟨g, D f⟩`. -/
theorem weightedPair_L_left {f g : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfs : HasCompactSupport f) :
    weightedPair (sourceL g) f = weightedPair g (sourceD f) := by
  have h := integral_weighted_symmetry hf hg hfs
  have hL : ∀ x : ℝ, sourceL g x * (starRingEnd ℂ) (f x) / sourceWeightC x
      = (starRingEnd ℂ) (f x * (starRingEnd ℂ) (sourceL g x) / sourceWeightC x) :=
    fun x => (conj_weightedPair_integrand (f x) (sourceL g x) x).symm
  have hR : ∀ x : ℝ, g x * (starRingEnd ℂ) (sourceD f x) / sourceWeightC x
      = (starRingEnd ℂ) (sourceD f x * (starRingEnd ℂ) (g x) / sourceWeightC x) :=
    fun x => (conj_weightedPair_integrand (sourceD f x) (g x) x).symm
  rw [weightedPair, weightedPair,
    integral_congr_ae (Filter.Eventually.of_forall hL),
    integral_congr_ae (Filter.Eventually.of_forall hR),
    integral_conj, integral_conj]
  exact congrArg (starRingEnd ℂ) h.symm

/-- **The supersymmetric Dirac operator is formally symmetric on the core.**  Two applications of
the weighted symmetry, one in each channel. -/
theorem weightedPair_dirac_symmetry {f₁ g₁ f₂ g₂ : ℝ → ℂ}
    (hf₁ : ContDiff ℝ 1 f₁) (hg₁ : ContDiff ℝ 1 g₁)
    (hf₂ : ContDiff ℝ 1 f₂) (hg₂ : ContDiff ℝ 1 g₂)
    (hf₁s : HasCompactSupport f₁) (hf₂s : HasCompactSupport f₂) :
    weightedPair (sourceL g₁) f₂ + weightedPair (sourceD f₁) g₂
      = weightedPair g₁ (sourceD f₂) + weightedPair f₁ (sourceL g₂) := by
  rw [weightedPair_L_left hf₂ hg₁ hf₂s, weightedPair_D_left hf₁ hg₂ hf₁s]



/-! ### Strict positivity of the shifted Hermitian square -/

/-- **The shifted pencil has no compactly supported null datum.**  If `(A + α) f = 0` and `f` has
compact support then `f` vanishes identically: the tilted product `f(x) e^{iαx}` has zero
derivative, hence is constant, and the constant is `0` because the line is not compact.  This is
the strictness in `H_α = (A+α)^*(A+α) > 0`. -/
theorem eq_zero_of_shifted_kernel {α : ℂ} {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f)
    (heq : ∀ x, -Complex.I * deriv f x + α * f x = 0) (x : ℝ) : f x = 0 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hfd : ∀ t : ℝ, HasDerivAt f (deriv f t) t := fun t =>
    (hf.differentiable (by simp) t).hasDerivAt
  have hchar : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * α * (s : ℂ)))
      (Complex.I * α * Complex.exp (Complex.I * α * (t : ℂ))) t := by
    intro t
    have hlin : HasDerivAt (fun s : ℝ => Complex.I * α * ((s : ℝ) : ℂ)) (Complex.I * α) t := by
      simpa using (hasDerivAt_id t).ofReal_comp.const_mul (Complex.I * α)
    have h := hlin.cexp
    refine h.congr_deriv ?_
    ring
  have hprod : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => f s * Complex.exp (Complex.I * α * (s : ℂ))) 0 t := by
    intro t
    have h := (hfd t).mul (hchar t)
    refine h.congr_deriv ?_
    have ht := heq t
    linear_combination (Complex.I * Complex.exp (Complex.I * α * (t : ℂ))) * ht
      + (Complex.exp (Complex.I * α * (t : ℂ)) * (deriv f t)) * hI
  have hdiff : Differentiable ℝ (fun s : ℝ => f s * Complex.exp (Complex.I * α * (s : ℂ))) :=
    fun t => (hprod t).differentiableAt
  have hderivzero : ∀ t : ℝ,
      deriv (fun s : ℝ => f s * Complex.exp (Complex.I * α * (s : ℂ))) t = 0 :=
    fun t => (hprod t).deriv
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y ∉ tsupport f := by
    by_contra hcon
    push Not at hcon
    exact (hfs.isCompact).ne_univ (Set.eq_univ_of_forall hcon)
  have hfy : f y = 0 := by
    by_contra hne
    exact hy (subset_tsupport f (by simpa [Function.mem_support] using hne))
  have hconst := is_const_of_deriv_eq_zero hdiff hderivzero x y
  rw [hfy, zero_mul] at hconst
  have hexp : Complex.exp (Complex.I * α * (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  exact (mul_eq_zero.mp hconst).resolve_right hexp


/-! ### The half-density conjugation -/

/-- **The half-density conjugation.**  Multiplying by `k^{1/2}` turns the plain derivative into the
derivative shifted by half the logarithmic derivative of the source; equivalently
`U D U^{-1} = D - (i/2) k'/k` for the unitary `U` of multiplication by `k^{-1/2}`. -/
theorem hasDerivAt_halfDensity_mul {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (fun t => ((Real.sqrt (thetaCuspFullSource t) : ℝ) : ℂ) * f t)
      (((Real.sqrt (thetaCuspFullSource x) : ℝ) : ℂ)
        * (f' x + ((sourceLogDeriv x / 2 : ℝ) : ℂ) * f x)) x := by
  have hkpos : 0 < thetaCuspFullSource x := thetaCuspFullSource_pos x
  have hsqrtpos : 0 < Real.sqrt (thetaCuspFullSource x) := Real.sqrt_pos.mpr hkpos
  have hsq : HasDerivAt (fun t => Real.sqrt (thetaCuspFullSource t))
      (sourceDeriv x / (2 * Real.sqrt (thetaCuspFullSource x))) x := by
    have h := (Real.hasDerivAt_sqrt hkpos.ne').comp x (hasDerivAt_thetaCuspFullSource x)
    refine h.congr_deriv ?_
    field_simp
  have hsqC : HasDerivAt (fun t => ((Real.sqrt (thetaCuspFullSource t) : ℝ) : ℂ))
      (((sourceDeriv x / (2 * Real.sqrt (thetaCuspFullSource x)) : ℝ) : ℂ)) x :=
    hsq.ofReal_comp
  refine (hsqC.mul (hf x)).congr_deriv ?_
  have hgoal : ((sourceDeriv x / (2 * Real.sqrt (thetaCuspFullSource x)) : ℝ) : ℂ)
      = ((Real.sqrt (thetaCuspFullSource x) : ℝ) : ℂ) * ((sourceLogDeriv x / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    set s := Real.sqrt (thetaCuspFullSource x) with hs
    have hsne : s ≠ 0 := hsqrtpos.ne'
    have hss : s * s = thetaCuspFullSource x := Real.mul_self_sqrt hkpos.le
    rw [sourceLogDeriv, ← hss]
    field_simp
  rw [hgoal]
  ring

end HedenmalmThetaSource

end

end RHTower
