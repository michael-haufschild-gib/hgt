import GaloisForLFunctions.RHTower.PrimeIsingTreeBalancedCentering

/-!
# The central mass floor of prime Ising tree partitions

Global spin inversion forces the central logarithmic derivative of every finite prime-labelled
ferromagnetic Ising tree partition to be minus half the total prime mass, and that mass is at
least `log 2` for every tree.  The bound survives passage to a locally uniform limit: any limit
which is nonzero at the origin has central logarithmic derivative of modulus at least
`log 2 / 2`.

This one inequality is the whole obstruction of the tree route.  Applied to a limit whose central
derivative vanishes it excludes that limit outright, which covers the raw completed Xi germ, its
unit-pointed version, and the scalar-normalized families.  Applied to a factored limit `E * XiC`
with `E` zero free, it shows that `E` alone must carry the entire mass floor, since the Xi factor
contributes nothing to the central logarithmic derivative.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The unnormalized finite tree partition has central logarithmic derivative exactly minus half
the total prime mass of the tree. -/
theorem deriv_primeIsingTreePartition_zero (T : PrimeIsingTree) :
    deriv (primeIsingTreePartition T) 0 =
      primeIsingTreePartition T 0 * (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2) := by
  have hN : HasDerivAt (centralNormalizedPrimeIsingTreePartition T)
      (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2) 0 := by
    rw [← deriv_centralNormalizedPrimeIsingTreePartition_zero]
    exact (differentiable_centralNormalizedPrimeIsingTreePartition T 0).hasDerivAt
  have hZ := hN.const_mul (primeIsingTreePartition T 0)
  have hfun : (fun z => primeIsingTreePartition T 0 *
      centralNormalizedPrimeIsingTreePartition T z) = primeIsingTreePartition T := by
    funext z
    rw [centralNormalizedPrimeIsingTreePartition, ← mul_assoc,
      mul_inv_cancel₀ (primeIsingTreePartition_zero_ne_zero T), one_mul]
  rw [hfun] at hZ
  exact hZ.deriv

/-- The central logarithmic derivative of a finite tree partition is exactly minus half its
prime mass. -/
theorem logDeriv_primeIsingTreePartition_zero (T : PrimeIsingTree) :
    deriv (primeIsingTreePartition T) 0 / primeIsingTreePartition T 0 =
      -((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2 := by
  rw [deriv_primeIsingTreePartition_zero]
  exact mul_div_cancel_left₀ _ (primeIsingTreePartition_zero_ne_zero T)

/-- **Finite-tree orientation law.**  The central logarithmic derivative is purely imaginary and
points down the imaginary axis by at least `log 2 / 2`. -/
theorem logDeriv_primeIsingTreePartition_orientation (T : PrimeIsingTree) :
    (deriv (primeIsingTreePartition T) 0 / primeIsingTreePartition T 0).re = 0 ∧
      (deriv (primeIsingTreePartition T) 0 / primeIsingTreePartition T 0).im ≤
        -(Real.log 2 / 2) := by
  rw [logDeriv_primeIsingTreePartition_zero]
  have hmass : Real.log 2 ≤ treePrimeLeeYangMass T := log_two_le_treePrimeLeeYangMass T
  constructor
  · simp
  · simp
    linarith

/-- A complex number below the oriented mass floor has norm at least `log 2 / 2`. -/
theorem logTwo_div_two_le_norm_of_im_le_neg_logTwo_div_two {z : ℂ}
    (him : z.im ≤ -(Real.log 2 / 2)) : Real.log 2 / 2 ≤ ‖z‖ := by
  have ha : 0 ≤ Real.log 2 / 2 := by positivity
  have him_nonpos : z.im ≤ 0 := le_trans him (neg_nonpos.mpr ha)
  have ha_abs : Real.log 2 / 2 ≤ |z.im| := by
    rw [abs_of_nonpos him_nonpos]
    linarith
  exact ha_abs.trans (Complex.abs_im_le_norm z)

/-- The modulus of that logarithmic derivative is half the prime mass, hence at least
`log 2 / 2`. -/
theorem logTwo_div_two_le_norm_logDeriv_primeIsingTreePartition (T : PrimeIsingTree) :
    Real.log 2 / 2 ≤
      ‖deriv (primeIsingTreePartition T) 0 / primeIsingTreePartition T 0‖ := by
  exact logTwo_div_two_le_norm_of_im_le_neg_logTwo_div_two
    (logDeriv_primeIsingTreePartition_orientation T).2

/-- **Oriented central mass-floor law.**  Local uniform limits preserve not only the size of the
finite-tree central logarithmic derivative but its phase: the limit derivative remains purely
imaginary and on the negative ray below `-log 2 / 2`. -/
theorem logDeriv_orientation_of_tendstoLocallyUniformly_primeIsingTreePartition
    (T : ℕ → PrimeIsingTree) {f : ℂ → ℂ} (hf0 : f 0 ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) f atTop) :
    (deriv f 0 / f 0).re = 0 ∧
      (deriv f 0 / f 0).im ≤ -(Real.log 2 / 2) := by
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (primeIsingTreePartition (T n)) Set.univ :=
    Filter.Eventually.of_forall fun n =>
      (differentiable_primeIsingTreePartition (T n)).differentiableOn
  have hUniv := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hval : Tendsto (fun n => primeIsingTreePartition (T n) 0) atTop (nhds (f 0)) := by
    simpa only [iteratedDeriv_zero] using
      GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ hUniv hdiff 0
        (Set.mem_univ 0)
  have hder : Tendsto (fun n => deriv (primeIsingTreePartition (T n)) 0) atTop
      (nhds (deriv f 0)) := by
    simpa only [iteratedDeriv_one] using
      GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform isOpen_univ hUniv hdiff 1
        (Set.mem_univ 0)
  have hquot : Tendsto (fun n => deriv (primeIsingTreePartition (T n)) 0 /
      primeIsingTreePartition (T n) 0) atTop (nhds (deriv f 0 / f 0)) :=
    hder.div hval hf0
  have hre : Tendsto (fun n => (deriv (primeIsingTreePartition (T n)) 0 /
      primeIsingTreePartition (T n) 0).re) atTop
      (nhds (deriv f 0 / f 0).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hquot
  have him : Tendsto (fun n => (deriv (primeIsingTreePartition (T n)) 0 /
      primeIsingTreePartition (T n) 0).im) atTop
      (nhds (deriv f 0 / f 0).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hquot
  constructor
  · apply tendsto_nhds_unique hre
    have hconst : (fun n : ℕ =>
        (deriv (primeIsingTreePartition (T n)) 0 /
          primeIsingTreePartition (T n) 0).re) = fun _ => 0 := by
      funext n
      exact (logDeriv_primeIsingTreePartition_orientation (T n)).1
    rw [hconst]
    exact tendsto_const_nhds
  · refine le_of_tendsto him ?_
    filter_upwards [] with n
    exact (logDeriv_primeIsingTreePartition_orientation (T n)).2

/-- **Central mass-floor law.**  Every locally uniform limit of finite prime-labelled
ferromagnetic Ising tree partitions which does not vanish at the origin has central logarithmic
derivative of modulus at least `log 2 / 2`. -/
theorem logTwo_div_two_le_norm_logDeriv_of_tendstoLocallyUniformly_primeIsingTreePartition
    (T : ℕ → PrimeIsingTree) {f : ℂ → ℂ} (hf0 : f 0 ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) f atTop) :
    Real.log 2 / 2 ≤ ‖deriv f 0 / f 0‖ := by
  exact logTwo_div_two_le_norm_of_im_le_neg_logTwo_div_two
    (logDeriv_orientation_of_tendstoLocallyUniformly_primeIsingTreePartition T hf0 hconv).2

/-- A target with vanishing central derivative is unreachable by finite tree partitions. -/
theorem not_tendstoLocallyUniformly_primeIsingTreePartition_of_deriv_zero
    (T : ℕ → PrimeIsingTree) {f : ℂ → ℂ} (hf0 : f 0 ≠ 0) (hf : deriv f 0 = 0) :
    ¬ TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) f atTop := by
  intro hconv
  have h :=
    logTwo_div_two_le_norm_logDeriv_of_tendstoLocallyUniformly_primeIsingTreePartition
      T hf0 hconv
  rw [hf, zero_div, norm_zero] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The unnormalized tree route to the raw completed Xi germ has an impossible premise. -/
theorem not_tendstoLocallyUniformly_primeIsingTreePartition_XiC
    (T : ℕ → PrimeIsingTree) :
    ¬ TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) _root_.RHTower.XiC atTop :=
  not_tendstoLocallyUniformly_primeIsingTreePartition_of_deriv_zero T
    _root_.RHTower.XiC_zero_ne deriv_XiC_zero_of_even

/-- The same for the unit-pointed target. -/
theorem not_tendstoLocallyUniformly_primeIsingTreePartition_unitCentralXiC
    (T : ℕ → PrimeIsingTree) :
    ¬ TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) unitCentralXiC atTop :=
  not_tendstoLocallyUniformly_primeIsingTreePartition_of_deriv_zero T
    (by simp) deriv_unitCentralXiC_zero

/-- Every even complex function has zero derivative at the symmetry centre.  No differentiability
hypothesis is needed because `deriv` is zero when differentiability fails. -/
theorem deriv_zero_of_even_complex {f : ℂ → ℂ} (hf : Function.Even f) : deriv f 0 = 0 := by
  have hfun : (fun w : ℂ => f (-w)) = f := funext hf
  have h := deriv_comp_neg (f := f) (x := 0)
  rw [hfun, neg_zero] at h
  have htwo : (2 : ℂ) * deriv f 0 = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- A conjugation-equivariant complex function takes a real value at the symmetry centre. -/
theorem value_zero_im_of_conj_equivariant {f : ℂ → ℂ}
    (hf : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    (f 0).im = 0 := by
  have hfix : f 0 = (starRingEnd ℂ) (f 0) := by
    simpa using hf 0
  have him := congrArg Complex.im hfix
  rw [Complex.conj_im] at him
  linarith

/-- The central derivative of a conjugation-equivariant complex function is real.  This remains
valid without a differentiability hypothesis because `deriv` vanishes at nondifferentiable
points. -/
theorem deriv_zero_im_of_conj_equivariant {f : ℂ → ℂ}
    (hf : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    (deriv f 0).im = 0 := by
  have hfun : (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) = f := by
    funext z
    simp only [Function.comp_apply]
    rw [hf]
    simp
  have hder : deriv f =
      (starRingEnd ℂ) ∘ deriv f ∘ (starRingEnd ℂ) := by
    calc
      deriv f = deriv ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) :=
        congrArg deriv hfun.symm
      _ = (starRingEnd ℂ) ∘ deriv f ∘ (starRingEnd ℂ) := deriv_conj_conj
  have hfix : deriv f 0 = (starRingEnd ℂ) (deriv f 0) := by
    simpa [Function.comp_apply] using congrFun hder 0
  have him := congrArg Complex.im hfix
  rw [Complex.conj_im] at him
  linarith

/-- **Even-normalization no-go.**  A nonzero even factor cannot normalize finite prime Ising tree
partitions to `E · XiC`: both factors are even, so the target has zero central derivative, contrary
to the oriented mass floor. -/
theorem not_tendstoLocallyUniformly_primeIsingTreePartition_mul_XiC_of_even
    (T : ℕ → PrimeIsingTree) (E : ℂ → ℂ)
    (hEeven : Function.Even E) (hE0 : E 0 ≠ 0) :
    ¬ TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n))
      (fun z => E z * _root_.RHTower.XiC z) atTop := by
  apply not_tendstoLocallyUniformly_primeIsingTreePartition_of_deriv_zero T
  · exact mul_ne_zero hE0 _root_.RHTower.XiC_zero_ne
  · apply deriv_zero_of_even_complex
    intro z
    change E (-z) * _root_.RHTower.XiC (-z) = E z * _root_.RHTower.XiC z
    rw [hEeven z, _root_.RHTower.XiC_even]

/-- **Factor orientation law.**  When a factor with zero central derivative is split off a tree
limit, the remaining factor inherits the full negative-imaginary orientation and mass floor. -/
theorem logDeriv_factor_orientation_of_tendstoLocallyUniformly
    (T : ℕ → PrimeIsingTree) (E g : ℂ → ℂ)
    (hE : DifferentiableAt ℂ E 0) (hg : DifferentiableAt ℂ g 0)
    (hE0 : E 0 ≠ 0) (hg0 : g 0 ≠ 0) (hgd : deriv g 0 = 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) (fun z => E z * g z) atTop) :
    (deriv E 0 / E 0).re = 0 ∧
      (deriv E 0 / E 0).im ≤ -(Real.log 2 / 2) := by
  have hf0 : (fun z => E z * g z) 0 ≠ 0 := mul_ne_zero hE0 hg0
  have hor :=
    logDeriv_orientation_of_tendstoLocallyUniformly_primeIsingTreePartition T hf0 hconv
  have hderiv : deriv (fun z => E z * g z) 0 = deriv E 0 * g 0 := by
    have hd := (hE.hasDerivAt.mul hg.hasDerivAt).deriv
    rw [hgd, mul_zero, add_zero] at hd
    exact hd
  rw [hderiv] at hor
  have hsimp : deriv E 0 * g 0 / (E 0 * g 0) = deriv E 0 / E 0 := by
    field_simp
  rwa [hsimp] at hor

/-- A normalization whose central logarithmic derivative is real cannot absorb the oriented
prime-mass floor.  Only differentiability and nonvanishing at the centre are needed. -/
theorem not_tendstoLocallyUniformly_primeIsingTreePartition_mul_XiC_of_real_logDeriv
    (T : ℕ → PrimeIsingTree) (E : ℂ → ℂ)
    (hE : DifferentiableAt ℂ E 0) (hE0 : E 0 ≠ 0)
    (hreal : (deriv E 0 / E 0).im = 0) :
    ¬ TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n))
      (fun z => E z * _root_.RHTower.XiC z) atTop := by
  intro hconv
  have hor := logDeriv_factor_orientation_of_tendstoLocallyUniformly
    T E _root_.RHTower.XiC hE (_root_.RHTower.XiC_differentiable 0)
      hE0 _root_.RHTower.XiC_zero_ne deriv_XiC_zero_of_even hconv
  rw [hreal] at hor
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith [hor.2]

/-- **Schwarz-real normalization no-go.**  No conjugation-equivariant factor nonzero and
differentiable at the centre can normalize finite prime Ising tree partitions to `E * XiC`.
Schwarz reality makes the factor's central logarithmic derivative real, while every such tree
limit forces it strictly down the imaginary axis. -/
theorem not_tendstoLocallyUniformly_primeIsingTreePartition_mul_XiC_of_schwarz_real
    (T : ℕ → PrimeIsingTree) (E : ℂ → ℂ)
    (hE : DifferentiableAt ℂ E 0) (hE0 : E 0 ≠ 0)
    (hEconj : ∀ z, E ((starRingEnd ℂ) z) = (starRingEnd ℂ) (E z)) :
    ¬ TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n))
      (fun z => E z * _root_.RHTower.XiC z) atTop := by
  apply not_tendstoLocallyUniformly_primeIsingTreePartition_mul_XiC_of_real_logDeriv
    T E hE hE0
  simp [Complex.div_im, deriv_zero_im_of_conj_equivariant hEconj,
    value_zero_im_of_conj_equivariant hEconj]

/-- **The normalization must carry the whole floor.**  If a factor with vanishing central
derivative is split off the limit, the remaining factor alone supports the mass floor. -/
theorem logTwo_div_two_le_norm_logDeriv_factor_of_tendstoLocallyUniformly
    (T : ℕ → PrimeIsingTree) (E g : ℂ → ℂ)
    (hE : DifferentiableAt ℂ E 0) (hg : DifferentiableAt ℂ g 0)
    (hE0 : E 0 ≠ 0) (hg0 : g 0 ≠ 0) (hgd : deriv g 0 = 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) (fun z => E z * g z) atTop) :
    Real.log 2 / 2 ≤ ‖deriv E 0 / E 0‖ := by
  exact logTwo_div_two_le_norm_of_im_le_neg_logTwo_div_two
    (logDeriv_factor_orientation_of_tendstoLocallyUniformly
      T E g hE hg hE0 hg0 hgd hconv).2

/-- A zero-free normalization of a factored Xi limit must have purely negative-imaginary central
logarithmic derivative, not merely one of sufficiently large modulus. -/
theorem logDeriv_normalization_mul_XiC_orientation
    (T : ℕ → PrimeIsingTree) (E : ℂ → ℂ)
    (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n))
      (fun z => E z * _root_.RHTower.XiC z) atTop) :
    (deriv E 0 / E 0).re = 0 ∧
      (deriv E 0 / E 0).im ≤ -(Real.log 2 / 2) :=
  logDeriv_factor_orientation_of_tendstoLocallyUniformly T E _root_.RHTower.XiC
    (hE 0) (_root_.RHTower.XiC_differentiable 0) (hEne 0) _root_.RHTower.XiC_zero_ne
    deriv_XiC_zero_of_even hconv

/-- The zero-free normalization of the factored tree route must have central logarithmic
derivative of modulus at least `log 2 / 2`: the completed Xi factor contributes nothing. -/
theorem logTwo_div_two_le_norm_logDeriv_normalization_mul_XiC
    (T : ℕ → PrimeIsingTree) (E : ℂ → ℂ)
    (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n))
      (fun z => E z * _root_.RHTower.XiC z) atTop) :
    Real.log 2 / 2 ≤ ‖deriv E 0 / E 0‖ :=
  logTwo_div_two_le_norm_of_im_le_neg_logTwo_div_two
    (logDeriv_normalization_mul_XiC_orientation T E hE hEne hconv).2

end

end GaloisForLFunctions.RHTower
