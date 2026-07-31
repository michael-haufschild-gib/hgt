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

/-- The modulus of that logarithmic derivative is half the prime mass, hence at least
`log 2 / 2`. -/
theorem logTwo_div_two_le_norm_logDeriv_primeIsingTreePartition (T : PrimeIsingTree) :
    Real.log 2 / 2 ≤
      ‖deriv (primeIsingTreePartition T) 0 / primeIsingTreePartition T 0‖ := by
  have hmass : Real.log 2 ≤ treePrimeLeeYangMass T := log_two_le_treePrimeLeeYangMass T
  have hnonneg : 0 ≤ treePrimeLeeYangMass T :=
    le_trans (Real.log_nonneg (by norm_num)) hmass
  rw [logDeriv_primeIsingTreePartition_zero]
  have hnorm : ‖-((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2‖ =
      treePrimeLeeYangMass T / 2 := by
    simp [abs_of_nonneg hnonneg]
  rw [hnorm]
  linarith

/-- **Central mass-floor law.**  Every locally uniform limit of finite prime-labelled
ferromagnetic Ising tree partitions which does not vanish at the origin has central logarithmic
derivative of modulus at least `log 2 / 2`. -/
theorem logTwo_div_two_le_norm_logDeriv_of_tendstoLocallyUniformly_primeIsingTreePartition
    (T : ℕ → PrimeIsingTree) {f : ℂ → ℂ} (hf0 : f 0 ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) f atTop) :
    Real.log 2 / 2 ≤ ‖deriv f 0 / f 0‖ := by
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
  refine ge_of_tendsto hquot.norm ?_
  filter_upwards [] with n
  exact logTwo_div_two_le_norm_logDeriv_primeIsingTreePartition (T n)

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

/-- **The normalization must carry the whole floor.**  If a factor with vanishing central
derivative is split off the limit, the remaining factor alone supports the mass floor. -/
theorem logTwo_div_two_le_norm_logDeriv_factor_of_tendstoLocallyUniformly
    (T : ℕ → PrimeIsingTree) (E g : ℂ → ℂ)
    (hE : DifferentiableAt ℂ E 0) (hg : DifferentiableAt ℂ g 0)
    (hE0 : E 0 ≠ 0) (hg0 : g 0 ≠ 0) (hgd : deriv g 0 = 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) (fun z => E z * g z) atTop) :
    Real.log 2 / 2 ≤ ‖deriv E 0 / E 0‖ := by
  have hf0 : (fun z => E z * g z) 0 ≠ 0 := mul_ne_zero hE0 hg0
  have h :=
    logTwo_div_two_le_norm_logDeriv_of_tendstoLocallyUniformly_primeIsingTreePartition
      T hf0 hconv
  have hderiv : deriv (fun z => E z * g z) 0 = deriv E 0 * g 0 := by
    have hd := (hE.hasDerivAt.mul hg.hasDerivAt).deriv
    rw [hgd, mul_zero, add_zero] at hd
    exact hd
  rw [hderiv] at h
  have hsimp : deriv E 0 * g 0 / (E 0 * g 0) = deriv E 0 / E 0 := by
    field_simp
  rwa [hsimp] at h

/-- The zero-free normalization of the factored tree route must have central logarithmic
derivative of modulus at least `log 2 / 2`: the completed Xi factor contributes nothing. -/
theorem logTwo_div_two_le_norm_logDeriv_normalization_mul_XiC
    (T : ℕ → PrimeIsingTree) (E : ℂ → ℂ)
    (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n))
      (fun z => E z * _root_.RHTower.XiC z) atTop) :
    Real.log 2 / 2 ≤ ‖deriv E 0 / E 0‖ :=
  logTwo_div_two_le_norm_logDeriv_factor_of_tendstoLocallyUniformly T E _root_.RHTower.XiC
    (hE 0) (_root_.RHTower.XiC_differentiable 0) (hEne 0) _root_.RHTower.XiC_zero_ne
    deriv_XiC_zero_of_even hconv

end

end GaloisForLFunctions.RHTower
