import GaloisForLFunctions.RHTower.IsingCavityRapidityAudioCascade
import GaloisForLFunctions.RHTower.SignedReflectionParity
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn

/-!
# Source-balanced centering of prime Ising trees

Global spin inversion does more than localize the zeros of a finite prime Ising tree.  It also
forces a zero-free exponential cocycle whose exponent is the total logarithmic prime mass of the
tree.  Consequently, scalar normalization at the centered point leaves a nonzero first derivative
and can never converge locally uniformly to the even function `XiC`.

Multiplication by the forced half-cocycle removes exactly this defect.  The resulting balanced
partition is entire, even, normalized to one at the origin, and has only real zeros.  Thus only the
source-comparison theorem for the balanced family remains in the Lee--Yang route to RH.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

mutual
  /-- Total logarithmic prime mass of the vertices of a finite prime Ising tree. -/
  def treePrimeLeeYangMass : PrimeIsingTree → ℝ
    | .node p branches =>
        _root_.RHTower.primeLeeYangLog p + forestPrimeLeeYangMass branches

  /-- Total logarithmic prime mass of all trees in a finite prime Ising forest. -/
  def forestPrimeLeeYangMass : PrimeIsingForest → ℝ
    | .nil => 0
    | .cons _ child tail =>
        treePrimeLeeYangMass child + forestPrimeLeeYangMass tail
end

/-- Every prime vertex has logarithmic mass at least `log 2`. -/
theorem log_two_le_primeLeeYangLog (p : Nat.Primes) :
    Real.log 2 ≤ _root_.RHTower.primeLeeYangLog p := by
  unfold _root_.RHTower.primeLeeYangLog
  exact Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)

mutual
  /-- A nonempty tree has mass at least that of its root, hence at least `log 2`. -/
  theorem log_two_le_treePrimeLeeYangMass (T : PrimeIsingTree) :
      Real.log 2 ≤ treePrimeLeeYangMass T := by
    cases T with
    | node p branches =>
        simp only [treePrimeLeeYangMass]
        exact (log_two_le_primeLeeYangLog p).trans
          (le_add_of_nonneg_right (forestPrimeLeeYangMass_nonneg branches))

  /-- Forest prime mass is nonnegative. -/
  theorem forestPrimeLeeYangMass_nonneg (F : PrimeIsingForest) :
      0 ≤ forestPrimeLeeYangMass F := by
    cases F with
    | nil => simp [forestPrimeLeeYangMass]
    | cons _ child tail =>
        simp only [forestPrimeLeeYangMass]
        exact add_nonneg
          ((Real.log_pos (by norm_num)).le.trans
            (log_two_le_treePrimeLeeYangMass child))
          (forestPrimeLeeYangMass_nonneg tail)
end

/-- The centered field is the exponential of its prime logarithmic phase. -/
theorem centeredPrimeLeeYangField_eq_massExp (p : Nat.Primes) (z : ℂ) :
    _root_.RHTower.centeredPrimeLeeYangField p z =
      Complex.exp (-((_root_.RHTower.primeLeeYangLog p : ℝ) : ℂ) * I * z) := by
  unfold _root_.RHTower.centeredPrimeLeeYangField _root_.RHTower.centeredPrimeMark
    _root_.RHTower.primeLeeYangLog
  congr 1
  ring

mutual
  /-- The product of all centered vertex fields is the exponential of total prime mass. -/
  theorem treeFieldProduct_centered_eq_massExp (T : PrimeIsingTree) (z : ℂ) :
      treeFieldProduct (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T =
        Complex.exp (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z) := by
    cases T with
    | node p branches =>
        rw [treeFieldProduct, centeredPrimeLeeYangField_eq_massExp,
          forestFieldProduct_centered_eq_massExp, ← Complex.exp_add]
        simp only [treePrimeLeeYangMass]
        push_cast
        congr 1
        ring

  /-- Forest form of the centered field-product identity. -/
  theorem forestFieldProduct_centered_eq_massExp (F : PrimeIsingForest) (z : ℂ) :
      forestFieldProduct (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) F =
        Complex.exp (-((forestPrimeLeeYangMass F : ℝ) : ℂ) * I * z) := by
    cases F with
    | nil => simp [forestFieldProduct, forestPrimeLeeYangMass]
    | cons c child tail =>
        rw [forestFieldProduct, treeFieldProduct_centered_eq_massExp,
          forestFieldProduct_centered_eq_massExp, ← Complex.exp_add]
        simp only [forestPrimeLeeYangMass]
        push_cast
        congr 1
        ring
end

/-- Spin inversion forces an exact exponential reflection cocycle. -/
theorem primeIsingTreePartition_reflectionCocycle (T : PrimeIsingTree) (z : ℂ) :
    primeIsingTreePartition T z =
      Complex.exp (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z) *
        primeIsingTreePartition T (-z) := by
  have hrecip := treePartition_reciprocal
    (fun p => _root_.RHTower.centeredPrimeLeeYangField p z)
    (fun p => centeredPrimeLeeYangField_ne_zero p z) T
  rw [treeFieldProduct_centered_eq_massExp] at hrecip
  have hinv : treePartition
      (fun p => (_root_.RHTower.centeredPrimeLeeYangField p z)⁻¹) T =
      primeIsingTreePartition T (-z) := by
    rw [primeIsingTreePartition]
    congr 2
    funext p
    exact (centeredPrimeLeeYangField_neg p z).symm
  rw [primeIsingTreePartition, hrecip, hinv]

/-- Scalar normalization preserves the same source-forced reflection cocycle. -/
theorem centralNormalizedPrimeIsingTreePartition_reflectionCocycle
    (T : PrimeIsingTree) (z : ℂ) :
    centralNormalizedPrimeIsingTreePartition T z =
      Complex.exp (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z) *
        centralNormalizedPrimeIsingTreePartition T (-z) := by
  unfold centralNormalizedPrimeIsingTreePartition
  rw [primeIsingTreePartition_reflectionCocycle T z]
  ring

/-- Source-forced half-cocycle normalization.  Unlike scalar central normalization, this removes
the complete spin-inversion drift. -/
def balancedPrimeIsingTreePartition (T : PrimeIsingTree) (z : ℂ) : ℂ :=
  Complex.exp (((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z / 2) *
    centralNormalizedPrimeIsingTreePartition T z

@[simp] theorem balancedPrimeIsingTreePartition_zero (T : PrimeIsingTree) :
    balancedPrimeIsingTreePartition T 0 = 1 := by
  simp [balancedPrimeIsingTreePartition]

/-- The half-cocycle makes the source approximant exactly even. -/
theorem balancedPrimeIsingTreePartition_even (T : PrimeIsingTree) (z : ℂ) :
    balancedPrimeIsingTreePartition T (-z) =
      balancedPrimeIsingTreePartition T z := by
  rw [balancedPrimeIsingTreePartition, balancedPrimeIsingTreePartition]
  have href := centralNormalizedPrimeIsingTreePartition_reflectionCocycle T z
  have hsolve : centralNormalizedPrimeIsingTreePartition T (-z) =
      Complex.exp (((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z) *
        centralNormalizedPrimeIsingTreePartition T z := by
    calc
      centralNormalizedPrimeIsingTreePartition T (-z) =
          (Complex.exp (((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z) *
            Complex.exp (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z)) *
              centralNormalizedPrimeIsingTreePartition T (-z) := by
                rw [← Complex.exp_add]
                simp
      _ = Complex.exp (((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z) *
          (Complex.exp (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z) *
            centralNormalizedPrimeIsingTreePartition T (-z)) := by ring
      _ = _ := by rw [← href]
  rw [hsolve, ← mul_assoc, ← Complex.exp_add]
  congr 1
  ring

/-- The balanced finite partition remains entire. -/
theorem differentiable_balancedPrimeIsingTreePartition (T : PrimeIsingTree) :
    Differentiable ℂ (balancedPrimeIsingTreePartition T) := by
  unfold balancedPrimeIsingTreePartition
  apply Differentiable.mul
  · fun_prop
  · exact differentiable_centralNormalizedPrimeIsingTreePartition T

/-- The half-cocycle is zero-free, so balancing changes no zero. -/
theorem balancedPrimeIsingTreePartition_eq_zero_iff
    (T : PrimeIsingTree) (z : ℂ) :
    balancedPrimeIsingTreePartition T z = 0 ↔
      primeIsingTreePartition T z = 0 := by
  rw [balancedPrimeIsingTreePartition, mul_eq_zero]
  simp [centralNormalizedPrimeIsingTreePartition_eq_zero_iff]

/-- Every zero of a balanced finite source partition is real. -/
theorem balancedPrimeIsingTreePartition_zero_im
    (T : PrimeIsingTree) {z : ℂ}
    (hz : balancedPrimeIsingTreePartition T z = 0) : z.im = 0 := by
  exact primeIsingTreePartition_zero_im T
    ((balancedPrimeIsingTreePartition_eq_zero_iff T z).mp hz)

/-- Scalar central normalization is the balanced partition times the inverse half-cocycle. -/
theorem centralNormalizedPrimeIsingTreePartition_eq_exp_mul_balanced
    (T : PrimeIsingTree) :
    centralNormalizedPrimeIsingTreePartition T = fun z =>
      Complex.exp (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z / 2) *
        balancedPrimeIsingTreePartition T z := by
  funext z
  rw [balancedPrimeIsingTreePartition, ← mul_assoc, ← Complex.exp_add]
  rw [show -((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z / 2 +
      ((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z / 2 = 0 by ring]
  simp

/-- The residual first derivative after scalar normalization is exactly minus one half of the
total prime phase. -/
theorem deriv_centralNormalizedPrimeIsingTreePartition_zero (T : PrimeIsingTree) :
    deriv (centralNormalizedPrimeIsingTreePartition T) 0 =
      -((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2 := by
  have hbalanced : deriv (balancedPrimeIsingTreePartition T) 0 = 0 := by
    simpa only [Function.iterate_one] using!
      (_root_.RHTower.iteratedDeriv_odd_eq_zero_of_symmetric
        (f := balancedPrimeIsingTreePartition T) (c := 0)
        ((differentiable_balancedPrimeIsingTreePartition T).differentiableOn.analyticOnNhd
          isOpen_univ)
        (by
          intro z
          rw [show 2 * (0 : ℂ) - z = -z by ring]
          exact balancedPrimeIsingTreePartition_even T z)
        (by exact odd_one))
  rw [centralNormalizedPrimeIsingTreePartition_eq_exp_mul_balanced]
  have hlin : HasDerivAt
      (fun z : ℂ => -((treePrimeLeeYangMass T : ℝ) : ℂ) * I * z / 2)
      (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I / 2) 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).const_mul
      (-((treePrimeLeeYangMass T : ℝ) : ℂ) * I)).div_const 2 using 1
    all_goals ring
  have hprod := hlin.cexp.mul
    ((differentiable_balancedPrimeIsingTreePartition T 0).hasDerivAt)
  simpa [hbalanced] using! hprod.deriv

/-- The pointed target germ.  Finite balanced partitions equal one at the origin, so the raw
`XiC` germ must be divided by its nonzero central value before a source comparison is attainable. -/
def unitCentralXiC (z : ℂ) : ℂ :=
  (_root_.RHTower.XiC 0)⁻¹ * _root_.RHTower.XiC z

@[simp] theorem unitCentralXiC_zero : unitCentralXiC 0 = 1 := by
  exact inv_mul_cancel₀ _root_.RHTower.XiC_zero_ne

/-- Pointing preserves the functional-equation parity. -/
theorem unitCentralXiC_even (z : ℂ) : unitCentralXiC (-z) = unitCentralXiC z := by
  rw [unitCentralXiC, unitCentralXiC, _root_.RHTower.XiC_even]

/-- The pointed target remains entire. -/
theorem differentiable_unitCentralXiC : Differentiable ℂ unitCentralXiC := by
  exact (differentiable_const _).mul _root_.RHTower.XiC_differentiable

/-- The raw completed Xi germ has zero central derivative by functional-equation parity. -/
theorem deriv_XiC_zero_of_even : deriv _root_.RHTower.XiC 0 = 0 := by
  simpa only [Function.iterate_one] using!
    (_root_.RHTower.iteratedDeriv_odd_eq_zero_of_symmetric
      (f := _root_.RHTower.XiC) (c := 0) _root_.RHTower.XiC_analytic
      (by
        intro z
        rw [show 2 * (0 : ℂ) - z = -z by ring]
        exact _root_.RHTower.XiC_even z)
      (by exact odd_one))

/-- The unit-pointed completed Xi germ also has zero central derivative. -/
theorem deriv_unitCentralXiC_zero : deriv unitCentralXiC 0 = 0 := by
  simpa only [Function.iterate_one] using!
    (_root_.RHTower.iteratedDeriv_odd_eq_zero_of_symmetric
      (f := unitCentralXiC) (c := 0)
      (differentiable_unitCentralXiC.differentiableOn.analyticOnNhd isOpen_univ)
      (by
        intro z
        rw [show 2 * (0 : ℂ) - z = -z by ring]
        exact unitCentralXiC_even z)
      (by exact odd_one))

/-- A target with zero first derivative cannot be a locally uniform limit of scalar-normalized
prime Ising trees.  Their source-forced first jets have masses uniformly bounded below by
`log 2`. -/
theorem not_tendstoLocallyUniformly_centralNormalizedPrimeIsingTreePartition_of_deriv_zero
    (T : ℕ → PrimeIsingTree) (f : ℂ → ℂ) (hf : deriv f 0 = 0) :
    ¬ TendstoLocallyUniformly
      (fun n => centralNormalizedPrimeIsingTreePartition (T n))
      f atTop := by
  intro hconv
  have hderiv := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_univ (tendstoLocallyUniformlyOn_univ.mpr hconv)
    (Filter.Eventually.of_forall (fun n =>
      (differentiable_centralNormalizedPrimeIsingTreePartition (T n)).differentiableOn))
    1 (Set.mem_univ 0)
  simp only [iteratedDeriv_one,
    deriv_centralNormalizedPrimeIsingTreePartition_zero, hf] at hderiv
  have hmassComplex : Tendsto
      (fun n => ((treePrimeLeeYangMass (T n) : ℝ) : ℂ)) atTop (nhds 0) := by
    have hscaled := hderiv.const_mul (2 * I)
    have hpoint (n : ℕ) :
        2 * I * (-((treePrimeLeeYangMass (T n) : ℝ) : ℂ) * I / 2) =
          ((treePrimeLeeYangMass (T n) : ℝ) : ℂ) := by
      calc
        2 * I * (-((treePrimeLeeYangMass (T n) : ℝ) : ℂ) * I / 2) =
            -(I * I) * ((treePrimeLeeYangMass (T n) : ℝ) : ℂ) := by ring
        _ = _ := by rw [I_mul_I]; ring
    simpa using hscaled.congr' (Filter.Eventually.of_forall hpoint)
  have hmassReal : Tendsto (fun n => treePrimeLeeYangMass (T n)) atTop (nhds 0) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hmassComplex
    simpa using! hre
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hevent : ∀ᶠ n in atTop, treePrimeLeeYangMass (T n) < Real.log 2 / 2 :=
    hmassReal.eventually (Iio_mem_nhds (half_pos hlog))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  linarith [log_two_le_treePrimeLeeYangMass (T N), hN N le_rfl]

/-- The previously stated scalar-normalized capstone has an impossible premise. -/
theorem not_tendstoLocallyUniformly_centralNormalizedPrimeIsingTreePartition_XiC
    (T : ℕ → PrimeIsingTree) :
    ¬ TendstoLocallyUniformly
      (fun n => centralNormalizedPrimeIsingTreePartition (T n))
      _root_.RHTower.XiC atTop :=
  not_tendstoLocallyUniformly_centralNormalizedPrimeIsingTreePartition_of_deriv_zero
    T _ deriv_XiC_zero_of_even

/-- **No-go for scalar normalization after correcting the target value.**  Pointing Xi at the
origin removes the value mismatch but not the source-forced first-jet obstruction. -/
theorem not_tendstoLocallyUniformly_centralNormalizedPrimeIsingTreePartition_unitCentralXiC
    (T : ℕ → PrimeIsingTree) :
    ¬ TendstoLocallyUniformly
      (fun n => centralNormalizedPrimeIsingTreePartition (T n))
      unitCentralXiC atTop :=
  not_tendstoLocallyUniformly_centralNormalizedPrimeIsingTreePartition_of_deriv_zero
    T _ deriv_unitCentralXiC_zero

/-- Corrected Lee--Yang capstone.  A locally uniform source comparison for the balanced finite
partitions with the unit-pointed Xi germ proves RH; all analytic and zero-location hypotheses are
unconditional. -/
theorem riemannHypothesis_of_balancedPrimeIsingTreePartition_tendstoLocallyUniformly
    (T : ℕ → PrimeIsingTree)
    (hconv : TendstoLocallyUniformly
      (fun n => balancedPrimeIsingTreePartition (T n))
      unitCentralXiC atTop) :
    RiemannHypothesis := by
  have hconst : TendstoLocallyUniformly
      (fun _ : ℕ => fun _ : ℂ => _root_.RHTower.XiC 0)
      (fun _ : ℂ => _root_.RHTower.XiC 0) atTop := by
    intro u hu x
    exact ⟨Set.univ, univ_mem,
      Filter.Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hu)⟩
  have hscaled : TendstoLocallyUniformly
      (fun n z => _root_.RHTower.XiC 0 * balancedPrimeIsingTreePartition (T n) z)
      _root_.RHTower.XiC atTop := by
    have hmul := hconst.mul₀ hconv continuous_const differentiable_unitCentralXiC.continuous
    change TendstoLocallyUniformly
      (fun n z => _root_.RHTower.XiC 0 * balancedPrimeIsingTreePartition (T n) z)
      (fun z => _root_.RHTower.XiC 0 * unitCentralXiC z) atTop at hmul
    convert hmul using 1
    funext z
    rw [unitCentralXiC, ← mul_assoc,
      mul_inv_cancel₀ _root_.RHTower.XiC_zero_ne, one_mul]
  apply _root_.RHTower.riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hscaled
  · exact Filter.Eventually.of_forall
      (fun n => (differentiable_const _).mul
        (differentiable_balancedPrimeIsingTreePartition (T n)))
  · exact Filter.Eventually.of_forall
      (fun n z hz => balancedPrimeIsingTreePartition_zero_im (T n)
        ((mul_eq_zero.mp hz).resolve_left _root_.RHTower.XiC_zero_ne))

end

end GaloisForLFunctions.RHTower
