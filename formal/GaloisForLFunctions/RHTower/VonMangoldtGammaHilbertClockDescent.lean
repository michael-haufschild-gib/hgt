import GaloisForLFunctions.RHTower.VonMangoldtGammaInfinitePointedWard
import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthHilbertSource
import GaloisForLFunctions.RHTower.PrimeLaplaceGammaJetIncidence
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.BalancedHilbertDefectPolarization
import GaloisForLFunctions.HTGeometry.SeparableBuresAlbertiApproximationLaw
import GaloisForLFunctions.HTGeometry.AllJetLevelSet
import GaloisForLFunctions.HTGeometry.ExponentialSeriesUniqueness
import GaloisForLFunctions.HTGeometry.StrictContractionRecurrenceNoGo
import GaloisForLFunctions.RHTower.VonMangoldtGammaBoundaryDisplacementThreshold
import GaloisForLFunctions.RHTower.EulerTranslationAnalyticFaithful
import GaloisForLFunctions.RHTower.VonMangoldtGammaAllDepthCauchy

open Complex Filter Topology
open scoped BigOperators ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

abbrev VonMangoldtGammaSource :=
  lp (fun _ : Nat.Primes × ℕ => ℂ) 2

def vonMangoldtGammaDensity (x : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  eulerPrimePowerWeight (1 + 2 * x) pe * eulerPrimePowerEnergy pe

theorem vonMangoldtGammaDensity_eq
    (x : ℝ) (pe : Nat.Primes × ℕ) :
    vonMangoldtGammaDensity x pe =
      Real.log (pe.1 : ℝ) / (eulerPrimePowerNat pe : ℝ) *
        Real.exp (-2 * x * eulerPrimePowerEnergy pe) := by
  have hn : (0 : ℝ) < eulerPrimePowerNat pe := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  have hd : (0 : ℝ) < pe.2 + 1 := by positivity
  rw [vonMangoldtGammaDensity, eulerPrimePowerWeight,
    eulerPrimePowerEnergy, Real.rpow_def_of_pos hn]
  have hlog : Real.log (eulerPrimePowerNat pe : ℝ) =
      (pe.2 + 1 : ℝ) * Real.log (pe.1 : ℝ) := by
    rw [eulerPrimePowerNat, Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlog]
  have hexp :
      Real.exp (((pe.2 + 1 : ℝ) * Real.log (pe.1 : ℝ)) * -(1 + 2 * x)) =
        (eulerPrimePowerNat pe : ℝ)⁻¹ *
          Real.exp (-2 * x * ((pe.2 + 1 : ℝ) * Real.log (pe.1 : ℝ))) := by
    rw [show (eulerPrimePowerNat pe : ℝ)⁻¹ =
        Real.exp (-Real.log (eulerPrimePowerNat pe : ℝ)) by
      rw [Real.exp_neg, Real.exp_log hn]]
    rw [hlog, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp [ne_of_gt hn, ne_of_gt hd]

theorem vonMangoldtGammaDensity_nonneg
    (x : ℝ) (pe : Nat.Primes × ℕ) :
    0 ≤ vonMangoldtGammaDensity x pe := by
  rw [vonMangoldtGammaDensity_eq]
  positivity

def vonMangoldtGammaJetAmplitude
    (x : ℝ) (j : ℕ) (pe : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt (vonMangoldtGammaDensity x pe) *
    (-eulerPrimePowerEnergy pe) ^ j

theorem vonMangoldtGammaJetAmplitude_sq
    (x : ℝ) (j : ℕ) (pe : Nat.Primes × ℕ) :
    vonMangoldtGammaJetAmplitude x j pe ^ 2 =
      eulerPrimePowerWeight (1 + 2 * x) pe *
        eulerPrimePowerEnergy pe ^ (2 * j + 1) := by
  rw [vonMangoldtGammaJetAmplitude, mul_pow,
    Real.sq_sqrt (vonMangoldtGammaDensity_nonneg x pe),
    vonMangoldtGammaDensity]
  have hpow : eulerPrimePowerEnergy pe ^ (2 * j + 1) =
      eulerPrimePowerEnergy pe * (eulerPrimePowerEnergy pe ^ j) ^ 2 := by
    rw [show 2 * j + 1 = j + j + 1 by omega, pow_succ, pow_add]
    ring
  have hneg : ((-eulerPrimePowerEnergy pe) ^ j) ^ 2 =
      (eulerPrimePowerEnergy pe ^ j) ^ 2 := by
    rw [neg_pow]
    rw [mul_pow]
    have hsign : (((-1 : ℝ) ^ j) ^ 2) = 1 := by
      rw [← pow_mul]
      simp
    rw [hsign, one_mul]
  rw [hpow]
  change eulerPrimePowerWeight (1 + 2 * x) pe * eulerPrimePowerEnergy pe *
      ((-eulerPrimePowerEnergy pe) ^ j) ^ 2 =
    eulerPrimePowerWeight (1 + 2 * x) pe *
      (eulerPrimePowerEnergy pe * (eulerPrimePowerEnergy pe ^ j) ^ 2)
  rw [hneg]
  ring

theorem summable_sq_vonMangoldtGammaJetAmplitude
    {x : ℝ} (hx : 0 < x) (j : ℕ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      vonMangoldtGammaJetAmplitude x j pe ^ 2) := by
  have hs := summable_abs_eulerPrimePower_moment
    (2 * j + 1) (1 + 2 * x) (by linarith)
  refine hs.congr (fun pe => ?_)
  rw [vonMangoldtGammaJetAmplitude_sq]
  symm
  rw [abs_of_nonneg]
  apply mul_nonneg
  · unfold eulerPrimePowerWeight
    positivity
  · exact pow_nonneg (Real.log_natCast_nonneg _) _

def vonMangoldtGammaJetVector
    (x : ℝ) (hx : 0 < x) (j : ℕ) : VonMangoldtGammaSource :=
  ⟨fun pe => (vonMangoldtGammaJetAmplitude x j pe : ℂ),
    HilbertSchmidt.memℓp_of_sq <| by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using
        summable_sq_vonMangoldtGammaJetAmplitude hx j⟩

@[simp] theorem vonMangoldtGammaJetVector_apply
    (x : ℝ) (hx : 0 < x) (j : ℕ) (pe : Nat.Primes × ℕ) :
    vonMangoldtGammaJetVector x hx j pe =
      (vonMangoldtGammaJetAmplitude x j pe : ℂ) := rfl

def vonMangoldtGammaJetReader
    (x : ℝ) (hx : 0 < x) (j : ℕ) :
    VonMangoldtGammaSource →L[ℂ] ℂ :=
  innerSL ℂ (vonMangoldtGammaJetVector x hx j)

def vonMangoldtGammaObservation
    (x : ℝ) (hx : 0 < x) (N : ℕ) :
    VonMangoldtGammaSource →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin N => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => vonMangoldtGammaJetReader x hx i)

@[simp] theorem vonMangoldtGammaObservation_apply
    (x : ℝ) (hx : 0 < x) (N : ℕ)
    (a : VonMangoldtGammaSource) (i : Fin N) :
    vonMangoldtGammaObservation x hx N a i =
      vonMangoldtGammaJetReader x hx i a := by
  rfl

theorem finiteCodomain_isHilbertSchmidt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] [FiniteDimensional ℂ F]
    (T : E →L[ℂ] F) : T.IsHilbertSchmidt := by
  have h := (finiteDomain_isHilbertSchmidt
    (ContinuousLinearMap.adjoint T)).adjoint
  simpa using h

theorem vonMangoldtGammaObservation_isHilbertSchmidt
    (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt (𝕜 := ℂ)
      (vonMangoldtGammaObservation x hx N) :=
  finiteCodomain_isHilbertSchmidt
    (E := VonMangoldtGammaSource) (F := EuclideanSpace ℂ (Fin N)) _

def vonMangoldtGammaSourceShift :
    VonMangoldtGammaSource →L[ℂ] VonMangoldtGammaSource :=
  lpDiagonalCLM
    (fun pe : Nat.Primes × ℕ => ((eulerPrimePowerNat pe : ℕ) : ℂ)⁻¹)
    (by positivity : (0 : ℝ) ≤ 1 / 2)
    (fun pe => by
      rw [norm_inv, Complex.norm_natCast]
      have hn : (2 : ℝ) ≤ eulerPrimePowerNat pe := by
        exact_mod_cast (show 2 ≤ eulerPrimePowerNat pe by
          unfold eulerPrimePowerNat
          exact pe.1.property.two_le.trans (Nat.le_pow (by omega : 0 < pe.2 + 1)))
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hn))

@[simp] theorem vonMangoldtGammaSourceShift_apply
    (a : VonMangoldtGammaSource) (pe : Nat.Primes × ℕ) :
    vonMangoldtGammaSourceShift a pe =
      ((eulerPrimePowerNat pe : ℕ) : ℂ)⁻¹ * a pe := rfl

theorem norm_vonMangoldtGammaSourceShift_le :
    ‖vonMangoldtGammaSourceShift‖ ≤ 1 / 2 :=
  norm_lpDiagonalCLM_le _ (by positivity) _

/-- **The radial source shift is not the recurrent prime clock.**  A cofinal return of the
iterated von-Mangoldt/Gamma shift to its initial source vector forces that vector to vanish.  Thus
radial completion and vertical phase recurrence cannot be identified on this fixed Hilbert
carrier; any common completion law must compare distinct clock directions or varying positive
topologies. -/
theorem vonMangoldtGammaSource_eq_zero_of_sourceShift_cofinal_return
    (a : VonMangoldtGammaSource) {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (hreturn : Tendsto
      (fun j => (fun x => vonMangoldtGammaSourceShift x)^[phi j] a)
      atTop (𝓝 a)) :
    a = 0 := by
  apply eq_zero_of_strictContraction_of_cofinal_iterate_return
    (fun x => vonMangoldtGammaSourceShift x) a (1 / 2 : ℝ)
    (by norm_num) (by norm_num) _ hphi hreturn
  intro x
  exact (vonMangoldtGammaSourceShift.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right norm_vonMangoldtGammaSourceShift_le (norm_nonneg x))

theorem sqrt_vonMangoldtGammaDensity_eq
    (x : ℝ) (pe : Nat.Primes × ℕ) :
    Real.sqrt (vonMangoldtGammaDensity x pe) =
      Real.sqrt (vonMangoldtGammaDensity 0 pe) *
        Real.exp (-x * eulerPrimePowerEnergy pe) := by
  rw [vonMangoldtGammaDensity_eq, vonMangoldtGammaDensity_eq]
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
  let q : ℝ := Real.log (pe.1 : ℝ) / (eulerPrimePowerNat pe : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hexp : Real.exp (-2 * x * eulerPrimePowerEnergy pe) =
      Real.exp (-x * eulerPrimePowerEnergy pe) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  change Real.sqrt (q * Real.exp (-2 * x * eulerPrimePowerEnergy pe)) =
    Real.sqrt q * Real.exp (-x * eulerPrimePowerEnergy pe)
  rw [hexp, Real.sqrt_mul hq,
    Real.sqrt_sq (Real.exp_pos _).le]

theorem vonMangoldtGammaJetAmplitude_eq
    (x : ℝ) (j : ℕ) (pe : Nat.Primes × ℕ) :
    vonMangoldtGammaJetAmplitude x j pe =
      Real.sqrt (vonMangoldtGammaDensity 0 pe) *
        (-eulerPrimePowerEnergy pe) ^ j *
          Real.exp (-x * eulerPrimePowerEnergy pe) := by
  rw [vonMangoldtGammaJetAmplitude,
    sqrt_vonMangoldtGammaDensity_eq]
  ring

def vonMangoldtGammaSourceTerm
    (a : VonMangoldtGammaSource) (j : ℕ) (s : ℂ)
    (pe : Nat.Primes × ℕ) : ℂ :=
  a pe * (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
    (-eulerPrimePowerEnergy pe : ℂ) ^ j *
      Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * s)

def vonMangoldtGammaSourceJet
    (a : VonMangoldtGammaSource) (j : ℕ) (s : ℂ) : ℂ :=
  ∑' pe : Nat.Primes × ℕ, vonMangoldtGammaSourceTerm a j s pe

theorem norm_vonMangoldtGammaSourceTerm
    (a : VonMangoldtGammaSource) (j : ℕ) (s : ℂ)
    (pe : Nat.Primes × ℕ) :
    ‖vonMangoldtGammaSourceTerm a j s pe‖ =
      ‖a pe‖ * |vonMangoldtGammaJetAmplitude s.re j pe| := by
  simp only [vonMangoldtGammaSourceTerm, norm_mul, norm_pow,
    Complex.norm_real, Complex.norm_exp,
    vonMangoldtGammaJetAmplitude_eq]
  have hre : (-(eulerPrimePowerEnergy pe : ℂ) * s).re =
      -eulerPrimePowerEnergy pe * s.re := by simp
  rw [hre]
  have hsqrt : 0 ≤ Real.sqrt (vonMangoldtGammaDensity 0 pe) := Real.sqrt_nonneg _
  have henergy : 0 ≤ eulerPrimePowerEnergy pe := by
    exact Real.log_natCast_nonneg _
  have hnormsqrt : ‖Real.sqrt (vonMangoldtGammaDensity 0 pe)‖ =
      Real.sqrt (vonMangoldtGammaDensity 0 pe) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hsqrt]
  have hnormenergy : ‖(-eulerPrimePowerEnergy pe : ℂ)‖ =
      eulerPrimePowerEnergy pe := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy]
  rw [hnormsqrt, hnormenergy]
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg henergy,
    abs_of_pos (Real.exp_pos _)]
  rw [abs_of_nonneg hsqrt]
  ring

theorem summable_norm_vonMangoldtGammaSourceTerm
    (a : VonMangoldtGammaSource) {x : ℝ} (hx : 0 < x) (j : ℕ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      ‖vonMangoldtGammaSourceTerm a j (x : ℂ) pe‖) := by
  have ha : Summable (fun pe : Nat.Primes × ℕ => ‖a pe‖ ^ 2) :=
    by simpa using (lp.memℓp a).summable (by norm_num)
  have hj : Summable (fun pe : Nat.Primes × ℕ =>
      ‖(vonMangoldtGammaJetAmplitude x j pe : ℂ)‖ ^ 2) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      summable_sq_vonMangoldtGammaJetAmplitude hx j
  have hprod := summable_norm_mul_norm_of_summable_norm_sq
    (E := ℂ) (f := fun pe => a pe)
    (g := fun pe => (vonMangoldtGammaJetAmplitude x j pe : ℂ)) ha hj
  refine hprod.congr (fun pe => ?_)
  rw [norm_vonMangoldtGammaSourceTerm]
  simp only [Complex.ofReal_re]
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem summable_vonMangoldtGammaSourceTerm
    (a : VonMangoldtGammaSource) {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      vonMangoldtGammaSourceTerm a j s pe) := by
  apply Summable.of_norm
  refine (summable_norm_vonMangoldtGammaSourceTerm a hs j).congr (fun pe => ?_)
  rw [norm_vonMangoldtGammaSourceTerm, norm_vonMangoldtGammaSourceTerm]
  simp

theorem vonMangoldtGammaJetReader_eq_sourceJet
    (x : ℝ) (hx : 0 < x) (j : ℕ) (a : VonMangoldtGammaSource) :
    vonMangoldtGammaJetReader x hx j a =
      vonMangoldtGammaSourceJet a j x := by
  rw [vonMangoldtGammaJetReader, innerSL_apply_apply,
    lp.inner_eq_tsum, vonMangoldtGammaSourceJet]
  apply tsum_congr
  intro pe
  rw [RCLike.inner_apply, vonMangoldtGammaSourceTerm,
    vonMangoldtGammaJetVector_apply]
  have hstar : starRingEnd ℂ (vonMangoldtGammaJetAmplitude x j pe : ℂ) =
      (vonMangoldtGammaJetAmplitude x j pe : ℂ) := by simp
  rw [hstar]
  rw [vonMangoldtGammaJetAmplitude_eq]
  have hexp : Complex.exp
      (-(eulerPrimePowerEnergy pe : ℂ) * (x : ℂ)) =
        (Real.exp (-x * eulerPrimePowerEnergy pe) : ℂ) := by
    have harg : -(eulerPrimePowerEnergy pe : ℂ) * (x : ℂ) =
        ((-x * eulerPrimePowerEnergy pe : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp]
  rw [hexp]
  push_cast
  ring

theorem vonMangoldtGammaSourceJet_shift
    (a : VonMangoldtGammaSource) (j : ℕ) (s : ℂ) :
    vonMangoldtGammaSourceJet (vonMangoldtGammaSourceShift a) j s =
      vonMangoldtGammaSourceJet a j (s + 1) := by
  apply tsum_congr
  intro pe
  rw [vonMangoldtGammaSourceTerm, vonMangoldtGammaSourceTerm,
    vonMangoldtGammaSourceShift_apply]
  have hn : ((eulerPrimePowerNat pe : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show eulerPrimePowerNat pe ≠ 0 by
      unfold eulerPrimePowerNat
      exact pow_ne_zero _ pe.1.property.ne_zero)
  have hlog : Complex.log ((eulerPrimePowerNat pe : ℕ) : ℂ) =
      (eulerPrimePowerEnergy pe : ℂ) := by
    rw [eulerPrimePowerEnergy, ← Complex.natCast_log]
  have hinv : ((eulerPrimePowerNat pe : ℕ) : ℂ)⁻¹ =
      Complex.exp (-(eulerPrimePowerEnergy pe : ℂ)) := by
    symm
    rw [Complex.exp_neg, ← hlog, Complex.exp_log hn]
  rw [hinv]
  have hexp :
      Complex.exp (-(eulerPrimePowerEnergy pe : ℂ)) *
          Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * s) =
        Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * (s + 1)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [show
      Complex.exp (-(eulerPrimePowerEnergy pe : ℂ)) * a pe *
            (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
            (-eulerPrimePowerEnergy pe : ℂ) ^ j *
            Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * s) =
        a pe * (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
            (-eulerPrimePowerEnergy pe : ℂ) ^ j *
            (Complex.exp (-(eulerPrimePowerEnergy pe : ℂ)) *
              Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * s)) by ring,
    hexp]

theorem abs_vonMangoldtGammaJetAmplitude_mono_re
    {x y : ℝ} (hxy : x ≤ y) (j : ℕ) (pe : Nat.Primes × ℕ) :
    |vonMangoldtGammaJetAmplitude y j pe| ≤
      |vonMangoldtGammaJetAmplitude x j pe| := by
  rw [vonMangoldtGammaJetAmplitude_eq, vonMangoldtGammaJetAmplitude_eq,
    abs_mul, abs_mul, abs_mul, abs_mul]
  have he : 0 ≤ eulerPrimePowerEnergy pe := Real.log_natCast_nonneg _
  have hexp : Real.exp (-y * eulerPrimePowerEnergy pe) ≤
      Real.exp (-x * eulerPrimePowerEnergy pe) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  gcongr

theorem norm_vonMangoldtGammaSourceTerm_mono_re
    (a : VonMangoldtGammaSource) (j : ℕ) {x : ℝ} {s : ℂ}
    (hxs : x ≤ s.re) (pe : Nat.Primes × ℕ) :
    ‖vonMangoldtGammaSourceTerm a j s pe‖ ≤
      ‖vonMangoldtGammaSourceTerm a j (x : ℂ) pe‖ := by
  rw [norm_vonMangoldtGammaSourceTerm, norm_vonMangoldtGammaSourceTerm]
  simp only [Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left
    (abs_vonMangoldtGammaJetAmplitude_mono_re hxs j pe) (norm_nonneg _)

theorem hasDerivAt_vonMangoldtGammaSourceTerm
    (a : VonMangoldtGammaSource) (j : ℕ) (s : ℂ)
    (pe : Nat.Primes × ℕ) :
    HasDerivAt (fun z : ℂ => vonMangoldtGammaSourceTerm a j z pe)
      (vonMangoldtGammaSourceTerm a (j + 1) s pe) s := by
  let E : ℂ := -(eulerPrimePowerEnergy pe : ℂ)
  let C : ℂ := a pe * (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) * E ^ j
  have hlinear : HasDerivAt (fun z : ℂ => E * z) E s :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul E
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (E * z))
      (E * Complex.exp (E * s)) s :=
    by simpa only [Function.comp_def, mul_comm] using
      (Complex.hasDerivAt_exp (E * s)).comp s hlinear
  have h := hexp.const_mul C
  simpa only [vonMangoldtGammaSourceTerm, E, C, pow_succ,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem hasDerivAt_vonMangoldtGammaSourceJet
    (a : VonMangoldtGammaSource) (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (vonMangoldtGammaSourceJet a j)
      (vonMangoldtGammaSourceJet a (j + 1) s) s := by
  let c : ℝ := s.re / 2
  let U : Set ℂ := {z : ℂ | c < z.re}
  have hc : 0 < c := by dsimp [c]; linarith
  have hopen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected U := by
    exact (convex_halfSpace_re_gt c).isPreconnected
  have hmem : s ∈ U := by dsimp [U, c]; linarith
  have hmajorant : Summable (fun pe : Nat.Primes × ℕ =>
      ‖vonMangoldtGammaSourceTerm a (j + 1) (c : ℂ) pe‖) :=
    summable_norm_vonMangoldtGammaSourceTerm a hc (j + 1)
  exact hasDerivAt_tsum_of_isPreconnected hmajorant hopen hconn
    (fun pe z _ => hasDerivAt_vonMangoldtGammaSourceTerm a j z pe)
    (fun pe z hz => norm_vonMangoldtGammaSourceTerm_mono_re a (j + 1) hz.le pe)
    hmem (summable_vonMangoldtGammaSourceTerm a hs j) hmem

theorem analyticOnNhd_vonMangoldtGammaSourceJet
    (a : VonMangoldtGammaSource) (j : ℕ) :
    AnalyticOnNhd ℂ (vonMangoldtGammaSourceJet a j) {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  intro s hs
  exact (hasDerivAt_vonMangoldtGammaSourceJet a j hs).differentiableAt.differentiableWithinAt
  exact isOpen_lt continuous_const Complex.continuous_re

theorem iteratedDeriv_vonMangoldtGammaSourceJet
    (a : VonMangoldtGammaSource) (j : ℕ) :
    ∀ (k : ℕ) {s : ℂ}, 0 < s.re →
      iteratedDeriv k (vonMangoldtGammaSourceJet a j) s =
        vonMangoldtGammaSourceJet a (j + k) s := by
  intro k
  induction k with
  | zero => intro s hs; simp
  | succ k ih =>
      intro s hs
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {z : ℂ | 0 < z.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have hev : iteratedDeriv k (vonMangoldtGammaSourceJet a j) =ᶠ[𝓝 s]
          vonMangoldtGammaSourceJet a (j + k) := by
        filter_upwards [hopen.mem_nhds hs] with z hz
        exact ih hz
      rw [hev.deriv_eq]
      have hderiv := (hasDerivAt_vonMangoldtGammaSourceJet a (j + k) hs).deriv
      simpa only [Nat.add_assoc] using hderiv

theorem vonMangoldtGammaDensity_pos
    (x : ℝ) (pe : Nat.Primes × ℕ) :
    0 < vonMangoldtGammaDensity x pe := by
  rw [vonMangoldtGammaDensity_eq]
  have hn : (0 : ℝ) < eulerPrimePowerNat pe := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  exact mul_pos
    (div_pos (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)) hn)
    (Real.exp_pos _)

def vonMangoldtGammaVerticalCoefficient
    (a : VonMangoldtGammaSource) (x : ℝ)
    (pe : Nat.Primes × ℕ) : ℂ :=
  vonMangoldtGammaSourceTerm a 0 (x : ℂ) pe

theorem summable_norm_vonMangoldtGammaVerticalCoefficient
    (a : VonMangoldtGammaSource) {x : ℝ} (hx : 0 < x) :
    Summable (fun pe : Nat.Primes × ℕ =>
      ‖vonMangoldtGammaVerticalCoefficient a x pe‖) := by
  simpa only [vonMangoldtGammaVerticalCoefficient] using
    summable_norm_vonMangoldtGammaSourceTerm a hx 0

theorem vonMangoldtGammaFrequency_injective :
    Function.Injective (fun pe : Nat.Primes × ℕ =>
      -eulerPrimePowerEnergy pe) := by
  intro x y hxy
  apply eulerPrimePowerNat_injective
  have hlog : Real.log (eulerPrimePowerNat x : ℝ) =
      Real.log (eulerPrimePowerNat y : ℝ) := by
    simpa only [eulerPrimePowerEnergy] using neg_injective hxy
  have hxpos : 0 < (eulerPrimePowerNat x : ℝ) := by
    exact_mod_cast pow_pos x.1.property.pos (x.2 + 1)
  have hypos : 0 < (eulerPrimePowerNat y : ℝ) := by
    exact_mod_cast pow_pos y.1.property.pos (y.2 + 1)
  exact_mod_cast Real.strictMonoOn_log.injOn
    (Set.mem_Ioi.mpr hxpos) (Set.mem_Ioi.mpr hypos) hlog

theorem vonMangoldtGammaSourceJet_vertical
    (a : VonMangoldtGammaSource) (x t : ℝ) :
    vonMangoldtGammaSourceJet a 0 ((x : ℂ) + I * (t : ℂ)) =
      ∑' pe : Nat.Primes × ℕ,
        vonMangoldtGammaVerticalCoefficient a x pe *
          Complex.exp (I * ((-eulerPrimePowerEnergy pe : ℝ) : ℂ) * (t : ℂ)) := by
  rw [vonMangoldtGammaSourceJet]
  apply tsum_congr
  intro pe
  let A : ℂ := a pe * (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ)
  let E : ℂ := -(eulerPrimePowerEnergy pe : ℂ)
  rw [vonMangoldtGammaVerticalCoefficient, vonMangoldtGammaSourceTerm,
    vonMangoldtGammaSourceTerm, pow_zero, mul_one]
  change A * Complex.exp (E * ((x : ℂ) + I * (t : ℂ))) =
    A * Complex.exp (E * (x : ℂ)) *
      Complex.exp (I * ((-eulerPrimePowerEnergy pe : ℝ) : ℂ) * (t : ℂ))
  calc
    _ = A * Complex.exp (E * (x : ℂ) +
          I * ((-eulerPrimePowerEnergy pe : ℝ) : ℂ) * (t : ℂ)) := by
        congr 2
        dsimp only [E]
        push_cast
        ring
    _ = A * (Complex.exp (E * (x : ℂ)) *
          Complex.exp (I * ((-eulerPrimePowerEnergy pe : ℝ) : ℂ) * (t : ℂ))) := by
        rw [Complex.exp_add]
    _ = _ := by
      dsimp only [A]
      simp only [mul_assoc]

theorem vonMangoldtGammaJetReaders_jointly_faithful
    {x : ℝ} (hx : 0 < x) {a : VonMangoldtGammaSource}
    (hzero : ∀ j : ℕ, vonMangoldtGammaJetReader x hx j a = 0) :
    a = 0 := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hxU : (x : ℂ) ∈ U := by simpa only [U, Set.mem_setOf_eq, Complex.ofReal_re]
  have hjet : ∀ k : ℕ,
      iteratedDeriv k (vonMangoldtGammaSourceJet a 0) (x : ℂ) =
        iteratedDeriv k (fun _ : ℂ => (0 : ℂ)) (x : ℂ) := by
    intro k
    rw [iteratedDeriv_vonMangoldtGammaSourceJet a 0 k hx, zero_add]
    have hk := hzero k
    rw [vonMangoldtGammaJetReader_eq_sourceJet x hx k a] at hk
    simpa using hk
  have hzeroOn : Set.EqOn (vonMangoldtGammaSourceJet a 0)
      (fun _ : ℂ => (0 : ℂ)) U :=
    eqOn_of_iteratedDeriv_eq hconn
      (analyticOnNhd_vonMangoldtGammaSourceJet a 0)
      analyticOnNhd_const hxU hjet
  have hseries : ∀ t : ℝ, (∑' pe : Nat.Primes × ℕ,
      vonMangoldtGammaVerticalCoefficient a x pe *
        Complex.exp (I * ((-eulerPrimePowerEnergy pe : ℝ) : ℂ) * (t : ℂ))) = 0 := by
    intro t
    rw [← vonMangoldtGammaSourceJet_vertical]
    apply hzeroOn
    simp only [U, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    simpa using hx
  have hcoeff : ∀ pe : Nat.Primes × ℕ,
      vonMangoldtGammaVerticalCoefficient a x pe = 0 := fun pe =>
    coeff_eq_zero_of_tsum_cis_eq_zero vonMangoldtGammaFrequency_injective
      (summable_norm_vonMangoldtGammaVerticalCoefficient a hx) hseries pe
  apply Subtype.ext
  funext pe
  have hc := hcoeff pe
  have hsqrt : (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.2 (vonMangoldtGammaDensity_pos 0 pe)).ne'
  have hexp : Complex.exp
      (-(eulerPrimePowerEnergy pe : ℂ) * (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hfac : (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
      Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * (x : ℂ)) ≠ 0 :=
    mul_ne_zero hsqrt hexp
  have ha : a pe * ((Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
      Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * (x : ℂ))) = 0 := by
    simpa only [vonMangoldtGammaVerticalCoefficient, vonMangoldtGammaSourceTerm,
      pow_zero, mul_one, mul_assoc] using hc
  exact (mul_eq_zero.mp ha).resolve_right hfac

/-- Closed faithfulness theorem for the literal prime-power Hilbert source at base point `2`. -/
theorem vonMangoldtGammaJetReaders_at_two_injective :
    Function.Injective (fun a : VonMangoldtGammaSource =>
      fun j : ℕ => vonMangoldtGammaJetReader 2 (by norm_num) j a) := by
  intro a b hab
  have hzero : ∀ j : ℕ,
      vonMangoldtGammaJetReader 2 (by norm_num) j (a - b) = 0 := by
    intro j
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun hab j)
  have hz := vonMangoldtGammaJetReaders_jointly_faithful (x := 2) (by norm_num) hzero
  exact sub_eq_zero.mp hz

theorem hasSum_taylor_vonMangoldtGammaJetReader
    (a : VonMangoldtGammaSource) {x : ℝ} (hx : 1 < x) (i : ℕ) :
    HasSum (fun k : ℕ =>
      vonMangoldtGammaJetReader x (by linarith) (i + k) a /
        (k.factorial : ℂ))
      (vonMangoldtGammaJetReader x (by linarith) i
        (vonMangoldtGammaSourceShift a)) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hball : Metric.ball (x : ℂ) x ⊆ U := by
    intro z hz
    have hdist : ‖z - (x : ℂ)‖ < x := by
      rw [← Complex.dist_eq]
      exact hz
    have hre : |z.re - x| ≤ ‖z - (x : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (z - (x : ℂ))
      simpa using h
    have hlt : |z.re - x| < x := lt_of_le_of_lt hre hdist
    have hlower := (abs_lt.mp hlt).1
    simpa only [U, Set.mem_setOf_eq] using (show 0 < z.re by linarith)
  have hdiff : DifferentiableOn ℂ (vonMangoldtGammaSourceJet a i)
      (Metric.ball (x : ℂ) x) :=
    ((analyticOnNhd_vonMangoldtGammaSourceJet a i).mono hball).differentiableOn
  have hxshift : (x : ℂ) + 1 ∈ Metric.ball (x : ℂ) x := by
    rw [Metric.mem_ball, Complex.dist_eq]
    simpa using hx
  have htaylor := Complex.hasSum_taylorSeries_on_ball hdiff hxshift
  have hval : vonMangoldtGammaSourceJet a i ((x : ℂ) + 1) =
      vonMangoldtGammaJetReader x (by linarith) i
        (vonMangoldtGammaSourceShift a) := by
    rw [← vonMangoldtGammaSourceJet_shift]
    exact (vonMangoldtGammaJetReader_eq_sourceJet x (by linarith) i
      (vonMangoldtGammaSourceShift a)).symm
  rw [hval] at htaylor
  refine htaylor.congr_fun fun k => ?_
  rw [iteratedDeriv_vonMangoldtGammaSourceJet a i k (by simpa using (show 0 < x by linarith))]
  rw [vonMangoldtGammaJetReader_eq_sourceJet x (by linarith) (i + k) a]
  simp [div_eq_inv_mul]

/-- Finite Gamma-clock shadow minus the exact source shift on the Hilbert carrier. -/
def vonMangoldtGammaHilbertDescentAnomaly
    (x : ℝ) (hx : 0 < x) (N : ℕ)
    (a : VonMangoldtGammaSource) (i : ℕ) : ℂ :=
  gammaClockShadowSum N (fun j => vonMangoldtGammaJetReader x hx j a) i -
    vonMangoldtGammaJetReader x hx i (vonMangoldtGammaSourceShift a)

theorem vonMangoldtGammaHilbertDescentAnomaly_eq
    (a : VonMangoldtGammaSource) {x : ℝ} (hx : 1 < x) (N i : ℕ) :
    vonMangoldtGammaHilbertDescentAnomaly x (by linarith) N a i =
      (∑ k ∈ Finset.range (N - i),
        vonMangoldtGammaJetReader x (by linarith) (i + k) a /
          (k.factorial : ℂ)) -
        ∑' k : ℕ, vonMangoldtGammaJetReader x (by linarith) (i + k) a /
          (k.factorial : ℂ) := by
  rw [vonMangoldtGammaHilbertDescentAnomaly, gammaClockShadowSum,
    (hasSum_taylor_vonMangoldtGammaJetReader a hx i).tsum_eq]

theorem vonMangoldtGammaHilbertDescentAnomaly_eq_neg_tail
    (a : VonMangoldtGammaSource) {x : ℝ} (hx : 1 < x) (N i : ℕ) :
    vonMangoldtGammaHilbertDescentAnomaly x (by linarith) N a i =
      -∑' k : ℕ, vonMangoldtGammaJetReader x (by linarith)
        (i + (k + (N - i))) a /
          (((k + (N - i)).factorial : ℕ) : ℂ) := by
  have hsum := hasSum_taylor_vonMangoldtGammaJetReader a hx i
  have hsplit := hsum.summable.sum_add_tsum_nat_add (N - i)
  rw [vonMangoldtGammaHilbertDescentAnomaly_eq a hx N i, ← hsplit]
  ring

theorem vonMangoldtGammaHilbertDescentAnomaly_bianchi
    (x : ℝ) (hx : 0 < x) (a : VonMangoldtGammaSource) {N i : ℕ}
    (hi : i ≤ N) :
    vonMangoldtGammaHilbertDescentAnomaly x hx (N + 1) a i -
        vonMangoldtGammaHilbertDescentAnomaly x hx N a i =
      vonMangoldtGammaJetReader x hx N a /
        (((N - i).factorial : ℕ) : ℂ) := by
  have hcard : N + 1 - i = (N - i) + 1 := by omega
  have hadd : i + (N - i) = N := by omega
  rw [vonMangoldtGammaHilbertDescentAnomaly,
    vonMangoldtGammaHilbertDescentAnomaly, gammaClockShadowSum,
    gammaClockShadowSum, hcard, Finset.sum_range_succ, hadd]
  ring

/-- Closed exact Taylor descent on the faithful Hilbert carrier at base point `2`. -/
theorem vonMangoldtGammaHilbert_taylor_descent_at_two
    (a : VonMangoldtGammaSource) (i : ℕ) :
    HasSum (fun k : ℕ =>
      vonMangoldtGammaJetReader 2 (by norm_num) (i + k) a /
        (k.factorial : ℂ))
      (vonMangoldtGammaJetReader 2 (by norm_num) i
        (vonMangoldtGammaSourceShift a)) :=
  hasSum_taylor_vonMangoldtGammaJetReader a (by norm_num) i

def vonMangoldtGammaRadialUnitVector
    (θ : ℝ) (hθ : 0 < θ) : VonMangoldtGammaSource :=
  vonMangoldtGammaJetVector θ hθ 0

@[simp] theorem vonMangoldtGammaRadialUnitVector_apply
    (θ : ℝ) (hθ : 0 < θ) (pe : Nat.Primes × ℕ) :
    vonMangoldtGammaRadialUnitVector θ hθ pe =
      (Real.sqrt (vonMangoldtGammaDensity 0 pe) *
        Real.exp (-θ * eulerPrimePowerEnergy pe) : ℂ) := by
  rw [vonMangoldtGammaRadialUnitVector,
    vonMangoldtGammaJetVector_apply, vonMangoldtGammaJetAmplitude_eq]
  simp

def vonMangoldtGammaEulerUnitCoefficient
    (pe : Nat.Primes × ℕ) : ℂ :=
  (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ)

theorem vonMangoldtGammaDensity_zero_prime_eq_boundaryCoordinate_sq
    (p : Nat.Primes) :
    vonMangoldtGammaDensity 0 (p, 0) =
      vonMangoldtGammaRenormalizedBoundaryCoordinate 0 p ^ 2 := by
  have hp2 : 2 ≤ (p : ℕ) := p.property.two_le
  have hnonneg : 0 ≤
      ArithmeticFunction.vonMangoldt p / (p : ℝ) *
        Real.exp (-0 * Real.log (p : ℝ)) := by positivity
  rw [vonMangoldtGammaDensity_eq,
    vonMangoldtGammaRenormalizedBoundaryCoordinate_eq hp2,
    Real.sq_sqrt hnonneg,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]
  simp [eulerPrimePowerNat, eulerPrimePowerEnergy]

theorem not_summable_vonMangoldtGammaDensity_zero :
    ¬Summable (fun pe : Nat.Primes × ℕ =>
      vonMangoldtGammaDensity 0 pe) := by
  intro hfull
  have hinj : Function.Injective
      (fun p : Nat.Primes => (p, (0 : ℕ))) := by
    intro p q hpq
    exact congrArg Prod.fst hpq
  have hprime := hfull.comp_injective hinj
  have hboundary : Summable (fun p : Nat.Primes =>
      vonMangoldtGammaRenormalizedBoundaryCoordinate 0 p ^ 2) := by
    exact hprime.congr fun p =>
      vonMangoldtGammaDensity_zero_prime_eq_boundaryCoordinate_sq p
  exact (not_lt_of_ge (le_refl 0))
    ((summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff 0).1 hboundary)

/-- Closed nonnormal-boundary theorem: literal Euler unit coefficient field is not in source. -/
theorem vonMangoldtGammaEulerUnit_not_mem_source :
    ¬ ∃ a : VonMangoldtGammaSource,
      ∀ pe : Nat.Primes × ℕ, a pe = vonMangoldtGammaEulerUnitCoefficient pe := by
  rintro ⟨a, ha⟩
  have hsq : Summable (fun pe : Nat.Primes × ℕ => ‖a pe‖ ^ 2) :=
    by simpa using (lp.memℓp a).summable (by norm_num)
  apply not_summable_vonMangoldtGammaDensity_zero
  refine hsq.congr fun pe => ?_
  rw [ha pe, vonMangoldtGammaEulerUnitCoefficient, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (vonMangoldtGammaDensity_nonneg 0 pe)]

theorem tendsto_vonMangoldtGammaRadialUnitCoefficient
    (pe : Nat.Primes × ℕ) :
    Tendsto (fun θ : ℝ =>
      (Real.sqrt (vonMangoldtGammaDensity 0 pe) *
        Real.exp (-θ * eulerPrimePowerEnergy pe) : ℂ))
      (𝓝 (0 : ℝ))
      (𝓝 (vonMangoldtGammaEulerUnitCoefficient pe)) := by
  have hcont : ContinuousAt (fun θ : ℝ =>
      (Real.sqrt (vonMangoldtGammaDensity 0 pe) *
        Real.exp (-θ * eulerPrimePowerEnergy pe) : ℂ)) 0 := by fun_prop
  have hzero : vonMangoldtGammaEulerUnitCoefficient pe =
      (Real.sqrt (vonMangoldtGammaDensity 0 pe) *
        Real.exp (-(0 : ℝ) * eulerPrimePowerEnergy pe) : ℂ) := by
    simp [vonMangoldtGammaEulerUnitCoefficient]
  rw [hzero]
  exact hcont

theorem vonMangoldtGammaRadialSourceTerm_eq_lSeriesTerm
    (θ : ℝ) (hθ : 0 < θ) (s : ℂ) (pe : Nat.Primes × ℕ) :
    vonMangoldtGammaSourceTerm (vonMangoldtGammaRadialUnitVector θ hθ) 0 s pe =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (((1 + θ : ℝ) : ℂ) + s) (eulerPrimePowerNat pe) := by
  have hnNat : eulerPrimePowerNat pe ≠ 0 := by
    unfold eulerPrimePowerNat
    exact pow_ne_zero _ pe.1.property.ne_zero
  have hn : ((eulerPrimePowerNat pe : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hnNat
  have hnR : (0 : ℝ) < eulerPrimePowerNat pe := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  have hsqrt : Real.sqrt (vonMangoldtGammaDensity 0 pe) ^ 2 =
      vonMangoldtGammaDensity 0 pe :=
    Real.sq_sqrt (vonMangoldtGammaDensity_nonneg 0 pe)
  have hlog : Complex.log ((eulerPrimePowerNat pe : ℕ) : ℂ) =
      (eulerPrimePowerEnergy pe : ℂ) := by
    rw [eulerPrimePowerEnergy, ← Complex.natCast_log]
  have hvm : ArithmeticFunction.vonMangoldt (eulerPrimePowerNat pe) =
      Real.log (pe.1 : ℝ) := by
    rw [eulerPrimePowerNat,
      ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero pe.2),
      ArithmeticFunction.vonMangoldt_apply_prime pe.1.property]
  rw [vonMangoldtGammaSourceTerm, vonMangoldtGammaRadialUnitVector_apply,
    pow_zero, mul_one, LSeries.term_of_ne_zero hnNat, hvm,
    Complex.cpow_def_of_ne_zero hn, hlog]
  have hdensity :
      ((Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
        (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ)) =
        (vonMangoldtGammaDensity 0 pe : ℂ) := by
    exact_mod_cast (by simpa only [pow_two] using hsqrt)
  have hinv : (((eulerPrimePowerNat pe : ℕ) : ℂ))⁻¹ =
      Complex.exp (-(eulerPrimePowerEnergy pe : ℂ)) := by
    symm
    rw [Complex.exp_neg, ← hlog, Complex.exp_log hn]
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  push_cast
  rw [show
      (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
          Complex.exp (-(θ : ℂ) * (eulerPrimePowerEnergy pe : ℂ)) *
          (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
          Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * s) =
        ((Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ) *
          (Real.sqrt (vonMangoldtGammaDensity 0 pe) : ℂ)) *
          (Complex.exp (-(θ : ℂ) * (eulerPrimePowerEnergy pe : ℂ)) *
            Complex.exp (-(eulerPrimePowerEnergy pe : ℂ) * s)) by ring,
    hdensity]
  rw [vonMangoldtGammaDensity_eq]
  simp only [mul_zero]
  push_cast
  rw [div_eq_mul_inv, hinv]
  simp only [zero_mul, Complex.exp_zero, mul_one]
  simp only [mul_assoc]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem vonMangoldtLSeriesTerm_support_primePower_for_radial
    (s : ℂ) :
    Function.support (LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) ⊆
      {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpow
  apply hn
  have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn0, hΛ]
    simp

theorem vonMangoldtGammaRadialSourceJet_eq_vonMangoldtLSeries
    (θ : ℝ) (hθ : 0 < θ) {s : ℂ} (hs : 0 < s.re) :
    vonMangoldtGammaSourceJet (vonMangoldtGammaRadialUnitVector θ hθ) 0 s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (((1 + θ : ℝ) : ℂ) + s) := by
  have hw : 1 < ((((1 + θ : ℝ) : ℂ) + s)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hsum : Summable (LSeries.term
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (((1 + θ : ℝ) : ℂ) + s)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hw
  have hreindex := tsum_eq_tsum_primes_of_support_subset_prime_powers hsum
    (vonMangoldtLSeriesTerm_support_primePower_for_radial
      (((1 + θ : ℝ) : ℂ) + s))
  have hpair : Summable (fun pe : Nat.Primes × ℕ =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (((1 + θ : ℝ) : ℂ) + s) (eulerPrimePowerNat pe)) :=
    hsum.comp_injective eulerPrimePowerNat_injective
  rw [vonMangoldtGammaSourceJet, LSeries, hreindex]
  calc
    _ = ∑' pe : Nat.Primes × ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (((1 + θ : ℝ) : ℂ) + s) (eulerPrimePowerNat pe) :=
      tsum_congr fun pe =>
        vonMangoldtGammaRadialSourceTerm_eq_lSeriesTerm θ hθ s pe
    _ = ∑' p : Nat.Primes, ∑' k : ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (((1 + θ : ℝ) : ℂ) + s) (eulerPrimePowerNat (p, k)) :=
      hpair.tsum_prod
    _ = _ := by rfl

/-- Literal equation `(18)`: every radial interior source is the shifted `-zeta'/zeta`. -/
theorem vonMangoldtGammaRadialSourceJet_eq_eulerLogDerivative
    (θ : ℝ) (hθ : 0 < θ) {s : ℂ} (hs : 0 < s.re) :
    vonMangoldtGammaSourceJet (vonMangoldtGammaRadialUnitVector θ hθ) 0 s =
      GaloisForLFunctions.RHTower.eulerLogDerivative
        (((1 + θ : ℝ) : ℂ) + s) := by
  rw [vonMangoldtGammaRadialSourceJet_eq_vonMangoldtLSeries θ hθ hs]
  have hw : 1 < ((((1 + θ : ℝ) : ℂ) + s)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  symm
  simpa only [iteratedDeriv_zero] using
    (GaloisForLFunctions.RHTower.iteratedDeriv_eulerLogDerivative_eq_vonMangoldtLSeries 0 hw)

/-- Closed full Hilbert/clock/boundary colligation package at canonical base point `2`. -/
theorem vonMangoldtGammaHilbertClockDescent_completion :
    ‖vonMangoldtGammaSourceShift‖ ≤ 1 / 2 ∧
    (∀ N : ℕ, ContinuousLinearMap.IsHilbertSchmidt (𝕜 := ℂ)
      (vonMangoldtGammaObservation 2 (by norm_num) N)) ∧
    Function.Injective (fun a : VonMangoldtGammaSource =>
      fun j : ℕ => vonMangoldtGammaJetReader 2 (by norm_num) j a) ∧
    (∀ (a : VonMangoldtGammaSource) (i : ℕ),
      HasSum (fun k : ℕ =>
        vonMangoldtGammaJetReader 2 (by norm_num) (i + k) a /
          (k.factorial : ℂ))
        (vonMangoldtGammaJetReader 2 (by norm_num) i
          (vonMangoldtGammaSourceShift a))) ∧
    (∀ (a : VonMangoldtGammaSource) (N i : ℕ),
      vonMangoldtGammaHilbertDescentAnomaly 2 (by norm_num) N a i =
        -∑' k : ℕ, vonMangoldtGammaJetReader 2 (by norm_num)
          (i + (k + (N - i))) a /
            (((k + (N - i)).factorial : ℕ) : ℂ)) ∧
    (∀ (a : VonMangoldtGammaSource) (N i : ℕ), i ≤ N →
      vonMangoldtGammaHilbertDescentAnomaly 2 (by norm_num) (N + 1) a i -
          vonMangoldtGammaHilbertDescentAnomaly 2 (by norm_num) N a i =
        vonMangoldtGammaJetReader 2 (by norm_num) N a /
          (((N - i).factorial : ℕ) : ℂ)) ∧
    (¬ ∃ a : VonMangoldtGammaSource,
      ∀ pe : Nat.Primes × ℕ, a pe = vonMangoldtGammaEulerUnitCoefficient pe) ∧
    (∀ (θ : ℝ) (hθ : 0 < θ) (s : ℂ), 0 < s.re →
      vonMangoldtGammaSourceJet
          (vonMangoldtGammaRadialUnitVector θ hθ) 0 s =
        GaloisForLFunctions.RHTower.eulerLogDerivative
          (((1 + θ : ℝ) : ℂ) + s)) ∧
    (∀ (M N n : ℕ) (w : Fin n → ℂ),
      @Matrix.PosSemidef (Fin n) ℂ Complex.instRing Complex.partialOrder
        Complex.instStarRing (finiteVonMangoldtAllDepthCauchyGram M N w)) ∧
    (∀ (x : ℝ), 0 < x → ∀ (n : ℕ) (a : Fin n → ℕ),
      (infiniteVonMangoldtGammaRawGram x a).PosSemidef) := by
  refine ⟨norm_vonMangoldtGammaSourceShift_le,
    fun N => vonMangoldtGammaObservation_isHilbertSchmidt 2 (by norm_num) N,
    vonMangoldtGammaJetReaders_at_two_injective,
    vonMangoldtGammaHilbert_taylor_descent_at_two,
    fun a N i => vonMangoldtGammaHilbertDescentAnomaly_eq_neg_tail a (by norm_num) N i,
    ?_, vonMangoldtGammaEulerUnit_not_mem_source, ?_, ?_, ?_⟩
  · intro a N i hi
    exact vonMangoldtGammaHilbertDescentAnomaly_bianchi 2 (by norm_num) a hi
  · intro θ hθ s hs
    exact vonMangoldtGammaRadialSourceJet_eq_eulerLogDerivative θ hθ hs
  · exact fun M N n w => finiteVonMangoldtAllDepthCauchyGram_posSemidef M N w
  · exact fun x hx n a => infiniteVonMangoldtGammaRawGram_posSemidef hx a

end RHTower
