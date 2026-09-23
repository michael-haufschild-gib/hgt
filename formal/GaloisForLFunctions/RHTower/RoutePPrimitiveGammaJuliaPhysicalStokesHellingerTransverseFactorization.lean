import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCofinalChildTraceClass
import GaloisForLFunctions.HTGeometry.LpInjectionCompression

/-!
# Completed prime–Gamma Hellinger transverse factorization

Full cofinal Route-P Hellinger carrier has an exact Lorentz square law on arbitrary complex prime
coefficients.  Its physical channel quadratic is positive child energy of one combined channel
minus `64r` times transverse child energy.  On every transverse null line the positive square
vanishes coefficientwise, leaving a nonpositive signed response on completed prime `ℓ²`.

At physical pivot ratio this is same cofinal operator whose diagonal trace is already identified
with completed prime–Gamma crossing current.  No Xi zero location enters.
-/

open Complex ContinuousLinearMap Filter Topology Set
open scoped InnerProductSpace

namespace RHTower

noncomputable section

abbrev routePPrimitiveGammaJuliaStokesChildSpace :=
  lp (fun _ : Nat.Primes => ℂ) 2

def routePPrimitiveGammaJuliaStokesChildOperator
    (d : ℝ) (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesChildSpace →L[ℂ]
      routePPrimitiveGammaJuliaStokesChildSpace :=
  HilbertSchmidt.toOperator
    (routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd)

def routePPrimitiveGammaJuliaStokesChildEnergy
    (d : ℝ) (hd : 0 < d)
    (x : routePPrimitiveGammaJuliaStokesChildSpace) : ℝ :=
  (inner ℂ x (routePPrimitiveGammaJuliaStokesChildOperator d hd x)).re

def routePPrimitiveGammaJuliaStokesChildCross
    (d : ℝ) (hd : 0 < d)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) : ℝ :=
  (inner ℂ x (routePPrimitiveGammaJuliaStokesChildOperator d hd y) +
    inner ℂ y (routePPrimitiveGammaJuliaStokesChildOperator d hd x)).re

def routePPrimitiveGammaJuliaStokesHellingerInterference
    (d : ℝ) (hd : 0 < d) (r : ℝ)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) : ℝ :=
  routePPrimitiveGammaJuliaStokesChildEnergy d hd x +
    (8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect) *
      routePPrimitiveGammaJuliaStokesChildCross d hd x y -
    r * routePPrimitiveGammaJuliaStokesChildEnergy d hd y

theorem routePPrimitiveGammaJuliaStokesChildEnergy_add_smul
    (d : ℝ) (hd : 0 < d) (a : ℝ)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) :
    routePPrimitiveGammaJuliaStokesChildEnergy d hd
        (x + (a : ℂ) • y) =
      routePPrimitiveGammaJuliaStokesChildEnergy d hd x +
        a * routePPrimitiveGammaJuliaStokesChildCross d hd x y +
        a ^ (2 : ℕ) * routePPrimitiveGammaJuliaStokesChildEnergy d hd y := by
  unfold routePPrimitiveGammaJuliaStokesChildEnergy
    routePPrimitiveGammaJuliaStokesChildCross
    routePPrimitiveGammaJuliaStokesChildOperator
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem routePPrimitiveGammaJuliaStokesHellingerInterference_factor
    (d : ℝ) (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) :
    routePPrimitiveGammaJuliaStokesHellingerInterference d hd r x y =
      routePPrimitiveGammaJuliaStokesChildEnergy d hd
        (x + ((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) -
      64 * r * routePPrimitiveGammaJuliaStokesChildEnergy d hd y := by
  have hsqrt : Real.sqrt r ^ (2 : ℕ) = r := Real.sq_sqrt hr
  have hdefect : routeEPCubicFourthDepthJuliaDefect ^ (2 : ℕ) = (63 / 64 : ℝ) :=
    routeEPCubicFourthDepthJuliaDefect_sq
  have ha : (8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect) ^ (2 : ℕ) =
      63 * r := by
    rw [mul_pow, mul_pow, hsqrt, hdefect]
    ring
  rw [routePPrimitiveGammaJuliaStokesChildEnergy_add_smul]
  unfold routePPrimitiveGammaJuliaStokesHellingerInterference
  rw [ha]
  ring

theorem routePPrimitiveGammaJuliaStokesChildEnergy_nonneg
    (d : ℝ) (hd : 0 < d)
    (x : routePPrimitiveGammaJuliaStokesChildSpace) :
    0 ≤ routePPrimitiveGammaJuliaStokesChildEnergy d hd x := by
  have hpos := routePPrimitiveGammaJuliaStokesCofinalChildOperator_isPositive hd
  have hself := routePPrimitiveGammaJuliaStokesCofinalChildOperator_isSelfAdjoint hd
  let T := routePPrimitiveGammaJuliaStokesChildOperator d hd
  change 0 ≤ (inner ℂ x (T x)).re
  calc
    0 ≤ (inner ℂ (T x) x).re := by
      simpa [T, routePPrimitiveGammaJuliaStokesChildOperator,
        ContinuousLinearMap.reApplyInnerSelf_apply] using hpos.2 x
    _ = (inner ℂ x (T x)).re :=
      congrArg Complex.re (hself.isSymmetric x x)

theorem routePPrimitiveGammaJuliaStokesHellingerInterference_transverse
    (d : ℝ) (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r)
    (y : routePPrimitiveGammaJuliaStokesChildSpace) :
    routePPrimitiveGammaJuliaStokesHellingerInterference d hd r
        (-((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y =
      -64 * r * routePPrimitiveGammaJuliaStokesChildEnergy d hd y := by
  rw [routePPrimitiveGammaJuliaStokesHellingerInterference_factor d hd hr]
  have hzero : routePPrimitiveGammaJuliaStokesChildEnergy d hd 0 = 0 := by
    simp [routePPrimitiveGammaJuliaStokesChildEnergy,
      routePPrimitiveGammaJuliaStokesChildOperator]
  have hcancel :
      -((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y +
          ((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y = 0 := by
    rw [neg_smul, neg_add_cancel]
  rw [hcancel, hzero]
  ring

theorem routePPrimitiveGammaJuliaStokesHellingerInterference_transverse_nonpos
    (d : ℝ) (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r)
    (y : routePPrimitiveGammaJuliaStokesChildSpace) :
    routePPrimitiveGammaJuliaStokesHellingerInterference d hd r
        (-((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y ≤ 0 := by
  rw [routePPrimitiveGammaJuliaStokesHellingerInterference_transverse d hd hr]
  have hscale : (-64 : ℝ) * r ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) hr
  exact mul_nonpos_of_nonpos_of_nonneg hscale
    (routePPrimitiveGammaJuliaStokesChildEnergy_nonneg d hd y)

/-- Physical completed prime–Gamma specialization of transverse sign law. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerInterference_transverse_nonpos
    {d : ℝ} (hd : 0 < d)
    (hr : 0 ≤ routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)
    (y : routePPrimitiveGammaJuliaStokesChildSpace) :
    routePPrimitiveGammaJuliaStokesHellingerInterference d hd
        (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)
        (-((8 * Real.sqrt (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
          routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y ≤ 0 :=
  routePPrimitiveGammaJuliaStokesHellingerInterference_transverse_nonpos
    d hd hr y

/-- Closed universal law: whenever physical right-ray parameters are supplied, arbitrary
coefficient factorization, transverse sign, and exact completed trace hold together. -/
theorem routePPrimitive_GammaJulia_physicalStokesHellingerTransverseFactorization :
    ∀ (d : ℝ) (hd : 0 < d)
      (_hr : 0 ≤ routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d),
      (∀ x y : routePPrimitiveGammaJuliaStokesChildSpace,
        routePPrimitiveGammaJuliaStokesHellingerInterference d hd
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) x y =
          routePPrimitiveGammaJuliaStokesChildEnergy d hd
            (x + ((8 * Real.sqrt
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
                routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) -
          64 * routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d *
            routePPrimitiveGammaJuliaStokesChildEnergy d hd y) ∧
      (∀ y : routePPrimitiveGammaJuliaStokesChildSpace,
        routePPrimitiveGammaJuliaStokesHellingerInterference d hd
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)
            (-((8 * Real.sqrt
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
                routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y ≤ 0) ∧
      (∑' ip : Fin 2 × Nat.Primes,
        routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel d
          (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) (ip, ip)) =
        (gammaSewnMobiusApertureStokesOrientedCompletedPrimeGammaCurrent d : ℂ) := by
  intro d hd hr
  exact ⟨fun x y =>
      routePPrimitiveGammaJuliaStokesHellingerInterference_factor
        d hd (r := routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) hr x y,
    fun y =>
      routePPrimitiveGammaJuliaPhysicalStokesHellingerInterference_transverse_nonpos
        (d := d) hd hr y,
    routePPrimitiveGammaJuliaPhysicalStokesHellinger_diagonalTrace_eq_completed hd⟩

/-- Premise-free physical right-ray law: sufficiently near wall, every completed transverse
coefficient vector has nonpositive signed Hellinger interference. -/
theorem eventually_routePPrimitiveGammaJuliaPhysicalStokesHellingerTransverse_nonpos :
    ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      ∃ hd : 0 < d, ∀ y : routePPrimitiveGammaJuliaStokesChildSpace,
        routePPrimitiveGammaJuliaStokesHellingerInterference d hd
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)
            (-((8 * Real.sqrt
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
                routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y ≤ 0 := by
  filter_upwards
    [eventually_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio_pos,
      self_mem_nhdsWithin] with d hr hd
  change 0 < d at hd
  exact ⟨hd, fun y =>
    routePPrimitiveGammaJuliaPhysicalStokesHellingerInterference_transverse_nonpos
      hd hr.le y⟩

abbrev routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSpace := lp (fun _ : Fin 2 × Nat.Primes => ℂ) 2

def routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection (i : Fin 2) : Nat.Primes → Fin 2 × Nat.Primes :=
  fun p => (i, p)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective (i : Fin 2) :
    Function.Injective (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection i) := by
  intro p q h
  exact congrArg Prod.snd h

def routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair (x y : routePPrimitiveGammaJuliaStokesChildSpace) : routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSpace :=
  lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 0) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 0) x +
    lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 1) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 1) y

private theorem routeP_lpScalarInjection_coordinate_of_ne
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f)
    (x : lp (fun _ : ι => ℂ) 2) (k : κ)
    (hk : ∀ i, f i ≠ k) :
    lpScalarInjection f hf x k = 0 := by
  let U := (lpScalarInjection f hf).toContinuousLinearMap
  calc
    lpScalarInjection f hf x k = inner ℂ (lp.single 2 k 1) (U x) := by
      rw [lp.inner_single_left]
      simp [U]
    _ = inner ℂ (U.adjoint (lp.single 2 k 1)) x := by
      exact (ContinuousLinearMap.adjoint_inner_left U _ _).symm
    _ = inner ℂ (lpCoordinatePullback (E := ℂ) f hf (lp.single 2 k 1)) x := by
      rw [lpCoordinatePullback_eq_adjoint_lpScalarInjection]
    _ = 0 := by
      have hz : lpCoordinatePullback (E := ℂ) f hf (lp.single 2 k 1) = 0 := by
        apply lp.ext
        funext i
        rw [lpCoordinatePullback_apply, lp.single_apply]
        simp [hk i]
      rw [hz, inner_zero_left]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_apply
    (j k : Fin 2) (x : routePPrimitiveGammaJuliaStokesChildSpace)
    (p : Nat.Primes) :
    lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection j) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective j) x
        (k, p) = if k = j then x p else 0 := by
  by_cases hkj : k = j
  · subst k
    simpa [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection] using
      lpScalarInjection_coordinate (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection j)
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective j) x p
  · rw [if_neg hkj]
    apply routeP_lpScalarInjection_coordinate_of_ne
    intro q hq
    exact hkj (congrArg Prod.fst hq).symm

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair_apply_zero
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y (0, p) = x p := by
  change
    lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 0) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 0) x
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 0 p) +
      lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 1) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 1) y
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 0 p) = x p
  rw [lpScalarInjection_coordinate
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 0) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 0) x p]
  rw [routeP_lpScalarInjection_coordinate_of_ne]
  · exact add_zero _
  · intro q h
    exact Fin.zero_ne_one (congrArg Prod.fst h).symm

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair_apply_one
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y (1, p) = y p := by
  change
    lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 0) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 0) x
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 1 p) +
      lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 1) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 1) y
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 1 p) = y p
  rw [routeP_lpScalarInjection_coordinate_of_ne]
  · rw [lpScalarInjection_coordinate
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection 1) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective 1) y p]
    exact zero_add _
  · intro q h
    exact Fin.zero_ne_one (congrArg Prod.fst h)

def routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator (d : ℝ) (hd : 0 < d) (r : ℝ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSpace →L[ℂ] routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSpace :=
  HilbertSchmidt.toOperator
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_injection_apply
    (d : ℝ) (hd : 0 < d) (r : ℝ) (i j : Fin 2)
    (x : routePPrimitiveGammaJuliaStokesChildSpace) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r
        (lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection j)
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective j) x) (i, p) =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r i j *
        routePPrimitiveGammaJuliaStokesChildOperator d hd x p := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator, HilbertSchmidt.toOperator_apply]
  have hsum := HilbertSchmidt.summable_row_mul
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel_isHS hd r)
    (lpScalarInjection (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection j)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_injective j) x) (i, p)
  rw [hsum.tsum_prod, tsum_fintype]
  simp_rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalKernel,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelInjection_apply]
  fin_cases i <;> fin_cases j <;>
    simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel,
      routePPrimitiveGammaJuliaStokesChildOperator,
      HilbertSchmidt.toOperator_apply, ← tsum_mul_left, mul_assoc]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_apply
    (d : ℝ) (hd : 0 < d) (r : ℝ)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) (i : Fin 2)
    (p : Nat.Primes) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y) (i, p) =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r i 0 *
          routePPrimitiveGammaJuliaStokesChildOperator d hd x p +
        routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel r i 1 *
          routePPrimitiveGammaJuliaStokesChildOperator d hd y p := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair, map_add, lp.coeFn_add, Pi.add_apply,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_injection_apply, routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_injection_apply]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_inner
    (d : ℝ) (hd : 0 < d) (r : ℝ)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) :
    inner ℂ (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y)
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y)) =
      inner ℂ x (routePPrimitiveGammaJuliaStokesChildOperator d hd x) +
        ((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) *
          inner ℂ x (routePPrimitiveGammaJuliaStokesChildOperator d hd y) +
        ((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) *
          inner ℂ y (routePPrimitiveGammaJuliaStokesChildOperator d hd x) -
        (r : ℂ) * inner ℂ y
          (routePPrimitiveGammaJuliaStokesChildOperator d hd y) := by
  rw [lp.inner_eq_tsum]
  have hsum := lp.summable_inner (𝕜 := ℂ) (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y)
    (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y))
  rw [hsum.tsum_prod, tsum_fintype]
  simp only [Fin.sum_univ_two]
  simp_rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair_apply_zero, routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair_apply_one,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_apply, RCLike.inner_apply]
  simp [routePPrimitiveGammaJuliaPhysicalStokesHellingerChannel]
  let T := routePPrimitiveGammaJuliaStokesChildOperator d hd
  let a : ℂ := 8 * (Real.sqrt r : ℂ) *
    (routeEPCubicFourthDepthJuliaDefect : ℂ)
  have hfirst :
      (fun c : Nat.Primes => (T x c + a * T y c) * star (x c)) =
        fun c => inner ℂ (x c) (T x c) + a * inner ℂ (x c) (T y c) := by
    funext c
    simp [RCLike.inner_apply]
    ring
  have hsecond :
      (fun c : Nat.Primes => (a * T x c - (r : ℂ) * T y c) * star (y c)) =
        fun c => a * inner ℂ (y c) (T x c) +
          (-(r : ℂ)) * inner ℂ (y c) (T y c) := by
    funext c
    simp [RCLike.inner_apply]
    ring
  change
    (∑' c : Nat.Primes, (T x c + a * T y c) * star (x c)) +
        (∑' c : Nat.Primes, (a * T x c - (r : ℂ) * T y c) * star (y c)) =
      inner ℂ x (T x) + a * inner ℂ x (T y) +
        a * inner ℂ y (T x) - (r : ℂ) * inner ℂ y (T y)
  rw [hfirst, hsecond]
  have hxx := lp.summable_inner (𝕜 := ℂ) x (T x)
  have hxy := lp.summable_inner (𝕜 := ℂ) x (T y)
  have hyx := lp.summable_inner (𝕜 := ℂ) y (T x)
  have hyy := lp.summable_inner (𝕜 := ℂ) y (T y)
  rw [hxx.tsum_add (Summable.mul_left a hxy),
    (Summable.mul_left a hyx).tsum_add (Summable.mul_left (-(r : ℂ)) hyy),
    tsum_mul_left, tsum_mul_left, tsum_mul_left,
    ← lp.inner_eq_tsum x (T x), ← lp.inner_eq_tsum x (T y),
    ← lp.inner_eq_tsum y (T x), ← lp.inner_eq_tsum y (T y)]
  dsimp only [a, T]
  ring

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_quadratic_eq_interference
    (d : ℝ) (hd : 0 < d) (r : ℝ)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) :
    (inner ℂ (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y))).re =
        routePPrimitiveGammaJuliaStokesHellingerInterference d hd r x y := by
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_inner]
  unfold routePPrimitiveGammaJuliaStokesHellingerInterference
    routePPrimitiveGammaJuliaStokesChildEnergy
    routePPrimitiveGammaJuliaStokesChildCross
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Actual full cofinal operator has exact Lorentz-square factorization on arbitrary completed
channel coefficients. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_factor
    (d : ℝ) (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r)
    (x y : routePPrimitiveGammaJuliaStokesChildSpace) :
    (inner ℂ
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair x y))).re =
      routePPrimitiveGammaJuliaStokesChildEnergy d hd
        (x + ((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) -
      64 * r * routePPrimitiveGammaJuliaStokesChildEnergy d hd y := by
  rw [
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_quadratic_eq_interference,
    routePPrimitiveGammaJuliaStokesHellingerInterference_factor d hd hr]

/-- Every completed transverse null line annihilates positive square of actual full cofinal
operator and leaves exact negative child energy. -/
theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_transverse
    (d : ℝ) (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r)
    (y : routePPrimitiveGammaJuliaStokesChildSpace) :
    (inner ℂ
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair
        (-((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair
          (-((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y))).re =
      -64 * r * routePPrimitiveGammaJuliaStokesChildEnergy d hd y := by
  rw [
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_quadratic_eq_interference,
    routePPrimitiveGammaJuliaStokesHellingerInterference_transverse d hd hr]

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_transverse_nonpos
    (d : ℝ) (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r)
    (y : routePPrimitiveGammaJuliaStokesChildSpace) :
    (inner ℂ
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair
        (-((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y)
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd r
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair
          (-((8 * Real.sqrt r * routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y))).re ≤ 0 := by
  rw [
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_channelPair_quadratic_eq_interference]
  exact routePPrimitiveGammaJuliaStokesHellingerInterference_transverse_nonpos
    d hd hr y

/-- Premise-free actual-operator law on punctured physical right neighborhood. -/
theorem eventually_routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_transverse_nonpos :
    ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      ∃ hd : 0 < d, ∀ y : routePPrimitiveGammaJuliaStokesChildSpace,
        (inner ℂ
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair
            (-((8 * Real.sqrt
              (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
                routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y)
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator d hd
            (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d)
            (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelPair
              (-((8 * Real.sqrt
                (routePPrimitiveGammaJuliaPhysicalStokesPivotRatio d) *
                  routeEPCubicFourthDepthJuliaDefect : ℝ) : ℂ) • y) y))).re ≤ 0 := by
  filter_upwards
    [eventually_routePPrimitiveGammaJuliaPhysicalStokesPivotRatio_pos,
      self_mem_nhdsWithin] with d hr hd
  change 0 < d at hd
  exact ⟨hd, fun y =>
    routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalOperator_transverse_nonpos
      d hd hr.le y⟩


end

end RHTower
