import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicAdditiveEvenProjectionNoGo
import GaloisForLFunctions.RHTower.ArithmeticLogClockFiniteJetSaturation
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesApertureWallXiDivisorNoGo
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.RHTower.RouteRReciprocalLogFisherEntranceWall
import GaloisForLFunctions.HTGeometry.FermionicFactorialTraceBound

/-!
# Cofinal real-scalar unitization no-go for the holomorphic SC reservoir

This module classifies every real scalar spectral shift of the complete coefficient-faithful
holomorphic prime Gamma-Bockstein reservoir. A compact-open normalized-Xi landing faces an exact
dichotomy. If packet dimension times scalar magnitude does not vanish, the same-sign cubic odd
exterior layer leaves a nonzero parity defect at `z = ±1`. If that product does vanish, the
prime neutral jets have zero Cesàro mean and the complete quadratic central jet collapses to zero,
contradicting the strictly negative quadratic central jet of normalized completed Xi.

Thus arbitrary signs, oscillations, and cofinal decay rates of a real scalar shift do not escape
the SC obstruction. A surviving unitization must change phase genuinely in the complex direction
or introduce non-scalar cross-prime coupling. No RH assumption, zero-location input, numerical
estimate, or nonstandard axiom is used.
-/

open Complex Filter Topology Set
open scoped BigOperators Matrix

namespace RHTower

noncomputable section


theorem six_mul_choose_three_add_three (m : ℕ) :
    6 * (m + 3).choose 3 = (m + 3) * (m + 2) * (m + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (m + 3) 3
  norm_num [Nat.descFactorial] at h
  have hm : m + 3 - 2 = m + 1 := by omega
  rw [hm] at h
  calc
    6 * (m + 3).choose 3 = (m + 1) * ((m + 2) * (m + 3)) := h.symm
    _ = (m + 3) * (m + 2) * (m + 1) := by ring


/-- Real scalar unitization of the complete coefficient-faithful holomorphic SC reservoir. -/
def preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant
    (a : ℕ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  (1 + (a m : ℂ) •
    preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) z).det

theorem preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_zero
    (a : ℕ → ℝ) (m : ℕ) :
    preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m 0 = 1 := by
  rw [preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant]
  have hmatrix :
      preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) 0 = 0 := by
    ext i j
    rw [preDivisorRiggedPrimeHolomorphicReservoirMatrix, Matrix.mul_diagonal]
    simp [preDivisorHolomorphicPrimeBockstein]
  rw [hmatrix]
  simp

theorem differentiable_preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant
    (a : ℕ → ℝ) (m : ℕ) :
    Differentiable ℂ
      (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m) := by
  unfold preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant
  unfold preDivisorRiggedPrimeHolomorphicReservoirMatrix
  unfold preDivisorHolomorphicPrimeBockstein
  simp only [Matrix.det_apply', Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_diagonal]
  fun_prop

theorem preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_ofReal
    (a : ℕ → ℝ) (m : ℕ) (t : ℝ) :
    preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m (t : ℂ) =
      (unitizedRealReservoirDeterminant
        (fun i : Fin (m + 3) =>
          a m * primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i)) : ℂ) := by
  rw [preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant,
    preDivisorRiggedPrimeHolomorphicReservoirMatrix_ofReal]
  let M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
    realReservoirDiagonalMatrix
      (fun i => primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i))
  let aC : ℂ := a m
  let aR : ℝ := a m
  have hscaled :
      aC • M.map Complex.ofRealHom = (aR • M).map Complex.ofRealHom := by
    ext i j
    simp [aC, aR]
  rw [hscaled]
  have hadd :
      (1 + (aR • M).map Complex.ofRealHom) =
        (1 + aR • M).map Complex.ofRealHom := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hadd]
  calc
    ((1 + aR • M).map Complex.ofRealHom).det =
        (Complex.ofRealHom.mapMatrix (1 + aR • M)).det := rfl
    _ = Complex.ofRealHom ((1 + aR • M).det) :=
      (RingHom.map_det Complex.ofRealHom (1 + aR • M)).symm
    _ = (((1 + aR • M).det : ℝ) : ℂ) := rfl
    _ = (unitizedRealReservoirDeterminant
        (fun i : Fin (m + 3) =>
          a m * primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i)) : ℂ) := by
      congr 2
      congr 1
      dsimp only [aR, M]
      ext i j
      rw [Matrix.smul_apply, realReservoirDiagonalMatrix_apply,
        realReservoirDiagonalMatrix_apply]
      ring

/-- The full cubic layer is a lower bound for the odd unitization defect on a negative packet. -/
theorem four_mul_cubicMass_le_unitizedRealReservoirDeterminant_sub_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hb : ∀ i, b i < 0) :
    4 * ∑ s ∈ (Finset.univ : Finset ι).powersetCard 3,
        -(∏ i ∈ s, b i) ≤
      unitizedRealReservoirDeterminant b -
        unitizedRealReservoirDeterminant (-b) := by
  classical
  rw [unitizedRealReservoirDeterminant_sub_neg_eq_odd_powerset]
  let O := ((Finset.univ : Finset ι).powerset).filter (fun s => Odd s.card)
  let C := (Finset.univ : Finset ι).powersetCard 3
  let term : Finset ι → ℝ := fun s =>
    (1 - (s.card : ℝ)) * ∏ i ∈ s, b i
  have hCO : C ⊆ O := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hs.1, by rw [hs.2]; decide⟩
  have hnonneg : ∀ s ∈ O, 0 ≤ term s := by
    intro s hs
    exact realReservoirOddSummand_nonneg hb s
      (Finset.mem_filter.mp hs).2
  have hsub : ∑ s ∈ C, term s ≤ ∑ s ∈ O, term s :=
    Finset.sum_le_sum_of_subset_of_nonneg hCO
      (fun s hsO hsC => hnonneg s hsO)
  have hcubic : 2 * ∑ s ∈ C, term s =
      4 * ∑ s ∈ C, -(∏ i ∈ s, b i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hcard : s.card = 3 := (Finset.mem_powersetCard.mp hs).2
    dsimp only [term]
    rw [hcard]
    norm_num
    ring
  change 4 * ∑ s ∈ C, -(∏ i ∈ s, b i) ≤
    2 * ∑ s ∈ O, term s
  rw [← hcubic]
  exact mul_le_mul_of_nonneg_left hsub (by norm_num)

def preDivisorRiggedPrimeScaledRealBocksteinVector
    (a : ℝ) (m : ℕ) : Fin (m + 3) → ℝ :=
  fun i => a * preDivisorRiggedPrimeRealBocksteinVector m i

theorem preDivisorRiggedPrimeScaledRealBocksteinVector_neg
    {a : ℝ} (ha : 0 < a) (m : ℕ) (i : Fin (m + 3)) :
    preDivisorRiggedPrimeScaledRealBocksteinVector a m i < 0 := by
  exact mul_neg_of_pos_of_neg ha (preDivisorRiggedPrimeRealBocksteinVector_neg m i)

theorem primeScaledBockstein_cubicMass_lower
    {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    ((m + 3).choose 3 : ℝ) * (a / 3) ^ 3 ≤
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 3,
        -(∏ i ∈ s, preDivisorRiggedPrimeScaledRealBocksteinVector a m i) := by
  classical
  let C := (Finset.univ : Finset (Fin (m + 3))).powersetCard 3
  have hlocal : ∀ s ∈ C, (a / 3) ^ 3 ≤
      -(∏ i ∈ s, preDivisorRiggedPrimeScaledRealBocksteinVector a m i) := by
    intro s hs
    have hcard : s.card = 3 := (Finset.mem_powersetCard.mp hs).2
    have hprod : (a / 3) ^ 3 ≤
        ∏ i ∈ s, -preDivisorRiggedPrimeScaledRealBocksteinVector a m i := by
      calc
        (a / 3) ^ 3 = ∏ _i ∈ s, (a / 3) := by
          simp [hcard]
          ring
        _ ≤ ∏ i ∈ s, -preDivisorRiggedPrimeScaledRealBocksteinVector a m i := by
          refine Finset.prod_le_prod ?_ ?_
          · intro i hi
            positivity
          · intro i hi
            rw [preDivisorRiggedPrimeScaledRealBocksteinVector,
              preDivisorRiggedPrimeRealBocksteinVector,
              primeGammaCofinalBocksteinCoefficient_one_eq_neg_weight]
            have hw := primeGammaBocksteinUnitWeight_ge_one_third (nthPrimePoint i)
            nlinarith
    calc
      (a / 3) ^ 3 ≤
          ∏ i ∈ s, -preDivisorRiggedPrimeScaledRealBocksteinVector a m i := hprod
      _ = -(∏ i ∈ s, preDivisorRiggedPrimeScaledRealBocksteinVector a m i) := by
        have hneg := Finset.prod_neg (s := s)
          (preDivisorRiggedPrimeScaledRealBocksteinVector a m)
        rw [hcard] at hneg
        norm_num at hneg
        exact hneg
  have hsum := Finset.sum_le_sum hlocal
  have hcardC : C.card = (m + 3).choose 3 := by simp [C]
  simpa only [Finset.sum_const, nsmul_eq_mul, hcardC] using hsum

theorem primeScaledBockstein_cubicParityDefect_lower_of_nonneg
    {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    4 * ((m + 3).choose 3 : ℝ) * (a / 3) ^ 3 ≤
      unitizedRealReservoirDeterminant
          (preDivisorRiggedPrimeScaledRealBocksteinVector a m) -
        unitizedRealReservoirDeterminant
          (-preDivisorRiggedPrimeScaledRealBocksteinVector a m) := by
  by_cases ha0 : a = 0
  · subst a
    have hz : preDivisorRiggedPrimeScaledRealBocksteinVector 0 m = 0 := by
      funext i
      simp [preDivisorRiggedPrimeScaledRealBocksteinVector]
    rw [hz]
    simp
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hcubic := primeScaledBockstein_cubicMass_lower ha m
    have hgap :=
      four_mul_cubicMass_le_unitizedRealReservoirDeterminant_sub_neg
        (preDivisorRiggedPrimeScaledRealBocksteinVector_neg hapos m)
    nlinarith

theorem primeScaledBockstein_cubicParityDefect_abs_lower
    (a : ℝ) (m : ℕ) :
    4 * ((m + 3).choose 3 : ℝ) * (|a| / 3) ^ 3 ≤
      |unitizedRealReservoirDeterminant
          (preDivisorRiggedPrimeScaledRealBocksteinVector a m) -
        unitizedRealReservoirDeterminant
          (-preDivisorRiggedPrimeScaledRealBocksteinVector a m)| := by
  by_cases ha : 0 ≤ a
  · have hgap := primeScaledBockstein_cubicParityDefect_lower_of_nonneg ha m
    have hnonneg : 0 ≤
        unitizedRealReservoirDeterminant
            (preDivisorRiggedPrimeScaledRealBocksteinVector a m) -
          unitizedRealReservoirDeterminant
            (-preDivisorRiggedPrimeScaledRealBocksteinVector a m) := by
      have hleft : 0 ≤ 4 * ((m + 3).choose 3 : ℝ) * (a / 3) ^ 3 := by
        positivity
      linarith
    rwa [abs_of_nonneg ha, abs_of_nonneg hnonneg]
  · have hneg : a < 0 := lt_of_not_ge ha
    let c := -a
    have hc : 0 ≤ c := by dsimp only [c]; linarith
    have hgap := primeScaledBockstein_cubicParityDefect_lower_of_nonneg hc m
    have hvec : preDivisorRiggedPrimeScaledRealBocksteinVector a m =
        -preDivisorRiggedPrimeScaledRealBocksteinVector c m := by
      funext i
      simp [preDivisorRiggedPrimeScaledRealBocksteinVector, c]
    have hcabs : |a| = c := by simp [abs_of_neg hneg, c]
    rw [hcabs, hvec]
    simpa [abs_sub_comm] using
      (le_trans hgap (le_abs_self
        (unitizedRealReservoirDeterminant
            (preDivisorRiggedPrimeScaledRealBocksteinVector c m) -
          unitizedRealReservoirDeterminant
            (-preDivisorRiggedPrimeScaledRealBocksteinVector c m))))

theorem dimensionCube_le_primeScaledBockstein_cubicParityDefect_abs
    (a : ℝ) (m : ℕ) :
    (2 / 81 : ℝ) * (((m + 1 : ℕ) : ℝ) * |a|) ^ 3 ≤
      |unitizedRealReservoirDeterminant
          (preDivisorRiggedPrimeScaledRealBocksteinVector a m) -
        unitizedRealReservoirDeterminant
          (-preDivisorRiggedPrimeScaledRealBocksteinVector a m)| := by
  have hlower := primeScaledBockstein_cubicParityDefect_abs_lower a m
  have hchoose : (6 : ℝ) * ((m + 3).choose 3 : ℝ) =
      ((m + 3 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast six_mul_choose_three_add_three m
  have hprod : (((m + 1 : ℕ) : ℝ) ^ 3) ≤
      ((m + 3 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
    have h1 : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m + 1 ≤ m + 2)
    have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((m + 3 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m + 1 ≤ m + 3)
    have h0 : 0 ≤ ((m + 1 : ℕ) : ℝ) := by positivity
    calc
      (((m + 1 : ℕ) : ℝ) ^ 3) =
          ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by ring
      _ ≤ ((m + 3 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
        gcongr
  have ha3 : 0 ≤ |a| ^ 3 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hprod ha3
  have hsource :
      (2 / 81 : ℝ) * (((m + 1 : ℕ) : ℝ) * |a|) ^ 3 ≤
        4 * ((m + 3).choose 3 : ℝ) * (|a| / 3) ^ 3 := by
    calc
      (2 / 81 : ℝ) * (((m + 1 : ℕ) : ℝ) * |a|) ^ 3 =
          (2 / 81 : ℝ) * (((m + 1 : ℕ) : ℝ) ^ 3 * |a| ^ 3) := by
            rw [mul_pow]
      _ ≤ (2 / 81 : ℝ) *
          (((m + 3 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
            ((m + 1 : ℕ) : ℝ) * |a| ^ 3) := by
            gcongr
      _ = 4 * ((m + 3).choose 3 : ℝ) * (|a| / 3) ^ 3 := by
            rw [← hchoose]
            ring
  exact hsource.trans hlower

theorem preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_gap_re
    (a : ℕ → ℝ) (m : ℕ) :
    (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m 1 -
      preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m (-1)).re =
      unitizedRealReservoirDeterminant
          (preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m) -
        unitizedRealReservoirDeterminant
          (-preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m) := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num]
  rw [preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_ofReal]
  have hminus :
      preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m (-(1 : ℂ)) =
        (unitizedRealReservoirDeterminant
          (fun i : Fin (m + 3) =>
            a m * primeGammaCofinalBocksteinCoefficient (-1) (nthPrimePoint i)) : ℂ) := by
    convert preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_ofReal
      a m (-1) using 1
    all_goals norm_num
  rw [show (-((1 : ℝ) : ℂ)) = -(1 : ℂ) by norm_num]
  rw [hminus]
  have hneg : (fun i : Fin (m + 3) =>
      a m * primeGammaCofinalBocksteinCoefficient (-1) (nthPrimePoint i)) =
      -preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m := by
    funext i
    rw [primeGammaCofinalBocksteinCoefficient_neg]
    simp [preDivisorRiggedPrimeScaledRealBocksteinVector,
      preDivisorRiggedPrimeRealBocksteinVector]
  rw [hneg]
  rfl

theorem tendsto_dimension_mul_abs_scale_zero_of_cubicParityDefect
    (a : ℕ → ℝ)
    (hgap : Tendsto (fun m : ℕ =>
      |unitizedRealReservoirDeterminant
          (preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m) -
        unitizedRealReservoirDeterminant
          (-preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m)|)
      atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => ((m + 3 : ℕ) : ℝ) * |a m|)
      atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ) * |a m|
  let gap : ℕ → ℝ := fun m =>
    |unitizedRealReservoirDeterminant
        (preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m) -
      unitizedRealReservoirDeterminant
        (-preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m)|
  have hx0 : ∀ m, 0 ≤ x m := fun m => by positivity
  have hx3le : ∀ m, x m ^ 3 ≤ (81 / 2 : ℝ) * gap m := by
    intro m
    have h := dimensionCube_le_primeScaledBockstein_cubicParityDefect_abs (a m) m
    dsimp only [x, gap]
    nlinarith
  have hmajor : Tendsto (fun m => (81 / 2 : ℝ) * gap m) atTop (𝓝 0) := by
    simpa only [mul_zero] using hgap.const_mul (81 / 2 : ℝ)
  have hx3 : Tendsto (fun m => x m ^ 3) atTop (𝓝 0) :=
    squeeze_zero (fun m => pow_nonneg (hx0 m) 3) hx3le hmajor
  have hx : Tendsto x atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb
      filter_upwards [] with m
      exact hb.trans_le (hx0 m)
    · intro b hb
      have hb3 : 0 < b ^ 3 := pow_pos hb 3
      have hevent : ∀ᶠ m : ℕ in atTop, x m ^ 3 < b ^ 3 :=
        (tendsto_order.1 hx3).2 (b ^ 3) hb3
      filter_upwards [hevent] with m hm
      by_contra hnot
      have hbx : b ≤ x m := le_of_not_gt hnot
      have hpow : b ^ 3 ≤ x m ^ 3 :=
        pow_le_pow_left₀ hb.le hbx 3
      linarith
  have hbound : ∀ m : ℕ,
      ((m + 3 : ℕ) : ℝ) * |a m| ≤ 3 * x m := by
    intro m
    have hnat : m + 3 ≤ 3 * (m + 1) := by omega
    have hreal : ((m + 3 : ℕ) : ℝ) ≤ 3 * ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    dsimp only [x]
    nlinarith [abs_nonneg (a m)]
  have hthree : Tendsto (fun m => 3 * x m) atTop (𝓝 0) := by
    simpa only [mul_zero] using hx.const_mul 3
  exact squeeze_zero (fun m => by positivity) hbound hthree

def complexReservoirOnesMatrix {ι : Type*} : Matrix ι ι ℂ := fun _ _ => 1

def complexReservoirBaseMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ :=
  (1 : Matrix ι ι ℂ) - complexReservoirOnesMatrix

def complexReservoirDiagonalMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) : Matrix ι ι ℂ :=
  complexReservoirBaseMatrix * Matrix.diagonal b

theorem complexReservoirBaseMatrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (complexReservoirBaseMatrix : Matrix ι ι ℂ).det =
      1 - (Fintype.card ι : ℂ) := by
  let c : Matrix ι (Fin 1) ℂ := fun _ _ => 1
  let r : Matrix (Fin 1) ι ℂ := fun _ _ => 1
  have hbase : (complexReservoirBaseMatrix : Matrix ι ι ℂ) = 1 - c * r := by
    ext i j
    simp [complexReservoirBaseMatrix, complexReservoirOnesMatrix,
      c, r, Matrix.mul_apply]
  rw [hbase, Matrix.det_one_sub_mul_comm]
  have hsmall :
      (1 - r * c : Matrix (Fin 1) (Fin 1) ℂ) =
        !![(1 - (Fintype.card ι : ℂ))] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [c, r, Matrix.mul_apply]
  rw [hsmall]
  simp

theorem complexReservoirDiagonalMatrix_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (i j : ι) :
    complexReservoirDiagonalMatrix b i j = complexReservoirBaseMatrix i j * b j := by
  rw [complexReservoirDiagonalMatrix, Matrix.mul_diagonal]

theorem complexReservoirDiagonalMatrix_submatrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) (s : Finset ι) :
    ((complexReservoirDiagonalMatrix b).submatrix
      (Subtype.val : s → ι) (Subtype.val : s → ι)).det =
      (1 - (s.card : ℂ)) * ∏ i : s, b i := by
  have hsub :
      (complexReservoirDiagonalMatrix b).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι) =
        (complexReservoirBaseMatrix : Matrix s s ℂ) *
          Matrix.diagonal (fun i : s => b i) := by
    ext i j
    rw [Matrix.submatrix_apply, complexReservoirDiagonalMatrix_apply,
      Matrix.mul_diagonal]
    simp [complexReservoirBaseMatrix, complexReservoirOnesMatrix,
      Matrix.one_apply]
  rw [hsub, Matrix.det_mul, complexReservoirBaseMatrix_det,
    Matrix.det_diagonal, Fintype.card_coe]

def unitizedComplexReservoirDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) : ℂ :=
  (1 + complexReservoirDiagonalMatrix b).det

theorem unitizedComplexReservoirDeterminant_eq_sum_powerset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℂ) :
    unitizedComplexReservoirDeterminant b =
      ∑ s ∈ (Finset.univ : Finset ι).powerset,
        (1 - (s.card : ℂ)) * ∏ i ∈ s, b i := by
  classical
  let P : Polynomial ℂ :=
    (1 + (Polynomial.X : Polynomial ℂ) •
      (complexReservoirDiagonalMatrix b).map Polynomial.C).det
  have hP : P =
      ∑ s ∈ (Finset.univ : Finset ι).powerset,
        Polynomial.monomial s.card
          ((1 - (s.card : ℂ)) * ∏ i ∈ s, b i) := by
    ext k
    rw [show P.coeff k =
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
          ((complexReservoirDiagonalMatrix b).submatrix
            (Subtype.val : s → ι) (Subtype.val : s → ι)).det by
      exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors
        (complexReservoirDiagonalMatrix b) k]
    simp_rw [complexReservoirDiagonalMatrix_submatrix_det]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.prod_coe_sort]
  have heval := congrArg (Polynomial.eval 1) hP
  have hevalDet : Polynomial.eval 1 P =
      unitizedComplexReservoirDeterminant b := by
    change Polynomial.eval 1
        ((1 + (Polynomial.X : Polynomial ℂ) •
          (complexReservoirDiagonalMatrix b).map Polynomial.C).det) = _
    have hmap := RingHom.map_det (Polynomial.evalRingHom (1 : ℂ))
      (1 + (Polynomial.X : Polynomial ℂ) •
        (complexReservoirDiagonalMatrix b).map Polynomial.C)
    simp only [Polynomial.coe_evalRingHom] at hmap
    rw [hmap]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply]
    simp only [map_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hevalDet] at heval
  simpa [Polynomial.eval_finsetSum] using heval

theorem preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_eq_complexReservoir
    (a : ℕ → ℝ) (m : ℕ) (z : ℂ) :
    preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m z =
      unitizedComplexReservoirDeterminant
        (fun i : Fin (m + 3) =>
          (a m : ℂ) * preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)) := by
  rw [preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant,
    unitizedComplexReservoirDeterminant]
  have hmat : (a m : ℂ) •
      preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) z =
    complexReservoirDiagonalMatrix
      (fun i : Fin (m + 3) =>
        (a m : ℂ) * preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)) := by
    ext i j
    rw [Matrix.smul_apply, preDivisorRiggedPrimeHolomorphicReservoirMatrix,
      Matrix.mul_diagonal, complexReservoirDiagonalMatrix_apply]
    by_cases hij : i = j
    · subst j
      simp [holomorphicReservoirBaseMatrix, holomorphicReservoirColumn,
        holomorphicReservoirRow, complexReservoirBaseMatrix,
        complexReservoirOnesMatrix, Matrix.mul_apply]
    · simp [holomorphicReservoirBaseMatrix, holomorphicReservoirColumn,
        holomorphicReservoirRow, complexReservoirBaseMatrix,
        complexReservoirOnesMatrix, Matrix.mul_apply, hij]
  rw [hmat]

theorem iteratedDeriv_one_preDivisorHolomorphicPrimeBockstein_zero
    (p : Nat.Primes) :
    iteratedDeriv 1 (fun z => preDivisorHolomorphicPrimeBockstein z p) 0 =
      -2 * (primeActivationOccupancyFisherDensity p : ℂ) *
        (Real.log (p : ℝ) : ℂ) := by
  rw [iteratedDeriv_one]
  let L : ℂ := (Real.log (p : ℝ) : ℂ)
  let c : ℂ := (primeActivationOccupancyFisherDensity p : ℂ)
  have hderiv :=
    ((HurwitzExp.hasDerivAt_expLin (-L) 0).sub
      (HurwitzExp.hasDerivAt_expLin L 0)).const_mul c
  convert hderiv.deriv using 1
  all_goals simp [preDivisorHolomorphicPrimeBockstein, L, c]
  ring

theorem finset_prod_zero_of_nonempty
    {ι : Type*} [DecidableEq ι] (f : ι → ℂ → ℂ)
    (hz : ∀ i, f i 0 = 0) {s : Finset ι} (hs : s.Nonempty) :
    ∏ i ∈ s, f i 0 = 0 := by
  obtain ⟨i, hi⟩ := hs
  exact Finset.prod_eq_zero hi (hz i)

theorem iteratedDeriv_one_finset_prod_zero_of_two_le_card
    {ι : Type*} [DecidableEq ι] (f : ι → ℂ → ℂ) (s : Finset ι)
    (hf : ∀ i, Differentiable ℂ (f i)) (hz : ∀ i, f i 0 = 0)
    (hs : 2 ≤ s.card) :
    iteratedDeriv 1 (fun z => ∏ i ∈ s, f i z) 0 = 0 := by
  rw [iteratedDeriv_one, deriv_fun_finsetProd]
  · apply Finset.sum_eq_zero
    intro i hi
    have herase : (s.erase i).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hi]
      omega)
    rw [finset_prod_zero_of_nonempty f hz herase]
    simp
  · intro i hi
    exact (hf i).differentiableAt

theorem iteratedDeriv_two_finset_prod_zero_of_three_le_card
    {ι : Type*} [DecidableEq ι] (f : ι → ℂ → ℂ) (s : Finset ι)
    (hf : ∀ i, Differentiable ℂ (f i)) (hz : ∀ i, f i 0 = 0)
    (hs : 3 ≤ s.card) :
    iteratedDeriv 2 (fun z => ∏ i ∈ s, f i z) 0 = 0 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  have heraseTwo : 2 ≤ (s.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    omega
  have heraseNonempty : (s.erase i).Nonempty := Finset.card_pos.mp (by omega)
  have hfun : (fun z => ∏ j ∈ s, f j z) =
      fun z => f i z * ∏ j ∈ s.erase i, f j z := by
    funext z
    exact (Finset.mul_prod_erase s (fun j => f j z) hi).symm
  rw [hfun]
  change iteratedDeriv 2 ((f i) * (fun z => ∏ j ∈ s.erase i, f j z)) 0 = 0
  rw [iteratedDeriv_mul
    (hf i).contDiff.contDiffAt
    ((Differentiable.fun_finsetProd fun j _ => hf j).contDiff.contDiffAt)]
  have hzero := finset_prod_zero_of_nonempty f hz heraseNonempty
  have hone := iteratedDeriv_one_finset_prod_zero_of_two_le_card f (s.erase i) hf hz heraseTwo
  norm_num [Finset.sum_range_succ, hz i, hzero, hone]

theorem iteratedDeriv_two_finset_prod_eq_of_card_eq_two
    {ι : Type*} [DecidableEq ι] (f : ι → ℂ → ℂ) (s : Finset ι)
    (hf : ∀ i, Differentiable ℂ (f i)) (hz : ∀ i, f i 0 = 0)
    (hs : s.card = 2) :
    iteratedDeriv 2 (fun z => ∏ i ∈ s, f i z) 0 =
      2 * ∏ i ∈ s, iteratedDeriv 1 (f i) 0 := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hs
  have hfun : (fun z => ∏ k ∈ ({i, j} : Finset ι), f k z) =
      fun z => f i z * f j z := by
    funext z
    simp [hij]
  rw [hfun]
  change iteratedDeriv 2 ((f i) * (f j)) 0 = _
  rw [iteratedDeriv_mul
    (hf i).contDiff.contDiffAt (hf j).contDiff.contDiffAt]
  norm_num [Finset.sum_range_succ, hz i, hz j, hij]
  ring

/-- Positive magnitude of the first central jet of one signed prime Bockstein. -/
def preDivisorHolomorphicPrimeNeutralJet (p : Nat.Primes) : ℝ :=
  2 * primeActivationOccupancyFisherDensity p * Real.log (p : ℝ)

theorem preDivisorHolomorphicPrimeBockstein_zero (p : Nat.Primes) :
    preDivisorHolomorphicPrimeBockstein 0 p = 0 := by
  simp [preDivisorHolomorphicPrimeBockstein]

theorem iteratedDeriv_one_scaled_preDivisorHolomorphicPrimeBockstein_zero
    (a : ℝ) (p : Nat.Primes) :
    iteratedDeriv 1
        (fun z => (a : ℂ) * preDivisorHolomorphicPrimeBockstein z p) 0 =
      -(a : ℂ) * (preDivisorHolomorphicPrimeNeutralJet p : ℂ) := by
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_one_preDivisorHolomorphicPrimeBockstein_zero]
  simp only [preDivisorHolomorphicPrimeNeutralJet, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem iteratedDeriv_two_preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant
    (a : ℕ → ℝ) (m : ℕ) :
    iteratedDeriv 2
        (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m) 0 =
      -(2 : ℂ) * (a m : ℂ) ^ 2 *
        ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
  let f : Fin (m + 3) → ℂ → ℂ := fun i z =>
    (a m : ℂ) * preDivisorHolomorphicPrimeBockstein z (nthPrimePoint i)
  have hf : ∀ i, Differentiable ℂ (f i) := by
    intro i
    exact (differentiable_const (a m : ℂ)).mul
      (differentiable_preDivisorHolomorphicPrimeBockstein (nthPrimePoint i))
  have hz : ∀ i, f i 0 = 0 := by
    intro i
    simp [f, preDivisorHolomorphicPrimeBockstein_zero]
  have hone : ∀ i, iteratedDeriv 1 (f i) 0 =
      -(a m : ℂ) *
        (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
    intro i
    exact iteratedDeriv_one_scaled_preDivisorHolomorphicPrimeBockstein_zero
      (a m) (nthPrimePoint i)
  have hfun : preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m =
      fun z => ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powerset,
        (1 - (s.card : ℂ)) * ∏ i ∈ s, f i z := by
    funext z
    rw [preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_eq_complexReservoir,
      unitizedComplexReservoirDeterminant_eq_sum_powerset]
  rw [hfun]
  rw [HurwitzExp.iteratedDeriv_finset_sum]
  · have hterm : ∀ s : Finset (Fin (m + 3)),
        iteratedDeriv 2
            (fun z => (1 - (s.card : ℂ)) * ∏ i ∈ s, f i z) 0 =
          if s.card = 2 then
            -(2 : ℂ) * (a m : ℂ) ^ 2 *
              ∏ i ∈ s,
                (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ)
          else 0 := by
      intro s
      by_cases htwo : s.card = 2
      · rw [if_pos htwo, iteratedDeriv_const_mul_field,
          iteratedDeriv_two_finset_prod_eq_of_card_eq_two f s hf hz htwo]
        have hprod :
            ∏ i ∈ s, iteratedDeriv 1 (f i) 0 =
              (a m : ℂ) ^ 2 *
                ∏ i ∈ s,
                  (preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i) : ℂ) := by
          obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp htwo
          simp [hone, hij]
          ring
        rw [hprod, htwo]
        norm_num
        ring
      · rw [if_neg htwo]
        by_cases hzero : s.card = 0
        · have hs : s = ∅ := Finset.card_eq_zero.mp hzero
          subst s
          simp [iteratedDeriv_const]
        by_cases honecard : s.card = 1
        · rw [iteratedDeriv_const_mul_field, honecard]
          norm_num
        · have hthree : 3 ≤ s.card := by omega
          rw [iteratedDeriv_const_mul_field,
            iteratedDeriv_two_finset_prod_zero_of_three_le_card f s hf hz hthree]
          simp
    simp_rw [hterm]
    rw [Finset.mul_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  · intro s hs
    have hprod : ContDiff ℂ 2 (fun z => ∏ i ∈ s, f i z) :=
      (Differentiable.fun_finsetProd fun i _ => hf i).contDiff
    exact (contDiff_const : ContDiff ℂ 2
      (fun _ : ℂ => (1 - (s.card : ℂ)))).mul hprod

theorem preDivisorHolomorphicPrimeNeutralJet_nonneg (p : Nat.Primes) :
    0 ≤ preDivisorHolomorphicPrimeNeutralJet p := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (primeActivationOccupancyFisherDensity_pos p).le)
    (log_prime_pos p).le

theorem tendsto_preDivisorHolomorphicPrimeNeutralJet_nthPrimePoint_zero :
    Tendsto (fun n => preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint n))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n => 2 * (Real.log ((nthPrimePoint n : Nat.Primes) : ℝ) *
        primeReciprocal (nthPrimePoint n))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      tendsto_log_mul_primeReciprocal_nthPrimePoint_zero
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      preDivisorHolomorphicPrimeNeutralJet_nonneg (nthPrimePoint n)) ?_ hupper
  exact Filter.Eventually.of_forall fun n => by
    calc
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint n) ≤
          2 * (1 / (((nthPrimePoint n : Nat.Primes) : ℕ) : ℝ)) *
            Real.log ((nthPrimePoint n : Nat.Primes) : ℝ) := by
        unfold preDivisorHolomorphicPrimeNeutralJet
        gcongr
        exact primeActivationOccupancyFisherDensity_le_one_div (nthPrimePoint n)
      _ = 2 * (Real.log ((nthPrimePoint n : Nat.Primes) : ℝ) *
          primeReciprocal (nthPrimePoint n)) := by
        rw [primeReciprocal]
        ring

theorem norm_iteratedDeriv_two_scalarUnitizedDeterminant_le
    (a : ℕ → ℝ) (m : ℕ) :
    ‖iteratedDeriv 2
        (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m) 0‖ ≤
      (|a m| * ∑ i : Fin (m + 3),
        preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) ^ 2 := by
  let q : Fin (m + 3) → ℝ := fun i =>
    preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)
  have hq : ∀ i, 0 ≤ q i := fun i =>
    preDivisorHolomorphicPrimeNeutralJet_nonneg (nthPrimePoint i)
  have hpair :=
    GaloisForLFunctions.HTGeometry.factorial_mul_sum_powersetCard_le_sum_pow
      hq (Finset.univ : Finset (Fin (m + 3))) 2
  norm_num at hpair
  have hpairsNonneg : 0 ≤
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
        ∏ i ∈ s, q i := by
    exact Finset.sum_nonneg fun s hs =>
      Finset.prod_nonneg fun i hi => hq i
  have hcast :
      (∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, (q i : ℂ)) =
        ((∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, q i : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [iteratedDeriv_two_preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant]
  change ‖-(2 : ℂ) * (a m : ℂ) ^ 2 *
      ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
        ∏ i ∈ s, (q i : ℂ)‖ ≤ _
  rw [hcast]
  calc
    ‖-(2 : ℂ) * (a m : ℂ) ^ 2 *
        ((∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
          ∏ i ∈ s, q i : ℝ) : ℂ)‖ =
        |a m| ^ 2 *
          (2 * ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
            ∏ i ∈ s, q i) := by
      have hnormPairs :
          ‖((∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
            ∏ i ∈ s, q i : ℝ) : ℂ)‖ =
            ∑ s ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard 2,
              ∏ i ∈ s, q i := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpairsNonneg]
      rw [norm_mul, norm_mul, norm_neg, norm_ofNat, norm_pow, hnormPairs,
        Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ |a m| ^ 2 * (∑ i : Fin (m + 3), q i) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hpair (sq_nonneg _)
    _ = (|a m| * ∑ i : Fin (m + 3),
        preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) ^ 2 := by
      ring

theorem tendsto_abs_scale_mul_neutralJet_packetSum_zero
    (a : ℕ → ℝ)
    (hscale : Tendsto (fun m => ((m + 3 : ℕ) : ℝ) * |a m|) atTop (𝓝 0)) :
    Tendsto (fun m => |a m| * ∑ i : Fin (m + 3),
      preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun m : ℕ => m + 3) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hcesaro := tendsto_preDivisorHolomorphicPrimeNeutralJet_nthPrimePoint_zero.cesaro
  have hcesaroShift := hcesaro.comp hshift
  have hproduct : Tendsto
      (fun m => (((m + 3 : ℕ) : ℝ) * |a m|) *
        ((((m + 3 : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.range (m + 3),
          preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)))
      atTop (𝓝 0) := by
    simpa using hscale.mul hcesaroShift
  refine hproduct.congr' ?_
  filter_upwards with m
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => preDivisorHolomorphicPrimeNeutralJet (nthPrimePoint i)) (m + 3)]
  have hmne : (((m + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem tendsto_iteratedDeriv_two_scalarUnitizedDeterminant_zero
    (a : ℕ → ℝ)
    (hscale : Tendsto (fun m => ((m + 3 : ℕ) : ℝ) * |a m|) atTop (𝓝 0)) :
    Tendsto (fun m => iteratedDeriv 2
      (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m) 0)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero
    (fun m => norm_nonneg _)
    (norm_iteratedDeriv_two_scalarUnitizedDeterminant_le a)
    (by simpa using
      (tendsto_abs_scale_mul_neutralJet_packetSum_zero a hscale).pow 2)

/-- **Cofinal real-scalar unitization dichotomy.** No real scale sequence can make the complete
coefficient-faithful holomorphic SC reservoir converge compact-open to normalized centered Xi.
If the scale does not collapse at packet rate, the cubic odd exterior layer survives at `z = ±1`;
if it does collapse, every quadratic central jet vanishes, contradicting Xi curvature. -/
theorem not_tendstoLocallyUniformly_normalizedXiC_of_cofinalRealScalarUnitization
    (a : ℕ → ℝ) :
    ¬ TendstoLocallyUniformly
      (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a)
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hconvOn : TendstoLocallyUniformlyOn
      (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a)
      (fun z => XiC z / XiC 0) atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have hplus := hconvOn.tendsto_at (Set.mem_univ (1 : ℂ))
  have hminus := hconvOn.tendsto_at (Set.mem_univ (-1 : ℂ))
  have hgapComplex := hplus.sub hminus
  have htarget :
      XiC (1 : ℂ) / XiC 0 - XiC (-1 : ℂ) / XiC 0 = 0 := by
    rw [show (-1 : ℂ) = -(1 : ℂ) by norm_num, XiC_even]
    ring
  have hgapReal : Tendsto
      (fun m =>
        (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m 1 -
          preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m (-1)).re)
      atTop (𝓝 0) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hgapComplex
    have hre' : Tendsto
        (fun m =>
          (preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m 1 -
            preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m (-1)).re)
        atTop
        (𝓝 ((XiC (1 : ℂ) / XiC 0 - XiC (-1 : ℂ) / XiC 0).re)) :=
      hre.congr' (Filter.Eventually.of_forall fun _ => rfl)
    simpa only [htarget, Complex.zero_re] using hre'
  have hgapAbsRe : Tendsto
      (fun m =>
        |(preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m 1 -
          preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m (-1)).re|)
      atTop (𝓝 0) := by
    convert continuous_abs.continuousAt.tendsto.comp hgapReal using 1 <;>
      simp [Function.comp_def, Complex.sub_re]
  have hgapAbs : Tendsto (fun m : ℕ =>
      |unitizedRealReservoirDeterminant
          (preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m) -
        unitizedRealReservoirDeterminant
          (-preDivisorRiggedPrimeScaledRealBocksteinVector (a m) m)|)
      atTop (𝓝 0) := by
    refine hgapAbsRe.congr' (Filter.Eventually.of_forall fun m => ?_)
    rw [preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant_gap_re]
  have hscale := tendsto_dimension_mul_abs_scale_zero_of_cubicParityDefect a hgapAbs
  have hjetZero := tendsto_iteratedDeriv_two_scalarUnitizedDeterminant_zero a hscale
  have hjetTarget := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_univ hconvOn
    (Filter.Eventually.of_forall fun m =>
      (differentiable_preDivisorRiggedPrimeHolomorphicScalarUnitizedDeterminant a m).differentiableOn)
    2 (Set.mem_univ 0)
  have hcurvatureZero :
      iteratedDeriv 2 (fun z => XiC z / XiC 0) 0 = 0 :=
    tendsto_nhds_unique hjetTarget hjetZero
  rw [iteratedDeriv_XiC_normalized_two] at hcurvatureZero
  have hre := congrArg Complex.re hcurvatureZero
  have hpos : 0 < thetaCuspNormalizedEvenMoment 1 := by
    rw [thetaCuspNormalizedEvenMoment]
    exact div_pos (thetaCuspRawEvenMoment_pos 1) thetaCuspRawEvenMoment_zero_pos
  norm_num at hre
  linarith

end
end RHTower
