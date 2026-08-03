import GaloisForLFunctions.HTGeometry.GammaWeierstrassCanonicalProduct
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.RationalPowerHypertranscendenceTransfer

/-!
# The exponent-one canonical product is hypertranscendental

`W_1` differs from the entire reciprocal Gamma function `z ↦ Γ(z+1)⁻¹` only by the differentially
algebraic gauge `e^{γ z}`.  Since a single reciprocal Gamma factor carries a nonzero orbit charge,
its meromorphic realization is hypertranscendental over `ℂ(X)`; hence so is `W_1`.

Combined with the rational transfer, every canonical product `W_{1/q}` with zeros `-n^{1/q}` is
hypertranscendental.
-/

namespace HTGeometry

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher Filter Set Topology

noncomputable section

local instance onePowerDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance onePowerRatFuncAlgebra : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance onePowerDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance onePowerRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance onePowerDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance onePowerCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective

/-- The Euler–Mascheroni gauge is entire. -/
theorem analyticOnNhd_eulerGauge :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z))
      Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  fun_prop

/-- Entirety of `z ↦ Γ(z+1)⁻¹`. -/
theorem analyticOnNhd_reciprocalGammaShift :
    AnalyticOnNhd ℂ (fun z : ℂ => reciprocalGammaEntire (z + 1)) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp
    (differentiable_id.add (differentiable_const 1))

/-- Removing the Euler–Mascheroni gauge from `W_1` leaves the entire reciprocal Gamma. -/
theorem eulerGauge_mul_powerCanonicalProduct_one :
    (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * powerCanonicalProduct 1 z)
      = fun z : ℂ => reciprocalGammaEntire (z + 1) := by
  funext z
  rw [powerCanonicalProduct_one_eq z, reciprocalGammaEntire, ← mul_assoc, ← Complex.exp_add]
  simp

/-- The meromorphic realization of `z ↦ Γ(z+1)⁻¹` is the reciprocal Gamma germ. -/
theorem analyticMeroElement_reciprocalGammaShift :
    analyticMeroElement (fun z : ℂ => reciprocalGammaEntire (z + 1))
        analyticOnNhd_reciprocalGammaShift
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
          (reciprocalGammaShiftAnalytic 1) := by
  rw [analyticMeroElement]
  congr 1

/-- The one-factor orbit product with charge `-1` is the reciprocal Gamma germ. -/
theorem gammaOrbitProductMero_single_neg_one :
    gammaOrbitProductMero (fun _ : Fin 1 => (1 : ℂ)) (fun _ => (-1 : ℤ))
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
          (reciprocalGammaShiftAnalytic 1) := by
  rw [gammaOrbitProductMero, Fin.prod_univ_one, gammaShiftMero, zpow_neg, zpow_one, inv_inv]

/-- **The exponent-one canonical product is hypertranscendental.** -/
theorem hypertranscendental_powerCanonicalProduct_one :
    Hypertranscendental (powerCanonicalProduct 1) := by
  intro hDA
  have hW : AnalyticOnNhd ℂ (powerCanonicalProduct 1) Set.univ :=
    analyticOnNhd_powerCanonicalProduct one_pos
  have hEDA : DifferentiallyAlgebraic
      (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)) :=
    differentiallyAlgebraic_cexp_linear _
  have hmul : DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement
        (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * powerCanonicalProduct 1 z)
        (analyticOnNhd_eulerGauge.mul hW)) := by
    rw [analyticMeroElement_mul analyticOnNhd_eulerGauge hW]
    exact differentialAlgebraicOver_mul
      (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
        analyticOnNhd_eulerGauge hEDA)
      (differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic hW hDA)
  have hgerm : analyticMeroElement
      (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
        * powerCanonicalProduct 1 z)
      (analyticOnNhd_eulerGauge.mul hW)
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
          (reciprocalGammaShiftAnalytic 1) := by
    rw [analyticMeroElement]
    congr 1
    apply Subtype.ext
    change Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ))
        (fun z : ℂ => Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * powerCanonicalProduct 1 z)
      = Germ.ofFun (l := 𝓟 (Set.univ : Set ℂ))
        (fun z : ℂ => reciprocalGammaEntire (z + 1))
    rw [eulerGauge_mul_powerCanonicalProduct_one]
  rw [hgerm, ← gammaOrbitProductMero_single_neg_one] at hmul
  have hHT := hypertranscendentalOver_gammaOrbitProductMero
    (fun _ : Fin 1 => (1 : ℂ)) (fun _ => (-1 : ℤ)) 0 (by decide)
    (fun c hc => absurd (Subsingleton.elim c 0) hc)
  exact hHT hmul

/-- **Dense rational hypertranscendence stratum.**  Every canonical product with zeros `-n^{1/q}`
is hypertranscendental. -/
theorem hypertranscendental_powerCanonicalProduct_inv_nat {q : ℕ} (hq : 0 < q) :
    Hypertranscendental (powerCanonicalProduct ((1 : ℝ) / (q : ℝ))) := by
  have h := hypertranscendental_powerCanonicalProduct_ratio (p := 1) (q := q) one_pos hq
    (by simpa using hypertranscendental_powerCanonicalProduct_one)
  simpa using h

end

end HTGeometry
