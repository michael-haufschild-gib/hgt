import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateIsTheZeroFreeRegion
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateOfTheCuspEnergy
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.RHTower.ZetaDivPowRepresentative
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator

/-!
# The optimal horocycle exponent and Euler differential annihilators

Let `Θ = zetaZeroAbscissa` and `Θ_∞ = zetaAsymptoticAbscissa` (`1/2 ≤ Θ_∞ ≤ Θ ≤ 1`).
For smooth compactly supported profiles `φ` with `tsupport φ ⊆ (1, ∞)` and closed horocycle means
`A_φ(y) = horocycleMean (pseudoEisenstein φ) y` on `SL₂(ℤ)\ℍ`:

1. **Unconditional optimal horocycle exponent (`1 − Θ/2`):**
   * `horocycle_rate_zetaZeroAbscissa`: every pseudo-Eisenstein horocycle mean equidistributes at
     rate `O(y^{1 − Θ/2 − ε})` as `y → 0⁺` for every `ε ∈ (0, 1)`.
   * `cusp_energy_rate_zetaZeroAbscissa`: every cusp-form horocycle energy slice equidistributes
     at rate `O(y^{1 − Θ/2 − ε})` as `y → 0⁺` for every `ε ∈ (0, 1/2)`.
   * `not_horocycle_rate_gt_one_sub_half_zetaZeroAbscissa` and `sSup_universalHorocycleExponents`:
     no exponent strictly exceeding `1 − Θ/2` holds across all admissible bumps, so the supremum
     of universal horocycle equidistribution exponents is `1 − Θ/2`.

2. **Euler-polynomial-filtered horocycle exponent (`1 − Θ_∞/2`):**
   For a real polynomial `P ∈ ℝ[X]`, let `eulerPolyR P φ = P(y d/dy) φ`, whose Mellin transform at
   `−s` is `P(s) 𝓜φ(−s)`.
   * `re_le_or_eval_eq_zero_of_eulerPoly_horocycle_rate`: if `A_{eulerPolyR P φ}` has rate `O(y^α)`
     for every admissible `φ`, then every zero `ρ` of `ζ` with `Re ρ > 0` either satisfies
     `Re ρ ≤ 2 − 2α` or is annihilated at `s = ρ/2` by `P`.
   * `not_eulerPoly_horocycle_rate_gt_three_quarters`: Hardy's infinitely many critical-line zeros
     unconditionally block any nonzero Euler polynomial from reaching an exponent `α > 3/4`.
   * `zetaAsymptoticAbscissa_le_of_eulerPoly_horocycle_rate` and
     `exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa`: a nonzero `P ∈ ℝ[X]`
     achieves universal horocycle rate `O(y^α)` on `{eulerPolyR P φ}` for every `α < 1 − Θ_∞/2`
     (by killing the finitely many `ξ(2s)` zeros right of `θ₀/2` via real conjugate-pair factors
     and shifting the Mellin contour past the removable singularities of `Q(s) P(s)` using the
     high-ordinate subpolynomial reciprocal-zeta bound), and never for `α > 1 − Θ_∞/2`.
   * `sSup_eulerFilteredHorocycleExponents`: the supremum of Euler-filtered horocycle exponents is
     `1 − Θ_∞/2`.

3. **Horocycle characterizations of `ZerosApproachLine` and `AsymptoticAbscissaLaw`:**
   * `zerosApproachLine_iff_eulerPoly_horocycle_rate`: `ZerosApproachLine` holds iff for every
     `ε > 0` some nonzero `P ∈ ℝ[X]` accelerates horocycle equidistribution to `O(y^{3/4 − ε})`.
   * `asymptoticAbscissaLaw_iff_no_eulerPoly_horocycle_acceleration`: `AsymptoticAbscissaLaw` holds
     iff no nonzero Euler differential operator accelerates universal horocycle equidistribution
     strictly past the unfiltered optimum `1 − Θ/2`.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology Complex
open scoped ContDiff ComplexConjugate

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower _root_.RHTower.BacklundConverse
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.TestFunctionPerron
open GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ## 1. Unconditional horocycle rates from the exact zero abscissa `Θ` -/

/-- `ξ` has no zeros strictly right of `Θ = zetaZeroAbscissa`. -/
theorem xi_ne_zero_of_zetaZeroAbscissa_lt {z : ℂ} (hz : zetaZeroAbscissa < z.re) :
    xi z ≠ 0 := fun h0 =>
  riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz
    (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp h0).1

/-- Polynomial vertical growth of `1/ζ` on closed strips strictly right of `Θ = zetaZeroAbscissa`. -/
theorem inv_zeta_poly_bound_of_zetaZeroAbscissa :
    ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
      ∀ z : ℂ, zetaZeroAbscissa + δ ≤ z.re → z.re ≤ d → 2 ≤ |z.im| →
        ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
  intro δ hδ d
  obtain ⟨Kb, hKb, -, hbd⟩ := exists_invZeta_shift_data_of_zeroFree
    half_le_zetaZeroAbscissa zetaZeroAbscissa_le_one
    (fun z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz)
    (δ := min δ (1 / 2)) (lt_min hδ (by norm_num))
    (by linarith [min_le_right δ (1 / 2)]) one_pos d
  refine ⟨2 * Kb, 1, by positivity, fun z hz1 hz2 hzt => ?_⟩
  have hmem : z ∈ GaloisForLFunctions.HTGeometry.verticalStrip
      (zetaZeroAbscissa + min δ (1 / 2)) d :=
    ⟨by linarith [min_le_left δ (1 / 2)], hz2⟩
  have hz1' : z ≠ 1 := fun h => by rw [h] at hzt; simp at hzt; linarith
  have h := hbd z hmem
  rw [Sieve.invZeta_eq_inv hz1', Real.rpow_one] at h
  calc ‖(riemannZeta z)⁻¹‖ ≤ Kb * (2 + |z.im|) := h
    _ ≤ Kb * (2 * |z.im|) := by gcongr; linarith
    _ = 2 * Kb * |z.im| ^ 1 := by ring

/-- **Unconditional horocycle rate at the exact zero abscissa `Θ`:** every smooth compactly
supported pseudo-Eisenstein series above height `1` equidistributes at rate `O(y^{1 − Θ/2 − ε})`. -/
theorem horocycle_rate_zetaZeroAbscissa {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤
          C * y ^ (1 - zetaZeroAbscissa / 2 - ε) := by
  obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
  have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
  have h := norm_horocycleMean_sub_le_of_zeroFree hψ ha (θ := zetaZeroAbscissa)
    zetaZeroAbscissa_pos.le zetaZeroAbscissa_le_one
    (fun _ hz => xi_ne_zero_of_zetaZeroAbscissa_lt hz)
    inv_zeta_poly_bound_of_zetaZeroAbscissa hε hε1
  rwa [residueConst_eq] at h

/-- **Unconditional cusp-energy horocycle rate at the exact zero abscissa `Θ`:** for every Maass
cusp form `g`, the horocycle energy slice converges to `(3/π)‖g‖²` at rate `O(y^{1 − Θ/2 − ε})`. -/
theorem cusp_energy_rate_zetaZeroAbscissa {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}
    (hg : g ∈ HeckeCusp.cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lamE))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      |WeylUpper.slice g y - 3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2| ≤
        C * y ^ (1 - zetaZeroAbscissa / 2 - ε) := by
  obtain ⟨C, hC, h⟩ := CuspHRate.norm_mass_sub_le_of_zeroFree hg hρ0 hρ (θ := zetaZeroAbscissa)
    zetaZeroAbscissa_pos.le zetaZeroAbscissa_le_one
    (fun _ hz => xi_ne_zero_of_zetaZeroAbscissa_lt hz)
    inv_zeta_poly_bound_of_zetaZeroAbscissa hε hε1
  have hγ : (0 : ℝ) < 1 - zetaZeroAbscissa / 2 - ε := by
    linarith [zetaZeroAbscissa_le_one]
  have hc := CuspHRate.rateConst_eq hg hρ0 hρ hγ h
  refine ⟨C, hC, fun y hy hy1 => ?_⟩
  have hy' := h y hy hy1
  rw [hc, CuspHR.mass, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hy'
  exact hy'

/-- Universal horocycle equidistribution rate `O(y^α)` across all smooth compactly supported
profiles in `(1, ∞)`. -/
def UniversalHorocycleRate (α : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
    ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (φ t : ℂ)) y - c‖ ≤ C * y ^ α

/-- The set of exponents `α` at which all admissible pseudo-Eisenstein horocycle means converge. -/
def universalHorocycleExponents : Set ℝ := {α : ℝ | UniversalHorocycleRate α}

/-- No exponent strictly above `1 − Θ/2` holds across all admissible pseudo-Eisenstein profiles. -/
theorem not_horocycle_rate_gt_one_sub_half_zetaZeroAbscissa {α : ℝ}
    (hα : 1 - zetaZeroAbscissa / 2 < α) : ¬ UniversalHorocycleRate α := by
  intro hrate
  have hlt : max (2 - 2 * α) 0 < zetaZeroAbscissa :=
    max_lt (by linarith) zetaZeroAbscissa_pos
  obtain ⟨ρ, hρ, hre⟩ := exists_zetaZero_lt_re hlt
  have hρ0 : 0 < ρ.re := lt_of_le_of_lt (le_max_right _ _) hre
  have hle := re_le_of_horocycle_rate hrate hρ hρ0
  have hgt : 2 - 2 * α < ρ.re := lt_of_le_of_lt (le_max_left _ _) hre
  linarith

theorem universalHorocycleRate_of_lt {α : ℝ} (hα : α < 1 - zetaZeroAbscissa / 2) :
    UniversalHorocycleRate α := by
  intro φ hφ hc hs
  set ε := min ((1 - zetaZeroAbscissa / 2 - α) / 2) (1 / 4)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C, hC, h⟩ := horocycle_rate_zetaZeroAbscissa hφ hc hs hε hε1
  refine ⟨_, C, fun y hy hy1 => (h y hy hy1).trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 ?_) hC
  have := min_le_left ((1 - zetaZeroAbscissa / 2 - α) / 2) (1 / 4)
  linarith

/-- **Exact supremum of unfiltered horocycle equidistribution exponents:** `1 − Θ/2`. -/
theorem sSup_universalHorocycleExponents :
    sSup universalHorocycleExponents = 1 - zetaZeroAbscissa / 2 := by
  have hne : universalHorocycleExponents.Nonempty :=
    ⟨0, universalHorocycleRate_of_lt (by linarith [zetaZeroAbscissa_le_one])⟩
  have hbdd : BddAbove universalHorocycleExponents :=
    ⟨1 - zetaZeroAbscissa / 2, fun α hα =>
      not_lt.mp fun hgt => not_horocycle_rate_gt_one_sub_half_zetaZeroAbscissa hgt hα⟩
  refine le_antisymm (csSup_le hne fun α hα =>
    not_lt.mp fun hgt => not_horocycle_rate_gt_one_sub_half_zetaZeroAbscissa hgt hα) ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hmem : 1 - zetaZeroAbscissa / 2 - ε / 2 ∈ universalHorocycleExponents :=
    universalHorocycleRate_of_lt (by linarith)
  linarith [le_csSup hbdd hmem]

/-! ## 2. Real Euler differential operators and their Mellin multipliers -/

/-- The `k`-th real Euler derivative `(u d/du)^k φ`. -/
def eulerIterR : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, φ => φ
  | k + 1, φ => fun u => u * deriv (eulerIterR k φ) u

/-- Real polynomial in `u d/du`: `eulerPolyR P φ u = ∑_{k=0}^{deg P} P_k ((u d/du)^k φ)(u)`. -/
def eulerPolyR (P : Polynomial ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * eulerIterR k φ u

theorem contDiff_eulerIterR {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∀ k, ContDiff ℝ ∞ (eulerIterR k φ)
  | 0 => hφ
  | k + 1 => contDiff_id.mul (contDiff_infty_iff_deriv.mp (contDiff_eulerIterR hφ k)).2

theorem contDiff_eulerPolyR (P : Polynomial ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (eulerPolyR P φ) := by
  unfold eulerPolyR
  exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_eulerIterR hφ k)

theorem ofReal_eulerIterR {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∀ k u, ((eulerIterR k φ u : ℝ) : ℂ) = eulerIter k (fun t => (φ t : ℂ)) u
  | 0, _ => rfl
  | k + 1, u => by
    have hsm := contDiff_eulerIterR hφ k
    have hd : DifferentiableAt ℝ (eulerIterR k φ) u :=
      (contDiff_infty_iff_deriv.mp hsm).1 u
    have heq : eulerIter k (fun t => (φ t : ℂ)) = fun t => ((eulerIterR k φ t : ℝ) : ℂ) :=
      funext (fun t => (ofReal_eulerIterR hφ k t).symm)
    rw [eulerIterR, eulerIter, heq, Complex.ofReal_mul]
    dsimp only
    rw [hd.hasDerivAt.ofReal_comp.deriv]

theorem ofReal_eulerPolyR (P : Polynomial ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (u : ℝ) :
    ((eulerPolyR P φ u : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        (P.coeff k : ℂ) * eulerIter k (fun t => (φ t : ℂ)) u := by
  unfold eulerPolyR
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ofReal_eulerIterR hφ k u]

theorem isTest_eulerPolyR (P : Polynomial ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b) :
    IsTest (fun t => (eulerPolyR P φ t : ℂ)) a b := by
  refine ⟨hψ.pos, hψ.le, Complex.ofRealCLM.contDiff.comp (contDiff_eulerPolyR P hφ), ?_⟩
  intro u hu
  by_contra hnot
  apply hu
  show ((eulerPolyR P φ u : ℝ) : ℂ) = 0
  rw [ofReal_eulerPolyR P hφ u]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [(isTest_eulerIter hψ k).eq_zero hnot, mul_zero]

theorem hasCompactSupport_and_tsupport_eulerPolyR (P : Polynomial ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 1) :
    HasCompactSupport (eulerPolyR P φ) ∧ tsupport (eulerPolyR P φ) ⊆ Ioi 1 := by
  obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
  have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
  have hψP := isTest_eulerPolyR P hφ hψ
  have hsupp : Function.support (eulerPolyR P φ) ⊆ Icc a b := by
    intro u hu
    by_contra hnot
    exact hu (Complex.ofReal_eq_zero.mp (hψP.eq_zero hnot))
  have htsupp : tsupport (eulerPolyR P φ) ⊆ Icc a b :=
    closure_minimal hsupp isClosed_Icc
  exact ⟨HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp,
    htsupp.trans fun u hu => lt_of_lt_of_le ha hu.1⟩

/-- **Mellin multiplier of `eulerPolyR P φ`:** `𝓜(eulerPolyR P φ)(w) = P_ℂ(−w) 𝓜φ(w)`, hence at
`−s` we obtain `𝓜(eulerPolyR P φ)(−s) = P_ℂ(s) 𝓜φ(−s)`. -/
theorem mellin_eulerPolyR (P : Polynomial ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b) (w : ℂ) :
    mellin (fun t => (eulerPolyR P φ t : ℂ)) w =
      (P.map (algebraMap ℝ ℂ)).eval (-w) * mellin (fun t => (φ t : ℂ)) w := by
  have hψP := isTest_eulerPolyR P hφ hψ
  rw [hψP.mellin_eq w]
  have hint : ∀ k ∈ Finset.range (P.natDegree + 1),
      IntervalIntegrable
        (fun u : ℝ => (P.coeff k : ℂ) * ((u : ℂ) ^ (w - 1) * eulerIter k (fun t => (φ t : ℂ)) u))
        volume a b := by
    intro k _
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hψ.le]
    refine continuousOn_const.mul (ContinuousOn.mul ?_ (isTest_eulerIter hψ k).continuous.continuousOn)
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hψ.pos hu.1
    exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 hu0)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hcongr : ∫ u in a..b, (u : ℂ) ^ (w - 1) * (eulerPolyR P φ u : ℂ) =
      ∫ u in a..b, ∑ k ∈ Finset.range (P.natDegree + 1),
        (P.coeff k : ℂ) * ((u : ℂ) ^ (w - 1) * eulerIter k (fun t => (φ t : ℂ)) u) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [ofReal_eulerPolyR P hφ u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hcongr, intervalIntegral.integral_finsetSum hint]
  have hsum : (∑ k ∈ Finset.range (P.natDegree + 1),
        ∫ u in a..b, (P.coeff k : ℂ) * ((u : ℂ) ^ (w - 1) * eulerIter k (fun t => (φ t : ℂ)) u)) =
      (∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k : ℂ) * (-w) ^ k) *
        mellin (fun t => (φ t : ℂ)) w := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, ← (isTest_eulerIter hψ k).mellin_eq w,
      mellin_eulerIter hψ w k]
    ring
  rw [hsum]
  congr 1
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rfl

theorem mellin_eulerPolyR_neg (P : Polynomial ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b) (s : ℂ) :
    mellin (fun t => (eulerPolyR P φ t : ℂ)) (-s) =
      (P.map (algebraMap ℝ ℂ)).eval s * mellin (fun t => (φ t : ℂ)) (-s) := by
  rw [mellin_eulerPolyR P hφ hψ (-s), neg_neg]

/-! ## 3. Converse theorem and Hardy's 3/4 barrier for Euler-filtered horocycles -/

/-- Universal horocycle rate `O(y^α)` along the image `{eulerPolyR P φ}` of a fixed real Euler
polynomial `P`. -/
def EulerFilteredHorocycleRate (P : Polynomial ℝ) (α : ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
    ∃ c : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖horocycleMean (pseudoEisenstein fun t => (eulerPolyR P φ t : ℂ)) y - c‖ ≤ C * y ^ α

/-- The set of exponents `α` achieved by at least one nonzero real Euler polynomial `P ≠ 0`. -/
def eulerFilteredHorocycleExponents : Set ℝ :=
  {α : ℝ | ∃ P : Polynomial ℝ, P ≠ 0 ∧ EulerFilteredHorocycleRate P α}

private theorem eval_map_real_conj (P : Polynomial ℝ) (z : ℂ) :
    (P.map (algebraMap ℝ ℂ)).eval (conj z) = conj ((P.map (algebraMap ℝ ℂ)).eval z) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
    Polynomial.eval₂_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- **Euler-filtered Zagier converse:** if `eulerPolyR P φ` achieves horocycle rate `O(y^α)` for
all smooth compactly supported `φ` on `(1, ∞)`, then every zero `ρ` of `ζ` with `Re ρ > 0`
either satisfies `Re ρ ≤ 2 − 2α` or satisfies `P_ℂ(ρ/2) = 0`. -/
theorem re_le_or_eval_eq_zero_of_eulerPoly_horocycle_rate {P : Polynomial ℝ} {α : ℝ}
    (hrate : EulerFilteredHorocycleRate P α) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) :
    ρ.re ≤ 2 - 2 * α ∨ (P.map (algebraMap ℝ ℂ)).eval (ρ / 2) = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hlt, hPne⟩ := hcon
  have hρ1 : ρ.re < 1 := by
    by_contra h1
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 h1) hρ
  obtain ⟨ρ', hρ', hre', him', hPne'⟩ :
      ∃ ρ' : ℂ, riemannZeta ρ' = 0 ∧ ρ'.re = ρ.re ∧ 0 < ρ'.im ∧
        (P.map (algebraMap ℝ ℂ)).eval (ρ' / 2) ≠ 0 := by
    rcases lt_trichotomy ρ.im 0 with hi | hi | hi
    · refine ⟨conj ρ, by rw [_root_.riemannZeta_conj, hρ, map_zero], by simp,
        by simp; linarith, ?_⟩
      have hdiv : conj ρ / 2 = conj (ρ / 2) := by rw [map_div₀, map_ofNat]
      rw [hdiv, eval_map_real_conj]
      exact fun h0 => hPne (by simpa using congrArg conj h0)
    · exfalso
      have hreal : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hi])
      exact riemannZeta_ne_zero_of_ofReal_mem_Ioo hρ0 hρ1 (hreal ▸ hρ)
    · exact ⟨ρ, hρ, rfl, hi, hPne⟩
  set s₀ : ℂ := ρ' / 2 with hs₀def
  have hs₀ : s₀ ∈ quarterPlane α := by
    refine ⟨max_lt ?_ ?_, ?_⟩ <;> simp [hs₀def] <;> linarith
  have hA : msA (s₀ - 1 / 2) = 0 := by
    rw [msA, show 1 + 2 * (s₀ - 1 / 2) = ρ' by rw [hs₀def]; ring, reflectedCompletedLambda, hρ',
      mul_zero]
  have hB : msB (s₀ - 1 / 2) ≠ 0 := msB_ne_zero_of_zero (by rw [hre']; exact hρ1) him'
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 1 →
      mellin (fun t => (φ t : ℂ)) (-s₀) = 0 := by
    intro φ hφ hc hs
    obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
    have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
    have hψP := isTest_eulerPolyR P hφ hψ
    obtain ⟨c, C, hr⟩ := hrate φ hφ hc hs
    have hm := msB_mul_mellin_eq_zero_of_rate (a := a) (b := b) hψP.continuous ha
      (fun y hy => hψP.eq_zero_of_le hy.le) (fun y hy => hψP.eq_zero_of_ge hy.le) hr hs₀ hA
    have hm' := (mul_eq_zero.1 hm).resolve_left hB
    rw [mellin_eulerPolyR_neg P hφ hψ s₀] at hm'
    exact (mul_eq_zero.1 hm').resolve_left hPne'
  set f : ℝ → ℂ := fun y => (y : ℂ) ^ (-s₀ - 1) with hf
  have hfint : LocallyIntegrableOn f (Ioi 1) := by
    refine ContinuousOn.locallyIntegrableOn (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    exact ((continuousAt_cpow_const (ofReal_mem_slitPlane.2 hy0)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hae := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfint
    (fun g hg hgc hgs => by
      rw [← hzero g hg hgc hgs, mellin,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) (fun y hy => ?_)]
      · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        simp only [hf, Complex.real_smul, smul_eq_mul]
        ring
      · have : g y = 0 :=
          image_eq_zero_of_notMem_tsupport fun h' =>
            hy (mem_Ioi.2 (lt_trans one_pos (mem_Ioi.1 (hgs h'))))
        simp [this])
  have hnull : volume (Ioi (1 : ℝ)) = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun y hy => ?_) hae
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 (lt_trans one_pos hy).ne'
    simp only [mem_setOf_eq, Classical.not_imp]
    exact ⟨hy, by simp [hf, cpow_eq_zero_iff, hy0]⟩
  rw [Real.volume_Ioi] at hnull
  exact ENNReal.top_ne_zero hnull

private theorem exists_root_im_bound (P : Polynomial ℝ) (hP : P ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ |z.im| → (P.map (algebraMap ℝ ℂ)).eval (z / 2) ≠ 0 := by
  classical
  have hPC : P.map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hP
  set S := (P.map (algebraMap ℝ ℂ)).roots.toFinset
  set M := ∑ w ∈ S, |w.im|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 * M + 2, by positivity, fun z hz h0 => ?_⟩
  have hmem : z / 2 ∈ S := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPC).mpr h0)
  have hle : |(z / 2).im| ≤ M :=
    Finset.single_le_sum (f := fun w : ℂ => |w.im|) (fun _ _ => abs_nonneg _) hmem
  have him : |(z / 2).im| = |z.im| / 2 := by
    have : (z / 2).im = z.im / 2 := by simp
    rw [this, abs_div]
    norm_num
  linarith

/-- **Hardy barrier (`3/4`):** no nonzero real Euler polynomial can accelerate horocycle
equidistribution to `O(y^α)` for `α > 3/4`, because Hardy's theorem supplies infinitely many
critical-line zeros of `ζ` while `P` has only finitely many roots. -/
theorem not_eulerPoly_horocycle_rate_gt_three_quarters {P : Polynomial ℝ} (hP : P ≠ 0) {α : ℝ}
    (hα : 3 / 4 < α) : ¬ EulerFilteredHorocycleRate P α := by
  intro hrate
  obtain ⟨R, hR0, hR⟩ := exists_root_im_bound P hP
  obtain ⟨t, ht, hXi⟩ := exists_Xi_zero_gt R
  have ht0 : 0 < t := lt_trans hR0 ht
  set ρ : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hρne0 : ρ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [ρ] at this
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [completedRiemannZeta_critical_eq_Xi t, hXi]
    simp
  have hζ : riemannZeta ρ = 0 := by
    rw [riemannZeta_def_of_ne_zero hρne0, hΛ, zero_div]
  have hρre : ρ.re = 1 / 2 := by simp [ρ]
  have hρim : ρ.im = t := by simp [ρ]
  have hPne : (P.map (algebraMap ℝ ℂ)).eval (ρ / 2) ≠ 0 :=
    hR ρ (by rw [hρim, abs_of_pos ht0]; exact ht.le)
  rcases re_le_or_eval_eq_zero_of_eulerPoly_horocycle_rate hrate hζ (by linarith) with hle | h0
  · linarith
  · exact hPne h0

/-- **Asymptotic-abscissa converse:** if `P ≠ 0` achieves Euler-filtered horocycle rate `O(y^α)`,
then `Θ_∞ ≤ 2 − 2α` (equivalently `α ≤ 1 − Θ_∞/2`). -/
theorem zetaAsymptoticAbscissa_le_of_eulerPoly_horocycle_rate {P : Polynomial ℝ} (hP : P ≠ 0)
    {α : ℝ} (hrate : EulerFilteredHorocycleRate P α) :
    zetaAsymptoticAbscissa ≤ 2 - 2 * α := by
  have hα34 : α ≤ 3 / 4 :=
    not_lt.mp fun hgt => not_eulerPoly_horocycle_rate_gt_three_quarters hP hgt hrate
  obtain ⟨R, hR0, hR⟩ := exists_root_im_bound P hP
  refine csInf_le bddBelow_zetaAsymptoticAbscissaSet ?_
  rw [mem_zetaAsymptoticAbscissaSet_iff_eventually_height]
  refine ⟨by linarith, R, hR0, fun q hq => ?_⟩
  have hζ := riemannZeta_eq_zero_of_xiZeroCopy q
  have hre0 := (xi_divisor_support_re_mem_open_unit q.1).1
  have hPne := hR (q.1 : ℂ) hq
  exact (re_le_or_eval_eq_zero_of_eulerPoly_horocycle_rate hrate hζ hre0).resolve_right hPne

/-! ## 4. Meromorphic cancellation of finite high-abscissa poles via real Euler polynomials -/

/-- `ξ(2s)` as an entire function of `s`. -/
def xiHalf (s : ℂ) : ℂ := xi (2 * s)

theorem analyticOnNhd_xiHalf : AnalyticOnNhd ℂ xiHalf univ :=
  DifferentiableOn.analyticOnNhd
    (fun s _ => ((xi_differentiable _).comp s (differentiableAt_id.const_mul 2)).differentiableWithinAt)
    isOpen_univ

theorem analyticAt_xiHalf (s : ℂ) : AnalyticAt ℂ xiHalf s :=
  analyticOnNhd_xiHalf s (mem_univ s)

theorem analyticOrderAt_xiHalf_ne_top (s : ℂ) : analyticOrderAt xiHalf s ≠ ⊤ := by
  have h1 : xiHalf 1 ≠ 0 := by
    show xi (2 * 1) ≠ 0
    exact xi_ne_zero_of_one_lt_re (by norm_num)
  have hord1 : analyticOrderAt xiHalf 1 ≠ ⊤ := by
    rw [(analyticAt_xiHalf 1).analyticOrderAt_eq_zero.mpr h1]
    exact ENat.zero_ne_top
  exact analyticOnNhd_xiHalf.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ 1) (mem_univ s) hord1

/-- Vanishing multiplicity of `ξ(2s)` at `s` as a natural number. -/
def xiHalfMult (s : ℂ) : ℕ := (analyticOrderAt xiHalf s).toNat

theorem coe_xiHalfMult (s : ℂ) : ((xiHalfMult s : ℕ) : ℕ∞) = analyticOrderAt xiHalf s :=
  ENat.coe_toNat (analyticOrderAt_xiHalf_ne_top s)

/-- Monic real quadratic polynomial `(X − Re s₀)² + (Im s₀)²` whose complexification factors as
`(z − s₀)(z − conj s₀)`. -/
def realPairQuad (s₀ : ℂ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C s₀.re) ^ 2 + Polynomial.C (s₀.im ^ 2)

theorem monic_realPairQuad (s₀ : ℂ) : (realPairQuad s₀).Monic := by
  have hdeg1 : ((Polynomial.X - Polynomial.C s₀.re : Polynomial ℝ) ^ 2).degree = 2 := by
    rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
    rfl
  have hdeg2 : (Polynomial.C (s₀.im ^ 2) : Polynomial ℝ).degree <
      ((Polynomial.X - Polynomial.C s₀.re : Polynomial ℝ) ^ 2).degree := by
    rw [hdeg1]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by decide)
  exact ((Polynomial.monic_X_sub_C s₀.re).pow 2).add_of_left hdeg2

theorem eval_map_realPairQuad (s₀ z : ℂ) :
    ((realPairQuad s₀).map (algebraMap ℝ ℂ)).eval z = (z - s₀) * (z - conj s₀) := by
  unfold realPairQuad
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Complex.ext <;> simp [pow_two] <;> ring

private theorem analyticAt_eval_poly (P : Polynomial ℝ) (z : ℂ) :
    AnalyticAt ℂ (fun s => (P.map (algebraMap ℝ ℂ)).eval s) z := by
  have heq : (fun s : ℂ => (P.map (algebraMap ℝ ℂ)).eval s) =
      ∑ k ∈ Finset.range (P.natDegree + 1), fun s : ℂ => (P.coeff k : ℂ) * s ^ k := by
    funext s
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, Finset.sum_apply]
    rfl
  rw [heq]
  exact Finset.sum_induction _ (fun g => AnalyticAt ℂ g z) (fun _ _ hf hg => hf.add hg)
    analyticAt_const fun k _ => analyticAt_const.mul (analyticAt_id.pow k)

private theorem eval_finset_prod_poly {ι : Type*} (S : Finset ι) (f : ι → Polynomial ℂ) (z : ℂ) :
    (∏ i ∈ S, f i).eval z = ∏ i ∈ S, (f i).eval z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Polynomial.eval_mul, ih, Finset.prod_insert ha]

/-- Monic real Euler polynomial annihilating every `s₀ ∈ F` to order at least `xiHalfMult s₀`. -/
def halfZeroAnnihilator (F : Finset ℂ) : Polynomial ℝ :=
  ∏ s₀ ∈ F, realPairQuad s₀ ^ xiHalfMult s₀

theorem halfZeroAnnihilator_ne_zero (F : Finset ℂ) : halfZeroAnnihilator F ≠ 0 :=
  (Polynomial.monic_prod_of_monic F _ fun s₀ _ => (monic_realPairQuad s₀).pow _).ne_zero

theorem exists_analytic_factor_halfZeroAnnihilator {F : Finset ℂ} {s : ℂ} (hs : s ∈ F) :
    ∃ H : ℂ → ℂ, (∀ z, AnalyticAt ℂ H z) ∧
      ∀ z : ℂ, ((halfZeroAnnihilator F).map (algebraMap ℝ ℂ)).eval z =
        (z - s) ^ xiHalfMult s * H z := by
  classical
  let H : ℂ → ℂ := fun z => (z - conj s) ^ xiHalfMult s *
    ∏ s₀ ∈ F.erase s, (((realPairQuad s₀).map (algebraMap ℝ ℂ)).eval z) ^ xiHalfMult s₀
  refine ⟨H, fun z => ?_, fun z => ?_⟩
  · refine ((analyticAt_id.sub analyticAt_const).pow _).mul ?_
    have hfn : (fun w : ℂ => ∏ s₀ ∈ F.erase s,
        (((realPairQuad s₀).map (algebraMap ℝ ℂ)).eval w) ^ xiHalfMult s₀) =
      ∏ s₀ ∈ F.erase s, fun w : ℂ =>
        (((realPairQuad s₀).map (algebraMap ℝ ℂ)).eval w) ^ xiHalfMult s₀ := by
      funext w; simp
    rw [hfn]
    exact Finset.prod_induction _ (fun g => AnalyticAt ℂ g z)
      (fun _ _ hf hg => hf.mul hg) analyticAt_const
      fun s₀ _ => (analyticAt_eval_poly (realPairQuad s₀) z).pow _
  · unfold halfZeroAnnihilator H
    rw [← Finset.mul_prod_erase F _ hs, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_prod, Polynomial.eval_mul, Polynomial.eval_pow, eval_map_realPairQuad,
      mul_pow, eval_finset_prod_poly]
    simp only [Polynomial.map_pow, Polynomial.eval_pow]
    ring

/-- The meromorphic normal form of `Q(s) P_ℂ(s)` on `ℂ`, removing the singularities where `P_ℂ`
cancels the poles of `Q(s) = s ξ(2s − 1) / ξ(2s)`. -/
def scatterQPoly (P : Polynomial ℝ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun s => scatterQ s * (P.map (algebraMap ℝ ℂ)).eval s) univ

private theorem scatterQRaw_eq_div (P : Polynomial ℝ) :
    (fun s => scatterQ s * (P.map (algebraMap ℝ ℂ)).eval s) =
      (fun s => s * xi (2 * s - 1) * (P.map (algebraMap ℝ ℂ)).eval s) / xiHalf := by
  funext s
  simp [scatterQ, xiHalf, div_mul_eq_mul_div]

private theorem analyticAt_scatterQPoly_num (P : Polynomial ℝ) (z : ℂ) :
    AnalyticAt ℂ (fun s => s * xi (2 * s - 1) * (P.map (algebraMap ℝ ℂ)).eval s) z := by
  have hx : AnalyticOnNhd ℂ (fun s : ℂ => xi (2 * s - 1)) univ :=
    DifferentiableOn.analyticOnNhd
      (fun s _ => ((xi_differentiable _).comp s
        ((differentiableAt_id.const_mul 2).sub_const 1)).differentiableWithinAt)
      isOpen_univ
  exact (analyticAt_id.mul (hx z (mem_univ z))).mul (analyticAt_eval_poly P z)

private theorem meromorphicOn_scatterQRaw (P : Polynomial ℝ) :
    MeromorphicOn (fun s => scatterQ s * (P.map (algebraMap ℝ ℂ)).eval s) univ := by
  rw [scatterQRaw_eq_div]
  exact fun z _ => (analyticAt_scatterQPoly_num P z).meromorphicAt.div
    (analyticAt_xiHalf z).meromorphicAt

/-- Wherever `ξ(2s) ≠ 0`, `scatterQPoly P` agrees pointwise with `scatterQ s * P_ℂ(s)`. -/
theorem scatterQPoly_eq_of_xi_ne_zero (P : Polynomial ℝ) {s : ℂ} (hx : xi (2 * s) ≠ 0) :
    scatterQPoly P s = scatterQ s * (P.map (algebraMap ℝ ℂ)).eval s := by
  have hNF : MeromorphicNFAt (scatterQPoly P) s :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ s)
  have hana : AnalyticAt ℂ (fun z => scatterQ z * (P.map (algebraMap ℝ ℂ)).eval z) s := by
    rw [scatterQRaw_eq_div]
    exact (analyticAt_scatterQPoly_num P s).div (analyticAt_xiHalf s) hx
  exact ((hNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hana.meromorphicNFAt).mp
    ((meromorphicOn_scatterQRaw P).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s))).eq_of_nhds

/-- If `F` contains all zeros of `ξ(2s)` in `Re s > θ₀/2`, then `scatterQPoly (halfZeroAnnihilator F)`
is analytic (hence differentiable) at every `s` with `Re s > θ₀/2`. -/
theorem analyticAt_scatterQPoly_halfZeroAnnihilator {F : Finset ℂ} {θ₀ : ℝ}
    (hF : ∀ s : ℂ, θ₀ / 2 < s.re → xi (2 * s) = 0 → s ∈ F) {s : ℂ} (hs : θ₀ / 2 < s.re) :
    AnalyticAt ℂ (scatterQPoly (halfZeroAnnihilator F)) s := by
  set P := halfZeroAnnihilator F
  have hNF : MeromorphicNFAt (scatterQPoly P) s :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ s)
  refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
  have hcongr : meromorphicOrderAt (scatterQPoly P) s =
      meromorphicOrderAt (fun z => scatterQ z * (P.map (algebraMap ℝ ℂ)).eval z) s :=
    meromorphicOrderAt_congr
      ((meromorphicOn_scatterQRaw P).toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s))
  rw [hcongr]
  by_cases hx : xi (2 * s) = 0
  · obtain ⟨H, hHana, hfac⟩ := exists_analytic_factor_halfZeroAnnihilator (hF s hs hx)
    have hnum_eq : (fun z => z * xi (2 * z - 1) * (P.map (algebraMap ℝ ℂ)).eval z) =
        (fun z : ℂ => (z - s) ^ xiHalfMult s) * (fun z : ℂ => z * xi (2 * z - 1) * H z) := by
      funext z
      dsimp only [Pi.mul_apply, P]
      rw [hfac z]
      ring
    have hGana : AnalyticAt ℂ (fun z : ℂ => z * xi (2 * z - 1) * H z) s := by
      have hx1 : AnalyticOnNhd ℂ (fun z : ℂ => xi (2 * z - 1)) univ :=
        DifferentiableOn.analyticOnNhd
          (fun z _ => ((xi_differentiable _).comp z
            ((differentiableAt_id.const_mul 2).sub_const 1)).differentiableWithinAt)
          isOpen_univ
      exact (analyticAt_id.mul (hx1 s (mem_univ s))).mul (hHana s)
    rw [scatterQRaw_eq_div,
      meromorphicOrderAt_div (analyticAt_scatterQPoly_num P s).meromorphicAt
        (analyticAt_xiHalf s).meromorphicAt,
      hnum_eq,
      meromorphicOrderAt_mul (analyticAt_sub_const_pow s (xiHalfMult s) s).meromorphicAt
        hGana.meromorphicAt,
      meromorphicOrderAt_sub_pow s (xiHalfMult s),
      (analyticAt_xiHalf s).meromorphicOrderAt_eq, ← coe_xiHalfMult s]
    simp only [ENat.map_coe]
    refine withTop_sub_nonneg_of_le ?_
    exact le_add_of_nonneg_right (meromorphicOrderAt_nonneg_of_analyticAt hGana)
  · have hana : AnalyticAt ℂ (fun z => scatterQ z * (P.map (algebraMap ℝ ℂ)).eval z) s := by
      rw [scatterQRaw_eq_div]
      exact (analyticAt_scatterQPoly_num P s).div (analyticAt_xiHalf s) hx
    exact meromorphicOrderAt_nonneg_of_analyticAt hana

/-! ### Polynomial vertical bounds above an ordinate height -/

private theorem exists_norm_eval_poly_le (P : Polynomial ℝ) (σ₀ σ₁ : ℝ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → 1 ≤ |s.im| →
      ‖(P.map (algebraMap ℝ ℂ)).eval s‖ ≤ C * |s.im| ^ N := by
  set M := max (|σ₀| + |σ₁| + 1) 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := by linarith
  set C := ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * M ^ k
  refine ⟨C, P.natDegree, Finset.sum_nonneg fun k _ => by positivity, fun s hs0 hs1 ht => ?_⟩
  have hsn : ‖s‖ ≤ M * |s.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im s
    have hre : |s.re| ≤ |σ₀| + |σ₁| := by
      rcases le_total 0 s.re with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self σ₁, abs_nonneg σ₀]
      · rw [abs_of_nonpos h]; linarith [neg_abs_le σ₀, abs_nonneg σ₁]
    have hmul : |σ₀| + |σ₁| ≤ (|σ₀| + |σ₁|) * |s.im| :=
      le_mul_of_one_le_right (by positivity) ht
    have hMge : |σ₀| + |σ₁| + 1 ≤ M := le_max_left _ _
    nlinarith
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  calc ‖∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k : ℂ) * s ^ k‖
      ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖(P.coeff k : ℂ) * s ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * M ^ k * |s.im| ^ P.natDegree := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hkle : k ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      calc |P.coeff k| * ‖s‖ ^ k ≤ |P.coeff k| * (M * |s.im|) ^ k := by gcongr
        _ = |P.coeff k| * M ^ k * |s.im| ^ k := by rw [mul_pow]; ring
        _ ≤ |P.coeff k| * M ^ k * |s.im| ^ P.natDegree := by gcongr
    _ = C * |s.im| ^ P.natDegree := by rw [← Finset.sum_mul]

private theorem exists_norm_scatterQ_le_above {σ₀ σ₁ T₁ K₀ : ℝ} {N₀ : ℕ}
    (hT₁ : 1 ≤ T₁) (hK₀ : 0 ≤ K₀)
    (hinv : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → T₁ ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ K₀ * |s.im| ^ N₀) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → T₁ ≤ |s.im| →
      ‖scatterQ s‖ ≤ C * |s.im| ^ N := by
  obtain ⟨C₁, N₁, hC₁, hΓ₁⟩ := exists_sharp_bound_norm_Gamma_strip (σ₀ - 1 / 2) (σ₁ - 1 / 2)
  obtain ⟨C₂, N₂, hC₂, hΓ₂⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_inv_Gamma_strip σ₀ σ₁
  obtain ⟨C₃, N₃, hC₃, hζ⟩ := exists_bound_norm_riemannZeta_strip (|2 * σ₀ - 1| + |2 * σ₁ - 1|)
  set L := |σ₀ - 1| + |σ₁ - 1| + 1
  refine ⟨L * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂)) * (C₃ * 2 ^ N₃) * K₀,
    1 + (N₁ + N₂) + N₃ + N₀, by positivity, fun s h0 h1 htT => ?_⟩
  have ht : 1 ≤ |s.im| := hT₁.trans htT
  have hsim : s.im ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
  rw [scatterQ_eq hsim, norm_mul, norm_mul, norm_mul, norm_gammaℝ_div]
  have hA : ‖s - 1‖ ≤ L * |s.im| := by
    have hnorm : ‖s - 1‖ ≤ |s.re - 1| + |s.im| := by
      simpa using Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre : |s.re - 1| ≤ |σ₀ - 1| + |σ₁ - 1| := by
      rcases le_total 1 s.re with h | h
      · rw [abs_of_nonneg (by linarith)]; linarith [le_abs_self (σ₁ - 1), abs_nonneg (σ₀ - 1)]
      · rw [abs_of_nonpos (by linarith)]; linarith [neg_abs_le (σ₀ - 1), abs_nonneg (σ₁ - 1)]
    have hS : |σ₀ - 1| + |σ₁ - 1| ≤ (|σ₀ - 1| + |σ₁ - 1|) * |s.im| :=
      le_mul_of_one_le_right (by positivity) ht
    calc ‖s - 1‖ ≤ |s.re - 1| + |s.im| := hnorm
      _ ≤ (|σ₀ - 1| + |σ₁ - 1|) * |s.im| + |s.im| := by linarith
      _ = L * |s.im| := by simp only [L]; ring
  have hB1 : ‖Gamma (s - 1 / 2)‖ ≤ C₁ * |s.im| ^ N₁ * Real.exp (-(Real.pi * |s.im| / 2)) := by
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    have him' : (s - 1 / 2).im = s.im := by simp
    have := hΓ₁ (s - 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him']; exact ht)
    rwa [him'] at this
  have hB2 := hΓ₂ s h0 h1 ht
  have hB : ‖Gamma (s - 1 / 2)‖ * ‖(Gamma s)⁻¹‖ ≤ C₁ * C₂ * |s.im| ^ (N₁ + N₂) := by
    calc ‖Gamma (s - 1 / 2)‖ * ‖(Gamma s)⁻¹‖
        ≤ (C₁ * |s.im| ^ N₁ * Real.exp (-(Real.pi * |s.im| / 2))) *
          (C₂ * |s.im| ^ N₂ * Real.exp (Real.pi * |s.im| / 2)) :=
          mul_le_mul hB1 hB2 (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * |s.im| ^ (N₁ + N₂) := by
          rw [pow_add]
          have hexp : Real.exp (-(Real.pi * |s.im| / 2)) * Real.exp (Real.pi * |s.im| / 2) = 1 := by
            rw [← Real.exp_add]; simp
          linear_combination (C₁ * C₂ * |s.im| ^ N₁ * |s.im| ^ N₂) * hexp
  have hC : ‖riemannZeta (2 * s - 1)‖ ≤ C₃ * 2 ^ N₃ * |s.im| ^ N₃ := by
    have hz : (2 : ℂ) * s - 1 = (((2 * s.re - 1 : ℝ)) : ℂ) + ((2 * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have hσ : |2 * s.re - 1| ≤ |2 * σ₀ - 1| + |2 * σ₁ - 1| := by
      rcases le_total (2 * s.re - 1) 0 with h | h
      · rw [abs_of_nonpos h]; linarith [neg_abs_le (2 * σ₀ - 1), abs_nonneg (2 * σ₁ - 1)]
      · rw [abs_of_nonneg h]; linarith [le_abs_self (2 * σ₁ - 1), abs_nonneg (2 * σ₀ - 1)]
    have ht2 : 1 ≤ |2 * s.im| := by rw [abs_mul]; norm_num; linarith
    have := hζ _ _ hσ ht2
    rw [hz]
    calc _ ≤ C₃ * |2 * s.im| ^ N₃ := this
      _ = C₃ * 2 ^ N₃ * |s.im| ^ N₃ := by rw [abs_mul, mul_pow]; norm_num; ring
  have hD := hinv s h0 h1 htT
  calc ‖s - 1‖ * (Real.pi ^ (1 / 2 : ℝ) * (‖Gamma (s - 1 / 2)‖ * ‖(Gamma s)⁻¹‖)) *
        ‖riemannZeta (2 * s - 1)‖ * ‖(riemannZeta (2 * s))⁻¹‖
      ≤ (L * |s.im|) * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂ * |s.im| ^ (N₁ + N₂))) *
        (C₃ * 2 ^ N₃ * |s.im| ^ N₃) * (K₀ * |s.im| ^ N₀) := by gcongr
    _ = L * (Real.pi ^ (1 / 2 : ℝ) * (C₁ * C₂)) * (C₃ * 2 ^ N₃) * K₀ *
        |s.im| ^ (1 + (N₁ + N₂) + N₃ + N₀) := by ring

/-! ### Regular part and contour shift for Euler-filtered test functions -/

/-- Desingularized pole numerator `2 scatterQPoly P s · 𝓜φ(−s) − c_P Γ(s)` for `eulerPolyR P φ`. -/
def poleNumeratorPoly (P : Polynomial ℝ) (φ : ℝ → ℝ) (s : ℂ) : ℂ :=
  2 * scatterQPoly P s * mellin (fun t => (φ t : ℂ)) (-s) -
    residueConst (fun t => (eulerPolyR P φ t : ℂ)) * Gamma s

/-- Desingularized regular part `Ψ_P(w)` for `eulerPolyR P φ`. -/
def regularPartPoly (P : Polynomial ℝ) (φ : ℝ → ℝ) (w : ℂ) : ℂ :=
  2 * mellin (fun t => (eulerPolyR P φ t : ℂ)) w + dslope (poleNumeratorPoly P φ) 1 (w + 1)

theorem poleNumeratorPoly_one (P : Polynomial ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b) :
    poleNumeratorPoly P φ 1 = 0 := by
  have hx : xi (2 * (1 : ℂ)) ≠ 0 := xi_ne_zero_of_one_lt_re (by norm_num)
  rw [poleNumeratorPoly, scatterQPoly_eq_of_xi_ne_zero P hx, residueConst,
    mellin_eulerPolyR_neg P hφ hψ 1, Complex.Gamma_one]
  ring

theorem regularPartPoly_eq (P : Polynomial ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b) {w : ℂ} (hw : w ≠ 0) :
    regularPartPoly P φ w =
      2 * mellin (fun t => (eulerPolyR P φ t : ℂ)) w + poleNumeratorPoly P φ (w + 1) / w := by
  rw [regularPartPoly, dslope_of_ne _ (by simpa using hw), slope_def_field,
    poleNumeratorPoly_one P hφ hψ, sub_zero, add_sub_cancel_right]

theorem regularPartPoly_eq_regularPart_of_re_pos (P : Polynomial ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b)
    {w : ℂ} (hw : 0 < w.re) :
    regularPartPoly P φ w = regularPart (fun t => (eulerPolyR P φ t : ℂ)) w := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hx : xi (2 * (w + 1)) ≠ 0 := xi_ne_zero_of_one_lt_re (by simp; linarith)
  rw [regularPartPoly_eq P hφ hψ hw0, regularPart_eq hw0]
  congr 2
  unfold poleNumeratorPoly poleNumerator
  rw [scatterQPoly_eq_of_xi_ne_zero P hx, mellin_eulerPolyR_neg P hφ hψ (w + 1)]
  ring

theorem differentiableAt_regularPartPoly {F : Finset ℂ} {θ₀ : ℝ} (hθ0 : 0 ≤ θ₀) (hθ2 : θ₀ < 2)
    (hF : ∀ s : ℂ, θ₀ / 2 < s.re → xi (2 * s) = 0 → s ∈ F)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b)
    {w : ℂ} (hw : θ₀ / 2 - 1 < w.re) :
    DifferentiableAt ℂ (regularPartPoly (halfZeroAnnihilator F) φ) w := by
  set P := halfZeroAnnihilator F
  have hψP := isTest_eulerPolyR P hφ hψ
  have hU : IsOpen {s : ℂ | θ₀ / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : {s : ℂ | θ₀ / 2 < s.re} ∈ 𝓝 (1 : ℂ) := hU.mem_nhds (by simp; linarith)
  have hdN : DifferentiableOn ℂ (poleNumeratorPoly P φ) {s : ℂ | θ₀ / 2 < s.re} := by
    intro s hs
    have hs' : θ₀ / 2 < s.re := hs
    have hQ := (analyticAt_scatterQPoly_halfZeroAnnihilator hF hs').differentiableAt
    have hΓ : DifferentiableAt ℂ Gamma s := by
      refine Complex.differentiableAt_Gamma s fun m hm => ?_
      have := congrArg Complex.re hm; simp at this
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold poleNumeratorPoly
    exact ((hQ.const_mul 2).mul
      ((hψ.differentiableAt_mellin (-s)).comp s differentiableAt_id.neg)).sub (hΓ.const_mul _)
  have hd := (Complex.differentiableOn_dslope h1).2 hdN
  have hw1 : w + 1 ∈ {s : ℂ | θ₀ / 2 < s.re} := by simp; linarith
  have hdw := (hd _ hw1).differentiableAt (hU.mem_nhds hw1)
  exact ((hψP.differentiableAt_mellin w).const_mul 2).add
    (hdw.comp w (differentiableAt_id.add_const 1))

theorem mellinRegularStrip_regularPartPoly {F : Finset ℂ} {θ₀ T₀ : ℝ}
    (hθhalf : 1 / 2 ≤ θ₀) (hθ1 : θ₀ ≤ 1) (_ : 0 < T₀)
    (hF : ∀ s : ℂ, θ₀ / 2 < s.re → xi (2 * s) = 0 → s ∈ F)
    (hzf : ∀ z : ℂ, θ₀ < z.re → T₀ ≤ |z.im| → riemannZeta z ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (hψ : IsTest (fun t => (φ t : ℂ)) a b) :
    MellinRegularStrip (regularPartPoly (halfZeroAnnihilator F) φ) (θ₀ / 2 - 1) 2 := by
  set P := halfZeroAnnihilator F
  have hψP := isTest_eulerPolyR P hφ hψ
  have hθ0 : 0 ≤ θ₀ := by linarith
  refine ⟨fun w hw _ => differentiableAt_regularPartPoly hθ0 (by linarith) hF hφ hψ hw,
    fun a' b' ha' hb' K => ?_⟩
  set T₁ : ℝ := max 3 (T₀ / 2 + 2)
  have hT₁1 : 1 ≤ T₁ := le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_max_left _ _)
  have hbox : IsCompact (Icc a' b' ×ℂ Icc (-T₁) T₁) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn
    (f := regularPartPoly P φ) (fun w hw => by
      have hw' : a' ≤ w.re := hw.1.1
      exact (differentiableAt_regularPartPoly hθ0 (by linarith) hF hφ hψ (by linarith)).continuousAt
        |>.continuousWithinAt)
  set δ := min (2 * (a' + 1) - θ₀) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨κ, hκ0, hζlow⟩ :=
    exists_zeta_lower_bound_subpolynomial_of_zeroFree_above hθhalf hθ1 hzf hδ hδ1 one_pos
  have hinv : ∀ s : ℂ, a' + 1 ≤ s.re → s.re ≤ b' + 1 → T₁ ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (4 * κ⁻¹) * |s.im| ^ 1 := by
    intro s hs0 _ htT
    have ht1 : 1 ≤ |s.im| := hT₁1.trans htT
    have h2im : |(2 * s).im| = 2 * |s.im| := by simp [abs_mul]
    have h6 : 6 ≤ |(2 * s).im| := by
      rw [h2im]; linarith [le_max_left 3 (T₀ / 2 + 2)]
    have hT4 : T₀ + 4 ≤ |(2 * s).im| := by
      rw [h2im]; linarith [le_max_right 3 (T₀ / 2 + 2)]
    have hre2 : θ₀ + δ ≤ (2 * s).re := by
      simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      linarith [min_le_left (2 * (a' + 1) - θ₀) (1 / 2)]
    have hlow := hζlow (2 * s) hre2 h6 hT4
    rw [Real.rpow_neg_one] at hlow
    have hpos_u : 0 < 2 + |(2 * s).im| := by positivity
    have hpos_z : 0 < ‖riemannZeta (2 * s)‖ := lt_of_lt_of_le (by positivity) hlow
    rw [norm_inv]
    have hinv_le : (‖riemannZeta (2 * s)‖)⁻¹ ≤ (κ * (2 + |(2 * s).im|)⁻¹)⁻¹ :=
      inv_anti₀ (by positivity) hlow
    calc (‖riemannZeta (2 * s)‖)⁻¹ ≤ (κ * (2 + |(2 * s).im|)⁻¹)⁻¹ := hinv_le
      _ = κ⁻¹ * (2 + 2 * |s.im|) := by rw [mul_inv, inv_inv, h2im]
      _ ≤ κ⁻¹ * (4 * |s.im|) := by gcongr; linarith
      _ = (4 * κ⁻¹) * |s.im| ^ 1 := by ring
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le_above hT₁1 (by positivity) hinv
  obtain ⟨CP, NP, hCP, hPbd⟩ := exists_norm_eval_poly_le P (a' + 1) (b' + 1)
  set R := |a' - 1| + |b' - 1| + |a' + 2| + |b' + 2|
  obtain ⟨C₁, hC₁, hm₁⟩ := exists_norm_mellin_le_decay_pow hψP R K
  obtain ⟨C₂, hC₂, hm₂⟩ := exists_norm_mellin_le_decay_pow hψ R (K + (NQ + NP))
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip (a' + 1) (b' + 1)
  obtain ⟨CE, hCE, hE⟩ := exists_pow_mul_exp_le NΓ K
  set cP := residueConst (fun t => (eulerPolyR P φ t : ℂ))
  refine ⟨max B 0 * (1 + T₁ ^ 2) ^ K + (2 * C₁ + 2 * (CQ * CP) * C₂ + ‖cP‖ * (CΓ * CE)),
    fun w hw1 hw2 => ?_⟩
  have hpos : 0 < (1 + w.im ^ 2) ^ K := by positivity
  rcases le_or_gt |w.im| T₁ with ht | ht
  · have hwb : w ∈ Icc a' b' ×ℂ Icc (-T₁) T₁ := ⟨⟨hw1, hw2⟩, abs_le.1 ht⟩
    have h1 : (1 + w.im ^ 2) ^ K ≤ (1 + T₁ ^ 2) ^ K := by
      apply pow_le_pow_left₀ (by positivity)
      have hsq : |w.im| ^ 2 ≤ T₁ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ht 2
      rw [sq_abs] at hsq
      linarith
    rw [le_div_iff₀ hpos]
    calc ‖regularPartPoly P φ w‖ * (1 + w.im ^ 2) ^ K
        ≤ max B 0 * (1 + T₁ ^ 2) ^ K :=
          mul_le_mul ((hB w hwb).trans (le_max_left _ _)) h1 (by positivity) (le_max_right _ _)
      _ ≤ _ := by
          have : 0 ≤ 2 * C₁ + 2 * (CQ * CP) * C₂ + ‖cP‖ * (CΓ * CE) := by positivity
          linarith
  · have htT : T₁ ≤ |w.im| := ht.le
    have ht1 : 1 ≤ |w.im| := hT₁1.trans htT
    have hw0 : w ≠ 0 := fun h => by rw [h] at ht1; simp at ht1; linarith
    have hnw : 1 ≤ ‖w‖ := ht1.trans (Complex.abs_im_le_norm w)
    rw [regularPartPoly_eq P hφ hψ hw0]
    set s := w + 1 with hsdef
    have hsre0 : a' + 1 ≤ s.re := by simp [hsdef]; linarith
    have hsre1 : s.re ≤ b' + 1 := by simp [hsdef]; linarith
    have hsim : s.im = w.im := by simp [hsdef]
    have htsT : T₁ ≤ |s.im| := by rw [hsim]; exact htT
    have hts1 : 1 ≤ |s.im| := by rw [hsim]; exact ht1
    have hx_ne : xi (2 * s) ≠ 0 := by
      intro hx0
      have hζ0 := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hx0).1
      have h2re : θ₀ < (2 * s).re := by
        simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
        linarith
      have h2im : T₀ ≤ |(2 * s).im| := by
        simp only [mul_im, re_ofNat, im_ofNat, zero_mul, add_zero, abs_mul, Nat.abs_ofNat, hsim]
        linarith [le_max_right 3 (T₀ / 2 + 2)]
      exact hzf (2 * s) h2re h2im hζ0
    have hP1 : ‖mellin (fun t => (eulerPolyR P φ t : ℂ)) w‖ ≤ C₁ / (1 + w.im ^ 2) ^ K := by
      refine hm₁ w ?_
      rw [abs_le]; constructor <;> linarith [abs_nonneg (a' - 1), le_abs_self (a' - 1),
        neg_abs_le (a' - 1), le_abs_self (b' - 1), abs_nonneg (a' + 2), abs_nonneg (b' + 2),
        abs_nonneg (b' - 1)]
    have hP2 : ‖mellin (fun t => (φ t : ℂ)) (-s)‖ ≤ C₂ / (1 + w.im ^ 2) ^ (K + (NQ + NP)) := by
      have h := hm₂ (-s) (by
        rw [abs_le]; simp [hsdef]; constructor <;>
          linarith [le_abs_self (a' + 2), neg_abs_le (b' + 2), abs_nonneg (a' - 1),
            abs_nonneg (b' - 1), neg_abs_le (a' + 2), le_abs_self (b' + 2)])
      simpa [hsdef] using h
    have hQP : ‖scatterQPoly P s‖ ≤ (CQ * CP) * |w.im| ^ (NQ + NP) := by
      rw [scatterQPoly_eq_of_xi_ne_zero P hx_ne, norm_mul]
      have hQs := hQ s hsre0 hsre1 htsT
      have hPs := hPbd s hsre0 hsre1 hts1
      rw [hsim] at hQs hPs
      calc ‖scatterQ s‖ * ‖(P.map (algebraMap ℝ ℂ)).eval s‖
          ≤ (CQ * |w.im| ^ NQ) * (CP * |w.im| ^ NP) :=
            mul_le_mul hQs hPs (norm_nonneg _) (by positivity)
        _ = (CQ * CP) * |w.im| ^ (NQ + NP) := by rw [pow_add]; ring
    have hΓs : ‖Gamma s‖ ≤ CΓ * (CE / (1 + w.im ^ 2) ^ K) := by
      have h := hΓ s hsre0 hsre1 hts1
      rw [hsim] at h
      calc ‖Gamma s‖ ≤ CΓ * (|w.im| ^ NΓ * Real.exp (-(Real.pi * |w.im| / 2))) := by linarith [h]
        _ ≤ CΓ * (CE / (1 + w.im ^ 2) ^ K) := by gcongr; exact hE _ ht1
    have hpowle : |w.im| ^ (NQ + NP) ≤ (1 + w.im ^ 2) ^ (NQ + NP) := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      nlinarith [sq_abs w.im, abs_nonneg w.im]
    have hQψ : ‖scatterQPoly P s‖ * ‖mellin (fun t => (φ t : ℂ)) (-s)‖ ≤
        (CQ * CP) * C₂ / (1 + w.im ^ 2) ^ K := by
      calc ‖scatterQPoly P s‖ * ‖mellin (fun t => (φ t : ℂ)) (-s)‖
          ≤ ((CQ * CP) * |w.im| ^ (NQ + NP)) * (C₂ / (1 + w.im ^ 2) ^ (K + (NQ + NP))) :=
            mul_le_mul hQP hP2 (norm_nonneg _) (by positivity)
        _ ≤ ((CQ * CP) * (1 + w.im ^ 2) ^ (NQ + NP)) *
              (C₂ / (1 + w.im ^ 2) ^ (K + (NQ + NP))) := by gcongr
        _ = (CQ * CP) * C₂ / (1 + w.im ^ 2) ^ K := by
          have hppos : (1 + w.im ^ 2) ^ (NQ + NP) ≠ 0 := by positivity
          rw [pow_add (1 + w.im ^ 2) K (NQ + NP)]
          field_simp [hppos]
    have hN : ‖poleNumeratorPoly P φ s‖ ≤
        (2 * (CQ * CP) * C₂ + ‖cP‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by
      unfold poleNumeratorPoly
      calc ‖2 * scatterQPoly P s * mellin (fun t => (φ t : ℂ)) (-s) - cP * Gamma s‖
          ≤ 2 * (‖scatterQPoly P s‖ * ‖mellin (fun t => (φ t : ℂ)) (-s)‖) + ‖cP‖ * ‖Gamma s‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul]; norm_num; linarith
        _ ≤ 2 * ((CQ * CP) * C₂ / (1 + w.im ^ 2) ^ K) +
              ‖cP‖ * (CΓ * (CE / (1 + w.im ^ 2) ^ K)) := by gcongr
        _ = _ := by ring
    calc ‖2 * mellin (fun t => (eulerPolyR P φ t : ℂ)) w + poleNumeratorPoly P φ s / w‖
        ≤ 2 * ‖mellin (fun t => (eulerPolyR P φ t : ℂ)) w‖ + ‖poleNumeratorPoly P φ s‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_div]; norm_num
          exact div_le_self (norm_nonneg _) hnw
      _ ≤ 2 * (C₁ / (1 + w.im ^ 2) ^ K) +
            (2 * (CQ * CP) * C₂ + ‖cP‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by gcongr
      _ = (2 * C₁ + 2 * (CQ * CP) * C₂ + ‖cP‖ * (CΓ * CE)) / (1 + w.im ^ 2) ^ K := by ring
      _ ≤ _ := by
          have hB0 : 0 ≤ max B 0 * (1 + T₁ ^ 2) ^ K := by positivity
          exact div_le_div_of_nonneg_right (by linarith [hB0]) hpos.le

/-- **Achievability below `1 − Θ_∞/2`:** for every `α < 1 − Θ_∞/2`, there exists a nonzero real
polynomial `P` such that `eulerPolyR P φ` equidistributes at rate `O(y^α)` across all admissible
profiles `φ`. -/
theorem exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa {α : ℝ}
    (hα : α < 1 - zetaAsymptoticAbscissa / 2) :
    ∃ P : Polynomial ℝ, P ≠ 0 ∧ EulerFilteredHorocycleRate P α := by
  rcases lt_or_ge α (1 / 2) with hα_low | hα_ge
  · refine ⟨1, one_ne_zero, fun φ hφ hc hs => ?_⟩
    have heq : (fun t : ℝ => (eulerPolyR 1 φ t : ℂ)) = fun t : ℝ => (φ t : ℂ) := by
      funext t
      simp [eulerPolyR, eulerIterR]
    set ε := min ((1 / 2 - α) / 2) (1 / 4)
    have hε : 0 < ε := lt_min (by linarith) (by norm_num)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    obtain ⟨C, hC, h⟩ := horocycle_rate hφ hc hs hε hε1
    refine ⟨6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1), C, fun y hy hy1 => ?_⟩
    rw [heq]
    refine (h y hy hy1).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow_of_exponent_ge hy hy1
      (by linarith [min_le_left ((1 / 2 - α) / 2) (1 / 4)])
  · set θ₀ := (zetaAsymptoticAbscissa + (2 - 2 * α)) / 2
    set ε := (1 - zetaAsymptoticAbscissa / 2 - α) / 2
    have hθ_gt : zetaAsymptoticAbscissa < θ₀ := by simp only [θ₀]; linarith
    have hθ_half : 1 / 2 ≤ θ₀ := le_trans half_le_zetaAsymptoticAbscissa hθ_gt.le
    have hθ1 : θ₀ ≤ 1 := by simp only [θ₀]; linarith [zetaAsymptoticAbscissa_le_one]
    have hε : 0 < ε := by simp only [ε]; linarith
    have hε1 : ε < 1 := by
      simp only [ε]
      linarith [half_le_zetaAsymptoticAbscissa]
    have hexp_eq : 1 - θ₀ / 2 - ε = α := by simp only [θ₀, ε]; ring
    obtain ⟨σ, hσ, hσlt⟩ := exists_lt_of_csInf_lt zetaAsymptoticAbscissaSet_nonempty hθ_gt
    have hθ_mem : θ₀ ∈ zetaAsymptoticAbscissaSet := zetaAsymptoticAbscissaSet_mono hσ hσlt.le
    obtain ⟨-, T₀, hT₀, hTbd⟩ := mem_zetaAsymptoticAbscissaSet_iff_eventually_height.mp hθ_mem
    have hSfin : {s : ℂ | θ₀ / 2 < s.re ∧ xi (2 * s) = 0}.Finite := by
      have himg : {z : ℂ | θ₀ < z.re ∧ xi z = 0}.Finite := by
        refine (hθ_mem.2.image fun q : XiZeroCopy => (q.1 : ℂ)).subset ?_
        rintro z ⟨hzre, hxi⟩
        obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hxi
        have hζ := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
        obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ h0 h1
        exact ⟨q, by show θ₀ < (q.1 : ℂ).re; rw [hq]; exact hzre, hq⟩
      refine (himg.preimage (mul_right_injective₀ (two_ne_zero : (2 : ℂ) ≠ 0)).injOn).subset ?_
      rintro s ⟨hsre, hxi⟩
      exact ⟨by simp; linarith, hxi⟩
    classical
    set F := hSfin.toFinset
    have hF : ∀ s : ℂ, θ₀ / 2 < s.re → xi (2 * s) = 0 → s ∈ F := fun s hsre hxi =>
      (Set.Finite.mem_toFinset hSfin).mpr ⟨hsre, hxi⟩
    have hzf : ∀ z : ℂ, θ₀ < z.re → T₀ ≤ |z.im| → riemannZeta z ≠ 0 := by
      intro z hzre hzim hζ0
      have hz1 : z.re < 1 := by
        by_contra hc
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hζ0
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ0 (by linarith) hz1
      have hle := hTbd q (by rw [hq]; exact hzim)
      rw [hq] at hle
      linarith
    set P := halfZeroAnnihilator F
    refine ⟨P, halfZeroAnnihilator_ne_zero F, fun φ hφ hc hs => ?_⟩
    obtain ⟨a, b, ha, hab, hφa, hφb⟩ := exists_band_of_tsupport hc hs
    have hψ := isTest_of_band hφ (by linarith) hab hφa hφb
    have hψP := isTest_eulerPolyR P hφ hψ
    have hΨ := mellinRegularStrip_regularPartPoly hθ_half hθ1 hT₀ hF hzf hφ hψ
    set ψP : ℝ → ℂ := fun t => (eulerPolyR P φ t : ℂ)
    set A := horocycleMean (pseudoEisenstein ψP)
    set c := residueConst ψP
    set g : ℝ → ℂ := fun y => A y - c * ((Real.exp (-y) : ℝ) : ℂ) with hg
    set c' : ℝ := θ₀ / 2 - 1 + ε with hc'
    have hc'1 : θ₀ / 2 - 1 < c' := by linarith
    have hc'2 : c' < 2 := by linarith
    have h11 : θ₀ / 2 - 1 < 1 := by linarith
    set K := (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖regularPartPoly P φ ((c' : ℂ) + t * Complex.I)‖ with hK
    have hψPa : ∀ y, y < a → ψP y = 0 := fun y hy => hψP.eq_zero_of_le hy.le
    have hψPb : ∀ y, b < y → ψP y = 0 := fun y hy => hψP.eq_zero_of_ge hy.le
    obtain ⟨B, -, hB⟩ := exists_norm_pseudoEisenstein_le hψP.continuous ha hψPa hψPb
    have hFc := continuous_pseudoEisenstein hψP.continuous (by linarith) hψPa
    refine ⟨c, K + ‖c‖, fun y hy hy1 => ?_⟩
    have hconv : MellinConvergent g 1 := by
      have h1 := mellinConvergent_horocycleMean hψP.continuous ha hψPa hψPb (s := 2) (by norm_num)
      have h2 := (mellinConvergent_exp_neg (w := 1) (by norm_num)).const_smul c
      norm_num at h1
      refine (h1.sub h2).congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, hg, smul_eq_mul]
      ring
    have hline : ∀ t : ℝ, mellin g ((1 : ℝ) + t * Complex.I) =
        regularPartPoly P φ ((1 : ℝ) + t * Complex.I) := by
      intro t
      rw [mellin_sub_exp_eq_regularPart hψP ha (by simp),
        regularPartPoly_eq_regularPart_of_re_pos P hφ hψ (by simp)]
    have hvert : VerticalIntegrable (mellin g) 1 :=
      (hΨ.integrable_line h11 (by norm_num)).congr (Eventually.of_forall fun t => (hline t).symm)
    have hcont : ContinuousAt g y :=
      (continuousAt_horocycleMean hFc hB hy).sub (continuousAt_const.mul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt)
    have hinv := mellinInv_mellin_eq 1 g hy hconv hvert hcont
    have hinv' : mellinInv 1 (mellin g) y = mellinInv 1 (regularPartPoly P φ) y := by
      unfold mellinInv
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hline t]
    have hshift := hΨ.mellinInv_eq h11 (by norm_num) hc'1 hc'2 hy
    have hbound := norm_mellinInv_le (Ψ := regularPartPoly P φ) c' hy
    have hgy : ‖g y‖ ≤ K * y ^ α := by
      rw [← hinv, hinv', hshift]
      refine hbound.trans (le_of_eq ?_)
      rw [hK, show -c' = α by rw [hc', ← hexp_eq]; ring]
      ring
    have hexp : ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ ≤ y := by
      rw [show ((Real.exp (-y) : ℝ) : ℂ) - 1 = ((Real.exp (-y) - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
          have := Real.exp_le_one_iff.2 (by linarith : -y ≤ 0); linarith)]
      linarith [Real.add_one_le_exp (-y)]
    have hyp : y ≤ y ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by rw [← hexp_eq]; linarith : α ≤ 1)
      simpa using this
    have hsplit : A y - c = g y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1) := by
      simp only [hg]; ring
    rw [hsplit]
    calc ‖g y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1)‖
        ≤ ‖g y‖ + ‖c‖ * ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ K * y ^ α + ‖c‖ * y ^ α := by gcongr; exact hexp.trans hyp
      _ = (K + ‖c‖) * y ^ α := by ring

/-! ## 5. Exact filtered supremum and equivalences for `ZerosApproachLine` and `AAL` -/

/-- **Exact supremum of Euler-filtered horocycle exponents:** `1 − Θ_∞/2`. -/
theorem sSup_eulerFilteredHorocycleExponents :
    sSup eulerFilteredHorocycleExponents = 1 - zetaAsymptoticAbscissa / 2 := by
  have hne : eulerFilteredHorocycleExponents.Nonempty :=
    ⟨0, exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa
      (by linarith [zetaAsymptoticAbscissa_le_one])⟩
  have hub : ∀ α ∈ eulerFilteredHorocycleExponents, α ≤ 1 - zetaAsymptoticAbscissa / 2 := by
    rintro α ⟨P, hP, hrate⟩
    have := zetaAsymptoticAbscissa_le_of_eulerPoly_horocycle_rate hP hrate
    linarith
  refine le_antisymm (csSup_le hne hub) (le_of_forall_pos_le_add fun ε hε => ?_)
  have hmem : 1 - zetaAsymptoticAbscissa / 2 - ε / 2 ∈ eulerFilteredHorocycleExponents :=
    exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa (by linarith)
  linarith [le_csSup ⟨1 - zetaAsymptoticAbscissa / 2, hub⟩ hmem]

/-- **`ZerosApproachLine` as polynomial-accelerated Zagier equidistribution:** `ZerosApproachLine`
holds iff for every `ε > 0` some nonzero real Euler polynomial accelerates pseudo-Eisenstein
horocycle equidistribution to rate `O(y^{3/4 − ε})`. -/
theorem zerosApproachLine_iff_eulerPoly_horocycle_rate :
    ZerosApproachLine ↔
      ∀ ε : ℝ, 0 < ε → ∃ P : Polynomial ℝ, P ≠ 0 ∧ EulerFilteredHorocycleRate P (3 / 4 - ε) := by
  rw [zerosApproachLine_iff_zetaAsymptoticAbscissa_eq_half]
  constructor
  · intro hΘ ε hε
    refine exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa ?_
    rw [hΘ]; linarith
  · intro hall
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) half_le_zetaAsymptoticAbscissa
    obtain ⟨P, hP, hrate⟩ := hall (ε / 2) (half_pos hε)
    have hle := zetaAsymptoticAbscissa_le_of_eulerPoly_horocycle_rate hP hrate
    linarith

/-- **`AsymptoticAbscissaLaw` as non-accelerability of horocycle equidistribution:** `AAL` holds
iff no nonzero real Euler polynomial `P(y d/dy)` achieves universal horocycle rate `O(y^α)` for
any `α > 1 − Θ/2`. -/
theorem asymptoticAbscissaLaw_iff_no_eulerPoly_horocycle_acceleration :
    AsymptoticAbscissaLaw ↔
      ¬ ∃ (P : Polynomial ℝ) (α : ℝ), P ≠ 0 ∧ 1 - zetaZeroAbscissa / 2 < α ∧
        EulerFilteredHorocycleRate P α := by
  rw [asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa]
  constructor
  · rintro hΘ ⟨P, α, hP, hgt, hrate⟩
    have hle := zetaAsymptoticAbscissa_le_of_eulerPoly_horocycle_rate hP hrate
    rw [hΘ] at hle
    linarith
  · intro hno
    refine le_antisymm zetaAsymptoticAbscissa_le_zetaZeroAbscissa ?_
    by_contra hlt
    push Not at hlt
    set α := 1 - (zetaAsymptoticAbscissa + zetaZeroAbscissa) / 4
    obtain ⟨P, hP, hrate⟩ :=
      exists_eulerPoly_horocycle_rate_of_lt_one_sub_half_zetaAsymptoticAbscissa
        (α := α) (by simp only [α]; linarith)
    exact hno ⟨P, α, hP, by simp only [α]; linarith, hrate⟩

end

end GaloisForLFunctions.BlackHoleRingdown
