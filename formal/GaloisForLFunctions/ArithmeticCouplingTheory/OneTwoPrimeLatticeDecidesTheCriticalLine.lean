import GaloisForLFunctions.ArithmeticCouplingTheory.BoundedCouplingIsTheRiemannHypothesis
import GaloisForLFunctions.ArithmeticCouplingTheory.MixedDifferencesSeeEveryZero
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationRateIsTheDepthOfTheDeepestSeenZero
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine

/-!
# One two-prime lattice decides the critical line

The coupling of Weil's kernel on a single two-prime lattice `⟨p⟩ × ⟨q⟩ ≅ ℤ²` is
`C(p^a, q^b) = S(aℓ_p + bℓ_q) − S(aℓ_p) − S(bℓ_q) + S(0)` (`S` the spline series, `ℓ = log`). The
axes `aℓ_p`, `bℓ_q` are discrete, so continuity cannot be applied to `C` itself. It applies to the
**increments** of `C`:

* **Axial cancellation.** The second difference of `C` in `(a, b)` is the mixed difference
  `D(s) = S(s + ℓ_p + ℓ_q) − S(s + ℓ_p) − S(s + ℓ_q) + S(s)` at the point `s = aℓ_p + bℓ_q`: every
  axial term cancels. So a bound `M` on `C` bounds `D` by `4M` on the grid `ℓ_pℤ + ℓ_qℤ`, which is
  dense in `ℝ`, hence on all of `ℝ` by continuity (`norm_mixedSeriesDiff_le`).
* **The Laplacian is a sum of mixed differences.** `(2 − X − X⁻¹)(2 − Y − Y⁻¹) =
  (X − 1)(Y − 1)(1 − X⁻¹)(1 − Y⁻¹)`, so the coupling Laplacian `L_{ℓ_p} L_{ℓ_q} S` is a sum of four
  translates of `±D` and is bounded by `16M` on `ℝ`.
* **The Laplacian is the orbit of the mixed-difference test** (`orbitSeries_mixedDiff`): its zero
  weights are those of the spline times `(2 − 2 cosh(ℓ_p z))(2 − 2 cosh(ℓ_q z))`, `z = ρ − ½`.
* **Rate theorem.** A bounded orbit is blind to every zero off the line
  (`orbitCorr_rate_iff_blindAbove` at `σ = 0`). The mixed difference sees exactly the zeros the
  spline sees off the line (`sees_mixedDiff_iff`), and the spline sees all of them.

**Theorem** (`riemannHypothesis_iff_exists_bound_coupling_zpow`). For any two distinct primes,
RH holds iff the coupling of `K_ζ` on `⟨p⟩ × ⟨q⟩` is bounded. No finiteness of the off-line zeros,
no Diophantine input: one lattice of rank two decides, as `κ(L_p L_q K_ζ|⟨p,q⟩) = κ(K_ζ)` does
for the index.
-/

open Complex Finset Filter Topology Set
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests rightZeros ScalingCycle
  rightZeros_zeta_eq_empty_iff fesSymmetric_zetaZeroConfig)
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory (splineSeries continuous_splineSeries)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The exponential series of a test over a zero configuration: `Σ_ρ e^{t(ρ−½)} w_ρ(f)`. -/
def orbitSeries (Z : ZeroConfig) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∑' ρ : Z.carrier, cexp ((t : ℂ) * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx f) (cx f) ρ

/-- **The orbit of a mixed difference is the coupling Laplacian of the orbit**, at every real
time. -/
theorem orbitSeries_mixedDiff (Z : ZeroConfig) (hZ : SquareRootThreshold.TemperedConfig Z)
    {f : ℝ → ℝ} (hf : f ∈ realTests) (α β t : ℝ) :
    orbitSeries Z (mixedDiff α β f) t =
      4 * orbitSeries Z f t - 2 * orbitSeries Z f (t + α) - 2 * orbitSeries Z f (t - α) -
        2 * orbitSeries Z f (t + β) - 2 * orbitSeries Z f (t - β) +
        orbitSeries Z f (t + α + β) + orbitSeries Z f (t + α - β) +
        orbitSeries Z f (t - α + β) + orbitSeries Z f (t - α - β) := by
  set W : Z.carrier → ℂ := fun ρ => Z.Wsummand (cx f) (cx f) ρ
  have hS : ∀ c : ℝ, HasSum (fun ρ : Z.carrier => cexp ((c : ℂ) * ((ρ : ℂ) - 1 / 2)) * W ρ)
      (orbitSeries Z f c) := fun c => (summable_cexp_mul_Wsummand Z hZ hf c).hasSum
  have hsum := (((((((((hS t).mul_left 4).sub ((hS (t + α)).mul_left 2)).sub
    ((hS (t - α)).mul_left 2)).sub ((hS (t + β)).mul_left 2)).sub
    ((hS (t - β)).mul_left 2)).add (hS (t + α + β))).add (hS (t + α - β))).add
    (hS (t - α + β))).add (hS (t - α - β))
  rw [← hsum.tsum_eq, orbitSeries]
  refine tsum_congr fun ρ => ?_
  rw [Wsummand_mixedDiff Z hf]
  set s : ℂ := (ρ : ℂ) - 1 / 2
  simp only [W]
  push_cast
  have e : ∀ x y : ℂ, cexp ((x + y) * s) = cexp (x * s) * cexp (y * s) := fun x y => by
    rw [← Complex.exp_add]; congr 1; ring
  have em : ∀ x y : ℂ, cexp ((x - y) * s) = cexp (x * s) * cexp (-(y * s)) := fun x y => by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e, em, e, em, e, e, e, em, em, e, em, em]
  ring

theorem norm_sub_sub_add_le (a b c d : ℂ) : ‖a - b - c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a - b - c) d
  have h2 := norm_sub_le (a - b) c
  have h3 := norm_sub_le a b
  linarith

/-- The spline series is the orbit series of the cubic spline over the zeros of `ζ`. -/
theorem splineSeries_eq_orbitSeries : splineSeries = orbitSeries zetaZeroConfig cubicSpline := rfl

/-- The mixed difference of the spline series across `ℓ_p` and `ℓ_q`. -/
def mixedSeriesDiff (α β s : ℝ) : ℂ :=
  splineSeries (s + α + β) - splineSeries (s + α) - splineSeries (s + β) + splineSeries s

theorem continuous_mixedSeriesDiff (α β : ℝ) : Continuous (mixedSeriesDiff α β) := by
  unfold mixedSeriesDiff
  have h := continuous_splineSeries
  fun_prop

/-- The coupling of `K_ζ` at `(p^a, q^b)` in terms of the spline series. -/
theorem coupling_zetaKernel_zpow {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℤ) :
    coupling zetaKernel (primeElt hp ^ (-a)) (primeElt hq ^ (-b)) =
      splineSeries (a * Real.log p + b * Real.log q) - splineSeries (a * Real.log p) -
        splineSeries (b * Real.log q) + splineSeries 0 := by
  have hsc : ∀ (r : ℕ) (hr : r.Prime) (c : ℤ), logScale (primeElt hr ^ (-c)) = -(c * Real.log r) :=
    fun r hr c => by
      rw [logScale, scale_zpow, scale_primeElt]; push_cast; ring
  simp only [coupling, zetaKernel_eq_weilProfile, logScale_mul, logScale_one, hsc, weilProfile]
  rw [neg_zero, ← neg_add, neg_neg, neg_neg, neg_neg]

/-- **Axial cancellation**: a bounded single-lattice coupling bounds the mixed difference of the
spline series by `4M` on all of `ℝ`. -/
theorem norm_mixedSeriesDiff_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {M : ℝ}
    (hM : ∀ a b : ℤ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M) (s : ℝ) :
    ‖mixedSeriesDiff (Real.log p) (Real.log q) s‖ ≤ 4 * M := by
  set ℓp := Real.log p
  set ℓq := Real.log q
  set P : ℤ → ℤ → ℂ := fun a b =>
    splineSeries (a * ℓp + b * ℓq) - splineSeries (a * ℓp) - splineSeries (b * ℓq) + splineSeries 0
  have hP : ∀ a b : ℤ, ‖P a b‖ ≤ M := fun a b => by
    have h := hM (-a) (-b)
    rwa [coupling_zetaKernel_zpow] at h
  have hgrid : ∀ m n : ℤ, mixedSeriesDiff ℓp ℓq (m * ℓp + n * ℓq) =
      P (m + 1) (n + 1) - P (m + 1) n - P m (n + 1) + P m n := fun m n => by
    simp only [mixedSeriesDiff, P]
    push_cast
    ring_nf
  have hdense : Dense (AddSubgroup.closure {ℓp, ℓq} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (RHTower.irrational_log_ratio hq hp hpq.symm)
  have hcl : IsClosed {s : ℝ | ‖mixedSeriesDiff ℓp ℓq s‖ ≤ 4 * M} :=
    isClosed_le (continuous_mixedSeriesDiff ℓp ℓq).norm continuous_const
  have hsub : (AddSubgroup.closure {ℓp, ℓq} : Set ℝ) ⊆ {s : ℝ | ‖mixedSeriesDiff ℓp ℓq s‖ ≤ 4 * M} := by
    intro x hx
    obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.mp hx
    simp only [Set.mem_setOf_eq, zsmul_eq_mul]
    rw [hgrid]
    calc ‖P (m + 1) (n + 1) - P (m + 1) n - P m (n + 1) + P m n‖
        ≤ ‖P (m + 1) (n + 1)‖ + ‖P (m + 1) n‖ + ‖P m (n + 1)‖ + ‖P m n‖ := norm_sub_sub_add_le _ _ _ _
      _ ≤ 4 * M := by linarith [hP (m + 1) (n + 1), hP (m + 1) n, hP m (n + 1), hP m n]
  have h := closure_minimal hsub hcl
  rw [hdense.closure_eq] at h
  exact h (Set.mem_univ s)

/-- **The orbit of the mixed-difference spline is bounded** by `16M` on `ℝ`. -/
theorem norm_orbitSeries_mixedDiff_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {M : ℝ} (hM : ∀ a b : ℤ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M)
    (t : ℝ) :
    ‖orbitSeries zetaZeroConfig (mixedDiff (Real.log p) (Real.log q) cubicSpline) t‖ ≤ 16 * M := by
  set ℓp := Real.log p
  set ℓq := Real.log q
  set D := mixedSeriesDiff ℓp ℓq
  have hD := norm_mixedSeriesDiff_le hp hq hpq hM
  have hlap : orbitSeries zetaZeroConfig (mixedDiff ℓp ℓq cubicSpline) t =
      D t - D (t - ℓp) - D (t - ℓq) + D (t - ℓp - ℓq) := by
    rw [orbitSeries_mixedDiff _ SquareRootThreshold.temperedConfig_zetaZeroConfig
      cubicSpline_mem_realTests, ← splineSeries_eq_orbitSeries]
    simp only [D, mixedSeriesDiff]
    ring_nf
  rw [hlap]
  calc ‖D t - D (t - ℓp) - D (t - ℓq) + D (t - ℓp - ℓq)‖
      ≤ ‖D t‖ + ‖D (t - ℓp)‖ + ‖D (t - ℓq)‖ + ‖D (t - ℓp - ℓq)‖ := norm_sub_sub_add_le _ _ _ _
    _ ≤ 16 * M := by linarith [hD t, hD (t - ℓp), hD (t - ℓq), hD (t - ℓp - ℓq)]

/-- **One two-prime lattice decides RH.** For distinct primes `p, q`, RH holds iff the coupling of
Weil's kernel on `⟨p⟩ × ⟨q⟩` is bounded. -/
theorem riemannHypothesis_iff_exists_bound_coupling_zpow {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    RiemannHypothesis ↔
      ∃ M : ℝ, ∀ a b : ℤ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M := by
  constructor
  · intro hRH
    obtain ⟨M, hM⟩ := (riemannHypothesis_iff_exists_bound_coupling hp hq hp hq hpq hpq).mp hRH
    have hmem : ∀ (a b : ℤ), primeElt hp ^ a ∈ twoPrimeLattice hp hq ∧
        primeElt hq ^ b ∈ twoPrimeLattice hp hq := fun a b =>
      ⟨Subgroup.mem_closure_pair.mpr ⟨a, 0, by rw [zpow_zero, mul_one]⟩,
        Subgroup.mem_closure_pair.mpr ⟨0, b, by rw [zpow_zero, one_mul]⟩⟩
    exact ⟨M, fun a b => hM _ (hmem a b).1 _ (hmem a b).2⟩
  · rintro ⟨M, hM⟩
    set h := mixedDiff (Real.log p) (Real.log q) cubicSpline
    have hh : h ∈ realTests := mixedDiff_mem_realTests cubicSpline_mem_realTests _ _
    let x : ScalingCycle := (0, 0, ⟨h, hh⟩)
    have hbd : ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
        |(configScalingDatum zetaZeroConfig SquareRootThreshold.temperedConfig_zetaZeroConfig).orbitCorr
          x t| ≤ K * Real.exp (0 * t) := by
      refine ⟨16 * M, fun t _ => ?_⟩
      rw [configScalingDatum_orbitCorr_eq, zero_mul, Real.exp_zero, mul_one]
      exact (Complex.abs_re_le_norm _).trans (norm_orbitSeries_mixedDiff_le hp hq hpq hM t)
    have hblind := (orbitCorr_rate_iff_blindAbove zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig fesSymmetric_zetaZeroConfig le_rfl x).mp hbd
    have hlp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    have hlq : Real.log q ≠ 0 := (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
    rw [← rightZeros_zeta_eq_empty_iff, Set.eq_empty_iff_forall_notMem]
    intro ρ hρ
    have hseen : ρ ∈ seenRightZeros zetaZeroConfig cubicSpline := by
      rw [seenRightZeros_cubicSpline]; exact hρ
    have hre : ρ.re ≠ 1 / 2 := ne_of_gt hρ.2
    have hsees : Sees h ρ :=
      (sees_mixedDiff_iff cubicSpline_mem_realTests hlp hlq hre).mpr hseen.2.2
    have hdeep : (0 : ℝ) < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hre)
    rcases hblind ρ hρ.1 hdeep with h0 | h0
    · exact hsees.1 h0
    · exact hsees.2 h0

end GaloisForLFunctions.ArithmeticCouplingTheory
