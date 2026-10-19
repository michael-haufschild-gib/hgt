import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateAdmissibility

/-!
# The shifted ground states fail the folded supersolution test at infinity

The theta harmonic identity (the explicit formula at the level of Riemann's kernel) evaluates the
*signed* prime shift sum of `ω_a`:

    Σ_n Λ(n) n^{−1/2} m_a(log n − x) = P(x+a) − P(x−a),   P(y) = Σ_n Λ(n) n^{−1/2} Φ(y − log n),

and `P(y) = cosh(y/2) − 2c Φ(y) + ∫_0^∞ S(y,u) du − Q(y)` with `Q(y) = Σ Λ(n) n^{−1/2} Φ(y + log n)`
bounded on `y ≥ 0` and `∫_0^∞ S(y,u) du` bounded uniformly in `y`. Since
`cosh((x+a)/2) − cosh((x−a)/2) = 2 sinh(a/2) sinh(x/2)`, the signed sum equals **twice** the source
up to a universal constant, and the reflected collar mass `C_a(x)` (positive parts only) dominates
the signed sum. Hence for `x ≥ a`

    C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K,   K = 2|c| Φ(0) + 4 ∫_0^∞ gammaSourceBound + Q(0),

so `C_a(x) > sinh(a/2) sinh(x/2)` for all large `x`: every shifted ground state is a strict folded
subsolution on a neighbourhood of infinity, with folded defect at most
`−2Φ(x)(sinh(a/2) sinh(x/2) − K)`. No prime number theorem enters: the prime mass below `e^x` that
the folding discards is exactly what the two-sided source equation already accounts for.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.ThetaSourceWard

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The symmetric archimedean integral is uniformly bounded -/

theorem symArchTerm_eq_add_gammaSourceTerm (x u : ℝ) :
    symArchTerm x u = gammaSourceTerm x u + gammaSourceTerm (-x) u := by
  have e : riemannKernelReal (-x + u) = riemannKernelReal (x - u) := by
    rw [show -x + u = -(x - u) by ring, riemannKernelReal_neg']
  rw [gammaSourceTerm_eq, gammaSourceTerm_eq, riemannKernelReal_neg', e]
  unfold symArchTerm
  ring

/-- The integral of `gammaSourceBound` over the half line. -/
def gammaSourceBoundMass : ℝ := ∫ u in Ioi (0 : ℝ), gammaSourceBound u

theorem abs_integral_symArchTerm_le (x : ℝ) :
    |∫ u in Ioi (0 : ℝ), symArchTerm x u| ≤ 2 * gammaSourceBoundMass := by
  have hg : Integrable (fun u => 2 * gammaSourceBound u) (volume.restrict (Ioi (0 : ℝ))) :=
    gammaSourceBound_integrable.const_mul 2
  have hle : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), ‖symArchTerm x u‖ ≤ 2 * gammaSourceBound u :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
      rw [Real.norm_eq_abs, symArchTerm_eq_add_gammaSourceTerm]
      have h1 := abs_gammaSourceTerm_le_bound x (mem_Ioi.mp hu)
      have h2 := abs_gammaSourceTerm_le_bound (-x) (mem_Ioi.mp hu)
      calc |gammaSourceTerm x u + gammaSourceTerm (-x) u|
          ≤ |gammaSourceTerm x u| + |gammaSourceTerm (-x) u| := abs_add_le _ _
        _ ≤ 2 * gammaSourceBound u := by linarith
  have h := norm_integral_le_of_norm_le hg hle
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h

/-! ### The signed prime shift sum -/

/-- The signed prime shift sum of `ω_a` (no positive part). -/
def signedPrimeShift (a x : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * shiftDifference a (Real.log n - x)

/-- The left prime shift sum `P(y) = Σ Λ(n) n^{−1/2} Φ(y − log n)`. -/
def leftPrimeShift (y : ℝ) : ℝ := ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (y - Real.log n)

/-- The right prime shift sum `Q(y) = Σ Λ(n) n^{−1/2} Φ(y + log n)`. -/
def rightPrimeShift (y : ℝ) : ℝ := ∑' n : ℕ, vonMangoldtAtom n * riemannKernelReal (y + Real.log n)

theorem atom_shiftDifference_log_sub_eq (a x : ℝ) (n : ℕ) :
    vonMangoldtAtom n * shiftDifference a (Real.log n - x) =
      vonMangoldtAtom n * riemannKernelReal (x + a - Real.log n) -
        vonMangoldtAtom n * riemannKernelReal (x - a - Real.log n) := by
  unfold shiftDifference
  rw [show Real.log n - x - a = -(x + a - Real.log n) by ring,
    show Real.log n - x + a = -(x - a - Real.log n) by ring, riemannKernelReal_neg',
    riemannKernelReal_neg']
  ring

theorem summable_atom_shiftDifference_log_sub (a x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * shiftDifference a (Real.log n - x) :=
  ((summable_primeShift_left (x + a)).sub (summable_primeShift_left (x - a))).congr fun n =>
    (atom_shiftDifference_log_sub_eq a x n).symm

theorem signedPrimeShift_eq (a x : ℝ) :
    signedPrimeShift a x = leftPrimeShift (x + a) - leftPrimeShift (x - a) := by
  unfold signedPrimeShift leftPrimeShift
  rw [← (summable_primeShift_left (x + a)).tsum_sub (summable_primeShift_left (x - a))]
  exact tsum_congr fun n => atom_shiftDifference_log_sub_eq a x n

theorem primeKernelSum_eq_add (y : ℝ) :
    primeKernelSum y = rightPrimeShift y + leftPrimeShift y := by
  unfold primeKernelSum rightPrimeShift leftPrimeShift
  rw [← (summable_primeShift_right y).tsum_add (summable_primeShift_left y)]
  exact tsum_congr fun n => by ring

theorem rightPrimeShift_nonneg (y : ℝ) : 0 ≤ rightPrimeShift y :=
  tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (riemannKernelReal_pos _).le

theorem rightPrimeShift_le_zero_point {y : ℝ} (hy : 0 ≤ y) :
    rightPrimeShift y ≤ rightPrimeShift 0 := by
  unfold rightPrimeShift
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_primeShift_right y)
    (summable_primeShift_right 0)
  refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
  rw [zero_add]
  exact riemannKernelReal_antitone_of_nonneg (Real.log_natCast_nonneg n) (by linarith)

/-- The reflected collar mass dominates the signed prime shift sum. -/
theorem signedPrimeShift_le_shiftedCollarMass (a x : ℝ) :
    signedPrimeShift a x ≤ shiftedCollarMass a x := by
  unfold shiftedCollarMass signedPrimeShift
  have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0 :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (le_max_right _ _)
  have h2 : (∑' n : ℕ, vonMangoldtAtom n * shiftDifference a (Real.log n - x)) ≤
      ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 :=
    Summable.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (le_max_left _ _) (vonMangoldtAtom_nonneg n))
      (summable_atom_shiftDifference_log_sub a x) (summable_atom_max_shiftDifference a x)
  linarith

/-- The universal constant `K = 2|c| Φ(0) + 4 ∫_0^∞ gammaSourceBound + Q(0)`. -/
def collarExcessConstant : ℝ :=
  2 * |archConstantReal| * riemannKernelReal 0 + 4 * gammaSourceBoundMass + rightPrimeShift 0

/-- **The collar mass is at least twice the source, up to a universal constant**, for `x ≥ a ≥ 0`. -/
theorem two_mul_source_sub_le_shiftedCollarMass {a x : ℝ} (ha : 0 ≤ a) (hx : a ≤ x) :
    2 * Real.sinh (a / 2) * Real.sinh (x / 2) - collarExcessConstant ≤ shiftedCollarMass a x := by
  have hs := signedPrimeShift_le_shiftedCollarMass a x
  rw [signedPrimeShift_eq] at hs
  have hP : ∀ y, leftPrimeShift y = primeKernelSum y - rightPrimeShift y := fun y => by
    rw [primeKernelSum_eq_add]
    ring
  rw [hP, hP, theta_harmonic_identity, theta_harmonic_identity] at hs
  have hQ1 := rightPrimeShift_le_zero_point (show 0 ≤ x + a by linarith)
  have hQ2 := rightPrimeShift_nonneg (x - a)
  have hA1 := abs_le.mp (abs_integral_symArchTerm_le (x + a))
  have hA2 := abs_le.mp (abs_integral_symArchTerm_le (x - a))
  have hcosh : Real.cosh ((x + a) / 2) - Real.cosh ((x - a) / 2) =
      2 * Real.sinh (a / 2) * Real.sinh (x / 2) := by
    rw [show (x + a) / 2 = x / 2 + a / 2 by ring, show (x - a) / 2 = x / 2 - a / 2 by ring,
      Real.cosh_add, Real.cosh_sub]
    ring
  have hΘ1 := riemannKernelReal_pos (x + a)
  have hΘ2 := riemannKernelReal_pos (x - a)
  have hΘ1' := riemannKernelReal_le_zero_point (x + a)
  have hΘ2' := riemannKernelReal_le_zero_point (x - a)
  have hc : -(2 * |archConstantReal| * riemannKernelReal 0) ≤
      -(2 * archConstantReal * riemannKernelReal (x + a)) +
        2 * archConstantReal * riemannKernelReal (x - a) := by
    have habs : |2 * archConstantReal * (riemannKernelReal (x + a) - riemannKernelReal (x - a))| ≤
        2 * |archConstantReal| * riemannKernelReal 0 := by
      rw [abs_mul, abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have := (abs_le.mp habs).2
    linarith
  unfold collarExcessConstant
  linarith [hs, hA1.1, hA2.2, hQ1, hQ2, hc, hcosh]

/-- The folded defect of `ω_a` is at most `−2Φ(x)(sinh(a/2) sinh(x/2) − K)` for `x ≥ a`. -/
theorem foldedDefect_shiftedGroundState_le {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) :
    foldedGenerator (shiftedGroundState a) x -
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x ≤
      -(2 * riemannKernelReal x *
        (Real.sinh (a / 2) * Real.sinh (x / 2) - collarExcessConstant)) := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  rw [foldedGenerator_shiftedGroundState_sub_potential ha hx0]
  have hC := two_mul_source_sub_le_shiftedCollarMass ha.le hx
  have hΘ := (riemannKernelReal_pos x).le
  have := mul_le_mul_of_nonneg_left hC hΘ
  linarith

/-- **Infinity failure.** For every `a > 0` there is `X > 0` such that the shifted ground state is a
strict folded subsolution on `[X, ∞)`. -/
theorem exists_infinity_window_foldedGenerator_lt_potential {a : ℝ} (ha : 0 < a) :
    ∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x →
      foldedGenerator (shiftedGroundState a) x <
        riemannKernelReal x * Real.cosh (x / 2) * shiftedGroundState a x := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = collarExcessConstant := ⟨_, rfl⟩
  have hsa : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  refine ⟨max a (2 * (|K| + 1) / Real.sinh (a / 2)), lt_of_lt_of_le ha (le_max_left _ _),
    fun x hx => ?_⟩
  have hxa : a ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hxa
  have hxK : 2 * (|K| + 1) / Real.sinh (a / 2) ≤ x := le_trans (le_max_right _ _) hx
  have h1 : 2 * (|K| + 1) ≤ x * Real.sinh (a / 2) := by
    rwa [div_le_iff₀ hsa] at hxK
  have hsinh : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h2 := mul_le_mul_of_nonneg_left hsinh hsa.le
  have hC := two_mul_source_sub_le_shiftedCollarMass ha.le hxa
  rw [← hK] at hC
  have hlt : Real.sinh (a / 2) * Real.sinh (x / 2) < shiftedCollarMass a x := by
    linarith [le_abs_self K]
  have hiff := foldedSupersolution_shiftedGroundState_iff ha hx0
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd (hiff.mp hcon) (not_le.mpr hlt)

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
