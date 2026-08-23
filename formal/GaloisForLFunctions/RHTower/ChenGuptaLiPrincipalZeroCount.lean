import GaloisForLFunctions.RHTower.ChenGuptaLiPrincipalHighOrdinate
import GaloisForLFunctions.RHTower.EulerUnitTangent
import GaloisForLFunctions.RHTower.SeamStripRamification
import GaloisForLFunctions.RHTower.XiZeroCountJensenBound
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity

/-!
# Chen--Gupta--Li principal-residue zero census

This closes the principal-character zero count used in CGL Section 12.1.
Every principal Dirichlet `L`-zero in the critical strip is an actual `ξ`-zero:
the finite Euler factors are nonzero there.  The logarithmic Gamma head from
`ChenGuptaLiPrincipalHighOrdinate` then confines every large-residue zero to a
disc of radius `O(log X)`, and Jensen's formula gives the unconditional
`O(log² X)` packet count.

No RH, zero-density, zero-free-region, or moment premise is used.
-/

open Complex LSeries DirichletCharacter Metric Set MeromorphicOn
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A principal Dirichlet `L`-zero in the critical strip is a Riemann-zeta
zero.  The finite Euler correction cannot vanish in the positive half-plane. -/
theorem cglPrincipalLZero_riemannZeta_eq_zero
    {q : ℕ} (z : CGLPrincipalCriticalStripLZero q) :
    riemannZeta z.point = 0 := by
  letI : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
  have hL : DirichletCharacter.LFunctionTrivChar (q + 1) z.point = 0 := by
    change DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ (q + 1)) z.point = 0
    simpa only [z.character_eq_one] using z.vanishes
  have hEuler :
      (∏ p ∈ (q + 1).primeFactors, (1 - (p : ℂ) ^ (-z.point))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact one_sub_prime_cpow_neg_ne_zero hpprime.two_le (by linarith [z.half_le])
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta z.point_ne_one] at hL
  exact (mul_eq_zero.mp hL).resolve_left hEuler

/-- A principal Dirichlet `L`-zero in the critical strip is an actual completed
`ξ`-zero. -/
theorem cglPrincipalLZero_xi_eq_zero
    {q : ℕ} (z : CGLPrincipalCriticalStripLZero q) :
    xi z.point = 0 := by
  exact (xi_zero_iff_zeta_zero_of_mem_strip
    (by linarith [z.half_le]) z.lt_one).mpr
      (cglPrincipalLZero_riemannZeta_eq_zero z)

/-- **CGL Section 12.1, principal census.**  Any finite injective packet of
positive-ordinate principal zeros whose CGL principal residues retain a fixed
positive size has cardinality `O(log²(X+2))`.  The constant is independent of
the modulus, detector length, packet size, and packet itself. -/
theorem exists_card_cglPrincipalLargeResidues_le_log_sq
    {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 0 < B ∧ ∀ (X q R : ℕ)
      (z : Fin R → CGLPrincipalCriticalStripLZero q),
      Function.Injective (fun r => (z r).point) →
      (∀ r, 0 < (z r).point.im) →
      (∀ r, η ≤ ‖cglPrincipalRegularizedMellinFactor X q (z r)
        (cglPrincipalPole (z r))‖) →
      (R : ℝ) ≤ B * Real.log ((X : ℝ) + 2) ^ 2 := by
  obtain ⟨A, K, hA, hK, hhead⟩ :=
    cglPrincipalRegularizedMellinFactor_large_forces_logarithmic_ordinate hη
  obtain ⟨C, hC, hgrow⟩ := orderOneEnvelope_xi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B0 : ℝ := 1 / Real.log 2 + A * (Real.log K / Real.log 2 + 1)
  let B1 : ℝ := 3 / Real.log 2 + 2 * B0
  let B2 : ℝ := 4 / Real.log 2 + 2 * B0
  let B : ℝ := (C * B1 * B2 + 1 / Real.log 2) / Real.log 2
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hB0 : 0 < B0 := by
    dsimp [B0]
    positivity
  have hB1 : 0 < B1 := by
    dsimp [B1]
    positivity
  have hB2 : 0 < B2 := by
    dsimp [B2]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    have hnum : 0 < C * B1 * B2 + 1 / Real.log 2 := by positivity
    exact div_pos hnum hlog2
  refine ⟨B, hB, ?_⟩
  intro X q R z hinj him hlarge
  let L : ℝ := Real.log ((X : ℝ) + 2)
  let H : ℝ := 1 + A * Real.log (K * ((X : ℝ) + 1))
  let r : ℝ := 1 + H
  have hX1 : 0 < (X : ℝ) + 1 := by positivity
  have hX2 : 2 ≤ (X : ℝ) + 2 := by
    have hX0 : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
    linarith
  have hL2 : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hX2
  have hL : 0 < L := hlog2.trans_le hL2
  have hlogX1 : Real.log ((X : ℝ) + 1) ≤ L := by
    dsimp [L]
    exact Real.log_le_log hX1 (by linarith)
  have hlogmul : Real.log (K * ((X : ℝ) + 1)) =
      Real.log K + Real.log ((X : ℝ) + 1) :=
    Real.log_mul (by linarith [hK]) hX1.ne'
  have hone : 1 ≤ (1 / Real.log 2) * L := by
    calc
      1 = (1 / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (1 / Real.log 2) * L := by gcongr
  have hlogK_le : Real.log K ≤ (Real.log K / Real.log 2) * L := by
    calc
      Real.log K = (Real.log K / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (Real.log K / Real.log 2) * L := by gcongr
  have hH : H ≤ B0 * L := by
    calc
      H = 1 + A * (Real.log K + Real.log ((X : ℝ) + 1)) := by
        dsimp [H]
        rw [hlogmul]
      _ ≤ (1 / Real.log 2) * L +
          A * ((Real.log K / Real.log 2) * L + L) := by
            gcongr
      _ = B0 * L := by
        dsimp [B0]
        ring
  have hr0 : 0 < r := by
    dsimp [r, H]
    have : 0 ≤ Real.log (K * ((X : ℝ) + 1)) :=
      Real.log_nonneg (by nlinarith [hK])
    positivity
  have hr : r ≤ B0 * L + 1 := by linarith [hH]
  have hr' : r ≤ B0 * L + (1 / Real.log 2) * L := by
    linarith [hone]
  have hcardZ : (R : ℤ) ≤
      xiRegionOrderSum (closedBall (0 : ℂ) r) := by
    have h := card_le_sum_divisor_of_finite_zeros
      (f := xi) (c := 0) xi_differentiable (by simp [xi_zero])
      (Finset.univ : Finset (Fin R)) (fun i => (z i).point)
      (fun _ _ _ _ hij => hinj hij) (r := r) ?_ ?_
    · simpa [xiRegionOrderSum] using h
    · intro i _
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      have hre0 : 0 ≤ (z i).point.re := by linarith [(z i).half_le]
      have hre : |(z i).point.re| < 1 := by
        rw [abs_of_nonneg hre0]
        exact (z i).lt_one
      have himabs : |(z i).point.im| < H := hhead X q (z i) (hlarge i)
      exact le_of_lt (calc
        ‖(z i).point‖ ≤ |(z i).point.re| + |(z i).point.im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ < 1 + H := add_lt_add hre himabs
        _ = r := rfl)
    · intro i _
      exact cglPrincipalLZero_xi_eq_zero (z i)
  have hcard : (R : ℝ) ≤ (xiRegionOrderSum (closedBall (0 : ℂ) r) : ℝ) := by
    exact_mod_cast hcardZ
  have hjensen := xiRegionOrderSum_closedBall_le hC hgrow hr0
  have hlinear1 : 1 + 2 * r ≤ B1 * L := by
    calc
      1 + 2 * r ≤ (1 / Real.log 2) * L +
          2 * (B0 * L + (1 / Real.log 2) * L) := by linarith
      _ = B1 * L := by
        dsimp [B1]
        ring
  have hlinear2 : 2 + 2 * r ≤ B2 * L := by
    calc
      2 + 2 * r ≤ 2 * ((1 / Real.log 2) * L) +
          2 * (B0 * L + (1 / Real.log 2) * L) := by linarith
      _ = B2 * L := by
        dsimp [B2]
        ring
  have hlogr : Real.log (2 + 2 * r) ≤ B2 * L := by
    have harg : 0 < 2 + 2 * r := by positivity
    calc
      Real.log (2 + 2 * r) ≤ (2 + 2 * r) - 1 :=
        Real.log_le_sub_one_of_pos harg
      _ ≤ 2 + 2 * r := by linarith
      _ ≤ B2 * L := hlinear2
  have hterm : C * (1 + 2 * r) * Real.log (2 + 2 * r) ≤
      C * B1 * B2 * L ^ 2 := by
    calc
      C * (1 + 2 * r) * Real.log (2 + 2 * r) ≤
          C * (B1 * L) * (B2 * L) := by
            gcongr
            exact Real.log_nonneg (by linarith [hr0])
      _ = C * B1 * B2 * L ^ 2 := by ring
  have hconst : Real.log 2 ≤ (1 / Real.log 2) * L ^ 2 := by
    have hsq : Real.log 2 ^ 2 ≤ L ^ 2 := by nlinarith
    calc
      Real.log 2 = (1 / Real.log 2) * Real.log 2 ^ 2 := by field_simp
      _ ≤ (1 / Real.log 2) * L ^ 2 := by gcongr
  calc
    (R : ℝ) ≤ (xiRegionOrderSum (closedBall (0 : ℂ) r) : ℝ) := hcard
    _ ≤ (C * (1 + 2 * r) * Real.log (2 + 2 * r) + Real.log 2) /
        Real.log 2 := hjensen
    _ ≤ (C * B1 * B2 * L ^ 2 + (1 / Real.log 2) * L ^ 2) /
        Real.log 2 := div_le_div_of_nonneg_right (add_le_add hterm hconst) hlog2.le
    _ = B * Real.log ((X : ℝ) + 2) ^ 2 := by
      dsimp [B, L]
      ring

end

end RHTower
