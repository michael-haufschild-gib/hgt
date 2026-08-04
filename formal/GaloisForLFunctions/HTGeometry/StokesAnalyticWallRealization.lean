import GaloisForLFunctions.HTGeometry.StokesCellularCategory
import GaloisForLFunctions.HTGeometry.StokesEquivariantSpectrumIntegrality
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Analytic realization of the finite Stokes-wall labels

For a nonzero leading exponential coefficient `c` and positive integral pole order `k`, the
dominance phase on the real oriented blow-up is

`Re (c * exp (-k * θ * I))`.

This module proves that its zero set on the angle circle consists of exactly `2k` simple walls.
It constructs a bijection from the cellular labels `Fin k × Bool` to that analytic zero set.  The
Boolean coordinate is not formal decoration: it records the two signs of the transverse phase
derivative, hence the two alternating wall orientations.
-/

namespace GaloisForLFunctions
namespace IrregularStokes
namespace AnalyticWall

open CellularMicrolocal
open CellularStokesCategory

noncomputable section

/-- Real lift of the analytic dominance phase determined by a leading coefficient. -/
def liftedStokesPhase (c : ℂ) (k : ℕ) (θ : ℝ) : ℝ :=
  (c * Complex.exp (-((k : ℝ) * θ) * Complex.I)).re

/-- Intrinsic dominance phase on the oriented boundary circle. -/
def stokesPhase (c : ℂ) (k : ℕ) (θ : Real.Angle) : ℝ :=
  ‖c‖ * Real.Angle.cos (((Complex.arg c : ℝ) : Real.Angle) - k • θ)

/-- Actual analytic Stokes walls: zero directions of the leading exponential phase. -/
def AnalyticStokesWall (c : ℂ) (k : ℕ) :=
  {θ : Real.Angle // stokesPhase c k θ = 0}

/-- The two quarter-turn targets of the phase, carrying opposite transverse orientations. -/
def branchTarget : Bool → ℝ
  | false => Real.pi / 2
  | true => -Real.pi / 2

/-- The root with index `j` in one of the two cosine-zero fibers. -/
def labelledWallAngle (c : ℂ) {k : ℕ} (_hk : 0 < k)
    (w : StokesWall k) : Real.Angle :=
  ((((Complex.arg c - branchTarget w.2) / (k : ℝ)) : ℝ) : Real.Angle) +
    (w.1 : ℕ) • (((2 * Real.pi / (k : ℝ)) : ℝ) : Real.Angle)

/-- The combinatorial successor is the actual positive cyclic successor: consecutive labels are
separated by the analytic half-step `π / k` on the oriented boundary circle. -/
theorem labelledWallAngle_nextWall (c : ℂ) {k : ℕ} (hk : 0 < k)
    (w : StokesWall k) :
    labelledWallAngle c hk (nextWall hk w) =
      labelledWallAngle c hk w +
        (((Real.pi / (k : ℝ) : ℝ)) : Real.Angle) := by
  let halfStep : Real.Angle := (((Real.pi / (k : ℝ) : ℝ)) : Real.Angle)
  let step : Real.Angle := (((2 * Real.pi / (k : ℝ) : ℝ)) : Real.Angle)
  let baseFalse : Real.Angle :=
    ((((Complex.arg c - branchTarget false) / (k : ℝ) : ℝ)) : Real.Angle)
  let baseTrue : Real.Angle :=
    ((((Complex.arg c - branchTarget true) / (k : ℝ) : ℝ)) : Real.Angle)
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hbaseFalse : baseFalse + halfStep = baseTrue := by
    rw [show baseFalse =
        ((((Complex.arg c - branchTarget false) / (k : ℝ) : ℝ)) : Real.Angle) by rfl,
      show halfStep = (((Real.pi / (k : ℝ) : ℝ)) : Real.Angle) by rfl,
      ← Real.Angle.coe_add]
    apply congrArg ((↑) : ℝ → Real.Angle)
    simp only [branchTarget]
    field_simp
    ring
  have hbaseTrue : baseTrue + halfStep = baseFalse + step := by
    rw [show baseTrue =
        ((((Complex.arg c - branchTarget true) / (k : ℝ) : ℝ)) : Real.Angle) by rfl,
      show halfStep = (((Real.pi / (k : ℝ) : ℝ)) : Real.Angle) by rfl,
      show baseFalse =
        ((((Complex.arg c - branchTarget false) / (k : ℝ) : ℝ)) : Real.Angle) by rfl,
      show step = (((2 * Real.pi / (k : ℝ) : ℝ)) : Real.Angle) by rfl,
      ← Real.Angle.coe_add, ← Real.Angle.coe_add]
    apply congrArg ((↑) : ℝ → Real.Angle)
    simp only [branchTarget]
    field_simp
    ring
  have hstepZero : k • step = 0 := by
    rw [show step = (((2 * Real.pi / (k : ℝ) : ℝ)) : Real.Angle) by rfl,
      ← Real.Angle.coe_nsmul]
    simp only [nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hk0, Real.Angle.coe_two_pi]
  rcases w with ⟨j, b⟩
  cases b
  · change baseTrue + (j : ℕ) • step =
      (baseFalse + (j : ℕ) • step) + halfStep
    rw [show (baseFalse + (j : ℕ) • step) + halfStep =
        (baseFalse + halfStep) + (j : ℕ) • step by abel,
      hbaseFalse]
  · change baseFalse + (succFin hk j : ℕ) • step =
      (baseTrue + (j : ℕ) • step) + halfStep
    have hmod : (j.val + 1) • step = ((j.val + 1) % k) • step :=
      nsmul_eq_mod_nsmul (j.val + 1) hstepZero
    rw [show (baseTrue + (j : ℕ) • step) + halfStep =
        (baseTrue + halfStep) + (j : ℕ) • step by abel,
      hbaseTrue]
    change baseFalse + ((j.val + 1) % k) • step =
      (baseFalse + step) + j.val • step
    rw [← hmod]
    simp only [add_nsmul, one_nsmul]
    abel

theorem liftedStokesPhase_eq_norm_mul_cos (c : ℂ) (k : ℕ) (θ : ℝ) :
    liftedStokesPhase c k θ = ‖c‖ * Real.cos (Complex.arg c - (k : ℝ) * θ) := by
  calc
    liftedStokesPhase c k θ =
        (c * Complex.exp (-((k : ℝ) * θ) * Complex.I)).re := rfl
    _ = (((‖c‖ : ℝ) : ℂ) * Complex.exp (Complex.arg c * Complex.I) *
        Complex.exp (-((k : ℝ) * θ) * Complex.I)).re := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (((‖c‖ : ℝ) : ℂ) *
        Complex.exp ((Complex.arg c - (k : ℝ) * θ) * Complex.I)).re := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 3
      ring
    _ = ‖c‖ * Real.cos (Complex.arg c - (k : ℝ) * θ) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        show ((Complex.arg c : ℂ) - ((k : ℝ) : ℂ) * (θ : ℂ)) =
            ((Complex.arg c - (k : ℝ) * θ : ℝ) : ℂ) by
          push_cast
          rfl,
        Complex.exp_ofReal_mul_I_re]

theorem liftedStokesPhase_eq_stokesPhase (c : ℂ) (k : ℕ) (θ : ℝ) :
    liftedStokesPhase c k θ = stokesPhase c k (θ : Real.Angle) := by
  rw [liftedStokesPhase_eq_norm_mul_cos]
  unfold stokesPhase
  rw [← Real.Angle.coe_nsmul]
  rw [← Real.Angle.coe_sub, Real.Angle.cos_coe]
  simp only [nsmul_eq_mul]

theorem labelledWallAngle_phase_argument (c : ℂ) {k : ℕ} (hk : 0 < k)
    (w : StokesWall k) :
    (((Complex.arg c : ℝ) : Real.Angle) - k • labelledWallAngle c hk w) =
      ((branchTarget w.2 : ℝ) : Real.Angle) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hbase :
      k • (((Complex.arg c - branchTarget w.2) / (k : ℝ) : ℝ) : Real.Angle) =
        (((Complex.arg c - branchTarget w.2 : ℝ)) : Real.Angle) := by
    rw [← Real.Angle.coe_nsmul]
    simp only [nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hk0]
  have hstep :
      k • (((2 * Real.pi / (k : ℝ) : ℝ)) : Real.Angle) = 0 := by
    rw [← Real.Angle.coe_nsmul]
    simp only [nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hk0, Real.Angle.coe_two_pi]
  have hjstep :
      k • ((w.1 : ℕ) • (((2 * Real.pi / (k : ℝ) : ℝ)) : Real.Angle)) = 0 := by
    rw [nsmul_left_comm, hstep, nsmul_zero]
  rw [labelledWallAngle, nsmul_add, hbase, hjstep, add_zero]
  simp only [Real.Angle.coe_sub]
  abel

theorem labelledWallAngle_mem (c : ℂ) {k : ℕ} (hk : 0 < k)
    (hc : c ≠ 0) (w : StokesWall k) :
    stokesPhase c k (labelledWallAngle c hk w) = 0 := by
  have _hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [stokesPhase, labelledWallAngle_phase_argument c hk w]
  cases w.2
  · rw [branchTarget, Real.Angle.cos_coe, Real.cos_pi_div_two, mul_zero]
  · rw [branchTarget, Real.Angle.cos_coe,
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.cos_pi_div_two, mul_zero]

theorem labelledWallAngle_injective (c : ℂ) {k : ℕ} (hk : 0 < k) :
    Function.Injective (labelledWallAngle c hk) := by
  rintro ⟨i, b⟩ ⟨j, b'⟩ h
  have htarget :
      (((branchTarget b : ℝ) : Real.Angle)) =
        (((branchTarget b' : ℝ) : Real.Angle)) := by
    rw [← labelledWallAngle_phase_argument c hk (i, b),
      ← labelledWallAngle_phase_argument c hk (j, b'), h]
  have hb : b = b' := by
    cases b <;> cases b'
    · rfl
    · exfalso
      have := congrArg Real.Angle.sin htarget
      simp only [branchTarget, Real.Angle.sin_coe] at this
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.sin_neg, Real.sin_pi_div_two] at this
      norm_num at this
    · exfalso
      have := congrArg Real.Angle.sin htarget
      simp only [branchTarget, Real.Angle.sin_coe] at this
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.sin_neg, Real.sin_pi_div_two] at this
      norm_num at this
    · rfl
  subst b'
  apply Prod.ext
  · apply Fin.ext
    let step : Real.Angle := (((2 * Real.pi / (k : ℝ)) : ℝ) : Real.Angle)
    have hstepOrder : addOrderOf step = k := by
      letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
      dsimp [step]
      exact AddCircle.addOrderOf_period_div hk
    have hi : (i : ℕ) < addOrderOf step := by
      rw [hstepOrder]
      exact i.isLt
    have hj : (j : ℕ) < addOrderOf step := by
      rw [hstepOrder]
      exact j.isLt
    have hij : (i : ℕ) • step = (j : ℕ) • step := by
      simpa only [labelledWallAngle, step, Prod.fst, Prod.snd] using add_left_cancel h
    exact nsmul_injOn_Iio_addOrderOf hi hj hij
  · rfl

theorem labelledWallAngle_surjective_analytic (c : ℂ) {k : ℕ} (hk : 0 < k)
    (hc : c ≠ 0) :
    Function.Surjective (fun w : StokesWall k =>
      (⟨labelledWallAngle c hk w, labelledWallAngle_mem c hk hc w⟩ :
        AnalyticStokesWall c k)) := by
  rintro ⟨θ, hθ⟩
  have hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hcos :
      Real.Angle.cos (((Complex.arg c : ℝ) : Real.Angle) - k • θ) = 0 := by
    exact (mul_eq_zero.mp hθ).resolve_left hnorm
  rcases Real.Angle.cos_eq_zero_iff.mp hcos with hplus | hminus
  · let base : Real.Angle :=
      ((((Complex.arg c - branchTarget false) / (k : ℝ)) : ℝ) : Real.Angle)
    have hbase : k • base =
        ((Complex.arg c : ℝ) : Real.Angle) - ((branchTarget false : ℝ) : Real.Angle) := by
      dsimp [base]
      rw [← Real.Angle.coe_nsmul]
      simp only [nsmul_eq_mul]
      rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hk.ne')]
      exact Real.Angle.coe_sub _ _
    have hphase :
        ((Complex.arg c : ℝ) : Real.Angle) - k • θ =
          ((branchTarget false : ℝ) : Real.Angle) := by
      simpa [branchTarget] using hplus
    have hθbase : k • θ = k • base := by
      rw [hbase]
      apply (eq_sub_iff_add_eq).2
      rw [add_comm]
      exact (sub_eq_iff_eq_add).mp hphase |>.symm
    obtain ⟨j, hj⟩ := (Real.Angle.nsmul_eq_iff hk.ne').mp hθbase
    refine ⟨(j, false), Subtype.ext ?_⟩
    simpa [labelledWallAngle, base] using hj.symm
  · let base : Real.Angle :=
      ((((Complex.arg c - branchTarget true) / (k : ℝ)) : ℝ) : Real.Angle)
    have hbase : k • base =
        ((Complex.arg c : ℝ) : Real.Angle) - ((branchTarget true : ℝ) : Real.Angle) := by
      dsimp [base]
      rw [← Real.Angle.coe_nsmul]
      simp only [nsmul_eq_mul]
      rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hk.ne')]
      exact Real.Angle.coe_sub _ _
    have hphase :
        ((Complex.arg c : ℝ) : Real.Angle) - k • θ =
          ((branchTarget true : ℝ) : Real.Angle) := by
      simpa [branchTarget] using hminus
    have hθbase : k • θ = k • base := by
      rw [hbase]
      apply (eq_sub_iff_add_eq).2
      rw [add_comm]
      exact (sub_eq_iff_eq_add).mp hphase |>.symm
    obtain ⟨j, hj⟩ := (Real.Angle.nsmul_eq_iff hk.ne').mp hθbase
    refine ⟨(j, true), Subtype.ext ?_⟩
    simpa [labelledWallAngle, base] using hj.symm

/-- Canonical equivalence between finite cellular wall labels and actual analytic Stokes walls. -/
noncomputable def cellularWallEquivAnalytic (c : ℂ) {k : ℕ} (hk : 0 < k)
    (hc : c ≠ 0) : StokesWall k ≃ AnalyticStokesWall c k :=
  Equiv.ofBijective
    (fun w => ⟨labelledWallAngle c hk w, labelledWallAngle_mem c hk hc w⟩)
    ⟨fun _ _ h => labelledWallAngle_injective c hk (Subtype.ext_iff.mp h),
      labelledWallAngle_surjective_analytic c hk hc⟩

theorem analyticStokesWall_card (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0) :
    Nat.card (AnalyticStokesWall c k) = 2 * k := by
  rw [Nat.card_congr (cellularWallEquivAnalytic c hk hc).symm]
  simpa [Nat.card_eq_fintype_card] using stokesWall_card k

/-! ## Actual leading phases of coefficient pairs -/

/-- Leading coefficient of the exponential difference between two distinct finite Puiseux
branches, taken at their coefficient-generated highest contact. -/
def branchPairLeadingCoefficient {m K N : ℕ} (p : FinitePuiseuxFamily m K N)
    {i j : Fin m} (_hij : i ≠ j) : ℂ :=
  p.coeff i ⟨p.contactNumerator i j, Nat.lt_succ_of_le (p.contactNumerator_le i j)⟩ -
    p.coeff j ⟨p.contactNumerator i j, Nat.lt_succ_of_le (p.contactNumerator_le i j)⟩

theorem branchPairLeadingCoefficient_ne_zero {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :
    branchPairLeadingCoefficient p hij ≠ 0 := by
  exact sub_ne_zero.mpr (p.coeff_ne_at_contact hij)

/-- Every distinct pair of coefficient-generated Puiseux branches has its finite wall labels
canonically equivalent to the analytic Stokes walls of its actual leading exponential
difference. -/
noncomputable def branchPairWallEquivAnalytic {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) :
    StokesWall (p.contactNumerator i j) ≃
      AnalyticStokesWall (branchPairLeadingCoefficient p hij)
        (p.contactNumerator i j) :=
  cellularWallEquivAnalytic (branchPairLeadingCoefficient p hij)
    (p.contactNumerator_pos_of_ne hij) (branchPairLeadingCoefficient_ne_zero p hij)

theorem hasDerivAt_liftedStokesPhase (c : ℂ) (k : ℕ) (θ : ℝ) :
    HasDerivAt (liftedStokesPhase c k)
      (‖c‖ * (k : ℝ) * Real.sin (Complex.arg c - (k : ℝ) * θ)) θ := by
  rw [show liftedStokesPhase c k =
      fun t => ‖c‖ * Real.cos (Complex.arg c - (k : ℝ) * t) by
    funext t
    exact liftedStokesPhase_eq_norm_mul_cos c k t]
  have hinner : HasDerivAt (fun t : ℝ => Complex.arg c - (k : ℝ) * t)
      (-(k : ℝ)) θ := by
    change HasDerivAt
      ((fun _ : ℝ => Complex.arg c) - fun y : ℝ => (k : ℝ) * id y)
      (-(k : ℝ)) θ
    simpa only [zero_sub, mul_one] using (hasDerivAt_const θ (Complex.arg c)).sub
      ((hasDerivAt_id θ).const_mul (k : ℝ))
  have h := hinner.cos.const_mul ‖c‖
  have hderiv :
      ‖c‖ * (-Real.sin (Complex.arg c - (k : ℝ) * θ) * -(k : ℝ)) =
        ‖c‖ * (k : ℝ) * Real.sin (Complex.arg c - (k : ℝ) * θ) := by
    ring
  rw [← hderiv]
  exact h

theorem analyticStokesWall_simple (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (w : AnalyticStokesWall c k) :
    ‖c‖ * (k : ℝ) *
      Real.sin (Complex.arg c - (k : ℝ) * w.1.toReal) ≠ 0 := by
  have hlift : liftedStokesPhase c k w.1.toReal = 0 := by
    rw [liftedStokesPhase_eq_stokesPhase, Real.Angle.coe_toReal]
    exact w.2
  rw [liftedStokesPhase_eq_norm_mul_cos] at hlift
  have hnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hcos : Real.cos (Complex.arg c - (k : ℝ) * w.1.toReal) = 0 :=
    (mul_eq_zero.mp hlift).resolve_left hnorm
  have hsin : Real.sin (Complex.arg c - (k : ℝ) * w.1.toReal) ≠ 0 := by
    intro hs
    have hsquares := Real.sin_sq_add_cos_sq (Complex.arg c - (k : ℝ) * w.1.toReal)
    rw [hs, hcos] at hsquares
    norm_num at hsquares
  exact mul_ne_zero (mul_ne_zero hnorm (Nat.cast_ne_zero.mpr hk.ne')) hsin

theorem labelledWall_transverse_sign (c : ℂ) {k : ℕ} (hk : 0 < k)
    (w : StokesWall k) :
    Real.Angle.sin
        (((Complex.arg c : ℝ) : Real.Angle) - k • labelledWallAngle c hk w) =
      if w.2 then -1 else 1 := by
  rw [labelledWallAngle_phase_argument c hk w]
  cases w.2
  · rw [branchTarget, Real.Angle.sin_coe, Real.sin_pi_div_two]
    rfl
  · rw [branchTarget, Real.Angle.sin_coe,
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
    rfl

end
end AnalyticWall
end IrregularStokes
end GaloisForLFunctions
