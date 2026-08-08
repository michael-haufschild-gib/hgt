import GaloisForLFunctions.HTGeometry.JacobiThetaDivisorSimple
import GaloisForLFunctions.HTGeometry.JacobiThetaExactDivisor
import GaloisForLFunctions.HTGeometry.MeromorphicLogDerivLocalForm
import GaloisForLFunctions.HTGeometry.MeromorphicTheta
import GaloisForLFunctions.HTGeometry.EllipticGammaConeSource

/-!
# The complete principal part of the theta source

The zeros of `jacobiTheta₂` are the odd half-period lattice orbit, and the `z`-derivative does not
vanish on that orbit, so every zero is simple.  Consequently the theta source `δ log θ` has a simple
pole of residue exactly `1` at each point of the orbit and no singularity anywhere else: its whole
Laurent principal part is one term.

This is the `ζ`-shaped atom of a rank-three mixed-constraint class — `1`-periodic, dropping by the
constant `2πi` under a quasiperiod step, with a single simple pole per lattice cell.

* `analyticOrderAt_jacobiTheta₂_eq_one` — the zeros are simple;
* `thetaSource`, `thetaSource_periodic`, `thetaSource_shift`;
* `laurentCoeff_thetaSource_lattice` — residue `1`;
* `laurentCoeff_thetaSource_of_le`, `laurentCoeff_thetaSource_of_notMem` — and nothing else.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

open GaloisForLFunctions

noncomputable section

theorem analyticAt_jacobiTheta₂_fst {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    AnalyticAt ℂ (jacobiTheta₂ · τ) z :=
  jacobiTheta₂_analyticOnNhd_fst τ hτ z (Set.mem_univ z)

theorem deriv_jacobiTheta₂_fst {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    deriv (jacobiTheta₂ · τ) z = jacobiTheta₂' z τ :=
  (hasDerivAt_jacobiTheta₂_fst z hτ).deriv

/-- **Every theta zero is simple.**  The value vanishes on the odd half-period orbit while the
`z`-derivative does not. -/
theorem analyticOrderAt_jacobiTheta₂_eq_one {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    analyticOrderAt (jacobiTheta₂ · τ) (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) = 1 := by
  have hzero : jacobiTheta₂ (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) τ = 0 :=
    jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero τ m n
  have hne : deriv (jacobiTheta₂ · τ) (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) ≠ 0 := by
    rw [deriv_jacobiTheta₂_fst hτ]
    exact jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero hτ m n
  have hiff := analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (analyticAt_jacobiTheta₂_fst hτ (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ)) (n := 1)
  rw [Nat.cast_one] at hiff
  rw [hiff]
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    simpa using hzero
  · simpa [iteratedDeriv_one] using hne

theorem meromorphicOrderAt_jacobiTheta₂_lattice {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    meromorphicOrderAt (jacobiTheta₂ · τ) (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ)
      = ((1 : ℤ) : ℤ) := by
  rw [(analyticAt_jacobiTheta₂_fst hτ _).meromorphicOrderAt_eq,
    analyticOrderAt_jacobiTheta₂_eq_one hτ m n]
  rfl

theorem meromorphicOrderAt_jacobiTheta₂_of_notMem {τ : ℂ} (hτ : 0 < τ.im) {z : ℂ}
    (hz : ¬ ∃ m n : ℤ, z = thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) :
    meromorphicOrderAt (jacobiTheta₂ · τ) z = ((0 : ℤ) : ℤ) := by
  have hne : jacobiTheta₂ z τ ≠ 0 := fun h =>
    hz ((jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hτ).mp h)
  have hord : analyticOrderAt (fun x => jacobiTheta₂ x τ) z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hne)
  rw [(analyticAt_jacobiTheta₂_fst hτ z).meromorphicOrderAt_eq, hord]
  rfl

theorem exists_meromorphicOrderAt_jacobiTheta₂ {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    ∃ k : ℤ, meromorphicOrderAt (jacobiTheta₂ · τ) z = (k : ℤ) := by
  by_cases h : ∃ m n : ℤ, z = thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ
  · obtain ⟨m, n, rfl⟩ := h
    exact ⟨1, meromorphicOrderAt_jacobiTheta₂_lattice hτ m n⟩
  · exact ⟨0, meromorphicOrderAt_jacobiTheta₂_of_notMem hτ h⟩

/-! ### The source -/

/-- The theta source `δ log θ`. -/
def thetaSource (τ : ℂ) : ℂ → ℂ := logDeriv (jacobiTheta₂ · τ)

/-- **The theta source is `1`-periodic.** -/
theorem thetaSource_periodic (τ z : ℂ) : thetaSource τ (z + 1) = thetaSource τ z :=
  logDeriv_of_periodic (fun w => jacobiTheta₂_add_left w τ) z

theorem hasDerivAt_thetaQuasiFactor (τ z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * w)))
      (Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * z)) *
        (-(2 * (Real.pi : ℂ) * Complex.I))) z := by
  have h1 : HasDerivAt (fun w : ℂ => τ + 2 * w) 2 z := by
    simpa using ((hasDerivAt_id z).const_mul (2 : ℂ)).const_add τ
  have hinner : HasDerivAt (fun w : ℂ => -(Real.pi : ℂ) * Complex.I * (τ + 2 * w))
      (-(2 * (Real.pi : ℂ) * Complex.I)) z := by
    have h2 := h1.const_mul (-(Real.pi : ℂ) * Complex.I)
    have hval : -(Real.pi : ℂ) * Complex.I * 2 = -(2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [hval] at h2
    exact h2
  exact hinner.cexp

/-- The quasiperiod multiplier has constant logarithmic derivative `-2πi`. -/
theorem logDeriv_thetaQuasiFactor (τ z : ℂ) :
    logDeriv (fun w : ℂ => Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * w))) z
      = -(2 * (Real.pi : ℂ) * Complex.I) := by
  have hne : Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * z)) ≠ 0 := Complex.exp_ne_zero _
  rw [logDeriv_apply, (hasDerivAt_thetaQuasiFactor τ z).deriv]
  field_simp

/-- **The theta source drops by `2πi` under a quasiperiod step**, off the divisor. -/
theorem thetaSource_shift {τ : ℂ} (hτ : 0 < τ.im) {z : ℂ} (hz : jacobiTheta₂ z τ ≠ 0) :
    thetaSource τ (z + τ) = thetaSource τ z - 2 * (Real.pi : ℂ) * Complex.I := by
  have hfun : (fun w : ℂ => jacobiTheta₂ (w + τ) τ)
      = fun w : ℂ => Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * w)) * jacobiTheta₂ w τ := by
    funext w
    exact jacobiTheta₂_add_left' w τ
  have hE : Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * z)) ≠ 0 := Complex.exp_ne_zero _
  have hd1 : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ + 2 * w))) z :=
    (hasDerivAt_thetaQuasiFactor τ z).differentiableAt
  have hd2 : DifferentiableAt ℂ (jacobiTheta₂ · τ) z :=
    (hasDerivAt_jacobiTheta₂_fst z hτ).differentiableAt
  rw [thetaSource, ← logDeriv_comp_add_const (jacobiTheta₂ · τ) τ z, hfun,
    logDeriv_mul z hE hz hd1 hd2, logDeriv_thetaQuasiFactor]
  ring

/-! ### Meromorphy and the exact principal-part data -/

theorem analyticAt_deriv_jacobiTheta₂_fst {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    AnalyticAt ℂ (deriv (jacobiTheta₂ · τ)) z :=
  (jacobiTheta₂_analyticOnNhd_fst τ hτ).deriv z (Set.mem_univ z)

theorem meromorphicAt_thetaSource {τ : ℂ} (hτ : 0 < τ.im) (z : ℂ) :
    MeromorphicAt (thetaSource τ) z :=
  (analyticAt_deriv_jacobiTheta₂_fst hτ z).meromorphicAt.div
    (analyticAt_jacobiTheta₂_fst hτ z).meromorphicAt

theorem meromorphicOn_thetaSource {τ : ℂ} (hτ : 0 < τ.im) :
    MeromorphicOn (thetaSource τ) Set.univ :=
  fun z _ => meromorphicAt_thetaSource hτ z

/-- **The theta source has residue one at every point of the divisor.** -/
theorem laurentCoeff_thetaSource_lattice {τ : ℂ} (hτ : 0 < τ.im) (m n : ℤ) :
    laurentCoeff (thetaSource τ) (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) (-1) = 1 := by
  have h := laurentCoeff_logDeriv_eq_order
    ((analyticAt_jacobiTheta₂_fst hτ (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ)).meromorphicAt)
    (meromorphicOrderAt_jacobiTheta₂_lattice hτ m n)
  rw [thetaSource, h]
  norm_num

/-- **The theta source has no coefficient below the residue.** -/
theorem laurentCoeff_thetaSource_of_le {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    laurentCoeff (thetaSource τ) w ℓ = 0 := by
  obtain ⟨k, hk⟩ := exists_meromorphicOrderAt_jacobiTheta₂ hτ w
  exact laurentCoeff_logDeriv_eq_zero_of_le ((analyticAt_jacobiTheta₂_fst hτ w).meromorphicAt) hk hℓ

/-- **Off the divisor the theta source is analytic.** -/
theorem laurentCoeff_thetaSource_of_notMem {τ : ℂ} (hτ : 0 < τ.im) {w : ℂ}
    (hw : ¬ ∃ m n : ℤ, w = thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) {ℓ : ℤ} (hℓ : ℓ < 0) :
    laurentCoeff (thetaSource τ) w ℓ = 0 := by
  rcases eq_or_lt_of_le (by omega : ℓ ≤ -1) with hone | hlt
  · have h := laurentCoeff_logDeriv_eq_order ((analyticAt_jacobiTheta₂_fst hτ w).meromorphicAt)
      (meromorphicOrderAt_jacobiTheta₂_of_notMem hτ hw)
    rw [thetaSource, hone, h]
    norm_num
  · exact laurentCoeff_thetaSource_of_le hτ w (by omega)

/-! ### The derivative -/

theorem deriv_thetaSource_periodic_one (τ z : ℂ) :
    deriv (thetaSource τ) (z + 1) = deriv (thetaSource τ) z := by
  have hfun : (fun w => thetaSource τ (w + 1)) = thetaSource τ := funext (thetaSource_periodic τ)
  have hd : deriv (fun w : ℂ => thetaSource τ (w + 1)) z = deriv (thetaSource τ) (z + 1) :=
    deriv_comp_add_const (thetaSource τ) 1 z
  rw [hfun] at hd
  exact hd.symm

end

end GaloisForLFunctions.HTGeometry
