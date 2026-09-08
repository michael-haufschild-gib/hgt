import GaloisForLFunctions.RHTower.ArchimedeanGammaModule

/-!
# Associated tensor charges of the actual difference-differential modules

The associated-representation construction in arXiv:2404.10461 transports one
connection into tensor powers and duals. Here every integer charge is constructed
for the existing rank-one datum, with all nonvanishing and differentiation fields
proved. The Gamma and completed-zeta applications use explicit coordinates on their
proved domains, so their statements have no unproved domain premises.
-/

noncomputable section
namespace GaloisForLFunctions

/-- All associated integer tensor charges, including negative dual powers. -/
def RankOneShiftDiffDatum.charge (M : RankOneShiftDiffDatum) (n : ℤ) : RankOneShiftDiffDatum where
  gen := fun s => M.gen s ^ n
  shift := M.shift
  mult := fun s => M.mult s ^ n
  conn := fun s => (n : ℂ) * M.conn s
  domain := M.domain
  shift_stable := M.shift_stable
  gen_ne_zero := fun s hs => zpow_ne_zero n (M.gen_ne_zero s hs)
  gen_differentiableAt := fun s hs =>
    (M.gen_differentiableAt s hs).zpow (Or.inl (M.gen_ne_zero s hs))
  gen_shift := fun s hs => by rw [M.gen_shift s hs, mul_zpow]
  gen_conn := fun s hs => by
    rw [logDeriv_fun_zpow (M.gen_differentiableAt s hs), M.gen_conn s hs]

/-- Every actual shift link is nonzero on the datum's domain. -/
theorem rankOneShift_multiplier_nonzero (M : RankOneShiftDiffDatum) :
    ∀ s ∈ M.domain, M.mult s ≠ 0 := by
  intro s hs hm
  have hz := M.gen_shift s hs
  rw [hm, zero_mul] at hz
  exact M.gen_ne_zero (M.shift s) (M.shift_stable s hs) hz

/-- All tensor grades inherit the same base shift, with additive infinitesimal charges. -/
theorem rankOneCharge_connection_add (M : RankOneShiftDiffDatum) (m n : ℤ) :
    (M.charge (m+n)).conn = fun s => (M.charge m).conn s + (M.charge n).conn s := by
  funext s
  simp [RankOneShiftDiffDatum.charge, add_mul]

/-- Tensor products of associated charges agree on generators, links, and connections. -/
theorem rankOneCharge_tensor_laws (M : RankOneShiftDiffDatum) (m n : ℤ) :
    Set.EqOn (M.charge (m+n)).gen
      ((M.charge m).tensor (M.charge n) rfl).gen M.domain ∧
    Set.EqOn (M.charge (m+n)).mult
      ((M.charge m).tensor (M.charge n) rfl).mult M.domain ∧
    (M.charge (m+n)).conn = ((M.charge m).tensor (M.charge n) rfl).conn := by
  refine ⟨?_, ?_, rankOneCharge_connection_add M m n⟩
  · intro s hs
    exact zpow_add₀ (M.gen_ne_zero s hs) m n
  · intro s hs
    exact zpow_add₀ (rankOneShift_multiplier_nonzero M s hs) m n

/-- Dual cancellation is valid for the full actual module, not merely its connection formula. -/
theorem rankOneCharge_dual_cancellation (M : RankOneShiftDiffDatum) (n : ℤ) :
    Set.EqOn ((M.charge n).tensor (M.charge (-n)) rfl).gen (fun _ => 1) M.domain ∧
    Set.EqOn ((M.charge n).tensor (M.charge (-n)) rfl).mult (fun _ => 1) M.domain ∧
    ((M.charge n).tensor (M.charge (-n)) rfl).conn = (fun _ => 0) := by
  have h := rankOneCharge_tensor_laws M n (-n)
  simpa [RankOneShiftDiffDatum.charge, RankOneShiftDiffDatum.tensor] using
    And.intro h.1.symm (And.intro h.2.1.symm h.2.2.symm)

/-- Consecutive matter charges recover the generating section on its entire proved domain. -/
theorem rankOneCharge_consecutive_reconstruct_gen (M : RankOneShiftDiffDatum) (n : ℤ) :
    Set.EqOn (fun s => (M.charge (n+1)).gen s / (M.charge n).gen s) M.gen M.domain := by
  intro s hs
  change M.gen s ^ (n+1) / M.gen s ^ n = M.gen s
  rw [zpow_add₀ (M.gen_ne_zero s hs), zpow_one]
  exact mul_div_cancel_left₀ (M.gen s) (zpow_ne_zero n (M.gen_ne_zero s hs))

/-- Consecutive matter charges also recover every discrete transport link. -/
theorem rankOneCharge_consecutive_reconstruct_link (M : RankOneShiftDiffDatum) (n : ℤ) :
    Set.EqOn (fun s => (M.charge (n+1)).mult s / (M.charge n).mult s) M.mult M.domain := by
  intro s hs
  change M.mult s ^ (n+1) / M.mult s ^ n = M.mult s
  rw [zpow_add₀ (rankOneShift_multiplier_nonzero M s hs), zpow_one]
  exact mul_div_cancel_left₀ (M.mult s) (zpow_ne_zero n (rankOneShift_multiplier_nonzero M s hs))

/-- The same consecutive-charge reconstruction recovers the infinitesimal connection. -/
theorem rankOneCharge_consecutive_reconstruct_connection (M : RankOneShiftDiffDatum) (n : ℤ) :
    (fun s => (M.charge (n+1)).conn s - (M.charge n).conn s) = M.conn := by
  funext s
  simp [RankOneShiftDiffDatum.charge, add_mul]

/-- Global coordinates on the right half-plane, with no external positivity premise. -/
def gomesPositiveHalfPlane (x y : ℝ) : ℂ := (Real.exp x : ℂ) + Complex.I * (y : ℂ)

/-- Positivity is proved by construction for every real coordinate pair. -/
theorem gomesPositiveHalfPlane_re (x y : ℝ) : 0 < (gomesPositiveHalfPlane x y).re := by
  simpa only [gomesPositiveHalfPlane, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    using Real.exp_pos x

/-- Every integer associated charge of Gamma has the inherited shift and logarithmic connection. -/
theorem gamma_associated_charge_laws (n : ℤ) (x y : ℝ) :
    Complex.Gammaℝ (gomesPositiveHalfPlane x y) ^ n ≠ 0 ∧
    Complex.Gammaℝ (gomesPositiveHalfPlane x y + 2) ^ n =
      (gomesPositiveHalfPlane x y / (2 * (Real.pi : ℂ))) ^ n *
        Complex.Gammaℝ (gomesPositiveHalfPlane x y) ^ n ∧
    logDeriv (fun z => Complex.Gammaℝ z ^ n) (gomesPositiveHalfPlane x y) =
      (n : ℂ) * gammaRealLogConnection (gomesPositiveHalfPlane x y) := by
  let s := gomesPositiveHalfPlane x y
  have hs : s ∈ archimedeanGammaModule.domain := gomesPositiveHalfPlane_re x y
  exact ⟨(archimedeanGammaModule.charge n).gen_ne_zero s hs,
    (archimedeanGammaModule.charge n).gen_shift s hs,
    (archimedeanGammaModule.charge n).gen_conn s hs⟩

/-- The completed Euler-product module inherits every integer tensor charge of its connection. -/
theorem completedZeta_associated_charge_connection (n : ℤ) (x y : ℝ) :
    logDeriv (fun z => completedZetaModule.gen z ^ n) (1 + gomesPositiveHalfPlane x y) =
      (n : ℂ) * (gammaRealLogConnection (1 + gomesPositiveHalfPlane x y) +
        logDeriv riemannZeta (1 + gomesPositiveHalfPlane x y)) := by
  have hp := gomesPositiveHalfPlane_re x y
  have hs : 1 + gomesPositiveHalfPlane x y ∈ completedZetaModule.domain := by
    change 0 < (1 + gomesPositiveHalfPlane x y).re ∧ 1 < (1 + gomesPositiveHalfPlane x y).re
    simp only [Complex.add_re, Complex.one_re]
    constructor <;> linarith
  exact (completedZetaModule.charge n).gen_conn _ hs

end GaloisForLFunctions
