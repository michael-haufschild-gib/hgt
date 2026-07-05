/-
The off-line domination floor for the certificate carrier.

The finite Hardy identity shows the certificate carrier `gN = D + zetaChi·D(1−·)` cannot be floored on
the critical line — there the two approximate-functional-equation halves have equal modulus
(`‖zetaChi·D(1−z)‖ = ‖D z‖`), so `gN` genuinely vanishes at its Hardy zeros. Off the line the halves
separate: the exact χ-modulus `‖zetaChi z‖ = π^{Re z−½}·‖Γ((1−z)/2)‖/‖Γ(z/2)‖` carries a vertical
decay (Stirling: `≍ (t/2π)^{½−Re z}`), so one half strictly dominates and a genuine floor
`‖gN‖ > ε` holds. This is the floor the pinning gates can actually have; it is a pointwise relative
domination (vacuous on the line, attainable off it), not a uniform floor. The domination inequality
itself is classical zero-free-region-grade input.
-/
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.DeckMultiZero
open Complex
namespace RHTower

/-- **The correct off-line floor mechanism.** If at every point of `S` the reflected AFE term is
strictly dominated by the Dirichlet part with margin `ε` — `‖zetaChi z·D(1−z)‖ + ε < ‖D z‖` — then the
certificate carrier is floored: `CarrierFloorOn S N ε`. Reverse triangle on `gN = D + zetaChi·D(1−·)`.
Unlike a uniform-`t₀` floor this is a POINTWISE relative domination: it can hold off the critical line
(where `‖D(1−z)‖ ≠ ‖D z‖` and `‖zetaChi z‖ ≠ 1`) but is vacuous on the line, where the two AFE halves
have equal modulus. -/
theorem carrierFloorOn_of_pointwise_domination (N : ℕ) {S : Set ℂ} {ε : ℝ}
    (hdom : ∀ z ∈ S, ‖zetaChi z * dirichletPoly N (1 - z)‖ + ε < ‖dirichletPoly N z‖) :
    CarrierFloorOn S N ε := by
  intro z hz
  have hd := hdom z hz
  have hgn : gN N z = dirichletPoly N z + zetaChi z * dirichletPoly N (1 - z) := rfl
  have key : ‖dirichletPoly N z‖
      ≤ ‖gN N z‖ + ‖zetaChi z * dirichletPoly N (1 - z)‖ := by
    rw [show dirichletPoly N z = gN N z - zetaChi z * dirichletPoly N (1 - z) by rw [hgn]; ring]
    exact norm_sub_le _ _
  linarith

/-- **Exact off-line modulus of the χ-factor.** `‖zetaChi z‖ = π^{Re z − ½}·‖Γ((1−z)/2)‖/‖Γ(z/2)‖`.
The archimedean phase contributes `π^{Re z − ½}` and the Gamma ratio carries the vertical decay; on
the line `Re z = ½` both factors are `1` (Gamma arguments conjugate), recovering `‖zetaChi‖ = 1`, and
for `Re z ≠ ½` the modulus departs from `1`. -/
theorem norm_zetaChi_eq (z : ℂ) :
    ‖zetaChi z‖ = Real.pi ^ (z.re - 1/2) * ‖Complex.Gamma ((1 - z)/2)‖ / ‖Complex.Gamma (z/2)‖ := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [zetaChi, Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_div, norm_mul, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi, Complex.norm_cpow_eq_rpow_re_of_pos hpi]
  have hre1 : (-(1 - z) / 2).re = -((1 - z.re)/2) := by
    rw [Complex.div_re]; simp [Complex.normSq]; ring
  have hre2 : (-z / 2).re = -(z.re/2) := by
    rw [Complex.div_re]; simp [Complex.normSq]; ring
  rw [hre1, hre2, show ((1:ℂ) - z)/2 = (1-z)/2 by ring,
    mul_div_mul_comm, ← Real.rpow_sub hpi,
    show -((1 - z.re)/2) - -(z.re/2) = z.re - 1/2 by ring, mul_div_assoc]

/-- **Off-line domination floor via the Gamma ratio.** Substituting the exact χ-modulus, the
certificate floor holds on `S` whenever, pointwise, the reflected Dirichlet part weighted by the
explicit archimedean factor is strictly below the direct Dirichlet part:
`π^{Re z−½}·‖Γ((1−z)/2)‖/‖Γ(z/2)‖·‖D(1−z)‖ + ε < ‖D z‖`. Off the critical line the Gamma ratio
supplies the vertical decay (`≍ (t/2π)^{½−Re z}`) that makes this inequality attainable; on the line
it collapses to `‖D‖ + ε < ‖D‖`, correctly vacuous. -/
theorem carrierFloorOn_of_gamma_ratio_domination (N : ℕ) {S : Set ℂ} {ε : ℝ}
    (hdom : ∀ z ∈ S,
      Real.pi ^ (z.re - 1/2) * ‖Complex.Gamma ((1 - z)/2)‖ / ‖Complex.Gamma (z/2)‖
          * ‖dirichletPoly N (1 - z)‖ + ε < ‖dirichletPoly N z‖) :
    CarrierFloorOn S N ε := by
  refine carrierFloorOn_of_pointwise_domination N (fun z hz => ?_)
  rw [norm_mul, norm_zetaChi_eq z]
  exact hdom z hz

end RHTower
