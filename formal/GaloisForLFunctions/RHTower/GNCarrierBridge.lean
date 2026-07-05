/-
Identifying the 2-D carrier `dpoly2` with the certificate carrier `gN`, and producing
`CarrierFloorOn` from a Dirichlet-part floor.

The certificate carrier is `gN N = chiSymmetrize zetaChi (dirichletPoly N)`, i.e.
`gN N z = dirichletPoly N z + zetaChi z · dirichletPoly N (1 − z)`, and its Dirichlet part is the
unit-coefficient 2-D carrier: `dirichletPoly N = dpoly2 (fun _ => 1) (Icc 1 N)`. Hence a floor on
the Dirichlet part, together with a bound on the reflected χ-term, yields the certificate floor
`CarrierFloorOn S N ε` by the reverse triangle inequality — the exact input the codex
`riemannHypothesis_of_…_floor_sign_local_windows` gates consume. On the critical line the Dirichlet
part is the 1-D `dpoly` with coefficients `n^{-1/2}`, so the density and cofinality machinery
transfers verbatim.
-/
import GaloisForLFunctions.RHTower.DpolyOffline
import GaloisForLFunctions.RHTower.ZetaCarrier

open Complex Finset

namespace RHTower

/-- **The certificate carrier's Dirichlet part is the 2-D carrier with unit coefficients.**
`dirichletPoly N = dpoly2 (fun _ => 1) (Icc 1 N)`. -/
theorem dirichletPoly_eq_dpoly2 (N : ℕ) (s : ℂ) :
    dirichletPoly N s = dpoly2 (fun _ => 1) (Finset.Icc 1 N) s := by
  rw [dirichletPoly, dpoly2]
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_one, one_mul]

/-- **The certificate carrier `gN` through the χ-symmetrization, in `dpoly2` terms.** -/
theorem gN_eq_dpoly2 (N : ℕ) (s : ℂ) :
    gN N s = dpoly2 (fun _ => 1) (Finset.Icc 1 N) s
      + zetaChi s * dpoly2 (fun _ => 1) (Finset.Icc 1 N) (1 - s) := by
  simp only [gN, chiSymmetrize]
  rw [dirichletPoly_eq_dpoly2, dirichletPoly_eq_dpoly2]

/-- **`CarrierFloorOn` from a Dirichlet-part floor.** A floor `‖dirichletPoly N z‖ > t₀` on `S`,
together with the reflected χ-term being at most `t₀ − ε`, gives the certificate floor
`CarrierFloorOn S N ε`. Reverse triangle inequality on `gN = D + χ·D(1−·)`. -/
theorem carrierFloorOn_of_dirichletPoly_floor (N : ℕ) {S : Set ℂ} {t₀ ε : ℝ}
    (hfloor : ∀ z ∈ S, t₀ < ‖dirichletPoly N z‖)
    (hrefl : ∀ z ∈ S, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₀ - ε) :
    CarrierFloorOn S N ε := by
  intro z hz
  have h1 := hfloor z hz
  have h2 := hrefl z hz
  have hgn : gN N z = dirichletPoly N z + zetaChi z * dirichletPoly N (1 - z) := rfl
  have key : ‖dirichletPoly N z‖
      ≤ ‖gN N z‖ + ‖zetaChi z * dirichletPoly N (1 - z)‖ := by
    rw [hgn]; exact norm_le_add_norm_add _ _
  linarith

/-- **`CarrierFloorOn` from a `dpoly2` floor.** The certificate floor produced directly from a
`dpoly2` floor on `S` plus the reflected χ-term budget — the form the off-line chart floor
supplies. -/
theorem carrierFloorOn_of_dpoly2_floor (N : ℕ) {S : Set ℂ} {t₀ ε : ℝ}
    (hfloor : ∀ z ∈ S, t₀ < ‖dpoly2 (fun _ => 1) (Finset.Icc 1 N) z‖)
    (hrefl : ∀ z ∈ S,
      ‖zetaChi z * dpoly2 (fun _ => 1) (Finset.Icc 1 N) (1 - z)‖ ≤ t₀ - ε) :
    CarrierFloorOn S N ε := by
  refine carrierFloorOn_of_dirichletPoly_floor N (t₀ := t₀) ?_ ?_
  · intro z hz; rw [dirichletPoly_eq_dpoly2]; exact hfloor z hz
  · intro z hz; rw [dirichletPoly_eq_dpoly2]; exact hrefl z hz

/-- **The certificate carrier on the critical line is a 1-D `dpoly`** with coefficients `n^{-1/2}`,
so the density and cofinality machinery transfers to `dirichletPoly` (hence `gN`) verbatim. -/
theorem dirichletPoly_line_eq (N : ℕ) (τ : ℝ) :
    dirichletPoly N (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I)
      = dpoly (fun n => (n : ℝ) ^ (-(1/2 : ℝ))) (Finset.Icc 1 N) τ := by
  rw [dirichletPoly_eq_dpoly2,
    dpoly2_line_eq (fun _ => 1) (Finset.Icc 1 N)
      (fun n hn => (Finset.mem_Icc.mp hn).1) (1/2) τ]
  congr 1
  funext n
  rw [one_mul]

/-- **Two-level seam product.** On the critical line, the product of the level-`N` and level-`N'`
Dirichlet carriers is a single convolution Dirichlet polynomial (via `dpoly_mul`): the mixed
carrier `dpoly_mul` is the native handle for correlating two levels across the seam. -/
theorem dirichletPoly_mul_line (N N' : ℕ) (τ : ℝ) :
    dirichletPoly N (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I)
        * dirichletPoly N' (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I)
      = dpoly (dpolyConv (fun n => (n : ℝ) ^ (-(1/2 : ℝ))) (fun n => (n : ℝ) ^ (-(1/2 : ℝ)))
              (Finset.Icc 1 N) (Finset.Icc 1 N'))
          (prodSupport (Finset.Icc 1 N) (Finset.Icc 1 N')) τ := by
  rw [dirichletPoly_line_eq, dirichletPoly_line_eq,
    dpoly_mul (fun n => (n : ℝ) ^ (-(1/2 : ℝ))) (fun n => (n : ℝ) ^ (-(1/2 : ℝ)))
      (Finset.Icc 1 N) (Finset.Icc 1 N')
      (fun n hn => Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1)
      (fun n hn => Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1) τ]

end RHTower
