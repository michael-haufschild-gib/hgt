/-
The finite Green witness: the contracting homotopy of the seam complex, built from the Laplacian.

`seam_hodge_compression` (in `SeamHodgeCompression`) takes the contracting homotopy `d h + h d = 1 − P`
as a hypothesis.  This file *builds* it, discharging that hypothesis for every finite seam differential
`d` with `d² = 0` — the finite-dimensional Hodge theory the seam construction needs.

The mechanism is that `d² = 0` forces `d` to commute with the Laplacian `Δ = dᴴ d + d dᴴ`:
`d·Δ = d dᴴ d = Δ·d` (both cross terms `d·d` vanish).  Hence, via the continuous functional calculus,
`d` commutes with the Green operator `G = Δ⁺` (the Moore–Penrose pseudo-inverse, `cfc` of
`x ↦ x⁻¹` off `0`), and

  `d(dᴴ G) + (dᴴ G)d = (dᴴ d + d dᴴ) G = Δ G = 1 − P`,

where `P = Δ⁰` is the harmonic projection (`cfc` of the indicator of `0`).  So the homotopy is
`h = dᴴ G`.  The pseudo-inverse identity `Δ·G = 1 − P` holds because on the finite (discrete)
spectrum `x·(x⁻¹ off 0) = (1 off 0) = 1 − (indicator of 0)`.

`seam_hodge_compression_finite` then states the compression with **no homotopy hypothesis**: for any
grading `Γ` with `d` odd and any `R` commuting with `d`,
`superTrace Γ R = superTrace Γ (R · P)`.  The Seam Stokes Lemma is a theorem for every finite seam
truncation — the moonshot's "dream" step, unconditional at finite height.
-/
import GaloisForLFunctions.RHTower.SeamHodgeCompression
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

noncomputable section

namespace RHTower

open Matrix

variable {n : Type*} [Fintype n]

/-- The Moore–Penrose value function: `x ↦ x⁻¹` off `0`, and `0 ↦ 0`.  On the finite (discrete)
spectrum of a matrix it is continuous, so its `cfc` is the pseudo-inverse. -/
def pinvFun : ℝ → ℝ := fun x => if x = 0 then 0 else x⁻¹

/-- The harmonic indicator: `0 ↦ 1`, nonzero `↦ 0`.  Its `cfc` is the projection onto the kernel. -/
def kerProjFun : ℝ → ℝ := fun x => if x = 0 then 1 else 0

/-- The seam Laplacian `Δ = dᴴ d + d dᴴ`. -/
def seamLaplacian (d : Matrix n n ℂ) : Matrix n n ℂ := dᴴ * d + d * dᴴ

/-- The seam Laplacian is self-adjoint. -/
theorem seamLaplacian_isSelfAdjoint (d : Matrix n n ℂ) : IsSelfAdjoint (seamLaplacian d) := by
  show (seamLaplacian d)ᴴ = seamLaplacian d
  unfold seamLaplacian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, add_comm]

/-- **The differential commutes with its Laplacian.**  `d² = 0` forces `d·Δ = d dᴴ d = Δ·d`: both
cross terms carry a `d·d = 0`. -/
theorem commute_d_seamLaplacian {d : Matrix n n ℂ} (hdd : d * d = 0) :
    Commute d (seamLaplacian d) := by
  show d * seamLaplacian d = seamLaplacian d * d
  unfold seamLaplacian
  have e1 : d * (dᴴ * d + d * dᴴ) = d * dᴴ * d := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc d d dᴴ, hdd, Matrix.zero_mul, add_zero,
      ← Matrix.mul_assoc d dᴴ d]
  have e2 : (dᴴ * d + d * dᴴ) * d = d * dᴴ * d := by
    rw [Matrix.add_mul, Matrix.mul_assoc dᴴ d d, hdd, Matrix.mul_zero, zero_add]
  rw [e1, e2]

variable [DecidableEq n]

/-- The Green operator `G = Δ⁺`: the Moore–Penrose pseudo-inverse of the seam Laplacian, `cfc` of the
value function `pinvFun`. -/
def seamGreen (d : Matrix n n ℂ) : Matrix n n ℂ := cfc pinvFun (seamLaplacian d)

/-- The harmonic projection `P`: `cfc` of the kernel indicator on the seam Laplacian. -/
def seamHarmonicProj (d : Matrix n n ℂ) : Matrix n n ℂ := cfc kerProjFun (seamLaplacian d)

/-- **The Green inverse identity.**  `Δ·G = 1 − P`.  On the finite spectrum,
`x·pinvFun x = kerProjFun`'s complement: `x·(x⁻¹ off 0) = 1 off 0 = 1 − (indicator of 0)`. -/
theorem seamLaplacian_green (d : Matrix n n ℂ) :
    seamLaplacian d * seamGreen d = 1 - seamHarmonicProj d := by
  set B := seamLaplacian d with hB
  have hsa : IsSelfAdjoint B := seamLaplacian_isSelfAdjoint d
  have hfin : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum (A := B)
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ B) := fun f => hfin.continuousOn f
  have hBid : cfc (id : ℝ → ℝ) B = B := cfc_id ℝ B
  show B * cfc pinvFun B = 1 - cfc kerProjFun B
  calc B * cfc pinvFun B
      = cfc (id : ℝ → ℝ) B * cfc pinvFun B := by rw [hBid]
    _ = cfc (fun x => id x * pinvFun x) B := (cfc_mul _ _ B (hcont _) (hcont _)).symm
    _ = cfc (fun x => (1 : ℝ) - kerProjFun x) B :=
        cfc_congr (fun x _ => by
          simp only [id, pinvFun, kerProjFun]
          by_cases hx : x = 0 <;> simp [hx])
    _ = cfc (fun _ => (1 : ℝ)) B - cfc kerProjFun B := cfc_sub _ _ B (hcont _) (hcont _)
    _ = 1 - cfc kerProjFun B := by rw [show (fun _ => (1 : ℝ)) = (1 : ℝ → ℝ) from rfl, cfc_one ℝ B]

/-- The Green operator commutes with the differential: `d·G = G·d`.  It is a functional-calculus
element of the Laplacian, which `d` commutes with (`commute_d_seamLaplacian`). -/
theorem commute_d_seamGreen {d : Matrix n n ℂ} (hdd : d * d = 0) :
    d * seamGreen d = seamGreen d * d :=
  ((commute_d_seamLaplacian hdd).symm.cfc_real pinvFun).symm

/-- **The seam contracting homotopy.**  `h = dᴴ G` satisfies `d h + h d = 1 − P`, from the Green
inverse identity `Δ G = 1 − P` and `d G = G d`:
`d(dᴴ G) + (dᴴ G)d = d dᴴ G + dᴴ d G = (dᴴ d + d dᴴ)G = Δ G = 1 − P`. -/
theorem seam_homotopy {d : Matrix n n ℂ} (hdd : d * d = 0) :
    d * (dᴴ * seamGreen d) + (dᴴ * seamGreen d) * d = 1 - seamHarmonicProj d := by
  have hlap : (dᴴ * d + d * dᴴ) * seamGreen d = 1 - seamHarmonicProj d := seamLaplacian_green d
  have hGd : d * seamGreen d = seamGreen d * d := commute_d_seamGreen hdd
  have h1 : (dᴴ * seamGreen d) * d = dᴴ * d * seamGreen d := by
    rw [Matrix.mul_assoc, ← hGd, ← Matrix.mul_assoc]
  rw [h1, ← Matrix.mul_assoc d dᴴ (seamGreen d), ← Matrix.add_mul,
    add_comm (d * dᴴ) (dᴴ * d), hlap]

/-- **Seam Hodge Compression, unconditional at finite height.**  For any finite seam differential `d`
with `d² = 0`, any grading `Γ` making `d` odd, and any `R` commuting with `d`, the flat supertrace
compresses onto the harmonic projection `P`:
`superTrace Γ R = superTrace Γ (R · P)`.  The homotopy hypothesis of `seam_hodge_compression` is
discharged by `seam_homotopy`, so the Seam Stokes Lemma holds unconditionally on every finite
truncation of the seam complex. -/
theorem seam_hodge_compression_finite (Γ R d : Matrix n n ℂ)
    (hdd : d * d = 0) (hd : Γ * d = -(d * Γ)) (hRd : R * d = d * R) :
    superTrace Γ R = superTrace Γ (R * seamHarmonicProj d) :=
  seam_hodge_compression Γ R (dᴴ * seamGreen d) (seamHarmonicProj d) d hd hRd (seam_homotopy hdd)

end RHTower
