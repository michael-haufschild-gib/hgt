/-
The Seam Hodge Compression as an unconditional finite theorem: the McKean–Singer supertrace identity.

The seam-suspension construction reduces the critical-line statement to a single step — the compression
of the flat resolvent supertrace `Str^♭((s − Θ_Δ)⁻¹)` onto the positive middle cohomology `H_Δ^1`.  In
the seam model this step is named the Seam Stokes Lemma: `Str^♭_ren([d_Δ, A]_super) = 0`.  In the finite
(graded, matrix) model it is not an open input — it is a theorem, and this file proves it.

With a grading involution `Γ` (`Γ² = 1`, `+1` on even degrees, `−1` on odd), the graded supertrace is
`superTrace Γ A = tr(Γ A)`.  Two facts:

* **`superTrace_supercommutator_zero`** — for an odd differential `d` (`Γ d = −d Γ`) and any `X`,
  `superTrace Γ (d X + X d) = 0`.  Supertrace of a supercommutator with an odd operator vanishes: the
  grading turns cyclicity into a sign that cancels the two terms.  This is the exact algebraic content
  of the Seam Stokes Lemma.

* **`seam_hodge_compression`** — given a contracting homotopy `d h + h d = 1 − P` (the Hodge/Green
  identity `I − P = dG + Gd`, with `h = G d*`) and a resolvent `R` commuting with `d`,
  `superTrace Γ R = superTrace Γ (R P)`.  The whole-complex flat supertrace equals the supertrace on
  the `P`-block (harmonics ≅ cohomology): `R(1 − P) = d(Rh) + (Rh)d` is a supercommutator, whose
  supertrace vanishes.

The commutation `R d = d R` is itself produced by the generator: a two-sided inverse `R` of
`s·1 − Θ` commutes with `d` whenever `Θ` does (`resolvent_comm_of_generator_comm`), and `s·1 − Θ`
commutes with `d` iff `Θ` does (`sub_smul_comm`).  So `seam_resolvent_compression` runs the whole step
from `[Θ, d] = 0` and the homotopy alone.

This isolates the moonshot's residual exactly.  The flat identity
`Str^♭((s − Θ_Δ)⁻¹) = ξ'/ξ` is banked (`seamFluxCochain_sector_sum`); the compression is now a theorem
(here); the closing `Hermitian generator ⟹ zeros on the line` is banked
(`rh_of_hermitian_spectral`).  The one genuinely open input is the *existence of the contracting
homotopy on the limiting seam complex* — the finite-height homotopy always exists (finite-dimensional
Hodge theory), and the Seam Stokes Lemma is precisely the claim that it survives the height limit.
-/
import GaloisForLFunctions.RHTower.SeamSuspensionTrace

noncomputable section

namespace RHTower

open Complex Matrix

variable {n : Type*} [Fintype n]

/-- The graded supertrace weighted by a grading involution `Γ`: `superTrace Γ A = tr(Γ A)`.  For the
grading `Γ = +1` on even seam degrees and `−1` on the odd degree, this is the alternating trace
`tr|_{𝒞⁰} − tr|_{𝒞¹} + tr|_{𝒞²}`. -/
def superTrace (Γ A : Matrix n n ℂ) : ℂ := (Γ * A).trace

@[simp] theorem superTrace_def (Γ A : Matrix n n ℂ) : superTrace Γ A = (Γ * A).trace := rfl

/-- **The supertrace of a supercommutator with an odd differential vanishes.**  For `d` odd
(`Γ d = −d Γ`) and any `X`, `superTrace Γ (d X + X d) = 0`.  Cyclicity of the trace,
`tr(Γ d X) = −tr(Γ X d)`, uses the grading sign `Γ d = −d Γ`; the two terms cancel.  This is the
algebraic core of the Seam Stokes Lemma. -/
theorem superTrace_supercommutator_zero (Γ d X : Matrix n n ℂ) (hd : Γ * d = -(d * Γ)) :
    superTrace Γ (d * X + X * d) = 0 := by
  rw [superTrace, Matrix.mul_add, Matrix.trace_add]
  have e1 : (Γ * (d * X)).trace = -((Γ * X) * d).trace := by
    rw [← Matrix.mul_assoc, hd, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc,
      Matrix.trace_mul_comm d (Γ * X), Matrix.mul_assoc]
  have e2 : (Γ * (X * d)).trace = ((Γ * X) * d).trace := by
    rw [← Matrix.mul_assoc]
  rw [e1, e2]; ring

/-- Commuting with `M` transfers to a two-sided inverse `R`: if `R M = 1`, `M R = 1`, and `M d = d M`,
then `R d = d R`. -/
theorem resolvent_comm_of_generator_comm [DecidableEq n] (M R d : Matrix n n ℂ)
    (hRM : R * M = 1) (hMR : M * R = 1) (hc : M * d = d * M) : R * d = d * R := by
  calc R * d = R * d * (M * R) := by rw [hMR, Matrix.mul_one]
    _ = R * (d * M) * R := by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d M R]
    _ = R * (M * d) * R := by rw [hc]
    _ = (R * M) * d * R := by rw [Matrix.mul_assoc R M d, Matrix.mul_assoc]
    _ = d * R := by rw [hRM, Matrix.one_mul]

/-- The shifted generator `s·1 − Θ` commutes with `d` exactly when `Θ` does. -/
theorem sub_smul_comm [DecidableEq n] (Θ d : Matrix n n ℂ) (s : ℂ) (hc : Θ * d = d * Θ) :
    (s • (1 : Matrix n n ℂ) - Θ) * d = d * (s • (1 : Matrix n n ℂ) - Θ) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, hc, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

/-- **Seam Hodge Compression.**  With a contracting homotopy `d h + h d = 1 − P` (the finite Hodge
identity `I − P = dG + Gd`) and a resolvent `R` commuting with the odd differential `d`, the flat
whole-complex supertrace equals the supertrace on the cohomology block:
`superTrace Γ R = superTrace Γ (R P)`.  Proof: `R(1 − P) = R(d h + h d) = d(R h) + (R h) d` (using
`R d = d R`) is a supercommutator with the odd `d`, so `superTrace Γ (R(1 − P)) = 0`. -/
theorem seam_hodge_compression [DecidableEq n] (Γ R h P d : Matrix n n ℂ)
    (hd : Γ * d = -(d * Γ)) (hRd : R * d = d * R) (hom : d * h + h * d = 1 - P) :
    superTrace Γ R = superTrace Γ (R * P) := by
  have key : superTrace Γ (R * (1 - P)) = 0 := by
    have hX : R * (1 - P) = d * (R * h) + (R * h) * d := by
      rw [← hom, Matrix.mul_add, ← Matrix.mul_assoc R d h, hRd,
        Matrix.mul_assoc d R h, Matrix.mul_assoc R h d]
    rw [hX]; exact superTrace_supercommutator_zero Γ d (R * h) hd
  have hsub : superTrace Γ R - superTrace Γ (R * P) = 0 := by
    rw [superTrace, superTrace, ← Matrix.trace_sub, ← Matrix.mul_sub,
      show R - R * P = R * (1 - P) by rw [Matrix.mul_sub, Matrix.mul_one]]
    exact key
  exact sub_eq_zero.mp hsub

/-- **Seam Hodge Compression for the resolvent.**  Run the compression from the generator alone: given
`[Θ, d] = 0`, a two-sided inverse `R` of `s·1 − Θ`, and the contracting homotopy `d h + h d = 1 − P`,
the flat resolvent supertrace compresses onto cohomology, `superTrace Γ R = superTrace Γ (R P)`.  The
commutation `R d = d R` is produced by `resolvent_comm_of_generator_comm` from `[Θ, d] = 0`. -/
theorem seam_resolvent_compression [DecidableEq n] (Γ Θ R h P d : Matrix n n ℂ) (s : ℂ)
    (hd : Γ * d = -(d * Γ)) (hΘd : Θ * d = d * Θ)
    (hRM : R * (s • (1 : Matrix n n ℂ) - Θ) = 1) (hMR : (s • (1 : Matrix n n ℂ) - Θ) * R = 1)
    (hom : d * h + h * d = 1 - P) :
    superTrace Γ R = superTrace Γ (R * P) :=
  seam_hodge_compression Γ R h P d hd
    (resolvent_comm_of_generator_comm _ R d hRM hMR (sub_smul_comm Θ d s hΘd)) hom

end RHTower
