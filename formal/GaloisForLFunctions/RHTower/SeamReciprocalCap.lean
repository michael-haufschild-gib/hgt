/-
Reciprocal capping: acyclic caps carry no supertrace, and the generator commutes with the Green data.

The seam Stokes step is made exact at finite height by *capping* the truncation reciprocally rather
than cutting it raw: at each height the seam is closed into a genuine finite complex by adjoining an
**acyclic** reciprocal cap, so the boundary defect is not deferred to a limit — it is a term of a
finite-dimensional supercommutator, whose supertrace already vanishes.  This file formalizes the two
structural facts that make that work.

**Acyclic caps carry no supertrace.**  `seam_hodge_compression_acyclic`: if a graded piece is acyclic
— it has a contracting homotopy `d K + K d = 1` (equivalently harmonic projection `P = 0`) — then for
every `R` commuting with the odd differential `d`, `superTrace Γ R = 0`.  This is McKean–Singer for an
acyclic complex: its Euler characteristic (supertrace of the identity, and of any chain map) is `0`.
So the regulator caps enforce Stokes but contribute nothing to the cohomology supertrace or the
determinant — they are invisible in the final divisor.

**The generator commutes with the Green data.**  `commute_generator_seamGreen`,
`commute_generator_seamHarmonicProj`: from `[Θ, d] = 0` and `[Θ, dᴴ] = 0` (hence `[Θ, Δ] = 0`), the
Green operator `G` and harmonic projection `P` — both functional-calculus elements of the Laplacian `Δ`
— satisfy `[Θ, G] = 0` and `[Θ, P] = 0`.  Combined with `SeamFiniteHodge`, this is the complete finite
Green witness: a contracting homotopy `d(dᴴG) + (dᴴG)d = 1 − P` whose data all commute with the scaling
generator, so the compression respects `Θ`.

The explicit `Fin 4` cap `ℂα → ℂe₀⊕ℂe₁ → ℂω` (`d α = e₀`, `d e₁ = ω`) realizes a reciprocity-graded
acyclic cap: `capD² = 0`, `capD` odd for the grading `capΓ = diag(1,−1,−1,1)`, `[capΘ, capD] = 0` for
`capΘ = diag(0,0,1,1)`, and the contracting homotopy `capD·capK + capK·capD = 1` — witnessing that the
acyclic-cap hypotheses are simultaneously satisfiable by a genuine reciprocal cap.
-/
import GaloisForLFunctions.RHTower.SeamFiniteHodge

noncomputable section

namespace RHTower

open Matrix

variable {n : Type*} [Fintype n]

/-! ### Acyclic caps carry no supertrace -/

/-- **An acyclic graded piece has zero supertrace.**  If `d K + K d = 1` (a contracting homotopy to
`0`, i.e. the complex is acyclic with harmonic projection `P = 0`) and `R` commutes with the odd
differential `d`, then `superTrace Γ R = 0`.  This is the compression `superTrace Γ R = superTrace Γ
(R·P)` at `P = 0`: McKean–Singer for an acyclic complex.  The reciprocal regulator caps are acyclic, so
they contribute nothing to the cohomology supertrace or the determinant. -/
theorem seam_hodge_compression_acyclic [DecidableEq n] (Γ R K d : Matrix n n ℂ)
    (hd : Γ * d = -(d * Γ)) (hRd : R * d = d * R) (hac : d * K + K * d = 1) :
    superTrace Γ R = 0 := by
  rw [seam_hodge_compression Γ R K 0 d hd hRd (hac.trans (sub_zero 1).symm),
    Matrix.mul_zero, superTrace, Matrix.mul_zero, Matrix.trace_zero]

/-! ### The generator commutes with the Green data -/

/-- The scaling generator commutes with the Laplacian when it commutes with `d` and `dᴴ`:
`[Θ, dᴴ d + d dᴴ] = 0`. -/
theorem commute_generator_seamLaplacian {Θ d : Matrix n n ℂ}
    (hΘd : Commute Θ d) (hΘdH : Commute Θ dᴴ) : Commute Θ (seamLaplacian d) :=
  (hΘdH.mul_right hΘd).add_right (hΘd.mul_right hΘdH)

/-- **The generator commutes with the Green operator.**  `[Θ, G] = 0`, since `G = cfc pinvFun Δ` is a
functional-calculus element of the Laplacian, which `Θ` commutes with. -/
theorem commute_generator_seamGreen [DecidableEq n] {Θ d : Matrix n n ℂ}
    (hΘd : Commute Θ d) (hΘdH : Commute Θ dᴴ) : Commute Θ (seamGreen d) :=
  ((commute_generator_seamLaplacian hΘd hΘdH).symm.cfc_real pinvFun).symm

/-- **The generator commutes with the harmonic projection.**  `[Θ, P] = 0`, since `P = cfc kerProjFun
Δ` is a functional-calculus element of the Laplacian. -/
theorem commute_generator_seamHarmonicProj [DecidableEq n] {Θ d : Matrix n n ℂ}
    (hΘd : Commute Θ d) (hΘdH : Commute Θ dᴴ) : Commute Θ (seamHarmonicProj d) :=
  ((commute_generator_seamLaplacian hΘd hΘdH).symm.cfc_real kerProjFun).symm

/-! ### The explicit reciprocal cap `ℂα → ℂe₀⊕ℂe₁ → ℂω` -/

/-- The cap differential: `α ↦ e₀`, `e₁ ↦ ω` (basis order `α, e₀, e₁, ω`). -/
def capD : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0]

/-- The cap contracting homotopy: `e₀ ↦ α`, `ω ↦ e₁`. -/
def capK : Matrix (Fin 4) (Fin 4) ℂ := !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0]

/-- The cap grading involution `diag(1, −1, −1, 1)`: `+1` on even degrees `α, ω`, `−1` on the odd
degree `e₀, e₁`. -/
def capΓ : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

/-- The cap scaling generator `diag(0, 0, 1, 1)`: weight `0` on `α, e₀`, weight `1` on `e₁, ω` (the
reciprocal pair). -/
def capΘ : Matrix (Fin 4) (Fin 4) ℂ := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The cap differential is square-zero: `d² = 0`. -/
theorem capD_sq : capD * capD = 0 := by
  simp only [capD]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The cap differential is odd for the grading: `Γ d = −d Γ`. -/
theorem capΓ_capD_odd : capΓ * capD = -(capD * capΓ) := by
  simp only [capD, capΓ]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The scaling generator commutes with the cap differential: `[Θ, d] = 0` — the finite-height
chain-level reciprocity `J Θ J⁻¹ = 1 − Θ*` realized on the cap. -/
theorem capΘ_capD_comm : capΘ * capD = capD * capΘ := by
  simp only [capD, capΘ]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **The cap is acyclic.**  `d K + K d = 1`: the contracting homotopy witnesses `H•(cap) = 0`, so the
reciprocal cap closes the truncation without adding cohomology. -/
theorem capD_capK_acyclic : capD * capK + capK * capD = 1 := by
  simp only [capD, capK]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- **Non-vacuity of the acyclic reciprocal cap.**  A reciprocity-graded acyclic cap complex exists:
some odd square-zero differential with a contracting homotopy.  So the hypotheses of
`seam_hodge_compression_acyclic` are simultaneously satisfiable, and the finite reciprocal capping of
the seam Stokes step is realized by a genuine object. -/
theorem exists_reciprocal_acyclic_cap :
    ∃ Γ d K : Matrix (Fin 4) (Fin 4) ℂ,
      d * d = 0 ∧ Γ * d = -(d * Γ) ∧ d * K + K * d = 1 :=
  ⟨capΓ, capD, capK, capD_sq, capΓ_capD_odd, capD_capK_acyclic⟩

end RHTower
