import GaloisForLFunctions.RHTower.DirichletHalfPlane

/-!
# The abscissas of convergence and of uniform convergence

Two invariants of an ordinary Dirichlet series, defined exactly as mathlib defines the abscissa of
*absolute* convergence: as an infimum over the real points where the relevant mode of convergence
holds, the half-plane property making the choice of real points harmless.

* `abscissaOfConv` : the abscissa of (conditional) convergence.
* `abscissaOfUnifConv` : the abscissa of uniform convergence on closed half-planes.

Uniform convergence on `Re s ≥ x` implies convergence at `x`, so `abscissaOfConv ≤ abscissaOfUnifConv`.
The reverse inequality is Bohr's theorem — false as stated for general Dirichlet series, and the
substance of the classical result is that the abscissa of uniform convergence coincides with the
abscissa of bounded holomorphy.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The partial sums of an ordinary Dirichlet series. -/
def dirichletPartialSum (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)

/-- The series converges at `s`. -/
def DirichletConvergesAt (a : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun N => dirichletPartialSum a N s) atTop (𝓝 L)

/-- The series converges uniformly on the closed half-plane `Re s ≥ x`. -/
def DirichletUniformlyConvergesOn (a : ℕ → ℂ) (x : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, TendstoUniformlyOn (dirichletPartialSum a) F atTop {s : ℂ | x ≤ s.re}

/-- **The abscissa of convergence.** -/
noncomputable def abscissaOfConv (a : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | DirichletConvergesAt a (x : ℂ)}

/-- **The abscissa of uniform convergence.** -/
noncomputable def abscissaOfUnifConv (a : ℕ → ℂ) : EReal :=
  sInf <| Real.toEReal '' {x : ℝ | DirichletUniformlyConvergesOn a x}

theorem DirichletConvergesAt.abscissaOfConv_le {a : ℕ → ℂ} {x : ℝ}
    (h : DirichletConvergesAt a (x : ℂ)) : abscissaOfConv a ≤ (x : EReal) :=
  sInf_le ⟨x, h, rfl⟩

/-- **The half-plane property in terms of the abscissa.** -/
theorem convergesAt_of_abscissaOfConv_lt_re {a : ℕ → ℂ} {s : ℂ}
    (hs : abscissaOfConv a < (s.re : EReal)) : DirichletConvergesAt a s := by
  obtain ⟨y, hy, hys⟩ : ∃ y : ℝ, DirichletConvergesAt a (y : ℂ) ∧ y < s.re := by
    simpa [abscissaOfConv, sInf_lt_iff] using hs
  refine tendsto_dirichlet_partialSum_of_re_lt (s₀ := (y : ℂ)) hy ?_
  simpa using hys

/-- Uniform convergence on a closed half-plane gives convergence at its edge. -/
theorem DirichletUniformlyConvergesOn.convergesAt {a : ℕ → ℂ} {x : ℝ}
    (h : DirichletUniformlyConvergesOn a x) : DirichletConvergesAt a (x : ℂ) := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F (x : ℂ), ?_⟩
  refine hF.tendsto_at ?_
  simp

/-- **The abscissa of convergence is at most the abscissa of uniform convergence.** -/
theorem abscissaOfConv_le_abscissaOfUnifConv (a : ℕ → ℂ) :
    abscissaOfConv a ≤ abscissaOfUnifConv a := by
  refine sInf_le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.convergesAt, rfl⟩

end GaloisForLFunctions.RHTower

end
