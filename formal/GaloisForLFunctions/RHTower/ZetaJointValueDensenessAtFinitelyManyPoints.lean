import GaloisForLFunctions.RHTower.ZetaVoroninUniversalityOnCompactSets

/-!
# Joint denseness of the values of `ζ` at finitely many points of the strip

For distinct points `s₁, …, s_k` of the open strip `1/2 < Re s < 1` and nonzero targets
`w₁, …, w_k`, the shifts `τ` with `|ζ(s_j + iτ) − w_j| < ε` for all `j` have positive lower density
(`exists_pos_density_forall_norm_zeta_sub_lt`).  This is the universality theorem on the compact
set `{s₁, …, s_k}` for the entire nonvanishing target `exp P`, where `P` is the Lagrange
interpolation polynomial with `P(s_j) = log w_j`.  The points may have arbitrary heights: the
joint phases of the disc-union machinery are what make the simultaneous approximation possible.
-/

open Complex Filter Topology Finset Metric MeasureTheory Set Polynomial
open scoped ENNReal

noncomputable section

namespace RHTower

/-- **Joint denseness of `ζ` at finitely many points.**  For an injective family `s : ι → ℂ` of
points of the strip and nonzero values `w : ι → ℂ`, the shifts at which `ζ(s j + iτ)` is within
`ε` of `w j` for every `j` have positive lower density. -/
theorem exists_pos_density_forall_norm_zeta_sub_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ι → ℂ} (hs : Function.Injective s) (hstrip : ∀ j, 1 / 2 < (s j).re ∧ (s j).re < 1)
    {w : ι → ℂ} (hw : ∀ j, w j ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤
      volume ({τ : ℝ | ∀ j, ‖riemannZeta (s j + τ * I) - w j‖ < ε} ∩ Icc 0 T) := by
  -- the interpolation polynomial of the logarithms of the targets
  set P : ℂ[X] := Lagrange.interpolate Finset.univ s (fun j => Complex.log (w j)) with hP
  have hPval : ∀ j, P.eval (s j) = Complex.log (w j) := fun j =>
    Lagrange.eval_interpolate_at_node _ (Set.injOn_of_injective hs) (mem_univ j)
  set g : ℂ → ℂ := fun z => Complex.exp (P.eval z) with hg
  have hgd : Differentiable ℂ g := Complex.differentiable_exp.comp (Polynomial.differentiable P)
  have hg0 : ∀ z, g z ≠ 0 := fun z => Complex.exp_ne_zero _
  have hgs : ∀ j, g (s j) = w j := fun j => by
    rw [hg]
    simp only
    rw [hPval j, Complex.exp_log (hw j)]
  -- universality on the finite set of points
  have hK : IsCompact (Set.range s) := Set.finite_range s |>.isCompact
  have hKstrip : ∀ z ∈ Set.range s, 1 / 2 < z.re ∧ z.re < 1 := by
    rintro _ ⟨j, rfl⟩
    exact hstrip j
  obtain ⟨c, hc, hT⟩ :=
    exists_pos_density_zetaTargetReturnSet_of_differentiable_of_isCompact hK hKstrip hgd hg0 hε
  refine ⟨c, hc, hT.mono fun T hT => hT.trans (measure_mono (inter_subset_inter_left _ ?_))⟩
  intro τ hτ j
  have := hτ (s j) ⟨j, rfl⟩
  rwa [hgs j] at this

end RHTower
