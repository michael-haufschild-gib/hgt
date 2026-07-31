import GaloisForLFunctions.HTGeometry.AnalyticGermRing
import GaloisForLFunctions.HTGeometry.MatrixFactorizationCategory

/-!
# The multiplier potential at a simple zero is the node, locally

For a function `F` holomorphic near `ρ` with a simple zero there, the Lagrange-multiplier potential
`W_F(s,u) = u F(s)` becomes the node `x y` in the coordinates `x = s - ρ`, `y = u G(s)`, where
`F(s) = (s - ρ) G(s)`.  The coordinate change is an analytic isomorphism near `(ρ, 0)`, so it
induces a ring isomorphism of the local rings of analytic germs carrying the germ of the node to the
germ of `W_F`, and therefore an equivalence of the two categories of matrix factorizations.

The local data attached to a simple vacuum is thus the same for every `F` and every `ρ`: it cannot
see where the zero lies.

* `lgPotential`, `nodePotential` — the two potentials.
* `exists_analyticAt_factor_of_simple_zero` — the local factorization at a simple zero.
* `lgCoordChange`, `lgCoordChangeInv` — the coordinate change and its inverse.
* `lgPotential_eventuallyEq_node_comp` — the potential is the node in the new coordinates.
* `lgNodeGermEquiv` — the induced isomorphism of local rings.
* `lgNodeMatrixFactorizationEquiv` — the induced equivalence of matrix-factorization categories.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The two-field Lagrange-multiplier potential `W_F(s,u) = u F(s)`. -/
def lgPotential (F : ℂ → ℂ) : ℂ × ℂ → ℂ := fun p => p.2 * F p.1

/-- The node potential `x y`. -/
def nodePotential : ℂ × ℂ → ℂ := fun p => p.1 * p.2

theorem analyticAt_lgPotential {F : ℂ → ℂ} {ρ : ℂ} (hF : AnalyticAt ℂ F ρ) :
    AnalyticAt ℂ (lgPotential F) (ρ, 0) := by
  have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (ρ, (0 : ℂ)) := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (ρ, (0 : ℂ)) := analyticAt_snd
  exact hsnd.mul (hF.comp hfst)

theorem analyticAt_nodePotential (p : ℂ × ℂ) : AnalyticAt ℂ nodePotential p := by
  have hfst : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) p := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) p := analyticAt_snd
  exact hfst.mul hsnd

/-! ### The local factorization at a simple zero -/

/-- **A simple zero factors off a nonvanishing analytic factor.** -/
theorem exists_analyticAt_factor_of_simple_zero {F : ℂ → ℂ} {ρ : ℂ}
    (hF : AnalyticAt ℂ F ρ) (hroot : F ρ = 0) (hsimple : deriv F ρ ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G ρ ∧ G ρ ≠ 0 ∧ ∀ᶠ z in 𝓝 ρ, F z = (z - ρ) * G z := by
  have horder : analyticOrderAt F ρ = (1 : ℕ) := by
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hf := hF)]
    refine ⟨fun k hk => ?_, ?_⟩
    · interval_cases k
      simpa using hroot
    · simpa using hsimple
  obtain ⟨G, hG, hG0, hGeq⟩ := (hF.analyticOrderAt_eq_natCast (n := 1)).mp horder
  refine ⟨G, hG, hG0, ?_⟩
  filter_upwards [hGeq] with z hz
  simpa [pow_one] using hz

/-! ### The coordinate change -/

/-- The coordinate change `(s,u) ↦ (s - ρ, u G(s))`. -/
def lgCoordChange (G : ℂ → ℂ) (ρ : ℂ) : ℂ × ℂ → ℂ × ℂ := fun p => (p.1 - ρ, p.2 * G p.1)

/-- The inverse coordinate change `(x,y) ↦ (x + ρ, y / G(x + ρ))`. -/
def lgCoordChangeInv (G : ℂ → ℂ) (ρ : ℂ) : ℂ × ℂ → ℂ × ℂ :=
  fun p => (p.1 + ρ, p.2 / G (p.1 + ρ))

theorem lgCoordChange_apply_base (G : ℂ → ℂ) (ρ : ℂ) :
    lgCoordChange G ρ (ρ, 0) = (0, 0) := by
  simp [lgCoordChange]

theorem lgCoordChangeInv_apply_base (G : ℂ → ℂ) (ρ : ℂ) :
    lgCoordChangeInv G ρ (0, 0) = (ρ, 0) := by
  simp [lgCoordChangeInv]

theorem analyticAt_lgCoordChange {G : ℂ → ℂ} {ρ : ℂ} (hG : AnalyticAt ℂ G ρ) :
    AnalyticAt ℂ (lgCoordChange G ρ) (ρ, 0) := by
  have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (ρ, (0 : ℂ)) := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (ρ, (0 : ℂ)) := analyticAt_snd
  exact (hfst.sub analyticAt_const).prod (hsnd.mul (hG.comp hfst))

theorem analyticAt_lgCoordChangeInv {G : ℂ → ℂ} {ρ : ℂ} (hG : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0) :
    AnalyticAt ℂ (lgCoordChangeInv G ρ) (0, 0) := by
  have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) ((0 : ℂ), (0 : ℂ)) := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) ((0 : ℂ), (0 : ℂ)) := analyticAt_snd
  have hshift : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 + ρ) ((0 : ℂ), (0 : ℂ)) :=
    hfst.add analyticAt_const
  have hGshift : AnalyticAt ℂ (fun p : ℂ × ℂ => G (p.1 + ρ)) ((0 : ℂ), (0 : ℂ)) := by
    have hGat : AnalyticAt ℂ G ((fun p : ℂ × ℂ => p.1 + ρ) ((0 : ℂ), (0 : ℂ))) := by
      simpa using hG
    exact AnalyticAt.comp (g := G) (f := fun p : ℂ × ℂ => p.1 + ρ) (x := ((0 : ℂ), (0 : ℂ)))
      hGat hshift
  have hne : G (((0 : ℂ), (0 : ℂ)).1 + ρ) ≠ 0 := by simpa using hG0
  exact hshift.prod (hsnd.div hGshift hne)

/-- Near `(ρ,0)` the factor `G` does not vanish along the first coordinate. -/
theorem eventually_G_ne_zero_nhds_base {G : ℂ → ℂ} {ρ : ℂ} (hG : AnalyticAt ℂ G ρ)
    (hG0 : G ρ ≠ 0) : ∀ᶠ p in 𝓝 ((ρ : ℂ), (0 : ℂ)), G p.1 ≠ 0 := by
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 ((ρ : ℂ), (0 : ℂ))) (𝓝 ρ) :=
    continuousAt_fst
  exact hfst.eventually (hG.continuousAt.eventually_ne hG0)

/-- Near `(0,0)` the shifted factor `G` does not vanish. -/
theorem eventually_G_shift_ne_zero_nhds_zero {G : ℂ → ℂ} {ρ : ℂ} (hG : AnalyticAt ℂ G ρ)
    (hG0 : G ρ ≠ 0) : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), G (p.1 + ρ) ≠ 0 := by
  have hshift : Tendsto (fun p : ℂ × ℂ => p.1 + ρ) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 ρ) := by
    have : Tendsto (fun p : ℂ × ℂ => p.1 + ρ) (𝓝 ((0 : ℂ), (0 : ℂ)))
        (𝓝 (((0 : ℂ), (0 : ℂ)).1 + ρ)) := (continuousAt_fst.add continuousAt_const)
    simpa using this
  exact hshift.eventually (hG.continuousAt.eventually_ne hG0)

theorem lgCoordChangeInv_comp_lgCoordChange {G : ℂ → ℂ} {ρ : ℂ} (hG : AnalyticAt ℂ G ρ)
    (hG0 : G ρ ≠ 0) :
    (lgCoordChangeInv G ρ ∘ lgCoordChange G ρ) =ᶠ[𝓝 ((ρ : ℂ), (0 : ℂ))] id := by
  filter_upwards [eventually_G_ne_zero_nhds_base hG hG0] with p hp
  have h1 : p.1 - ρ + ρ = p.1 := by ring
  simp only [Function.comp_apply, lgCoordChange, lgCoordChangeInv, h1, id_eq]
  refine Prod.ext rfl ?_
  simp [mul_div_assoc, div_self hp]

theorem lgCoordChange_comp_lgCoordChangeInv {G : ℂ → ℂ} {ρ : ℂ} (hG : AnalyticAt ℂ G ρ)
    (hG0 : G ρ ≠ 0) :
    (lgCoordChange G ρ ∘ lgCoordChangeInv G ρ) =ᶠ[𝓝 ((0 : ℂ), (0 : ℂ))] id := by
  filter_upwards [eventually_G_shift_ne_zero_nhds_zero hG hG0] with p hp
  have h1 : p.1 + ρ - ρ = p.1 := by ring
  simp only [Function.comp_apply, lgCoordChange, lgCoordChangeInv, h1, id_eq]
  refine Prod.ext rfl ?_
  simp [hp]

/-- **The multiplier potential is the node in the new coordinates.** -/
theorem lgPotential_eventuallyEq_node_comp {F G : ℂ → ℂ} {ρ : ℂ}
    (hFG : ∀ᶠ z in 𝓝 ρ, F z = (z - ρ) * G z) :
    lgPotential F =ᶠ[𝓝 ((ρ : ℂ), (0 : ℂ))] nodePotential ∘ lgCoordChange G ρ := by
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 ((ρ : ℂ), (0 : ℂ))) (𝓝 ρ) := continuousAt_fst
  filter_upwards [hfst.eventually hFG] with p hp
  simp only [lgPotential, nodePotential, Function.comp_apply, lgCoordChange, hp]
  ring

/-! ### The induced isomorphisms -/

variable {F : ℂ → ℂ} {ρ : ℂ}

/-- **The local ring isomorphism induced by the node coordinate change.** -/
def lgNodeGermEquiv {G : ℂ → ℂ} (hG : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0) :
    AnalyticGerm ((0 : ℂ), (0 : ℂ)) ≃+* AnalyticGerm ((ρ : ℂ), (0 : ℂ)) :=
  analyticGermEquiv (analyticAt_lgCoordChange hG) (analyticAt_lgCoordChangeInv hG hG0)
    (lgCoordChange_apply_base G ρ) (lgCoordChangeInv_apply_base G ρ)
    (lgCoordChangeInv_comp_lgCoordChange hG hG0) (lgCoordChange_comp_lgCoordChangeInv hG hG0)

/-- The isomorphism carries the germ of the node to the germ of the multiplier potential. -/
theorem lgNodeGermEquiv_node {G : ℂ → ℂ} (hG : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hF : AnalyticAt ℂ F ρ) (hFG : ∀ᶠ z in 𝓝 ρ, F z = (z - ρ) * G z) :
    lgNodeGermEquiv hG hG0 (analyticGermOf (analyticAt_nodePotential ((0 : ℂ), (0 : ℂ))))
      = analyticGermOf (analyticAt_lgPotential hF) := by
  refine Subtype.ext ?_
  rw [lgNodeGermEquiv, analyticGermEquiv_apply, analyticGermPullback_analyticGermOf,
    analyticGermOf_val, Germ.coe_eq]
  exact (lgPotential_eventuallyEq_node_comp hFG).symm

/-- **Local matrix-factorization blindness.**  At a simple zero the category of matrix
factorizations of the multiplier potential over the local ring of analytic germs is equivalent to
the category of matrix factorizations of the node, by the ring isomorphism induced by the
coordinate change.  The equivalence does not depend on `F` or on `ρ` beyond the coordinate change
itself. -/
def lgNodeMatrixFactorizationEquiv {G : ℂ → ℂ} (hG : AnalyticAt ℂ G ρ) (hG0 : G ρ ≠ 0)
    (hF : AnalyticAt ℂ F ρ) (hFG : ∀ᶠ z in 𝓝 ρ, F z = (z - ρ) * G z) :
    MatrixFactorization (AnalyticGerm ((0 : ℂ), (0 : ℂ)))
        (analyticGermOf (analyticAt_nodePotential ((0 : ℂ), (0 : ℂ))))
      ≌ MatrixFactorization (AnalyticGerm ((ρ : ℂ), (0 : ℂ)))
        (analyticGermOf (analyticAt_lgPotential hF)) :=
  MatrixFactorization.mapEquivalence (lgNodeGermEquiv hG hG0)
    (lgNodeGermEquiv_node hG hG0 hF hFG)

/-- **Every simple vacuum is the node.**  For a function analytic near `ρ` with a simple zero there,
the matrix-factorization category of the multiplier potential at `(ρ,0)` is equivalent to that of
the node at the origin. -/
theorem exists_lgNodeMatrixFactorizationEquiv (hF : AnalyticAt ℂ F ρ) (hroot : F ρ = 0)
    (hsimple : deriv F ρ ≠ 0) :
    Nonempty (MatrixFactorization (AnalyticGerm ((0 : ℂ), (0 : ℂ)))
        (analyticGermOf (analyticAt_nodePotential ((0 : ℂ), (0 : ℂ))))
      ≌ MatrixFactorization (AnalyticGerm ((ρ : ℂ), (0 : ℂ)))
        (analyticGermOf (analyticAt_lgPotential hF))) := by
  obtain ⟨G, hG, hG0, hFG⟩ := exists_analyticAt_factor_of_simple_zero hF hroot hsimple
  exact ⟨lgNodeMatrixFactorizationEquiv hG hG0 hF hFG⟩

end

end GaloisForLFunctions.RHTower
