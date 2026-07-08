import GaloisForLFunctions.RHTower.OmegaComplexStructure
import GaloisForLFunctions.RHTower.OmegaObstruction
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The seam supermetric is not Lorentzian

Read as a Wheeler–DeWitt datum, the seam carries a symmetric bilinear form `Q` (the supermetric) on a
space `V` together with the complex structure `J` induced by the obstruction class (`J² = −1`, `Q`
preserved by `J`, `Q x (J x) = 0`).  The question is the signature of `Q`: does it single out a time
direction — is it Lorentzian?

It cannot be.  On the plane spanned by any vector and its `J`-partner, `Q` is *conformally definite*:
`Q(a·x + b·Jx) = (a²+b²)·Q(x,x)`.  So a single time-like direction (`Q x x < 0`) never stands alone —
it spans a two-dimensional time-like plane `{x, Jx}` on which `Q` is negative-definite.  Time
directions come in `J`-pairs; the negative index of inertia is therefore never `1`.  The seam's
supermetric has even-even signature `(2p, 2q)`, never the `(n−1, 1)` of a gravitational superspace.
The complex structure that the weld forces on `V` obstructs a clock the way York time works: no isolated
time-like axis survives.

Everything here is a property of the *given* polarization data `(V, Q, J)` — a constraint on what the
supermetric can be — with no carrier constructed.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The supermetric is conformally definite on a `J`-plane.**  For any vector `x`, on the plane
`{x, J x}` the form `Q` is the constant `Q x x` times the Euclidean norm: `J` rotates without changing
the sign.  Uses `Q(Jx,Jx) = Q(x,x)`, `Q(x,Jx) = 0`, and symmetry of `Q`. -/
theorem Q_plane_diag {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    (hQ : Q.IsSymm) (x : V) (a b : ℝ) :
    Q (a • x + b • P.complex.J x) (a • x + b • P.complex.J x) = (a ^ 2 + b ^ 2) * Q x x := by
  have hJJ : Q (P.complex.J x) (P.complex.J x) = Q x x := P.preserves x x
  have hxJ : Q x (P.complex.J x) = 0 := P.Q_self_J_eq_zero_of_isSymm hQ x
  have hJx : Q (P.complex.J x) x = 0 := by rw [hQ.eq]; exact hxJ
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hJJ, hxJ, hJx]; ring

/-- The `J`-plane `{x, J x}` of a nonzero vector is two-dimensional. -/
theorem plane_finrank {Q : LinearMap.BilinForm ℝ V} (P : PolarizedOmegaComplexStructure V Q)
    {x : V} (hx : x ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ {x, P.complex.J x}) = 2 := by
  have hli : LinearIndependent ℝ ![x, P.complex.J x] := P.complex.linearIndependent_pair hx
  have hrange : Set.range ![x, P.complex.J x] = {x, P.complex.J x} := by
    ext z
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
  rw [← hrange, finrank_span_eq_card hli]; simp

/-- **A time-like direction forces a time-like plane.**  If `Q x x < 0` then `Q` is negative-definite
on the two-dimensional `J`-plane `{x, J x}`.  The negative index of inertia is therefore never exactly
one. -/
theorem timelike_forces_two_dim_negdef {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) {x : V} (hx : Q x x < 0) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = 2 ∧ ∀ v ∈ W, v ≠ 0 → Q v v < 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  refine ⟨Submodule.span ℝ {x, P.complex.J x}, plane_finrank P hx0, ?_⟩
  intro v hv hv0
  rw [Submodule.mem_span_pair] at hv
  obtain ⟨a, b, rfl⟩ := hv
  rw [Q_plane_diag P hQ x a b]
  have hab : 0 < a ^ 2 + b ^ 2 := by
    rcases eq_or_ne a 0 with ha | ha
    · rcases eq_or_ne b 0 with hb | hb
      · exact absurd (by rw [ha, hb]; simp : (a : ℝ) • x + b • P.complex.J x = 0) hv0
      · positivity
    · positivity
  exact mul_neg_of_pos_of_neg hab hx

/-- Dually, a space-like direction forces a space-like plane: positive index of inertia is never
exactly one either. -/
theorem spacelike_forces_two_dim_posdef {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) {x : V} (hx : 0 < Q x x) :
    ∃ W : Submodule ℝ V, Module.finrank ℝ W = 2 ∧ ∀ v ∈ W, v ≠ 0 → 0 < Q v v := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  refine ⟨Submodule.span ℝ {x, P.complex.J x}, plane_finrank P hx0, ?_⟩
  intro v hv hv0
  rw [Submodule.mem_span_pair] at hv
  obtain ⟨a, b, rfl⟩ := hv
  rw [Q_plane_diag P hQ x a b]
  have hab : 0 < a ^ 2 + b ^ 2 := by
    rcases eq_or_ne a 0 with ha | ha
    · rcases eq_or_ne b 0 with hb | hb
      · exact absurd (by rw [ha, hb]; simp : (a : ℝ) • x + b • P.complex.J x = 0) hv0
      · positivity
    · positivity
  exact mul_pos hab hx

/-- **Any `J`-invariant subspace has even dimension.**  `J` restricts to a complex structure on it
(`omegaRestrict`), and a real space with `J² = −1` has even dimension. -/
theorem jInvariant_finrank_even {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (hW : ∀ x ∈ W, P.complex.J x ∈ W) :
    Even (Module.finrank ℝ W) := by
  have hsq : (LinearMap.restrict P.complex.J hW).comp (LinearMap.restrict P.complex.J hW)
      = -LinearMap.id := by
    ext w
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq,
      Submodule.coe_neg, LinearMap.coe_restrict_apply]
    exact P.complex.apply_sq w
  exact OmegaComplexStructure.finrank_even { J := LinearMap.restrict P.complex.J hW, sq := hsq }

/-- **The seam supermetric is not Lorentzian.**  There is no vector that is time-like while every
negative-definite subspace is at most a line: a time-like vector always spans a time-like plane. So
`Q` has no single isolated time direction. -/
theorem supermetric_not_lorentzian {Q : LinearMap.BilinForm ℝ V}
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) :
    ¬ ∃ x : V, Q x x < 0 ∧
      ∀ W : Submodule ℝ V, (∀ v ∈ W, v ≠ 0 → Q v v < 0) → Module.finrank ℝ W ≤ 1 := by
  rintro ⟨x, hx, hmax⟩
  obtain ⟨W, hW2, hWneg⟩ := timelike_forces_two_dim_negdef P hQ hx
  have := hmax W hWneg
  omega

/-- Negative-definite subspaces of `Q` are the `PosDef` subspaces of `-Q.toQuadraticMap` — the data
that the negative index of inertia `sigNeg` maximizes over. -/
theorem negdef_restrict_posdef {Q : LinearMap.BilinForm ℝ V} {W : Submodule ℝ V}
    (h : ∀ v ∈ W, v ≠ 0 → Q v v < 0) :
    (QuadraticMap.restrict (-(LinearMap.BilinMap.toQuadraticMap Q)) W).PosDef := by
  rintro ⟨v, hv⟩ hne
  have hv0 : v ≠ 0 := fun hh => hne (Subtype.ext hh)
  have heq : (QuadraticMap.restrict (-(LinearMap.BilinMap.toQuadraticMap Q)) W) ⟨v, hv⟩
      = -(Q v v) := by
    simp [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply]
  rw [heq]; linarith [h v hv hv0]

/-- **The negative index of inertia is never one** — the citable form of "not Lorentzian".  A time-like
direction always spans a two-dimensional time-like plane, so `sigNeg` of the seam supermetric cannot
equal `1`. -/
theorem sigNeg_ne_one {Q : LinearMap.BilinForm ℝ V} [FiniteDimensional ℝ V]
    (P : PolarizedOmegaComplexStructure V Q) (hQ : Q.IsSymm) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap Q) ≠ 1 := by
  intro h1
  obtain ⟨W, hWdim, hWpd⟩ :=
    exists_finrank_eq_sigNeg_and_negDef (LinearMap.BilinMap.toQuadraticMap Q)
  rw [h1] at hWdim
  have hne : W ≠ ⊥ := by intro h; rw [h] at hWdim; simp at hWdim
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxneg : Q x x < 0 := by
    have hpos := hWpd ⟨x, hxW⟩ (fun hh => hx0 (Subtype.ext_iff.mp hh))
    have heq : (QuadraticMap.restrict (-(LinearMap.BilinMap.toQuadraticMap Q)) W) ⟨x, hxW⟩
        = -(Q x x) := by
      simp [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply]
    rw [heq] at hpos; linarith
  obtain ⟨W', hW'2, hW'neg⟩ := timelike_forces_two_dim_negdef P hQ hxneg
  have hle := le_sigNeg_of_negDef (LinearMap.BilinMap.toQuadraticMap Q)
    (negdef_restrict_posdef hW'neg)
  rw [hW'2, h1] at hle; omega

/-- The seam's realized supermetric — the `Q` of a `PolarizedObstructionRealization` — is not
Lorentzian, whenever it is symmetric. -/
theorem seam_realization_not_lorentzian {G A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] {InducesJ : ClassInducesJ G A V}
    {cls : secondConstraintCohomology (G := G) (A := A)} {Q : LinearMap.BilinForm ℝ V}
    (R : PolarizedObstructionRealization InducesJ cls Q) (hQ : Q.IsSymm) :
    ¬ ∃ x : V, Q x x < 0 ∧
      ∀ W : Submodule ℝ V, (∀ v ∈ W, v ≠ 0 → Q v v < 0) → Module.finrank ℝ W ≤ 1 :=
  supermetric_not_lorentzian R.toPolarizedOmegaComplexStructure hQ

end RHTower
end GaloisForLFunctions
