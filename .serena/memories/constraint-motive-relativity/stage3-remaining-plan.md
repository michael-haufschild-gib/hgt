# CMR stage-3: COMPLETE — 18/18 promoted

All eighteen `constraint-motive-relativity` cards are formalized unconditionally in Lean 4 and live
in `docs/drafts/pipeline/3-formalized/constraint-motive-relativity/`, each with a
`<id>-formalized.md` companion.  `2-fully-proven/constraint-motive-relativity/` is empty.

## Reusable infrastructure created by this sweep (do not rebuild)

- `HTGeometry/SimpleEigenvalueBranch.lean` — `IsSimpleEigenpair` and `exists_eigenBranch`: the
  first-order perturbation theorem `μ̇(0) = ⟪u, Bu⟫` for a simple isolated eigenvalue of a compact
  self-adjoint operator on a Hilbert space.  Riesz-projection-free: mathlib's Fredholm alternative
  on `uᗮ` plus a contraction fixed point for the `uᗮ`-component.  Not in mathlib.
- `HTGeometry/ConstraintMotiveRelativity/FiniteReporterAdmission.lean` —
  `exists_continuous_annihilator_of_notMem_closure`: Hahn–Banach separation of a point from a
  *subspace* by a continuous ℂ-functional.  Mathlib has only the algebraic and convex-set forms.
- `HTGeometry/ConstraintMotiveRelativity/MarkedEulerShellSkeleton.lean` — `rank_hankelBlock`:
  `rank H_R(F) = min(R+1,|F|)` for the weighted prime-log Hankel block, via a Gram factorisation
  and an invertible weighted-Vandermonde submatrix.
- `HTGeometry/UniformIteratedDerivLimit.lean` — repaired the pre-existing break in
  `HTGeometry/TestFunctionComplete.lean`.
- `HTGeometry/CompactOperatorBoundedBelow.lean` — generalized to `E →L[𝕜] F₀`.

## Known deliberate gaps (documented in the companions' scope notes)

- The Fredholm determinant `det_F(I - τ⁻¹K)` is not constructed; the Helson card's wall condition
  is formalized in its Fredholm-alternative form (`helson_wall_iff`).  Mathlib has no Fredholm
  determinant.
- Theorem 4.1 (4)'s packaging of the crossing datum as a `C¹` Banach hypersurface needs Fréchet
  `C¹`-dependence of the eigenvalue on an `ℓ¹_d`-neighbourhood; the one-parameter branch theorem
  supplies transversality and orientation but not the chart.

## Toolchain traps hit repeatedly

- `lake build <module>` for the audit; `lake env lean <file>` while iterating; `pkill -f "lake env
  lean"` afterwards.  Full-umbrella builds exceed the 600 s Bash cap — run in background.
- Namespace collisions are real (`hyperbolicForm` already existed in `PrimeAugmentationSymplectic`);
  `rg` before naming.
- `↥S ⧸ T` needs `T : Submodule R ↥S` (`Submodule.comap S.subtype T`).
- `Module.evalEquiv`/`Module.IsReflexive` can fail instance search on `↥(Submodule …)` of a
  `→L[ℂ]` space; route through `Submodule.quotDualCoannihilatorToDual` and `Module.Finite.equiv`,
  not `LinearEquiv.finiteDimensional`.
- `convert` on `HasDerivAt` hits a `Complex.addCommGroup` vs `instCommCStarAlgebraComplex` diamond;
  use `HasDerivAt.congr_deriv` with `Pi.inv_apply` in the simp set.
- `ContinuousLinearMap.{add,smul,sub,mul,sum,one}_apply` are deprecated; the replacements
  `add_apply`, `smul_apply`, `sub_apply`, `mul_apply_eq_comp`, `sum_apply`, `one_apply_eq_self`
  live at the root.
- `SuzukiDiagonalResolventInstantiation` is in namespace `GaloisForLFunctions.RHTower` while
  `DiagonalEllTwoOperator` is in `RHTower`; qualify accordingly.
- Recurrence and compact-orbit statements come free from
  `ConstraintMotiveRelativity/PortRecurrenceJets.lean`.
