# Hellmann–Feynman, unconditional and complex

- **ID:** hellmann-feynman-unconditional
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** goal request 2026-08-21 — "formalize and prove fully, unconditional and closed, the Hellmann–Feynman theorem"
- **Statement:** For a differentiable family of symmetric operators on a `𝕜`-Hilbert space (`𝕜` real or
  complex) with a simple, isolated eigenvalue at a normalized eigenvector, a differentiable branch of
  normalized eigenpairs exists and its eigenvalue derivative is the expectation of the family's motion,
  `nu'(c_0) = ⟪psi_0, (dA/dc) psi_0⟫`.

## Goal

The corpus already owned the Hellmann–Feynman derivative law for **real** inner product spaces
(`HTGeometry.HellmannFeynman`), the branch construction from an **assumed** pseudo-inverse
(`HTGeometry.SimpleEigenvalueBranch`), and a pseudo-inverse for **compact** operators at a **nonzero**
eigenvalue (`HTGeometry.SimpleEigenvalueCompactBranch`).  Three things were missing and are supplied here.

1. **The complex law.**  Quantum mechanics lives over `ℂ`, and the complex case is *not* a corollary of the
   real one: viewing a complex Hilbert space as a real one turns a simple complex eigenvalue into a
   two-dimensional real eigenspace, so real simplicity fails.  Over `𝕜` the cancellation of the eigenvector's
   own motion produces a **conjugated** eigenvalue and the mechanism only closes once `conj nu = nu` is known
   — which is proved, not assumed.
2. **A pseudo-inverse without compactness.**  What perturbation theory actually needs is that the eigenvalue
   be *isolated*.  For a bounded symmetric operator that is exactly a transverse coercivity bound, and from
   it alone the pseudo-inverse is constructed — no Fredholm theory, and `nu_0 = 0` allowed.
3. **No auxiliary input at all in finite dimensions.**  Simplicity already forces a gap there.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper
- [x] 2 → 3  formalized: `lake build` green on all six modules; `#print axioms` gives exactly
  `[propext, Classical.choice, Quot.sound]` for all 46 new declarations across the seven modules; `formal_tools.py lint`
  reports no `sorry`/`admit`/`axiom`/`opaque`/`unsafe` and no unreachable module of this batch
- [ ] 3 → 4  publication-ready

## Lean modules

All in `formal/GaloisForLFunctions/HTGeometry/`, all wired into the `HTGeometry` umbrella.

| Module | Content |
|---|---|
| `HellmannFeynmanRCLike.lean` | the derivative law over `RCLike`: `eigenvalue_conj_eq_self_of_symmetric_at`, `hellmann_feynman_rclike_eventually`, `hellmann_feynman_rclike`, `hellmann_feynman_rclike_ofReal`, `hellmann_feynman_rclike_re` |
| `SimpleEigenvalueGapInverse.lean` | `exists_pseudoInverse_of_gap` (bounded symmetric, gap ⇒ pseudo-inverse), `exists_gap_of_finiteDimensional` (simplicity ⇒ gap) |
| `SimpleEigenvalueBorderedRCLike.lean` | the bordered system over `𝕜` and its explicit inverse; `borderedCLMRC_isInvertible`, `borderedCLMRC_restrictScalars_isInvertible` |
| `SimpleEigenvalueBranchRCLike.lean` | the eigen-residual, its strict derivative, and the implicit-function branch: `exists_differentiable_simple_eigen_branchRC`, `exists_differentiable_normalized_simple_eigen_branchRC` |
| `HellmannFeynmanUnconditional.lean` | the capstones: `exists_normalized_branch_deriv_eq_expectationRC`, `..._of_gapRC`, `..._of_finiteDimensionalRC`, `exists_real_branch_deriv_eq_re_expectationRC`, the real specializations in the packaging of `SimpleEigenvalueBranch`, and the `ℂ` forms |
| `HellmannFeynmanAffineFamily.lean` | `H(λ) = H₀ + λ V`: `hasStrictFDerivAt_affineFamily`, `isSymmetric_affineFamily`, `exists_real_branch_affine_deriv_eq_re_expectation`, `..._complex`, and the finite-dimensional forms with no gap hypothesis |
| `HellmannFeynmanWitness.lean` | non-vacuity: on every inner product space with a unit vector, `exists_twoLevel_branch_deriv_eq_one` exhibits an affine family meeting every hypothesis with gap `|delta|` and computes `dE/dλ(0) = 1` |

## Approach

* **The law.**  Differentiate `A_t psi_t = nu_t • psi_t` at `c` and pair with `psi c`.  The left side gives
  `⟪psi, w⟫ + ⟪psi, A psi'⟫`; the right gives `nu ⟪psi, psi'⟫ + nu'`.  Symmetry turns `⟪psi, A psi'⟫` into
  `conj(nu) ⟪psi, psi'⟫`, and reality of `nu` — from symmetry at the normalized eigenvector — makes the two
  eigenvector-motion terms cancel.  Only the value at `c` is used.
* **The pseudo-inverse.**  On `W = psi_0^perp` the restriction of `T = A - nu_0` is injective (simplicity) and
  bounded below (the gap), hence has closed range; a vector of `W` orthogonal to `T W` is killed by `T` and so
  lies in the eigendirection, hence is zero — so the range is dense as well.  Closed plus dense is everything;
  the Banach inverse composed with the transverse projector is the pseudo-inverse.
* **The branch.**  Implicit function theorem for the eigen-residual `f (c, (phi, nu)) = (A c phi - nu • phi,
  ⟪psi_0, phi⟫ - 1)`, whose partial derivative in the eigenpair variables is the bordered map.  Since `c` is
  real, the residual is only `ℝ`-differentiable and the bordered map is inverted after restricting scalars —
  legitimate because it is `𝕜`-linearly invertible.  Rescaling by `‖psi c‖⁻¹` normalizes the branch.

## Log

- 2026-08-21 — created directly at stage 3: seven modules written, built, and axiom-audited; every new result
  closes on `[propext, Classical.choice, Quot.sound]` only.
