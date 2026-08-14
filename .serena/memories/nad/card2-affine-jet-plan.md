# Card 2 `affine-jet-packet-collision-completeness` — construction plan (2026-08-14)

## DONE: the source space
`HTGeometry/SeveralVariableEntire.lean` (wired, axiom-clean):
`entireSet d` ⊆ `C(Fin d → ℂ, ℂ)`, `lineMap`, `deriv_comp_lineMap_zero`
(`fderiv ℂ f x v = deriv (fun λ => f (x + λ • v)) 0`), `tendstoLocallyUniformly_of_tendsto`,
**`norm_fderiv_sub_le_of_norm_le`** (Cauchy estimate along a line: bound `C` on the circle of radius
`r` ⇒ derivative difference `≤ C/r`), **`opNorm_fderiv_sub_le`**, **`isClosed_entireSet`**,
`completeSpace_entireSet`, **`baireSpace_entireSet`**.
mathlib has NO several-variable holomorphy; none is needed — everything runs along complex lines.

## The remaining construction, in dependency order
The goal is a term of `AffineJetPacketCollisionInput X Λ Frame frame` with `X := entireSet d`;
`affineJetPacketCollision_denseResidual_exactMatroid` then gives the card's theorem.

1. **Continuity of jet evaluation** (`defect_closed`).  Do NOT try to prove "fderiv of an entire
   function is entire" (several-variable).  Instead represent each directional Taylor coefficient by
   a circle integral, `c_k(f, x, v) = (2πi)⁻¹ ∮_{|z|=r} z^{-(k+1)} f(x + z v) dz`, which is
   continuous in `f` for the compact-open topology (uniform convergence on the compact set
   `{x + z v : |z| = r}`); recover multi-index derivatives from directional coefficients by
   polarisation.  `Δ_S` is then a polynomial in finitely many such continuous functionals, hence
   continuous, and its zero set is closed.
2. **Hermite interpolation in `ℂ^d`** (for `defect_interior_empty`).  Chinese remainder:
   the ideals `m_p^{N+1}` at distinct points are pairwise comaximal (`IsCoprime.pow`), so
   `ℂ[z]/⋂ m_p^{N+1} ≅ ∏ ℂ[z]/m_p^{N+1}`; combine with the Taylor identification of
   `ℂ[z]/m_p^{N+1}` with jets of order `≤ N` to realise arbitrary finite jets at finitely many
   points by a polynomial.
3. **Empty interior of each defect.**  Given `g` in the zero set and the interpolating `f_S` with
   `Δ_S (f_S) ≠ 0`, the map `t ↦ Δ_S (g + t • (f_S - g))` is a polynomial in `t` (the jets are affine
   in `f`, `Δ_S` is a determinant of monomials in them) and is nonzero at `t = 1`, hence has finitely
   many zeros; arbitrarily small `t` therefore leave the zero set.
4. **Affine chain rule for jets**: the jet of `f ∘ σ_λ` at `x` is the jet of `f` at `σ_λ x`
   composed with the invertible `A_λ`; needed so that prescribing jets of `f` at the distinct points
   `σ_λ (x_j)` prescribes the packet data.  Also the Zariski-genericity step (12): points can be
   chosen with `σ_λ(x_j) ≠ σ_μ(x_k)` for distinct occurrences.
5. **Determinant avoidance ⇒ differential independence** (`collisionRank_of_avoids`) and the
   constant-coefficient operator-rank law (`operatorRank_of_avoids`): clearing denominators in a
   differential polynomial relation and expanding coefficients into coordinate monomials produces a
   nontrivial finite ℂ-linear relation among distinct decorated monomials, contradicting one
   determinant.  The finite witness already exists in the corpus:
   `affineDecoratedMonomials_exist_packet_det_ne_zero`.

## Notes
- `Δ_S` and the defect enumeration must be indexed by a countable type; `Λ` and `ℕ^d` are countable,
  so the decorated monomials are countable — use an explicit `Encodable`/`Denumerable` enumeration.
- Instance trap hit while building the foundation: `HasFDerivAt.comp_hasDerivAt` produces the
  `RCLike.innerProductSpace.toModule` path for ℂ; close the mismatch with
  `convert … using 1 <;> rfl`.
