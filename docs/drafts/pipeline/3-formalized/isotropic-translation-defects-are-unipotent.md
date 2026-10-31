# Isotropic translation defects are unipotent

- **ID:** AFFINE-ISOTROPIC-TRANSLATION-UNIPOTENCE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean verified)
- **Parent:** [Finite-index Mautner rigidity](../1-in-progress/finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** For a Hermitian group kernel of negative index at most `r<∞`, every nonpositive column subspace has dimension at most `r`. For an affine kernel, every totally isotropic translation-invariant subspace `W` satisfies `(T_b−1)^(dim W)=0` for every rational `b`. Every nonzero isotropic common translation eigenvector is fixed by all translations. No dilation invariance of `W` is required.

## Dependency-closed paper proof

On the span of columns `v_g(h)=k(h⁻¹g)`, set `B(v_g,v_h)=k(g⁻¹h)` and extend sesquilinearly. Hermitian symmetry makes this independent of column expansions: `B(v_g,f)=f(g)`. The form is nondegenerate because all evaluations separate functions, and the left group action preserves it.

The corpus's finite-index completion supplies at most `r` linear evaluation features `Φ` such that `P=B+Φ*Φ` is positive semidefinite. On a nonpositive subspace, `Φ(w)=0` gives `0≤P(w,w)=B(w,w)≤0`. Cauchy–Schwarz then gives `P(w,z)=0` for every `z`, hence `B(w,z)=0` and `w=0`. Thus `Φ` embeds that subspace into `ℂ^r`. This includes every totally isotropic subspace.

Let `v≠0` be isotropic and satisfy `T_bv=χ(b)v` for every rational `b`. The group law gives `χ(0)=1`, `χ(x+y)=χ(x)χ(y)`, and nonzero character values. For positive integers `n`, put `v_n=D_nv`; then `v_n` is nonzero and isotropic, with character `χ_n(b)=χ(b/n)`.

Two elementary character identities control this orbit. If `χ(ut)=χ(vt)` for every rational `t` and `u≠v`, then `χ((u−v)t)=1`, so `χ=1`. If `conj(χ(ut))χ(vt)=1` and `u²≠v²`, apply the relation at `ut` and conjugate it at `vt`; cancellation gives `χ(u²t)=χ(v²t)`, again forcing `χ=1`.

If `χ` were nontrivial, the characters `χ_n` would be distinct by the first identity. If `B(v_n,v_m)≠0` for distinct positive integers, translation invariance would give the second identity with `u=1/n`, `v=1/m`, a contradiction. Thus the dilation images are mutually orthogonal isotropic vectors. Distinct joint eigencharacters of commuting operators are linearly independent. Taking `r+1` images contradicts the isotropic dimension bound. Therefore `χ=1`.

Now let `W` be translation-invariant and totally isotropic. It is finite-dimensional. Each eigenspace of a fixed `T_b|W` is invariant under all translations. The common-eigenvector theorem applied there, followed by the preceding paragraph, forces its eigenvalue to be one. Generalized eigenspaces exhaust a finite complex vector space, so `(T_b−1)^(dim W)=0`.

## Lean and scope

`Index/ColumnForm.lean`, `Index/IsotropicSubspaces.lean`, `Affine/RationalCharacters.lean`, and `Affine/IsotropicTranslations.lean` pass direct Lean checks with only `propext`, `Classical.choice`, and `Quot.sound`. Endpoints: `finite_nonpositive_column_subspace`, `isotropic_translation_eigencharacter_eq_one`, `isotropic_translation_unipotent`, and `isotropic_translation_difference_pow_apply`.

For Haar successors this controls the translation-period radical; it does not construct the [relative splitting](../1-in-progress/finite-index-haar-carriers-split-modulo-polynomial-kernels.md) or prove continuity of mixed coefficients.
