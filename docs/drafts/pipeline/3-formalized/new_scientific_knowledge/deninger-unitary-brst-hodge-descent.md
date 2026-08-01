# Deninger unitary BRST--Hodge descent

- **ID:** `deninger-unitary-brst-hodge-descent`
- **Stage:** 3-formalized
- **Type:** SOURCE HODGE DESCENT THEOREM
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.BRSTHodgeConstraint` (`(3)`, `(5)`),
  `GaloisForLFunctions.RHTower.DeningerArithmeticUnitaryBRSTHodge` (`(2)`, `(4)`, harmonic
  stability),
  `GaloisForLFunctions.RHTower.DeningerUnitaryHarmonicAction` (the unitary action on the harmonic
  sector)

## Statement

Let \(E\) be a real or complex Hilbert space, \(Q:E\to E\) a bounded differential, and
\(U:E\to E\) a unitary operator.  Assume
\[
 UQ=QU.                                                           \tag{1}
\]
Then
\[
 UQ^\dagger=Q^\dagger U,                                         \tag{2}
\]
and therefore \(U\) commutes with the BRST--Hodge Hamiltonian
\[
 \Delta_Q=Q^\dagger Q+QQ^\dagger:                                \tag{3}
\]
\[
 U\Delta_Q=\Delta_QU.                                             \tag{4}
\]
Consequently \(U\) preserves the harmonic sector
\[
 \ker\Delta_Q=\ker Q\cap\ker Q^\dagger.                           \tag{5}
\]

No separate Laplacian-commutation conjecture is needed at a finite Deninger packet.  Once the
centered power transfer is unitary and is a chain map, harmonic cohomology inherits its unitary
action automatically.

## Proof

Taking adjoints in `(1)` gives
\[
 Q^\dagger U^\dagger=U^\dagger Q^\dagger.                        \tag{6}
\]
Multiply `(6)` by \(U\) on the left and by \(U\) on the right.  Using
\[
 UU^\dagger=U^\dagger U=1
\]
gives `(2)`.  Now
\[
\begin{aligned}
 UQ^\dagger Q
   &=(UQ^\dagger)Q
    =(Q^\dagger U)Q
    =Q^\dagger(UQ)
    =Q^\dagger(QU)
    =(Q^\dagger Q)U,\\
 UQQ^\dagger
   &=(UQ)Q^\dagger
    =(QU)Q^\dagger
    =Q(UQ^\dagger)
    =Q(Q^\dagger U)
    =(QQ^\dagger)U.
\end{aligned}
\]
Adding proves `(4)`.  If \(\Delta_Qx=0\), then
\[
 \Delta_QUx=U\Delta_Qx=0,
\]
which proves harmonic preservation.  Equality `(5)` is the already formalized positive
BRST--Hodge identity.

## Deninger consequence

At a finite MW--Gamma packet, combine:

1. hyperbolic localization, which turns \(F_nV_n=n\,\mathrm{id}\);
2. Poincare adjunction and moving-Hodge naturality, which make
   \(U_n=n^{-1/2}V_n\) unitary;
3. framed functoriality, which gives \(U_nQ=QU_n\);
4. the theorem above.

Then every \(U_n\) acts unitarily on harmonic cohomology and commutes with its Hodge Laplacian.
The finite centered-purity gate is therefore reduced to constructing the positive moving Hodge
realization and proving chain-map functoriality.  It is not an additional spectral hypothesis.

## Formalized statement

`GaloisForLFunctions/HTGeometry/BRSTHodgeConstraint.lean`:

- `brstHodgeHamiltonian Q = Q†Q + QQ†` and
  `brstHodgeHamiltonian_eq_adjoint_mul_add_mul_adjoint` : the definition `(3)`;
- `brstHodgeHamiltonian_apply_eq_zero_iff` : `Δ_Q ψ = 0 ↔ Qψ = 0 ∧ Q†ψ = 0`, which is `(5)`,
  proved from `re ⟪Δ_Q ψ, ψ⟫ = ‖Qψ‖² + ‖Q†ψ‖²`.

`GaloisForLFunctions/RHTower/DeningerArithmeticUnitaryBRSTHodge.lean`, over an arbitrary
`RCLike` field and complete inner-product space:

- `deningerUnitary_commutes_adjoint_of_commutes` : `(2)`, `UQ† = Q†U`, by taking adjoints in
  `(1)` and multiplying by `U` on both sides;
- `deningerUnitary_commutes_brstHodgeHamiltonian` : `(4)`, `UΔ_Q = Δ_QU`;
- `deningerUnitary_maps_brstHarmonic_to_brstHarmonic` : `Δ_Q x = 0 → Δ_Q (Ux) = 0`.

`GaloisForLFunctions/RHTower/DeningerUnitaryHarmonicAction.lean` upgrades stability of the
harmonic sector to the unitary action the Deninger consequence asserts:

- `deningerBRSTHarmonic Q = ker Q ⊓ ker Q†` with
  `deningerBRSTHarmonic_eq_ker : deningerBRSTHarmonic Q = ker Δ_Q`, so `(5)` is available as an
  equality of submodules and not only as a pointwise iff;
- `deningerUnitary_norm_apply`, `deningerUnitary_inner_apply` : a two-sided unitary preserves the
  norm and the inner product;
- `deningerUnitary_adjoint_commutes` : `U†Q = QU†`, so `U†` is again a unitary chain symmetry;
- `deningerUnitary_mem_harmonic`, `deningerUnitary_adjoint_mem_harmonic` : both `U` and `U†` map
  the harmonic sector into itself;
- `deningerUnitary_harmonic_bijective` : `U` is therefore a *bijection* of the harmonic sector,
  not merely stable on it;
- `deningerHarmonicUnitary : ker Δ_Q ≃ₗᵢ[𝕜] ker Δ_Q` : the induced unitary, with
  `deningerHarmonicUnitary_inner` recording that it preserves the inner product.

Everything the theorem asserts — `(2)`, `(4)`, `(5)`, and the resulting unitary action on the
harmonic sector — is formalized, unconditionally, from `(1)` and two-sided unitarity alone.  The
Deninger consequence's four inputs `1`--`3` (hyperbolic localization, Poincaré adjunction and
moving-Hodge naturality, framed chain-map functoriality) are separate cards; input `4` is this
theorem.

### Verification

- Direct commands: `lake env lean` on all three modules — pass with no errors and no warnings.
- Cached module build: `lake build GaloisForLFunctions.RHTower.DeningerUnitaryHarmonicAction`
  completes (`✔ [3084/3084]`).
- Scratch `#print axioms` on every headline declaration: only `propext`, `Classical.choice`,
  `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: descent statement isolated
- [x] 1 → 2 fully-proven: `(2)`, `(4)`, `(5)` proved
- [x] 2 → 3 formalized: `(2)`, `(4)`, `(5)`, and the unitary action on the harmonic sector
- [ ] 3 → 4 publication-ready: the cofinal unbounded limit noted below (common cores,
      closability, strong-resolvent convergence) is a separate card

## Hostile audit

- Invertibility without unitarity is insufficient: adjoint commutation need not follow.
- Commutation with \(Q\) alone does not imply commutation with \(Q^\dagger\).
- The theorem is finite/bounded.  Passage to the cofinal unbounded limit still requires common
  cores, closability, and strong-resolvent/harmonic-projection convergence.
- Defining \(U\) from Xi spectral coordinates would make the application circular; the theorem
  must consume framed source transfers.

## Log

- 2026-08-01 — Closed the formalization.  `(2)`, `(4)` and pointwise harmonic stability were
  already in the corpus, and `(5)` was already available as
  `brstHodgeHamiltonian_apply_eq_zero_iff`.  Missing was the Deninger consequence's actual
  content: that `U` acts *unitarily* on harmonic cohomology.  Added
  `DeningerUnitaryHarmonicAction`, which shows `U†` is also a unitary chain symmetry, hence `U`
  is a bijection of `ker Δ_Q`, and packages the restriction as a linear isometry equivalence
  `deningerHarmonicUnitary`.  Card moved to `3-formalized`.  The unbounded cofinal limit remains
  open, as the hostile audit states.
