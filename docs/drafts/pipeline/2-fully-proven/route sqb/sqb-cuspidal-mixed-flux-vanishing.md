# SQB mixed cusp flux: full-height vanishing and a tail bound

- **ID:** SQB-CUSPIDAL-MIXED-FLUX
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Literal exceptional finite-deck Maass vector paired with an arbitrary cusp-zero finite-energy test vector
- **Status in Lean:** The source Maass equation, cusp-zero Poincaré inequality, energy integrability, and finite-strip mixed Green identity are proved. The full-height limit and bound below are not yet formalized.

## Statement

Fix a deck level `N`, let `L=N+1`, and let `U` be the literal exceptional source vector with eigenvalue `λ∈(0,1/4)`. Let `V` be any vector in the finite-deck cuspidal form pre-domain. On the Euclidean cusp cylinder `C_Y=[0,L]×(Y,∞)`, `Y>1`, write the deck-coordinate functions as `U_q,V_q`. Define

```text
J_V(y) = Σ_q ∫₀ᴸ (∂_y U_q)(x,y) conjugate(V_q(x,y)) dx,
E_F(Y)² = Σ_q ∫_Y^∞∫₀ᴸ (|∂_x F_q|²+|∂_y F_q|²) dx dy.
```

Then `J_V` is integrable on `(Y,∞)` and tends to zero as `y→∞`. More precisely,

```text
J_V(Y) = -∫_Y^∞ G_V(y) dy,
G_V(y) = Σ_q ∫₀ᴸ [-λ y⁻² U_q conjugate(V_q)
                 + (∂_x U_q) conjugate(∂_x V_q)
                 + (∂_y U_q) conjugate(∂_y V_q)] dx,
|J_V(Y)| ≤ [1+λ(L/(2πY))²] E_U(Y) E_V(Y).       (1)
```

Both energies are finite and their tails tend to zero. Thus the mixed upper boundary current vanishes for **every** cusp-zero finite-energy test vector, not only along a selected height subsequence. Formula (1) is a quantitative, source-specific full-cusp Green boundary law.

The bound is uniform on test vectors with `E_V(Y)≤1`:

```text
sup_{E_V(Y)≤1} |J_V(Y)| ≤ [1+λ(L/(2πY))²] E_U(Y) → 0.       (2)
```

The finite-deck periodization already identifies `E_V(Y)` with a bounded part of the cuspidal form norm, up to the fixed level factor. Hence the upper boundary functional extends continuously through form completion, and its norm tends to zero. This is the part needed to exchange cusp exhaustion with the completed Friedrichs test domain.

## Proof

The actual source belongs to the cuspidal form pre-domain. Both `U` and `V` have finite hyperbolic horizontal and vertical gradient energies. On `C_Y`, the hyperbolic area factor `y⁻²` cancels the `y²` in `|hypGradX|²` and `|hypGradY|²`. Therefore `∂_x U`, `∂_y U`, `∂_x V`, and `∂_y V` all belong to ordinary Euclidean `L²(C_Y)`.

Each deck coordinate has period `L` and zero mean on every horocycle. The sharp periodic Wirtinger inequality gives

```text
∫₀ᴸ |F_q(x,y)|² dx ≤ (L/(2π))² ∫₀ᴸ |∂_x F_q(x,y)|² dx
```

for `F=U,V`. Integrating over `y>Y` proves `U,V∈L²(C_Y)` and the norm bound `‖F‖₂≤(L/(2π))E_F(Y)`. Cauchy--Schwarz in the full cylinder now gives

```text
∫_Y^∞ |J_V(y)| dy ≤ ‖∂_y U‖₂ ‖V‖₂ < ∞.       (3)
```

Above the cutoff the already-proved retracted source equation is literal:
`∂_{xx}U_q+∂_{yy}U_q=-λ y⁻² U_q`. The already-proved periodic mixed Green identity says, for `Y<a<b`,

```text
J_V(b)-J_V(a)=∫_a^b G_V(y)dy.
```

Its original density has `U_{xx} conjugate(V)+U_x conjugate(V_x)+U_{yy} conjugate(V)+U_y conjugate(V_y)`; the Maass equation gives the displayed `G_V`. By Cauchy--Schwarz, `G_V∈L¹(Y,∞)`. Its three terms have integral bounds `λY⁻²‖U‖₂‖V‖₂`, `‖U_x‖₂‖V_x‖₂`, and `‖U_y‖₂‖V_y‖₂`. The last two combine to at most `E_U(Y)E_V(Y)`.

Since `G_V` is integrable, the increment identity makes `J_V(y)` converge to a finite limit at infinity. Equation (3) forces that limit to be zero. Letting `b→∞` in the increment identity gives the exact tail representation. Applying the stated norm bounds proves (1), then taking the supremum proves (2). No zero-location, arithmetic cancellation, or spectral selection premise enters this argument.

## Consequence and remaining gate

The finite-strip Green bridge now has a dependency-closed paper proof of its upper-boundary limit on the actual cuspidal source and the full cuspidal test pre-domain, with a uniform form-norm tail bound. This discharges the *vertical cusp flux* item of SQB at paper level; the retracted Maass equation was already closed in Lean. To enter the Friedrichs operator domain, the lower/core boundary identities must be assembled with this tail limit and extended by form closure. Even a resulting exceptional Maass eigenvector would not itself identify an Xi divisor. The hardest gate remains a source-derived arithmetic-to-Maass spectral occurrence law (and its symmetric-power/selection requirements).

## Corpus dependencies

- `MaassFiniteDeckCuspidalDirichlet.sourceInCuspidalFormPreDomain` gives `U` in the cusp-zero pre-domain.
- `MaassFiniteDeckCuspidalTail.level_cusp_slice_poincare` gives the periodic Wirtinger bound; `cusp_hypGradX_weighted_integrable` and `cusp_hypGradY_weighted_integrable` give finite cylinder gradient energy after the coordinate change already used there.
- `MaassFiniteDeckCuspidalGreen.retractedSourceDeckComponent_laplacian` gives the literal equation above the cutoff.
- `MaassFiniteDeckCuspidalCrossFlux.sourceTestGreenDensity_increment` gives the finite-strip current increment.

The theorem is not yet a Lean theorem. The new step is combining these source-specific facts into full-height, all-test flux vanishing and the quantitative tail law (1).
