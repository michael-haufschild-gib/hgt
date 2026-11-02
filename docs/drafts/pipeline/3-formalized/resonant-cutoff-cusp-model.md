# Resonant cutoff families have an exact joint cusp model

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** [Arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).
- **Lean namespace:** `GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates`.
- **Modules:** `ResonantStates/CutoffGramKernel.lean`, `ResonantStates/HeckeCutoffShifts.lean` within `RenormalizedIntersectionTheory`; both imported by its umbrella.

## Exact statements

Let `u,v` satisfy `-1/2<Re u,Re v<0`, `Im u,Im v>0`, and `Λ(1+2u)=Λ(1+2v)=0`. Put `B(u)=Λ(2u)` and `τ_(u,Y)=Λ^Y E_u`. For any `Y,Z≥1`,

`〈τ_(u,Y),τ_(v,Z)〉 = -B(u)conj(B(v)) min(Y,Z)^(-u-conj(v))/(u+conj(v))`.

The functions `f_(u,Y)(y)=1_(0,Y](y) B(u)y^(-u-1/2)` in `L²(dy)` have exactly this Gram kernel. Their cross products are integrable for every `Re u,Re v<0`, without a resonance condition. Consequently,

`‖Σ_i c_i τ_(u_i,Y_i)‖²_(L²(fd)) = ‖Σ_i c_i f_(u_i,Y_i)‖²_(L²(dy))`

for every finite family of resonant parameters, individual cutoffs `Y_i≥1`, and complex coefficients.

The corpus coordinate Hecke operator satisfies

`T_p τ_(u,Y) = p^u τ_(u,pY) + p^(-u) τ_(u,Y/p)`.

Multiplying by `Y^u` turns this into two coefficient-free shifts. For simultaneous Hecke transforms at arbitrary primes `p_i`, the same finite-combination norm identity holds with `f` replaced by `p_i^u_i f_(u_i,p_iY_i)+p_i^(-u_i) f_(u_i,Y_i/p_i)`, provided `Y_i≥p_i`. This includes all cross terms between primes and distinct resonant states.

## Proof

For `Y≤Z`, the difference of the two truncations is a constant Fourier mode supported on `(Y,Z]`. The state already truncated at `Y` has zero horocycle average there. Thus mixed-height pairings reduce to the smaller height. Maass–Selberg evaluates the remaining pairing; its two denominators are nonzero because the real parts are negative and imaginary parts positive. Integrating the elementary cusp powers gives the same kernel. Expanding finite sums proves the isometry, with cross-product integrability established before interchanging sums and integrals.

At a resonance only one constant Weyl coefficient survives. The two Hecke branches rescale its cutoff by `p` and `1/p`; the existing exact Hecke remainder gives the shift identity. Applying the finite isometry to both shifted copies proves the simultaneous-prime statement.

## Rigidity boundary and positive survivor

The elementary positive Gram model exists throughout `Re u<0`. Positivity of joint cutoff Gram data therefore supplies no additional restriction selecting `Re u=-1/4`. The positive survivor is the exact isometric model, including simultaneous-prime correlations; this extends the corpus's single-state first two Hecke moments and reflected-partner angle.

The proof uses complete horocycles above height one. It does not classify microlocal limits or prove recurrence or entropy. Coordinate Hecke formulas below that cutoff do not establish the corresponding automorphic truncation formula. Compact-core returns remain the next source-level question.

## Verification

Both modules passed direct `lake --old env lean` checks. The Gram module's olean was produced only for the Hecke module's import. No umbrella build. Transitive `#print axioms` for `resonant_finite_combination_isometry`, `cusp_cutoff_gram`, `hecke_cutoff_shifts`, `normalized_hecke_cutoff_shifts`, and `hecke_finite_combination_isometry` returned only `propext`, `Classical.choice`, `Quot.sound`.
