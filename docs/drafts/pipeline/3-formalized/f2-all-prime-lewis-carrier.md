# F2 — corrected all-prime transport on the retained-boundary source carrier

- **Stage:** 3-formalized
- **Result:** On `0<Re s<1/2`, retained-boundary restoration intertwines every corrected prime Hecke operator with the actual source correspondence and its arithmetic boundary eigenvalue. The carrier contains every actual upper-strip PM core.
- **Scope:** Parameterized physical source action; no assumed Hecke eigenfunction law for arbitrary carrier elements.

## Source invariance

Let `W_s` consist of physical functions fixed on `(0,∞)` by modular inversion and the Lewis three-term operator. The [positive-determinant carrier theorem](../3-formalized/f2-all-determinant-lewis-carrier.md) gives

`T_(n,s) W_s ⊆ W_s` for every `n>0` and every complex `s`.

Its proof uses the actual finite Hecke basis set, a uniquely labelled finite suffix partition, homogeneous binary splitting, and reversal of basis entries.

## Boundary evaluation from the three-term equation alone

For a three-term solution `g`, put `F(x,y)=y^(−2s)g(x/y)`. Then `F(x,y)=F(x+y,y)+F(x,x+y)`.

At `a=1`, the literal source sum is

`T_(p,s)g(1)=Σ_(B∈heckeSet p) F(rowSums B)`.

The primitive row sums form a complete finite suffix partition, giving contribution `F(1,1)=g(1)`. The remaining prime-determinant bases have row sums `(p,p)` and are exactly

`[[k,p−k],[k−1,p−k+1]]`, `1≤k≤p`.

Their contribution is `p F(p,p)=p^(1−2s)g(1)`. Thus

`T_(p,s)g(1)=(1+p^(1−2s))g(1)`.

This boundary eigenfunctional requires only the three-term equation. Inversion, regularity, resonance, and a spectral-strip restriction are unnecessary.

## Retained-boundary reconstruction

Write `w=2s`, `A(a)=1+a^(−w)`, `P(a)=a⁻¹+a^(1−w)`. The audited evaluation coordinates `α,β` define

`Rf=f+α(f)A+β(f)P`, `F(g,c)=g−cA−g(1)/(w−1)P`.

On `V={g:2g(2)=g(1)}`, these give exact inverse coordinates:

`R F(g,c)=g`, `α(F(g,c))=c`, `β(F(g,c))=g(1)/(w−1)`,

`F(Rf,α(f))=f`.

Every `g∈W_s` lies in `V`; define `D_s={f:Rf∈W_s}`. Thus restoration and its retained coordinate identify `D_s` with `W_s×ℂ`.

Let `λ_p=1+p^(1−2s)`. The actual corrected operator is

`T̂_p f=T_p f+α(f)(T_p A−λ_p A)+β(f)(T_p P−λ_p P)`.

Finite-sum linearity and the boundary evaluation law give the exact function identity

`T̂_p F(g,c)=F(T_p g,λ_p c)` for every `g∈W_s`.

Carrier invariance and the inverse-coordinate identities therefore give

`R(T̂_p f)=T_p(Rf)`, `α(T̂_p f)=λ_p α(f)`, `T̂_p D_s⊆D_s`.

In particular the zero-boundary-coordinate channel is invariant under every prime. The previously audited actual-core identity gives `R core_s=E_s` on the positive axis and `α(core_s)=ζ(2s)`, so all upper-strip physical cores belong to this carrier; upper resonances lie in its zero channel.

## Remaining F2 problem

These are actual source-operator identities on an explicit extended carrier. They do not construct a common bounded action on mixed-parameter physical synthesis, identify the PM Krein form with a positive physical form, intertwine the full Mayer transfer families, or prove complete Weil positivity.

## Lean declarations and audit

`MayerScattering/PrimeLewisBoundaryFunctional.lean`:

- `lewisHeckeOperator_at_one_of_farey_fixed`
- `mayerCompletedLewisCarrier_prime_at_one`

`MayerScattering/AllPrimeBoundaryTransport.lean`:

- `mayerCorrectedHeckeOperator_reconstruct`
- `mayerBoundaryRestore_correctedHeckeOperator`
- `mayerBoundaryCoreCarrier_correctedHeckeOperator`

Both individual final `lake --old env lean` audits pass without warnings. All five transitive axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into the umbrella.
