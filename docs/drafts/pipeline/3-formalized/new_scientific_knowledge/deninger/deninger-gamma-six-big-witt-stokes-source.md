# Deninger Gamma-six Big-Witt Stokes source

- **ID:** deninger-gamma-six-big-witt-stokes-source
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route L, canonical arbitrary-ring big-Witt source
- **Statement:** The unique first-ghost-null Teichmüller codiagonal has a division-free quadratic Green source; at faces `1/2` and `1/3` it forces the exact Gamma-six atom `1/6` and tail `5/6` already read by the Route-L Wold and Gibbs layers.

## Goal

Produce a genuinely mixed, source-generated class before any physical landing. Route L already
proved canonical big-Witt multiplication over every commutative ring, the Gamma-six Wold
compression coefficient `1/6`, shell mass `5`, and physical Gibbs continuation. Missing was a
single source law explaining why the same constants occur together rather than entering as
independent normalizations.

This theorem supplies that law. It does not prove the global strict source-to-physical lift, target
boundary annihilation, or RH.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and division-free attack
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: Lean module `DeningerGammaSixBigWittStokesSource`
- [ ] 3 → 4 publication-ready: external novelty review and integration into Route-L paper

## Theorem `[PROVED HERE]`

Let `A` be any commutative ring. No reducedness, torsion-freeness, characteristic, domain, or
field assumption is made. In the canonical big-Witt ring `Λ(A)`, write `[a]` for the
Teichmüller factor with literal series `1-aT`, and define

```text
C(a,b) = [a] + [b] - [a+b].
```

Then:

1. `gh₁(C(a,b))=0`. More strongly, `gh₁([a]+[b]-[c])=0` iff `c=a+b`.
2. The literal series `S(C(a,b))` satisfies the division-free Green equation

   ```text
   (1-(a+b)T)(S(C(a,b))-1) = ab T².
   ```

3. `C(a,b)=0` iff `ab=0`. Equivalently, `C(a,b)=0` iff `[a]⊙[b]=0`.

For `A=ℚ`, `a=1/2`, and `b=1/3`, put

```text
u = ab = 1/6,       v = a+b = 5/6,
ω₆ = C(1/2,1/3).
```

Then `gh₁(ω₆)=0`, `ω₆≠0`, and

```text
(1-vT)(S(ω₆)-1) = uT²,
[1/2]⊙[1/3] = [u],
v = 1-u.
```

The unordered rational faces are rigid: if `a+b=5/6` and `ab=1/6`, then
`{a,b}={1/2,1/3}`. Existing Route-L theorems identify this same `u` with the Wold compression
eigenvalue and this same `6v=5` with shell trace mass; the existing physical continuation is
`u(1-u^δ)`.

## Proof

Big-Witt addition is literal multiplication of series. The balance identity

```text
C(a,b)+[a+b]=[a]+[b]
```

therefore gives, without division,

```text
S(C(a,b))(1-(a+b)T)=(1-aT)(1-bT).
```

Subtract `1-(a+b)T` from both sides and expand. Linear terms cancel and the remainder is
`abT²`, proving the Green equation.

The first ghost component is additive and sends `[x]` to `x`, hence
`gh₁([a]+[b]-[c])=a+b-c`; this proves both first-ghost assertions.

If `C(a,b)=0`, the Green equation has zero left side. Its coefficient of `T²` is `ab`, so
`ab=0`. Conversely, if `ab=0`, expansion gives

```text
(1-aT)(1-bT)=1-(a+b)T.
```

Injectivity of the literal-series carrier then gives `[a]+[b]=[a+b]`, hence `C(a,b)=0`.
Canonical Teichmüller multiplication gives `[a]⊙[b]=[ab]`; injectivity of `[·]` proves the
equivalent product criterion. This coefficient proof remains valid with nilpotents and in positive
characteristic; it never invokes ghost injectivity.

For the rational specialization, direct field identities give
`1/2+1/3=5/6`, `(1/2)(1/3)=1/6`, and `5/6=1-1/6`. Nonvanishing follows from
`(1/2)(1/3)≠0`. If rational `a,b` have the same sum and product, then

```text
(2a-1)(3a-1)=6a²-5a+1=0,
```

so `a` is `1/2` or `1/3`, and the sum fixes `b`. Existing formal Wold, shell-trace, and Gibbs
identities finish the source-to-reader coefficient comparison.

## Conjecture loop and failures

1. **Nilpotent multiplicity thickening.** Failed novelty audit: already classified by the
   arbitrary-ring big-Witt and rational-Witt nilpotent modules.
2. **Dual-number second cross-effect.** Failed significance audit: re-encoded the already formal
   Hodge mass and introduced no new source law.
3. **Frobenius/Verschiebung commutator at `2,3`.** Failed as producer: coprime operations commute;
   resulting identity is classical zero curvature.
4. **Teichmüller additivity cross-effect.** Survived. Its first ghost vanishes while its literal
   class is nonzero exactly when the mixed face product is nonzero. The denominator-cleared
   remainder simultaneously generates `1/6` and `5/6`.

## Novelty boundary

Generic big-Witt ring laws and Teichmüller factors are classical; see Lenstra,
[*Construction of the Ring of Witt Vectors*](https://math.berkeley.edu/~hwl/papers/witt.pdf),
Cuntz--Deninger [arXiv:1410.5249](https://arxiv.org/abs/1410.5249), and Hesselholt
[arXiv:1006.3125](https://arxiv.org/abs/1006.3125). This card claims no novelty for those facts or
for the elementary polynomial expansion in isolation.

Corpus search and targeted primary-literature search found no prior identification of the
first-ghost-null cross-prime codiagonal `C(1/2,1/3)` with the Deninger Gamma-six Wold atom,
regular tail, shell mass, and Gibbs continuation. That source-specific constitutive weld is the
candidate new result. External novelty verification remains required before publication.

## Hostile audit

- **Not an RH proof.** No target complex, completed Xi Green vector, or physical cyclicity follows.
- **Not a hidden ghost-injectivity argument.** Vanishing is read from one literal coefficient, so
  nilpotents and torsion remain present.
- **Not normalization freedom.** First-ghost cancellation forces the codiagonal face `a+b`; sum
  and product rigidly force the unordered rational pair `{1/2,1/3}`.
- **Frontier movement is narrow.** This removes independent choice of Route-L atom/tail constants
  and constructs a nonzero mixed source radical class. Remaining hard frontier is to transport
  this exact class through the global trace-ideal-preserving chain lift and prove its fixed
  physical boundary is annihilated.

## Lean certificate

File:
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerGammaSixBigWittStokesSource.lean`

Capstone:
`RHTower.DAC_DENINGER_GAMMA_SIX_BIG_WITT_STOKES_SOURCE`

Supporting declarations include:

- `deningerBigWittTeichmullerCodiagonal_ghost_one_eq_zero_iff`
- `deningerBigWittTeichmullerCrossEffect_green`
- `deningerBigWittTeichmullerCrossEffect_eq_zero_iff`
- `deningerBigWittTeichmullerCrossEffect_eq_zero_iff_mul_zero`
- `deningerGammaSixBigWittFaces_rigid`
- `deningerGammaSixBigWittCoefficients_control_wold`
- `deningerGammaSixGreenGibbsContinuation_eq_bigWittAtom`

All mathematical statements are closed theorems over existing definitions. No new axiom or
unproved premise is introduced.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerGammaSixBigWittStokesSource.lean` passed.
- Targeted `lake build GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixBigWittStokesSource` passed;
  no umbrella or full build was run.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Repository lint reports no issue in this module and confirms umbrella reachability. It exits
  nonzero on unrelated concurrently unwired modules.

## Log

- 2026-08-15 — conjecture loop, paper proof, and Lean formalization completed.
