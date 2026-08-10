# Relative-law observer-descent duality — formalized

- **ID:** `relative-law-observer-descent-duality-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `relative-law-observer-descent-duality.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ObserverDescentDuality` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ObserverDescentDuality.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RelativeConeExactness` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RelativeConeExactness.lean` |

Both wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`, over an arbitrary field —
the card's own hypothesis, and the one its hostile-falsifier list insists on.

1. `pullback` — **card `(ROD.3)`**: precomposition `f*`.
2. `restrictKer` — restriction of an observer to `ker f`.
3. `range_pullback_eq_ker_restrictKer` — **card `(ROD.6)`**, exactness at `Hom(H_C,V)`: an observer
   restricts to zero on the kernel exactly when it is pulled back.  The nontrivial direction
   factors `χ` through `H_C/ker f ≅ im f` and extends along `im f ↪ H_X`
   (`LinearMap.exists_extend`), which is where the field hypothesis is used.
4. `restrictKer_surjective` — **card `(ROD.6)`**, surjectivity, by the same extension.
5. `observerDescentEquiv` — **card `(ROD.7)`, boxed**: `𝓞_f(V) ≅ Hom(ker f, V)`.
6. `descends_iff_vanishes` — **descent–detection complementarity**: an observer descends through
   the exactification exactly when it annihilates every class created by it.
7. `relativeLawEquiv` — **card `(ROD.10)`, boxed**, in the form that takes the exact segment as
   input: `𝓡_f = H^{n-1}(Cone)/im H^{n-1}(X) ≅ ker f`.
8. `relativeObserverDuality` — **card `(ROD.11)`, boxed**: `𝓞_f(V) ≅ Hom(𝓡_f, V)`.
9. `relativePairing`, `relativePairing_well_defined` — **card `(ROD.12)`**: the canonical pairing
   and its well-definedness on both sides.
10. `simultaneous_nonvanishing` — **card §6**: if the forward evaluation vanishes exactly on one
    open half-line and the reflected evaluation on the opposite one, both are nonzero exactly at
    the centre.

The mapping cone, built from scratch so that no exactness is assumed anywhere:

11. `ZCochain`, `cocycles`, `coboundaries`, `cohomology`, `cls` — `ℤ`-graded cochain complexes of
    `k`-vector spaces and their cohomology.  Indexing cohomology by the *lower* degree
    (`H n := ker (d (n+1)) / range (d n)`) avoids every dependent-index cast.
12. `ZCochainMap`, `cocyclesMap`, `cohomologyMap` — comparisons and the induced maps.
13. `coneComplex` — **card `(ROD.5)`**: `Cone(Φ)ⁿ = Xⁿ ⊕ Cⁿ⁺¹` with `d(x,c) = (d_X x − Φ c, −d_C c)`;
    `d² = 0` is exactly the chain-map identity.  `coneInc` — **card `(ROD.8)`**, the inclusion
    `X → Cone(Φ)`; `conePr` — the projection to `H^{n+1}(C)`.
14. `cone_exact_left`, `cone_exact_right` — **card `(ROD.9)`**: the segment
    `Hⁿ(X) → Hⁿ(Cone Φ) → Hⁿ⁺¹(C) → Hⁿ⁺¹(X)` is exact at both middle terms.  No long exact
    sequence machinery is imported; both inclusions are proved by exhibiting the witnessing
    cochains (`(0, b)` on one side, `(x, c)` on the other).
15. `coneRelativeLawEquiv` — **card `(ROD.10)`, boxed, unconditional**; and
    `coneRelativeObserverDuality` — **card `(ROD.11)`, boxed, unconditional**.
16. `sourceCharacter`, `coneCharacter`, `coneCharacter_coneInc`, `coneCharacterRel` — the character
    layer of **cards `(ROD.16)`, `(RRC.26)`–`(RRC.30)`**: a functional on the source that kills
    coboundaries (the card's `I_p D_0 = 0`) defines a character of the cone cohomology, that
    character annihilates every class coming from the target complex — so it reads the shifted
    source coordinate and never the chosen primitive `L_p` — and it therefore descends to the
    relative-law space.
17. `coneCharacterRel_eq` — **cards `(ROD.12)`, `(ROD.17)`–`(ROD.18)`, `(RRC.31)`**, abstract form:
    pairing a cone character with a relative-law class computes the source character on the class
    that the relative law names in `ker f`.  Instantiating `P` at `c_ρ I_p(·)[F_{∓t}]` is exactly
    the card's forward and reflected values; that instantiation names the Route-R objects below.

18. `RouteRSource`, `D₀`, `D₁`, `D₁_comp_D₀`, `complex` — **cards `(RRC.5)`–`(RRC.6)`**: the
    Route-R source datum (prime transport `α`, augmentation `ε`, bilateral Stokes regulator `R`)
    and the three-term source complex `A → A ⊕ ℂ → ℂ`.  `pieceCat`/`truncComplex` place three
    modules in degrees `0, 1, 2` and extend by zero over all of `ℤ`.
19. `eta`, `eta_mem_cocycles`, `regulator`, `regulator_comp_D₀`, `regulator_eta`, `regulatorBar`,
    `regulatorBar_eta` — **cards `(RRC.7)`–`(RRC.9)`**: the retained class `η = (0,1)`, the Stokes
    functional `I(y,z) = z − R(y)`, its vanishing on coboundaries, and the descended
    `Ī : H¹(C) → ℂ` with `Ī[η] = 1`.
20. `eta_class_ne_zero` — **card `(ROD.13)`, first half, unconditional**: `[η] ≠ 0`.  The regulator
    axiom `R(αx − x) = εx` forces it: a primitive would give `εx = R(0) = 0 ≠ 1`.
21. `exactifyComplex`, `exactifyMap`, `exactifyPrimitive`, `exactify_comm_eta`,
    `exactify_cohomologyMap_eta` — **cards `(RRC.10)`–`(RRC.11)`, `(ROD.13)` second half**: the
    universal exactification `X⁰ = A ⊕ ℂ`, `δ₀(x,λ) = D₀x + λη`, with the strict comparison
    `Φ : C → X`, `x ↦ (x,0)`.  The adjoined primitive is `L = (0,1)`, `Φ¹η = δ₀L`, and therefore
    `H¹(Φ)[η] = 0`.  This makes the whole Route-R layer hypothesis-free: the resolved complex is
    constructed, not assumed.
22. `cone_cocycle_of_primitive`, `exactifyConeClass`, `exactify_conePr_coneClass` — **cards
    `(ROD.14a)`, `(ROD.14)`**: `κ = (L, η)` is a cone cocycle and its projection to the source is
    exactly `[η]`.
23. `ellOnePrimes`, `physicalQuotient`, `eulerProfile`, `eulerClass`, `eulerClass_ne_zero_iff` —
    **cards `(RRC.12)`, `(ROD.15)`, `(RRC.14)`**: the fixed physical quotient
    `V = ℂ^𝒫/ℓ¹(𝒫)`, the Euler profile `F_t(p) = p^t·p/(p+1)²`, and
    `[F_t] ≠ 0 ↔ 0 ≤ t`.  Divergence for `t ≥ 0` is the prime harmonic series through
    `p/(p+1)² ≥ 1/(4p)`; convergence for `t < 0` is comparison with `∑ p^{t−1}`.
24. `physChar`, `forwardPhysChar`, `reflectedPhysChar`, `exactify_forward_value`,
    `exactify_reflected_value` — **cards `(RRC.13)`, `(ROD.16)`, `(ROD.17)`, `(ROD.18)`, boxed**:
    the pairing of the observer covector with the relative cone class is `c_ρ[F_{-t}]` forward and
    `c_ρ[F_t]` reflected.
25. `exactify_forward_ne_zero_iff`, `exactify_reflected_ne_zero_iff`, `exactify_both_ne_zero_iff` —
    **card `§6`, boxed**: forward value nonzero exactly for `t ≤ 0`, reflected value nonzero exactly
    for `0 ≤ t`, both nonzero exactly at `t = 0`.

26. `shearRouteRSource`, `shearRouteRSource_eps_ne_zero`, `shearRouteRSource_alpha_ne_id` — **the
    Route-R source datum is inhabited nondegenerately**: on `ℂ²` the shear `(x,y) ↦ (x, y+x)` with
    augmentation `(x,y) ↦ x` and regulator `(x,y) ↦ y` satisfies both axioms with a nonzero
    augmentation and a transport different from the identity.  Everything in items 18–25 is
    therefore a statement about an inhabited class.

## Scope

The exactness that item 7 takes as input is *proved* in items 13–14, so items 15 give `(ROD.10)`
and `(ROD.11)` with no hypotheses at all, and items 16–17 give the character/pairing layer that
`(ROD.16)`–`(ROD.18)` compute with.  Items 18–25 carry out the literal Route-R instantiation
`(ROD.13)`–`(ROD.18)` unconditionally: the source complex, the retained class, the resolved
complex and its comparison, the physical quotient `V = ℂ^𝒫/ℓ¹(𝒫)` and the Euler profile are all
*constructed*, so every displayed value is a theorem with no premises beyond `c_ρ ≠ 0` (card
`(RRC.1)`, which is false at `c_ρ = 0` and so cannot be dropped).  Item 10 formalizes the §6
consequence abstractly from the vanishing pattern, so it imports nothing unproved.

What is *not* claimed: `(ROD.13)`–`(ROD.18)` are proved for the universal exactification of a
Route-R source datum, and `§6`'s dichotomy is proved as a statement about `t`.  The card states
plainly that it does not prove that the actual Xi-divisor `t_ρ` equals `0` — inserting that as an
axiom would be RH-equivalent circularity — and nothing of that kind is claimed here.  The two
remaining open gates (continuous/filtered version, source-derived simultaneous nonvanishing) are
unaffected.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ObserverDescentDuality.lean   # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/RelativeConeExactness.lean   # clean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/RouteRConeCharacter.lean     # clean
lake build GaloisForLFunctions.HTGeometry                                                      # green
```
