# The divisibility firewall, and the exceptional-unit reformulation of `rank K₂(𝒪_F) = 0`

- **ID:** `k2-rank-divisibility-firewall`
- **Stage:** 1-in-progress
- **Type:** NO-GO + REFORMULATION (route selection for `garland-tame-kernel-torsion`)
- **Serves:** `deninger-algebraic-cyclotomic-milnor-amplitude` (its `(1)`), `garland-tame-kernel-torsion`
- **Created:** 2026-08-18

## Why this card exists

The programme card `garland-formalization-programme` selected Garland's 1973 `p`-adic curvature
method; the route audit of 2026-08-18 showed it cannot reach `SL_n(𝒪_S)` (non-uniform lattice,
infinite cell stabilizers).  The natural replacement hypothesis was: *do it with algebra instead* —
Moore's reciprocity, Tate's `K₂(F)/m ≅ H²(F, μ_m^{⊗2})`, Poitou–Tate, and the Iwasawa-theoretic
vanishing `H²(𝒪_S, ℚ_p(j)) = 0` for `j ≥ 2`.  This card settles that hypothesis in the negative,
proves the obstruction unconditionally in Lean, and replaces it with a reformulation that is not
blocked by it.

## 1. The no-go `[PROVED HERE]` `[K2_DIVISIBILITY_FIREWALL]`

Let `A` be an abelian group, `V` a nonzero `ℚ`-vector space, and `T = ⨁_{i∈I} G_i` a direct sum of
**finite** abelian groups.  Then

1. for every `m ≠ 0` and every `x ∈ A × V`, `x` is divisible by `m` in `A × V` **iff** its first
   component is divisible by `m` in `A`;
2. `x ∈ A × V` is torsion **iff** its second component is `0` and its first component is torsion;
3. every homomorphism `A × V → T` kills `V`;
4. `A × V` is **not** torsion.

### Proof

`V` is uniquely divisible and torsion free, which gives `(1)`, `(2)` and `(4)` at once.  For `(3)`,
let `φ : A × V → T` and `v ∈ V`.  For every `n ≠ 0` write `v = n·w`; then
`φ(0,v) = n·φ(0,w) ∈ nT`.  So `φ(0,v)` lies in `⋂_n nT`.  For `t ∈ ⋂_n nT` and any coordinate `i`,
`t_i ∈ n·G_i` for every `n`; taking `n = |G_i|` gives `t_i = 0`.  Hence `t = 0`. ∎

The third item is the one with arithmetic teeth: **the target of every family of tame symbols, of
every family of Hilbert symbols, and of Moore's reciprocity sequence is a direct sum of finite
groups.**

### The consequence for route selection

Read with `A = K₂(𝒪_F)`.  Adjoining a `ℚ`-vector space `V` to `K₂(𝒪_F)` (and hence to `K₂(F)`)
preserves:

- every group `K₂(F)/m` and every `Tor(K₂(F), ℤ/m)` — hence every instance of the Tate /
  Merkurjev–Suslin isomorphism `K₂(F)/m ≅ H²(F, μ_m^{⊗2})`, and every étale-cohomological
  computation of those groups, including finiteness of `H²_ét(𝒪_S, ℤ_p(2))`;
- the torsion subgroup, and the localization sequence `0 → K₂(𝒪_S) → K₂(F) → ⊕_v κ(v)^× → 0`
  (the perturbation maps to `0` by item `(3)`);
- Moore's exact sequence `K₂(F) → ⊕_{v ∈ S_nc} μ(F_v) → μ(F) → 1`, again by item `(3)`;
- the wild kernel, which absorbs `V`.

and it destroys the conclusion.  Therefore **no combination of finite-coefficient statements can
prove that `K₂(𝒪_F)` is torsion.**  Any proof must contain a step whose input does not factor
through the mod-`m` theory.  In the literature there are exactly two such inputs: finite generation
of the integral group (Quillen, via the geometric finiteness of arithmetic groups), and a direct
rank computation (Borel; equivalently Garland 1971).

This also settles the sub-question that motivated the card: the Iwasawa-theoretic vanishing
`H²(𝒪_S, ℚ_p(j)) = 0` for `j ≥ 2` is *not* an independent substitute.  It is a statement about the
`p`-adic completion, i.e. about `K₂/div`, and in the literature (Soulé 1979) it is deduced from
Borel's rank computation through the surjectivity of the étale Chern classes.  The firewall explains
structurally why no such statement could be independent.

## 2. What the firewall leaves open, and the reformulation `[BRIDGE]`

The firewall says the missing input must be integral.  The cheapest integral input is *finite
generation*, and the following reformulation turns the whole problem into finite-dimensional linear
algebra over `ℚ` indexed by `S`-unit equations.

Write `V_S := 𝒪_S^× ⊗ ℚ`, a `ℚ`-vector space of dimension `|S| − 1` by Dirichlet.  Since
`K₂^M(F) = (F^× ⊗ F^×)/⟨a ⊗ (1−a)⟩` and the Steinberg relation forces antisymmetry,

```text
K₂^M(F) ⊗ ℚ  =  Λ²_ℚ(F^× ⊗ ℚ) / span_ℚ{ a ∧ (1−a) : a ∈ F ∖ {0,1} }.
```

`[BRIDGE] [K2_EXCEPTIONAL_UNIT_SPANNING]`

> `K₂^M(F) ⊗ ℚ = 0` **iff** for every finite `S ⊇ S_∞` there is a finite `S' ⊇ S` with
> `Λ²(V_S) ⊆ span_ℚ{ a ∧ (1−a) : a, 1−a ∈ 𝒪_{S'}^× }` inside `Λ²(V_{S'})`.

The equivalence is immediate from the displayed presentation together with
`F^× ⊗ ℚ = colim_S V_S` and the fact that every `a` with `a ∈ 𝒪_S^×` becomes an *exceptional*
`S'`-unit for `S' = S ∪ supp(1−a)`.

Three things make this the right shape to attack.

- **It is finite dimensional at each stage.**  `dim Λ²(V_S) = binom(|S|−1, 2)`, quadratic in `|S|`,
  while the number of solutions of the `S`-unit equation `a + b = 1` grows exponentially in `|S|`
  (Evertse; and for `F = ℚ` explicitly).  The count is not the obstruction.
- **It is exactly Tate's theorem when `F = ℚ`, and the corpus has it.**  For `S = {∞,2,3}`:
  `a = 3` gives `3 ∧ (−2) = −(2∧3)`, which spans `Λ²(V_S) = ℚ·(2∧3)`.  For `S = {∞,2,3,5}`:
  `a = 3` gives `3∧2`, `a = 5` gives `2·(5∧2)`, `a = 6` gives `2∧5 + 3∧5`; together they span the
  three-dimensional `Λ²(V_S)`.  The Euclidean descent formalized in
  `HTGeometry/MilnorKTateEuclid.lean` is precisely a systematic production of these vectors.
- **It isolates the obstruction.**  For `F` of unit rank `≥ 2` the directions `u ∧ u'` with
  `u, u'` units of `𝒪_F` cannot be reached by exceptional units of `𝒪_F` itself (there may be
  none), so the spanning must be achieved through vectors `u ∧ (1−u)` whose prime parts cancel in a
  larger `S'`.  **That cancellation is the exact open core.**

`[OPEN CORE]` For a number field `F` of unit rank `≥ 2`, produce explicitly, for each pair of
units `u, u'` of `𝒪_F`, a finite `S'` and a rational combination of vectors `a ∧ (1−a)`
(`a, 1−a ∈ 𝒪_{S'}^×`) equal to `u ∧ u'` in `Λ²(V_{S'})`.

A proof of the open core would be an **elementary, effective proof of the rank-zero half of Borel's
theorem in weight two** — which the literature does not have — and would make the whole card
`deninger-algebraic-cyclotomic-milnor-amplitude` unconditional without any analysis.  Its failure
would be equally informative: by the equivalence it would contradict Garland's theorem, so it cannot
fail; what can fail is only the *effectivity*, and the search for the obstruction to effectivity is
itself the next research step.

## 3. Lean

`formal/GaloisForLFunctions/HTGeometry/DivisibilityFirewall.lean`, wired into the `HTGeometry`
umbrella.  Axiom audit for every declaration: `propext, Classical.choice, Quot.sound`.

```text
directSumFinite_eq_zero_of_forall_nsmul   a direct sum of finite groups has no nonzero element
                                          divisible by every natural number
firewall_nsmul_iff                        the mod-m classes are blind to a rational summand
firewall_torsion_iff                      the torsion is blind to a rational summand
firewall_hom_directSumFinite              ** every map into a direct sum of finite groups is blind **
firewall_not_torsion                      a rational summand destroys torsion
divisibility_firewall                     ** the four together: the no-go **

exists_int_surjection_of_not_isTorsion    ** f.g. + not torsion  ==>  a ℤ-quotient **
exists_zmod_surjection_of_not_isTorsion   ** hence a surjection onto ℤ/m for every m **
isTorsion_of_fg_of_no_int_quotient        ** the firewall is broken exactly by finite generation **
```

The last three are the converse half and they matter as much as the no-go: they say that finite
generation is not merely *a* way past the firewall, it is *the* way — for a finitely generated group
the failure of torsion is visible modulo every `m`, so once finite generation is in hand the
mod-`m` theory suffices.  This pins the missing input of the card exactly.

### The integral form of the bridge is FALSE — do not attempt it

"`K₂(𝒪_S)` is generated by Steinberg symbols of `S`-units" is **false**: for imaginary quadratic `F`
the only units are roots of unity, so unit symbols generate a group of exponent dividing `2`
(spanned by `{-1,-1}`), while computed tame kernels of imaginary quadratic fields are larger.  Only
the **rational** spanning statement of §2 is available, and it is genuinely weaker — which is exactly
why it is not contradicted.

## 4. Hostile audit

- **Not a claim that `K₂(𝒪_F)` is non-torsion.**  It is torsion (Garland).  The firewall is a
  statement about which *proofs* are possible, and it is proved unconditionally.
- **Not circular.**  The firewall is pure abelian-group theory; no arithmetic input.
- **The reformulation is an equivalence, not a weakening.**  It does not assume the conclusion; both
  directions are proved from the presentation of `K₂^M`.
- **Novelty, stated honestly.**  Item `(3)` and the perturbation argument are elementary; what is
  new here is the *use*: a precise, machine-checked statement of which classes of arithmetic input
  are provably insufficient for the rank statement, and the resulting redirection of a formalization
  programme.  The exceptional-unit spanning form of `rank K₂ = 0` is, as far as the August-2026
  literature shows, not stated anywhere as the definition of the problem, and it converts an
  analytic theorem into a Diophantine one.
- **Effectivity is untouched.**  Nothing here proves the open core.

## 5. Consequences for the programme

1. Retire Layers D1–D3 and C5 of `garland-formalization-programme` *for this target*.
2. Do not attempt a Moore/Tate/Iwasawa route: it is provably insufficient (§1).
3. The two viable integral inputs are (a) finite generation of `K₂(𝒪_S)` and (b) the exceptional-unit
   spanning of §2.  Route (b) needs no geometry at all.
4. Route (a) is reachable without analysis as well: `SL_n(𝒪_F)` acts cocompactly with **finite**
   stabilizers on Ash's well-rounded retract, a contractible complex built from reduction theory
   (Minkowski/Voronoi), which gives `H_i(SL_n(𝒪_F), ℤ)` finitely generated and hence `K₂(𝒪_S)`
   finitely generated.  This replaces Borel's analysis by geometry of numbers — but by §1 it must
   still be combined with a mod-`m` bound, so it is strictly more expensive than route (b).

## Log

- 2026-08-18 — Card opened.  Firewall proved and formalized; Moore/Tate/Iwasawa route excluded;
  exceptional-unit spanning frozen as the replacement bridge with its open core.

## 6. The stage-by-stage criterion — the firewall broken, one stage at a time `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKStageCriterion.lean` (wired into the `HTGeometry`
umbrella; axiom audit for all declarations `propext, Classical.choice, Quot.sound`).

The firewall says the mod-`m` theory cannot decide whether `K₂^M(F)` is torsion, because a directed
union of infinite cyclic groups can be `ℚ`.  Its converse says finite generation restores
decidability.  `K₂^M(F)` **is** such a directed union, and every stage **is** finitely generated —
so the obstruction dissolves stage by stage:

```text
symbolStage G                                    = symbolSubgroup (closure G),  G : Finset Fˣ
symbolStage_fg, symbolStage_addGroup_fg          ** every stage is finitely generated **
milnorKDegTwo_le_torsion_iff_stages              K₂^M(F) is torsion iff every stage is
symbolStage_le_torsion_iff_no_int_quotient       ** a stage is torsion iff it has no ℤ-quotient **
milnorKDegTwo_le_torsion_iff_no_stage_int_quotient
                                                 ** K₂^M(F) is torsion  ⟺  no stage surjects onto ℤ **
symbolStage_mono
milnorKDegTwo_le_torsion_of_cofinal_stages       ** a cofinal family of stages suffices **
```

The last item is the formal counterpart of the freedom the exceptional-unit formulation of §2 uses:
to control a symbol one may enlarge the set of units until enough Steinberg relations `{g, 1−g} = 0`
are available.

### What this changes

`rank K₂(𝒪_F) = 0` — an analytic theorem of Borel, equivalently Garland 1971 — is now equivalent, in
Lean, to a statement about a **directed system of finitely generated abelian groups**, each decided
by its `ℤ`-quotients.  The rank of the stage `symbolStage G` is `binom(|G|, 2)` minus the rank of the
lattice of Steinberg relations available inside `⟨G⟩`, so the criterion reads:

> for a cofinal family of finite `G ⊆ Fˣ`, the Steinberg vectors `g ∧ (1−g)` available inside
> `⟨G⟩` must span `Λ²(⟨G⟩ ⊗ ℚ)`.

which is §2's bridge at finite level.  This is the sharpest formulation the corpus now owns, it is
entirely elementary, and it is the statement any future elementary proof has to establish.

## 7. The reduction is now sharp: single symbols, dependence, and the subtraction identity `[PROVED]`

Same module.  Three further theorems bring the target down to its irreducible core.

```text
milnorKDegTwo_le_torsion_iff_symbols     ** K₂^M(F) is torsion  ⟺  every single symbol {a,b} is **
milnorSym2_mem_torsion_of_dependent      ** aᵐbⁿ = 1 with m ≠ 0  ⟹  {a,b} is torsion **
subUnit, milnorSym2_sub_identity         ** {a,b} = {a/b, b − a} + {−1, b} **
```

- The first is the exhaustion in its most usable form: the stage machinery collapses, because a
  two-element stage already contains an arbitrary symbol.
- The second disposes of every **multiplicatively dependent** pair in one line — `m·{a,b} = {aᵐ,b}
  = {b⁻ⁿ,b} = −n·{b,b}` and `{b,b} = {−1,b}` is killed by two — with no structure theory.  It
  subsumes the rank-at-most-one theorem for a single symbol.
- The third is the Steinberg relation at `x = a/b` expanded in both slots.  It is *the* Euclidean
  move: it trades `{a,b}` for a symbol whose second entry is the remainder `b − a`.

**So the entire remaining content of `rank K₂(𝒪_F) = 0` is: for a multiplicatively independent pair
`a, b` in a number field, `{a,b}` is torsion.**  Everything else in the card's `(1)` is now formal.
The subtraction identity is the only known engine for attacking such a pair, and over `ℤ` iterating
it terminates because `|b − a| < max(|a|,|b|)` can be arranged; over a field with two or more
archimedean places no size function decreases, which is the precise obstruction recorded in
`garland-tame-kernel-torsion`.

## 8. The cyclotomic engine `[PROVED]`

Same module.  The reduction of §7 leaves one statement — `{a,b}` torsion for multiplicatively
independent `a, b`.  There is an unconditional, elementary supply of torsion symbols that attacks
exactly that, and it is now formal.

```text
milnorSym2_zpow_oneSub_isTorsion   ** n·{a, 1 − aⁿ} = 0 **   (Steinberg at aⁿ, left slot ℤ-linear)
milnorSym2_zpow_oneSub_mem_torsion  hence {a, 1 − aⁿ} is torsion for n ≠ 0
leftStab, rightStab, mem_leftStab, mem_rightStab
torsionPartners a                   ** {b : {a,b} is torsion} is a SUBGROUP of Fˣ **
oneSub_zpow_mem_torsionPartners     1 − aⁿ is always a torsion partner of a
milnorKDegTwo_le_torsion_iff_torsionPartners
                                    K₂^M(F) is torsion ⟺ torsionPartners a = ⊤ for every a
symbolSubgroup_top
milnorKDegTwo_closure_of_generating ** symbols of any generating set of Fˣ generate K₂^M(F) **
milnorKDegTwo_le_torsion_of_generating   torsion is decided on any generating set
```

### The engine, and exactly where it stalls

`torsionPartners a` is a subgroup containing `1 − aⁿ` for every `n ≠ 0`.  Over a Dedekind domain with
finite residue fields this is a genuine induction: for a prime `π ∤ a` the residue `ā` has finite
order `n` in the finite group `κ(π)^×`, so `π ∣ aⁿ − 1`, and `1 − aⁿ` factors as a unit times primes
all of which divide `aⁿ − 1`.  If all but one of those factors is already known to be a torsion
partner, the subgroup property delivers the last one.

Worked over `ℚ` with `a = 2`: `1−2² = −3` gives `{2,3}`; `1−2³ = −7` gives `{2,7}`;
`1−2⁴ = −3·5` then gives `{2,5}`; `1−2⁸ = −3·5·17` gives `{2,17}`; `1−2¹⁰ = −3·11·31` gives
`{2,11}`, and so on — every odd prime is reached because `2` has finite order modulo it.

**Where it stalls**: when `aⁿ − 1` has *two or more* primitive prime divisors at the same level `n`,
the relation only makes their **sum** a torsion partner, not each separately.  Separating them
requires relations from a different base `a`, and whether the resulting system of relations spans is
precisely the exceptional-unit spanning question of §2.  So the engine reduces `rank K₂ = 0` to a
concrete, finite-level **linear-algebra-over-ℚ question about `S`-unit equations**, with no analysis
anywhere in sight — which is the strongest formulation this card can currently support.

### The arithmetic half of the engine `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/DedekindResidueFieldAtPlace.lean`.

```text
exists_pow_sub_one_mem_of_finite_quotient
    I maximal with finite residue ring, a ∉ I  ⟹  ∃ n > 0, aⁿ − 1 ∈ I
```

The residue of `a` is a nonzero element of a finite field, hence a root of unity.  This is exactly
what guarantees that *every* prime not dividing `a` occurs in the factorisation of some `1 − aⁿ`,
and `{a, 1 − aⁿ}` is always `n`-torsion — so the cyclotomic engine reaches every prime.  What it
cannot yet do is **separate** two primes that first appear at the same level `n`; that separation is
the open core.

## 9. Tate's theorem transported: rational entries are torsion everywhere `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/MilnorKRationalEntries.lean` (wired, axiom-clean).

Functoriality of Milnor `K`-theory is an additive map, so it carries torsion to torsion.  Applied to
the corpus's formalization of Tate's theorem this gives, unconditionally:

```text
milnorKDegMap_mem_torsion                    functoriality preserves torsion
milnorKDegMap_milnorSym2                     the induced map on degree-two symbols
symbolSubgroup_range_le_torsion_of_torsion   ** K₂^M(F) torsion ⟹ the symbols of f(Fˣ) are
                                                torsion in K₂^M(E), for any f : F →+* E **
milnorSym2_rat_mem_torsion                   ** {a,b} is torsion in K₂^M(E) for all a,b ∈ ℚˣ,
                                                for EVERY field E of characteristic zero **
symbolSubgroup_rat_le_torsion                the rational symbols span a torsion subgroup
rat_mem_torsionPartners                      every rational unit is a torsion partner of every other
```

So for a number field `F` the symbols `{a, b}` with `a, b ∈ ℚˣ` are settled outright — this is the
first infinite family of symbols in an arbitrary number field that the corpus proves torsion without
any hypothesis.  Together with:

- `milnorSym2_mem_torsion_of_dependent` (multiplicatively dependent pairs),
- `oneSub_zpow_mem_torsionPartners` (the cyclotomic family `1 − aⁿ`),
- `torsionPartners` being a subgroup,

the provably-torsion part of `K₂^M(F)` now contains: everything generated by rational units, every
dependent pair, and every partner reachable from the cyclotomic relations.  What is **not** yet
reachable is a symbol `{a, b}` in which `a` and `b` are independent and neither is rational — and
the separation obstruction of §8 is exactly why.
