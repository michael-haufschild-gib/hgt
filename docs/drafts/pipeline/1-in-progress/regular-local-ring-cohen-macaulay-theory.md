# Local Cohen–Macaulay theory: regular local rings are domains, and systems of parameters are regular sequences

- **ID:** `regular-local-ring-cohen-macaulay-theory`
- **Stage:** 1-in-progress
- **Type:** INFRASTRUCTURE / COMMUTATIVE ALGEBRA
- **Scientific status:** `[CLASSICAL] [NOT NEW SCIENTIFIC KNOWLEDGE]` — standard theory, absent from mathlib
- **Consumers:**
  - `hypertranscendental-maximal-finite-horizon-galois-law` (card 7 of
    `03-ht-translation-projective-geometry`), Brick D: the block cover is étale at every closed point
  - `projective-horizon-hankel-secant-stratification` (card 11), normality for `r ≥ 2` via Serre

## Why

Both open cards of the `03-ht-translation-projective-geometry` folder reduce to one classical
statement that mathlib does not have:

```text
a system of parameters of a Cohen–Macaulay (in particular regular) local ring is a regular sequence.
```

mathlib has, as of this toolchain:

```text
IsRegularLocalRing                                      bare definition (spanFinrank 𝔪 = dim)
IsRegularLocalRing.of_spanFinrank_maximalIdeal_le       and its cotangent-space form
ModuleCat.exists_isRegular_tfae                         Rees's theorem (RingTheory/Depth/Rees.lean)
ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank   dim R ≤ dim R/I + spanFinrank I
Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
                                                        dim M/xM + 1 = dim M off the minimal primes
Module.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
Ideal.height_le_spanRank_toENat                         Krull's height theorem
```

but **no** depth, **no** Cohen–Macaulay, **no** Koszul complexes, **no** "regular local ⟹ domain",
and no gl.dim of a regular local ring.

## The chain to build

```text
1. exists_span_insert_of_notMem_sq   x ∈ 𝔪 \ 𝔪² extends to a minimal generating set of 𝔪
2. IsRegularLocalRing.isDomain       regular local ⟹ domain
     induction on dim: prime-avoid 𝔪² and the minimal primes to get x; R/(x) is regular local of
     dimension one less by (1) and mathlib's dimension lemmas; by induction (x) is prime; a minimal
     prime p ⊆ (x) satisfies p = x·p, so p = ⊥ by Nakayama.
3. isRegular_regularSystemOfParameters   a minimal generating set of 𝔪 is an R-regular sequence
     each successive quotient is regular local by (1), hence a domain by (2).
4. grade / HasDepthGE via Rees, and its radical invariance
     hasDepthGE_of_radical_eq is already proved in scratch: conditions (1) of the two TFAEs are
     literally the same statement, because zeroLocus depends only on the radical.
5. grade drop modulo a regular element (Ext long exact sequence)
6. depth transfer along a finite ring map (Ass_A M = contractions of Ass_D M, then induct with (5))
7. gl.dim of a regular local ring: pd(k) = dim by
     projectiveDimension_quotient_eq_length applied to (3), then pd(N) ≤ pd(k)
8. Auslander–Buchsbaum in the only form needed:
     M finite over regular local A of dim d with an M-regular sequence of length d in 𝔪 ⟹ M free
     (projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular + (7))
```

Steps (4) and (8) are what Brick D of card 7 consumes: `D` regular ⟹ `grade_D(𝔪_D, D) = d` by (3),
radical invariance (4) moves it to `𝔪_A D`, the transfer (6) moves it to `𝔪_A` acting on `D`, the
trace retraction moves it to `B''`, and (8) makes `B''` free over `A` — after which the discriminant
argument already recorded on card 7 gives étaleness.

## Progress

- **Step 4 (radical invariance) — verified in scratch**, three lines from Rees's TFAE.
- Steps 1–3 are the next build.
