# Relative-law observer-descent duality — formalized

- **ID:** `relative-law-observer-descent-duality-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `relative-law-observer-descent-duality.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ObserverDescentDuality` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ObserverDescentDuality.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

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
7. `relativeLawEquiv` — **card `(ROD.10)`, boxed**: for the exact segment supplied by the mapping
   cone, `𝓡_f = H^{n-1}(Cone)/im H^{n-1}(X) ≅ ker f`.  The mapping-cone long exact sequence is
   classical and is taken as the *input* exactness `range g = ker π`, `range π = ker f`, exactly as
   the card cites it.
8. `relativeObserverDuality` — **card `(ROD.11)`, boxed**: `𝓞_f(V) ≅ Hom(𝓡_f, V)`.
9. `relativePairing`, `relativePairing_well_defined` — **card `(ROD.12)`**: the canonical pairing
   and its well-definedness on both sides.
10. `simultaneous_nonvanishing` — **card §6**: if the forward evaluation vanishes exactly on one
    open half-line and the reflected evaluation on the opposite one, both are nonzero exactly at
    the centre.

## Scope

The literal Route-R instantiation `(ROD.13)`–`(ROD.18)` names objects built in
`route-r-raw-resolved-relative-cone-character-law`, which is still in stage 2; it is therefore not
instantiated here.  Item 10 formalizes the §6 consequence abstractly from the vanishing pattern, so
it imports nothing unproved.  The card states plainly that it does not prove the simultaneous
nonvanishing and that inserting it as an axiom would be RH-equivalent circularity; nothing of that
kind is claimed.  The two remaining open gates (continuous/filtered version, source-derived
simultaneous nonvanishing) are unaffected.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ObserverDescentDuality.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.ObserverDescentDuality          # green
```
