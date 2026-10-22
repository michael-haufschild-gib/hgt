# Integral Brauer induction by concrete monomial characters

- **ID:** `artin-brauer-integral-monomial-induction`
- **Stage:** 1-in-progress
- **Type:** THEOREM (literature infrastructure)
- **Status:** `[LITERATURE] [BRIDGE] [NOT NEW]`
- **Statement:** every concrete `VirtualCharacter G` of a finite group is a finite
  \(\mathbb Z\)-linear combination of `monomialVirtualCharacter G H lambda`, with every `H`
  Brauer-elementary and every `lambda` linear.

## Goal

Formalize the *integral* finite-character input for Brauer's meromorphic-continuation theorem.
The downstream Lean form must be an actual finitely supported integer coefficient function, not a
span membership proposition:

```text
forall theta : VirtualCharacter G,
  exists c : brauerElementaryMonomialIndex G ->₀ Z,
    theta = c.sum (fun q n => n • brauerElementaryMonomialVirtualCharacter G q),
```

Each generator is already indexed by an elementary witness, so there is no hidden support
predicate.  A Brauer-elementary group is a product of a cyclic group of order prime to a prime
\(p\) and a \(p\)-group.  Forgetting that witness gives the unrestricted all-subgroup `Finsupp`
equality as a downstream API.

The concrete generator index has been source-checked in scratch as data, not a bare predicate:

```text
BrauerElementarySubgroup G :=
  subgroup, prime p, internal cyclic p'-part, internal p-part,
  multiplication equivalence C × P ≃* subgroup,
  and proof that it is actual multiplication.

brauerElementaryMonomialIndex G :=
  Σ E : BrauerElementarySubgroup G, LinearCharacter E.subgroup.
```

## Literature frontier

Brauer's integral induction theorem is exactly the theorem needed here; Artin's rational cyclic
induction is strictly weaker.  Rational coefficients only give a meromorphic power of an Artin
factor, whereas integer exponents yield the factor itself as a quotient of degree-one/Hecke
factors.  Primary/authoritative sources:

- R. Brauer, *On Artin's L-series with general group characters* (1947),
  https://www.jstor.org/stable/1969183
- J. Cogdell, *On Artin L-functions*, pp. 9–10,
  https://math.osu.edu/~cogdell/artin-www.pdf
- S. Gun, S. Hazra, D. Sahu, *On holomorphy and non-vanishing of Artin L-functions* (2025),
  https://doi.org/10.1007/s00605-025-02060-7

## Internal frontier

`ArtinMonomialCharacter.lean` supplies the actual induced linear generators;
`ArtinVirtualFrobeniusReciprocity.lean` transports their multiplicities; and
`ArtinMonomialMultiplicitySeparation.lean` proves those multiplicities jointly separate virtual
characters.  The separation theorem is not an integral spanning theorem.  Maschke's module
decomposition supplies simple summands but not a finite irreducible-character lattice or Brauer
induction.  No project or Mathlib Brauer character-induction theorem exists.

## Paper-proof route and `[OPEN CORE]`

Classically, Brauer proves the character-ring statement by induction on group order, reducing
through elementary subgroups and using character-theoretic integrality.  The first dependency-
closed group-theoretic lemma is closure of concrete elementary data under subgroups:

```text
forall E : BrauerElementarySubgroup G, forall K <= E.subgroup,
  exists E' : BrauerElementarySubgroup G,
    E'.subgroup = image(K -> E.subgroup -> G).
```

Its paper proof writes \(E=C\times P\).  A sufficiently large power of \(p\) kills the
\(P\)-coordinate and is an automorphism of the coprime-order cyclic part \(C\); hence every
element of \(K\) splits into its two coordinates in \(K\), so
\(K=(K\cap C)\times(K\cap P)\).  Cyclicity, coprimality, and the \(p\)-group property inherit.

The exact remaining paper-to-Lean core is not a local algebra lemma:

```text
[OPEN CORE] Build a finite irreducible-character lattice with integral coordinates and formalize
the elementary-subgroup induction step that places every coordinate in the monomial lattice.
```

No Brauer-induction proof infrastructure is started until that proof is written dependency-closed
in the project vocabulary and its finite-group APIs are source-checked.  The existing literature
proves the theorem, but does not supply a ready Lean dependency graph.

The exact generator carrier is now present in
`formal/GaloisForLFunctions/RHTower/Artin/ArtinBrauerElementary.lean`; it defines only the concrete
elementary witness, index, and induced-linear virtual character.  It contains no claimed span,
closure, or induction theorem.

## Hostile non-circularity audit

- Rational Artin induction is insufficient: clearing denominators proves meromorphicity only of a
  power, not of an individual Artin factor.
- Monomial-multiplicity separation is injectivity of a test map, not surjectivity of the integral
  monomial lattice.
- A `BrauerInduced` proposition or an assumed character basis would encode the theorem to be
  proved and violates the no-interface rule.
- Even full Brauer induction gives meromorphic continuation, not holomorphy: negative exponents
  leave exactly the unresolved pole/effectivity mechanism exposed by C1/C2.

## Successor boundary

After this theorem, separate actual-global work remains: induced local-factor identity,
degree-one/Hecke class-field bridge, meromorphic continuation, Artin--Takagi, and the genuine
Heilbronn order character.  None may be replaced by a generic analytic interface.

## Log

- 2026-08-15 — opened after internal corpus and current literature audit confirmed full integral
  Brauer induction is the first nonlocal continuation bridge.  The theorem is known but its
  concrete finite-lattice formalization has not begun; no claim of Artin holomorphy is made.
- 2026-08-15 — source-checked the exact `Finsupp` theorem surface and concrete elementary-subgroup
  data in `/tmp/BrauerFormalDesign.lean`.  The dual-separation route is ruled out sharply:
  injectivity of the monomial profile does not kill an integral cokernel (`2ℤ ⊂ ℤ` is the model).
- 2026-08-15 — added the concrete `BrauerElementarySubgroup` carrier and monomial index, then
  source-checked, target-built, axiom-audited, and wired it.  This is necessary data for the
  theorem, not evidence of integral generation; the card remains Stage 1.
- 2026-08-15 — reduced the subgroup-closure lemma to a concrete checked component argument for
  `K ≤ C × P`: define the `snd=1` and `fst=1` parts, use coprimality to make the relevant power
  map bijective on the `p`-part, and recover both coordinates of each `K` element.  Projection
  injections and the component separation source-check; packaging the multiplication equivalence
  and transporting it through the existing elementary witness remains unverified Lean work.  No
  closure theorem is claimed yet.
- 2026-08-15 — formalized and target-built the central component-extraction lemmas in
  `ArtinBrauerElementary.lean`: any subgroup of a finite coprime `C × P` product contains both
  coordinates of each of its elements, and the result transports through a recorded elementary
  multiplication equivalence.  The five-theorem axiom audit is standard-foundations-only.  This
  closes a real subgroup-closure sublemma, but not the required intersection/equivalence packaging
  and emphatically not the integral Finsupp-surjectivity theorem.
- 2026-08-15 — the coordinate extraction now gives the exact direct-product equality
  `K = (K.map fst).prod (K.map snd)` for every subgroup `K ≤ C × P` with `C` finite of order
  coprime to `p` and `P` a `p`-group.  The isolated scratch proof is source-green and has only
  standard Lean foundations.  It is integrated as
  `subgroup_prod_eq_prod_maps_of_card_coprime`; the full transport to a new
  `BrauerElementarySubgroup` witness still needs the intersection/subgroup-image multiplication
  equivalence.  No integral-induction or span claim is made.
