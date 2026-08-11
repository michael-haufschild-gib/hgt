# Exchange residual, strict quotient, central promotion, and nonsplit history law

- **ID:** ULF-OPM-3
- **Stage:** 3-formalized
- **Type:** CROSS-PROMOTION MECHANISM THEOREM
- **Statement:** One exchange residual has two exact completions: strict abelianization erases it,
  while Heisenberg promotion retains it as a central cocycle; associativity is the cocycle law and
  no commuting section can reconstruct the promoted history from strict endpoints.
- **Status:** [PAPER-PROVED] [LEAN-CERTIFIED] [DEPENDENCY-CLOSED]
  [SAME RESIDUAL / TWO PROMOTIONS] [STRICT + EXTENSION COMPARISON] [NOT RH]

## 1. One residual, two responses

Let

\[
 A=\mathbb Z^2
 \tag{HP.1}
\]

with addition. The strict response to the exchange law is to force the two standard generators to
commute and retain only their total multiplicities.

The history-retaining response uses the integer Heisenberg set

\[
 H=\mathbb Z^3
 \tag{HP.2}
\]

with multiplication

\[
 (a,b,c)(a',b',c')
 =\bigl(a+a',\ b+b',\ c+c'+ab'\bigr).
 \tag{HP.3}
\]

The third coordinate is not an auxiliary decoration. It is the promoted exchange residual.

## 2. Cocycle and group law

Define

\[
 \kappa((a,b),(a',b'))=ab'.
 \tag{HP.4}
\]

### Theorem 2.1

The function `kappa` obeys the normalized cocycle identity

\[
 \boxed{
 \kappa(u,v)+\kappa(u+v,w)
 =\kappa(v,w)+\kappa(u,v+w).}
 \tag{HP.5}
\]

Consequently `(HP.3)` is associative. Its identity and inverse are

\[
 e=(0,0,0),
 \qquad
 (a,b,c)^{-1}=(-a,-b,-c+ab).
 \tag{HP.6}
\]

Hence `H` is a group.

### Proof

For `u=(a,b)`, `v=(a',b')`, and `w=(a'',b'')`, both sides of `(HP.5)` equal

\[
 ab'+ab''+a'b''.
\]

Expanding the third coordinate of the two bracketings of `(HP.3)` gives exactly `(HP.5)`.
The identity and inverse formulas follow by direct substitution. QED.

The mechanism law is already visible: coherence of promoted history is not added later;
associativity is exactly the residual's cocycle equation.

## 3. Strict quotient and central residual

Define

\[
 \pi:H\longrightarrow A,
 \qquad
 \pi(a,b,c)=(a,b),
 \tag{HP.7}
\]

and

\[
 Z(n)=(0,0,n).
 \tag{HP.8}
\]

### Theorem 3.1

The map `pi` is a surjective group homomorphism with

\[
 \ker\pi=Z(\mathbb Z),
 \tag{HP.9}
\]

and `Z(mathbb Z)` is central. Thus

\[
 0\longrightarrow\mathbb Z\xrightarrow{Z}H
 \xrightarrow{\pi}\mathbb Z^2\longrightarrow0
 \tag{HP.10}
\]

is a central extension.

Let

\[
 F=(1,0,0),
 \qquad
 G=(0,1,0).
 \tag{HP.11}
\]

Then

\[
 \boxed{FG=Z(1)GF,}
 \tag{HP.12}
\]

while

\[
 \pi(F)\pi(G)=\pi(G)\pi(F).
 \tag{HP.13}
\]

Hence strict observation erases the exchange residual and central promotion retains it.

### Proof

Equations `(HP.7)`--`(HP.9)` follow from the coordinate formulas. A central element has first two
coordinates zero, so its cross term in `(HP.3)` vanishes on both sides. Finally

\[
 FG=(1,1,1),
 \qquad
 GF=(1,1,0),
\]

which proves `(HP.12)`. QED.

## 4. Exact commutator and abelianization

### Theorem 4.1

For `x=(a,b,c)` and `y=(a',b',c')`,

\[
 \boxed{xyx^{-1}y^{-1}=Z(ab'-a'b).}
 \tag{HP.14}
\]

Consequently:

1. every commutator lies in `Z(mathbb Z)`;
2. `[F,G]=Z(1)`, so every `Z(n)` lies in the commutator subgroup;
3. the commutator subgroup and centre both equal `Z(mathbb Z)`;
4. the fibres of `pi` are exactly the central cosets, so quotienting by the commutator/centre
   identifies the strict shadow with

   \[
     H/Z(\mathbb Z)\cong\mathbb Z^2.
     \tag{HP.15}
   \]

### Proof

Expanding `(HP.3)` and `(HP.6)` gives `(HP.14)`. This puts every commutator in the central copy of
`mathbb Z`. Conversely, `(HP.12)` gives `[F,G]=Z(1)`, and powers give every `Z(n)`. An element
commuting with `F` has `b=0` by `(HP.14)`; commuting also with `G` forces `a=0`. Thus the centre is
exactly `Z(mathbb Z)`. Equal `pi`-images are exactly central translates, and `pi` is surjective,
proving `(HP.15)`. QED.

## 5. Nonsplitting and irrecoverable history

### Theorem 5.1

Every lift `x` of `(1,0)` and every lift `y` of `(0,1)` satisfy

\[
 xyx^{-1}y^{-1}=Z(1)\neq e.
 \tag{HP.16}
\]

Therefore the extension `(HP.10)` has no group-homomorphic section.

### Proof

The first two coordinates of `x,y` are fixed by the lifting conditions, while their third
coordinates are arbitrary. Formula `(HP.14)` is independent of those third coordinates and gives
`Z(1)`. If a group section existed, the two commuting basis elements of `A` would have commuting
lifts, contradicting `(HP.16)`. QED.

Thus the strict quotient is not a coordinate choice on the central promotion. It is a genuine loss
of compositional history. No endpoint rule on `A` reconstructs the exchange carry.

## 6. Exact cross-promotion conclusion

One source exchange failure now has two mathematically forced responses:

### Strict promotion

\[
 FG\sim GF,
 \qquad
 \text{retain only }(a,b)\in\mathbb Z^2.
 \tag{HP.17}
\]

This is the least-quotient logic of ULF-OPM-2.

### Extension promotion

\[
 FG=Z(1)GF,
 \qquad
 \text{retain }(a,b,c)\in H.
 \tag{HP.18}
\]

The new central law satisfies the cocycle identity `(HP.5)` and cannot be removed by a commuting
section.

The withheld prediction distinguishing the modes is `(HP.16)`: every pair of endpoint lifts has the
same nonzero commutator, regardless of arbitrary central coordinates. Strict endpoint data predict
zero; promoted history predicts `Z(1)`.

This is the first exact answer to the field's cross-mode gate. The remaining higher question is what
source law decides whether a residual is killed, centralized, promoted to higher arity, or sent
through a singular admission change.

## 7. Sharp boundaries

1. The cocycle representative depends on the chosen section of `pi`, but the nonsplit extension
   class and commutator pairing do not.
2. Central promotion is not homotopy-coherent promotion; it retains a degree-two extension, not an
   arbitrary higher operation.
3. The theorem has no topology, positivity, completion, differential growth, cost, or physical
   clock.
4. Nothing here selects central promotion over strictification. That selection law is the open
   mechanism problem.
5. The integer Heisenberg group and its central extension are classical. The field contribution is
   the exact comparison of two promotion laws for one residual, not novelty of the group.

## Lean certification

Module:
`GaloisForLFunctions.HTGeometry.ConstitutiveExchangeCentralPromotion`.

It reuses the already certified integer Heisenberg group law from
`ConstitutiveQuadraticFilling` and closes:

1. the exchange cocycle identity;
2. projection, surjectivity, kernel criterion, exact central fibres, centrality, and the
   subgroup identity `ker pi = Z(H)`;
3. exact generator exchange and general commutator formula;
4. every commutator is central and every central element is an exchange commutator;
5. exact centre characterization through the two generators, the commutator-subgroup identity
   `[H,H] = Z(H)`, and the strict-shadow quotient isomorphism `H/Z(H) ~= Z^2`;
6. fixed nonzero commutator for every pair of basis lifts;
7. no homomorphic section of the strict quotient;
8. bundled cross-promotion theorem.

Direct elaboration and targeted module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-09 -- same-residual strict/central promotion comparison proved on paper.
- 2026-08-09 -- all significant mechanism clauses closed in Lean and wired into the dedicated
  universal-law umbrella.
- 2026-08-11 -- kernel/centre and commutator-subgroup identities and the strict-shadow quotient isomorphism certified; card promoted to stage 3.
