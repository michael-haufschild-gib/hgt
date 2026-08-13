# Formation-transfer germ mechanics

- **ID:** ULF-FTGM
- **Stage:** 1-in-progress
- **Type:** COFINAL INFORMATION-TRANSFER MECHANICS / SATURATED-BOUNDARY TOMOGRAPHY
- **Status:** `[FIELD PROGRAMME] [ONE CHAMBER PAPER-CLOSED] [UNIVERSAL RECONSTRUCTION OPEN]`
  `[NOT RH]`

## 1. Pivot

The preceding universal-law work retained an observer boundary point and a recovered history.
That is still too coarse.  In many corpus chambers every formed observer converges to the same
boundary point, so the point itself contains no transverse information.  The stronger object is
not another completion and not a likelihood bound.  It is the **cofinal germ of information
transferred out of the observer under source-native formation**.

The primitive claim is a mechanism:

> A source formation law carries an additive resource.  Every compatible observer quotient moves
> part of that resource into a hidden fibre.  Losses between formation depths are nonnegative
> transfer cells.  Their cocycle law makes total transfer path-independent.  The complete vanishing
> transfer germ can be source-faithful even when its limiting observer point is constant.

This is a different answer to route stagnation.  A finite route sees a quotient point.  A cofinal
route must retain how information approaches that point and how much information crossed each
formation scale.

## 2. Abstract grammar

A formation-transfer chart consists of:

1. a multiplicative depth monoid `M`;
2. source laws `P_m,Q_m` with additive divergence
   `I(P_m,Q_m)=m I(P_1,Q_1)`;
3. observer laws `p_m,q_m` obtained by a formation-compatible quotient;
4. a hidden-history disintegration with
   `m I_1=I_m^obs+H_m`;
5. block-composition maps taking `n` depth-`m` observer blocks to one depth-`mn` observer;
6. transfer cells

   \[
   T_{m,n}=nI_m^{\rm obs}-I_{mn}^{\rm obs}\ge0;
   \]

7. a cofinal scale germ made from normalized transfer cells.

Three laws are forced before any geometry language is admitted:

\[
 T_{m,nk}=kT_{m,n}+T_{mn,k},
 \tag{FTG.1}
\]

\[
 H_{mn}=nH_m+T_{m,n},
 \tag{FTG.2}
\]

\[
 \frac{T_{m,n}}{mn}
 =\frac{I_m^{\rm obs}}m-\frac{I_{mn}^{\rm obs}}{mn}.
 \tag{FTG.3}
\]

Thus normalized observer information is a decreasing potential, transfer is its exact discrete
differential, and hidden history is the compensating current.  `(FTG.1)` is not curvature: it is
strict scale coherence.  Nonzero transfer is not an anomaly: it is conserved migration.

## 3. First closed chamber

For Poisson formation followed by Boolean occupancy, Jeffreys divergence supplies the additive
resource.  Block composition is Boolean OR.  Data processing gives transfer positivity, the chain
rule identifies transfer with conditional block-history information, and independent
superposition gives `(FTG.1)`--`(FTG.3)` exactly.

More strongly, let `m_j=d^j`, `d>=2`, and let `g_j` be normalized information transferred by the
single step `m_j -> d m_j`.  Although the occupancy pairs converge to `(1,1)` and `g_j -> 0`, the
complete germ reconstructs both unordered Poisson rates:

\[
 b=\lim_j-\frac{\log g_j}{m_j},
 \qquad
 \Delta=
 \left(\lim_j\frac{g_{j+1}}{g_j^d}\right)^{-1/(d-1)},
 \qquad a=b+\Delta.
 \tag{FTG.4}
\]

The two directed transfer germs reconstruct orientation as well.  The larger directed transfer is
asymptotic to `m_j Delta` times the smaller one, so exchanging source labels exchanges the two
germs while preserving their symmetric sum.

The dependency-closed theorem is in:

`../../../2-fully-proven/universal-law-field/formation-transfer-germ-mechanics/poisson-boolean-information-transfer-cocycle-and-boundary-germ-tomography-law.md`.

## 4. Field conjecture

### Conjecture FTGM-A -- jointly sufficient transfer atlas

For the source-generated subcategory of the RH corpus, there is a finite family of additive or
ordered resources and compatible formation exits such that the joint cofinal transfer germ is
faithful on source interventions modulo the declared functional equation.

The claim is deliberately stronger than retaining every history object.  Histories may be huge,
presentation-dependent, or noncompact.  The transfer atlas asks only for the information current
created by each legal formation comparison.  It predicts that route no-gos are failures of one
finite truncation or one scalar transfer coordinate, not absence of a source distinction.

### Conjecture FTGM-B -- selection by neutral transfer formation

The literal source functional-equation action preserves total transfer and exchanges oriented
transfer coordinates.  A source-normal global formation law forces its physical fixed packet to
have zero oriented transfer germ.  In the reflected prime chamber, zero germ is equivalent to the
neutral parameter.

The first sentence is proved in the Poisson chamber.  The second is the actual selection gate: no
current theorem derives zero germ from the pre-zero arithmetic source.

## 5. Why this is not the previous likelihood proposal

Uniform integrability, contiguity, Kakutani equivalence, and bounded modular oscillation already
exist in the corpus and are consumer criteria.  They collapse the question to boundedness of one
chosen cocycle and still need a producer.  Formation-transfer mechanics instead retains the
entire cofinal scale differential.  In the first chamber it reconstructs nonneutral source rates
precisely when all bounded observer values converge to the same limit.

## 6. Parent mathematics and scope

Data processing, relative-entropy chain rules, statistical sufficiency, information loss under
coarse graining, renormalization, and inverse asymptotics are established mathematics.  The field
programme is a Frankenstein synthesis by design.  Its possible contribution is the interpretation
and the requirement that source-native formation, observer quotient, hidden history, cofinal
transfer, functional equation, and route comparison form one jointly reconstructive doctrine.

The first chamber does not prove that every corpus route admits such a resource or that a finite
atlas suffices.  It proves that “all observers saturate, therefore information is gone” is false:
the cofinal transfer germ can be complete for the source parameter.

## 7. Next gates

1. instantiate the transfer laws in a nonprobabilistic capacity/rank organ;
2. prove one comparison transporting a transfer germ across two nonisomorphic formation species;
3. identify which existing route completion preserves the full germ and which retains only its
   zero boundary point;
4. construct the source-normal rule forcing neutral oriented germ before Xi specialization;
5. only then apply the zero-germ equivalence to RH selection.

## 8. Lean boundary

The exact scale cocycle and tomography theorem are Stage 2 and are eligible for formalization in
the `UniversalLawField` Lean umbrella.  No universal conjecture in this card may be formalized as
an axiom or promoted to Stage 3.
