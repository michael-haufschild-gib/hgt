# Pointed second-Cartier Krein boundary relation

- **ID:** source-horizontal-second-cartier-pointed-krein-boundary-relation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `source-horizontal-second-cartier-physical-order-moderation-firewall.md`
- **Statement:** The literal rank-two second-Cartier source admits a controlled multivalued boundary relation into a nondegenerate indefinite three-coordinate jet: its nonzero quadratic ghost is null but not radical, both orientations and their coefficients are retained, the vertical fibre is exactly the one-dimensional unit line, and every nonzero prime character acts by a Krein-isometric source-covariant transfer.

## Goal

Construct the first receiver outside both proved firewall horns. It must not scalarize `G`, impose
positivity on `G` or `-G`, or hide the off-line character in an assumed moderation law. It must
retain the literal two-orientation source, actual endpoint coefficient, prime character, and Xi
multiplicity.

## Gates

- [x] 0 → 1 in-progress: exact source, relation, form, transfer, falsifiers, and passport fixed
- [x] 1 → 2 fully-proven: dependency-closed proof and hostile audit
- [ ] 2 → 3 formalized: exact unconditional Lean theorem, axiom audit, exact leaf build, umbrella
- [ ] 3 → 4 publication-ready: standalone proof and independent novelty review

## Internal and external frontier

`[CORPUS]` In `Q = Z[q,q⁻¹]/(q-1)³`, the literal classes satisfy

\[
F+R=G\ne0,\qquad F^2=G,\qquad FR=-G,\qquad F^3=R^3=G^2=0.
\]

Reduced multiplicative receivers erase the full source lattice. Ordered multiplicative receivers
retaining `G` cannot make both `G` and `FR=-G` nonnegative. Additive coefficient-faithful Hardy
receivers send `G` to a nonmoderate bilateral eigenfamily on every strict-right Xi fibre.

`[CORPUS]` A full reciprocity graph in a doubled Krein space is Lagrangian and has zero quotient
(`SeamKreinStructure`). Closed cofinal linear relations retaining the completed prime reader become
fully vertical and therefore impose no output information (`CompleteResolutionCofinalConditioningLaw`,
`DeningerMeyerHalfDensityXiGraphClosure`).

`[LITERATURE]` Multivalued unitary/isometric boundary relations between Krein spaces and their Weyl
families are established operator theory. Local Artinian Gorenstein algebras likewise retain their
socle through a perfect pairing with a dual unit. Neither parent theory supplies this literal
Cartier/Xi coefficient and prime-character construction. Exact priority is unverified.

## Conjecture loop

### C1 — full Lagrangian graph

Map both orientations into a doubled reciprocity graph and take its signed quotient.

**Verdict:** `[FALSIFIED]`. The graph is Lagrangian, hence its signed orthogonal quotient is zero.
It erases rather than retains the quadratic class.

### C2 — arbitrary closed completed linear relation

Retain the entire cofinal Hardy graph in a closed relation and use its multivalued part.

**Verdict:** `[FALSIFIED]`. Existing closure theorems force the vertical fibre to be the complete
target. Such a relation has no output information.

### C3 — source-pointed one-vertical-line relation

Use only the literal finite second-Cartier jet. The missing dual of the nilpotent socle is the
source unit, carried as one controlled vertical gauge line rather than as a scalar quotient.

**Verdict:** `[PAPER-PROVED]`. It is neither a full Lagrangian quotient nor a cofinal graph closure.
The proof below classifies its vertical fibre as exactly one-dimensional and proves that its ghost
pairs nontrivially with that fibre.

## Frozen construction

Let the complexified source be `V=C²`, with coordinates `(a,b)` on `(F,R)`. Let the pointed jet be

\[
K=C\oplus C^2,\qquad x=(u,a,b).
\]

Set `g(x)=a+b` and `d(x)=a-b`. Define

\[
[x,y]=\bar u_x g(y)+\overline{g(x)}u_y+\overline{d(x)}d(y). \tag{1}
\]

The distinguished vectors are

\[
U=(1,0,0),\quad F_c=(0,c,0),\quad R_c=(0,0,c),\quad G_c=(0,c,c).
\]

For `c∈C`, define the boundary relation

\[
\mathcal R_c=\{((a,b),(u,c a,c b)):a,b,u\in C\}\subseteq V\times K. \tag{2}
\]

This is deliberately a relation, not a fitted reporter: the anchor `u` is free.

For `λ≠0`, put `r=(\bar λ)^{-1}` and define

\[
S_λ(a,b)=\left(\frac{r(a+b)+(a-b)}2,
                    \frac{r(a+b)-(a-b)}2\right), \tag{3}
\]

\[
T_λ(u,a,b)=(λu,S_λ(a,b)). \tag{4}
\]

## Exact producer theorem

For every `c≠0` and `λ≠0`:

1. `(0,U)` is in the vertical fibre of `R_c`, and that fibre is exactly `C U`;
2. `R_c` is genuinely multivalued and not the graph of a function;
3. the canonical lifts of `F`, `R`, and `G=F+R` are `F_c`, `R_c`, and `G_c`;
4. `G_c≠0`, `[G_c,G_c]=[-G_c,-G_c]=0`, but `[U,G_c]=2c≠0`; hence the ghost is null but not radical;
5. the form `(1)` is Hermitian, nondegenerate, and indefinite;
6. `T_λ` preserves `(1)` exactly;
7. `(v,w)∈R_c` implies `(S_λv,T_λw)∈R_c`;
8. `T_λ U=λU` and `T_λ G_c=(\bar λ)^{-1}G_c`, so the prime character and its reciprocal-star mate are retained without Euclidean moderation;
9. swap of the two source orientations preserves the relation and the form and commutes with both transfers.

For the actual Xi endpoint scale and `λ=χ_p(ρ)`, the scale and character are nonzero. The canonical
ghost lift therefore supplies the same nonzero null/nonradical block on every support copy, and
finite fibre summation multiplies it by the exact analytic multiplicity.

## Paper-proof ledger

- Relation linearity: equations `(2)` are homogeneous linear equations.
- Vertical classification: setting `(a,b)=0` in `(2)` leaves precisely `(u,0,0)=uU`.
- Multivaluedness: both `0` and `U` occur above source zero and are distinct.
- Source fidelity: substitute `(1,0)`, `(0,1)`, `(1,1)` into the canonical zero-anchor lift.
- Null/nonradical law: direct substitution in `(1)` gives `0`, `0`, and `2c`; `2c≠0` since `c≠0`.
- Hermitian law: conjugate `(1)` with arguments exchanged.
- Nondegeneracy: pair a radical candidate successively with `U`, `(0,1,1)`, and `(0,1,-1)` to obtain `a+b=0`, `u=0`, and `a-b=0`.
- Indefiniteness: `U+(0,1,1)` has square `4`; `U-(0,1,1)` has square `-4`.
- Transfer identities: `(3)` gives `g(S_λv)=r g(v)` and `d(S_λv)=d(v)`. In `(1)`, `\bar λr=1` and `\bar rλ=1`, proving `(6)`.
- Covariance: apply `(3)` to `(ca,cb)` and commute scalar `c` through the formula.
- Eigenlegs: substitute `U` and `G_c` in `(4)`.
- Swap covariance: swap fixes `g`, negates `d`, and therefore preserves `(1)` and commutes with `(3)`.
- Actual coefficient and multiplicity: existing endpoint-scale nonvanishing and support-fibre
  constancy theorems apply; summing one constant lift over the fibre gives its Fintype cardinal,
  already identified with Xi support multiplicity.

## Hostile falsifiers

- If the vertical fibre contains any vector outside `C U`, C3 collapses to the full-vertical no-go.
- If `G_c` is radical, the construction merely stores a zero-norm ghost and supplies no physical
  information.
- If transfer preservation needs `|λ|=1`, the construction is circular and fails its purpose.
- If covariance loses either source coefficient or the actual support multiplicity, it is not the
  requested producer.
- If the resulting relation alone implies criticality, the proof must be checked for a hidden
  same-fibre fixed-star assumption. The expected theorem admits all `λ≠0`; it is a carrier producer,
  not RH by itself.

## Novelty boundary

The abstract hyperbolic/Krein completion and multivalued boundary-relation language are
`[REDISCOVERED]`. The exact source-pointed Cartier/Xi realization and its simultaneous coefficient,
prime-transfer, two-orientation, and multiplicity laws are `[NOVELTY UNVERIFIED]`. Scientific value
is the exact surviving category and the removal of the scalar moderation demand, not a claim that
indefinite boundary relations are new.

## Hostile proof audit

All five falsifiers were applied to the displayed formulas:

- `(2)` makes the vertical equations `a=b=0`, so no extra vertical direction exists;
- `[U,G_c]=2c≠0` excludes radicality;
- transfer invariance uses only `λ≠0`, never `|λ|=1`;
- relation covariance retains the two coefficients separately before their even/odd recombination;
- support-copy constancy and the existing fibre-cardinality theorem preserve analytic multiplicity.

No same-fibre star equality, RH criterion, scalar positivity, bilateral moderation, or completed
graph closure is imported. The paper proof is dependency-closed. `[PAPER-PROVED]`

## Log

- 2026-08-18 — C1 and C2 killed by exact corpus theorems; C3 frozen for hostile proof audit.
- 2026-08-18 — C3 survived all stated falsifiers; dependency-closed paper theorem promoted to
  Stage 2.
