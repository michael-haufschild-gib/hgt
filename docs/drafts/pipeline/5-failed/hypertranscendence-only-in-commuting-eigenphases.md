# Hypertranscendence only in commuting eigenphases is a rejected conjecture

- **ID:** `hypertranscendence-only-in-commuting-eigenphases`
- **Stage:** 5-failed
- **Type:** FAILED CONJECTURE / REDISCOVERY GATE
- **Status:** `[REJECTED BEFORE PROMOTION] [CORPUS COLLISION] [NOT A THEOREM]`
- **Scope:** general finite-channel positive-unitary factorizing scattering
- **Claim attempted:** Positive-unitary factorization forces all hypertranscendence into commuting
  scalar or eigenphase sectors, while every intrinsically mixing projective quotient is
  differential algebraic.

## Why the conjecture was tempting

All currently physical HT controls in the corpus place HT in scalar or commuting relative phases.
Standard intrinsically mixing matrix solutions usually have rational, trigonometric, elliptic, or
Gamma-dressed projective ratios and are therefore DA in the projective sector. The two-state
flip-anchored braid classification also has a fixed product eigenframe.

These observations do not prove the universal claim.

## Why it was rejected

1. `before-time-finite-rank-no-interaction.md` already proves the relevant abstract flatness
   theorem: a regular exact-flat finite-rank matrix-symbol tower is a static commuting family up
   to gauge. Restating it for scattering would be corpus rediscovery unless the physical axioms
   forced that exact flatness hypothesis.
2. `hypertranscendental-nonabelian-asymptotic-connection.md` already constructs the complementary
   nonabelian connection object and shows that bounded uniformization, not algebraic flatness, is
   the meaningful obstruction category.
3. Positive unitarity and Yang--Baxter factorization do not by themselves imply the coefficient-
   flat tower used in the first theorem. No derivation of that bridge was found.
4. The corpus contains algebraic non-difference Yang--Baxter controls with projective HT and
   intrinsic mixing. Their failures are positive-metric unitarity and Lorentz difference form,
   not Yang--Baxter consistency. They block any purely algebraic universal no-go.
5. The 2026 complete analytic `4 x 4` classification supports a narrow two-state theorem only
   after a specific zero-anchor and positive-unitarity filter. It cannot be extrapolated to all
   channel dimensions or to the convention-correct physical quantum lane.

## Exact failed proof step

The attempted proof needed

```text
positive unitarity + Yang--Baxter + difference form
  => exact coefficient-flat finite-rank symbol tower.          (1)
```

No such implication follows from the axioms, and the existing flatness theorem cannot supply it.
Without `(1)`, simultaneous abelianization is assumed rather than derived.

## Surviving insight

The correct separation is not “HT is abelian.” It is:

```text
scalar CDD HT
  is invisible to the quantitatively bounded all-particle intertwiner property;

projective mixing HT
  is the genuinely open physical sector;

exact flatness
  forces abelianity, but physical factorization has not been shown to force exact flatness. (2)
```

The first statement is the direct parent-theory bridge
`../2-fully-proven/not_new_scientific_knowledge/06-integrable-qft-yang-baxter/scalar-cdd-invariance-of-intertwiner-property.md`. The second remains
the construction target. The third is existing corpus mathematics and must not be advertised as
a new QFT no-go.

## Reopening condition

Reopen only if a new physical theorem derives the precise coefficient-flatness hypothesis from
positive-unitary factorizing QFT axioms, or if a complete higher-dimensional classification proves
projective differential algebraicity without assuming flatness. Examples and absence-of-hit
searches are insufficient.

## Primary controls

- M. de Leeuw and A. L. Retore/Posch classification line for analytic `4 x 4` Yang--Baxter
  solutions, <https://arxiv.org/abs/2411.18685>.
- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.
