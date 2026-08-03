# Riemann centered-flow modular capacity intertwining

- **ID:** riemann-centered-flow-modular-capacity-intertwining
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** actual Xi residue transport, Cayley order-space conservation, prime-tail entropy
- **Statement:** Complete derivative-order capacity of every Xi residue is an exact one-dimensional modular cocycle; its source-entropy countercharacter trivializes the cocycle, while a time-independent positive capacity is possible exactly on the critical line.

## Goal

Construct the missing centered-flow capacity object without hiding RH in a boundedness premise.
Separate unconditional covariant conservation from the still-RH-equivalent assertion that the
arithmetic modular cocycle is trivial.

## Exact definitions

For an actual Xi divisor point `rho`, put

\[
 m_\rho=\operatorname{ord}_\rho\Xi>0,
 \qquad x_\rho(\tau)=\frac{\tau}{|\rho-1|^{-2}},
 \qquad \kappa_\rho=2\Re\rho-1.
\]

Let the transported residue mode be

\[
 F_\rho(x)=m_\rho\exp\!\left(\frac{x}{\rho-1}\right).
\]

Its complete order capacity is

\[
 \mathcal C_\rho(\tau)
 =\sum_{r\ge0}\frac{x_\rho(\tau)^r}{r!}
   \left|F_\rho^{(r)}(x_\rho(\tau))\right|^2.
\]

The source-tail entropy and its countercharacter are

\[
 S_\rho=\frac{\log|\chi_2(\rho)|-
                  \log|\chi_2(1-\bar\rho)|}{\log2}
       =-\kappa_\rho,
 \qquad T_\rho(\tau)=e^{S_\rho\tau}.
\]

Define the source-trivialized capacity

\[
 \widehat{\mathcal C}_\rho(\tau)
 :=T_\rho(\tau)\mathcal C_\rho(\tau).
\]

## Theorem [PROVED HERE]

For every actual Xi divisor point and all real `tau,u`:

1. **Exact capacity character**
   \[
   \mathcal C_\rho(\tau)=m_\rho^2e^{\kappa_\rho\tau}.
   \]
2. **Centered-flow intertwining**
   \[
   \mathcal C_\rho(\tau+u)=e^{\kappa_\rho u}\mathcal C_\rho(\tau),
   \qquad
   T_\rho(\tau+u)=T_\rho(\tau)T_\rho(u).
   \]
3. **Source-derived covariant conservation**
   \[
   \widehat{\mathcal C}_\rho(\tau)=m_\rho^2.
   \]
4. **Static-capacity gate**
   \[
   \bigl(\forall\tau,\ \mathcal C_\rho(\tau)=\mathcal C_\rho(0)\bigr)
   \Longleftrightarrow S_\rho=0
   \Longleftrightarrow \Re\rho=\tfrac12.
   \]
5. Globally, static capacity on every Xi divisor fibre is equivalent to RH.

### Proof

The source-Cayley residue conservation identity gives, order by order,

\[
 \frac{x_\rho(\tau)^r}{r!}|F_\rho^{(r)}(x_\rho(\tau))|^2
 =m_\rho^2e^{\kappa_\rho\tau}
   e^{-\tau}\frac{\tau^r}{r!}.
\]

The algebraic Poisson weights on the right have total mass one for every real `tau`.
Summing proves (1).  Replacing `tau` by `tau+u` and using the exponential addition law proves
the first identity in (2); the second is the same addition law applied to the source entropy.
The independently proved source-boundary orientation law gives `S_rho=-kappa_rho`, so the two
characters cancel and prove (3).

If `C_rho` is static, compare `tau=1` with `tau=0`.  Since `m_rho>0`, cancellation gives
`exp(kappa_rho)=1`, hence `kappa_rho=0`, hence `Re rho=1/2`.  The converse follows directly
from (1).  The prime-tail identity gives the equivalent entropy formulation.  Applying the local
equivalence to every actual divisor point gives (5) by the established divisor form of RH.

Every dependency above is an unconditional theorem already present in the corpus.  No boundedness,
continuity, divisor-selected damping, or RH premise enters the construction.

## Hostile antagonist review

### Objection 1: this proves RH by renormalization

False.  The countercharacter depends on the nontrivial modular slope `S_rho`.  It constructs a
moving positive metric, not one fixed invariant positive metric.  RH is precisely triviality of
that cocycle.  Claiming the trivialized moving capacity as the missing static source weight would
be circular.

### Objection 2: reflection already cancels opposite rates

Only pairwise.  A reflected product or hyperbolic cross form is invariant off line but each
individual character axis is isotropic.  It cannot supply the atomic positive weight required by
the conormal-socle criterion.  The pointed Cartan theorem proves that every invariant seminorm
kills a nonzero-slope atom.

### Objection 3: summing derivative orders may erase orientation

It does not: the entire sum retains the signed exponent `kappa_rho`; only its Poisson profile is
summed out.  Multiplying by `T_rho` cancels that sign deliberately and records it in the metric
cocycle.

### Objection 4: the theorem is another decorative RH equivalence

The positive content is the exact unconditional factorization

\[
 \text{raw capacity}
 =\text{multiplicity mass}\times\text{arithmetic modular character}.
\]

It constructs the previously missing intertwining object and proves uniqueness of the remaining
obstruction: not conservation, transport, Poisson completion, non-erasure, or reflection, but
source-forced triviality of the modular character.

## Scientific correction to frontier

“Global centered-flow capacity conservation” was too coarse.  Covariant conservation is now
closed.  Exact remaining theorem is:

\[
 \boxed{\text{the arithmetic source forces }S_\rho=0
        \text{ on every Xi divisor fibre}.}
\]

Equivalently, arithmetic must trivialize its own prime-tail modular cocycle without using divisor
boundedness.  Hodge commutator, Green fracture, Wold--Poisson instability, Rees type split,
Gaussian Wronskian, and projective descent defect are representations of this same cocycle.

## Gates

- [x] 0 → 1: source-pure construction and exact formulas
- [x] dependency-closed paper proof
- [x] hostile non-circularity review
- [x] 2 → 3: formalized in `RiemannCenteredFlowCapacityIntertwining.lean`
- [x] targeted Lean and axiom audit
- [ ] source-forced cocycle triviality
- [ ] RH

## Log

- 2026-08-03 — exact modular capacity/trivialization law isolated and proved on paper.
- 2026-08-03 — formalized unconditionally; direct Lean and targeted module build pass; axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
