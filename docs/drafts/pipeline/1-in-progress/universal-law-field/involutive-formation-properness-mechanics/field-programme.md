# Involutive Formation-Properness Mechanics

- **ID:** ULF-IFPM-FIELD
- **Stage:** 1 — in progress
- **Type:** UNIVERSAL-LAW FIELD PROGRAMME
- **Status:** `[MECHANISM-FIRST] [TWO LEAN-PROVED REALIZATIONS] [SELECTION PRODUCER OPEN]`

## 1. Primitive question

What laws turn a reversible, information-neutral formation into a selector?

The corpus had treated three operations separately:

1. form a richer packet through a split recovery kernel;
2. apply a functional-equation involution;
3. impose a positive/proper cost.

The new mechanism treats their compatibility as one structure.  A chart carries

\[
 \operatorname{Form}:X\to Z,\qquad
 \operatorname{Rec}:Z\to X,\qquad
 \operatorname{Rec}\operatorname{Form}=1,
\]

an involution `rho`, an amplification semigroup `A_n`, and a nonnegative work `W`.  Its laws are:

1. **neutral lift:** common recovery preserves complete divergence information;
2. **reflection:** `rho` reverses one recoverable coordinate and fixes its formation midpoint;
3. **amplification:** `A_m A_n=A_{mn}` or `A_{m+n}` according to marking;
4. **work covariance:** reflection preserves work and amplification scales it;
5. **properness:** bounded complete amplified work is equivalent to the reflection fixed locus;
6. **observer conservation:** any bounded observed work forces the missing amplified work into an
   information-loss fibre unless observer is sufficient.

The field object is not a manifold or stack.  It is this coupled law package and its legal changes
of chart.

## 2. Exact realizations

### Positive-matrix realization

Every positive reciprocal packet is uniquely

\[
 (X,Y)=(RQR,RQ^{-1}R).
\]

Reflection fixes `R`, inverts `Q`, and the complete work vector is

\[
 (2a\|\log R\|_{HS},b\|\log Q\|_{HS}).
\]

Boundedness on both axes selects `(R,Q)=(I,I)`.

### Finite escort realization

For a positive finite law `w` and score `r`, let

\[
 p_t(x)=\frac{w_xe^{t r_x}}{\sum_yw_ye^{t r_y}}.
\]

Reflection sends `t` to `-t`.  The exact Jeffreys work is

\[
 J(t)=D(p_t\|p_{-t})+D(p_{-t}\|p_t)
     =2t\bigl(m(t)-m(-t)\bigr),
\]

where `m(t)=E_{p_t}r`.  Complete integer-amplification work is bounded exactly when `r` is constant,
equivalently when the family has no nontrivial reflected direction.

These realizations are structurally different: one is noncommutative positive-cone reconstruction;
the other is commutative statistical formation.  They satisfy the same mechanism without being
identified.

## 3. Fourth-organ law

Let `O_k` be work seen by any observer on the reflected escort pair and suppose `O_k<=C`.  Define
hidden loss `L_k=J(k)-O_k`.  If the score is nonconstant, then

\[
 \boxed{L_k\ge kJ(1)-C.}
\]

Thus a compact/recurrent bounded observer has only two possibilities:

1. it is sufficient, hence cannot remain bounded off the fixed locus; or
2. its hidden information fibre grows at least linearly.

This is a prediction in the recurrence/observer organ derived from packet formation, reflection,
and information properness.  It is not assumed in those three organs.

## 4. Selection gate

For an RH consequence, one must construct before zero specialization:

1. a coefficient-faithful formation chart;
2. a functional-equation action intertwining the chart reflection;
3. a source amplification law for the reflected coordinate;
4. either a uniform full-work bound, or a sufficient observer with bounded work.

The properness theorem then forces the reflected coordinate to its fixed locus.  No pointwise
vanishing premise is required.

## 5. Hostile boundaries

1. Split formation alone is flat; it cannot select.
2. Reflection alone is an information isometry; it cannot select.
3. Positivity at one depth gives distinguishability, not global properness.
4. Properness without source amplification only bounds a coordinate.
5. A bounded recurrent observer may hide unlimited fibre work.
6. Matrix and escort instances do not prove every route admits this mechanism.
7. Exponential-family and symmetric-cone ingredients are classical.  Field content is their
   compatible law package and the source-realization gate.

## Log

- 2026-08-12 — opened after exact functional-equation packet lifting and positive-cone bi-axis
  reconstruction showed that neutrality and selection are distinct laws.
- 2026-08-12 — finite escort realization proved on paper: variance generates monotone response,
  reflected Jeffreys work is proper exactly off the constant-score locus, and bounded observation
  forces linear hidden-information escape.
- 2026-08-12 — finite escort realization formalized in Lean, including stronger theorem that every
  bounded-above observer forces an unbounded hidden-loss sequence off the fixed locus.
