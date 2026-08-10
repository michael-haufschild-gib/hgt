# Fixed-point defect, ternary genesis, and convex repair law

- **ID:** ULF-EAG-1
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL-LAW-FIELD / EQUIVARIANT LAW GENESIS
- **Statement:** An unoriented failed pair with fixed background cannot generate an equivariant
  deterministic binary successor.  Every equivariant deterministic separator uses at least three
  output values; a ternary reporter is minimal.  Convexification repairs binary equivariance by the
  unique symmetric mixture, while orientation repairs it by breaking source symmetry.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [CLASSICAL G-SET/CONVEX INGREDIENTS] [NOT RH] [LEAN-CERTIFIED]

## 1. Source failure record

Let

\[
 X=\{\bot,-,+\}
\]

and let the involution (s_X) fix the background (ot) and exchange the failed alternatives:

\[
 s_X(\bot)=\bot,
 \qquad s_X(-)=+,
 \qquad s_X(+)=-.
 \tag{EAG.1}
\]

A successor reporter (q:X\to Y) into a set with involution (s_Y) is **unoriented-natural** when

\[
 q\circ s_X=s_Y\circ q.
 \tag{EAG.2}
\]

It **resolves the failure** when (q(-)\ne q(+)).

## 2. Fixed-point transport

### Theorem 2.1 -- fixed points must transport

For arbitrary sets (A,B), maps (s_A:A\to A), (s_B:B\to B), and an equivariant map
(f:A\to B), every fixed point of (s_A) maps to a fixed point of (s_B).

### Proof

If (s_A(a)=a), then equivariance gives

\[
 s_B(f(a))=f(s_A(a))=f(a).
\]

Thus (f(a)) is fixed. \(\square\)

### Corollary 2.2 -- deterministic binary impossibility

Let (Y=\{0,1\}) and let (s_Y) exchange (0) and (1).  There is no equivariant map
(X\to Y).

### Proof

The source has the fixed point (ot), while the binary swap has no fixed point.  Apply Theorem
2.1. \(\square\)

This is stronger than failure to resolve the marked pair: no deterministic binary map preserves the
unoriented symmetry at all.

## 3. Exact deterministic arity floor

### Theorem 3.1 -- three-image law

Let (Y) carry any involution (s_Y), and let (q:X\to Y) be equivariant and resolve the failed
pair.  Then

\[
 q(\bot),\quad q(-),\quad q(+)
 \tag{EAG.3}
\]

are pairwise distinct.  In particular every deterministic equivariant separator has at least three
values in its image.

### Proof

Equivariance gives

\[
 s_Y(q(\bot))=q(\bot),
 \qquad
 s_Y(q(-))=q(+),
 \qquad
 s_Y(q(+))=q(-).
 \tag{EAG.4}
\]

The last two values are distinct by hypothesis.  If (q(\bot)=q(-)), apply (s_Y) to obtain
(q(\bot)=q(+)), a contradiction.  The case (q(\bot)=q(+)) is symmetric. \(\square\)

### Theorem 3.2 -- sharp ternary repair

The identity reporter (q_3:X\to X), with target involution (s_X), is equivariant, resolves the
pair, and has exactly three image values.  Therefore the lower bound in Theorem 3.1 is sharp.

### Proof

Identity commutes with every map, and the three source values are distinct. \(\square\)

The failure record itself has generated the smallest deterministic successor vocabulary compatible
with its symmetry: the exchanged alternatives plus one fixed background outcome.

## 4. Convex binary repair

Let the binary probability coordinate be (p\in\mathbb Q), with involution

\[
 s_{\Delta}(p)=1-p.
 \tag{EAG.5}
\]

Define

\[
 q_{\Delta}(-)=0,
 \qquad q_{\Delta}(+)=1,
 \qquad q_{\Delta}(\bot)=\frac12.
 \tag{EAG.6}
\]

### Theorem 4.1 -- equivariant convex repair

The reporter (q_{\Delta}) is equivariant and resolves the failed pair.  Its background value is
the unique fixed point of the binary probability involution:

\[
 1-p=p
 \quad\Longleftrightarrow\quad
 p=\frac12.
 \tag{EAG.7}
\]

### Proof

Equivariance is immediate on the two exchanged endpoints.  At the background,
(1-\frac12=\frac12).  Solving (1-p=p) over (mathbb Q) gives (2p=1), hence
(p=\frac12); the converse is direct. \(\square\)

The convex repair does not recover a pure deterministic background choice.  It replaces the third
deterministic outcome by a symmetric mixture of the two binary outcomes.

## 5. Oriented binary repair

If the failed pair is ordered, its transposition is no longer an admitted source symmetry.  The map

\[
 q_{\mathrm{or}}(-)=0,
 \qquad q_{\mathrm{or}}(\bot)=q_{\mathrm{or}}(+)=1
 \tag{EAG.8}
\]

is a deterministic binary separator.  It is not equivariant for the original unoriented swap,
because the fixed background would have to map to a fixed binary value and none exists.

Thus orientation and convexification are different repairs:

\[
\begin{array}{c|c|c}
\text{repair}&\text{preserves pair-swap?}&\text{successor type}\\
\hline
\text{ternary deterministic}&\text{yes}&\text{swapped pair plus fixed value}\\
\text{oriented binary}&\text{no}&\text{pure deterministic bit}\\
\text{convex binary}&\text{yes}&\text{binary simplex with fixed mixture}
\end{array}
\tag{EAG.9}
\]

## 6. Mechanism law

The exact universal-law statement is:

> A failure record can generate only successor doctrines containing its required orbit types.
> When an unoriented failure contains both a two-cycle and a fixed background, deterministic
> effectivity forces ternary arity.  Binary effectivity requires either symmetry breaking by
> orientation or convex completion by a mixed fixed point.

This is a formation law, not a proposed universal carrier.  It classifies the smallest possible
successor test from the failure's symmetry.

## 7. Hostile boundaries

1. **No background:** on the two-point swapped orbit alone, an equivariant binary bijection exists.
2. **Trivial output action:** a binary map can be equivariant, but then it identifies the swapped
   pair and does not resolve the failure.
3. **Randomized or multivalued reporters:** these evade deterministic impossibility by changing
   doctrine; their effectivity and cost require separate laws.
4. **Orientation is input:** the theorem proves what orientation enables, not where orientation
   comes from.
5. **Convexity is not universally erasing:** this finite calibration shows one precise mixed repair;
   it does not identify every positive construction with a phase quotient.
6. **Classical machinery:** fixed-point transport under equivariant maps and barycentric fixed
   points are classical.  New-field leverage, if any, lies in composing such forced doctrine
   changes during law genesis.

## 8. Closed proof ledger

| Claim | Status |
|---|---|
| fixed source point maps to fixed target point | proved |
| no equivariant deterministic binary reporter | proved |
| every equivariant separator has three distinct image values | proved |
| ternary lower bound is attained | proved |
| rational convex binary repair is equivariant | proved |
| symmetric mixture (1/2) is unique | proved |
| oriented binary separator exists but breaks swap equivariance | proved |

No RH statement, route realization, analytic continuation, physical measurement law, or general
positivity theorem is asserted.
