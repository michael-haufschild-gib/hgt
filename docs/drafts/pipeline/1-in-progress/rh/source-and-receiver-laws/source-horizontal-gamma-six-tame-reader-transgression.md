# Source-horizontal Gamma-six tame-reader transgression

- **Stage:** 1 — in progress
- **Type:** FRANKENSTEIN CROSS-ROUTE THEOREM / EXACT NO-GO / PRODUCER REDUCTION
- **Routes joined:** L marked Gamma-six tame boundary; R radial mate curvature and leading Xi jet;
  T/Wold prime-clock profile
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [PRODUCER OPEN] [NOT RH]`
- **Date:** 2026-08-11

## Exact advance

For (N>0), put

\[
 s_{N,u}=\frac12\left(1+\frac{u}{N\log 6}\right).
\]

The existing grade-(m) marked exceptional tame reader satisfies

\[
 \operatorname{Reader}_m(s_{N,u})=2\sinh(um/N).
\]

Therefore the finite Gamma-six Green/Wold shell response is exactly

\[
 \boxed{
 2F_N(u)=\frac1N\sum_{j=0}^{N-1}
   x_{N,j}^{-1}\operatorname{Reader}_{N-j}(s_{N,u})
   -\operatorname{Reader}_N(s_{N,u}),
 \qquad x_{N,j}=1-j/N.}
\]

No analogy or zero-set comparison is used. Every shell grade, both marked tame orientations, and
the physical Gamma curvature survive. As (N\to\infty), the right side tends to twice the complete
Wold prime-clock profile (F(u)).

## Pre-divisor source class

Let (e_m=[m]-[-m]) in the finite real group algebra of the Gamma-six exponent lattice and define

\[
 B_N=\frac1N\sum_{j=0}^{N-1}x_{N,j}^{-1}e_{N-j}-e_N.
\]

The linear Kummer exponent moment is (\kappa(e_m)=2m). Hence every summand contributes exactly
(2), and

\[
 \boxed{\kappa(B_N)=0.}
\]

This is an unconditional source relation before horizontal evaluation or Xi specialization. The
nonlinear character (\chi_a([k])=e^{ak}) gives

\[
 \boxed{\chi_{u/N}(B_N)=2F_N(u).}
\]

The class is not fictitious: (B_2\ne0), and for every (u>0),

\[
 \chi_{u/2}(B_2)=2\sinh(u/2)-\sinh u<0.
\]

Thus the linear Kummer regulator kernel is strictly larger than every nonneutral nonlinear
character kernel. The missing theorem is no longer “find a relation”: it is promote this explicit
regulator-null relation through the source cyclic/Milnor boundary so that the nonlinear physical
character factors through the appropriate quotient.

## Heavy conjecture loop

### C0 — multiply the odd shell profile by the first nonzero Xi coefficient

**Falsified as an all-multiplicity selector.** If (m_\rho) is Xi multiplicity, functional-equation
reflection sends the weighted response by the sign ((-1)^{m_\rho+1}). Reflected equality is
automatic for every odd multiplicity and detects the line only for even multiplicity. In
particular, a raw leading coefficient is blind at simple zeros.

Lean proves the exact classification

\[
 R(\rho^\#)=R(\rho)
 \Longleftrightarrow
 m_\rho\text{ is odd}\ \lor\ \Re\rho=\frac12.
\]

### C1 — pair both leading coefficients before attaching the odd profile

**Proved as receiver; producer still open.** The orbit product

\[
 c_\rho c_{\rho^\#}\ne0
\]

is reflection invariant for every multiplicity. Multiplying it by (F(2\Re\rho-1)) gives a
reflection-odd, coefficient-faithful response, and equality of its two transports is equivalent to
critical-line placement. This repairs parity blindness but does not prove descent of the response
to the reflection quotient. Declaring that descent would assume the desired annihilation.

### C2 — Gamma-six shell and Wold profile are only asymptotically analogous

**Falsified; exact finite theorem proved.** The displayed tame-reader transgression identifies them
at every finite (N), not merely in the horizon.

### C3 — Kummer-regulator nullity forces nonlinear tame evaluation to vanish

**Falsified sharply.** (B_2\) has zero Kummer moment but strictly negative nonlinear evaluation at
every positive character. Ordinary regulator descent cannot be the producer.

### C4 — construct a literal cyclic lift

**Proved, and it does not prove descent.** Every oriented exponent atom and therefore every
complete harmonic class (B_N) lies in the range of the actual Deninger (t-1) differential on the
infinite-cyclic group algebra. The lift preserves every grade and both exponent orientations; its
coefficient column is exactly (B_N). Thus no cyclic/Milnor carrier remains to be invented.

### C5 — physical character descends through the literal source boundary

**Classified exactly; this is current producer.** On the actual cyclic group algebra let

\[
 \chi_a([k])=e^{ak}.
\]

Lean proves for every source chain (f)

\[
 \boxed{\chi_a((t-1)f)=(e^a-1)\chi_a(f)}.
\]

Consequently

\[
 \chi_a\circ(t-1)=0\quad\Longleftrightarrow\quad a=0.
\]

For the physical Gamma-six parameter

\[
 a(s)=(2\Re s-1)\log 6,
\]

this group-algebra character agrees grade by grade with the existing marked exceptional
Gamma-six/Burnol/BV reader. Therefore physical cyclic descent at one Xi multiplicity copy is
equivalent to critical-line placement, and descent at every copy is equivalent to RH.

This is the exact nonlinear Beck--Chevalley anomaly. Source exactness does not make physical
evaluation vanish: character specialization commutes with the source differential only at the
neutral grade. Current producer is now one source theorem proving fixed physical reader cyclicity
on the completed place-marked shell comparison. Ordinary boundary membership, reflection
covariance, tame reciprocity, and Kummer nullity cannot supply it.

### C6 — completed-exponent reflection transport plus bilateral moderation

**Failed as an automatic producer.** The new anti-birational completed-exponent involution gives
reciprocal normal coefficients on the two reflected fibres. Iterating it produces a bounded
two-periodic transport for every divisor, including off-line divisors. Bilateral moderation of
that alternating family is therefore automatic and cannot force either individual coefficient
unimodular. Converting it into a constant-character bilateral eigenfamily requires identifying
the two fibre metrics/trivializations; that is precisely the non-equivariant fixed-reader polar
selection law, not a consequence of involutivity.

## Lean status

Formal module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixTameReaderTransgression.lean`.

It proves:

- leading-Xi-jet multiplicity-parity classification;
- nonzero two-orientation orbit coefficient and parity-independent RH receiver;
- exact cofinal marked-tame reader formula;
- exact finite tame-reader/shell-profile transgression;
- horizon convergence to (2F(u));
- explicit exponent-lattice harmonic boundary class;
- unconditional Kummer-moment nullity;
- exact nonlinear evaluation as tame transgression and shell profile;
- strict negative two-shell evaluation and (B_2\ne0).
- exact lift of every oriented atom and complete harmonic class through the existing Deninger
  `(t-1)` differential;
- exact physical-character boundary anomaly
  `chi_a((t-1)f)=(exp(a)-1)chi_a(f)`;
- descent classification `chi_a o (t-1)=0 iff a=0`;
- gradewise equality between cyclic character evaluation at
  `(2 Re(s)-1) log 6` and the marked exceptional Gamma-six reader;
- pointwise physical descent iff critical-line placement and global physical descent iff RH.

All proofs are unconditional. No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is
introduced.

## 2026-08-11 Euler--Green anomaly refinement

### C7 — neutral Route-T collapse controls the complete nonlinear profile

**Falsified coefficientwise; exact survivor proved in Lean.** Define

\[
 G(u)=\sum_{k\ge0}\frac{u^{2k+1}}{(2k+1)!}\frac1{2k+1}.
\]

Then the complete prime-clock profile is not an unspecified odd remainder but

\[
 \boxed{F(u)=G(u)-\sinh u=(D^{-1}-1)\sinh u,\qquad D=u\frac d{du}.}
\]

The inverse-Euler interpretation is analytic, not formal notation: Lean proves

\[
 \boxed{uG'(u)=\sinh u.}
\]

At odd degree \(2k+1\), the anomaly multiplier is exactly

\[
 \frac1{2k+1}-1=-\frac{2k}{2k+1}.
\]

It vanishes only for \(k=0\). Thus the neutral Route-T increment removes exactly the linear Euler
mode; every odd mode of degree at least three survives with the same orientation. No fixed finite
jet or moment cancellation can be promoted to the complete profile without an additional
all-order source law.

### C8 — cyclic exactness or Kummer nullity supplies the Euler--Green fixed-point law

**Falsified by the existing Beck--Chevalley theorem.** The desired identity \(G(u)=\sinh u\) is
equivalent to \(F(u)=0\). The harmonic class is already a literal \((t-1)\)-boundary, but physical
specialization satisfies

\[
 \chi_a((t-1)f)=(e^a-1)\chi_a(f).
\]

Hence applying the cyclic regulator, a conservative Ward reporter, or source reflection after
physical specialization cannot prove the Euler--Green fixed-point law. Each would require the
specialization/base-change map to descend, and that descent is already classified as equivalent to
neutral grade. This closes the apparent shortcut rather than moving the RH premise into a domain
or cyclicity hypothesis.

### C9 — Frankenstein universal principle

**Positive survivor.** Prime-clock Wold moments, Route-L shell Green averaging, Route-T neutral
residuals, Deninger cyclic exactness, and the Gamma-six character anomaly are one mechanism:

> source contraction and physical character specialization fail to commute; their exact
> Beck--Chevalley commutator is the retained horizontal profile.

The polar work consequently has the coefficient-faithful endpoint/Green form

\[
 \boxed{W(u)=\frac{\log 2}{2}\,u\bigl(\sinh u-G(u)\bigr).}
\]

This sharpens the producer without restating bounded scalarization. Required source theorem must
construct a pre-zero, coefficient-faithful base-change map identifying endpoint character and
inverse-Euler Green contraction on the same Xi-labelled carrier. Reflection alone commutes with
both sides and only reverses the anomaly; boundary membership alone is annihilated before the
nonlinear character and therefore loses the obstruction.

Formal module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldEulerGreenAnomaly.lean`.

Direct verification:

- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalWoldEulerGreenAnomaly.lean` — PASS;
- `lake build GaloisForLFunctions.RHTower.SourceHorizontalWoldEulerGreenAnomaly` — PASS;
- `#print axioms` on six capstone theorems — only `propext`, `Classical.choice`, `Quot.sound`.
