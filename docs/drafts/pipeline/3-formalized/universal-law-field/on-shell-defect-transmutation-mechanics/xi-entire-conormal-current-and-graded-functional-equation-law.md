# Xi-entire conormal current and graded functional-equation law

- **ID:** `ULF-ODTM-2`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / ACTUAL-XI INSTANTIATION
- **Scientific status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [NOT RH]`
- **Statement:** Ordinary complex differentiation on the entire Xi source algebra produces a
  canonical on-shell conormal current on `Entire(C)/(XiC)`. The current is odd under the actual
  functional-equation Real action, is nonzero, and at every Xi zero of multiplicity `m` its
  `(m-1)`-jet is exactly the negative nonzero `m`-th Xi jet.

## Goal

Remove model dependence from `ULF-ODTM-1`. The equation-Wronskian mechanism is instantiated on the
literal completed Xi entire quotient already used by source arithmetic cohomology. The result must
retain every Xi multiplicity and interact with the existing functional-equation action by a proved
graded law.

This card does not identify the Xi quotient with an independently constructed prime Hilbert
carrier. That conservative realization remains the selection gate.

## Gates

- [x] 0 → 1: actual Xi carrier, actual functional equation, exact jets, and falsifier identified
- [x] 1 → 2: dependency-closed proofs below
- [x] 2 → 3: Lean module, named leaf build, umbrella wires, and axiom audit
- [ ] 3 → 4: conservative source/Hodge realization

## 1. Actual entire differential source

Let

\[
  A=\operatorname{Entire}(\mathbb C),\qquad
  a(z)=\Xi_C(z),\qquad I=(a),\qquad Q=A/I.
\]

Here `XiC(z)=xi(1/2+iz)` is the centered completed Xi function. Define

\[
  \partial F=F'.                                             \tag{XIC.1}
\]

### Theorem 1.1 — entire derivation

`partial` is a `Z`-derivation of `A`.

### Proof

The derivative of an entire function is entire. Additivity and the Leibniz identity

\[
  (FG)'=F'G+FG'
\]

give the additive and derivation laws. Integer constants have zero derivative, so this is a
`Z`-derivation. ∎

## 2. Literal Xi on-shell current

Define on `A`

\[
  W_\Xi(F)=\Xi_C F'-\Xi_C'F.                                \tag{XIC.2}
\]

### Theorem 2.1 — exact descent and reconstruction

For all `B,F in A`,

\[
  W_\Xi(BF)-B W_\Xi(F)=\Xi_C B'F,                           \tag{XIC.3}
\]

and

\[
  W_\Xi(\Xi_C F)=\Xi_C^2F'.                                \tag{XIC.4}
\]

Therefore `W_Xi` preserves `I`, descends to a `Q`-linear endomorphism

\[
  \mathcal J_\Xi:Q\longrightarrow Q,
\]

and obeys the exact reconstruction law

\[
  \mathcal J_\Xi([F])=-[\Xi_C'][F].                         \tag{XIC.5}
\]

Its range is the principal conormal module `Q[-XiC']`, and

\[
  \mathcal J_\Xi^2([F])=[\Xi_C']^2[F].                      \tag{XIC.6}
\]

### Proof

Apply the Leibniz rule to (XIC.2). In (XIC.3), all terms except `XiC B'F` cancel. In (XIC.4),
the two terms containing `XiC XiC'F` cancel. Modulo `(XiC)`, the first summand in (XIC.2) vanishes,
giving (XIC.5). Range and square follow by multiplication. ∎

## 3. Multiplicity-faithful nonvanishing

Let `rho` be any point of the global Xi divisor, let

\[
  \alpha_\rho=\operatorname{xiSpectralPointSupport}(\rho),
  \qquad m_\rho=\operatorname{xiSupportMultiplicity}(\rho)>0.
\]

The corpus proves the exact jet law

\[
  \Xi_C^{(j)}(\alpha_\rho)=0\quad(j<m_\rho),\qquad
  \Xi_C^{(m_\rho)}(\alpha_\rho)\ne0.                       \tag{XIC.7}
\]

It also proves that every jet of order `<m_rho` annihilates `(XiC)` and therefore descends to `Q`.

### Theorem 3.1 — exact top-conormal jet

For every Xi divisor point `rho`, the descended jet of order `m_rho-1` satisfies

\[
  \operatorname{jet}_{\alpha_\rho}^{m_\rho-1}
    (\mathcal J_\Xi[1])
  =-\Xi_C^{(m_\rho)}(\alpha_\rho)\ne0.                     \tag{XIC.8}
\]

Consequently `J_Xi[1] != 0`, `J_Xi != 0`, and `XiC'` is not in the ideal `(XiC)`.

### Proof

By (XIC.5), `J_Xi[1]=-[XiC']`. Since `m_rho>0`, the natural number `m_rho-1` is strictly less
than `m_rho`, so its jet is defined on the quotient. Differentiating `XiC'` another `m_rho-1`
times gives the `m_rho`-th derivative of `XiC`. Equation (XIC.7) makes the right side of (XIC.8)
nonzero. A quotient class detected by a descended linear functional is nonzero; hence all three
consequences follow. ∎

This is stronger than support detection. One fixed global current contains the top surviving
conormal layer at every zero, while the detecting jet order adapts to local multiplicity.

## 4. Actual functional-equation action

Define the source Real action

\[
  (\sigma F)(z)=\overline{F(-\bar z)}.                      \tag{XIC.9}
\]

The existing functional-equation theorem gives `sigma(XiC)=XiC`; multiplication and involutivity
make `sigma` a ring automorphism of `A` and it descends to `Q`.

### Theorem 4.1 — derivative and current are graded

For every `F in A`,

\[
  \partial(\sigma F)=-\sigma(\partial F),                  \tag{XIC.10}
\]

and therefore

\[
  W_\Xi\sigma=-\sigma W_\Xi,
  \qquad
  \mathcal J_\Xi\bar\sigma=-\bar\sigma\mathcal J_\Xi.    \tag{XIC.11}
\]

### Proof

The complex chain rule applied to (XIC.9) gives

\[
  (\sigma F)'(z)=-\overline{F'(-\bar z)},
\]

which is (XIC.10). Since `sigma(XiC)=XiC`, applying (XIC.10) to `XiC` also gives
`sigma(XiC')=-XiC'`. Substitute these two identities into (XIC.2) to get the off-shell law, then
pass to the stable quotient. ∎

### Corollary 4.2 — parity is information-neutral

The functional-equation action neither creates nor deletes the conormal current: it carries its
range isomorphically to itself and reverses its grade. In particular, nonvanishing at one divisor
point transports to the reflected divisor point with the forced odd sign.

### Proof

`bar sigma` is an involutive ring automorphism and (XIC.11) is an exact anticommutation identity.
Thus it maps `range(J_Xi)` bijectively onto itself. ∎

## 5. Fusion law and fourth-organ prediction

One literal Xi object now joins four route organs:

1. **analytic source:** ordinary differentiation of entire cochains;
2. **scheme-theoretic divisor:** the conormal class `-[XiC']` on `Entire/(XiC)`;
3. **functional equation:** odd Real grade (XIC.11);
4. **multiplicity/Jordan organ:** the exact top-jet law (XIC.8).

The mechanism predicts the following rule for any conservative realization into a graded source
complex: multiple Xi zeros must appear as nonzero nilpotent odd boundary currents, while simple
zeros appear as nonzero invertible local conormal phases. A positive Hilbert realization cannot
represent a nonzero square-zero conormal current as an ungraded skew-adjoint operator; it must use
a graded/BRST doubling whose positive observable is the Hodge Hamiltonian
`J*J + JJ*`. This prediction is already compatible with the corpus's abstract BRST/Hodge laws and
its skew-adjoint-square-zero no-go.

## 6. Exact RH gate and falsifier

This theorem is not RH. `Q` is Xi-built comparison cohomology, not yet an independently formed
prime source carrier. The exact next theorem must construct a source-natural conservative functor

\[
  \mathfrak R:Q\text{-conormal complexes}
    \longrightarrow \text{closed graded prime--Gamma source correspondences}
\]

such that:

1. `R` intertwines functional-equation reflection and common recovery;
2. `R(J_Xi)` is nonzero whenever `J_Xi` is nonzero;
3. its ungraded observer quotient is the existing positive/Hodge carrier;
4. at a prime-sector fibre, a nonzero closed sewing remains possible only on the critical line.

Existing common-recovery superselection would then turn conservativity into selection. If every
admissible positive source realization kills the conormal range, this current explains divisor
multiplicity but cannot close RH. That is the falsifier.

## 7. Collision audit

- `DeningerEntireQuotientCohomology.lean` constructs `Q` but no derivative current.
- `DeningerArithmeticJetDuality.lean` descends multiplicity-bounded jets but does not assemble
  them into one global on-shell endomorphism.
- `DeningerArithmeticRealStructure.lean` constructs the even functional-equation action but no
  odd conormal operator.
- `XiHedenmalmSymmetricMultiplicity.lean` relates symmetry to simple zeros after a Hilbert
  realization; it does not construct the actual Xi conormal current.
- `ULF-ODTM-1` proves the universal algebra and polynomial local model; this card proves the
  actual entire-Xi instantiation and exact all-divisor jet detector.

No novelty criterion is asserted or required. Contribution is exact fusion and reinterpretation.

## Log

- 2026-08-30 — complete paper proof written after scratch verification of entire differentiation,
  functional-equation anti-commutation, and the top-jet nonvanishing argument.
- 2026-08-30 — formalized as
  `GaloisForLFunctions.RHTower.XiEntireOnShellWronskianInternalization`; direct elaboration and
  named leaf build pass (`8956/8956`), RHTower and universal-law-field imports wired without
  building either umbrella, forbidden-declaration scan clean, and headline axiom audit contains
  only `propext`, `Classical.choice`, and `Quot.sound`.
