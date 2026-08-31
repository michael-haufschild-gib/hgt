# Parity suspension, conservative positivity, and the Xi-current lift

- **ID:** `ULF-ODTM-3`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / FUSION LAW
- **Scientific status:** `[PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-FORMALIZED] [NOT RH]`
- **Statement:** Every linear current has a canonical faithful square-zero parity suspension. An
  odd source symmetry becomes an even chain symmetry after the parity sign is included. Every
  bounded Hilbert realization then has a canonical positive self-adjoint Hodge Hamiltonian which
  vanishes exactly when the original current vanishes. Applied to the actual Xi conormal current,
  this gives an unconditional nonzero BRST charge retaining every multiplicity jet and commuting
  with the parity-corrected functional equation.

## Goal

Explain how multiplicity-bearing nilpotent information can coexist with positivity without being
killed by the existing skew-adjoint-square-zero no-go. Positivity must be a functorial observer of
an odd complex, not an ungraded property imposed on its differential.

## Gates

- [x] 0 → 1: universal construction, actual Xi application, collision audit, and falsifier explicit
- [x] 1 → 2: dependency-closed proofs below
- [x] 2 → 3: Lean modules, named leaf builds, umbrella wires, and axiom audit
- [ ] 3 → 4: source-natural Hilbert realization of the actual Xi complex

## 1. Algebraic parity suspension

Let `R` be a commutative ring, `M` an `R`-module, and `J:M→M` an `R`-linear current. Define the
parity double

\[
  \Pi M=M_{\bar0}\oplus M_{\bar1}
\]

and the odd charge

\[
  Q_J(x,y)=(0,Jx).                                         \tag{PSH.1}
\]

### Theorem 1.1 — faithful square-zero completion

\[
  Q_J^2=0,
  \qquad Q_J=0\Longleftrightarrow J=0.                    \tag{PSH.2}
\]

Moreover,

\[
\begin{aligned}
  \ker Q_J&=(\ker J)\oplus M,\\
  \operatorname{im}Q_J&=0\oplus\operatorname{im}J.
\end{aligned}                                             \tag{PSH.3}
\]

### Proof

Applying (PSH.1) twice gives `Q_J(0,Jx)=(0,J0)=0`. If `Q_J=0`, evaluation on `(x,0)` and projection
to the odd component give `Jx=0` for every `x`; the converse is immediate. Finally,
`Q_J(x,y)=0` iff `Jx=0`, while a vector is in its image iff it has the form `(0,Jx)`. ∎

This is information-neutral: square-zero completion does not identify or discard any current.

## 2. Symmetry transmutation

Suppose `tau:M→M` fixes zero and the current is `tau`-odd:

\[
  J\tau=-\tau J.                                          \tag{PSH.4}
\]

There are two lifts to the parity double:

\[
  \tau_{\mathrm{diag}}(x,y)=(\tau x,\tau y),\qquad
  \widehat\tau(x,y)=(\tau x,-\tau y).                    \tag{PSH.5}
\]

### Theorem 2.1 — external oddness becomes internal symmetry

\[
  Q_J\tau_{\mathrm{diag}}=-\tau_{\mathrm{diag}}Q_J,
  \qquad
  Q_J\widehat\tau=\widehat\tau Q_J.                      \tag{PSH.6}
\]

### Proof

Both identities follow by evaluating on `(x,y)` and using (PSH.4). The second sign in
`widehat tau` cancels the odd sign of `J`. ∎

Thus parity is not cosmetic bookkeeping: it is the exact lift converting a functional-equation
anti-intertwiner into a chain automorphism.

## 3. Positivity is an observer quotient

Let `E` be a complete real or complex Hilbert space and `J:E→E` bounded. Equip the Hilbert parity
double `E⊕₂E` with its `l²` inner product and use the same formula (PSH.1). Define

\[
  H_J=Q_J^*Q_J+Q_JQ_J^*.                                  \tag{PSH.7}
\]

### Theorem 3.1 — conservative Hodge positivity

`H_J` is positive and self-adjoint, and

\[
  H_J=0\Longleftrightarrow Q_J=0\Longleftrightarrow J=0.  \tag{PSH.8}
\]

For every `psi`,

\[
  \operatorname{Re}\langle\psi,H_J\psi\rangle
   =\|Q_J\psi\|^2+\|Q_J^*\psi\|^2\ge0.                  \tag{PSH.9}
\]

### Proof

Self-adjointness and (PSH.9) follow from the adjoint identities. If `H_J=0`, then (PSH.9) gives
`Q_J psi=0` for every `psi`, hence `Q_J=0`; the reverse implication is immediate. Apply Theorem
1.1 for the final equivalence. ∎

This resolves the apparent clash:

- an ungraded positive or skew-adjoint square-zero operator must vanish;
- a nonzero current survives as an odd square-zero differential;
- positivity is generated one categorical level later by its even Hodge anticommutator.

## 4. Actual Xi lift

Let `Q_Xi=Entire(C)/(XiC)` and let `J_Xi` be the actual conormal current of `ULF-ODTM-2`:

\[
  J_\Xi[F]=-[\Xi_C'][F].                                  \tag{PSH.10}
\]

Define

\[
  \mathcal Q_\Xi=Q_{J_\Xi}:Q_\Xi\oplus Q_\Xi
    \longrightarrow Q_\Xi\oplus Q_\Xi.                  \tag{PSH.11}
\]

### Theorem 4.1 — nonzero actual-Xi BRST current

The charge `mathcal Q_Xi` is square-zero and nonzero. For every Xi divisor point `rho` of exact
multiplicity `m_rho`,

\[
  \operatorname{jet}^{m_\rho-1}_{\alpha_\rho}
    \left(\operatorname{pr}_{\bar1}\mathcal Q_\Xi(1,0)\right)
  =-\Xi_C^{(m_\rho)}(\alpha_\rho)\ne0.                   \tag{PSH.12}
\]

### Proof

Square-zero and nonvanishing follow from Theorem 1.1 and the unconditional nonvanishing of
`J_Xi`. Formula (PSH.1) gives odd component `J_Xi[1]`; (PSH.12) is exactly the multiplicity-adapted
top-jet theorem of `ULF-ODTM-2`. ∎

### Theorem 4.2 — functional-equation chain lift

Let `sigma` be the actual functional-equation Real action on `Q_Xi`. Then

\[
  \widehat\sigma(x,y)=(\sigma x,-\sigma y)
\]

commutes with `mathcal Q_Xi`, while the unsigned diagonal lift anticommutes with it.

### Proof

`ULF-ODTM-2` proves `J_Xi sigma=-sigma J_Xi`. Apply Theorem 2.1. ∎

## 5. Fusion across route organs

One conservation mechanism now spans five distinct organs:

1. **analytic/divisor:** `J_Xi` is the conormal derivative class;
2. **multiplicity/Jordan:** its local top jet is nonzero at every multiplicity;
3. **functional equation:** the current is reflection-odd;
4. **homological/BRST:** parity suspension makes it a faithful square-zero differential and turns
   reflection into a commuting chain symmetry;
5. **positive/Hodge:** the anticommutator produces a positive self-adjoint observer without
   requiring the differential itself to be normal.

The predicted law in the positivity organ is exact: every faithful bounded realization of the Xi
current has nonzero Hodge Hamiltonian. Therefore a proposed positive realization with zero Hodge
energy is necessarily non-conservative; it has erased the conormal current.

## 6. Exact RH gate and falsifier

Parity suspension does not create the missing prime-source realization. It identifies its correct
type. Required object is now a graded bounded realization of the *complex*

\[
  (Q_\Xi\oplus Q_\Xi,\mathcal Q_\Xi,\widehat\sigma),
\]

not an ungraded normal realization of `J_Xi`. It must be:

1. source-natural for the independently formed theta/prime--Gamma carrier;
2. conservative on the nonzero odd range;
3. compatible with common recovery;
4. positive only after Hodge formation;
5. connected to the existing prime-sector superselection theorem.

If every such source-natural graded realization kills `mathcal Q_Xi`, this mechanism cannot close
RH. If one is conservative, its Hodge observer is automatically positive and nonzero; existing
superselection can then be applied without the nilpotent-normality contradiction.

## 7. Collision audit

- `BRSTHodgeConstraint.lean` proves Hodge positivity for a supplied bounded charge but does not
  construct a faithful charge from an arbitrary current or apply it to the actual Xi conormal.
- `TateFractureObstructionBianchiAmplitudeLaw.lean` proves a skew-adjoint square-zero map vanishes;
  this card explains that result as a category error for multiplicity currents.
- `PolarizedExactnessHorizonRelativeConnesPhaseLaw.lean` contains specific dual-number exactness,
  not the faithful functor `J↦Q_J`, its symmetry lift, or the actual-Xi application.
- `DeningerArithmeticBoundedHilbertComplex.lean` assumes a bounded arithmetic differential; it
  does not derive one from the Xi conormal current.

No novelty criterion is asserted or required. Contribution is exact fusion and reinterpretation.

## Log

- 2026-08-30 — dependency-closed paper proof written; generic algebraic and Hilbert constructions
  pass scratch Lean elaboration.
- 2026-08-31 — formalized as
  `GaloisForLFunctions.HTGeometry.ConstitutiveParitySuspensionHodge` and
  `GaloisForLFunctions.RHTower.XiConormalParitySuspensionHodge`; direct elaboration and batched
  named leaf builds pass (`8962/8962`), umbrellas wired without building them, scoped
  forbidden-declaration and diff checks pass, and audited capstones depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
