# Ramsey--Weyl causal phase law

- **ID:** `ramsey-weyl-causal-phase-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / QUANTUM CLOCKS / CAUSAL PROPAGATOR / NONPERTURBATIVE MEASUREMENT
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** paper-proved; central-phase, Ramsey reconstruction, and branch-free phase-generator
  recovery formalized unconditionally in Lean.

## Headline

> **Swap the order of two clock kicks; their phase is the arrow of causal influence.**

This supplies a nonperturbative clock-to-causal-propagator bridge for a Weyl field. It does not rely
on detector transition probabilities or a chosen quantum state.

## Weyl clock kicks

Let \(\Phi(f)\) be a real linear bosonic field smeared with a real test function \(f\), and let

\[
  W(\lambda f)=e^{i\lambda\Phi(f)}
\]

be its Weyl unitary. Let \(E(f,h)\) denote the real causal propagator pairing. In the convention

\[
  W(f)W(h)
  =
  e^{-\frac i2E(f,h)}W(f+h),                                             \tag{1}
\]

antisymmetry of \(E\) gives

\[
  \boxed{
  W(\lambda f)W(\eta h)
  =
  e^{-i\lambda\eta E(f,h)}
  W(\eta h)W(\lambda f).}                                                \tag{2}
\]

## Theorem 1 — order commutator is causal phase

\[
  \boxed{
  W(\lambda f)W(\eta h)
  W(\lambda f)^{-1}W(\eta h)^{-1}
  =
  e^{-i\lambda\eta E(f,h)}I.}                                           \tag{3}
\]

### Proof

Multiply `(2)` on the right by
\(W(\lambda f)^{-1}W(\eta h)^{-1}\). The Weyl operators cancel in reverse order, leaving only the
central phase. \(\square\)

Equation `(3)` is state-independent. A quantum-controlled order experiment can place the two
sequences \(W(\lambda f)W(\eta h)\) and \(W(\eta h)W(\lambda f)\) on two clock-control branches.
Their interference phase is the causal propagator phase.

## Theorem 2 — Ramsey expectations reconstruct the phase

Let \(\omega\) be any complex-linear state functional. Applying \(\omega\) to `(2)` gives

\[
  \omega\!\left(W(\lambda f)W(\eta h)\right)
  =
  e^{-i\lambda\eta E(f,h)}
  \omega\!\left(W(\eta h)W(\lambda f)\right).                            \tag{4}
\]

If the reverse-order expectation is nonzero,

\[
  \boxed{
  e^{-i\lambda\eta E(f,h)}
  =
  \frac{\omega(W(\lambda f)W(\eta h))}
       {\omega(W(\eta h)W(\lambda f))}.}                                 \tag{5}
\]

A controlled Ramsey qubit reads the real and imaginary parts of each complex expectation in its
Pauli-X and Pauli-Y quadratures. The two-quadrature map is injective, so `(5)` is fully observable
within the controlled-unitary model.

Nonvanishing is automatic in a sufficiently small neighborhood of
\((\lambda,\eta)=(0,0)\) when the expectation is continuous, because both ordered expectations
equal \(1\) at zero coupling.

## Theorem 3 — branch-free causal-pairing recovery

Put \(t=\lambda\eta\) and let

\[
  \Omega_{f,h}(t)=e^{-itE(f,h)}.
\]

Although one fixed phase determines \(E(f,h)\) only modulo \(2\pi/t\), a continuous calibrated scan
through \(t=0\) gives

\[
  \boxed{
  E(f,h)=i\,\Omega'_{f,h}(0).}                                           \tag{6}
\]

### Proof

\[
  \Omega'_{f,h}(t)
  =
  -iE(f,h)e^{-itE(f,h)}.
\]

At \(t=0\), \(\Omega'_{f,h}(0)=-iE(f,h)\), proving `(6)`. \(\square\)

Thus the causal pairing is recovered without selecting a logarithm branch.

## From causal phase to retarded response

For clock-labelled interventions with known local time orientation, the retarded linear response
is the future-supported half of the Pauli--Jordan propagator. Repeating `(3)` over a separating
family of compact smearings reconstructs the causal propagator on the accessible test-function
space. Source-response data then supply the retarded sector used by the two-mass self-calibration
law.

This final support step is not yet proved here for an unknown Lorentzian causal diamond. It
requires a globally hyperbolic support theorem and relational event anchoring by the clock
laboratory.

## Scope and failure modes

Load-bearing hypotheses:

1. a linear bosonic Weyl/CCR probe sector;
2. controllable compactly smeared Weyl unitaries;
3. coherent quantum control of the two orderings;
4. complex Ramsey quadrature readout;
5. calibrated continuous coupling near zero;
6. sufficient test-function coverage.

The theorem does not establish Weyl relations for nonlinear gravitational observables, nor
controlled implementation in relativistic QFT with detector backreaction. Gauge constraints may
restrict the available smearings. These are the physical open core, not hidden assumptions.

Published fast-kick detector protocols recover both Wightman quadratures at leading perturbative
order (<https://arxiv.org/abs/1807.00013>). Equation `(3)` instead uses the exact Weyl group
commutator and is state-independent. A priority audit of quantum-switch, out-of-time-order, and
characteristic-functional measurement protocols remains required before claiming experimental
novelty.
