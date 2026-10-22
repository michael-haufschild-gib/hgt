# Deninger Kummer normalized-cup small-divisor cancellation

**Stage:** 3-formalized  
**Status:** fully proved on paper; formalized unconditionally in Lean  
**Route:** `L`  
**Exact label:** `DAC_KUMMER_NORMALIZED_CUP_SMALL_DIVISOR_CANCELLATION`  
**Positive survivor:** `DAC_KUMMER_CUP_HILBERT_EXTENSION`

## Claim

Let `\mu\ne0` be a signed Kummer frequency and let `\alpha_\mu` be its harmonic half-cylinder
mode.  Existing source formulas give

\[
 \|\alpha_\mu\|_{\mathcal E}^{2}=\frac1{|\mu|},
 \qquad
 \Psi(\alpha_\mu,\alpha_{-\mu})=\frac{i}{\mu}.                 \tag{1}
\]

Define the energy-normalized mode

\[
 e_\mu=|\mu|^{1/2}\alpha_\mu.                                 \tag{2}
\]

Then

\[
 \|e_\mu\|_{\mathcal E}=1,
 \qquad
 \Psi(e_\mu,e_{-\mu})=i\,\operatorname{sgn}(\mu).            \tag{3}
\]

Distinct characters are orthogonal, and the cup is zero unless characters are opposite.  Hence on
every finite symmetric Kummer packet

\[
 \Psi(a,b)=
 \sum_m a_m b_{-m}\,i\operatorname{sgn}(\ell(m))              \tag{4}
\]

satisfies the frequency- and rank-independent estimate

\[
 |\Psi(a,b)|
 \le
 \left(\sum_m|a_m|^2\right)^{1/2}
 \left(\sum_m|b_m|^2\right)^{1/2}.                            \tag{5}
\]

Therefore `(4)` extends uniquely to a bounded complex-bilinear form of norm at most one on the
energy Hilbert completion.  Dense signed Kummer frequencies do **not** obstruct the global
cup/Green cross-form.  They obstruct the inverse generator and contraction homotopy instead.

## Proof

By bilinearity and `|{-\mu}|=|\mu|`, equations `(1)`--`(2)` give

\[
 \Psi(e_\mu,e_{-\mu})
 =|\mu|\frac{i}{\mu}
 =i\operatorname{sgn}(\mu),
\]

proving `(3)`.  Haar orthogonality on the Kummer torus gives `(4)`.  Since opposition
`m\mapsto-m` is a permutation and the sign multiplier has modulus one, triangle inequality followed
by Cauchy--Schwarz gives

\[
 \begin{aligned}
 |\Psi(a,b)|
 &\le\sum_m |a_m|\,|b_{-m}|\\
 &\le\left(\sum_m|a_m|^2\right)^{1/2}
       \left(\sum_m|b_{-m}|^2\right)^{1/2},
 \end{aligned}
\]

and the last sum equals `\sum_m|b_m|^2`.  This proves `(5)` and the Hilbert extension.

## Hard distinction: form versus homotopy

The cancellation does not produce a bounded Green inverse.  On the normalized basis,

\[
 |D_\ell|^{-1}e_\mu=|\mu|^{-1}e_\mu,
\]

which is unbounded because signed prime-log frequencies approach zero.  Thus:

- cup form: bounded, small divisor cancels exactly;
- Hodge sign: bounded and unitary;
- Green inverse/Koszul contraction: unbounded without a stronger domain or closed-range theorem.

This separates two mechanisms previously conflated in Route L.

## Hostile audit

- **Not wrapper work.** Exact cancellation removes a live proposed obstruction to construction of
  global Kummer cup form.
- **Not a positivity assumption.** Formula follows from explicit harmonic mode integral and energy
  normalization.
- **No hidden uniform gap.** Frequencies may approach zero; estimate remains uniform because form
  and norm have the same singular weight.
- **No false cohomology claim.** Bounded cup does not imply bounded contraction, closed range,
  nonzero cohomology, or Paugam comparison.
- **No RH premise.** No Xi divisor or zeta-zero datum appears.

## Collision and novelty audit

Internal corpus separately contains raw identities
`deningerCylinderInner_self = 1/|\mu|`, `deningerCylinderCup_mode_neg = i/\mu`, and normalized-mode
orthonormality.  Search found no theorem computing normalized opposite-mode cup or proving the
uniform packet bound `(5)`.  New knowledge is exact Route-L localization: the same Kummer small
divisor that destroys a bounded inverse cancels from the Hilbert cup form.

The argument is elementary after the correct energy normalization is selected.  Its novelty is not
Cauchy--Schwarz; it is identifying which global Route-L object is and is not small-divisor singular.

## Formalization target

Formalize unconditionally:

1. complex bilinearity of cylinder cup under constant rescaling;
2. normalized opposite-mode identity `(3)`;
3. abstract finite packet form `(4)` and estimate `(5)` for an opposition equivalence and a
   unimodular real sign family.

## Lean status

All three targets are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerKummerNormalizedCupSmallDivisorCancellation.lean`.
Axiom audit for every declaration: `propext, Classical.choice, Quot.sound`.

- Target 1 — `deningerCylinderCup_smul` is the complex bilinearity of the cylinder cup under
  constant rescaling, proved by moving the two constants through the leafwise wedge and the two
  integrals.
- Target 2 — `deningerNormalizedCylinderMode_cup_neg` is `(3)`: the energy normalization `|μ|^{1/2}`
  cancels the complete small divisor and leaves the unimodular value `i·sgn(μ)`.  It consumes the
  raw identities `deningerCylinderCup_mode_neg` and `deningerCylinderInner_mode` from
  `DeningerCylinderModes.lean` rather than reproving them.
- Target 3 — `deningerNormalizedKummerCupPacket` is the finite packet form `(4)` for an arbitrary
  opposition equivalence and unimodular real sign family, `deningerNormalizedKummerPacketMass` the
  squared coefficient mass, and `deningerNormalizedKummerCupPacket_norm_le` the frequency- and
  rank-independent estimate `(5)`, obtained from the triangle inequality followed by
  Cauchy--Schwarz and the fact that opposition is a permutation.

## Route-L effect

The form-level part of `[CONJECTURE] DAC_KUMMER_INCIDENCE_GREEN_CROSS_FORM` is solved on the complete
Kummer phase sector.  Replace its surviving analytic core by

`[CONJECTURE] DAC_KUMMER_GREEN_HOMOTOPY_CLOSED_RANGE`:

> construct the correct source domain for the unbounded inverse `|D_\ell|^{-1}`, identify its
> closed/reduced cohomology under Milnor incidence, and prove compatibility with Cauchy/residue
> transition maps.

Cross-sector Milnor terms and comparison with Paugam's cup remain open.

- 2026-08-06 — Lean modules re-audited on this toolchain (`#print axioms` = `propext, Classical.choice, Quot.sound` for every capstone); every gate except the declared successor conjecture is closed, so the card moves to `3-formalized`.
