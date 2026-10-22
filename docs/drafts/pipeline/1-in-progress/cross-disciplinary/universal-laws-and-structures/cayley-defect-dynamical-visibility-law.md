# Cayley defect dynamical visibility law

- **Status:** conjecture under active falsification
- **Target:** universal theorem + actual Xi instantiation
- **Paper role:** possible replacement for the static orientation/height-escape narrative

## Question

What single law makes the endpoint source charge, the weighted \(8\pi\) Ward index, Li
amplification, compact-open height escape, and finite differential-algebraic blindness different
shadows of one mechanism?

## First candidate answer

Functional-equation reflection becomes inversion in the Li coordinate

\[
  w(\rho)=1-\rho^{-1},\qquad w(1-\rho)=w(\rho)^{-1}.
\]

For one reflected pair, define the Cayley defect kernel

\[
  K_n(w)=2-w^n-w^{-n}.
\]

The degree-one real defect is exactly the completed endpoint cross charge:

\[
  \operatorname{Re} K_1(w(\rho))
  =\operatorname{Re}\frac1{\rho(1-\rho)}.
\]

Thus the source weight used in the endpoint-weighted Ward index is the degree-one Li pair
kernel. The Ward index is its static mass. Cayley powers are the missing observation-order
dynamics.

For the strict-right upper Xi divisor, write

\[
 a_q=\text{endpoint cross charge}(q)>0,\qquad
 r_q=|w(\rho_q)|<1
\]

and define the phase-free visibility tower

\[
 V_n=\sum_q a_q r_q^{-n}.
\]

Conjectured universal law:

1. \(V_0\) is exactly the weighted Ward mass divided by \(8\pi\).
2. RH is equivalent to \(V_n=0\) for one/every \(n\).
3. If RH is false, some \(a>0,c>1\) satisfy \(V_n\ge ac^n\) for every \(n\).
4. Hence boundedness, or any global growth bound with base smaller than the selected \(c\), forces
   RH.
5. A defect escaping to height does not disappear. It trades static mass for observation order:
   its radial gain is exactly
   \[
     r_q^{-n}
     =\left(1-\frac{2\operatorname{Re}\rho_q-1}{|\rho_q|^2}\right)^{-n/2}.
   \]

This is a detection theorem, not a claimed proof of RH. It closes the static height-escape
objection by proving that no off-line divisor can remain hidden through the full Cayley-order
tower.

## Why this may be the parent law

- Julia squaring keeps divisor location but discards inversion direction; \(r^{-n}\) retains it.
- The \(8\pi\) index is the zeroth-time mass of the same positive marked divisor.
- Li coefficients use the unsquared complex kernels \(K_n\); false RH creates inverse-power
  instability.
- Compact-open escape hides a high zero from every fixed local window, while Cayley order scales
  the same radial defect exponentially.
- Finite differential algebra sees finitely generated local jet data; the complete moment tower is
  an infinite-order observable.
- Source positivity supplies the noncancelling weights. No phase selection or equidistribution is
  needed for \(V_n\).

## Required proof closure

- [ ] Prove the abstract positive marked-divisor visibility theorem in HTGeometry.
- [ ] Prove the exact \(K_1\)/endpoint-cross-charge identity.
- [ ] Prove \(1/2<|w(\rho_q)|<1\) for every strict-right Xi representative, using the critical
      strip and certified off-line height gap.
- [ ] Prove absolute convergence of every \(V_n\) from summability of endpoint weights and the
      uniform lower radial bound.
- [ ] Prove \(V_0=\text{weighted Ward index}/(8\pi)\).
- [ ] Prove actual-Xi exponential visibility under \(\neg\mathrm{RH}\).
- [ ] Audit whether a source-side formula for \(V_n\) exists. Do not call the route prime-accessible
      without one.
- [ ] Test novelty against Li/Voros asymptotics, minimum-phase/all-pass theory, moment problems,
      and dynamical visibility literature.
- [ ] Reject as headline if the final result is only a repackaged zero-sum equivalence.

## Current falsifier verdict

The exact degree-one bridge appears absent from searched literature and from existing corpus
statements. The phase-free tower is stronger than the prior static index because it proves
all-order, no-cancellation amplification. It does **not** yet exclude zeros. Publication
significance depends on proving the universal all-order theorem, actual Xi instantiation, and a
clear consequence beyond renaming RH.

## Stronger reinterpretation: Poisson order-space conservation

The inverse-radial tower is only one marginal of a sharper two-parameter law.  Put

\[
  a=w^{-1},\qquad b=a-1,\qquad
  d=|b|^2,\qquad \kappa=|a|^2-1.
\]

For a coherent exponential mode \(e^{bx}\), its factorially normalized derivative-order energy is
exactly

\[
 e^{-x}\frac{x^r}{r!}|b^r e^{bx}|^2
 =e^{\kappa x}\Pr\{\operatorname{Pois}(dx)=r\}.
\]

Thus a divisor defect is not merely exponentially visible.  It is conserved as a Poisson packet
in observation-order space:

- packet center: \(r=dx\);
- total exponential mass: \(e^{\kappa x}\);
- local width: \(\sqrt{dx}\);
- critical line: \(\kappa=0\);
- strict-right defect: \(\kappa>0\).

For the conjugate pair \(b,\bar b\), the exterior curvature

\[
 H_r=G_rG_{r+2}-G_{r+1}^2
\]

has no rotating phase:

\[
 H_r=m^2(b-\bar b)^2|b|^{2r}e^{2\operatorname{Re}(b)x}<0.
\]

After factorial normalization its magnitude is the same Poisson packet, and summing over every
order gives the exact signed scalar

\[
 e^{-x}\sum_{r\ge0}\frac{x^r}{r!}H_r
 =m^2(b-\bar b)^2e^{\kappa x}.
\]

For \(b=(\rho-1)^{-1}\),

\[
 d=\frac1{|\rho-1|^2},\qquad
 \kappa=(2\operatorname{Re}\rho-1)d.
\]

Consequently ridge position and growth reconstruct the zero up to conjugation:

\[
 \operatorname{Re}\rho=\frac12\left(1+\frac\kappa d\right),\qquad
 (\operatorname{Im}\rho)^2=
 \frac1d-\frac14\left(1-\frac\kappa d\right)^2.
\]

This makes the existing results shadows of one law:

- compact-open height escape sends \(d\to0\), so every fixed order misses the packet;
- complete differential-algebraic finite-jet data fixes order before the packet arrives;
- the Ward index is the static marked divisor mass;
- Cayley/Li powers read the radial exponent \(\kappa\);
- growing-order Fock channels follow the packet center \(dx\);
- exterior square removes phase while retaining \(d\) and \(\kappa\).

The headline must be this order-space conservation and reconstruction theorem, not the bounded
radial criterion.  Remaining hostile gate: establish an actual source-side Xi realization of the
coherent packet, or the theorem risks being judged a universal identity applied decoratively to
zeros.
