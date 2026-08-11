# Functional-equation split-formation lift, information isometry, and reflected-work no-go

- **ID:** ULF-PFM-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM + EXACT NO-GO
- **Source:** \`../../../../2-fully-proven/universal-law-field/packet-formation-mechanics/hasse-packet-reconstruction-information-properness-and-atomic-refinement-wall.md\`
- **Statement:** A reversible action on a sufficient observer has a canonical stochastic lift through
  every common recovery kernel; the lift preserves all relative-entropy information. Theta
  reflection supplies the functional-equation action for a completed Hasse packet, but reflected
  Jeffreys work is strictly positive off center, so information neutrality is an isometry law, not
  the missing RH selection law.

## Goal

Construct the functional-equation action requested by \`ULF-PFM-1\` without fitting an arbitrary
transport to two endpoint measures. Determine exactly what survives after lifting through the
common Hasse recovery kernel and whether that conservation can force the critical center.

The load-bearing distinction is

\[
 \text{information-neutral action}
 \quad\ne\quad
 \text{zero information separation of its endpoints}.
\]

The first means that the action loses no distinguishability. The second means that two laws are
equal. Conflating them would turn a reversible symmetry into a false RH proof.

## Gates

- [x] 0 -> 1 in-progress: typed action, literal theta source, and exact counterprediction identified
- [x] 1 -> 2 fully-proven: dependency-closed measure-kernel proof and hostile audit
- [ ] 2 -> 3 formalized: exact survivor in \`ConstitutiveFunctionalEquationPacketLift.lean\`
- [ ] 3 -> 4 publication-ready

## 1. The mechanism: split formation rather than a route object

Let \`X\` be an observer space, \`H\` a latent-history space, and let

\[
 K:X\rightsquigarrow H
\]

be a Markov kernel independent of the source parameter. The associated **split formation** sends a
law \(\mu\) on \(X\) to the joint law

\[
 \mathsf E_K(\mu)(dx,dh)=\mu(dx)K(x,dh).
 \tag{FEL.1}
\]

Let \(\pi:X\times H\to X\) be projection. Then

\[
 \pi_*\mathsf E_K(\mu)=\mu.
 \tag{FEL.2}
\]

This is the common recovery structure already present in the Hasse packet, now isolated as a
general formation mechanism.

### Theorem 1.1 — split-formation information law

For any probability laws \(\mu,\nu\) on \(X\), extended relative entropy satisfies

\[
 D(\mathsf E_K\mu\Vert\mathsf E_K\nu)=D(\mu\Vert\nu).
 \tag{FEL.3}
\]

Consequently every symmetric sum, in particular Jeffreys work, is also preserved.

### Proof

Data processing through the formation kernel gives

\[
 D(\mathsf E_K\mu\Vert\mathsf E_K\nu)\le D(\mu\Vert\nu).
\]

Data processing through \(\pi\), followed by \((\mathrm{FEL}.2)\), gives the reverse inequality:

\[
 D(\mu\Vert\nu)
 =D(\pi_*\mathsf E_K\mu\Vert\pi_*\mathsf E_K\nu)
 \le D(\mathsf E_K\mu\Vert\mathsf E_K\nu).
\]

Both inequalities hold with value \(+\infty\), so no absolute-continuity or finite-information
qualification is needed. This proves \((\mathrm{FEL}.3)\).

## 2. Canonical action lift

Let \(A:X\to X\) be a measurable bijection with measurable inverse. Define the lifted Markov action

\[
 \widehat A_K((x,h),dy\,dk)
 =\delta_{Ax}(dy)K(Ax,dk).
 \tag{FEL.4}
\]

It first applies the observer action, then regenerates the latent history from the same common
recovery law. The old latent coordinate is deliberately discarded: \(K\), not an arbitrary
coupling of old and new histories, is the source-certified recovery mechanism.

### Theorem 2.1 — formation-action naturality

For every observer law \(\mu\),

\[
 (\widehat A_K)_*\mathsf E_K(\mu)=\mathsf E_K(A_*\mu).
 \tag{FEL.5}
\]

For composable measurable bijections \(A,B\),

\[
 (\widehat B_K)_*(\widehat A_K)_*\mathsf E_K(\mu)
 =(\widehat{B\circ A}_K)_*\mathsf E_K(\mu).
 \tag{FEL.6}
\]

Thus action composition is strict on the image of the formation map, although the stochastic lift
need not be an inverse on arbitrary off-image joint states. If \(A^2=\mathrm{id}\), then

\[
 (\widehat A_K)_*^2\mathsf E_K(\mu)=\mathsf E_K(\mu).
 \tag{FEL.7}
\]

### Proof

For bounded measurable \(f\) on \(X\times H\), the left side of \((\mathrm{FEL}.5)\) evaluates to

\[
 \int_X\mu(dx)\int_HK(x,dh)
 \int_HK(Ax,dk)f(Ax,k).
\]

The middle integral of \(K(x,dh)\) equals one, leaving

\[
 \int_X\mu(dx)\int_HK(Ax,dk)f(Ax,k),
\]

which is exactly \(\mathsf E_K(A_*\mu)(f)\). Applying this identity twice proves
\((\mathrm{FEL}.6)\); \((\mathrm{FEL}.7)\) follows when \(A\) is involutive.

### Corollary 2.2 — information-neutral lift

For all \(\mu,\nu\),

\[
 D((\widehat A_K)_*\mathsf E_K\mu
   \Vert(\widehat A_K)_*\mathsf E_K\nu)
 =D(\mathsf E_K\mu\Vert\mathsf E_K\nu).
 \tag{FEL.8}
\]

### Proof

By \((\mathrm{FEL}.5)\) and \((\mathrm{FEL}.3)\), the left side is
\(D(A_*\mu\Vert A_*\nu)\). Data processing under \(A\) and its inverse gives
\(D(A_*\mu\Vert A_*\nu)=D(\mu\Vert\nu)\). Apply \((\mathrm{FEL}.3)\) again.

Equations \((\mathrm{FEL}.2)\), \((\mathrm{FEL}.3)\), \((\mathrm{FEL}.5)\),
\((\mathrm{FEL}.6)\), and \((\mathrm{FEL}.8)\) are the **split-formation action laws**. They are
independent of zeta, theta, or any proof route.

## 3. Canonical two-sheet reflection closure

The preceding laws lift an action once the observer action exists. They do not assume that a
one-chart formation family is closed under reflection. There is an exact minimal closure when it is
not.

Let \(R:X\to X\) be a measurable involution and let \(\beta\) be a finite nonzero positive source measure
equivalent to \(R_*\beta\). Use the canonical invariant dominating measure
\(\omega=\beta+R_*\beta\), and write the two densities with respect to \(\omega\) as \(b\) and
\(b^R\). Define the Hellinger midpoint and modular half-cocycle by

\[
 d\lambda=\sqrt{b\,b^R}\,d\omega,
 \qquad
 \chi=\frac12\log\frac b{b^R}.
 \tag{FEL.D1}
\]

The same objects result from every equivalent dominating measure. Since
\(\sqrt{bb^R}\le(b+b^R)/2\), \(\lambda\) is finite. They satisfy

\[
 R_*\lambda=\lambda,\qquad
 \chi\circ R=-\chi,\qquad
 d\beta=e^\chi d\lambda,\qquad
 d(R_*\beta)=e^{-\chi}d\lambda.
 \tag{FEL.D2}
\]

Let \(T:X\to\mathbb R\) be reflection-odd, \(T\circ R=-T\). For every tilt \(a\) and sheet
\(\varepsilon\in\{+1,-1\}\) for which the following normalizer is finite and nonzero, define

\[
 dP_{a,\varepsilon}
 =Z_{a,\varepsilon}^{-1}
   e^{aT+\varepsilon\chi}\,d\lambda.
 \tag{FEL.D3}
\]

### Theorem 3.1 — modular formation double

Reflection acts by

\[
 \boxed{R_*P_{a,\varepsilon}=P_{-a,-\varepsilon}.}
 \tag{FEL.D4}
\]

The original source formation is the \(+\) sheet. Its reflected law lies on the \(-\) sheet. More
precisely, whenever both normalizers are finite, same-sheet closure means

\[
 R_*P_{a,+}=P_{-a,+}.
 \tag{FEL.D4a}
\]

This can hold for one admitted tilt only if

\[
 \chi=0\quad\text{almost everywhere},
 \tag{FEL.D5}
\]

equivalently \(\beta=R_*\beta\); conversely this condition makes the two sheets identical and gives
same-sheet closure for every admitted tilt.

### Proof

The geometric-mean density in \((\mathrm{FEL.D1})\) is fixed by exchange of \(b\) and \(b^R\), while
their log ratio changes sign. Therefore

\[
 Z_{a,\varepsilon}=Z_{-a,-\varepsilon}.
\]

Changing variables by \(R\) in \((\mathrm{FEL.D3})\) proves \((\mathrm{FEL.D4})\). If
\((\mathrm{FEL.D4a})\) holds, then \((\mathrm{FEL.D4})\) identifies
\(P_{-a,-}=P_{-a,+}\). Their Radon--Nikodym ratio is a normalizing constant times
\(e^{2\chi}\), so \(e^{2\chi}\) is constant; normalization and
\(\chi\circ R=-\chi\) force that constant to be one. Hence \(\chi=0\). The converse is immediate.

### Corollary 3.2 — recovery lift of the modular double

Put

\[
 Q_{a,\varepsilon}=\mathsf E_K(P_{a,\varepsilon}).
\]

Then the canonical lift \(\widehat R_K\) satisfies

\[
 (\widehat R_K)_*Q_{a,\varepsilon}=Q_{-a,-\varepsilon}
 \tag{FEL.D6}
\]

and preserves every pairwise KL divergence and Jeffreys work. This is the coordinate-free
reflection action required by any packet realization of a functional equation. It is
information-neutral on the doubled formation space.

### Literal Hasse modular cocycle

For the raw Hasse/Fermi marginal in logarithmic scale \(y=\log t\), the untilted base is

\[
 b_H(y)=\frac{e^{y/2}}{e^{e^y}+1}.
\]

Its canonical reflection data are

\[
 s_H(y)
 =\frac1{\sqrt{(e^{e^y}+1)(e^{e^{-y}}+1)}},
 \tag{FEL.D7}
\]

\[
 \chi_H(y)
 =\frac y2+\frac12\log(e^{e^{-y}}+1)
             -\frac12\log(e^{e^y}+1).
 \tag{FEL.D8}
\]

Thus

\[
 b_H=s_He^{\chi_H},\qquad
 b_H(-y)=s_He^{-\chi_H},
 \tag{FEL.D9}
\]

and \(\chi_H\) is odd. It is nonzero because

\[
 \chi_H'(0)=\frac12-\frac e{e+1}\ne0.
 \tag{FEL.D10}
\]

Writing \(a=\sigma-1/2\), the original Fermi packet is \(Q_{a,+}\), while its canonical reflected
lift is

\[
 Q_{a,+}\longmapsto Q_{-a,-}.
 \tag{FEL.D11}
\]

It is **not** the same-sheet packet \(Q_{-a,+}\) used in the Jeffreys properness theorem. The
missing sheet flip \(\chi_H\mapsto-\chi_H\) is the exact formation datum that the one-parameter
description erased.

This is stronger than saying “the Fermi base is not even.” It constructs the smallest
reflection-closed formation, identifies its hidden coordinate, and proves that common recovery
lifts reflection without information loss once that coordinate is retained.

## 4. Literal theta functional-equation action

Let

\[
 \Phi(x)=\operatorname{thetaCuspFullSource}(x).
\]

The certified theta source is strictly positive, even, Schwartz, and satisfies

\[
 \int_{\mathbb R}e^{-iwx}\Phi(x)\,dx=\Xi_C(w),
 \qquad |\operatorname{Im}w|<1.
 \tag{FEL.9}
\]

For \(|a|<1\), define

\[
 Z(a)=\int_{\mathbb R}e^{ax}\Phi(x)\,dx=\Xi_C(ia)>0,
 \qquad
 \nu_a(dx)=Z(a)^{-1}e^{ax}\Phi(x)\,dx.
 \tag{FEL.10}
\]

Because \(\Phi\) is even,

\[
 Z(-a)=Z(a).
 \tag{FEL.11}
\]

Let \(R(x)=-x\). Direct change of variables gives

\[
 R_*\nu_a=\nu_{-a}.
 \tag{FEL.12}
\]

This is not an arbitrary endpoint transport. Under the corpus convention

\[
 \Xi_C(w)=\xi(1/2+iw),
\]

the tilt \(a\) represents the real coordinate \(\sigma=1/2-a\); \(a\mapsto-a\) is exactly
\(\sigma\mapsto1-\sigma\), and \((\mathrm{FEL}.12)\) is the positive-source action generating the
functional equation.

## 5. Theta-carrier packet with Hasse recovery

For \(x\in\mathbb R\) and \(n\in\mathbb N\), put

\[
 K_H(x,n)=K(e^x,n)
 =(1-r(e^x))r(e^x)^n,
 \qquad r(t)=\frac{1-e^{-t}}2.
 \tag{FEL.13}
\]

Since \(e^x>0\), \(K_H(x,\cdot)\) is a probability law. Define the theta-carrier packet with Hasse
recovery

\[
 \widehat Q_a(dx,n)=\nu_a(dx)K_H(x,n).
 \tag{FEL.14}
\]

Its functional-equation lift is

\[
 \widehat R((x,n),dy,m)
 =\delta_{-x}(dy)K_H(-x,m).
 \tag{FEL.15}
\]

### Theorem 5.1 — functional-equation packet lift

For every \(|a|<1\),

\[
 \widehat R_*\widehat Q_a=\widehat Q_{-a},
 \qquad
 \widehat R_*^2\widehat Q_a=\widehat Q_a.
 \tag{FEL.16}
\]

For every \(a,b\in(-1,1)\),

\[
 D(\widehat Q_a\Vert\widehat Q_b)=D(\nu_a\Vert\nu_b),
 \tag{FEL.17}
\]

and

\[
 D(\widehat R_*\widehat Q_a\Vert\widehat R_*\widehat Q_b)
 =D(\widehat Q_a\Vert\widehat Q_b).
 \tag{FEL.18}
\]

Thus the functional equation has a canonical lift through the common Hasse recovery kernel and the
lift is exactly information-neutral.

### Proof

Apply Theorems 1.1 and 2.1 to \(X=\mathbb R\), \(H=\mathbb N\), \(K=K_H\), and \(A=R\); use
\((\mathrm{FEL}.12)\).

## 6. Exact reflected-work classification

Put \(F(a)=\log Z(a)\). Exponential decay of \(\Phi\) justifies differentiation under the integral
for \(|a|<1\), giving

\[
 F'(a)=\mathbb E_{\nu_a}X,
 \qquad
 F''(a)=\operatorname{Var}_{\nu_a}(X)>0.
 \tag{FEL.19}
\]

Evenness of \(Z\) makes \(F\) even. The reflected likelihood ratio is

\[
 \log\frac{d\nu_a}{d\nu_{-a}}(x)=2ax.
 \tag{FEL.20}
\]

Hence

\[
 D(\nu_a\Vert\nu_{-a})=2aF'(a)
 =D(\nu_{-a}\Vert\nu_a),
 \tag{FEL.21}
\]

and, by common-kernel sufficiency,

\[
 \boxed{
 J(\widehat Q_a,\widehat Q_{-a})=4aF'(a).}
 \tag{FEL.22}
\]

Since \(F\) is even and strictly convex, \(F'(0)=0\) and \(F'\) is strictly increasing. Therefore

\[
 \boxed{
 J(\widehat Q_a,\widehat Q_{-a})=0
 \iff a=0.}
 \tag{FEL.23}
\]

But \((\mathrm{FEL}.21)\) also gives

\[
 \boxed{
 D(\widehat Q_a\Vert\widehat Q_{-a})
 -D(\widehat Q_{-a}\Vert\widehat Q_a)=0
 \quad\text{for every }a.}
 \tag{FEL.24}
\]

The functional equation kills directed KL **chirality** everywhere while retaining strictly
positive symmetric information **work** off center.

This is the decisive classification:

| statement | truth value |
|---|---|
| functional equation acts on completed positive formation | true |
| action lifts through common Hasse recovery kernel | true |
| lift loses no relative-entropy information | true |
| lift makes directed reflected costs equal | true for every tilt |
| lift makes reflected laws equal | false off center |
| lift makes reflected Jeffreys work zero | false off center |

## 7. Why the raw Fermi packet has no reciprocal functional-equation action

Write the raw Hasse/Fermi marginal in logarithmic scale \(y=\log t\). With
\(a=\sigma-1/2\), its density is an exponential tilt of

\[
 b_H(y)=\frac{e^{y/2}}{e^{e^y}+1}:
 \qquad
 p_a(y)=Z_a^{-1}e^{ay}b_H(y).
 \tag{FEL.25}
\]

Suppose logarithmic inversion \(y\mapsto-y\) carried \(p_a\) to \(p_{-a}\). Equality of the two
continuous densities would imply

\[
 \frac{b_H(-y)}{Z_a}=\frac{b_H(y)}{Z_{-a}}
 \quad\text{for all }y.
 \tag{FEL.26}
\]

At \(y=0\), \((\mathrm{FEL}.26)\) gives \(Z_a=Z_{-a}\), hence it forces
\(b_H(-y)=b_H(y)\). This is false: logarithmic differentiation gives

\[
 (\log b_H)'(0)=\frac12-\frac e{e+1}\ne0,
 \tag{FEL.27}
\]

whereas every differentiable even positive function has zero logarithmic derivative at the origin.

Therefore the zeta functional equation is not reciprocal inversion of the original Fermi packet.
The theta completion is load-bearing. An arbitrary quantile transport between \(\mu_\sigma\) and
\(\mu_{1-\sigma}\) would exist, but it would be endpoint-fitted and would not represent the
functional equation.

## 8. No-go closure and new open core

- **Exact killing theorem/mechanism:** information neutrality in the correct sense is KL isometry.
  The functional-equation lift satisfies it for every tilt. It cannot imply zero Jeffreys work.
- **Strongest positive survivor:** five split-formation action laws \((\mathrm{FEL}.2)\),
  \((\mathrm{FEL}.3)\), \((\mathrm{FEL}.5)\), \((\mathrm{FEL}.6)\), \((\mathrm{FEL}.8)\), concrete
  modular formation double \((\mathrm{FEL.D1})\)--\((\mathrm{FEL.D11})\), theta/Hasse lift
  \((\mathrm{FEL}.16)\)--\((\mathrm{FEL}.18)\), and exact work classification
  \((\mathrm{FEL}.22)\)--\((\mathrm{FEL}.24)\).
- **New insight:** functional equation is a reversible transport symmetry. RH selection needs a
  second mechanism that **annihilates reflected work**, not another mechanism preserving
  information or making directed costs symmetric.
- **Status:** dependency-closed paper proof; hostile audit passed; Lean formalization pending.

The corrected RH-facing target is now:

> Construct a pre-zero source law whose functional-equation lift is not merely information
> preserving, but whose zero relation forces symmetric work \(4aF'(a)\) to vanish.

By \((\mathrm{FEL}.23)\) that law would select \(a=0\), equivalently
\(\operatorname{Re}\rho=1/2\). Functional equation alone does not provide it.

## 9. Relation to the universal-law field

This theorem supplies a mechanism rather than another route object:

1. **formation:** extend an observer law by a common recovery kernel;
2. **reduction:** project back to the sufficient observer;
3. **intervention:** act reversibly on observer laws;
4. **closure:** double a chiral formation by its Hellinger midpoint and modular half-cocycle;
5. **generation:** lift the action by regenerating latent history;
6. **conservation:** relative entropy is unchanged by both formation and reversible action;
7. **dissipation gate:** selection can only come from an additional law that kills, rather than
   transports, conserved symmetric work.

This grammar applies to every corpus organ with a parameter-independent recovery/disintegration,
not only Hasse packets. It also provides a falsifiable formation test: if route-specific latent data
cannot be reconstructed by one common kernel, then that observer is not sufficient and lost
conditional KL is a genuine vertical formation defect.

## 10. Literature and corpus boundary

- Chentsov invariance and its exponential-family form establish the general information-geometric
  role of sufficient statistics; see James G. Dowty, *Chentsov's theorem for exponential
  families*, arXiv:1701.08895.
- Equality in relative-entropy data processing and recovery is established parent mathematics.
  The split proof above is the elementary two-sided data-processing specialization.
- KL divergence in a natural exponential family is the Bregman divergence of its log partition;
  \((\mathrm{FEL}.21)\)--\((\mathrm{FEL}.22)\) are its reflection specialization.
- Classical even positive theta kernel for Xi supplies \((\mathrm{FEL}.9)\)--\((\mathrm{FEL}.12)\);
  corpus certificates are \`ThetaCuspSchwartzFourierXi.lean\`,
  \`ThetaCuspFourierLaplace.lean\`, and \`HedenmalmThetaSourceUnconditional.lean\`.
- Existing \`ConstitutiveObserverFibreChirality.lean\` proves that involutive reversal kills KL
  chirality. \((\mathrm{FEL}.21)\)--\((\mathrm{FEL}.24)\) expose the sharp limitation: completed Xi
  family has zero chirality for all reflected pairs, so no strict chirality chronology can be
  instantiated here.

New-to-corpus content is exact common-recovery lift of functional equation and proof that
information isometry and zero work are different laws. Hellinger midpoint and likelihood-ratio
cocycles are classical ingredients; their role here is to expose the missing formation sheet in the
literal Hasse packet. No external novelty claim is needed for universal-law programme.

## Hostile checks

1. **Is lift deterministic?** No. It is canonical as a Markov lift because it regenerates latent
   coordinate from certified common conditional law. Demanding deterministic coupling would add
   information absent from packet theorem.
2. **Is lift an involution on every joint state?** No. It is an involution on formed-law image. This
   is exact scope of \((\mathrm{FEL}.7)\).
3. **Does zero chirality select center?** No. \((\mathrm{FEL}.24)\) is explicit countertheorem.
4. **Does construction prove RH?** No. It replaces vague missing \`information-neutral\` premise by
   stronger and correctly typed missing \`zero symmetric work\` premise.
5. **Could one act directly on raw Fermi scale?** Not by canonical reciprocal reflection;
   \((\mathrm{FEL}.25)\)--\((\mathrm{FEL}.27)\) prove obstruction.
6. **Is attaching \(K_H\) to theta marginal fitted?** \(K_H\) is fixed before tilt and before zero
   specialization, and is same certified Hasse recovery kernel. What is new is a theta-carrier
   packet with Hasse recovery, not a claim that raw Hasse joint law equals theta joint law.
7. **Does theta completion equal the Hellinger-balanced Hasse base?** No such equality is claimed or
   known. The modular double is intrinsic to raw Hasse formation; theta is a separate, literal
   functional-equation realization with zero modular cocycle.

## Log

- 2026-08-11 — constructed split-formation action laws and canonical Hellinger/modular formation
  double; instantiated theta functional-equation reflection; found exact
  zero-chirality/positive-work no-go; Stage-1 proof written.
- 2026-08-11 — hostile audit repaired same-sheet normalization typing and verified the literal Hasse
  cocycle, theta sign convention, and reflected-work classification; promoted to Stage 2.
