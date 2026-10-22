# Two-prime quantile-flow fingerprint of the theta source

- **ID:** TQ2P
- **Stage:** 1-in-progress
- **Type:** THEOREM (nonlinear rigidity in Lean; infinitesimal formula on paper)
- **Source:** literal completed-theta density and its prime-translation quantile flows
- **Claim:** The two interval maps induced by multiplication by 2 and 3 determine any normalized positive source density up to translation; fixing its median removes that freedom. Their first variations likewise detect every non-translation source perturbation.

## Why this is a different interface

The exact theta determinant carrier has Xi occurrence but no proved real-spectrum law. The WS2 signed saddle has real spectrum but its natural correction to the theta carrier is non-trace-class and nonselfadjoint. A spectral transfer must retain complete source information rather than finitely many moments, local modes, or a prescribed zero list. The pair of prime quantile flows is a candidate *source coordinate* for such a transfer: just two maps, but each is a full function on the probability interval.

For a strictly positive continuous integrable density $k$, write $M=\int k$, $F(x)=M^{-1}\int_{-\infty}^x k$, $Q=F^{-1}$, and

\[
\Psi_n(t)=F(Q(t)+\log n),\qquad 0<t<1,\quad n\ge1.
\tag{1}
\]

The corpus proves the actual-theta semigroup law $\Psi_{mn}=\Psi_m\circ\Psi_n$ and strict displacement $\Psi_n(t)>t$ for $n>1$ in [HedenmalmThetaPrimeTranslationQuantileFlow.lean](../../../../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrimeTranslationQuantileFlow.lean).

## Nonlinear rigidity theorem

Let $F_1,F_2$ be CDFs of two positive continuous integrable densities, with inverse quantiles $Q_1,Q_2$. If their maps (1) agree for $n=2$ and $n=3$ at every interior $t$, then for some $c\in\mathbb R$,

\[
F_2(x+c)=F_1(x)\quad\text{for every }x\in\mathbb R.
\tag{2}
\]

If the two CDFs have the same median coordinate, especially if both densities are even about zero, then $c=0$. Thus the two prime maps determine the normalized density; knowing the total mass determines the unnormalized density.

**Proof.** Set $H=Q_2\circ F_1$. Equality of the $n$th maps at $t=F_1(x)$ gives $H(x+\log n)=H(x)+\log n$ for $n=2,3$. Hence $H(x)-x$ is continuous with periods $\log2$ and $\log3$. Their ratio is irrational, since $2^a=3^b$ is impossible for positive integers $a,b$. The subgroup they generate is dense, so $H(x)-x=c$. Applying $F_2$ gives (2). If $F_1(0)=F_2(0)$, then $H(0)=0$ and $c=0$. The corpus already proves the needed irrational-log/dense-period lemma in [TwoDilationDivisorMetric.lean](../../../../../../formal/GaloisForLFunctions/RHTower/TwoDilationDivisorMetric.lean).

The median-anchored conclusion $F_1=F_2$ for arbitrary positive-density sources is now proved in [ThetaTwoPrimeQuantileFlowRigidity.lean](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaTwoPrimeQuantileFlowRigidity.lean), reusing that dense-period lemma. Its leaf module passed `lake build --old GaloisForLFunctions.RHTower.ThetaTwoPrimeQuantileFlowRigidity`; no umbrella build was run. The translation-ambiguous version and infinitesimal formula remain paper proofs.

## Infinitesimal rigidity theorem

Suppose $F_\varepsilon$ is a differentiable family of such CDFs, $F_0=F$, and $g(x)=\partial_\varepsilon F_\varepsilon(x)|_0$. Put $\rho=F'=k/M$ and $v=g/\rho$. Differentiation of (1) at fixed $t=F(x)$ gives the exact response

\[
\left.\partial_\varepsilon\Psi_{n,\varepsilon}(F(x))\right|_0
=\rho(x+\log n)\bigl(v(x+\log n)-v(x)\bigr).
\tag{3}
\]

If both responses for 2 and 3 vanish everywhere and $v$ is continuous, then the two-period theorem forces $v$ to be constant. Thus $g=c\rho$, precisely an infinitesimal translation of the source. For an even normalized family, $g$ is odd and $\rho$ even, so $c=0$ and $g=0$. The two-map response has trivial kernel on even source deformations.

The sign of $c$ depends on whether the perturbation is written $F(x+\varepsilon c)$ or $F(x-\varepsilon c)$; the kernel classification is unaffected.

## Literal theta arithmetic in the same coordinates

For the theta atom $a_m(x)$ used in [ThetaCuspFinitePrimeFluxSplit.lean](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspFinitePrimeFluxSplit.lean), its proved shift identity is

\[
a_m(x+\log n)=\sqrt n\,a_{nm}(x).
\tag{4}
\]

Consequently, wherever the source atom sum and derivative may be exchanged,

\[
\Psi_n'(F(x))=\frac{k(x+\log n)}{k(x)}
=\sqrt n\,\frac{\sum_{m\ge1}a_{nm}(x)}{\sum_{r\ge1}a_r(x)}.
\tag{5}
\]

For $x\ge0$ every displayed atom is positive, so the final ratio is the literal source-weighted probability that an integer label is divisible by $n$. This is an arithmetic realization of the two source maps, not merely an abstract conjugacy. The strict log-concavity already proved for the actual theta source makes $x\mapsto\Psi_n'(F(x))/\sqrt n$ strictly decreasing for $n>1$, since its logarithmic derivative is $(\log k)'(x+\log n)-(\log k)'(x)<0$.

## Proof-chain implication and open attack

Equations (2)–(3) solve one fidelity question: a proposed source-to-selfadjoint transfer preserving both complete prime flows cannot replace the normalized theta density by a distinct even one, and its linearization cannot silently erase an even deformation. They do **not** orient the theta determinant spectrum.

The first spectral conjecture fails: the ordinary unitary Koopman action of these flows on $L^2(0,1)$ is conjugate, by the quantile map with its Jacobian, to translation on $L^2(\mathbb R)$. Translation by $\log 2$ has no nonzero $L^2$ eigenvector, so an Xi eigenmode cannot simply be assigned a unit-modulus prime character there. This matches the corpus's [continuous-spectrum prime coupling](../../../../../../formal/GaloisForLFunctions/RHTower/FinitePrimeCommutingDilationNoPointSpectrum.lean); the actual-theta [finite-stationary-carrier theorem](../../../../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaDivisorFiniteStationarityNoGo.lean) shows that every nonzero finite measure on the interval fails stationarity under a genuine prime flow, while the surviving invariant Haar measure has infinite mass. The pivot is a **source boundary-cocycle** problem: construct a rigged or quotient action that retains the pinned-mean port and whose defect-fibre phase is controlled by a source energy. The existing [prime-pinned normal form](../../../../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrimeTranslationQuantileFlow.lean) shows the boundary port moves rather than vanishes, so that anomaly must be included in any proof.

The exact energy target is already formalized in [FrankensteinThetaPrimeTranslationPluckerLanding.lean](../../../../../../formal/GaloisForLFunctions/RHTower/FrankensteinThetaPrimeTranslationPluckerLanding.lean): at an Xi divisor, the two reflected normalized prime-translation energies are reciprocal, and simultaneous contractivity at one retained prime is equivalent to critical-line placement. The new two-flow theorem supplies **fidelity of the source coordinate**, not either contractivity inequality. The hard conjecture is a source-derived, boundary-aware positive realization of both reflected evaluations; simply using the ordinary translation unitary cannot provide it.

The period-rigidity ingredient is classical and already in the corpus; the joint quantile-flow/source-fidelity application has not been checked against external literature. No RH proof or falsification follows from this card, and the frontier map remains read-only.
