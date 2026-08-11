# Hasse packet reconstruction, information properness, and the atomic-refinement wall

- **ID:** ULF-PFM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `../../../../1-in-progress/rh-current-frontier-map.md` and the certified Salem Fermi
  carrier
- **Statement:** Hasse's finite-difference continuation is a source-native joint formation law:
  its Mellin-scale marginal reconstructs the full packet history through one parameter-independent
  geometric kernel, reflected packet laws have zero Jeffreys work exactly at the critical center,
  while atomizing the same packets has infinite total variation throughout the critical strip.

## Goal

Replace another receiver framework by one literal mechanism produced by the analytically continued
source.  The theorem separates four statements which earlier discussions conflated:

1. a cancellation packet can be admitted even when its atoms are not;
2. a packet history can be reconstructed from a sufficient continuous observer;
3. reflection has a strict, globally proper information cost;
4. a zero gives phase orthogonality, not equality of reflected source laws.

The last distinction fixes the RH-facing open core.  The functional equation already reflects a
zero.  What remains is an arithmetic law making that reflection compatible with the packet
formation kernel at zero information cost.  The properness theorem would then force the center.

## Gates

- [x] 0 -> 1 in-progress: literal pre-zero source law and exact hostile falsifier identified
- [x] 1 -> 2 fully-proven: dependency-closed proof below
- [x] 2 -> 3 formalized: certified core in
  `GaloisForLFunctions.HTGeometry.ConstitutiveHassePacketFormation`; umbrella build, lint, and
  axiom audit passed
- [ ] 3 -> 4 publication-ready

## 1. The finite-difference packet

For `s in C` with `Re s > 0` and `n >= 0`, put

\[
 h_n(s)=\sum_{k=0}^n(-1)^k {n\choose k}(k+1)^{-s}.
 \tag{PFM.1}
\]

Euler's integral for a reciprocal power and the binomial theorem give

\[
 h_n(s)=\frac1{\Gamma(s)}\int_0^\infty
 t^{s-1}e^{-t}(1-e^{-t})^n\,dt.
 \tag{PFM.2}
\]

Write

\[
 \eta(s)=(1-2^{1-s})\zeta(s).
\]

For real `sigma > 0`, `(PFM.2)` shows `h_n(sigma)>0`.  Summing the geometric
series in `n` gives

\[
 \sum_{n\ge0}2^{-n-1}h_n(s)
 =\frac1{\Gamma(s)}\int_0^\infty\frac{t^{s-1}}{e^t+1}\,dt
 =\eta(s).
 \tag{PFM.3}
\]

Moreover, for `s=sigma+i tau`,

\[
 |h_n(s)|\le \frac{\Gamma(\sigma)}{|\Gamma(s)|}h_n(\sigma),
 \tag{PFM.4}
\]

so `(PFM.3)` is absolutely convergent after each finite-difference row has formed.  This is the
load-bearing order of operations.

## 2. Joint packet law and exact reconstruction

For `sigma>0`, let

\[
 Z_\sigma=\Gamma(\sigma)\eta(\sigma)>0
\]

and define a probability law `Q_sigma` on `N times (0,infinity)` by

\[
 dQ_\sigma(n,t)=\frac{2^{-n-1}}{Z_\sigma}
 t^{\sigma-1}e^{-t}(1-e^{-t})^n\,dt.
 \tag{PFM.5}
\]

Its scale marginal is the positive Fermi--Mellin law

\[
 d\mu_\sigma(t)=\frac{t^{\sigma-1}}{Z_\sigma(e^t+1)}\,dt,
 \tag{PFM.6}
\]

and its depth marginal is

\[
 Q_\sigma\{n\}=\frac{2^{-n-1}h_n(\sigma)}{\eta(\sigma)}.
 \tag{PFM.7}
\]

Set

\[
 r(t)=\frac{1-e^{-t}}2.
\]

Then the conditional packet-depth law is

\[
 K(t,n)=Q_\sigma(N=n\mid T=t)=(1-r(t))r(t)^n.
 \tag{PFM.8}
\]

Crucially, `K` is independent of `sigma`.  Therefore

\[
 Q_\sigma=\mu_\sigma K
 \tag{PFM.9}
\]

for every `sigma>0`.  The scale projection is not merely an observer: it is sufficient for the
entire reflected family, and the one Markov kernel `(PFM.8)` reconstructs the full Hasse packet
history.

### Proof

Summing `(PFM.5)` in `n` uses

\[
 \sum_{n\ge0}2^{-n-1}(1-e^{-t})^n=\frac1{1+e^{-t}}.
\]

After multiplication by `e^{-t}`, this is `(e^t+1)^{-1}`, proving `(PFM.6)` and normalization.
Integrating one fixed row and using `(PFM.2)` proves `(PFM.7)`.  Dividing `(PFM.5)` by
`(PFM.6)` gives

\[
 2^{-n-1}(1+e^{-t})(1-e^{-t})^n=(1-r(t))r(t)^n,
\]

which proves `(PFM.8)`--`(PFM.9)`.

## 3. Exact phase fusion and zero orthogonality

Let `s=sigma+i tau`.  Under either `Q_sigma` or its sufficient marginal `mu_sigma`,

\[
 \mathbb E_\sigma[T^{i\tau}]
 =\frac{\Gamma(s)\eta(s)}{\Gamma(\sigma)\eta(\sigma)}.
 \tag{PFM.10}
\]

Thus every nontrivial zeta zero `rho=sigma+i tau` in the open critical strip gives an unconditional,
absolutely admitted source relation

\[
 \sum_{n\ge0}2^{-n-1}h_n(\rho)=0
 \tag{PFM.11}
\]

and an exact Hilbert-space orthogonality

\[
 \langle 1,T^{i\tau}\rangle_{L^2(\mu_\sigma)}=0.
 \tag{PFM.12}
\]

The generator of this unitary phase orbit is `log T`.  Hence its pure-state quantum Fisher
information is

\[
 \mathcal I_\sigma=4\operatorname{Var}_{\mu_\sigma}(\log T).
 \tag{PFM.13}
\]

The elementary inequality `|1-e^{ix}|<=|x|` and `(PFM.12)` imply the fourth-organ prediction

\[
 \operatorname{Var}_{\mu_\sigma}(\log T)\ge \tau^{-2},
 \qquad \mathcal I_\sigma\ge4\tau^{-2}.
 \tag{PFM.14}
\]

Indeed, after centering `X=log T`,

\[
 1=|\mathbb E(1-e^{i\tau(X-\mathbb EX)})|
 \le |\tau|\mathbb E|X-\mathbb EX|
 \le |\tau|\sqrt{\operatorname{Var}(X)}.
\]

## 4. Reflected information properness

Put

\[
 F(\sigma)=\log Z_\sigma
 =\log\int_0^\infty\frac{t^{\sigma-1}}{e^t+1}\,dt.
 \tag{PFM.15}
\]

On every compact subinterval of `(0,infinity)`, differentiation under the integral is justified by
the integrable majorants obtained by adding powers of `|log t|` at zero and exponential decay at
infinity.  Therefore

\[
 F'(\sigma)=\mathbb E_{\mu_\sigma}\log T,
 \qquad
 F''(\sigma)=\operatorname{Var}_{\mu_\sigma}(\log T)>0.
 \tag{PFM.16}
\]

For `a,b>0`, the likelihood ratio depends only on the sufficient scale:

\[
 \log\frac{dQ_a}{dQ_b}(n,t)
 =\log\frac{d\mu_a}{d\mu_b}(t)
 =(a-b)\log t-F(a)+F(b).
 \tag{PFM.17}
\]

Consequently both directed relative entropies, and hence Jeffreys work, are preserved exactly by
the scale projection:

\[
 J(Q_a,Q_b)=J(\mu_a,\mu_b)
 =(a-b)(F'(a)-F'(b)).
 \tag{PFM.18}
\]

For `0<sigma<1`, set `b=1-sigma`.  Strict convexity now gives the global selection law

\[
 \boxed{
 J(Q_\sigma,Q_{1-\sigma})=0
 \iff J(\mu_\sigma,\mu_{1-\sigma})=0
 \iff \sigma=\tfrac12.}
 \tag{PFM.19}
\]

This is genuine properness, not a local Hessian test: every off-center reflected formation pays
strict positive information work.

## 5. Atomic-refinement wall

If a packet is refined before its alternating boundary is formed, its unsigned mass is

\[
 A(\sigma)=\sum_{n\ge0}2^{-n-1}
 \sum_{k=0}^n {n\choose k}(k+1)^{-\sigma}.
 \tag{PFM.20}
\]

All terms are nonnegative, so Tonelli applies.  For fixed `k`,

\[
 \sum_{n\ge k}2^{-n-1}{n\choose k}=1,
 \tag{PFM.21}
\]

because

\[
 \sum_{n\ge k}{n\choose k}x^n=\frac{x^k}{(1-x)^{k+1}}
\]

and `x=1/2`.  Therefore

\[
 \boxed{A(\sigma)=\sum_{m\ge1}m^{-\sigma}.}
 \tag{PFM.22}
\]

It follows that

\[
 A(\sigma)<\infty\iff\sigma>1,
 \qquad
 A(\sigma)=\infty\quad(0<\sigma\le1).
 \tag{PFM.23}
\]

Thus Hasse packets are admitted throughout the critical strip, but their integer atoms are not.
Prime factorization can label those atoms, yet no continuous coefficientwise prime coframe can be
obtained by Tonelli refinement there.  The cancellation packet, not its atoms, is the primitive
source formation.

## 6. Exact conservation and the RH-facing missing law

The theorem gives one literal four-organ packet:

| organ | exact shadow |
|---|---|
| incidence / relation | binomial finite-difference row `(PFM.1)` |
| positive formation | joint law `Q_sigma` and Fermi marginal `mu_sigma` |
| analytic / divisor | zero relation and phase orthogonality `(PFM.11)`--`(PFM.12)` |
| information / quantum | sufficient reconstruction, Jeffreys properness, QFI bound |
| topology / admission | atomic refinement wall `(PFM.23)` |

The conservation identity is stronger than equality of scalar transforms:

\[
 Q_\sigma=\mu_\sigma K,
 \qquad K\text{ independent of }\sigma,
 \qquad J(Q_a,Q_b)=J(\mu_a,\mu_b).
 \tag{PFM.24}
\]

The functional equation sends a zero at `sigma+i tau` to one at `1-sigma+i tau`, so it gives
phase orthogonality in both reflected laws.  It does **not** imply that their Jeffreys work is zero.
Shared vanishing of one Fourier coefficient is strictly weaker than equality of source laws.

The next theorem is now sharply typed:

> Construct the functional-equation action on the packet source and prove that its lift through the
> common recovery kernel `K` is information-neutral (or prove an equivalent source conservation
> identity forcing `J(Q_sigma,Q_(1-sigma))=0`).

If that statement is proved before zero specialization, `(PFM.19)` forces `sigma=1/2`.  If it is
false, the exact obstruction is no longer mysterious: functional reflection changes packet
formation work even though both phase observers vanish.

## 7. Hostile checks

1. **This is not another presentation of the Salem criterion.**  The existing Salem theorem is the
   marginal formula `(PFM.10)`.  It does not contain the latent Hasse formation, the universal
   recovery kernel, the preserved Jeffreys work, or the atomic-refinement wall.
2. **Zero orthogonality does not prove RH.**  Two distinct probability laws can share a vanishing
   characteristic function value.  The exact missing premise is information-neutral reflection.
3. **Atomization cannot be used silently.**  `(PFM.23)` proves that absolute atomic refinement is
   illegal at every nontrivial zero.
4. **The packet is not prime-local.**  Its atoms are integers and only subsequently factor into
   primes.  Any prime-local route must provide an admitted packet-level map, not split the rows by
   Tonelli.
5. **Strict convexity is load-bearing.**  It follows because `log T` is not almost surely constant
   under the positive density `(PFM.6)`.

## 8. Sources and corpus boundary

- Jonathan Sondow, *Analytic continuation of Riemann's zeta function and values at negative
  integers via Euler's transformation of series*, Proc. AMS 120 (1994), 421--424,
  https://doi.org/10.1090/S0002-9939-1994-1172954-7.
- Yochay Jerby, *An approximate functional equation for the Riemann zeta function with
  exponentially decaying error*, arXiv:1910.05754.  The paper states the Hasse--Sondow row and its
  integral representation.
- Existing corpus marginal:
  `formal/GaloisForLFunctions/RHTower/SalemFermiModeIntegral.lean`.
- Existing abstract information receivers:
  `ConstitutiveGlobalFormationInformationProperness.lean` and
  `ConstitutiveObserverFibreChirality.lean`.

Corpus search found no Hasse/Sondow finite-difference source, no parameter-independent packet
recovery kernel, and no atomic-refinement wall.  This card supplies their literal source
instantiation.  No RH conclusion is claimed.

## Log

- 2026-08-11 — source identity, reconstruction kernel, information properness, quantum prediction,
  and atomic-refinement wall proved on paper; Lean gate opened.
- 2026-08-11 — finite packet formation, common-kernel reconstruction, exact atomic wall, finite
  positive formation measures, parameter recovery, and reflected Jeffreys selection certified in
  Lean.  The complex Hasse integral, eta phase identity, and QFI corollary remain paper-level source
  links and are not counted among the certified declarations.
