# Chronological geometry: RH interface assessment

- **ID:** CTF-RH-RECOVERY
- **Stage:** 1-in-progress
- **Type:** Research assessment; no new RH architecture established
- **Source:** [Working knowledge](../../cross-disciplinary/universal-laws-and-structures/excursion-intervention-geometry.md), [RH frontier](../../rh-current-frontier-map.md), CTF candidate row.
- **Question:** Can literal chronological repair yield a new proof of an arithmetic recovery estimate?

## What the existing theorem supplies

The actual normalization quotient and radial flow give

\[
h(t)=\frac1t-\frac1{e^t-1},\qquad
\mathcal Mh(s)=-\Gamma(s)\zeta(s),\quad 0<\Re s<1.
\]

`RecoverySurgeryFlow.recoverySurgeryResponseKernel_mellin` and
`recoverySurgeryResponseKernel_zeroMultiplicity` establish the literal response
and zero multiplicities. The names before the dot here identify the source module;
declarations are in `GaloisForLFunctions.HTGeometry.ChronologicalTensor`.

The completed surgery theorem preserves this response while changing actual
recovery-moment representability. It disproves an implication from the listed
geometric properties to that positivity, not the possibility of any geometric RH
proof. Nor does it show that every invariant involving recovery costs is useless.
The radial generator has eigenvalues 1,2,3,…; Mellin zeros are not its eigenvalues.

## Exact literature collision

For \(f(t)=e^{-t}\), our \(-h\) is exactly the classical Müntz transform
\(Pf(t)=\sum_{n\ge1}f(nt)-t^{-1}\int_0^\infty f\).
This is a specialization of Báez-Duarte's [2005 paper, (1.1), (2.10)](https://arxiv.org/pdf/math/0505453).
Thus the scalar zeta mechanism is classical, even though the geometric derivation
and surgery theorem may have separate novelty.

More explicitly, put \(\rho(x)=\{1/x\}\), \(\chi=1_{(0,1]}\), and
\[
(SF)(x)=\int_0^\infty F(x/y)e^{-y}\,dy.
\]
Then \(S\chi=e^{-x}\), \(S\rho=h\), and \(S\) commutes with dilations.
For the second identity, integrate the fractional part:
\(\int\{y/x\}e^{-y}dy=x^{-1}-\sum_{n\ge1}e^{-nx}\).
Mellin transformation gives \(\mathcal M(SF)(s)=\Gamma(s+1)\mathcal MF(s)\)
on an initial dense class and then in the L² Plancherel sense.

On \(s=1/2+i\tau\), the squared multiplier is
\[
|\Gamma(3/2+i\tau)|^2
=\frac{\pi(\tau^2+1/4)}{\cosh(\pi\tau)}.
\]
It is positive but tends to zero. Consequently S is injective on L² and has no
bounded inverse on its range: unit Mellin packets escaping to large |τ| have
smoothed norm tending to zero. This does **not** decide whether a restricted
arithmetic approximation family admits a stronger comparison. These are classical
analytic deductions, not new Lean results or a new impossibility theorem for RH.

## A precise endpoint and its actual missing input

A sufficient target is a fixed finite C and finite coefficient arrays with
\[
|a_{k,N}|\le C,\qquad
\left\|e^{-t}+\sum_{k=1}^N a_{k,N}h(kt)\right\|_{L^2(0,\infty)}\longrightarrow0.
\tag{R}
\]
This is a classical endpoint, not a new conjecture. Darses–Hillion's
[2021 paper, Theorems 3.1 and 3.3, Example 4(1)](https://www.numdam.org/item/10.5802/cml.71.pdf)
uses exactly the exponential family \(E\{X/(kt)\}=h(kt)\), X exponential of mean
one. Its more general coefficient-tail condition is automatic under this uniform
bound. With a sign change of coefficients their target is (R).

Why the bound matters can also be checked directly. Write its residual as
\(E_N(t)=b_N/t+r_N(t)\), where
\(b_N=\sum_{k\le N}a_{k,N}/k\) and
\(r_N(t)=e^{-t}-\sum_{k\le N}a_{k,N}/(e^{kt}-1)\).
For t≥1, \(|r_N(t)|\le B e^{-t}\) uniformly, with
\(B=1+C/(1-e^{-1})^2\).
For each fixed M≥1,
\[
|b_N|\le\sqrt M\bigl(\|E_N\|_2+B e^{-M}/\sqrt2\bigr).
\]
First taking N→∞ and then M→∞ gives b_N→0. If ζ had a zero z with
1/2<Re z<1, the Mellin transform of every E_N at z would be Γ(z)≠0.
On (0,M), Cauchy–Schwarz makes this integral tend to zero. On (M,∞), the b_N/t
term tends to zero and the remaining integral is uniformly exponentially small
as M→∞. Contradiction. Reflection and the usual zero-free exterior complete RH.
This explains the known endpoint without assuming convergence at a moving height.

**Missing geometric theorem:** construct such coefficients from literal repair
operations and prove both estimates in (R). A novel proof could use this classical
endpoint; merely restating (R) cannot count as a novel architecture. No construction
or comparison achieving this is currently available here.

The existing polynomial iteration
\(p_{n+1}=p_n+(c^2-p_n^2)/2\) recovers c with uniform error ≤2/(n+2), but it acts
on polynomial observations of a compact probe domain. It is not an arithmetic
dilation combination of h. No proved map transfers its error or coefficient
control to (R). Likewise, graded Hankel positivity, finite repairs, and trace
identities alone do not supply that transfer.

## Status

The serious next target is this construction/comparison, or a different explicit
source law retaining information before the trace. No novel architecture, new RH
proof, or new Lean theorem is claimed by this assessment. No route is retired.
No numerical experiments or Lean builds were needed for this literature and
mathematical comparison; the previous geometric audit remains unchanged.
