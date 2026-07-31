# Meyer Poisson nuclear polarization pair

- **ID:** `deninger-meyer-poisson-nuclear-polarization-pair`
- **Stage:** 2-fully-proven
- **Type:** PUBLISHED SOURCE THEOREM / TOPOLOGICAL GUARDRAIL
- **Label:** `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR`
- **Parent:** `deninger-arithmetic-calderon-paugam-hardy-comparison`
- **Statement:** Meyer's source trace uses one exact and one
  almost-complemented Poisson polarization; convolution makes their
  defects nuclear, so no exact continuous Hardy projector on the
  nuclear source is required or presently justified.

## Ambient Poisson pair

Use Meyer's notation
\[
 \mathcal W=\mathcal S_>\oplus\mathcal S_<.
\]
The two closed source embeddings are
\[
\begin{aligned}
 \iota_+f&=(Zf,\mathcal JZ\mathcal Ff),\\
 \iota_-g&=(g,g).
\end{aligned}                                                    \tag{1}
\]
For a cutoff \(M_\phi\), Meyer constructs continuous maps
\[
 \pi_+:\mathcal W\to H_+,\qquad
 \pi_-:\mathcal W\to H_-                                       \tag{2}
\]
with
\[
 \pi_-\iota_-=1.                                                \tag{3}
\]
Hence
\[
 P_-=\iota_-\pi_-
\]
is an actual continuous projection onto \(\iota_-H_-\).

For the positive/Poisson leg,
\[
 \pi_+\iota_+
 =
 M_\phi+\mathcal F M_\phi\mathcal F
 =
 1+M_\phi-\mathcal F\mathcal J
                 M_\phi\mathcal J\mathcal F                   \tag{4}
\]
in Meyer's conventions.  Meyer states that he does not know whether
\(\iota_+H_+\) admits an honest continuous section in \(\mathcal W\).
Thus
\[
 P_+=\iota_+\pi_+
\]
must not be silently treated as an idempotent.

## Nuclear replacement

`[PROVED: MEYER] [DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR]`

For every admissible convolution test packet \(F\),
\[
 \lambda(F)(P_--P_+)                                          \tag{5}
\]
is nuclear on \(\mathcal W\), and
\[
 \lambda(F)(1-\pi_+\iota_+)                                   \tag{6}
\]
is nuclear on \(H_+\).  The same assertions hold uniformly for
bounded sets of test packets.

Meyer's hereditary nuclear trace theorem then computes the virtual
source character from `(5)` and `(6)` without complementing
\(\iota_+H_+\).  The result is the complete prime-plus-real Weil
distribution.

## Arithmetic interpretation

Equations `(1)`--`(6)` are the analytic model of a global Calderón
polarization **relation**, not a pair of strict nuclear projectors.
The correct arithmetic construction has three levels:

1. exact complementary Hardy projectors on every finite local
   Calderón packet;
2. a closed global source relation whose cutoff representatives are
   idempotent only modulo the nuclear trace ideal;
3. exact orthogonal Hardy projectors on the completed positive Hodge
   Hilbert space.

Level 2 suffices for Green/cup trace comparison because nuclear trace
is hereditary and cyclic.  Level 3 is required for Hodge positivity
and skew-adjointness.  It must be constructed from source Dirichlet
energy, not assumed on Meyer's Fréchet quotient.

## Hostile audit

- Closed range of \(\iota_+\) does not imply complemented range.
- \(P_+\) is not an idempotent in the proved source theorem.
- Calling `(5)` a difference of exact projectors would strengthen
  Meyer without proof.
- An exact projector may exist after Hodge Hilbert completion; that is
  a separate arithmetic theorem.
- Nuclear almost-complementation gives traceability, not positivity.
- No zeta zero, RH premise, CCM object, or numerical computation
  enters.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277, the almost-sections corollary and
  summable-character proposition.
- `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION`.
- `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

## Log

- 2026-07-27 — Replaced an unjustified strict source Hardy projector
  by Meyer's exact analytic structure: closed Poisson embeddings and
  an almost-projector whose convolution defects are nuclear.
