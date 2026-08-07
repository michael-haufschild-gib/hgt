# Route E static all-prime antiscale-frame dichotomy

- **ID:** `ROUTE-E-STATIC-ANTISCALE-FRAME-DICHOTOMY-001`
- **Stage:** 2-fully-proven
- **Type:** `[EXHAUSTIVE PRODUCER-CLASS NO-GO]` / `[POSITIVE ROUTE CONSTRAINT]`
- **Scientific status:** `[PAPER-PROVED] [INTERNAL COLLISION-AUDITED] [EXTERNAL AUDIT OMITTED BY INSTRUCTION]`
- **Parent:** `../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no

## Purpose

Finite antiscale character frames are coercive on bounded frequency windows but contain only
harmonic mass.  A natural attempted repair is to replace the harmonic coefficient by one fixed
all-prime diagonal weight.  This card classifies **every** nonnegative fixed weight: summable
weights lose coercivity by simultaneous prime-phase recurrence, while nonsummable weights fail to
define the quadratic form already at zero frequency.

This closes the static diagonal all-prime producer class.  It does not close Route E: moving
boundary weights and genuinely off-diagonal cross-prime forms remain outside the theorem.

## Exact theorem

Let ℙ be the set of primes, let \(\omega_p\ge0\), and define

\[
 \mathcal F_\omega(t)
 =\sum_{p\in\mathbb P}{\omega_p\over p}
   \left|1+e^{it\log p}\right|^2.                       \tag{1}
\]

The series in `(1)` is understood only when its nonnegative terms are summable.

Exactly one of the following two cases holds.

### Case S: finite static mass

If

\[
 \sum_p {\omega_p\over p}<\infty,                        \tag{2}
\]

then `(1)` converges for every real \(t\), and for every \(\delta>0\) and \(T\in\mathbb R\)
there exists \(t>T\) such that

\[
 \boxed{\mathcal F_\omega(t)<\delta.}                    \tag{3}
\]

Consequently \(\liminf_{t\to+\infty}\mathcal F_\omega(t)=0\); no positive uniform frame lower
bound exists.

### Case D: divergent static mass

If `(2)` fails, then the frame is not summable at zero frequency, because

\[
 \mathcal F_\omega(0)=4\sum_p{\omega_p\over p}.          \tag{4}
\]

Hence no fixed nonnegative diagonal weight makes `(1)` both finite at every frequency and
uniformly coercive.

## Proof

The pointwise ceiling

\[
 \left|1+e^{it\log p}\right|^2\le4                     \tag{5}
\]

shows that `(2)` implies summability of `(1)` for every \(t\).

Fix \(\delta>0\) and \(T\).  By `(2)`, choose a finite prime set \(P\) such that

\[
 \sum_{p\notin P}4{\omega_p\over p}<\delta/2.            \tag{6}
\]

Put \(W_P=\sum_{p\in P}\omega_p/p\).  Choose \(\varepsilon>0\) with

\[
 \varepsilon^2W_P<\delta/2.                              \tag{7}
\]

Unique factorization makes \(\{\log p:p\in P\}\) linearly independent over \(\mathbb Q\).
Kronecker recurrence therefore supplies arbitrarily large \(t\), in particular one with
\(t>T\), for which simultaneously

\[
 \left|e^{it\log p}-e^{i\pi}\right|<\varepsilon
 \qquad(p\in P).                                         \tag{8}
\]

Since \(e^{i\pi}=-1\), equations `(7)`--`(8)` give

\[
 \sum_{p\in P}{\omega_p\over p}|1+e^{it\log p}|^2
 <\varepsilon^2W_P<\delta/2.                             \tag{9}
\]

The tail is below \(\delta/2\) by `(5)`--`(6)`, proving `(3)`.

At \(t=0\), each character is one, so every term in `(1)` equals \(4\omega_p/p\).  Multiplication
by the nonzero scalar four preserves and reflects summability, proving `(4)` and Case D.  The two
cases exhaust all weights by excluded middle.

## Hostile audit

1. This is not a finite-prime statement: the tail is controlled before simultaneous recurrence,
   so `(3)` concerns the complete all-prime series.
2. Increasing fixed weights cannot repair the frame.  It eventually enters Case D and destroys
   zero-frequency finiteness.
3. The theorem does not apply to weights depending on physical aperture \(x\), frequency \(t\),
   or another prime, nor to off-diagonal kernels.
4. It proves no Möbius bound and makes no RH claim.
5. `OPEN-SOURCE-001` remains open.

## Positive survivor

Any viable all-prime Route E quadratic producer must violate static diagonality in at least one
load-bearing way:

- use a moving nonsummable weight whose cutoff is tied to the physical Gibbs boundary and whose
  renormalization retains source mass; or
- use a genuinely off-diagonal cross-prime/cross-leaf kernel.

Combined with the parity-coarse determinant law, mere nonproductness is still insufficient.  The
survivor must act transversely to \(D_{\rm np}\) and produce \(D_{\rm anti}\) or same-parity
variation at physical-power strength.

## Formalization target

Formalize the all-prime summable case, zero-frequency summability equivalence, and final
no-fixed-weight theorem using `KroneckerApproxRecurrence`, `linearIndependent_log_primes`, and the
existing antiscale character definitions.  No analytic or RH hypothesis is permitted.
