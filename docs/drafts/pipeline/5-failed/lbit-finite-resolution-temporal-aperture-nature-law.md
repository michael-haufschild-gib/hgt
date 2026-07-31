# L-bit finite-resolution temporal aperture is not a Nature law

- **ID:** `lbit-finite-resolution-temporal-aperture-nature-law`
- **Stage:** 5-failed
- **Labels:** `[FALSIFIED AS STATED] [REDISCOVERED AFTER REPAIR] [BRIDGE]`
- **Date:** 2026-07-31

## Failed conjecture

For an absolutely summable exponentially quasi-local l-bit field, define
the local flip gap
\[
 g_x(\sigma)=E(\sigma^x)-E(\sigma)
\]
and let \(N_x^{\mathrm{vis}}(T,\varepsilon)\) count conditional gaps separated
by more than \(2\varepsilon/T\). The proposed law claimed that a
logarithmic influence radius and the time--bandwidth interval jointly bound
this visible temporal dimension, with matching examples.

The intended interpretation was that exact recurrence dimension is
infinite or exponential, but only a causal finite-resolution aperture is
observable.

## Exact killing mechanisms

### Orientation counterexample

The statement omitted the value of the flipped bit. For
\[
 E(\sigma)=J_{\{x\}}\chi_{\{x\}}(\sigma),\qquad J_{\{x\}}\ne0,
\]
the radius-zero environment excluding \(x\) has one pattern, but
\[
 g_x(\sigma)\in\{-2J_{\{x\}},2J_{\{x\}}\}.
\]
Thus the claimed pattern bound is false unless one fixes
\(\sigma(x)=0\), fixes the opposite orientation, or identifies
\(\omega\sim-\omega\).

### Visibility was stipulated

The separation \(2\varepsilon/T\) was inserted as a definition rather than
derived from an experimental model. For pure phase signals on
\([0,T]\),
\[
 \sup_{0\le t\le T}|e^{it\omega}-e^{it\omega'}|
 =
 2\sin\!\left(
   \frac{\min\{T|\omega-\omega'|,\pi\}}2
 \right).
\]
Disjoint sup-norm error balls of radius \(\varepsilon<1\) require the exact
threshold
\[
 |\omega-\omega'|>
 \frac{2\arcsin\varepsilon}{T},
\]
not \(2\varepsilon/T\). State-dependent spectral weights, preparation,
probe restrictions and noise are also absent.

### Repaired theorem is routine

Fix the positive transition orientation
\[
 G_x^+=\{g_x(\sigma):\sigma(x)=0\},
\]
and local masses
\[
 M_x=\sum_{S\ni x}|J_S|,\qquad
 K_x=\sum_{S\ni x}2^{\operatorname{diam}S}|J_S|.
\]
For an integer-valued metric, configurations agreeing on the closed
radius-\(R\) ball satisfy
\[
 |g_x(\sigma)-g_x(\sigma')|
 \le
 4\sum_{\substack{S\ni x\\\operatorname{diam}S>R}}|J_S|
 \le 2K_x2^{-R}.
\]
Consequently the \(\delta\)-packing number obeys the standard cylinder and
interval bounds
\[
 P_\delta(G_x^+)
 \le
 \min\left\{
   2^{|B_R(x)\setminus\{x\}|},
   \max\left(1,\left\lceil\frac{4M_x}{\delta}\right\rceil\right)
 \right\}
\]
whenever the tail is at most \(\delta\).

The first term is cylinder approximation; the second is interval packing.
Nandkishore--Gopalakrishnan--Huse already derive the l-bit spectral tree
and its linewidth-limited truncation. Kim--Chandran--Abanin already prove
the logarithmic influence cone. The repaired inequality is an elementary
metric-entropy specialization, not new physical knowledge.

## Strongest positive survivor

`[BRIDGE]` Exact arithmetic rank and finite-resolution spectral capacity
are inequivalent. A quasi-local l-bit field may have maximal rational rank
in every finite environment while every fixed-resolution conditional gap
packet has finite metric capacity controlled by the local interaction
tail.

This is important manuscript scope control but does not change the
scientific frontier. It is not promoted for Lean formalization because the
claimed Nature-level insight is rediscovered metric packing and the
operational notion remains incomplete.

## Stronger replacement

The surviving non-cosmetic question is a minimax operational theorem that
includes:

- state-dependent spectral weights;
- allowed state preparation and probes;
- measurement noise and total observation time;
- a microscopically derived localized Hamiltonian;
- matching upper and lower capacities.

No exact conjecture satisfying all five requirements is presently frozen.

`NO POSITIVE SCIENTIFIC SALVAGE FOUND` beyond the bridge above.

## Representation lesson

Exact rational dimension is an arithmetic invariant. Experimental
visibility is a metric-statistical decision problem. Replacing the former
by an ad hoc frequency packing does not create a new law; the observation
model must be part of the primitive.

