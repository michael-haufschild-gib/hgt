# Finite theta Euler stages have a zero port and a growing-order pole port

- **ID:** theta-euler-two-port-jet-pole-renormalization
- **Stage:** 3-formalized
- **Type:** exact two-endpoint Mellin order and renormalization-price theorem
- **Routes:** STC, CSB, U, MPLF, RHist; source-side comparison with EDQ
- **Status:** [PROVED HERE ON PAPER] [LEAN: `GaloisForLFunctions.RHTower.ThetaEulerTwoPortJetPole`, see `theta-euler-two-port-jet-pole-renormalization-formalized.md`] [NOT AN RH PROOF]
- **Dependencies:** the Gaussian atom Mellin formula and finite-prime smooth-number source in [theta-euler-critical-boundary-mass-escape.md](theta-euler-critical-boundary-mass-escape.md), plus the corpus's completed theta transform and endpoint charges. No numerical computation is used.

## Exact two-port law

Let `P` be a finite set of primes, `r=|P|`, and `S_P=∑_(n≥1, all prime factors of n in P)φ_(πn²)` the literal finite Euler theta source. Put `L_P(w)=∫_ℝ exp(wx)S_P(x)dx`. For `Re w>−1/2`, the atom Mellin identity and finite Euler product give

`L_P(w)=G(w) Z_P(w+1/2)`,

`G(w)=(w−1/2)Γ(w/2+5/4)π^(−w/2−1/4)`,

`Z_P(s)=∏_(p∈P)(1−p^(−s))^(−1)`.                      (1)

The **right critical port** has a simple zero:

`L_P(1/2)=0`,

`L_P'(1/2)=(1/2)Z_P(1)`,

`[∏_(p∈P)(1−1/p)] L_P'(1/2)=1/2`.                     (2)

The **left reflected port** has a pole of exact order `r` when `P≠∅`:

`lim_(s↓0) s^r L_P(−1/2+s)=−1/∏_(p∈P)log p`.          (3)

For `P=∅`, (3) reads `L_∅(−1/2)=−1`. The completed source `k` instead has an even entire Mellin transform with

`L_k(1/2)=L_k(−1/2)=1/2`.                              (4)

Thus completion changes a finite-stage **zero plus growing-order pole** into two finite positive boundary charges. The factor in (2) extracts the completed charge from the first right-port jet; an ordinary finite-stage integral at that port remains zero.

## Proof and exact renormalizer price

For one Gaussian atom, `∫exp(wx)φ_(πn²)(x)dx=G(w)n^(−w−1/2)`. Its absolute integral is summable over the `P`-smooth monoid whenever `Re(w+1/2)>0`, so termwise integration yields (1). Since `G(w)=(w−1/2)A(w)` with `A(1/2)=Γ(3/2)π^(−1/2)=1/2`, differentiation gives (2). At the opposite endpoint `G(−1/2)=−Γ(1)=−1`, while for each `p∈P`,

`lim_(s↓0)(1−p^(−s))/s=log p>0`.

Multiplying these `r` factors proves (3), including exact pole order. Equation (4) is the already formalized completed theta endpoint law and evenness.

There is an immediate **divisor-price corollary**. Suppose a meromorphic scalar `R_P(w)` is chosen so `R_P(w)L_P(w)` extends holomorphically and nonzero at both `w=±1/2`. Then `R_P` must have a pole of order exactly one at `+1/2` and a zero of order exactly `r` at `−1/2`. This follows by adding local zero/pole orders in (2)--(3). The required left order grows without bound along any exhaustion of the primes. A regular nonvanishing scalar normalization cannot carry both finite ports to the completed pair (4); any scalar repair must be singular and increasingly high-order.

## Relation to the hard obstacle

The [all-sieve seed-projector theorem](theta-all-sieve-seed-projector-translation-cone.md) shows that positivity of every finite-prime-deleted flux recovers a regular translation measure, and that ordinary mass plus **both** reflected critical charges rigidifies that measure. Formulae (2)--(3) show why this regular-measure mechanism cannot simply be applied to the literal finite Euler chronology: one port is identically zero, the other has growing pole order, while reflection and two finite charges appear only after singular completion. The first right-port derivative carries a normalized half-charge, but a scalar jet value by itself supplies no complex-phase orientation or bound at moving spectral height. A successful transport must control the full complex family across this two-port singularity, preserving the actual Euler coefficients. These order laws do not exclude any Xi zero; they are formalized in Lean (see the certificate); literature novelty of the combined interpretation remains open.

## Log
- 2026-09-27 — (1)–(4), the divisor-price corollary and unbounded left order formalized unconditionally; moved to 3-formalized.
