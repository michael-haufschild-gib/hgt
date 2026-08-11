# Mixed-radix gauge critical-normal geometry conjecture

- **ID:** `ulf-mrfg-critical-normal-gauge`
- **Stage:** 1 — frozen conjecture and hostile proof gate
- **Status:** `[CONJECTURE] [MECHANISM-FIRST] [SOURCE-LEVEL] [NOT RH]`
- **Parent corpus:**
  - `mfree-telescoping-tower.md`;
  - `prime-valuation-dyadic-fermion-normal-cone-law.md`;
  - `dyadic-squarefree-euler-fock-source-factorization.md`.

## Public sentence

Changing the digit system used to resolve prime multiplicities changes the finite arithmetic
coordinates but not the singular statistical geometry seen at the critical boundary.

## 1. Frozen conjecture

Fix integers `m_j >= 2` and define place values

\[
 P_0=1,\qquad P_{j+1}=m_jP_j.
 \tag{MRG.1}
\]

For `0<q<1`, let `K` have geometric law

\[
 \Pr_q(K=k)=(1-q)q^k,\qquad k\in\mathbb N_0.
 \tag{MRG.2}
\]

Write the unique mixed-radix expansion

\[
 K=\sum_{j\ge0}P_jD_j,\qquad 0\le D_j<m_j.
 \tag{MRG.3}
\]

The conjecture has four clauses.

1. **Exact source formation.** The digits are independent with
   \[
   \Pr_q(D_j=a)=
   \frac{q^{P_ja}}{S_{m_j}(q^{P_j})},\qquad
   S_m(z)=1+z+\cdots+z^{m-1},
   \tag{MRG.4}
   \]
   and their product reconstructs `(MRG.2)`.
2. **Hellinger conservation.** For every pair `q,r`, geometric Hellinger affinity equals the
   product of all digit affinities.
3. **Critical gauge invariance.** At the prime source
   \[
   q_{p,c}=p^{-(1-2c)},\qquad c_x=u/\log x,
   \tag{MRG.5}
   \]
   the complete two-parameter Hellinger kernel has the same limit for every fixed mixed-radix
   system:
   \[
   K(u,v)=\exp\!\left[-\frac12\int_0^1
      \frac{(e^{ut}-e^{vt})^2}{t}\,dt\right].
   \tag{MRG.6}
   \]
   The zeroth digit alone has this limit; the product of every digit `j>=1` tends to one.
4. **Information and divisor prediction.** The exact Fisher/Hellinger curvature decomposes as
   an orthogonal digit sum. Only `j=0` has divergent all-prime critical trace. Correspondingly,
   the first arithmetic factor
   \[
   \zeta(s)/\zeta(m_0s)
   \tag{MRG.7}
   \]
   carries the complete strict-right zeta divisor, while all positive-depth mixed-radix factors
   are units there.

The claimed geometry is the limiting kernel `(MRG.6)` and its canonical Gaussian/Fock completion,
not the finite digit presentation. Mixed-radix changes are proposed gauges because they induce the
same limiting kernel and the same singular/regular decomposition.

## 2. Why this is not the existing dyadic theorem

The dyadic parent proves `(MRG.6)` only for `m_j=2`. The `m`-free tower proves exact arithmetic
telescoping for constant and mixed radices, and proves divisor localization, but contains no
Hellinger experiment, Fisher decomposition, or presentation-independent normal-cone theorem.

The new residue is therefore precise:

\[
 \boxed{\text{mixed-radix arithmetic gauges have one critical statistical normal geometry}.}
 \tag{MRG.8}
\]

## 3. Closest external parents

- independent digits of a geometric random variable in an arbitrary numeral system;
- Kakutani product-measure/Hellinger theory;
- prime-number-theorem partial summation and mod-Poisson prime-factor models;
- Gaussian kernels and symmetric Fock exponential vectors.

These parents make each ingredient plausible. The exact mixed-radix prime-source conservation and
radix-independent critical kernel were not located in the literature audit. Priority is not a
premise of the conjecture.

## 4. Hostile falsifiers fixed before proof search

1. **Radices depending on `x`.** Not claimed. Uniformity can fail if the presentation changes with
   the aperture.
2. **Le Cam equivalence.** Not claimed. Equality of limiting pairwise Hellinger kernels does not by
   itself prove vanishing deficiency distance.
3. **Noncritical scalings.** Not claimed. Higher digits need not be invisible away from the
   `1/log x` normal scale.
4. **Finite calibration.** Not invariant. Digit Fisher contributions and finite Hellinger products
   depend on the chosen radices.
5. **Radix one.** Excluded. `m_j>=2` is load-bearing for place-value growth and tail summability.
6. **RH selection.** Not claimed. Divisor localization detects hypothetical strict-right zeros but
   does not eliminate them.

## 5. Proof obligations

1. Prove the mixed-radix probability pushforward and exact Hellinger product.
2. Establish the uniform first-digit expansion
   \[
   \log H_{p,0}(u/\log x,v/\log x)
   =-\frac{(e^{ut_p}-e^{vt_p})^2}{2p}+O(p^{-2}).
   \tag{MRG.9}
   \]
3. Prove a summable bound for every `j>=1`, uniformly over the arbitrary fixed radix sequence.
4. Use PNT partial summation to obtain `(MRG.6)`.
5. Prove exact variance/Fisher conservation and isolate the unique divergent digit.
6. Audit whether `(MRG.7)` is genuinely predicted or merely imported from the existing telescope.

## 6. First open core

`[OPEN CORE]` Close obligation 3 without any boundedness assumption on the sequence `(m_j)` beyond
`m_j>=2`. The intended bound must depend only on the place values `P_j>=2^j`, not on the alphabet
sizes themselves.

## Log

- 2026-08-11 — fixed-radix generalization was killed as an alleged missing source theorem by the
  existing mixed-radix `m`-free telescope. The killing mechanism forced the stronger
  presentation-invariance conjecture `(MRG.8)`.
