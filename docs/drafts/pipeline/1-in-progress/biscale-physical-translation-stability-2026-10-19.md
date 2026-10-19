# Uniform physical-translation stability from fifth and sixth sieve arrays

- **ID:** biscale-physical-translation-stability-2026-10-19
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; paper argument under audit, uncounted
- **Source:** [100-contribution programme](biscale-100-contribution-programme-2026-10-18.md); [existing zero-support obstruction](biscale-mixed-stability-strata-1810.md); [existing BVI stability proposal](bvi-mixed-valuation-moment-stability-audit-2026-10-18.md).
- **Statement:** Fifth and sixth translated arrays should control actual sieve signals modulo one physical translation with a uniform sixth-root modulus, across all vanishing coordinates and mixed two-adic support.

## Goal and prior ownership

The amplitude-threshold mechanism and the need for an ambient translation quotient were already proposed in the linked cards. They are prior ideas and earn no new credit. Fixed-valuation stability, prime-family noise estimates and their sharpness are already formalized. The proposed advance here is a complete uniform theorem for every real divisor-sieve profile, using only fifth and sixth arrays, with an explicit signal bound and an optimal exponent in the actual translation metric. The two predecessor cards remain read-only during this work.

For cutoff N≥1, let `f=sieveSeq N c`, `g=sieveSeq N e`, with completely arbitrary real divisor weights c,e. Let `M_m(c;h)` be the existing normalized translated moment. Put `T_N=∑_{q=1}^N φ(q)`. Proposed exact theorem: for `0≤δ≤1`, if

`|M_m(c;h)−M_m(e;h)|≤δ^6` for m=5,6 and every lag vector h,

then there is one natural shift t such that

`|g(n)−f(n+t)|≤5*T_N*δ` for every natural n.

Equivalently, raw error ε≤1 permits a uniform `5*T_N*ε^(1/6)` bound. No upper amplitude bound, support gap, fixed nonzero stratum, affine data or quadratic/cubic observations are assumed. The comparison uses literal translated signals; the translated full signal may leave the order-constant coordinate family. For each fixed N≥10, no uniform estimate with exponent α>1/6 can hold near zero. Constants in N are not claimed optimal.

## Gates

- [x] Existing obstruction, threshold proposal, fixed-block stability and exact recovery audited before new code.
- [ ] Complete corpus and primary-source comparison of the stronger physical-translation conclusion.
- [ ] Re-audit the dependency-closed paper argument below, including normalizations and zero cases.
- [ ] Formalize the exact surviving theorem; named original-source checks, full public axiom audit, wiring and lint evidence.
- [ ] Decide substantive contribution separately from proof correctness. Programme remains 4/100.

## Paper argument

Write `a_q=Y_N(c,q)`, `b_q=Y_N(e,q)` for admitted q. The following proof uses the existing Fourier identity, actual Ramanujan inverse and canonical translation. Their general mechanisms are prior tools.

**Raw arrays control spectral products.** The m-dimensional moment Fourier transform at a resonant frequency tuple is `P^m∏_i a_(ord r_i)`, where P=N!. Dividing the transform difference by P^m averages P^m terms, each a unit-modulus character times a raw array difference. Thus every resonant product difference has absolute value at most δ^6. This normalization introduces no P-dependent loss.

The existing exact-order frequency constructions give four families of inequalities:

1. `|a_q^6−b_q^6|≤δ^6` for every admitted q, by the diagonal sixth readout.
2. `|a_q^5−b_q^5|≤δ^6` for every odd admitted q. At a frequency r of order q, the tuple `(r,r,−2r,r,−r)` is resonant and every entry has order q.
3. `|(a_q*a_r)^3−(b_q*b_r)^3|≤δ^6` when q,r have equal two-adic valuation, by the existing valuation-six tuple.
4. `|a_q^3*a_r^2−b_q^3*b_r^2|≤δ^6` when `v₂(q)<v₂(r)`, by the existing mixed quintic tuple. Both orders are admitted at the same original cutoff; the old construction's auxiliary cutoff is rewritten to N as in `lower_coordinate_of_fifth`.

These are measured polynomial readouts, not assumed abstract phase information. For x,y≥0, `|x−y|^6≤|x^6−y^6|`, since expanding `(y+(x−y))^6` when x≥y gives nonnegative remaining terms. Consequently

`||a_q|−|b_q||≤δ` for every q.

**Select significant coordinates.** First suppose 0<δ≤1. Let `S={q∈[1,N]:|a_q|>2δ}`. For q∈S, `|b_q|>δ`, so both signs are defined. Write `ρ_q=sign(b_q)/sign(a_q)∈{−1,1}`. If S is nonempty, choose r∈S with greatest two-adic valuation K.

For q∈S with `v₂(q)<K`, a negative ρ_q makes the two fifth-order products in item 4 have opposite signs. Their difference then has magnitude at least `|a_q|^3*|a_r|^2>(2δ)^5>δ^6`, contradiction. Hence every significant coordinate below K keeps its sign.

For q∈S with `v₂(q)=K`, if `ρ_q≠ρ_r`, the two sixth-order products in item 3 have opposite signs. Their difference has magnitude at least `|a_q*a_r|^3>(2δ)^6>δ^6`, contradiction. Thus the significant coordinates at K have one common relative sign. If K=0, item 2 forbids a negative sign individually, because `|a_q|^5>(2δ)^5>δ^6`.

**Realize one actual shift.** Truncate the source coordinate profile to S, and realize it by the existing Ramanujan inverse as weights c*, with signal `f*=sieveSeq N c*`. If S is empty, set c*=0 and take t=0. Otherwise its greatest active valuation is K. If the significant signs all agree, take t=0 and w=c*. In the remaining case K>0, take the already proved canonical shift of c*, and let w be its companion weights. Set `h=sieveSeq N w`. The coordinates of w flip exactly valuation K and keep lower valuations fixed; `h(n)=f*(n+t)` for every n. In every case the coordinates of w are zero outside S and have the signs of b on S, with magnitudes |a_q| there. Therefore

`|b_q−Y_N(w,q)|≤δ` on S, and `|b_q−Y_N(w,q)|=|b_q|≤3δ` outside S.

The discarded coordinates of f−f* have magnitude at most 2δ. No claim that translating the discarded part stays inside the coordinate family is needed: its uniform signal bound holds at every natural argument, including n+t.

**Convert to literal signal error.** The exact Ramanujan expansion is

`sieveSeq N c(n)=∑_{q=1}^N Y_N(c,q)*c_q(n)`, with `|c_q(n)|≤φ(q)`.

The first identity follows either from the existing inverse or from `d*1_(d|n)=∑_{q|d}c_q(n)` and finite summation. The second follows from the definition as a sum of φ(q) unit complex characters. Hence uniformly bounded coordinate error η gives signal error at most T_N η. Apply this to g−h and f−f*, then translate the second bound:

`|g(n)−f(n+t)|≤3*T_N*δ+2*T_N*δ=5*T_N*δ`.

If δ=0, the existing exact fifth/sixth recovery theorem and canonical-companion translation give equality for one actual shift. This closes the empty-support and exact-data boundary too. All input weights may have arbitrary tails beyond N; these are invisible to both the literal signal and the observations.

**Optimal exponent in the physical translation quotient.** Fix N≥10 and use the existing order-six/order-ten pair `f=u_6+u_10`, `g=u_6−u_10`. Both are actual sieve signals with absolute value at most six. Every fifth translated moment vanishes, and their zero-lag sixth moments differ by 960. Scaling both weights by λ>0 gives signals bounded by 6λ, with fifth arrays still identical and every sixth array difference at most `2*6^6*λ^6`.

For any natural shift t, translation preserves the sixth moment. The elementary inequality `|x^6−y^6|≤6*max(|x|,|y|)^5*|x−y|` therefore implies

`960*λ^6≤6*(6λ)^5*sup_n |λg(n)−λf(n+t)|`.

Thus every physical translation has uniform error at least `960/(6*6^5)*λ`. A putative uniform exponent α>1/6 would instead bound that error by `C*(2*6^6)^α*λ^(6α)` for arbitrarily small λ, contradiction. This lower bound applies to all actual translations, including ones that leave the order-constant family; a coefficient common-sign metric alone would not prove it.

## Corpus and primary-source audit

Initial scoped deep request `/tmp/bsu-100-mixed-stability-frontier.json` completed with 74,297 inventoried files. All returned candidate/source statement entries, prose/passage inventories and generated proposals were inspected. It recovers exact valuation recovery and prime-family raw stability. Some indexed signatures stop at `let`, so those are not complete applicability reviews. The proposed transfer from the new arithmetic-edge rank theorem to mixed-support stability is invalid and rejected.

The whole-corpus query `mixed valuation stability`, excluding new ArithmeticEdge modules, completed with 74,299 inventoried files (`/tmp/bsu-100-mixed-stability-global-search.json`). All 20 candidate and 20 source statement entries and ten prose entries were inspected. Most declaration results concerned nonarchimedean valuations rather than observation stability; the generated valuation-order ingredient chain is irrelevant. The useful prose hits recover precisely the two existing proposals and prior fixed-block stability. This weak declaration retrieval cannot establish absence of an existing quantitative theorem. Semantic coverage is unmeasured and compiler freshness incomplete. A separate coordinate-to-signal norm search has completed and awaits inventory review.

Primary-source comparison remains open. The existing rational/cyclic reconstruction baseline and general polynomial orbit-recovery literature must be distinguished from this proposed uniform physical-translation estimate on arbitrary real divisor profiles. No external novelty claim is made yet.

## No-go closure

This candidate is a proposed positive replacement for the already identified discontinuity of the support-dependent coefficient quotient. If the global bound fails, preserve the exact obstruction and audit the strongest corrected physical-translation statement. No new negative theorem or positive survivor is counted before complete proof and formalization.

## Log

- 2026-10-19 — Created after package 4 and explicit prior-work searches. The prior threshold idea is acknowledged. A proposed complete proof uses only fifth/sixth data, a 2δ significance threshold and the actual canonical translation of the truncated source. No new Lean file has been created. Count remains 4/100.
