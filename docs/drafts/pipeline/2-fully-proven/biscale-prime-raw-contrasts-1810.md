# Actual lag measurements from prime-selective differences

- **ID:** biscale-prime-raw-contrasts-1810
- **Stage:** 2-fully-proven
- **Type:** BRIDGE; exact symbolic construction, not yet formalized
- **Parent:** [field programme](../1-in-progress/biscale-field-development-1810.md), items 5–6

## Concrete protocol

Fix the actual `primeFamilyWeight N a`. Its finite mode set consists of odd primes `p` with `2p≤N`; let its size be `M`. The literal signal is

`f(n)=parityFactor(n) Σp a_p R_p(n mod p)`,

where `R_p(x)=p·1_(x=0)−1`. For each mode `p`, use CRT to choose a natural lag `t_p` satisfying

`t_p≡0 (mod 2)`, `t_p≡1 (mod p)`, `t_p≡0 (mod q)` for every other mode `q`.

All moduli are pairwise coprime. The inverse of their product CRT equivalence gives this lag explicitly; no coefficient or nonvanishing assumption is used.

For a six-tuple of lags `t`, form the signed difference of **64 individual sixth translated moments**

`D(t)=Σ_(b∈{0,1}⁶) (−1)^(Σb_i) M₆(b₁t₁,…,b₆t₆)`.

For each ordered mode pair `(p,q)`, take `t=(t_p,t_p,2t_p,t_q,t_q,2t_q)`. Then

`D(t)=p²q²(a_pa_q)³` if `p≠q`,

`D(t)=p⁵a_p⁶` if `p=q`.

Thus at most `64M²` raw lag measurements recover the entire normalized sixth Fourier readout matrix. The count is independent of the factorial period. Repeated measurements can be shared, but this bound does not rely on that optimization.

The diagonal entries give `|a_p|`. If all are zero, the coefficient vector is zero. Otherwise choose one nonzero diagonal at `r`, set the recovered `a_r` positive, and obtain every other `a_p` from the real cube root of `(a_ra_p)³` divided by `a_r`. The only ambiguity is the actual common sign. Zero support is discovered, not assumed.

An exact adaptive version first measures all `M` diagonals, then the `M−1` anchor pairs. It uses at most `128M−64` raw observations for `M≥1`, and zero for `M=0`. Stability below is for the fixed full-matrix protocol; no adaptive-noise guarantee is asserted yet.

## Dependency-closed proof

Multilinearity of the period average gives

`D(t)=mean_n ∏_(i=1)^6 (f(n)−f(n+t_i))`.

Since each `t_p` is even, parity is unchanged by either `t_p` or `2t_p`. Every mode except `p` cancels in its difference. The surviving row difference is

`f(n)−f(n+t_p)=parityFactor(n) a_p p (1_(n≡0 mod p)−1_(n≡−1 mod p))`.

The difference at `2t_p` replaces `−1` by `−2`. In a product of six differences parity has sixth power one.

For an odd prime, `0,−1,−2` are distinct. Consequently

`(1_(x=0)−1_(x=−1))²(1_(x=0)−1_(x=−2))=1_(x=0)`.

The three differences belonging to mode `p` therefore contribute `a_p³ p³ 1_(n≡0 mod p)`. For distinct `p,q`, their product has mean `a_p³a_q³ p³q³/(pq)=p²q²(a_pa_q)³`, by the existing exact CRT period-average theorem. When `p=q`, the product contributes `a_p⁶p⁶1_(n≡0 mod p)` and its mean is `p⁵a_p⁶`. The factorial period is a multiple of every required modulus, so these are identities for literal observations.

## Noise and necessary measurement count

If two raw observation arrays differ by at most `η` in supremum norm, each contrast differs by at most `64η`. Both normalizing denominators above are at least `81`, so each recovered normalized readout differs by at most `64η/81`. The full `M×M` readout discrepancy has Frobenius norm at most `64Mη/81`. Applying the separately proved symbolic Gram stability estimate gives

`minε ‖a−εb‖₆ ≤ 2^(3/4)(64Mη/81)^(1/6)`.

The stronger mass/coordinate-weighted estimates transfer by the same substitution. This compares exact source vectors whose observations are close; an estimator can use any admissible vector fitting noisy data and the triangle inequality for its observation residual.

Any fixed collection of `m` raw moments that recovers all vectors up to common sign must have `m≥M`. On the positive orthant the common-sign quotient is trivial, and the observation map is continuous. If `m<M`, composing an injective such map with the standard inclusion `ℝ^m→ℝ^M` contradicts invariance of domain: its image would have to be open while lying in a proper linear subspace. This lower bound covers fixed protocols. No lower bound for unrestricted adaptive decision rules is claimed.

## Audit and gates

- Existing exact source ingredients: `sieveSeq_primeFamilyWeight`, `period_average_crt`, and the common-sign sixth recovery theorem. The new work is the specific raw contrast and its amplification bound.
- Corpus query `prime selective shift finite difference sixth raw moment recovery` returned the full Fourier readouts and small-family moment identities, without this raw protocol among returned statements. Snapshot coverage does not establish global absence.
- Standard CRT, finite differences and rank-one reconstruction are prior mechanisms. [Bendory–Edidin–Kreymer](https://arxiv.org/abs/2103.01551) studies linear measurements of higher spectra; its count does not itself certify this literal-lag protocol. No originality claim is made for the construction.
- [x] `PrimeRawMomentContrasts.lean` passes its direct artifact-producing source audit without diagnostics: finite observation cube, exact multilinearity, raw error-sum bound, even CRT lags and isolation of an arbitrary prime coefficient are formalized. Leaf wired; final axiom audit pending.
- [ ] Formal exact pair/diagonal contrasts, raw count and reconstruction.
- [ ] Formal noise bound and fixed-protocol lower bound.
- [ ] Direct source and axiom audits, umbrella wiring, index and lint.

This card does not close item 6 until its Lean gates and the stated-family scope are discharged.
