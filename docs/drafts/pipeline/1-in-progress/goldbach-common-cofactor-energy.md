# Common-cofactor energy with retained congruences

- **ID:** goldbach-common-cofactor-energy
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Goldbach target](goldbach-unconditional-2026-10-23.md), Cycles 2 and 5.
- **Statement:** Test whether averaging divisibility on a common cofactor can
  retain a polynomial family of root congruences without a polynomial loss.

## Goal and gates

The missing input is an arithmetic cancellation estimate. The finite
inequalities below isolate one possible transfer; they do not supply that
input or imply Goldbach. In particular, a fixed additive shift must not be
silently replaced by every reflected target of comparable size.

- [x] 0 → 1: exact finite transfer and its missing arithmetic inputs recorded.
- [ ] 1 → 2: prove the required arithmetic energy and all transfers.
- [ ] 2 → 3: formalize only dependency-closed unconditional conclusions.
- [ ] 3 → 4: scientific novelty and publication audit.

## Source boundary

[Lü–Wang–Wu, §§2.3, 4.1, 4.6, 5.2–5.3](https://arxiv.org/html/2610.20242v1)
uses fixed prime pools
`exp((log x)^a_i)<p≤exp(2(log x)^a_i)`, `0.1<a_i<0.2`,
whose reciprocal mass tends to `log 2`. Its marked Type II energy has
arbitrary logarithmic saving after choosing sufficiently many fixed pools.
The final removal of marks instead takes `x→∞` with the number of weight
families fixed, then lets that number grow; it gives an unquantified `o(x)`.
The relevant moment/root/memory chain was subsequently replayed against
Guo's reflected changes on the [source-audit card](goldbach-varying-shift-source-audit.md).
Its external zero-free dependency remains unverified locally. None of
these analytic claims is a Lean dependency.

## Exact finite transfer, proved here on paper

Let `H,Q` be positive integers, `S(1),…,S(H)` complex numbers, and
`|u(h)|≤1`. Put

`T(q)=Σ_{1≤h≤H, q|h} u(h)S(h)`,
`E=Σ_{h≤H}|S(h)|²`,
`E₂=Σ_{h≤H}τ(h)²|S(h)|²`,
`L_Q=Σ_{q≤min(Q,H)}1/q`.

Then

`Σ_{q≤Q}|T(q)| ≤ (H L_Q)^(1/2) (E E₂)^(1/4)`.

For each `q≤H`, Cauchy gives
`|T(q)|≤(H/q)^(1/2)(Σ_{q|h}|S(h)|²)^(1/2)`;
for `q>H` the sum is empty. Cauchy over `q` bounds the total by
`(H L_Q)^(1/2)(Σ_h d_Q(h)|S(h)|²)^(1/2)`, where
`d_Q(h)=#{q≤Q:q|h}≤τ(h)`. A third Cauchy application gives
`Σ_h τ(h)|S(h)|²≤E^(1/2)E₂^(1/2)`. This proves the claim,
including zero energy. No cancellation assumption entered this finite proof.
The same bound holds with each `|T(q)|` replaced by the maximum of
`|Σ_{h≤t,q|h}u(h)S(h)|` over `0≤t≤H`: its number of terms and
energy are bounded by the same full-range quantities, separately for
each `q`. No additional maximal inequality is needed for this cutoff.

Consequently, at `H≈X/Y`, bounds
`E≪XY(log X)^(-A)` and `E₂≪XY(log X)^C` would yield
`Σ_q|T(q)|≪X(log X)^((C-A+2)/4)`.
This is a conditional deduction on paper, not a proposed Lean interface.
The transfer is ordinary Cauchy and divisor counting, not new scientific
knowledge.

## What divisibility on the cofactor does and does not encode

If an auxiliary label `a` is coprime to `q`, then
`q|a h` is equivalent to `q|h`. However, restricting `a` to be coprime
to `q` changes its inner sum to `S_q(h)`. The displayed inequality is
for one common `S`; it cannot be applied to this family without proving
a corresponding simultaneous energy estimate. It does apply unchanged
to moduli coprime to every allowed label.

For squarefree `q`, let `j=gcd(q,a)` and `r=q/j`. Unique factorization
gives `q|a h` if and only if `r|h`; the shared factor `j` is automatic.
Thus unrestricted roots require partial-label sums indexed by `j`,
with a coprimality restriction involving `r`. The extreme case `a|q`
retains every selected prime in the modulus and leaves no unselected
pool in that label. It cannot be removed as a coprime error without an
aggregate bound. Fixed-parameter constants do not justify growing the
number of pools with `x`.

The source identity is `mn+2=a h`. A maximum over an original endpoint
`mn≤t_q` becomes `a h≤t_q+2`; this varies with both `a` and `q`.
A common-cofactor maximal bound by itself does not resolve this cutoff.

## Exact simultaneous energy and its positive remainder

Here is a refinement that retains the modulus-dependent inner sums.
Fix positive integers `h,Q`, a finite set `A` of positive labels, arbitrary
complex coefficients `c_a`, and nonnegative real weights `w(q)`. Define

`S_q=Σ_{a∈A, q|a h} c_a`, `S=Σ_{a∈A}c_a`,
`D_w(t)=Σ_{1≤q≤Q, q|t}w(q)`.

Then the following two expressions are equal:

`Σ_{q≤Q} w(q)|S_q|²
 =Σ_{a,b∈A} D_w(h gcd(a,b)) c_a conjugate(c_b)
 =D_w(h)|S|² + R_w`,

where

`R_w=Σ_{q≤Q, q∤h}w(q)|S_q|²≥0`.

Proof: expand each finite square and interchange sums. The two root
conditions on `q` are equivalent to `q|gcd(ah,bh)=h gcd(a,b)`.
For `q|h`, every label is admitted, so its inner sum is `S`; splitting
off exactly these moduli gives the second expression and positivity.
In particular the remainder is a positive quadratic form, even though
individual cross terms can have either sign. It also has the exact form

`R_w=Σ_{a,b∈A, gcd(a,b)>1}
 [D_w(h gcd(a,b))-D_w(h)] c_a conjugate(c_b)`.

All terms with coprime labels vanish from this remainder. This identifies
the shared-label contribution instead of deleting it. It is finite
divisor/Gram algebra, not a new arithmetic cancellation result. The
underlying divisor-incidence factorization belongs to the classical
[GCD-matrix literature](https://users.math.msu.edu/users/bsagan/Papers/Old/gcd.pdf);
the precise finite identities above were derived directly for this support.

For `w=1`, the entry difference is at most `τ(h)τ(gcd(a,b))`.
If each label is a product of `K` distinct primes, it is at most
`2^K τ(h)`. With a linear modulus weight the same saving cannot be
assumed: already at `h=1`, `gcd(a,b)=p` prime, and `Q≥p`, the entry
difference is `1` for `w=1` and `p` for `w(q)=q`. This is an exact
finite comparison, not a counterexample on the arithmetic support.

### Coarse bound for the unweighted shared-label remainder

For reflected products, suppose `a,b∈[Y,4Y]` are squarefree with `K`
prime factors, all at least `P`, and are coprime to a positive target
`T≍X`. Let `1≤h≤H≍X/Y`, where `Y=X^o(1)`, and let

`c_a(h)=η(a/Y) Σ_{mn=T-ah>0} α_m β_n`,

with bounded cutoff and `|α_mβ_n|≤(log X)^C`. The product supports
are contained in a fixed multiple of `[1,X]`. The constants here may
depend on fixed `K,C` and the support constants. Then

`Σ_{h≤H} R_1(h) ≪ X Y (log X)^(2C+7) / P`.

To prove this bound, first note `|c_a(h)|≪(log X)^C τ(T-ah)`.
For each fixed pair `a,b`, Hölder bounds
`Σ_h τ(h)τ(T-ah)τ(T-bh)` by the geometric mean of the three
corresponding third divisor moments. The ordinary moment is
`O(H(log X)^7)`. For the affine moment use `τ(n)^3≤τ₈(n)`.
In each ordered eight-factor decomposition, delete a largest factor.
The product `d` of the seven remaining factors is `O(X^(7/8))`,
and its number of choices is at most `8τ₇(d)`. The divisibility
`d|T-ah` implies `(d,a)=1`, so it selects one class of `h` modulo
`d`, with at most `H/d+1` members. Thus this moment is at most

`O(H(log X)^7 + X^(7/8)(log X)^6)=O(H(log X)^7)`.

The same argument applies to `b`; omit nonpositive shifted arguments
throughout. Finally, labels sharing a prime have at most
`Σ_{p≥P}(4Y/p)^2≪Y²/P` ordered pairs. The entry bound above and
`H≍X/Y` give the claimed estimate. This proof uses only classical
divisor-moment bounds; no signed estimate has been assumed in it.

For completeness, the coarse total moment required earlier also follows:
`E₂≪XY(log X)^(2C+15)`. Cauchy over at most `4Y` labels reduces it
to the sum of `τ(h)²τ(T-ah)²` for each `a`. Cauchy over `h` and
`τ(n)^4≤τ₁₆(n)` bound that sum by `O(H(log X)^15)`; the same
largest-factor argument now leaves a product `O(X^(15/16))`, still
smaller than `H` up to a fixed logarithmic factor because `Y=X^o(1)`.
Sum over the at most `4Y` labels. The elementary divisor sums used
here can be bounded by expanding their factor tuples:
`Σ_{d≤D}τ_k(d)/d≤(1+log D)^k` and
`Σ_{d≤D}τ_k(d)≤D(1+log D)^(k-1)`.

Consequently an independently proved small total energy `E` and the
coarse moment `E₂` would also control the sum of the *unweighted*
root energies, including shared labels. This repairs one overly strong
objection to that energy transfer. It still does not bound the sum of
the original absolute root sums: Cauchy must count their outer cofactor
supports. For moduli sharing labels those supports are larger than
`H/q`. Applying that bound there would reintroduce the original error.

Fixing the shared primes leaves fewer free prime pools. A possible
iteration must therefore cover the terminal case in which the modulus
contains a whole label. At fixed `K`, these labels have subpower size,
so a polynomial modulus range includes that case. No terminal estimate
has been proved here.

## Matched residue blocks: valid local norm transfer

Let `P_g` be mutually orthogonal row projections and `Q_g` mutually
orthogonal column projections on finite Hilbert spaces. For any matching
`σ` of the labels and any operator `K`,

`‖Σ_g P_g K Q_{σ(g)}‖ ≤ ‖K‖`.

Indeed, orthogonal output blocks give
`‖Σ_g P_g K Q_{σ(g)}v‖²
 =Σ_g‖P_g K Q_{σ(g)}v‖²
 ≤‖K‖²Σ_g‖Q_{σ(g)}v‖²≤‖K‖²‖v‖²`.
This includes a unit-product residue condition: match row residue `g`
with column residue `t/g`. It need not be a single row and column
compression. For two product roots, use ordered pairs of unit residues.
Thus a coupled root condition is not, by itself, an obstruction to an
operator-norm transfer. This is known block pinching, not a new theorem.

Two limitations remain. First, contraction has no factor `1/q`, nor an
automatic saving after summing different moduli. Second, the inspected
source transfers localized moments to endpoint pairings; no suitably
small global operator norm has been established here. Its small-prime
state weights, moment normalization, major arcs, and removal errors must
all retain the extra restriction. A generic norm observation does not
complete that proof.

## Current open core

1. Upgrade simultaneous root energy to the required sum of absolute root
   sums without inserting the false outer-support bound `H/q`. Handle
   the terminal case where a modulus contains a whole auxiliary label.
2. The coarse divisor-weighted moment and original-variable maximal
   cutoff transfer are now proved on paper. Their actual prime-sum
   assembly is on the [R2 card](goldbach-reflected-marked-root-average.md);
   its external zero-free dependency remains open.
3. Remove the mark at the precision required by prime counting. Marked
   weights vanish on primes larger than their pools; an unquantified
   average approximation cannot silently supply this precision.
4. Guo supplies an every-target reflected adaptation, whose specified
   moment chain now has a paper replay. The external fixed zero-free
   proof closure is still required before using its energy here.

Verdict: active transfer investigation, no analytic theorem or scientific
advance claimed. No route is retired by these observations; no conditional
analytic statement has been put into Lean.

## Log

- 2026-10-23 — Derived common-cofactor inequality; checked the partial-label,
  original-cutoff, parameter-order, and matched-block issues against the
  source. Corpus query for orthogonal block compression returned partial
  semantic coverage and no checked theorem supplying the analytic input.
- 2026-10-23 — Derived the exact gcd Gram matrix, its positive shared-label
  remainder, and a coarse unweighted remainder bound. The remaining gap
  is the outer-support/absolute-sum transfer, not unweighted root energy.
- 2026-10-23 — The pool-coprime actual prime-sum transfer is assembled
  on the R2 card, including maximal endpoints and averaged errors.
  Shared-label absolute sums and prime-detecting mark removal remain open.
