# Finite modular-inverse rectangles with all frequency gcds retained

- **ID:** goldbach-modular-inverse-rectangle-completion
- **Stage:** 2-fully-proven
- **Type:** Classical bridge; no novelty claim
- **Sources:** [composite Kloosterman budget](../3-formalized/not_new_scientific_knowledge/goldbach-composite-kloosterman-budget.md), [flat prime-dilation dispersion](goldbach-flat-prime-dilation-dispersion.md)
- **Lean status:** Not formalized; existing interval-column completion has a different, larger remainder

## Exact statement

Let M≥1, let U and V be finite intervals of consecutive integers, and let
c be a residue modulo M. Write L=|U|, H=|V|, g=gcd(M,c.val),
λ=1+log M and τ=τ(M). Let C count the actual pairs (u,v)∈U×V satisfying
gcd(u,M)=1 and uv≡c modulo M. Then

    |C − φ(M)LH/M²|
      ≤ 24 τ M^(2/3) g^(1/3) λ² + τ λ (Lg+H)/M.       (R)

Lengths may be zero or exceed M, starts may be negative, and c may be
zero. No coprimality premise on c or on the Fourier frequencies appears.
The exponents in (R) are real powers of positive integers.

## Gates

- [x] Exact actual-source statement, with every endpoint retained.
- [x] Dependency-closed paper proof below, using the separate proved composite budget.
- [ ] Direct Lean leaf check and proof-closure audit of (R).
- [ ] No publication or scientific-novelty claim.

## Paper proof [PROVED HERE]

Put e_M(t)=exp(2πit/M) and

    F_U(a)=Σ_(u∈U) e_M(−au).

For a nonzero residue a, put h=min(a.val,M−a.val). The geometric-series
identity, including the case of an empty interval, gives

    |F_U(a)| ≤ 2/|1−e_M(a)| ≤ M/(2h).                  (2)

The first factor from the interval's starting point has modulus one.
For the second inequality, |1−e_M(a)|=2 sin(πh/M), and
sin t≥2t/π for 0≤t≤π/2. The latter follows from concavity of sine on
that interval and its endpoint values. Thus complete periods and finite
endpoints require no separate approximation.

Summing (2), pairing a.val with M−a.val, and bounding the harmonic sum
by its decreasing integral gives

    Σ_(a≠0 mod M) |F_U(a)| ≤ M(1+log M).              (3)

For M=1 the sum is empty. For M≥2 the pairing bound is at most
M H_(M−1), and H_(M−1)≤1+log M. This also proves (3) for every length L.

If d|M and q=M/d, the nonzero residues a with d|a.val are uniquely
a=dt with 1≤t<q. Their characters satisfy e_M(dtu)=e_q(tu). Applying
(3) at q and using 1+log q≤λ yields the progression-sensitive estimate

    Σ_(a≠0 mod M, d|a.val) |F_U(a)| ≤ (M/d) λ.        (4)

The same estimates hold for V.

Finite character orthogonality counts the residue multiplicities of U
and V. A unit x determines v≡c x⁻¹, so exact Fourier inversion gives

    C = M⁻² Σ_(a,b mod M) F_U(a)F_V(b) S(a,bc;M).    (5)

Here S is the actual Kloosterman sum over units. Orthogonality follows
by summing a finite geometric series: the sum of e_M(at) over a is M
if t≡0 and zero otherwise. Substitution into the two residue counts and
finite regrouping prove (5), with no limiting operation. The (0,0)
term is exactly φ(M)LH/M².

For the nonzero/nonzero terms, the separately proved cubic bound implies

    |S(a,bc;M)| ≤ 8 τ M^(2/3) gcd(M,a.val,(bc).val)^(1/3).

The gcd is invariant under changing integer representatives. At each
prime, the inequality

    min(v_M,v_a,v_b+v_c)
      ≤ min(v_M,v_c)+min(v_M,v_a,v_b)

shows that it is at most g·gcd(M,a.val,b.val). If c=0 the same conclusion
is immediate from the bound by M. For t=gcd(M,a.val,b.val), the term d=t
is present in the divisor sum, hence

    t^(1/3) ≤ Σ_(d|M, d|a.val, d|b.val) d^(1/3).

Triangle inequality, finite regrouping, and (4) bound the contribution
of all nonzero/nonzero frequencies to (5) by

    8 τ M^(2/3) g^(1/3) λ² Σ_(d|M) d^(−5/3)
      ≤ 24 τ M^(2/3) g^(1/3) λ².                    (6)

Indeed the divisor sum is at most the full positive-integer sum, which
is at most 1+∫_1^∞ t^(−5/3)dt=5/2≤3. The cube-root deduction uses
monotonicity of the cube on nonnegative reals; its right-hand cube is
exactly the existing bound 512 τ³ M² gcd(M,a,bc).

The two axes must be kept separately. The Ramanujan bound

    |c_M(t)| ≤ gcd(M,t)

follows from its prime-power values for k≥1: φ(p^k) when p^k|t, −p^(k−1)
when p^(k−1)|t but p^k does not, and zero otherwise. These values follow
by subtracting the complete sum over multiples of p from the full
additive-character sum. CRT multiplies both the Ramanujan sums and the
gcd bounds, proving the assertion for every M, including M=1.

As S(0,bc;M)=c_M(bc), F_U(0)=L, and
gcd(M,bc)≤g·gcd(M,b), the a=0,b≠0 contribution has modulus at most

    (Lg/M²) Σ_(b≠0) |F_V(b)| gcd(M,b.val)
      ≤ (Lg/M²) Σ_(d|M) d Σ_(b≠0,d|b.val) |F_V(b)|
      ≤ τ λ Lg/M.                                   (7)

The gcd product inequality follows from the same primewise minimum
inequality. The divisor expansion is an upper bound because it includes
d=gcd(M,b.val); every summand is nonnegative. Similarly,
S(a,0;M)=c_M(a) gives an a≠0,b=0 contribution at most τλH/M. Combining
(6), (7), and this second axis proves (R). If M=1 both nonzero frequency
sets are empty and (5) already equals its main term.

## Corpus audit and exact Lean obligation

`RHTower/Sieve/KloostermanSameModulusIntervalCompletion.lean` proves exact
column-correlation completion with a remainder bounded by Mφ(M).
`KloostermanAnalyticFrontier.lean` retains that remainder in the signed
Gram decomposition. Those are useful exact identities, but their bound
does not give (R): (R) counts a modular-inverse graph on a rectangle and
uses the progression-sensitive Fourier bound (4). Do not substitute a
column Gram estimate or an assumed Fourier-decay premise for this step.

`RHTower/Sieve/KloostermanCrossPhaseGeometric.lean` supplies
`stdAddChar_eq_one_iff` and `stdAddChar_nsmul_eq_pow`; its last proof
applies the existing `RHTower.norm_geom_sum_le`. The inspected
`RHTower/SawtoothFourierSeries.lean` also proves
`one_sub_exp_mul_I_eq`, the exact sine-times-unit formula for the chord.
These are concrete sources for (2), not a certificate for the summed
progression estimate (4).

The inspected `RHTower/Sieve/KuzminLandau.lean` proves
`two_mul_le_sin_pi_mul`, supplying the chord lower bound on the whole
unit band. The RH programme's
`BiScaleUncertainty/DivisorAverageChebyshevAndDyadicBlockVarianceProducer.lean`
proves `realHarmonic_le_one_add_log` by its Chebyshev cell lengths.
That logarithmic budget supplies the summation step in (3). The modulus-one
case and each positive-index side condition are discharged from the
actual interval data, rather than added to the final theorem.

Formalize the finite interval transform, (2)–(4), exact graph expansion
(5), and the two frequency axes before claiming (R). The eventual
theorem takes actual modulus, residue, starts, and lengths only. The
flat dispersion theorem, Möbius progression input, signed amplifier,
and marked Type II sum remain separate proof obligations.

## Log

- 2026-10-23 — Formalization in progress in the existing Goldbach arithmetic
  leaf: actual finite interval transforms, character chords, and the
  progression-sensitive Fourier mass. The composite certificate remains
  complete; no certificate for (R) is claimed yet.
- 2026-10-23 — Extracted an explicit constant and a complete finite
  completion proof from the flat-dispersion argument. Existing column
  completion inspected and distinguished from the required graph count.
  No new Lean certificate or novelty claim.
