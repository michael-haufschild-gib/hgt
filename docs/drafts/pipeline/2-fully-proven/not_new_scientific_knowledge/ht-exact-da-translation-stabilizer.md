# Exact Differential-Algebraic Translation Stabilizer of an HT Entire Function

- **ID:** ht-exact-da-translation-stabilizer
- **Stage:** 2-fully-proven/not-new
- **Type:** THEOREM (paper) / BRIDGE / REALIZATION EXAMPLE
- **Scientific status:** `[BRIDGE]` — proved, significant as a boundary example, but too directly obtained from Carroll plus Ostrowski to count as new scientific knowledge
- **Statement:** Every nonzero locally cyclic additive subgroup `H` of `C` is the exact additive differential-algebraic translation stabilizer of some entire function hypertranscendental over `C(z)`; in particular `H = Q` is realizable, with D-finite defects on `Q` and HT defects off `Q`.

## Goal

Determine whether an HT function can be fixed modulo the DA functions by a dense proper translation subgroup, and whether that subgroup can be recovered exactly rather than merely embedded. This tests the constraint-first claim at the level of a new invariant:

`Stab_DA(F) = {h in C : z |-> F(z+h)-F(z) is DA over C(z)}`.

The target is about hypertranscendental functions as a class. It does not use zeta, the Riemann hypothesis, or an L-function-specific structure.

The set `Stab_DA(F)` is always an additive subgroup. Indeed, DA functions are closed under translation, addition, and negation, while

`Delta_(h+k)F = (Delta_k F)(z+h) + Delta_h F`

and

`Delta_(-h)F = -(Delta_h F)(z-h)`.

## Gates

- [x] 0 -> 1 in-progress: exact claim, explicit construction, proof skeleton, named parent theorem, and live literature threat.
- [x] Paper-proof gate: Ostrowski's definition and Theorem 8 were checked against the primary English translation; the coefficient-field, tail-gcd, realization, and multiplicative arguments are complete.
- [x] Significance gate: exact invariant, finite-or-HT dichotomy, spectral classification, dense proper examples, and prescribed locally cyclic spectra.
- [x] Parent-theory gate: **FAIL for scientific novelty.** Carroll supplies the character-series skeleton and Ostrowski supplies exactly the coefficient criterion; the tail-gcd computation and off-subgroup field-recovery argument are short consequences once those parents are juxtaposed.
- [x] Literature gate, provisional: no exact result found in the checked primary and citation literature or exact multilingual searches; independent MathSciNet/zbMATH/specialist confirmation remains required.
- [x] Rediscovery gate: exact wording was not found, but absence of wording does not rescue a routine parent consequence. Classified `[BRIDGE]`.
- [ ] 2 -> 3 formalized: formalize only after the scientific gate survives.
- [ ] 3 -> 4 publication-ready: standalone theorem, proof, parent comparison, and literature certificate.

## Tail-gcd classification and realization theorem `[PROVED HERE] [BRIDGE]`

Let `(n_k)` be a strictly increasing sequence of positive integers and let `(c_k)` be algebraically independent nonzero complex numbers with sufficiently fast decay that

`F(z) = sum_k c_k exp(2 pi i n_k z)`

is entire. For each `N`, let

`g_N = gcd(n_N, n_(N+1), ...)`.

Then every translation defect satisfies the sharp dichotomy

`Delta_h F is a finite exponential polynomial` or `Delta_h F is HT`,

and the first alternative occurs exactly on

`Stab_DA(F) = union_N (1/g_N)Z`.

In particular there are no infinite DA defects hidden between the finite and HT cases. The frequency-tail gcd completely determines the DA-translation spectrum.

Conversely, every nonzero locally cyclic additive subgroup of `C` is obtained, after scaling, by such a tail-gcd spectrum. Therefore:

For every nonzero locally cyclic additive subgroup `H` of `C`, there is an entire HT function `F_H` such that

`Stab_DA(F_H) = H`.

The multiplicative analogue also holds: there is a zero-free entire HT function `G_H` such that

`{h in C : G_H(z+h)/G_H(z) is DA} = H`.

Here locally cyclic means that every finitely generated subgroup of `H` is cyclic. Since `H` is a nonzero subgroup of the torsion-free group `(C,+)`, this is equivalent to `H` being contained in a rational line `alpha Q` for any chosen nonzero `alpha in H`.

Coefficients satisfying algebraic independence and any prescribed positive decay bounds exist without a probabilistic argument. Inductively, the algebraic closure of `Q(c_1,...,c_(k-1))` inside `C` is countable, while every punctured disk is uncountable; choose `c_k` in the required disk outside that closure.

### Exact `Q` instance

Choose algebraically independent nonzero complex numbers `c_k` satisfying

`|c_k| <= exp(-(k!)^2)`

and put

`F(z) = sum_{k >= 1} c_k exp(2 pi i k! z)`.

Then:

1. `F` is entire, `1`-periodic, and hypertranscendental over `C(z)`.
2. If `q in Q`, then `Delta_q F(z) = F(z+q)-F(z)` is a finite exponential polynomial, hence D-finite.
3. If `h notin Q`, then `Delta_h F` is hypertranscendental.
4. Consequently `Stab_DA(F) = Q`, a dense nonclosed proper subgroup of `C`.
5. For `G = exp(F)`, `G` is zero-free and hypertranscendental and
   `{h in C : G(z+h)/G(z) is DA} = Q`.

### Prescribed locally cyclic subgroup

Fix `0 != alpha in H` and put `H_0 = alpha^(-1)H`, so `Z subset H_0 subset Q`. Write

`H_0 = union_k (1/a_k)Z`,

where `a_k` are positive integers with `a_k | a_(k+1)`. Choose pairwise distinct primes `p_k`, large enough that

`n_k = a_k p_k`

is strictly increasing. Choose algebraically independent nonzero coefficients `c_k` with decay faster than `exp(-|2 pi n_k/alpha|^2)`, and set

`F_H(z) = sum_k c_k exp(2 pi i n_k z/alpha)`.

If `h in H`, then `h/alpha in (1/a_K)Z` for some `K`. For all `k >= K`, `a_K | a_k`, so `n_k h/alpha` is an integer and the tail is invariant. Thus `Delta_h F_H` is a finite exponential polynomial.

If `h notin H`, put `u = exp(2 pi i h/alpha)`. There are infinitely many `k` for which `u^(n_k) != 1`:

- if `h/alpha` is irrational or nonreal, it holds for every `k`;
- if `h/alpha = r/b` is rational in lowest terms, membership outside `H_0` means `b` divides no `a_k`; since the auxiliary primes `p_k` are pairwise distinct, `b | a_k p_k` can hold for only finitely many `k`.

On the infinite nonvanishing index set `I`, the defect coefficients

`d_k = c_k(u^(n_k)-1)`

recover the algebraically independent `c_k` after adjoining the single number `u`. Hence `(d_k)` has no finite Ostrowski basis, and `Delta_h F_H` is HT. This proves exactness.

### Proof of the tail-gcd formula

For a shift `h`, put `u = exp(2 pi i h)`. The defect is

`Delta_h F(z) = sum_k c_k(u^(n_k)-1) exp(2 pi i n_k z)`.

The defect is finite exactly when `u^(n_k)=1` eventually, equivalently when `n_k h` is an integer eventually. For a fixed tail this forces `h` to be real rational, and Bezout's identity gives

`{h : n_k h in Z for every k >= N} = (1/g_N)Z`.

Taking the union over `N` gives the asserted eventual period group.

If the defect is not finite, the index set

`I_h = {k : u^(n_k) != 1}`

is infinite. After adjoining the single phase `u`, every `c_k` with `k in I_h` is recovered from the corresponding defect coefficient. A finite Ostrowski basis for all defect coefficients would therefore put an infinite algebraically independent subset of the `c_k` inside a field of finite transcendence degree, which is impossible. Ostrowski's theorem makes the defect HT.

## Proof architecture

The following details are written for `H = Q`; the prescribed-subgroup proof above changes only the integer frequency sequence.

### Entire convergence

On `|z| <= R`, the `k`th term is bounded by

`exp(-(k!)^2 + 2 pi k! R)`,

which is summable. Thus the series converges locally uniformly and defines an entire function.

### Hypertranscendence

After the affine change `s = -2 pi i z`, the series becomes

`Phi(s) = sum c_k exp(-k! s)`.

The coefficient set has infinite transcendence degree over `Q`, hence has no finite coefficient basis in Ostrowski's sense. Ostrowski's Dirichlet-series theorem then makes `Phi`, and therefore `F`, hypertranscendental.

### Rational translations

If `q = m/N!`, then `exp(2 pi i k! q) = 1` for every `k >= N`. Therefore

`Delta_q F = sum_{k < N} c_k (exp(2 pi i k!q)-1) exp(2 pi i k!z)`,

a finite exponential polynomial.

### Exact converse

Let `h notin Q` and `u = exp(2 pi i h)`. Then `u` is not a root of unity, so

`d_k = c_k (u^(k!)-1)`

is nonzero for every `k`. Moreover

`Q(u,c_1,c_2,...) = Q(u,d_1,d_2,...)`.

If `(d_k)` had a finite coefficient basis, the field on the right would have finite transcendence degree over `Q`. The field on the left has infinite transcendence degree because the `c_k` are algebraically independent and adjoining one element `u` cannot reduce infinite transcendence degree to finite. Hence `(d_k)` has no finite basis. Ostrowski's theorem applied to

`Delta_h Phi(s) = sum d_k exp(-k!s)`

shows that `Delta_h F` is hypertranscendental.

### Multiplicative form

For rational `q`,

`G(z+q)/G(z) = exp(Delta_q F(z))`

is DA. Conversely, if this quotient were DA for some `h notin Q`, then its logarithmic derivative would make `(Delta_h F)'` DA, hence `Delta_h F` DA, contradicting the exact converse. The same logarithmic-derivative argument shows that `G` itself is HT.

## Constraint complexity

For `q = 1/N!`, the nonzero defect contains exactly the frequencies

`1!, 2!, ..., (N-1)!`.

Its minimal constant-coefficient linear differential equation has order `N-1`. Thus DA constraints exist at shifts tending to zero, but their linear spectral rank diverges. No nonlinear differential-order growth is claimed.

## Parent theory and novelty threats

1. **Carroll 1965 is a genuine parent.** For a non-compactly-generated locally compact abelian group, Carroll constructs a uniformly convergent infinite character series whose every group difference is a trigonometric polynomial. On discrete `Q`, his nested-subgroup construction can use the same factorial characters. Therefore the bare assertion that every rational defect is an exponential polynomial is not new.
2. **The proposed survivor is the exact analytic/HGT lift.** Carroll works on the abstract group `Q`; he does not, in the checked theorem and construction, prove an entire HT extension or identify the exact set of complex shifts with DA defects.
3. **Ostrowski 1920 is the HT engine.** Combining Carroll's character skeleton with Ostrowski's no-finite-basis theorem may still be judged routine. The literature and rediscovery gates remain open.
4. **Montel-type theorems are adjacent but do not immediately apply.** Results based on finitely many shifts generating a dense subgroup cannot fire on `Q`, since every finitely generated subgroup of `Q` is discrete.

## Primary-literature audit

1. **A. Ostrowski (1920), English translation (2022), Theorem 8 and Proposition 4.** A convergent Dirichlet series whose coefficients have no finite basis satisfies no algebraic differential equation. The definition is exactly rational generation by finitely many complex numbers. Proposition 1 eliminates explicit dependence on the independent variable, so the conclusion applies over `C(z)`. Source: `https://arxiv.org/abs/2211.02088`.
2. **F. W. Carroll (1965), Theorems 2 and 3.** The exponential-polynomial difference property holds on an LCA group exactly when it is compactly generated. His non-compact construction is a convergent character series with finite character differences, and is the direct parent/source kill for the weak inclusion theorem. Source: DOI `10.1090/S0002-9947-1965-0171875-2`.
3. **J. M. Almira (2017), Theorem 5.** Finitely many shifts generating a dense subgroup force an exponential polynomial when the corresponding differences are exponential polynomials. This does not apply to the non-finitely-generated dense group `Q`, and it does not treat DA defects. Source: DOI `10.14712/1213-7243.2015.224`.
4. **T. Dreyfus (2025), Theorem 1.** DA meromorphic solutions of a fixed linear shift equation lie in a ring generated by periodic functions and exponentials. This is a fixed-shift classification and does not classify the full set of shifts for one function. Source: `https://arxiv.org/abs/2212.00388`.
5. Carroll's indexed citation chain found five papers, concerned with measurable differences, regularity of exponential polynomials, Riemann sums, and the general difference property; none gave an entire HT lift or exact DA-shift spectrum.

**Audit verdict:** the weak theorem is known; the exact tail-gcd wording was not located, but its proof is too direct a Carroll--Ostrowski synthesis to pass the scientific parent-theory gate. Keep it as a proved bridge and sharp example, not new knowledge.

## Boundary significance

The theorem would introduce an exact constraint invariant for HT functions, calculate it by a spectral tail-gcd formula, and realize every locally cyclic constraint subgroup, including arbitrary supernatural denominator profiles inside a rational line. It shows that the invariant can be discrete or dense, proper and nonclosed. It would also prove that DA is not topologically rigid under translation defects: constraints can hold on shifts accumulating at zero while the limiting function and all off-subgroup defects remain HT. The finite-or-HT dichotomy rules out hidden nonlinear DA defects, while divergent spectral rank identifies the escape mechanism.

## Successor residue

1. Prove or disprove that every HT entire function has at most countably many DA translation defects.
2. Prove bounded-ADE-complexity accumulation rigidity for the analytic family `h |-> Delta_h F`.
3. Classify which countable subgroups can occur beyond the locally cyclic character-tail construction.

## Log

- 2026-07-10 - Created after the weak dense-defect claim was parent-killed by Carroll's 1965 difference-property theorem. Kept only the exact DA-stabilizer strengthening.
- 2026-07-10 - Strengthened to the tail-gcd finite-or-HT classification and prescribed locally cyclic realization theorem. Primary parent and descendant literature checked.
- 2026-07-10 - Re-audited under the explicit routine-parent test and downgraded to `[BRIDGE]`: scientifically useful, but too directly generated by Carroll's character construction plus Ostrowski's coefficient theorem.
