# Torsion-Universal Phase Languages Force Polynomial-Magnitude Hypertranscendence

- **ID:** `torsion-universal-phase-polynomial-magnitude-hypertranscendence`
- **Stage:** 2-fully-proven / needs scientific-novelty audit
- **Type:** THEOREM CANDIDATE / GENERAL HT PHASE-LANGUAGE LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** If `beta>2` and the Taylor phases recurrently contain every finite
  word over every finite root-of-unity alphabet, then the entire series with coefficients
  `a_n=exp(-B n^beta)u_n` is hypertranscendental over `C(z)`.

## Goal

Close the exact smooth polynomial escape left by the magnitude-only Prouhet law. Polynomial
log-magnitudes permit arbitrarily high finite moment cancellations, so magnitude separation alone
cannot exclude every ADE. The missing constraint is not randomness or coefficient arithmetic: it
is whether one finite differential equation can keep its bounded Prouhet phase cancellation valid
against every finite torsion character table that recurs in the phase tail.

## Torsion-language universality

Let

```text
mu_infinity = union_(m>=1) mu_m subset S^1,
mu_m = {zeta in C : zeta^m=1}.
```

A phase sequence `u=(u_n)_(n>=0)` in `S^1` is **torsion-language universal** if, for every
`m>=1`, every word `(zeta_0,...,zeta_(ell-1)) in mu_m^ell`, and every lower bound `Q`, there is a
`q>=Q` such that

```text
u_(q+j)=zeta_j  for 0<=j<ell.                              (TLU)
```

Equivalently, every finite word over every finite root-of-unity alphabet occurs arbitrarily far
out in the phase tail. Such sequences exist: enumerate the countable family of all finite
root-of-unity words and concatenate the first `r` words during the `r`-th pass. Repeating the passes
makes every word occur arbitrarily far out. No probabilistic choice is required.

Condition `(TLU)` also realizes every assignment on an arbitrary finite offset set `R subset Z`:
extend the assignment to the interval from `min R` to `max R` by filling unused positions with
`1`, and translate sufficiently far to keep all indices nonnegative.

## Theorem `[PROVED HERE]`

Fix `B>0` and a real `beta>2`. Let `u` be torsion-language universal and put

```text
f(z)=sum_(n>=0) exp(-B n^beta) u_n z^n.                    (1)
```

Then `f` is entire and hypertranscendental over `C(z)`.

More precisely, no nonzero integer algebraic differential equation

```text
P(z,f,f',...,f^(r))=0,   P in Z[z,Y_0,...,Y_r],            (2)
```

can hold. By Mahler's integer-normalization theorem, this excludes every ADE over `C(z)`.

## Proof

The coefficient decay in (1) is faster than every geometric sequence, so `f` is entire. Suppose
for contradiction that it is DA. Mahler normalization supplies an equation (2). Let `D>=1` be the
maximal total degree of `P` in the dependent variables.

Apply the polynomial-magnitude Prouhet phase-lock theorem to (2). Fix one residue
class `tau modulo D`. It gives:

- a finite cluster `C_tau` containing at least two distinct bounded degree-`D` offset multisets;
- a finite offset set `R subset Z` supporting every multiset in `C_tau`;
- nonzero integer-valued polynomials `w_A(q) in Q[q]` for `A in C_tau`;
- constants `c>0`, `eta>0`, and `M>=0`;

such that, for every sufficiently large integer `q`,

```text
|sum_(A in C_tau) w_A(q) exp(-delta_A)
     product_(r in R) u_(q+r)^(m_A(r))|
  <= q^M exp(-c q^eta).                                      (3)
```

Here `m_A(r)` is the multiplicity of `r` in `A`. We first record the exact regularity of the
relative valuations. Put `t=1/q`.

If `beta=k` is an integer, all cluster patterns have the same moments through `k-1`, and the exact
binomial expansion leaves only the constant `p_k(A)` term. Thus every `delta_A` is independent of
`q`.

Suppose that `beta` is not an integer. Put

```text
L=floor(beta),   alpha=L+1-beta in (0,1).                    (4)
```

All cluster patterns agree in moments through `L`. For bounded offsets and small positive `t`, the
convergent binomial expansion gives, relative to any fixed cluster pattern `A_0`,

```text
B sum_r (m_A(r)-m_(A_0)(r))(t^(-1)+r)^beta
  = B t^alpha h_A(t),                                       (5)
```

where `h_A` is analytic near `0`. The finite cluster has a stable minimizer for all sufficiently
small positive `t`: for two distinct patterns, Newton's identities give a first differing power
moment, whose corresponding generalized power has an eventually fixed sign. Choosing a stable
minimizer as `A_0` therefore gives

```text
delta_A(t)=B t^alpha h_A(t)                                 (6)
```

with `h_A` analytic. Hence in both the integer and noninteger cases every factor
`exp(-delta_A(t))` is a convergent generalized-analytic germ at `t=0+`.

Choose an integer `m>D`. For a phase state `s=(s_r)_(r in R) in mu_m^R`, define

```text
H_s(q)=sum_(A in C_tau) w_A(q) exp(-delta_A(q))
          product_(r in R) s_r^(m_A(r)).                     (7)
```

Torsion-language universality gives an unbounded sequence `q_j` on which the local phase window
equals `s`. Evaluating (3) on that sequence yields

```text
|H_s(q_j)| <= q_j^M exp(-c q_j^eta).                         (8)
```

Let `d` be the largest degree of the finitely many `w_A` and define

```text
G_s(t)=t^d H_s(t^(-1)).                                      (9)
```

For integer `beta`, this is an ordinary analytic germ at `0`. For noninteger `beta`, equations
(4)--(6) show that it is a finite sum of germs

```text
p(t) exp(-t^alpha h(t)),                                    (10)
```

with `p,h` analytic and `0<alpha<1`.

Such a germ is either identically zero or has a first generalized power. Indeed, expanding the
exponential and the analytic factors gives a convergent series whose exponents lie in

```text
{i+j alpha : i,j>=0}.
```

This set is locally finite. If `alpha` is rational, the expansion is an ordinary convergent Puiseux
series; if `alpha` is irrational, distinct pairs have distinct exponents. After combining the
finitely many summands, a nonzero germ therefore has

```text
G_s(t)=gamma t^lambda(1+o(1)),   gamma!=0.                   (11)
```

It cannot be smaller than every power of `t` along any sequence tending to zero. But (8), after
multiplication by `q_j^(-d)`, is exponentially smaller than every power. Consequently

```text
G_s=0 as a germ, and hence H_s(q)=0 for all large q,          (12)
```

for every `s in mu_m^R`.

For `A in C_tau`, let

```text
chi_A(s)=product_(r in R) s_r^(m_A(r)).                       (8)
```

These are distinct characters of the finite abelian group `mu_m^R`. To see this, every
`m_A(r)` lies in `[0,D]`; since `m>D`, congruence of two exponent vectors modulo `m` implies their
ordinary equality, hence equality of the two offset multisets.

For every sufficiently large fixed `q`, equation (12) says

```text
sum_(A in C_tau) w_A(q) exp(-delta_A(q)) chi_A(s)=0
  for every s in mu_m^R.                                    (13)
```

Distinct characters of a finite abelian group are linearly independent. Hence

```text
w_A(q) exp(-delta_A(q))=0
```

for every `A` and every sufficiently large `q`. Since the exponential factor is nonzero, every
`w_A` has infinitely many roots and is the zero polynomial. This
contradicts the phase-lock theorem, which deleted identically zero grouped weights. Thus no
equation (2) exists and `f` is HT. `square`

## Existence corollary `[PROVED HERE]`

For every `B>0` and real `beta>2`, there is an explicit deterministic phase sequence with values
in `mu_infinity` for which (1) is HT. One construction is the repeated diagonal concatenation of an
enumeration of all finite words over all `mu_m`.

The theorem is stronger than existence: every phase tail with the same language-universality
property is HT, independently of the order and density with which its torsion words occur.

## Boundary attacks

1. **Recurrence, not one occurrence, is essential.** One occurrence of a torsion word gives only
   one exponentially small polynomial value. Arbitrarily late recurrence forces the fixed
   polynomial `F_s` to vanish identically.
2. **The alphabet order is chosen after the hypothetical ADE.** The phase sequence contains every
   `mu_m` language. After the ADE exposes its finite degree `D`, choosing `m>D` makes the finite
   character table separate all degree-`D` convolution patterns. No uniform degree bound is
   assumed.
3. **The noninteger residue is not treated as an arbitrary error.** It is a convergent
   generalized-analytic germ `t^alpha h(t)`. Quasianalyticity of this finite generalized-power
   algebra, rather than a numerical estimate, converts exponential flatness into exact vanishing.
4. **No finite-width recurrence is assumed.** An ADE normally gives an unbounded convolution
   recurrence. The earlier confinement and Prouhet theorem is what reduces its dominant face to a
   fixed bounded phase window.
5. **The phase sequence need not itself be periodic, automatic, random, or generated by a finite
   alphabet.** In fact no fixed finite alphabet could permit the post-ADE choice `m>D`.
6. **No claim is made for arbitrary coefficient magnitudes.** The exact polynomial profile and
   `beta>2` supplies the bounded Prouhet cluster with exponentially separated complement.

## Parent-theory and novelty questions

- **Generic power-series HT:** Baire or Haar genericity can produce many HT phase choices for fixed
  magnitudes, but it does not make torsion-language universality a deterministic certificate and
  does not extract the finite character obstruction from a hypothetical ADE.
- **Universal/disjunctive sequences:** their defining language recurrence is classical. The new
  candidate mechanism is that ADE coefficient confinement converts it into simultaneous vanishing
  on a finite character group of order chosen beyond the unknown differential degree.
- **Automatic and finite-alphabet transcendence:** those theories usually exploit finite kernels,
  natural boundaries, or functional equations. Here the phases range over all torsion orders, the
  support is full, and the resulting function is entire of order zero.
- **Prouhet--Tarry--Escott theory:** Prouhet relations create the only possible dominant ADE face;
  torsion character separation then destroys every such finite face at once.
- **Slow-growth ADE theory:** Valiron's order-zero third-order DA example prevents ordinary order
  zero from proving the theorem. The present function has full Taylor support, so the
  Lipshitz--Rubel support-gap theorems do not apply.
- **Algebraically independent coefficients:** Gokhman's theorem proves differential transcendence
  when the coefficients are algebraically independent. Here every phase witness used by the proof
  is a root of unity, and the argument uses repeated finite character tables rather than coefficient
  algebraic independence.
- **Arithmetic DA coefficient theory:** the Krattenthaler--Rivoal nonlinear recurrence and
  denominator bounds concern algebraic Taylor coefficients satisfying ADEs. The coefficients here
  contain `exp(-B n^k)` and the proof is Archimedean, not denominator-theoretic.
- **Verified preliminary search verdict:** exact-statement searches for differentially algebraic
  disjunctive sequences, root-of-unity phase languages, universal coefficient words, and
  polynomial-magnitude phase recurrences found no theorem implying the result. The nearest parent
  results each lose a load-bearing feature: they are linear/D-finite, support-gap, algebraically
  independent-coefficient, arithmetic-coefficient, or functional-equation theorems. Scientific
  novelty remains provisional pending specialist and independent proof review.

Primary comparisons:

1. K. Mahler, *A remark on algebraic differential equations* (1971),
   https://eudml.org/doc/296107.
2. L. Lipshitz and L. A. Rubel, *A gap theorem for power series solutions of algebraic
   differential equations*, Amer. J. Math. 108 (1986), 1193--1213, and *A Gap Theorem for
   Differentially Algebraic Power Series* (1991), DOI `10.1007/978-1-4757-4158-2_10`.
3. D. Gokhman, *Differentially transcendental formal power series*, Complex Variables 29 (1996),
   41--44, DOI `10.1080/17476939608814872`.
4. J. P. Bell and S. Chen, *Power series with coefficients from a finite set*, J. Combin. Theory A
   151 (2017), 241--253, DOI `10.1016/j.jcta.2017.05.002`.
5. A. Bostan, L. Di Vizio, and K. Raschel, *Differential transcendence of Bell numbers and
   relatives: a Galois theoretic approach*, arXiv:2012.15292.
6. C. Krattenthaler and T. Rivoal, *Arithmetic properties of the Taylor coefficients of
   differentially algebraic power series*, arXiv:2502.09259.

## Exact RH-route scope

This is a general coefficient-law theorem, not an RH theorem. It proves that a finite differential
constraint cannot coexist with simultaneous recurrence of all finite torsion phase languages under
exact polynomial super-Gaussian magnitudes. It therefore excludes only an RH implementation that
factors its completed function through such a finite differential constraint while retaining this
coefficient regime. It does not by itself show that zeta, Xi, or every object used by a literature
criterion has these Taylor magnitudes or this phase language.

The resulting route boundary is exact:

- a finite-order nonlinear ODE surrogate for such a coefficient model is impossible;
- a fixed finite differential state-space or finite ADE closure of its phase tail is impossible;
- Hilbert--Polya, Connes trace formulas, de Branges canonical systems, Nyman--Beurling
  approximation, Weil positivity, and Li's criterion are not excluded unless a particular
  implementation first makes precisely one of those finite differential compressions;
- the theorem supplies no sign, self-adjoint operator, approximation norm, or zero-location law.

This complements two independent route gates already proved in the pipeline: fixed Taylor moduli
plus HT status do not select real-rootedness, and the Li sequence admits no closed P-recursive
implementation. The three no-goes concern different lost data--phase, nonlinear differential
memory, and holonomic recurrence--and must not be merged into a categorical rejection of the full
literature criteria.

## Lean status

The finite torsion-language layer is formalized in
`HTGeometry/TorsionLanguageUniversalPhase.lean`: `TorsionLanguageUniversal` states cofinal exact
occurrence of every finite torsion word, and
`TorsionLanguageUniversal.exists_strictMono_occurrences` extracts a cofinal strictly increasing
sequence of exact occurrences. The finite-character layer is formalized in
`HTGeometry/TorsionLanguageFaceExactification.lean`:
`face_weights_eq_zero_of_torsionLanguageUniversal` turns asymptotic cancellation of a finite ADE
face into exact vanishing of every limiting weight, with finite Fourier inversion supplied by
`face_fin_weights_eq_zero`.

The remaining unconditional formalization is the polynomial super-Gaussian analytic chain before
that theorem: Mahler normalization, generic ADE coefficient extraction, bounded Prouhet-cluster
confinement, polynomial grouped weights, the stable-minimizer generalized-analytic expansion,
generalized-power nonflatness, and the passage to the finite asymptotically cancelling face accepted
by `face_weights_eq_zero_of_torsionLanguageUniversal`. The phase-existence input is now complete:
`universalTorsionPhase_torsionLanguageUniversal` proves that the concatenated enumeration of all
finite root-of-unity words is torsion-language-universal, and
`exists_torsionLanguageUniversal` supplies the existential form. The theorem cannot move to stage
3 until the remaining polynomial super-Gaussian analytic chain is formalized unconditionally.

## Gates

- [x] 0 -> 1: exact phase-language property, source-pure theorem, and contradiction mechanism stated.
- [x] 1 -> 2: complete unconditional paper proof written and boundary-attacked.
- [x] Torsion-language recurrence and finite-character exactification formalized in Lean.
- [x] Torsion-language-universal phase existence formalized in Lean.
- [ ] Parent-theory and exact literature novelty audit.
- [ ] Independent proof audit.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Extracted the finite-character exactification mechanism from the polynomial
  Prouhet phase-lock theorem and proved torsion-language-universal polynomial-magnitude HT.
- 2026-07-11 — Removed the integer-exponent restriction: noninteger within-cluster defects are
  convergent generalized-analytic germs and cannot be exponentially flat without vanishing.
