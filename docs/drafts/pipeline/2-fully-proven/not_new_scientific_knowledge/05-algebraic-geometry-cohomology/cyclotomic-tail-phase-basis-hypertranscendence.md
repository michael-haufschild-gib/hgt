# Cyclotomic total-degree phase tails force hypertranscendence

- **ID:** `cyclotomic-tail-phase-basis-hypertranscendence`
- **Stage:** 2-fully-proven / needs independent scientific audit
- **Type:** THEOREM / GENERAL HT COEFFICIENT-PHASE LAW
- **Scientific status:** `[NOVELTY UNVERIFIED]`. The proof is complete, but the exact theorem is a
  short synthesis of Mahler's nonlinear coefficient recurrence, the Sibuya--Sperber forward-tail
  normalization, Lindemann--Weierstrass, and coprime cyclotomic bases. It must not be promoted to
  candidate-new before specialists decide whether that synthesis is scientifically nonroutine.
- **Statement:** Let `b_n` be arbitrary real algebraic numbers with `liminf b_n/n>-infinity`.
  Every algebraic unit phase sequence with number-field-robust bounded-total-degree tail freedom
  forces

  ```text
  sum_(n>=0) u_n exp(-b_n) z^n
  ```

  to be HT. Primitive roots of unity of pairwise distinct prime orders tending to infinity realize
  the phase law explicitly. The series is entire when `b_n/n->infinity`.

## Number-field-robust bounded-total-degree tail freedom

Let `k` be a subfield of `Qbar`, and let `(u_n)` be nonzero algebraic numbers. Say that `(u_n)` has
**bounded-total-degree tail freedom over `k`** if, for every integer `D>=1`, there is an index
`M(D)` such that, for every finite

```text
T subset {n:n>=M(D)},
```

the monomials

```text
product_(n in T) u_n^(e_n),   e_n>=0, sum_(n in T)e_n<=D, (TF)
```

are linearly independent over the prefix field

```text
K_M=k(u_0,...,u_(M(D)-1)).                                (1)
```

Call the sequence **number-field robust** when this property holds for every number field `k`, with
`M(D)` allowed to depend on `k`. This is weaker than the exponent-box condition `0<=e_n<=D`: the
number of nonzero exponents in `(TF)` is itself bounded by `D`. It is exactly the amount of phase
information visible to one fixed-arity nonlinear coefficient recurrence after its finite prefix
has been absorbed.

## Prime-cyclotomic tail basis `[PROVED]`

Let `(p_n)` be pairwise distinct odd primes tending to infinity and let `u_n` be a primitive
`p_n`-th root of unity. Then `(u_n)` has number-field-robust bounded-total-degree tail freedom.

### Proof

First take `k=Q`. For a finite prime set `S`, coprimality of conductors gives

```text
Q(u_n:n in S)=Q(zeta_(product_(n in S)p_n))
```

and

```text
[Q(u_n:n in S):Q]=product_(n in S)(p_n-1).                (2)
```

After splitting the indices into a finite prefix and a disjoint finite tail `T`, the monomials

```text
product_(n in T)u_n^(e_n),   0<=e_n<=p_n-2,               (3)
```

form the tensor power basis over the prefix cyclotomic field. Given `D`, choose `M(D)` so that
`p_n>D+1` for every `n>=M(D)`. Every monomial in `(TF)` lies in the basis box (3), proving the
claim. `square`

For an arbitrary fixed number field `k`, delete the finitely many primes ramified in `k`. A
nontrivial subfield of `Q(zeta_p)` is ramified at `p`, so for every remaining `p`,

```text
k intersect Q(zeta_p)=Q.
```

Applying the same ramification argument successively to the pairwise coprime tail conductors gives
the relative tensor basis (3) over `k` joined with the finite prefix. Thus the property is robust
over every number field. `square`

## Mahler forward-recurrence lemma `[SEARCH]`

If a convergent power series

```text
f(z)=sum_(n>=0)a_nz^n                                     (4)
```

is DA over `C(z)`, then after a finite index shift its coefficients satisfy a forward recurrence

```text
a_(n+1)
  = 1/M(n) sum_(sigma,k) sum_(j_1+...+j_k=n-sigma)
      P_(sigma,k)(n,j_1,...,j_k) a_(j_1)...a_(j_k),        (5)
```

possibly after adjoining finitely many initial coefficients to the recurrence field. Equivalently,
after denominators in that finite prefix are cleared, there is a polynomial identity of the same
fixed late-coefficient arity. Here:

1. `M` is a fixed nonzero polynomial;
2. `sigma` ranges through a fixed finite set of nonnegative integers;
3. `1<=k<=D` for one fixed `D`;
4. every `j_i<=n`; and
5. all coefficients outside the fixed initial coefficient prefix are algebraic after
   differential-algebraic constant descent.

This is Mahler's nonlinear coefficient recurrence. The nonnegative-shift form is the
Sibuya--Sperber tail normalization. Only finitely many complex constants occur in an initial ADE;
each satisfies `c'=0`, so differential-algebraic transitivity first gives an ADE over `Qbar(z)`.
Thus every nonalgebraic recurrence coefficient is a rational expression in one fixed finite prefix
`a_0,...,a_R`; clearing its denominators converts it into finitely many additional prefix factors.

## Abstract phase-tail theorem `[PROVED]`

Let `(b_n)` be real algebraic numbers satisfying

```text
liminf_(n->infinity) b_n/n > -infinity.                    (6)
```

Let `(u_n)` be algebraic complex numbers of modulus one with number-field-robust
bounded-total-degree tail freedom. Then

```text
f(z)=sum_(n>=0)u_n exp(-b_n)z^n                            (7)
```

has positive radius of convergence and is HT over `C(z)`. If `b_n/n->infinity`, it is entire.

### Proof

Condition (6) gives positive convergence radius by the root test. The stronger limit gives radius
infinity.

Assume that `f` is DA. Apply the forward-recurrence lemma and let `D` be its fixed maximal
multiplicative arity. Let `k` be the number field generated by the algebraic recurrence constants
and all phases occurring in its fixed initial coefficient prefix. Apply number-field-robust tail
freedom over this `k`, and write `M(D)` for the resulting cutoff. Choose `n` so large that:

1. the recurrence (5) is valid and `M(n)!=0`; and
2. `n+1>=M(D)` for the phase-tail law.

Substitute

```text
a_j=u_j exp(-b_j)
```

into (5), move the left side to the right, and clear both `M(n)` and every denominator involving
the fixed initial coefficient prefix. Expanding those finitely many prefix coefficients as
`u_j exp(-b_j)` produces a finite identity

```text
sum_alpha c_alpha U_alpha exp(-B_alpha)=0,                 (8)
```

where every `c_alpha` is algebraic, every `B_alpha` is algebraic, and the part of every phase
monomial `U_alpha` supported beyond the fixed prefix has total degree at most `D`. The collection
of terms descending from the left side has the form

```text
C_n u_(n+1) exp(-b_(n+1)),                                 (9)
```

where `C_n` is a nonzero rational expression in the fixed prefix coefficients. After its
denominator has been cleared, expand its numerator into prefix phase monomials times exponentials
of algebraic numbers. Because `C_n!=0`, Lindemann--Weierstrass implies that at least one of those
exponential groups has a nonzero algebraic prefix-phase coefficient.

Now group the whole identity (8) by the distinct algebraic values `B_alpha`.
Lindemann--Weierstrass makes every grouped algebraic phase coefficient vanish separately. In the
nonzero group selected from (9), the coefficient contains

```text
c_n^* u_(n+1),   c_n^*!=0 in the prefix phase field,       (10)
```

plus a linear combination of phase monomials formed only from `u_j` with `j<=n`, each having tail
total degree at most `D`.

Absorb phases with index below `M(D)` into the prefix field (1). The monomial `u_(n+1)` is one of
the independent tail basis monomials `(TF)`. No recurrence term can contain it because every index
on the right of (5) is at most `n`. Its basis coefficient in (10) is the nonzero prefix-field
element `c_n^*`. Hence the grouped coefficient cannot vanish, contradicting
Lindemann--Weierstrass.

Therefore no ADE exists and `f` is HT. `square`

## Exact smooth-profile corollary `[PROVED]`

Let `B>0` be algebraic and let `beta>1` be rational. Put

```text
b_n=B n^beta,   n>=1,
```

with any algebraic initial value `b_0`. For prime-cyclotomic phases as above,

```text
sum_(n>=0)u_n exp(-B n^beta)z^n
```

is entire and HT. This includes every exact subquadratic profile `1<beta<2`; no convexity,
relation confinement, recurrent phase language, randomness, or coefficient algebraic independence
is used.

## Attacks and boundaries

1. **The result is a recurrence obstruction.** Mahler's theorem supplies the finite arity. The new
   proof does not require the balanced-survival coefficient lemma.
2. **Algebraic logarithmic magnitudes are essential.** Lindemann--Weierstrass is used on the finite
   collection of exponent sums. Arbitrary real magnitudes are not covered.
3. **Unbounded cyclotomic orders are load-bearing.** A fixed number field cannot supply tail bases
   through every recurrence arity.
4. **The theorem is sufficient, not necessary.** Classical HT functions need not expose this
   coefficient-phase structure.
5. **No divisor or positivity statement follows.** The law excludes a finite recurrence/ADE but
   does not locate zeros.

## Parent and novelty audit

The proof has four strong parents:

1. Mahler's fixed-arity nonlinear recurrence for coefficients of a DA series;
2. Sibuya--Sperber normalization to a genuine forward recurrence;
3. Lindemann--Weierstrass separation of distinct algebraic exponential weights; and
4. tensor bases for cyclotomic fields of coprime conductors.

The exact arbitrary-log-profile phase theorem was not found in searches for cyclotomic coefficient
tails, prime-order root-of-unity phases, and nonlinear DA coefficient recurrences. That negative
search evidence is insufficient for promotion. The argument is short once the four parents are
juxtaposed, so scientific novelty and significance require independent specialist judgment.

Primary comparisons:

1. K. Mahler, *Lectures on Transcendental Numbers*, Lecture Notes in Mathematics 546, Springer,
   1976, Chapter 8.
2. Y. Sibuya and S. Sperber, *Some new results on power-series solutions of algebraic differential
   equations*, in *Singular Perturbations and Asymptotics*, Academic Press, 1980, 379--404.
3. Y. Sibuya and S. Sperber, *Arithmetic properties of power series solutions of algebraic
   differential equations*, Ann. of Math. 113 (1981), 111--157,
   https://doi.org/10.2307/1971135.
4. C. Krattenthaler and T. Rivoal, *Arithmetic properties of the Taylor coefficients of
   differentially algebraic power series*, https://arxiv.org/abs/2502.09259.
5. Lindemann--Weierstrass in its finite linear-independence form,
   https://encyclopediaofmath.org/wiki/Lindemann_theorem.

## Exact RH-route scope

The theorem excludes every concrete Hilbert--Polya, Connes, de Branges, Nyman--Beurling, Weil,
Li, heat, theta, or coefficient implementation that first claims to generate the exact
cyclotomic-exponential coefficient model (7) from one finite algebraic differential state or one
fixed-arity Mahler recurrence.

It does not exclude any complete named criterion. Those criteria retain spectral, norm, positivity,
Euler-product, heat-flow, or divisor data which need not factor through (7) or through a finite ADE.

## Lean status

No Lean formalization is claimed. The complete theorem requires Mahler recurrence extraction and
forward normalization, differential-algebraic constant descent, finite-family
Lindemann--Weierstrass, and relative cyclotomic tensor bases. The current Lean tree does not expose
that chain. The card cannot enter stage 3 until the whole unconditional theorem is formalized.

## Gates

- [x] Complete paper proof.
- [x] Exponent-box hypothesis weakened to bounded total degree.
- [x] Balanced-survival dependency removed.
- [x] Mahler--Sibuya--Sperber parent incorporated.
- [x] Candidate-new label withdrawn pending independent audit.
- [ ] Independent proof and scientific-novelty audit.
- [ ] Whole theorem formalized unconditionally in Lean.
