# Gaussian Torsion-Language Universality Forces Hypertranscendence

- **ID:** `gaussian-torsion-language-hypertranscendence`
- **Stage:** 2-fully-proven / needs scientific-novelty audit
- **Type:** THEOREM CANDIDATE / GENERAL HT GAUSSIAN-FACE LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** If the Taylor phases recurrently contain every finite word over every finite
  root-of-unity alphabet, then every full-support Gaussian-magnitude series
  `sum exp(-B n^2)u_n z^n` is hypertranscendental over `C(z)`.

## Goal

Reach the critical quadratic coefficient scale excluded from the bounded Prouhet-confinement
theorem. At `-log|a_n|=B n^2`, an ADE dominant face can contain infinitely many offset patterns:
an offset of size `R` costs only `B R^2`, independently of the balanced index. The replacement for
bounded confinement is a complete, summable discrete-Gaussian face. The question is whether a
single finite ADE can cancel that entire face against a phase tail containing every finite torsion
language.

## Setup

Use the torsion-language-universality condition `(TLU)` from
`torsion-universal-phase-polynomial-magnitude-hypertranscendence.md`: every finite word over every
finite group `mu_m` occurs arbitrarily far out in the phase sequence `u=(u_n)`.

Fix `B>0` and put

```text
f(z)=sum_(n>=0) exp(-B n^2)u_n z^n.                         (1)
```

## Theorem `[PROVED HERE]`

If `u` is torsion-language universal, then the function (1) is entire and HT over `C(z)`.

## Proof

The Gaussian coefficient decay makes (1) entire. Suppose that `f` is DA. Mahler's
integer-normalization theorem supplies a nonzero equation

```text
P(z,f,f',...,f^(r))=0,   P in Z[z,Y_0,...,Y_r].              (2)
```

Let `D>=1` be its maximal total dependent-variable degree. Generic coefficient extraction and
grouping give exact finite identities with integer weights at every sufficiently large coefficient
index.

### 1. Degree and source-sum confinement

Fix a residue `tau modulo D` and write the coefficient index as `N=Dq+tau`. For a degree-`d`
convolution atom with source sum `N+c`, the balanced Gaussian valuation is

```text
B d ((N+c)/d)^2 = B(N+c)^2/d.                              (3)
```

Every degree `d<D` therefore loses to a balanced degree-`D` witness by a positive multiple of
`q^2`. Among the finitely many degree-`D` source shifts, increasing the shift by one raises the
balanced valuation by `2Bq+O(1)`. Let `c_*` be the least shift whose grouped top-degree
polarization is not identically zero. Balanced survival supplies a nonzero fixed-offset atom in
that group. All lower degrees and all larger active shifts are exponentially negligible after the
least degree-`D`, shift-`c_*` face is normalized.

For an atom on that face write its source indices as

```text
q+r_1,...,q+r_D,   sum_i r_i=S_tau,                          (4)
```

where `S_tau` is fixed. Its valuation is exactly

```text
B sum_i(q+r_i)^2
 = B(Dq^2+2qS_tau+sum_i r_i^2).                              (5)
```

Thus the complete residual face is indexed by integer offset multisets of size `D` and sum
`S_tau`, with discrete-Gaussian weight determined by

```text
Q(A)=sum_r m_A(r)r^2.                                       (6)
```

Let `Q_0` be the minimum of `Q` on this lattice.

### 2. Uniform polynomial weights and a fixed leading atom

For a fixed offset multiset `A`, its grouped coefficient weight `w_A(q)` is a rational polynomial
in `q`, integer-valued at the relevant integers. It is obtained from finitely many symmetrized
products of falling factorials `(q+r)_j`. Consequently there are constants `J,C`, depending only
on `P`, such that all grouped weights admit a common description polynomial in `q` and the offsets,
of total offset degree at most `J`.

Let `H` be the largest `q`-degree of a nonzero grouped weight on the least face. This maximum exists
because the differential monomials and derivative orders are finite. Choose a fixed bounded offset
pattern `A_0` for which

```text
ell_(A_0)=lim_(q->infinity) q^(-H)w_(A_0)(q) != 0.           (7)
```

For every fixed pattern `A`, the limit

```text
ell_A=lim_(q->infinity) q^(-H)w_A(q)                         (8)
```

exists, possibly with value zero. Polynomiality in the offsets gives the uniform bound

```text
q^(-H)|w_A(q)| <= C(1+max_r|r|)^J                            (9)
```

whenever all source indices `q+r` are nonnegative. Patterns with a macroscopic offset are even
more strongly suppressed by the exact quadratic valuation.

### 3. The exterior of a finite phase window is a Gaussian tail

For `R>=1`, let `I_R={-R,...,R}` and let `C_R` be the finite set of face patterns supported in
`I_R`. From (9), the absolute contribution of every pattern outside `C_R`, after division by the
common face magnitude and by `q^H`, is bounded uniformly in large `q` by

```text
epsilon_R
 <= C' sum_(r_1+...+r_D=S_tau, max|r_i|>R)
          (1+max|r_i|)^J exp(-B(sum_i r_i^2-Q_0)).           (10)
```

The lattice Gaussian with a polynomial weight is summable, so

```text
epsilon_R -> 0.                                             (11)
```

The lower-degree and larger-shift atoms omitted in Step 1 contribute `o(1)` after the same
normalization, uniformly in all phases.

### 4. Torsion recurrence exposes every finite Fourier coefficient

Choose an integer `m>D`. Fix `R` large enough that `A_0` is supported in `I_R`, and prescribe an
arbitrary phase state

```text
s=(s_r)_(r in I_R) in mu_m^(I_R).                           (12)
```

By torsion-language universality there is an unbounded sequence `q_j` on which
`u_(q_j+r)=s_r` for every `r in I_R`. Evaluate the normalized exact coefficient identity along
this sequence. Equations (8)--(11), with no assumption on the phases outside `I_R`, give

```text
|sum_(A in C_R) ell_A exp(-B(Q(A)-Q_0))
      product_(r in I_R)s_r^(m_A(r))|
 <= epsilon_R.                                              (13)
```

This holds for every state `s in mu_m^(I_R)`.

For `A in C_R`, the functions

```text
chi_A(s)=product_r s_r^(m_A(r))                              (14)
```

are distinct characters. Indeed, all multiplicities lie in `[0,D]`, and `m>D`, so congruence of
two exponent vectors modulo `m` implies equality of their ordinary multiplicity vectors.

Take the finite Fourier coefficient of (13) at the character `chi_(A_0)`. Character orthogonality
and the sup-norm bound give

```text
|ell_(A_0)| exp(-B(Q(A_0)-Q_0)) <= epsilon_R.                (15)
```

Now let `R->infinity`. The left side is a fixed positive number by (7), while the right side tends
to zero by (11), a contradiction. Therefore (2) cannot exist and `f` is HT. `square`

## Existence corollary `[PROVED HERE]`

For every `B>0`, the repeated diagonal concatenation of all finite root-of-unity words gives an
explicit deterministic phase sequence `u_n in mu_infinity` such that

```text
sum_(n>=0) exp(-B n^2)u_n z^n
```

is an entire HT function of quadratic logarithmic growth.

## Boundary attacks

1. **Bounded confinement is false and is not used.** Offsets of every fixed size remain on the
   Gaussian face. The proof controls the whole infinite face by the summable tail (10).
2. **No density or quantitative recurrence is required.** For each fixed finite phase state, an
   arbitrarily late subsequence is enough to pass to the normalized leading face. The exterior
   phases are discarded by absolute Gaussian summability.
3. **The character order is selected after the ADE degree.** Choosing `m>D` prevents aliasing of
   distinct degree-`D` multiplicity vectors.
4. **A fixed leading pattern is essential.** Normalization uses the maximal `q`-degree `H` and a
   fixed pattern with nonzero leading coefficient. Gaussian tail patterns whose leading weights
   tend to zero cannot supply the contradiction by themselves.
5. **The range below two remains open.** For `1<beta<2`, the fixed-offset quadratic cost is
   multiplied by `q^(beta-2)->0`; no fixed summable offset face remains after normalization.
6. **Theta-scale DA examples are not contradicted.** The theorem requires torsion-language
   universality. Classical theta and Valiron-type coefficients have highly constrained phase and
   offset structure.

## Parent and novelty status

- Valiron--Strelitz theory shows that order-zero entire DA functions exist from differential order
  three onward, so growth order alone does not imply this theorem.
- Classical theta and partial-theta theory supplies Gaussian coefficients with rigid functional
  equations; it does not supply maximal recurrent torsion phase language.
- Linear `q`-difference Galois theory proves HT for many particular partial-theta-type solutions,
  but the phase sequences here need satisfy no functional equation.
- Lipshitz--Rubel gap theorems concern support gaps; the present support is full.
- Generic phase HT does not prove that every torsion-language-universal phase tail is HT.
- Exact searches for Gaussian Taylor magnitudes with disjunctive or root-of-unity-universal phases,
  ADE coefficient faces, and differential transcendence found no theorem implying the result. The
  closest sources require a fixed linear difference equation, support gaps, algebraically
  independent coefficients, or arithmetic coefficients. Scientific novelty remains provisional
  pending specialist and independent proof review.

Primary comparisons:

1. G. Valiron, *Sur les fonctions entieres d'ordre nul et les equations differentielles*, Bull.
   Soc. Math. France 53 (1925), 34--42, https://eudml.org/doc/86494.
2. L. Lipshitz and L. A. Rubel, *A gap theorem for power series solutions of algebraic
   differential equations*, Amer. J. Math. 108 (1986), 1193--1213.
3. B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
   equations*, arXiv:1910.01874.
4. D. Gokhman, *Differentially transcendental formal power series*, Complex Variables 29 (1996),
   41--44, DOI `10.1080/17476939608814872`.
5. C. Krattenthaler and T. Rivoal, *Arithmetic properties of the Taylor coefficients of
   differentially algebraic power series*, arXiv:2502.09259.

## Exact RH-route scope

This theorem reaches the Gaussian coefficient scale native to theta and heat constructions, but it
does not reject the de Bruijn--Newman theorem or any complete RH criterion. It excludes only a
heat/theta implementation that simultaneously:

1. compresses its Gaussian full-support coefficient model into one finite ADE; and
2. retains a torsion-language-universal phase tail.

The theorem supplies no monotonic heat parameter, zero-line selector, positivity, or spectral
operator. Its role is to prove that maximal finite phase recurrence is incompatible with finite
differential memory even at the critical Gaussian scale.

## Lean status

No Lean formalization is claimed. Full formalization requires Mahler normalization, generic ADE
coefficient extraction, Gaussian degree/source-shift confinement, a uniform grouped-weight bound,
summability of polynomially weighted lattice Gaussian tails, torsion-language recurrence, and
finite-character Fourier inversion. The card cannot enter stage 3 until the entire unconditional
theorem is formalized.

## Gates

- [x] 0 -> 1: exact Gaussian face and finite-window attack stated.
- [x] 1 -> 2: complete unconditional paper proof written and boundary-attacked.
- [ ] Parent-theory and exact literature novelty audit.
- [ ] Independent proof audit.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Replaced failed bounded confinement at `beta=2` by the complete summable
  discrete-Gaussian ADE face and proved torsion-language-universal Gaussian HT.
