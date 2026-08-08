# Möbius right inverse and exact Poisson-range classification

- **ID:** `deninger-mobius-right-inverse-poisson-range-classification`
- **Stage:** 2-fully-proven
- **Type:** CLASSICAL MÖBIUS INPUT / PROJECT-SPECIFIC EXACT RANGE CLASSIFICATION
- **Labels:**
  - `DAC_DENINGER_MOBIUS_POINTWISE_RIGHT_INVERSE`;
  - `DAC_DENINGER_MOBIUS_REGULARITY_POISSON_RANGE_CLASSIFICATION`;
  - `DAC_DENINGER_REFLECTED_GRAPH_MOBIUS_INCIDENCE_CLASSIFICATION`.
- **Parent:** `DAC_DENINGER_CORRECTED_TATE_FLOQUET_POISSON_DESCENT`
- **Inputs:**
  - Meyer's strict Poisson embedding $Z:H_\cap\hookrightarrow H_-$;
  - the already-formalized left Möbius inversion on $Z(H_\cap)$;
  - `DAC_DENINGER_COFINAL_FLOQUET_SECONDARY_POISSON_GRAPH`.
- **Novelty status:** **not new scientific knowledge.** Pointwise right inversion is elementary
  Dirichlet/Möbius inversion and belongs to classical Müntz/co-Poisson calculus. The
  project-specific $H_\cap$ regularity and reflected-graph formulations below are frontier
  bookkeeping consequences, not claimed as external novelty.
- **Claim:** every Meyer cochain has a canonical pointwise Möbius preimage on the positive radial
  line, and Poisson summation of that preimage returns the cochain exactly. Membership in the
  literal Poisson boundary range is therefore equivalent to one concrete condition: the canonical
  Möbius preimage extends through the radial origin as a member of $H_\cap$. On the reflected
  two-collar graph, this same regularity condition is exactly the missing Poisson-range incidence.

## 1. Canonical Möbius preimage

Let
\[
 H_-=\mathscr S_{\exp}(\mathbb R)
\]
and for $h\in H_-$ write its positive radial profile as
\[
 H_h(x)=h(\log x),\qquad x>0.
\tag{1}
\]
It decays faster than every power at both $0$ and $+\infty$. Define, pointwise for $x>0$,
\[
 (\mathfrak M_\mu h)(x)
 =\sum_{n\ge1}\mu(n)H_h(nx).
\tag{2}
\]

`[PROVED HERE] [DAC_DENINGER_MOBIUS_POINTWISE_RIGHT_INVERSE]`

For every $h\in H_-$ and $x>0$, series `(2)` converges absolutely. Moreover the double series
\[
 \sum_{m,n\ge1}|H_h(nmx)|
\tag{3}
\]
is finite and
\[
 \sum_{m\ge1}(\mathfrak M_\mu h)(mx)=H_h(x).
\tag{4}
\]

### Proof

Fix $x>0$ and choose $A>2$. There is $C_A$ such that
$|H_h(y)|\le C_Ay^{-A}$ for $y\ge1$. Only finitely many pairs $(m,n)$ satisfy $mnx<1$, while
\[
 \sum_{mnx\ge1}|H_h(mnx)|
 \le C_Ax^{-A}\sum_{m,n\ge1}m^{-A}n^{-A}<\infty.
\tag{5}
\]
This proves `(3)` and hence absolute convergence of `(2)`. Absolute rearrangement and the Dirichlet
convolution identity $\sum_{n\mid k}\mu(n)=\mathbf1_{k=1}$ give
\[
 \begin{aligned}
 \sum_{m\ge1}(\mathfrak M_\mu h)(mx)
 &=\sum_{m,n\ge1}\mu(n)H_h(nmx)\\
 &=\sum_{k\ge1}\left(\sum_{n\mid k}\mu(n)\right)H_h(kx)
 =H_h(x).
 \end{aligned}
\]
This is `(4)`. No estimate for the Mertens function and no hypothesis on zeta zeros is used.

The point is the direction of `(4)`: the corpus had already formalized
$\mathfrak M_\mu(Zf)=f$ for $f\in H_\cap$. Formula `(4)` proves that the same canonical transform
is also a pointwise right inverse of positive Poisson summation on every $H_-$ cochain, although
its output need not have acceptable behavior at the radial origin.

## 2. Exact range as a regularity domain

Let $E\mathfrak M_\mu h$ denote the even extension of `(2)` to $\mathbb R\setminus\{0\}$, with
value $0$ prescribed at the origin when such an extension is regular. Define the maximal regular
Möbius domain
\[
 \mathscr D_\mu
 =\{h\in H_-:E\mathfrak M_\mu h\text{ extends as a member of }H_\cap\}.
\tag{6}
\]

`[PROVED HERE] [DAC_DENINGER_MOBIUS_REGULARITY_POISSON_RANGE_CLASSIFICATION]`

One has the exact equality
\[
 \boxed{\ \mathscr D_\mu=Z(H_\cap).\ }
\tag{7}
\]
On this domain, $E\mathfrak M_\mu$ is the inverse of $Z$. Consequently $\mathscr D_\mu$ is closed
in the nuclear Meyer topology and the inverse
\[
 E\mathfrak M_\mu:\mathscr D_\mu\longrightarrow H_\cap
\tag{8}
\]
is continuous.

### Proof

If $h=Zf$ with $f\in H_\cap$, the existing left Möbius-inversion theorem gives
$\mathfrak M_\mu h=f$ on $x>0$; evenness and $f(0)=0$ give the extension in `(6)`. Hence
$Z(H_\cap)\subseteq\mathscr D_\mu$.

Conversely, suppose $h\in\mathscr D_\mu$ and put $f=E\mathfrak M_\mu h\in H_\cap$. Formula `(4)`
says $Zf(x)=H_h(x)$ for every $x>0$, hence the logarithmic Poisson cochain $Zf$ equals $h$.
Therefore $h\in Z(H_\cap)$, proving `(7)`. Closedness and continuity of `(8)` follow from the
already-proved strict closed embedding $Z:H_\cap\to H_-$.

This is not the false assertion that `(2)` maps all of $H_-$ to $H_\cap$. It generally need not:
absolute estimates lose cancellation as $x\downarrow0$. Precisely that endpoint regularity loss
supports the nonzero quotient $M_\zeta$.

## 3. Exact incidence inside the reflected Calderón graph

For $h\in H_-$ put
\[
 (Jh)(t)=e^{-t}h(-t).
\tag{9}
\]
Every pair in the reflected graph has the unique form $(h,Jh)$. Define the Möbius-regular part of
that graph by
\[
 \Gamma_{\mathrm{sec}}^{\mu\text{-reg}}
 =\{(h,Jh):h\in\mathscr D_\mu\}.
\tag{10}
\]

`[PROVED HERE] [DAC_DENINGER_REFLECTED_GRAPH_MOBIUS_INCIDENCE_CLASSIFICATION]`

The regular part is exactly the literal two-collar Poisson boundary graph:
\[
 \boxed{\Gamma_{\mathrm{sec}}^{\mu\text{-reg}}
 =\{(Zf,Z\widehat f):f\in H_\cap\}.}
\tag{11}
\]

Indeed, `(7)` writes $h=Zf$. Meyer--Poisson reflection gives $Jh=Z\widehat f$, proving one
inclusion; the same reflection and left Möbius inversion prove the other.

Thus the abstract incidence requested previously is now explicit at set level:
\[
 \text{Poisson incidence}
 \quad\Longleftrightarrow\quad
 E\mathfrak M_\mu h\in H_\cap.
\tag{12}
\]
What remains open is not range identification. It is construction of the **singular regularity
defect** of `(2)` as a continuous Gamma/co-Poisson Green--Stokes operator on the full nuclear source,
with a positive weight-one norm and real-Fourier covariance. Defining a quotient by `(6)` would
merely rename $M_\zeta$ and does not solve that problem.

## 4. Conjecture loop

1. **Conjecture: Möbius inversion is available only after assuming a Poisson preimage.**
   **Failed by `(3)`--`(4)`.** It is a pointwise right inverse on every Meyer cochain.
2. **Conjecture: reconstruction failure distinguishes nonboundaries.**
   **Failed.** Reconstruction `(4)` is automatic. Only extension through the radial origin with
   the exact $H_\cap$ endpoint/Fourier conditions distinguishes the range.
3. **Conjecture: reflected-graph incidence remains unspecified.**
   **Refined and proved set-theoretically by `(11)`--`(12)`.** It is canonical Möbius regularity.
4. **Conjecture: declare the maximal regularity domain and quotient.**
   **Rejected as theatre.** That recovers the already-known quotient without its source Green
   operator, positivity, or covariance. Missing knowledge is the singular regularity-defect
   realization, not the set equality.

## 5. Hostile audit

- **No RH premise.** Only rapid decay, absolute rearrangement, and finite divisor Möbius inversion
  enter `(4)`.
- **No hidden surjectivity.** Right inversion is pointwise on $x>0$; membership in $H_\cap$ is
  explicitly not automatic.
- **No quotient relabeling claim.** Equality `(7)` is a range classification. It does not claim a
  new Hodge form.
- **Existing corpus and literature separated from project consequence.** Left inversion on
  $Z(H_\cap)$ and Poisson reflection were already formalized. Right inversion is classical
  Dirichlet/Möbius calculus; `(7)` and `(11)` record its exact consequence for the already-fixed
  Route-L spaces.
- **No Lean claim.** Lean corpus was inspected read-only during refactor.

## References

- Jean-François Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007),
  arXiv:math/0407443.
- Semyon Yakubovich, *New summation and transformation formulas of the Poisson, Müntz, Möbius and
  Voronoi type*, arXiv:1410.7934.

## Gates

- [x] 0 → 1 in-progress: exact transform, convergence, and falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed proof `(1)`--`(12)`
- [ ] 2 → 3 formalized: paused during Lean corpus refactor
- [ ] 3 → 4 publication-ready

## Log

- 2026-08-08 — Extended corpus left Möbius inversion to a pointwise right inverse on every Meyer
  cochain; proved exact Poisson-range and reflected-graph regularity classifications. Narrowed open
  core to Gamma/co-Poisson realization of the singular endpoint/Fourier defect.
- 2026-08-08 — Novelty audit located classical Müntz/co-Poisson and Möbius-transform literature;
  relabeled the inversion theorem as not new scientific knowledge. Retained only its exact Route-L
  frontier consequence.
