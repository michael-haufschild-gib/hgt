# Möbius right inverse and exact Poisson-range classification

- **ID:** `deninger-mobius-right-inverse-poisson-range-classification`
- **Stage:** 3-formalized
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
- **Lean claim, unconditional.** See the Lean status section below: `(3)`, `(4)`, `(7)`, `(8)`,
  `(11)` and `(12)` are theorems with axiom audit `propext, Classical.choice, Quot.sound`.

## References

- Jean-François Burnol, *Entrelacement de co-Poisson*, Ann. Inst. Fourier 57 (2007),
  arXiv:math/0407443.
- Semyon Yakubovich, *New summation and transformation formulas of the Poisson, Müntz, Möbius and
  Voronoi type*, arXiv:1410.7934.

## Gates

- [x] 0 → 1 in-progress: exact transform, convergence, and falsifiers fixed
- [x] 1 → 2 fully-proven: dependency-closed proof `(1)`--`(12)`
- [x] 2 → 3 formalized: every `[PROVED HERE]` statement is an unconditional Lean theorem
- [ ] 3 → 4 publication-ready

## Lean status — FORMALIZED, unconditional

Two new modules, both wired into `GaloisForLFunctions.RHTower`, both checked with
`lake env lean` and `lake build`; axiom audit for every declaration named below is exactly
`propext, Classical.choice, Quot.sound`.  Nothing is assumed: no hypothesis, no `sorry`, no added
axiom.

### `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMobiusPoissonRangeClassification.lean`

```text
deningerLogPull_double_summable                 (3)  ∑_{m,n≥1} ‖H_h(mnx)‖ < ∞
DeningerMobiusRegularDomain                     (6)  𝒟_μ
mem_deningerMobiusRegularDomain_iff                  positive-ray form of membership
deningerPoissonSource_eq_of_ray                      a regular Möbius preimage is a Poisson preimage
deningerMobiusRegularDomain_eq_poissonRange     (7)  ** 𝒟_μ = Z(H_∩) **
deningerMobiusRegularDomain_existsUnique             E𝔐_μ inverts Z on 𝒟_μ, uniquely
deningerPoissonIncidence_iff                   (12)  Poisson incidence ⟺ E𝔐_μ h ∈ H_∩
DeningerReflectedGraphMuRegular                (10)  Γ_sec^{μ-reg}
DeningerPoissonBoundaryGraph                         {(Zf, Z ℱf) : f ∈ H_∩}
deningerReflectedGraphMuRegular_eq             (11)  ** the two graphs are equal **
DeningerMobiusRegularDomainMeyer                     𝒟_μ inside the nuclear Meyer source
deningerMobiusRegularDomainMeyer_eq_range            it is the image of the Poisson operator
deningerPoissonMeyerRange_carrier                    the same, as a submodule carrier
deningerMobiusRegularDomainMeyer_isClosed       (8)  ** 𝒟_μ is closed in the Meyer topology **
deningerPoissonMeyerRangeEquiv_symm_eq_mobiusExtension
                                                     the continuous inverse *is* E𝔐_μ
deningerMobiusRegularDomain_inverse_continuous  (8)  ** E𝔐_μ : 𝒟_μ → H_∩ is continuous **
```

`(2)` and `(4)` were already in the tree and are reused verbatim:
`deningerMobiusRay_summable` (absolute convergence of `∑_n μ(n) H_h(nx)` on every positive ray) and
`deningerMobius_rightInverse` (`∑_{m≥1} (𝔐_μ h)(mx) = H_h(x)`, the pointwise right inverse), in
`RHTower/Deninger/DeningerMobiusPreimage.lean` and `RHTower/Deninger/DeningerMobiusRightInverse.lean`; the left
inversion `𝔐_μ(Zf) = f` is `deningerMobiusPreimage_poissonSource` and the Meyer--Poisson reflection
`J(Zf) = Z(ℱf)` is `deningerCollarExchange_poissonSource`, both in
`RHTower/Deninger/DeningerPoissonPreimage.lean`.  `J` is the corpus's `deningerCollarExchange`, whose
defining formula `deningerCollarExchange_apply` is literally `(Jh)(t) = e^{-t}h(-t)`, i.e. `(9)`.

### `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerStrictEmbedding.lean`

`(8)` is the only part of the card that is not purely algebraic: it asserts closedness and inverse
continuity **for the nuclear Meyer topology**, while the corpus's strictness and closed-range
theorems for `Z` were stated against the *radial* presentation (the family of all integer
exponential weights, topologised inside a countable product of Schwartz spaces).  This module builds
the missing bridge and is reusable well beyond this card.

```text
deningerMeyerSeminormFun_mono                   q_{A,n} increases with the exponent
deningerExpMulExponent, deningerPow_mul_exp_le  ‖t‖^k e^{ct} ≤ k!·e^{⌈1+|c|⌉|t|}
deningerExpMul_seminorm_le           ** p_{k,n}(e^{ct}h) ≤ Σ_j C(n,j)|c|^j k! q_{⌈1+|c|⌉,n-j}(h) **
deningerExpMulSchwartzLM                        e^{ct}· as a map H_- → 𝒮(ℝ)
deningerExpMulSchwartzLM_continuous  ** it is continuous for the Meyer topology **
deningerRadialLM                                h ↦ (e^{st}h)_{s∈ℤ}, into the radial space
deningerRadialLM_continuous          ** the radial presentation is continuous **
deningerPoissonMeyerLM                          Z, with the Meyer topology on the target
deningerRadialLM_poissonMeyer                   its radial presentation is the radial Poisson datum
deningerPoissonMeyer_range_isClosed  ** Z(H_∩) is closed in the Meyer topology **
exists_bound_schwartzSup_expMul, exists_bound_sum_schwartzSup_expMul
deningerPoissonSchwartz_eq_expMul               the s-th radial datum of Zf is e^{st}·Zf
deningerPoissonMeyer_strict          ** p_{k,n}(f) ≤ C·sup_T q(Zf): Z is strict for Meyer **
deningerMeyerCap_withSeminorms, deningerPoissonMeyerRange_withSeminorms
deningerPoissonMeyerRangeEquiv                  Z as an isomorphism onto its image
deningerPoissonMeyerRangeEquiv_symm_continuous  ** the inverse is continuous **
```

The mechanism of the bridge is one estimate.  Multiplication by `e^{ct}` carries `H_-` into the
Schwartz space, and Leibniz expands `D^n(e^{ct}h)` into `Σ_j C(n,j)|c|^j e^{ct} D^{n-j}h`; the power
weight `‖t‖^k` is absorbed by `‖t‖^k ≤ k!e^{|t|}`, so one extra unit of Meyer exponent pays for both
the power and the exponential factor.  Closedness then costs nothing: `Z(H_∩)` is the preimage,
under the continuous radial presentation, of the already-proved closed radial Poisson image.
Inverse continuity is the corpus's radial strictness `exists_bound_seminorm_radial` composed with
the same estimate.

### Scope, honestly

What is formalized is exactly what the card proves.  The open core the card names — a continuous
Gamma/co-Poisson Green--Stokes realization of the **singular regularity defect** of `(2)` on the
full nuclear source, with a positive weight-one norm and real-Fourier covariance — is untouched
here and remains open; the set-level range classification does not address it, as `§4.4` already
records.

## Log

- 2026-08-08 — Extended corpus left Möbius inversion to a pointwise right inverse on every Meyer
  cochain; proved exact Poisson-range and reflected-graph regularity classifications. Narrowed open
  core to Gamma/co-Poisson realization of the singular endpoint/Fourier defect.
- 2026-08-08 — Novelty audit located classical Müntz/co-Poisson and Möbius-transform literature;
  relabeled the inversion theorem as not new scientific knowledge. Retained only its exact Route-L
  frontier consequence.
- 2026-08-18 — **Stage 3.** Formalized `(3)`, `(7)`, `(8)`, `(11)`, `(12)` unconditionally in Lean,
  reusing the tree's `(2)`, `(4)`, left inversion and Poisson reflection. Built the missing
  Meyer-topology half of the strict closed embedding `Z : H_∩ → H_-`
  (`DeningerMeyerStrictEmbedding.lean`), which the card's `(8)` needs and which the corpus had only
  in the radial presentation.
