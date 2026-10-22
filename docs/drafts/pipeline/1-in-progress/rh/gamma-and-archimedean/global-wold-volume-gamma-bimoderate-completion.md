# Global Wold volume and Gamma bi-moderate completion

- **ID:** `global-wold-volume-gamma-bimoderate-completion`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper core) / CONJECTURE (source-effective enhanced completion)
- **Scientific status:** `[SOURCE-PURE CORE] [NEW TO CORPUS] [EXTERNAL NOVELTY UNVERIFIED]`
  `[NOT AN RH PROOF]`
- **RH used:** no
- **Computation used:** no
- **Parents:**
  `multiplicative-wold-gamma-anomaly-purity-rh.md`;
  `unit-exponential-wold-calderon-suspension.md`;
  `../2-fully-proven/new_scientific_knowledge/prime-occupation-polarized-gamma-phase-survival.md`;
  `../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/bv-prime-window-polar-coefficient-decimation-law.md`;
  `deninger-enhanced-adiabatic-milnor-calderon-vanishing-cycle.md`.
- **Statement:** The unused adjacent BV dilation step has exact off-multiple Laurent factor
  `1-r^(-1)`.  For `r=p` this equals the unit Wold fundamental-cell mass.  Their finite-prime
  product is the reciprocal prime-occupation first trace and gives a canonical global irregular
  coordinate whose two reflected exponential branches are simultaneously moderate only on the
  centered critical line.

## Goal

Construct the missing third completion: singular enough to retain every Xi conormal fibre, but
Hausdorff and contractive under every prime dilation.  The paper core below supplies a canonical
source parameter and the exact critical-line selector.  It does **not** yet prove that every Xi
conormal fibre enters both moderate branches; that source-effectivity theorem is the open core.

## 1. Adjacent dilation removes the square-index mismatch

Let `W` be a compactly supported BV prime window, let `r>=2` be an integer, and put

```text
W_j(x)=W(r^j x),
M_j(s)=integral_0^infinity W_j(x)x^(-s)dx,
T_j(N)=sum_(k>=1) Lambda(k)/sqrt(k) W_j(N/k),
p_j(N)=2M_j(3/2)sqrt(N)-2T_j(N).
```

The earlier reciprocal comparison used `j` and `j-2`, hence the square-index parameter `q=r^2`.
The full ladder has the stronger adjacent identity

```text
p_j(N)=p_(j-1)(rN).                                      (1)
```

Indeed, the prime terms agree term by term:

```text
T_(j-1)(rN)
 =sum_k Lambda(k)/sqrt(k) W(r^(j-1)rN/k)
 =T_j(N).
```

Also `M_j(3/2)=r^(1/2)M_(j-1)(3/2)` and
`sqrt(rN)=r^(1/2)sqrt(N)`, so the polar terms agree.  No continuation or zero data enter.

Let `D_r a(N)=a(rN)`, let `S_r` be inflation by zero away from multiples of `r`, and
`P_r=S_rD_r`.  Then `D_r p_(j-1)=p_j`.  The off-multiple coefficient

```text
c_(j-1)=(1-P_r)p_(j-1)
```

has Dirichlet series

```text
C_(j-1)(s)=F_(j-1)(s)-r^(-s)F_j(s).                     (2)
```

At an uncensored zeta zero `rho`, the established Mellin residue character is

```text
R_j(rho)=r^(rho-1/2) R_(j-1)(rho).
```

Substitution in `(2)` at `s=rho+1/2` gives the zero-independent split

```text
Res C_(j-1)
 =(1-r^(-(rho+1/2))r^(rho-1/2))R_(j-1)
 =(1-r^(-1))R_(j-1).                                    (3)
```

Thus choosing `r=p` for each prime is legitimate.  The previous apparent `p` versus `p^2`
mismatch came only from restricting attention to the reciprocal pair `j=1,-1`.

## 2. Exact Wold--BV local weld

For the multiplication-by-`p` coisometry, the Wold defect has density

```text
delta_p=1-p^(-1).
```

The unit exponential suspension gives the same number as its first-cell mass:

```text
integral_[0,log p] exp(-c) dc=1-p^(-1).                 (4)
```

Equations `(3)` and `(4)` identify one and the same source quantity in three roles:

1. off-`p`-multiple BV Laurent residue fraction;
2. multiplication-Wold defect density;
3. unit-exponential Calderón fundamental-cell mass.

This is an operator/source identification, not a scalar Gamma coincidence.

## 3. Finite-prime global volume

For a finite set of primes `S`, define

```text
epsilon_S=product_(p in S)(1-p^(-1)).                   (5)
```

Unique prime occupation and finite products of geometric series give

```text
Z_S(1)
 =sum_(nu:S ->_0 N) product_(p in S)p^(-nu_p)
 =product_(p in S)(1-p^(-1))^(-1)
 =epsilon_S^(-1).                                       (6)
```

Hence `epsilon_S` is simultaneously:

- product Wold boundary volume;
- iterated off-multiple BV residue fraction;
- critical finite Möbius-vacuum mass;
- reciprocal finite prime-occupation first moment.

This equality is exact at every finite stage.

## 4. Canonical irregular factor

Let `G_(g,S)(t)` denote the finite-prime multiple-elliptic-Gamma product in genus `g`.  The
established scheme-change theorem and `(6)` give

```text
G_(1,S)(t)/G_(1,S)(-t)
 =exp(2t/epsilon_S) G_(0,S)(t)/G_(0,S)(-t).             (7)
```

Equivalently, the raw reflected phase is

```text
G_(0,S)(t)/G_(0,S)(-t)
 =exp(-2t/epsilon_S) R_S(t),                            (8)
```

where `R_S` is the tangent-normalized phase.  Reflection gives the opposite exponential branch:

```text
G_(0,S)(-t)/G_(0,S)(t)
 =exp(2t/epsilon_S) R_S(-t),    R_S(-t)=R_S(t)^(-1).    (9)
```

Euler divergence at `1` implies `epsilon_S -> 0+` along cofinal finite prime sets.

## 5. Bi-moderate critical-line selector

For `epsilon>0`,

```text
|exp(-2t/epsilon)|=exp(-2 Re(t)/epsilon),
|exp( 2t/epsilon)|=exp( 2 Re(t)/epsilon).               (10)
```

The negative branch is polynomially moderate as `epsilon -> 0+` only if `Re(t)>=0`; the reflected
positive branch is polynomially moderate only if `Re(t)<=0`.  Therefore

```text
both reflected branches polynomially moderate
  iff Re(t)=0.                                          (11)
```

With `t=s-1/2`, `(11)` selects exactly `Re(s)=1/2`.  This is the first corpus mechanism whose
critical selector is produced by the divergent prime first trace itself rather than inserted as a
positivity, norm, or zero-location hypothesis.

## 6. Bold completion conjecture

**SOURCE-EFFECTIVE BI-MODERATE XI TRANSgression.**  There exists a Hausdorff enhanced
Wold--BV--Gamma completion over the boundary parameter `epsilon_S -> 0+` such that:

1. finite prime dilation, off-multiple BV conormal maps, and the polarized Gamma determinant
   descend from their literal source maps;
2. every nontrivial Xi conormal jet has a nonzero image in both reflected enhanced branches;
3. source sections are required to be polynomially moderate in both branches;
4. no divisor-selected weights, zero-location assumptions, or RH-equivalent contractivity are
   used in constructing the completion.

If this conjecture is proved, `(11)` forces every nontrivial zero onto the critical line.

## 7. Hostile audit

1. **Gamma alone does not select zeros.**  Equations `(7)--(11)` are scalar until the Xi conormal
   map is source-constructed and conservative.
2. **Functional equation alone is insufficient.**  It may pair two separate one-sided objects
   without forcing one fibre to inhabit both.
3. **Hida/white-noise duals are too large.**  Exponential characters of both signs remain
   continuous, including off-line characters.
4. **Ordinary Dirichlet--Hardy space is too small.**  It loses the Laurent fibres.
5. **The reciprocal BV pair is not prime-local.**  Its two-step density is `1-r^(-2)`.  Only the
   adjacent ladder theorem `(1)--(3)` supplies `1-p^(-1)`.
6. **Finite hypertranscendence is insufficient.**  All-prime unpolarized completion can collapse
   to a differential-algebraic sine factor; the polarized Gamma phase survives, but survival is
   not conservativity.
7. **Circularity falsifier.**  Retire the completion if “both branches moderate” is imposed only
   on divisor fibres, or if continuity of Xi evaluation is assumed rather than derived from the
   prime source.
8. **Generalized-prime falsifier.**  Retire the selector if an explicit off-line generalized-prime
   Euler system carries the same literal integer-multiplication, adjacent off-multiple,
   first-trace, polarized-Gamma, and bi-moderate conormal package.

## Literature boundary

Preliminary exact-phrase and structural searches found Wold decomposition, arithmetic
co-Poisson/Sonine spaces, Gamma/Fredholm determinants, and enhanced irregular
Riemann--Hilbert theory, but no source identifying `(3)--(9)` or proving the conjectured
Xi transgression.  The elementary adjacent decimation identity itself is not claimed as novel.
External novelty remains unverified until a targeted primary-source audit is complete.

## Gates

- [x] adjacent finite coefficient identity paper-proved
- [x] adjacent off-multiple Laurent factor paper-proved
- [x] exact local Wold--BV--Calderón weld paper-proved
- [x] finite-prime global parameter and Gamma irregular factor derived
- [x] hostile `p` versus `p^2` mismatch resolved
- [ ] formalize `(1)--(4)` unconditionally in Lean
- [ ] formalize finite-prime first-moment identity `(6)`
- [ ] formalize finite-stage Gamma factorization `(7)--(9)`
- [ ] define enhanced bi-moderate source category without divisor data
- [ ] prove source-effective Xi conormal transgression
- [ ] complete unconditional RH proof

## Log

- 2026-07-28 — Created after adjacent-step audit resolved the square-index obstruction.
