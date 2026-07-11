# The canonical source form for the Hedenmalm theta pair is Weil polarization

- **ID:** `hedenmalm-pair-weil-polarization-law`
- **Stage:** 2-fully-proven / needs full literature audit
- **Type:** THEOREM (paper) / DIRECT HILBERT--POLYA--WEIL IDENTIFICATION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Statement:** The completed Weil explicit-formula distribution polarizes to an unconditional
  source-defined sesquilinear form which makes Hedenmalm's 2026 theta differential pair formally
  self-adjoint.  Its positivity is exactly the Weil RH criterion, while its nondegeneracy on the
  theta eigenfunction span is exactly RH plus simplicity of every zeta zero.

## 1. Centered divisor and the Weil distribution

For every nontrivial zero `rho` of `zeta`, including multiplicity, put

```text
alpha_rho=(rho-1/2)/i.                                    (1)
```

Thus `alpha_rho` is real exactly when `rho` lies on the critical line.  Functional equation and
Schwarz symmetry make the centered divisor invariant under

```text
alpha |-> -alpha,
alpha |-> conjugate(alpha).                               (2)
```

Let `A_W` be any standard `#`-stable Weil test algebra of entire functions, with sufficient decay
in a horizontal strip to justify the completed explicit formula.  For `F in A_W`, put

```text
F#(z)=conjugate(F(conjugate(z))).                          (3)
```

The zero-side Weil distribution is

```text
W(F)=sum_rho m_rho F(alpha_rho).                           (4)
```

The completed explicit formula gives the same functional from

```text
the full prime-power von Mangoldt tail
  + the Gamma/digamma archimedean term
  + the pole and normalization terms.                     (5)
```

Equation `(5)`, rather than `(4)`, is its source presentation.

## 2. Polarized source form

For source vectors `u,v` whose Fourier transforms and polarized products are in `A_W`, define

```text
F_u(z)=hat u(z),

q_W(u,v)=W(F_u F_v#)
        =sum_rho m_rho F_u(alpha_rho)F_v#(alpha_rho).      (6)
```

This is a Hermitian sesquilinear form because of the divisor symmetries `(2)`.  It is defined
unconditionally; away from RH it need not be positive.

Let

```text
k(x)=2 VarTheta_00(i exp(2x)),
D=-i partial_x,
L=k D k^(-1).                                              (7)
```

The factor `2` corrects the normalization of the displayed theta-Mellin identity in the June 2026
preprint and changes `-log k` only by a constant, so `L` is unchanged.  Riemann's theta formula then
gives

```text
F_k(z)=Xi(z),
Lk=0.                                                      (8)
```

## 3. The Weil form descends through the theta constraint `[PROVED HERE]`

Since every `alpha_rho` is a zero of `Xi`, equations `(6)` and `(8)` give

```text
q_W(k,v)=q_W(v,k)=0                                       (9)
```

for every admissible `v`.  The smooth kernel of `L` is `C k`.  Therefore

```text
q_2(Lu,Lv):=q_W(u,v)                                      (10)
```

is independent of the chosen preimages and defines a sesquilinear form on the algebraic source
range of `L`.

This is the exact quotient required by Hedenmalm's seminorm proposal: the theta source vector is
null because it is the constraint vector whose Fourier transform vanishes on the completed
divisor.

## 4. Formal self-adjointness is automatic `[PROVED HERE]`

With the Fourier convention above,

```text
F_(Du)(z)=-z F_u(z),
F_(Dv)#(z)=-z F_v#(z).                                    (11)
```

Hence `(6)` gives

```text
q_W(Du,v)=q_W(u,Dv).                                      (12)
```

Using `(10)`, this is exactly

```text
q_2(LDu,Lv)=q_2(Lu,LDv).                                  (13)
```

Thus the Hedenmalm pair `(L D,L)` is unconditionally self-adjoint with respect to the polarized
Weil form as an algebraic Hermitian form.  The open issue is not symmetry.  It is whether `(6)` is
positive and whether `(10)` is nondegenerate on the theta eigenfunctions.

## 5. Positivity is exactly RH `[PROVED; CLASSICAL WEIL INPUT]`

For `u=v`,

```text
q_W(u,u)=W(F_u F_u#).                                     (14)
```

If RH holds, every `alpha_rho` is real and

```text
q_W(u,u)=sum_gamma m_gamma |F_u(gamma)|^2>=0.             (15)
```

Conversely, Weil's positivity criterion says that nonnegativity of `(14)` on a sufficiently rich
completed test algebra implies RH.  Therefore

```text
RH iff q_W is nonnegative on the Weil source core.         (16)
```

The prime and archimedean expression `(5)` makes `(16)` a source theorem.  It does not require the
zeros to be listed before the form is defined.

## 6. Eigenfunction norm and the simplicity threshold `[PROVED HERE]`

For a zero parameter `alpha`, normalize the eigenfunction to be twice Hedenmalm's displayed
solution.  This harmless scalar choice matches the normalized kernel in `(7)` and gives

```text
(D+alpha)u_alpha=-i k.                                    (17)
```

Fourier transformation and `(8)` give the entire removable quotient

```text
F_(u_alpha)(z)=-i Xi(z)/(alpha-z).                        (18)
```

This quotient lies in the required completed explicit-formula class.  Indeed, removal at `alpha`
makes it entire, while Stirling's formula for the completed Gamma factor and the standard
polynomial vertical bounds in every fixed `s`-strip give, uniformly on closed horizontal
`z`-strips,

```text
Xi(z)/(alpha-z)
 =exp(-pi |Re z|/4) (1+|z|)^O(1).                         (18a)
```

The polarized product of two such quotients therefore has exponential real-direction decay and
is an admissible Guinand--Weil test function.  Thus both the zero-side and the prime-plus-Gamma
source side of `(6)` apply to the eigenfunction calculations below.

At any centered zero `beta`,

```text
F_(u_alpha)(beta)=0                         if beta!=alpha,
F_(u_alpha)(alpha)=i Xi'(alpha).                          (19)
```

If `alpha` is nonreal, then `conjugate(alpha)` is a distinct zero.  Consequently

```text
F_(u_alpha)#(alpha)
 =conjugate(F_(u_alpha)(conjugate(alpha)))=0,              (20)
```

and `(6)` gives

```text
q_W(u_alpha,u_alpha)=0.                                   (21)
```

If `alpha` is real, equations `(6)` and `(19)` instead give

```text
q_W(u_alpha,u_alpha)=m_alpha |Xi'(alpha)|^2.              (22)
```

Thus a multiple real zero is also null.  For distinct real zeros, the corresponding
eigenfunctions are orthogonal.

It follows that `(10)` is positive definite on the finite span of all nonzero theta
eigenfunctions if and only if

```text
every zeta zero lies on the critical line,
every zeta zero is simple.                                (23)
```

Equivalently,

```text
Hedenmalm--Weil Hilbert metric on the full eigen-span
  iff RH + simplicity.                                    (24)
```

## 7. Positive carrier law

The 2026 theta boundary-value problem already supplies the exact completed trace and the
eigenfunction equation.  The present theorem supplies its canonical source form.  A viable direct
Hilbert--Polya proof in this architecture must therefore establish two increasingly strong facts:

```text
Weil positivity of q_W              -> RH,
conservativity on theta eigenvectors -> RH + simplicity.   (25)
```

There is no missing local integration weight to guess.  The metric must be the nonlocal
prime--Gamma incidence `(5)` polarized as in `(6)`, or another divisor-supported weighting from
the classification in `hedenmalm-theta-pair-divisor-supported-metric-law.md`.

At finite prime cutoff `N`, a genuine approximation must retain at least `pi(N)` independent prime
phases, approximate the prime side of `(5)`, and converge to `(6)` in a topology strong enough to
preserve its divisor atoms.  Finite positivity alone does not give `(16)`; cofinal Weil positivity
is exactly the required transfer theorem.

## 8. Relation to the trace-class RVM skeleton

`prime-indexed-rvm-trace-class-hp-normal-form.md` constructs the marked prime-space smooth
Riemann--von Mangoldt operator `Q`.  Under RH, its atomic quantile measure is relocated to the exact
measure in `(15)` by a trace-class correction in reciprocal coordinates.

The two descriptions are the same missing incidence viewed from opposite sides:

```text
operator side: Q + source-defined trace-class relocation,
metric side:   source-defined positive Weil polarization. (26)
```

Either construction must carry the full prime source through the finite Gamma boundary and land on
the exact completed divisor.

## 9. Attacks and exact boundary

1. **No RH is hidden in formal symmetry.**  Equations `(9)`--`(13)` are unconditional.  The sign of
   the form is precisely the classical open content.
2. **The source presentation is essential.**  Defining `(6)` only by the zero sum is target-side.
   The explicit formula `(5)` supplies the prime-plus-completion definition.
3. **The test algebra matters.**  The equivalence `(16)` uses a standard class rich enough for
   Weil's criterion.  A finite or compact strict-positive test family is insufficient.
4. **Positivity does not imply simplicity.**  Under RH, `(15)` is positive even with repeated
   atoms.  Nondegeneracy on Hedenmalm's particular eigenfunctions adds the derivative condition in
   `(22)`.
5. **A quotient is not automatically a Hilbert space.**  One must complete `(10)` only after
   positivity and identify its radical.  Off-line and multiple-zero eigenfunctions lie in that
   radical by `(21)`--`(22)`.
6. **No finite-Gamma rank substitution occurs.**  The Gamma term in `(5)` contributes the one
   archimedean direction; the infinite prime-power tail supplies the separate arithmetic carrier.
7. **Hilbert completion remains analytic work.**  The polarized eigenfunction quotients are
   admissible by `(18a)`, so the algebraic theorem is closed.  A realized unbounded operator still
   requires closability and a description of the completed positive-form domain under RH.

## 10. Parent and novelty audit

Primary parents are:

1. H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494 (June 2026),
   for `(2)`, `(7)`, `(8)`, and `(17)`;
2. Weil's explicit formula and positivity criterion for `(4)`--`(6)` and `(16)`;
3. the standard polarization `F G#` of the Weil quadratic form.

Hedenmalm does not mention the Weil criterion, construct the form `(10)`, or compute the exact
norm `(22)`.  Searches through 11 July 2026 did not locate the identification of his proposed
self-adjoint pair form with polarized Weil positivity, nor the resulting RH-plus-simplicity
nondegeneracy law.

The classical ingredients are substantial, so novelty attaches only to their exact application to
the June 2026 theta pair.  The result is mathematically significant because it resolves the shape
of the proposed metric and identifies its precise open content, but remains
`[NOVELTY UNVERIFIED]` pending specialist review of contemporaneous work.

## Lean status

`formal/GaloisForLFunctions/RHTower/XiWeilPolarization.lean` now constructs the multiplicity-exact
zero-side Weil polarization on the actual centered Xi divisor. Functional-equation reflection and
Schwarz conjugation are lifted to the divisor-copy index and prove the Hermitian identity without
RH. The module also proves unconditionally that multiplication by the centered spectral coordinate
is formally symmetric, that `XiC` lies in both radicals, and that adding a multiple of `XiC` to
either preimage leaves the form unchanged. Under RH, every square-summable diagonal is identified
exactly with the nonnegative atomic Gram sum. For every actual zero `alpha`, Lean proves that the
divisor-copy fiber is finite and nonempty, sums the eigenfunction diagonal to
`m_alpha * ||XiC'(alpha)||^2`, proves that this norm vanishes exactly at a multiple zero, and proves
orthogonality for distinct zero parameters. The same module defines the removable entire
Hedenmalm quotient as `i * dslope XiC alpha`, proves its literal quotient formula away from
`alpha`, its value `i XiC'(alpha)` at the removed point, and its exact vanishing at every distinct
divisor copy.

`formal/GaloisForLFunctions/RHTower/XiWeilResolventSource.lean` supplies a first genuine
prime-plus-Gamma realization on a concrete infinite Weil test core. For the Cauchy tests
`C_z(a)=(a-z)^(-1)`, Lean proves absolute summability and the exact polarized identity

```text
q_W(C_z,C_w)
  = (T(conj(w))-T(z))/(z-conj(w)),
```

where `T` is the multiplicity-exact Xi relative resolvent trace. It then replaces both copies of
`T` by the unordered von-Mangoldt `LSeries` plus the fixed archimedean/boundary term on the
absolute-convergence half-plane, and by the continued prime carrier plus the same archimedean term
on the natural pole-free domain. These identities use the existing source theorem
`primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace`; no zero enumeration or prime cutoff is
introduced.

The result is closed under finite Cauchy packets: for
`F=sum_z c_z C_z` and `G=sum_w d_w C_w`, the same file proves the exact sesquilinear double sum

```text
q_W(F,G)
 = sum_z sum_w c_z conjugate(d_w)
   * (T(conjugate(w))-T(z))/(z-conjugate(w)),
```

and substitutes the prime--Gamma source for every entry, in both source domains. Thus the
formalized source core is an actual finite-dimensional resolvent test algebra, not only one
isolated kernel identity.

`formal/GaloisForLFunctions/RHTower/XiWeilHilbertCore.lean` now realizes every square-summable
divisor evaluation as an actual `ell^2` vector. Under RH, Lean identifies the Weil polarization
exactly with the Hilbert inner product (with the argument order dictated by Lean's convention),
proves that the completed theta transform is literally the zero vector, and proves that every
centered Cauchy test is square-summable. It defines the closed span of the regular Cauchy evaluation
vectors as a complete Hilbert subspace. For every actual Xi zero, the removable Hedenmalm quotient
has the exact Hilbert norm

```text
||u_alpha||^2 = m_alpha ||XiC'(alpha)||^2.
```

This is an unconditional construction of the evaluation carrier; only its identification with the
positive Weil metric uses RH. It does not assert that the full differential pair extends to a
closable unbounded operator on this completion.

This closes the algebraic divisor side of `(6)`, `(9)`, `(11)`, `(12)`, and `(15)`. The formal tree
still lacks the extension of the prime-plus-Gamma equality from the Cauchy/resolvent core to the
full Guinand--Weil test algebra, and the closability/domain theorem for the full unbounded
Hedenmalm pair. No source-side or positivity claim is represented by an assumption.

## Gates

- [x] completed centered Weil distribution fixed
- [x] source polarization defined
- [x] theta kernel proved radical
- [x] quotient form on `ran L` proved well-defined
- [x] Hedenmalm pair symmetry proved unconditionally
- [x] positivity identified exactly with the Weil RH criterion
- [x] eigenfunction Fourier quotient computed
- [x] nondegeneracy identified exactly with RH plus simplicity
- [x] all-prime and archimedean provenance stated
- [x] eigenfunction quotients checked in a Guinand--Weil class
- [x] closed Hilbert completion of the square-summable Cauchy evaluation core
- [ ] closability/domain theorem for the full unbounded Hedenmalm pair
- [ ] independent specialist novelty audit
- [x] multiplicity-exact zero-side Weil polarization and theta radical in Lean
- [x] Lean prime-plus-Gamma realization on the Cauchy/resolvent core
- [ ] Lean extension to the full Guinand--Weil test algebra
- [x] Lean entire eigenfunction quotient and pointwise derivative law
- [x] Lean multiplicity-summed eigenfunction norm and orthogonality law
- [x] Lean `ell^2` evaluation carrier, Cauchy completion, and exact Hedenmalm Hilbert norm
