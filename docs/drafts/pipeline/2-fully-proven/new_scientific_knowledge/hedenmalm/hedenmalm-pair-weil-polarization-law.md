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

This closes the algebraic divisor side of `(6)`, `(9)`, `(11)`, `(12)`, and `(15)`.  The
eigenfunction statements `(19)`--`(24)` were subsequently proved unconditionally in
`XiThetaEigenGramLaw.lean`; the RH-hypothesis versions in `XiWeilPolarization.lean` are their
specializations. The formal tree
still lacks the extension of the prime-plus-Gamma equality from the Cauchy/resolvent core to the
full Guinand--Weil test algebra, and the closability/domain theorem for the full unbounded
Hedenmalm pair. No source-side or positivity claim is represented by an assumption.

`formal/GaloisForLFunctions/RHTower/XiQuotientRealDecay.lean` supplies the admissibility half of
`(18a)` on the real axis:

```text
exists_norm_xiThetaEigenFourier_ofReal_le
  : ||xiThetaEigenFourier alpha t|| <= C exp(-delta |t|) for every delta < pi/4;
exists_norm_xiThetaEigenFourier_horizontal_le
  : the same bound at t + i a, uniformly over |a| <= A, for every A < 1.
```

The exponential factor of `(18a)` is therefore unconditional, and the polynomial factor is not
needed for it: away from the removed point the linear denominator is bounded below, so the quotient
simply inherits the exponential decay of `XiC` proved in
`RHTower/ThetaCuspComplexStrip.lean`, and on the remaining compact interval continuity gives a bound.
What `(18a)` still lacks in Lean is the same estimate on closed *horizontal strips* rather than the
real axis alone.  The first piece of that is now built and stated for an arbitrary function, in
`formal/GaloisForLFunctions/RHTower/StripHorizontalShift.lean`:

```text
integral_horizontal_shift_of_decay
  : a function holomorphic on a closed horizontal strip and decaying exponentially in the real
    direction there has the same full-line integral on every horizontal line of the strip.
```

This is the theta-free form of the shift used for the real-axis decay, and applying it to the
tilted kernel gives the strip estimate itself, in
`formal/GaloisForLFunctions/RHTower/XiHorizontalStripDecay.lean`:

```text
exists_norm_XiC_horizontal_le
  : ||XiC (t + i a)|| <= C exp(-delta |t|), uniformly over |a| <= A, for every A < 1
    and every delta < pi/4.
```

So the exponential factor of `(18a)` is unconditional on every closed horizontal substrip, not only
on the real axis, and the same is true of the removable quotient itself: away from the removed point
the linear denominator is bounded below on the substrip, and on the remaining compact box continuity
gives a bound.  This is the estimate the card cites to place the eigenfunction quotients in the
Guinand--Weil test class.

The same module also discharges the polarization's own convergence hypothesis:

```text
xiWeilPairSummable_of_squareSummable
  : XiWeilSquareSummable F -> XiWeilSquareSummable (xiWeilSharp G) -> XiWeilPairSummable F G.
```

and, with the sharp hypothesis removed,

```text
XiWeilSquareSummable_sharp
  : square-summability is stable under the Weil sharp involution;
xiWeilPairSummable_of_squareSummable'
  : XiWeilSquareSummable F -> XiWeilSquareSummable G -> XiWeilPairSummable F G.
```

`XiWeilPairSummable` was previously an assumed condition.  The arithmetic--geometric mean bound
dominates each polarized term by half the sum of the two squared divisor evaluations, and the sharp
involution preserves square-summability because the Xi divisor is conjugation stable --- `xi` has
real Taylor coefficients.  That stability is **unconditional**: the corpus already owned
`xi_divisor_conj`, `xiZeroCopyConjEquiv` and `xiSpectralPoint_copyConj`, and composing the
conjugation equivalence with the reflection one gives an involution `xiZeroCopyStarEquiv` realising
plain conjugation of the centered spectral points.  Only the *pointwise* identity `conj rho = rho`
needs RH; the divisor being conjugation stable does not.

With absolute convergence available, the polarization is a genuine sesquilinear form on the
square-summable class, unconditionally:

```text
XiWeilSquareSummable.add, XiWeilSquareSummable.const_smul
  : the class is closed under sums and scalar multiples;
xiWeilPolarization_add_left, xiWeilPolarization_const_smul_left
  : the form is additive and homogeneous in the left argument.
```

The right-hand laws `xiWeilPolarization_add_right` and `xiWeilPolarization_const_smul_right` are
proved from these through the existing Hermitian symmetry `xiWeilPolarization_conj_symm`.

Cross-reference worth keeping: `RHTower/XiWeilLineConjHilbert.lean` already proves, **without RH**,
that the polarization *is* an `ell^2` inner product --- `inner_xiWeilLineConjLp_evaluation_eq_polarization`,
through the line-conjugation isometry `xiWeilLineConjLp` --- and deduces the Cauchy--Schwarz bound
`norm_xiWeilPolarization_le` in the sharp form `||F|| ||G||`.  So the RH hypothesis in
`inner_xiWeilEvaluationLp_eq_polarization_of_riemannHypothesis` is needed only to make the *plain*
inner product work; the conjugated one needs nothing.  So the square-summable class is a module and the polarization is defined
and sesquilinear on it --- the structural half of "test algebra".  The form is moreover Lipschitz for the divisor `ell^2` distance:

```text
XiWeilSquareSummable.sub, xiWeilPolarization_sub_left
norm_xiWeilPolarization_sub_left_le
  : ||q_W(F1,G) - q_W(F2,G)|| <= ||v(F1) - v(F2)|| ||v(G)||.
```

The function-level packets and the vector-level Hilbert core are also now bridged:

```text
XiWeilSquareSummable_cauchyPacket
xiWeilEvaluationLp_cauchyPacket_mem
  : the evaluation vector of a finite Cauchy packet lies in the algebraic Cauchy span.
```

The two were defined independently --- packets as functions in `XiWeilResolventSource`, the span as
a submodule of the divisor `ell^2` in `XiWeilHilbertCore` --- with nothing connecting them, so the
prime-plus-Gamma identity for packets and the Hilbert closure could not previously be used together.

Lipschitz continuity is the mechanism by which an identity proved on a subclass passes to its
closure, so the extension of the prime-plus-Gamma equality now reduces to two separable questions: whether the
Cauchy packets are `ell^2`-dense in the intended test class, and whether the prime-plus-Gamma side
converges along the same limits.  What is still missing for the open gate is therefore analytic, not
structural: the prime-plus-Gamma *value* is known only on the Cauchy resolvent core and on the
rectangular family, not for an arbitrary member of this class.  One subtlety in the proof is worth recording: the *uniform* bound needed by the
contour-shift hypothesis must use `exp(|t| delta)`, since `t z.im <= t delta` fails for `t <= 0`;
the sharp factor `exp(t delta)` is available only on the shifted line itself, where `z.im = delta`
exactly.  Using the sharp factor uniformly is the natural mistake and makes the estimate false.

## Both limit questions of the Cauchy core, answered

The two questions left by the Lipschitz continuity of the polarization --- whether the
prime-plus-Gamma side converges along `ell^2`-convergent sequences of Cauchy packets, and whether
those packets are `ell^2`-dense --- are now both settled in Lean, and they have opposite answers.

**Convergence: yes, unconditionally.**

```text
tendsto_primeArchSource_packetSum_of_tendsto
  : if the evaluation vectors of a sequence of finite Cauchy packets converge in the divisor
    ell^2 space, then the prime-plus-Gamma double sums

      sum_{z in s_n} sum_{w in t} c_n(z) conj(d(w)) (T(conj w) - T(z)) / (z - conj w)

    converge, with limit the inner product of the fixed line-conjugated evaluation vector against
    the limit vector.
```

The mechanism is that the polarization *is* an inner product against a fixed vector
(`inner_xiWeilLineConjLp_evaluation_eq_polarization`), hence continuous in the evaluation vector,
while on packets it is literally the prime-plus-Gamma expression.  So the arithmetic side of the
explicit formula has a canonical continuous extension to the closure of the Cauchy core: no
additional analytic input is needed for the passage to the limit, only for identifying the limit
with a prime sum for a *given* test function.

**Density: exactly obstructed by multiplicity.**

```text
mem_orthogonal_xiWeilCauchyAlgebraicSubspace_iff
  : u orthogonal to the algebraic Cauchy core
      <-> for every Xi zero rho, the sum of the coordinates of u over the multiplicity copies
          above rho vanishes.
xiWeilCauchyHilbertSubspace_eq_top_iff
  : the closed Cauchy core is the whole divisor ell^2 space
      <-> every Xi zero is simple.
```

This is a sharp, unconditional structural theorem about the carrier, and it is not what the naive
picture suggests.  The Cauchy kernels `q |-> (rho_q - z)^{-1}` are constant along each multiplicity
fibre, so they cannot separate two copies of a multiple zero; the content of the theorem is that
this is the *only* obstruction.  The nontrivial direction extracts the fibre sum as a residue: for
an orthogonal `u` the resolvent transform `sum_q conj(u_q) (rho_q - z)^{-1}` vanishes at every
regular point, multiplying by `a - z` turns the fibre part into the constant fibre sum, and the
remaining terms are bounded uniformly by Cauchy--Schwarz because the divisor is separated from `a`
(finitely many divisor points meet any disc).  Letting `z` approach `a` inside the punctured
neighbourhood of regular points --- which is nonempty because the zeros of `XiC` are isolated ---
kills the fibre sum.

Consequences for the open gate:

1. The resolvent core sees the Xi divisor only through its support weighted by total multiplicity.
   No family of Cauchy packets, and no limit of such, can ever detect the difference between a
   double zero and two coincident simple zeros.  Any test-algebra extension that intends to
   reach the *whole* `ell^2` carrier must therefore either assume simplicity or add non-Cauchy
   generators (derivatives of the Cauchy kernel are the natural candidates, since
   `d/dz (rho - z)^{-1}` still only separates fibres if the fibre index enters the coefficients).
2. Unconditionally, the closure of the Cauchy core is exactly the orthogonal complement of the
   fibrewise mean-zero space, so the polarization extends canonically to that subspace and to
   nothing larger.
3. Simplicity of the zeros is thus *equivalent* to density of the resolvent core --- the same
   hypothesis that already appeared in the nondegeneracy gate ("RH plus simplicity") reappears
   here for an independent reason, on the zero side alone and with no use of RH.

## The test-algebra gate, in its limit form

The two structural facts above combine into an approximation theorem that goes past the Cauchy
resolvent core.  Three ingredients:

```text
xiWeilEvaluationLp_mem_xiWeilCauchyHilbertSubspace
  : the evaluation vector of ANY square-summable test function lies in the closed Cauchy core.
exists_cauchyPacket_of_mem_xiWeilCauchyNodeSpan
  : every element of a node-restricted Cauchy span IS the evaluation vector of a finite Cauchy
    packet with nodes in the same set.
eventually_mem_xiWeilContinuedNodeSet
  : the continued prime-plus-Gamma domain accumulates at every Xi zero.
```

The first is the positive half of the multiplicity theorem: evaluation vectors are fibrewise
constant by construction, so they never meet the fibrewise mean-zero annihilator, and the failure of
density for multiple zeros never touches the range of the evaluation map.  The third says the
restriction to nodes where the *continued* trace is defined --- `Re(1/2 + zi) > 0`,
`1/2 + zi != 1`, `zeta(1/2 + zi) != 0` --- costs nothing, because the two open conditions hold at
each zero itself and the zeta condition fails only at the zero.  Together with the Lipschitz bound:

```text
exists_cauchyPacket_continuedPrimeArchSource_approx
  : for every square-summable F, every finite Cauchy packet G with nodes in the conjugated
    continued domain, and every eps > 0, there is a finite node set s in the continued domain,
    disjoint from the conjugated nodes of G, and coefficients c, with

      || sum_{z in s} sum_{w in t} c_z conj(d_w)
           (Ttilde(conj w) - Ttilde(z)) / (z - conj w)   -   q_W(F, G) ||  <=  eps.
```

So the zero-side Weil polarization of an *arbitrary* square-summable test function against a Cauchy
packet is a limit of explicit finite prime-plus-Gamma expressions, unconditionally.  This is the
limit form of the open gate: what is still missing is not the approximation but a *closed formula*
--- the identification of the limit with a prime sum attached to `F` itself rather than to its
approximants.  The gate below is therefore split into the part now proved and the part remaining.

## The eigenfunction Gram matrix is antidiagonal, unconditionally

The Lean statements of `(19)`--`(22)` in the tree carried the Riemann hypothesis as a hypothesis,
because they were derived from the RH form of `(6)` in which every divisor point is real.  That was
an artefact of the derivation, not of the mathematics: the card's own proof of `(21)` and `(22)`
uses only whether `alpha` itself is real.  The full unconditional computation is now formalized.

```text
xiWeilPolarization_thetaEigen
  : q_W(u_alpha, u_beta) = 0                                      if beta != conj(alpha)
    q_W(u_alpha, u_beta) = m_alpha (i Xi'(alpha)) conj(i Xi'(beta)) if beta  = conj(alpha),
    for any two zeros alpha, beta of XiC.  No hypothesis.
```

The mechanism is the one the card describes at `(20)`: the sharp involution evaluates the second
quotient at `conj(alpha)`, which is again a zero of `XiC` by the functional equation together with
Schwarz reflection, and a quotient based at one zero vanishes at every *other* zero.  So the Gram
matrix of the theta eigenfunctions is carried by the conjugation involution on the divisor and is
*antidiagonal*, not diagonal.  It becomes diagonal exactly when the involution is trivial, which is
RH.  Two immediate unconditional corollaries are `(21)` and `(22)`:

```text
xiWeilPolarization_thetaEigen_diagonal_eq_zero_of_im_ne_zero
  : Im(alpha) != 0  ->  q_W(u_alpha, u_alpha) = 0.
xiWeilPolarization_thetaEigen_diagonal_of_im_eq_zero
  : Im(alpha)  = 0  ->  q_W(u_alpha, u_alpha) = m_alpha ||Xi'(alpha)||^2.
```

With the finite sesquilinear expansion

```text
xiWeilPolarization_thetaEigen_finsetSum
  : q_W(sum_alpha c_alpha u_alpha, sum_beta d_beta u_beta)
      = sum_alpha sum_beta c_alpha conj(d_beta) Gram(alpha, beta),
```

this closes `(23)` and `(24)` as an unconditional equivalence with mathlib's `RiemannHypothesis`:

```text
forall_finsetSum_thetaEigen_re_pos_iff
  : ( q_W is strictly positive on every nonzero finite combination of theta eigenfunctions )
      <->  RiemannHypothesis  and  every zero of XiC is simple.
```

Forward is the single-eigenfunction case: a nonreal zero is null by `(21)` and a multiple real zero
is null by `(22)`.  Backward is diagonality of the Gram matrix on real zeros, which turns the double
sum into `sum_alpha |c_alpha|^2 m_alpha ||Xi'(alpha)||^2`.  This is the first statement in the tree
that ties the Hedenmalm metric to RH *and* simplicity in both directions without assuming either.

## The time-side eigenfunction equation `(17)`

`(17)` is now formalized in the corpus normalization.  The corpus already carried the two
source-pointed one-sided inverses of the theta source (the causal and anti-causal Volterra
integrals) and the fact that their difference is the free mode weighted by `XiC(alpha)`.  What was
missing is that they are *solutions* of the Hedenmalm equation at all:

```text
hasDerivAt_hedenmalmCausalVolterra
hasDerivAt_hedenmalmAntiCausalVolterra
hedenmalmCausalVolterra_thetaEigen_ode
hedenmalmAntiCausalVolterra_thetaEigen_ode
  : with D = -i d/dx,  (D + alpha) u = -k   for both one-sided inverses,
    at every spectral parameter with |Im alpha| < 1.
```

The proof is the fundamental theorem of calculus for the left half-line profile of the source
against the free mode, plus the product rule; the anti-causal case follows from the causal one and
the defect identity, because the free mode is annihilated by `D + alpha`.  Combined with the
existing coincidence criterion, this is the exact time-side statement behind `(17)`:

```text
exists_unique_twoSided_thetaEigen_solution_iff
  : the causal and anti-causal solutions agree everywhere  <->  XiC(alpha) = 0.
```

So a Xi zero is precisely a spectral parameter at which the inhomogeneous equation has a
distinguished two-sided solution, and off the divisor the two half-line solutions are genuinely
different.  The remaining half of the eigenfunction package, `(18)`, is the Fourier transform of
that solution; the Fourier-side object `-i Xi(z)/(alpha - z)` is already fully formalized and is
what the Gram law above is stated about.

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
- [x] Lean extension of the prime-plus-Gamma value to every square-summable test function in
      approximation form (finite continued prime sums, arbitrary accuracy, unconditional)
- [ ] Lean extension to the full Guinand--Weil test algebra in closed form (a prime formula attached
      to the test function itself, not to its Cauchy approximants)
- [x] Lean entire eigenfunction quotient and pointwise derivative law
- [x] Lean multiplicity-summed eigenfunction norm and orthogonality law
- [x] Lean unconditional theta-eigenfunction Gram law (`(19)`--`(22)` with no RH hypothesis)
- [x] Lean time-side eigenfunction equation `(17)` for both source-pointed inverses
- [x] Lean finite sesquilinear expansion on the eigen-span
- [x] Lean unconditional equivalence `(23)`/`(24)`: positive definiteness on the eigen-span iff
      RH plus simplicity
- [x] Lean `ell^2` evaluation carrier, Cauchy completion, and exact Hedenmalm Hilbert norm
- [x] Lean bridge from finite Cauchy packets to the Hilbert core
- [x] Lean convergence of the prime-plus-Gamma side along `ell^2`-convergent packet sequences
- [x] Lean exact density criterion for the Cauchy core (multiplicity annihilator; density is
      equivalent to simplicity of the Xi zeros)
