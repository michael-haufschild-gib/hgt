# Hedenmalm's theta pencil is a supersymmetric Fredholm range divisor

- **ID:** `hedenmalm-supersymmetric-fredholm-range-divisor`
- **Stage:** 2-fully-proven / range-divisor half formalized; unbounded-operator half open
- **Type:** THEOREM / FREDHOLM--WITTEN REINTERPRETATION
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** Hedenmalm's theta boundary problem;
  `../new_scientific_knowledge/hedenmalm-reflection-folded-dirac-source-defect.md`;
  `../new_scientific_knowledge/hedenmalm-pair-weil-polarization-law.md`;
  `../../1-in-progress/hedenmalm-theta-l2-cyclic-radical-collapse.md`.

## Exact statement

Use logarithmic coordinates in Hedenmalm's problem and normalize the positive even theta source
so that

\[
 k(x)>0,\qquad \int_{\mathbb R}k(x)e^{i\alpha x}\,dx=\Xi_C(\alpha).
 \tag{1}
\]

Multiplying `k` by a fixed positive constant changes none of the assertions below.  Put

\[
 \mathcal H_k=L^2(\mathbb R,k(x)^{-1}dx),\qquad
 D=-i\partial_x,\qquad
 L=kDk^{-1}=D+i\frac{k'}k.
 \tag{2}
\]

Let `A` be the closure of `D` from `C_c^\infty(\mathbb R)` in `\mathcal H_k`.  Then:

1. `A` is closed and densely defined, and
   \[
   A^*=L
   \tag{3}
   \]
   with the maximal first-order domain.
2. `A` is Fredholm of index `-1`:
   \[
   \ker A=0,\qquad \ker A^*=\mathbb Ck,
   \qquad \operatorname{ran}A=k^\perp.
   \tag{4}
   \]
3. For every `\alpha\in\mathbb C`, `A+\alpha` is Fredholm of index `-1`, is injective, and
   \[
   \ker(A+\alpha)^*
   =\mathbb C g_\alpha,
   \qquad
   g_\alpha(x)=k(x)e^{-i\overline\alpha x}.
   \tag{5}
   \]
4. The literal Hedenmalm source equation has the exact Fredholm alternative
   \[
   (A+\alpha)u=-ik
   \quad\Longleftrightarrow\quad
   \Xi_C(\alpha)=0.
   \tag{6}
   \]
   When it is solvable, its solution is unique and equals
   \[
   u_\alpha(x)
   =e^{-i\alpha x}\int_{-\infty}^{x}k(y)e^{i\alpha y}\,dy
   =-e^{-i\alpha x}\int_x^{\infty}k(y)e^{i\alpha y}\,dy.
   \tag{7}
   \]
5. The Hedenmalm second-order bulk is already a positive self-adjoint Witten Hamiltonian:
   \[
   LD=A^*A\ge0.
   \tag{8}
   \]
   It has compact resolvent.  The supersymmetric Dirac operator
   \[
   \mathcal Q=
   \begin{pmatrix}0&A^*\\A&0\end{pmatrix},
   \qquad
   \operatorname{dom}\mathcal Q=\operatorname{dom}A\oplus\operatorname{dom}A^*,
   \tag{9}
   \]
   is self-adjoint with compact resolvent.  Its supersymmetric/Witten index is
   `\operatorname{ind}A=-1` (the Fredholm index of the self-adjoint block `\mathcal Q` itself is
   zero).
6. For every `\alpha`, the ordinary Hermitian square
   \[
   H_\alpha=(A+\alpha)^*(A+\alpha)
   \tag{10}
   \]
   is positive self-adjoint, has compact resolvent, and is strictly positive.  In particular,
   `\Xi_C(\alpha)=0` does **not** produce a zero mode of `(10)`.

Thus the positive self-adjoint bulk asked for by the differential expression is canonical and
unconditional.  What remains open is categorically different: turn the range-incidence divisor
in `(6)` into faithful spectrum without replacing its unsquared cokernel coordinate by a norm
square.

## Proof

### 1. Weighted adjoint

Write `a=k'/k`.  For `f,g\in C_c^\infty(\mathbb R)`, integration by parts gives

\[
\begin{aligned}
 \langle Df,g\rangle_{\mathcal H_k}
 &=\int_{\mathbb R}(-if')\overline g\,k^{-1}dx\\
 &=\int_{\mathbb R}f\,
   \overline{\left(-ig'+ia g\right)}\,k^{-1}dx
 =\langle f,Lg\rangle_{\mathcal H_k}.
\end{aligned}
\tag{11}
\]

The standard maximal/minimal theorem for a first-order differential expression on the whole line
therefore identifies the adjoint of the closure of `D` with the maximal realization of `L`.
Equivalently, multiplication by `k^{-1/2}` is a unitary

\[
 U:\mathcal H_k\longrightarrow L^2(\mathbb R,dx)
\]

and on the compactly supported core

\[
 UAU^{-1}=D-\frac{i}{2}a,
 \qquad
 UA^*U^{-1}=D+\frac{i}{2}a.
\tag{12}
\]

This proves `(3)` after closure.

### 2. Compact Witten square and the index

The first component of the Witten square becomes

\[
 U A^*A U^{-1}
 =-\partial_x^2+V_k(x),
 \qquad
 V_k=\frac14a^2-\frac12a'.
 \tag{13}
\]

Hedenmalm's theta asymptotic, in logarithmic coordinates, is

\[
 -\log k(x)=\pi e^{2x}-\frac92x+O(1)
 \qquad(x\to+\infty),
 \tag{14}
\]

with the reflected asymptotic at `-\infty`.  Hence

\[
 a(x)=-2\pi e^{2x}+\frac92+O(e^{-2x}),
 \qquad
 a'(x)=-4\pi e^{2x}+O(e^{-2x})
 \tag{15}
\]

at `+\infty`, and `(13)` tends to `+\infty` at both ends.  The one-dimensional confining
Schrodinger theorem gives compact resolvent for `A^*A`.

A distributional solution of `Af=0` is constant.  No nonzero constant belongs to
`\mathcal H_k`, because `k^{-1}` grows super-exponentially at both ends.  Thus `\ker A=0`.
A distributional solution of `A^*g=0` is `g=ck`; moreover

\[
 \|k\|_{\mathcal H_k}^2=\int_{\mathbb R}k(x)\,dx<\infty.
\]

Since `A^*A` has compact resolvent and zero is not an eigenvalue, its spectrum has a positive
lower edge.  Therefore `A` is bounded below, its range is closed, and

\[
 (\operatorname{ran}A)^\perp=\ker A^*=\mathbb Ck.
\]

This proves `(4)` and `\operatorname{ind}A=-1`.

### 3. Every complex translate remains Fredholm

Let `\alpha=r+ib` and set

\[
 k_b(x)=k(x)e^{-2bx}.
\]

All exponential moments of `k` are finite, and the tilted logarithmic derivative is `a-2b`.
Consequently the tilted Witten potential

\[
 V_{k_b}=\frac14(a-2b)^2-\frac12a'
\]

still tends to `+\infty` at both ends.  Multiplication by `e^{-i\alpha x}` is a unitary map

\[
 M_\alpha:\mathcal H_{k_b}\longrightarrow\mathcal H_k
\]

and satisfies, first on the common compactly supported core and then after closure,

\[
 (A_k+\alpha)M_\alpha=M_\alpha A_{k_b}.
 \tag{16}
\]

The preceding index argument applied to `k_b` proves that `A+\alpha` is Fredholm of index `-1`
and injective.  Solving the adjoint first-order equation gives `(5)`; its vector belongs to
`\mathcal H_k` because

\[
 \|g_\alpha\|_{\mathcal H_k}^2
 =\int_{\mathbb R}k(x)e^{-2(\operatorname{Im}\alpha)x}\,dx<\infty.
 \tag{17}
\]

### 4. Xi is the source coordinate in the cokernel line

Closed range and `(5)` give

\[
 -ik\in\operatorname{ran}(A+\alpha)
 \quad\Longleftrightarrow\quad
 \langle-ik,g_\alpha\rangle_{\mathcal H_k}=0.
\]

But `(1)` gives the exact coordinate

\[
 \langle-ik,g_\alpha\rangle_{\mathcal H_k}
 =-i\int_{\mathbb R}k(x)e^{i\alpha x}\,dx
 =-i\Xi_C(\alpha).
 \tag{18}
\]

This proves `(6)`.  Direct integration of `(A+\alpha)u=-ik` gives the first expression in
`(7)`.  When `\Xi_C(\alpha)=0`, subtracting the complete integral gives the second expression.
The super-exponential theta tails put this two-ended solution in `\operatorname{dom}A`; uniqueness
follows from injectivity.

### 5. Positive supersymmetry and why it does not prove RH

For every closed densely defined operator, `A^*A` is positive self-adjoint, and the block operator
in `(9)` is self-adjoint.  Its square is

\[
 \mathcal Q^2=
 \begin{pmatrix}A^*A&0\\0&AA^*\end{pmatrix}.
\]

The nonzero spectra of the two Witten partners agree, `A^*A` has compact resolvent, and
`\ker A=0`, `\ker A^*=\mathbb Ck`.  This proves the compact-resolvent assertion and the
supersymmetric index `\dim\ker A-\dim\ker A^*=-1`.  As required for a self-adjoint Fredholm
operator, `\mathcal Q` itself has Fredholm index zero.
The same closed-operator theorem applied to `A+\alpha` proves positivity and self-adjointness of
`H_\alpha`.  Its kernel equals `\ker(A+\alpha)=0`; compact resolvent then makes it strictly
positive.  Thus `(10)` has no zero mode even at a Xi zero.

This closes every item of the theorem.

## Cokernel-bundle geometry

The lines

\[
 \mathcal E_\alpha=\ker(A+\alpha)^*=\mathbb Cg_\alpha
 \tag{19}
\]

form an anti-holomorphic coherent-state line bundle.  The fixed theta ground state defines a
holomorphic quotient section whose coordinate is `-i\Xi_C(\alpha)`.  Its squared quotient norm is

\[
 \|[-ik]_\alpha\|^2
 =\frac{|\Xi_C(\alpha)|^2}
 {\displaystyle\int_{\mathbb R}k(x)e^{-2(\operatorname{Im}\alpha)x}\,dx}.
 \tag{20}
\]

If `N(y)` denotes the denominator, then

\[
 \frac{d^2}{dy^2}\log N(y)
 =4\operatorname{Var}_{\mu_y}(x)>0,
 \qquad
 d\mu_y=\frac{k(x)e^{-2yx}}{N(y)}dx.
 \tag{21}
\]

Hence the bulk supplies a canonical positive Fisher/Chern metric.  The Xi divisor is carried by
the *phase-sensitive source section* of that metric, not by positivity of the metric itself.
Poincare--Lelong decomposes the curvature of the section norm into the Xi divisor current plus the
smooth Fisher curvature `(21)`.  This gives one geometric object behind the corpus's Witten,
Fisher, Julia-current, divisor-conormal, and squared-orientation observations.

## Hostile audit and exact open core

### What is wrong with the naive claim

The theorem does **not** solve Hedenmalm's requested pair self-adjointness.  It proves that the
second-order factor `LD` is positive self-adjoint in a canonical weight.  Hedenmalm needs a
positive form for which the *pencil* `(LD,L)` turns each range crossing into nonzero spectrum.
The coefficient `L=A^*` remains chiral and non-self-adjoint.

The ordinary Hermitian repair `(10)` is worse than incomplete: it provably deletes the divisor
mechanism.  Xi is the unsquared cokernel pairing `(18)`, whereas `(10)` sees norms and singular
values.  This is the same odd/even fracture isolated independently by the source-modular paper.

### Exact remaining theorem

`[OPEN CORE]` Construct, from the ordinary-integer Euler--Poisson--Gamma source before choosing a
zero, a singular boundary functor which sends the cokernel-section zero in `(18)` to a nonzero
eigenmode of one self-adjoint operator, preserves analytic multiplicity and reflection, and does
not factor through `A^*A`, `(A+\alpha)^*(A+\alpha)`, or the quotient norm `(20)`.

Equivalently, the missing operation must be **chiral before Hilbert scalarization**.  It must carry
the determinant-line/source-section coordinate itself into a conservative boundary mode.  The
updated source-modular completion theorem supplies dense prime--Gamma Cauchy packets for the
resulting Weil form, but its decisive orientation packet is selected through divisor closure and
its eventual sign is exactly RH; it does not construct this chiral boundary functor.

### Stronger conjecture after the positive-square failure

`[CONJECTURE -- ESSENTIAL CHIRAL HODGE TRANSMUTATION]` The source-normal blow-up of the complete
ordinary-prime valuation complex admits a Real, reflection-equivariant Hodge boundary map into the
cokernel bundle `(19)` such that:

1. the quotient section is exactly `(18)`, and at a zero of order `m` the image of the
   BV/co-Poisson principal conormal is its first nonzero normal jet of order `m` (not the vanishing
   value of the section);
2. its Hodge adjoint acts before the quotient norm and exchanges the two causal determinant-line
   sections;
3. after source reflection, the common section lands in the domain of one self-adjoint boundary
   generator;
4. the map is of essential Rees order and is nonzero on every Xi conormal.

The ordinary weighted square does not kill this conjecture because the conjectured map explicitly
acts on the determinant line before `(20)`.  The finite-Rees and smooth-Sonin no-go theorems do not
kill it because essential Rees order and the nonsmooth source-normal face are hypotheses forced by
those exact obstructions.  The conjecture remains RH-bearing at item 4; no construction is claimed.

### 1 August source-normal progress

`hedenmalm-two-prime-theta-interval-normal-frame.md` now constructs the algebraic acquisition and
nonannihilation part of items 1 and 4.  Centered prime-2 and prime-3 translation anomalies are
positive even theta-window sources with transforms `a_p XiC`; the two multipliers have no common
zero, generate the full normal module `(XiC)/(XiC)^2`, retain arbitrary multiplicity, and become
the essential reciprocal symbols

```text
2 p^(-1/2) mu sin(log(p)/(2 mu)).
```

This does not construct the Hodge adjoint or the closed self-adjoint landing in items 2--3.
Moreover, every finite and every summably weighted diagonal prime frame has zero lower boundary
frame bound.  The remaining transmutation must therefore be a nonsummable renormalized or
genuinely cross-prime strict completion; ordinary Hilbert-frame closure is now excluded rather
than merely unproved.

### Complete positive channel landing

`../../3-formalized/needs-audit/complete-positive-resolution-summable-conormal-landing.md` uses the
updated complete Kolchin-free source resolution and the least-prime shell ratio to construct a
different countable object.  For every point of `Re s > 0`, its normalized channel vector lies in
`ell^1`, sums exactly to one, and is therefore nonzero.  At every right-half Xi zero, including the
critical boundary, the completed vector retains the first nonzero conormal jet and exact
multiplicity.  This is now formalized unconditionally in Lean.

The result supplies a fixed Hausdorff source-pointed Banach mode, but not the Hodge adjoint in
items 2--3.  Off-line zeros would also have nonzero summable channel vectors.  The surviving open
core is therefore sharper: construct the theta/Poisson boundary intertwiner carrying this
`ell^1` mode into one reflection-internal operator domain, and prove symmetry of the spectral
generator there.  Channel summability and conormal nonannihilation may no longer be named as that
missing theorem.

## Corpus and literature audit

- `[LOCAL-RESEARCH]` The reflection-folded Dirac card already proves that ordinary free squaring
  leaves a forced resolvent and that a rank-one positive dilation replaces Xi by a Cauchy response
  of `|Xi|^2`.  It does not identify the weighted adjoint, Fredholm index, or exact range divisor.
- `[LOCAL-RESEARCH]` The theta Born--Witten hierarchy factorizes each positive theta atom on the
  half-line.  It is not the global weighted factorization `LD=A^*A` and does not yield `(6)`.
- `[LOCAL-RESEARCH]` The Weil-polarization theorem supplies the correct algebraic pair form, whose
  positivity is RH.  The present theorem instead supplies an unconditional positive bulk and
  proves exactly why that bulk does not orient the Weil form.
- `[LITERATURE]` Hedenmalm constructs the theta pencil and asks for its positive sesquilinear
  realization, but does not state `(2)`--`(6)` or the supersymmetric range-divisor interpretation.
- `[LITERATURE]` Witten factorization, closed-operator supersymmetric Dirac blocks, Fredholm
  alternatives, and de Branges models of simple symmetric deficiency-index `(1,1)` operators are
  established parent theories.  Therefore the general operator ingredients are a `[BRIDGE]`;
  novelty, if any, is restricted to their exact theta-pencil conjunction and the cokernel-section
  identification `(18)`.
- Searches through 1 August 2026 found no follow-up to Hedenmalm's June 2026 preprint and no source
  stating the exact weighted Fredholm range-divisor theorem.  This cannot establish priority, so
  status remains `[NOVELTY UNVERIFIED]`.

Primary references:

- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494 (2026).
- R. T. W. Martin, *Representation of simple symmetric operators with deficiency indices (1,1)
  in de Branges space*, Complex Analysis and Operator Theory 5 (2011), 545--577;
  arXiv:0909.2220.
- Standard closed-operator and Witten-Laplacian theorems for `A^*A`, `AA^*`, and the
  supersymmetric Dirac block.

## Lean status

`[PARTIAL]`  `formal/GaloisForLFunctions/RHTower/HedenmalmFredholmRangeDivisor.lean`
(namespace `RHTower.HedenmalmFredholmRange`) formalizes the **range-divisor half** of the theorem
in explicit integral form over the general source class
`GaloisForLFunctions.HTGeometry.PositiveDensitySource`.  Every declaration has `#print axioms`
equal to `[propext, Classical.choice, Quot.sound]`.

| # | statement | Lean declaration |
|---|---|---|
| `(5)` | the cokernel vector `g_alpha(x) = k(x) e^(-i conj(alpha) x)` | `cokernelVector` |
| `(5)` | its weighted pairing weight is the plain character | `conj_cokernelVector_div` |
| `(5)` | it annihilates the range of `A + alpha` | `integral_range_pairing` |
| `(6)` | solvability forces `Xi_C(alpha) = 0` | `xiC_eq_zero_of_solution` |
| `(6)`,`(7)` | the two-ended function is an explicit solution | `twoEndedSolution_equation`, `hasDerivAt_twoEndedSolution` (with `HedenmalmPrimeTranslation.sourceModeU`, `sourceModeD`) |
| `(7)` | the two formulas agree exactly at a zero | `sourceModeI_eq_neg_tail_iff`, `setIntegral_Iic_add_Ioi` |

`integral_range_pairing` and `xiC_eq_zero_of_solution` are proved by the improper fundamental
theorem of calculus on the whole line applied to the tilted product `u(x) e^(i alpha x)`; the
hypotheses are exactly the vanishing of that product at both ends, which is what membership of
`u` in the weighted space supplies.

**Weighted adjoint core.**  `formal/GaloisForLFunctions/RHTower/HedenmalmWeightedAdjointCore.lean`
(namespace `RHTower.HedenmalmThetaSource`) proves the core content of `(3)` and `(12)` at the
actual arithmetic source, with no hypothesis on the source.

| # | statement | Lean declaration |
|---|---|---|
| `(2)` | the logarithmic derivative `a = k'/k` is continuous | `sourceDeriv`, `hasDerivAt_thetaCuspFullSource`, `continuous_sourceDeriv`, `sourceLogDeriv`, `continuous_sourceLogDeriv` |
| `(11)` | **the weighted formal symmetry `<D f, g>_(H_k) = <f, L g>_(H_k)`** on compactly supported differentiable data | `integral_weighted_symmetry` |
| `(12)` | **the half-density conjugation** `(k^(1/2) f)' = k^(1/2)(f' + (a/2) f)` | `hasDerivAt_halfDensity_mul` |

`formal/GaloisForLFunctions/RHTower/HedenmalmSourceKernelTrivial.lean` supplies the analytic
reason for `ker A = 0` in `(4)`: the formal kernel of `D` is the constants, and the weighted space
carries none.

| # | statement | Lean declaration |
|---|---|---|
| `(4)` | the exponential ceiling forces `1/k` to be non-integrable | `not_integrableOn_exp_Ioi`, `not_integrable_exp_abs`, `not_integrable_inv_thetaSource` |
| `(4)` | **no nonzero constant is square integrable against `k^(-1)`**, so the formal kernel is trivial | `not_integrable_const_mul_inv_thetaSource` |
| `(8)` | **the formal Witten identity `<f, L D f> = <D f, D f>` on the compactly supported `C^2` core**, and the energy form is real and nonnegative | `integral_weighted_witten`, `integral_weighted_energy_nonneg` |

`integral_weighted_symmetry` is a single integration by parts: `f conj(g)/k` has compact support,
so its derivative integrates to zero by the improper fundamental theorem of calculus, and the
three terms of that derivative are exactly the difference of the two sides.

Still missing in Lean, and requiring genuine unbounded-operator infrastructure that mathlib does
not carry: the passage from the formal symmetry `(11)` to the operator identity `A^* = L` after
closure in `(3)`, closedness and the Fredholm index `-1` in `(4)`, compactness of the resolvent,
the Witten square `(8)`, the supersymmetric Dirac operator `(9)`, and strict positivity of the
Hermitian square `(10)`.  mathlib supplies `LinearPMap.adjoint`, `LinearPMap.closure` and
`LinearPMap.IsClosable`, but no Fredholm theory for unbounded operators.

## Gates

- [x] exact weighted adjoint proved
- [x] confining Witten square and compact resolvent proved
- [x] Fredholm index and tilted-family theorem proved
- [x] exact Xi cokernel coordinate and range-divisor law proved
- [x] positive supersymmetric bulk constructed
- [x] ordinary-square erasure proved
- [x] corpus collision and parent-theory audit completed provisionally
- [x] stronger essential-chiral conjecture extracted from the failure
- [x] algebraic essential source-normal conormal frame and nonannihilation constructed
- [x] finite/summable diagonal Hilbert-frame completion excluded
- [ ] independent specialist novelty audit
- [x] audit exact Lean unbounded-operator feasibility
- [x] Lean cokernel conormal `(5)` and exact Fredholm alternative `(6)`--`(7)` in
      explicit integral form
- [ ] formalize the full weighted Fredholm theorem
- [ ] construct the essential chiral Hodge transmutation
- [ ] deduce and formalize RH
