# Exact Gamma-skew frequency flux excludes \(L^2\) homogeneous Suzuki seam coronas

- **ID:** `suzuki-gamma-skew-frequency-flux-liouville`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / EXACT NONCONORMAL SEAM RIGIDITY
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Route:** Connes/CCM restricted-Weil form through Suzuki's completed zero modes
- **Inputs:** `suzuki-weak-signed-half-log-trace.md`,
  `suzuki-bounded-seam-half-log-rigidity.md`
- **Statement:** After logarithmic boundary straightening, the literal nonlocal remainder has a
  real Gamma multiplier.  In the differentiated homogeneous seam equation this multiplier and
  every bounded self-adjoint prime-seam coupling are exactly skew in frequency.  The radial
  Fourier current

  ```text
  |eta| ||Fhat(eta)||^2
  ```

  is therefore constant on each frequency half-line.  No nonzero \(L^2\) homogeneous seam state
  exists.  This removes the previously live nonconormal high-frequency escape for every
  self-adjoint Hilbert seam realization.

## 1. Exact whole-line remainder

Let \(X\) be a complex Hilbert space.  For a Schwartz function
\(F:\mathbb R\to X\), define

```text
(R F)(L)
 =integral_0^infinity
   [2F(L)-F(L+s)-F(L-s)]/(exp(s)-1) ds.                 (1)
```

Use the Fourier convention

```text
Fhat(eta)=integral_R F(L) exp(-i eta L)dL.              (2)
```

`[PROVED]` The exact multiplier of `(1)` is

```text
r(eta)
 =2 integral_0^infinity
    [1-cos(eta s)]/(exp(s)-1) ds
 =psi(1+i eta)+psi(1-i eta)+2 EulerGamma.               (3)
```

In particular,

```text
r(eta) is real, even, nonnegative for real eta.          (4)
```

### Proof

Translation by \(+s\) has Fourier multiplier \(e^{i\eta s}\), while translation by \(-s\)
has multiplier \(e^{-i\eta s}\).  Thus the multiplier of `(1)` is

```text
integral_0^infinity
 [2-exp(i eta s)-exp(-i eta s)]/(exp(s)-1) ds,
```

which is the first expression in `(3)`.  It converges at zero because
\(1-\cos(\eta s)=O(s^2)\), and at infinity because the denominator is exponential.
The classical integral

```text
psi(1+z)+EulerGamma
 =integral_0^infinity [1-exp(-z s)]/(exp(s)-1) ds
```

at \(z=i\eta\) and \(z=-i\eta\) gives the second expression.  Reality, evenness, and
nonnegativity follow from the first expression. `QED`

The identity is the exact Fourier version of the zero-extension formula

```text
R_full f=R_half F-log(1-exp(-L))F,
```

already used in the signed-trace theorem.  No pointwise-multiplier replacement of the
nonlocal remainder is being made.

## 2. Differentiated homogeneous seam equation

Let \(T\in\mathcal B(X)\) be bounded and self-adjoint.  Let \(F\) be an \(X\)-valued tempered
distribution represented by an \(L^2(\mathbb R;X)\) function.  Suppose

```text
(2L I+R-T)F'(L)+F(L)=0                                  (5)
```

in tempered distributions.

Equation `(5)` is exactly the derivative of the homogeneous logarithmic boundary system

```text
P F+R F-T F=constant,
P F(L)=2L F(L)-integral_(-infinity)^L F(t)dt.            (6)
```

Differentiation loses only the displayed constant.  This is the correct loss: a compact
initial segment and every regular power-scale source enter the tail problem as an inhomogeneous
frequency flux, not as a homogeneous corona state.

Put \(f=\widehat F\).  Since

```text
Fourier(F')=i eta f,
Fourier(L F')=-(f+eta f'),
Fourier(R F')=i eta r(eta)f,                             (7)
```

equation `(5)` becomes, away from \(\eta=0\),

```text
f'(eta)
 =-f(eta)/(2 eta)
   +(i/2)[r(eta)I-T]f(eta).                              (8)
```

This conclusion is valid for weak \(L^2\) solutions.  On every compact interval disjoint from
zero, the coefficient in `(8)` is bounded.  The distributional equation therefore puts
\(f\) in \(H^1_{\rm loc}\), hence gives its locally absolutely continuous representative.

## 3. Exact frequency-current conservation

`[PROVED]` Every weak solution of `(8)` satisfies

```text
d/deta [eta ||f(eta)||^2]=0                              (9)
```

on each of \((0,\infty)\) and \((-\infty,0)\).  Equivalently,

```text
|eta| ||f(eta)||^2=C_+     for eta>0,
|eta| ||f(eta)||^2=C_-     for eta<0,                   (10)
```

for constants \(C_+,C_-\ge0\).

### Proof

For real \(\eta\), `(3)` makes \(r(\eta)I-T\) self-adjoint.  Hence

```text
Re inner(i[r(eta)I-T]f(eta),f(eta))=0.                  (11)
```

Taking the real part of the inner product of `(8)` with \(f\) gives

```text
d/deta ||f(eta)||^2
 =2 Re inner(f'(eta),f(eta))
 =-||f(eta)||^2/eta.                                    (12)
```

The product rule gives `(9)`, and `(10)` follows. `QED`

The cancellation in `(11)` is load-bearing.  The exact Gamma remainder is not estimated,
smoothed, or declared lower order.  Its complete multiplier survives, but it transports phase
only and creates no radial Fourier mass.  The same is true of the literal bounded
self-adjoint prime-seam adjacency \(T\).

There is an exact forced version.  If the right side of `(5)` is \(G'\), then `(8)` becomes

```text
f'
 =-f/(2 eta)+(i/2)(r I-T)f-(i/2)Ghat,
```

and

```text
d/deta [eta ||f||^2]
 =eta Re inner(-i Ghat,f).                               (13)
```

Thus every departure from the conserved critical law is assigned to the actual regular or
boundary forcing.  Gamma and prime transport cannot manufacture it.

## 4. \(L^2\) Liouville theorem

`[PROVED]` Under the hypotheses of Section 2,

```text
F=0 in L2(R;X).                                          (14)
```

### Proof

Plancherel gives \(f\in L^2(\mathbb R;X)\).  If \(C_+>0\), `(10)` gives

```text
integral_1^N ||f(eta)||^2deta=C_+ log N,
```

contradicting \(f\in L^2\) as \(N\to\infty\).  Hence \(C_+=0\) and \(f=0\) almost everywhere
on the positive half-line.  The same argument gives \(C_-=0\) on the negative half-line.
An \(L^2\) function has no point mass at zero, so \(f=0\) almost everywhere.  Plancherel gives
`(14)`. `QED`

The obstruction is sharp.  A nonzero formal homogeneous mode has

```text
||f(eta)||=C |eta|^(-1/2),                               (15)
```

which is exactly outside \(L^2\) at logarithmic order.  The half-log boundary corona is therefore
the unique radial Fourier defect of the homogeneous system; an \(L^2\) flat sector cannot hide
behind arbitrarily rapid oscillation.

## 5. Explicit Gamma transport

The current law does not require an explicit propagator, but one exists.  On a simply connected
region avoiding the imaginary integers and zero, define

```text
M_T(z)
 =z^(1/2)
  [Gamma(1-i z)/Gamma(1+i z)]^(1/2)
  exp(-i EulerGamma z+i z T/2).                          (16)
```

The logarithmic derivative of `(16)` is

```text
M_T'(z) M_T(z)^(-1)
 =1/(2z)-(i/2)[r(z)I-T].                                (17)
```

Consequently `(8)` is equivalent to

```text
d/deta [M_T(eta)f(eta)]=0.                              (18)
```

For real \(\eta\), the Gamma ratio and \(\exp(i\eta T/2)\) are unitary, so

```text
||M_T(eta)v||=sqrt(|eta|)||v||,                          (19)
```

which recovers `(10)`.  The nearest nonzero singularities of the meromorphic Gamma factor occur
at \(\eta=\pm i\).  This identifies, but does not yet prove for the forced Suzuki problem, the
expected next physical boundary scale \(e^{-L}=r\) after the half-log defect is removed.

## 6. Literal Route-O consequence

The previous bounded-coupling theorem excluded inverse-log-flat tails only when the exact
remainder could be estimated as lower order on a controlled conormal class.  Its hostile audit
left open a nonconormal state with rapidly increasing logarithmic frequency, for which \(R\)
is as large as the principal \(2L\) term.

The theorem above closes that escape without any conormal, derivative, positivity-of-the-solution,
or pointwise regularity assumption:

```text
exact Gamma remainder
 + arbitrary bounded self-adjoint Hilbert seam coupling
 + homogeneous L2 logarithmic tail
 -> zero.                                                (20)
```

In particular, the explicit intermediate model

```text
F(L)=exp(-sqrt(L))
```

and every super-polynomially flat bounded tail lie in \(L^2(dL)\); none can survive as a
homogeneous solution of the exact self-adjoint seam system, even after arbitrary nonconormal
oscillation is added.

This is not yet `SUZUKI-TRACE-ZERO-H1`.  Three source connectors remain:

1. realize the complete support-pruned valuation seam state of a completed Suzuki zero mode in
   one self-adjoint Hilbert carrier on which the finite von-Mangoldt adjacency is bounded;
2. show that after both signed half-log traces vanish, the homogeneous corona component belongs
   to \(L^2(dL;X)\), while all inhomogeneous terms have physical power rate \(e^{-\sigma L}\) with
   some \(\sigma>1/2\);
3. use the forced current `(13)` and the Gamma strip in `(16)` to prove that the surviving
   particular solution has the same power rate, hence lies in \(H^1_0\).

The live analytic gap has therefore moved.  It is no longer “the exact logarithmic remainder may
support a nonconormal flat homogeneous cycle.”  It is the source-domain realization and forced
Gamma-strip estimate in items 1--3.

## 7. Hostile audit

1. **Not a disguised pointwise multiplier.**  Only the Fourier transform diagonalizes \(R\);
   `(1)` remains the literal nonlocal operator.
2. **Self-adjointness is essential.**  For non-self-adjoint \(T\), the second term in `(12)` may
   have nonzero real part.  The actual von-Mangoldt translation graph is symmetric, but its
   completed infinite seam realization still has to preserve that symmetry.
3. **No tail/source deletion.**  Differentiating loses a constant and any compact cutoff creates
   forcing.  Those terms belong in `(13)` and cannot be discarded in the Suzuki application.
4. **No \(L^2\) smuggling.**  A signed trace equal to zero gives \(o(L^{-1/2})\), not automatically
   \(L^2(dL)\).  Connector 2 is still open.
5. **No \(H^1\) overreach.**  \(L^2(dL)\) is not physical \(H^1\); the Gamma-strip estimate is
   still required.
6. **No RH claim.**  Corona no-return, raw Evans positivity, and cofinal nonvanishing remain open.

## 8. Novelty audit

The digamma integral, Hilbert-space skew generators, Plancherel, and the elementary current
calculation are parent mathematics.  The claimed new content is their exact conjunction for
Suzuki's logarithmic boundary normal form:

```text
literal Gamma jump remainder
 -> exact skew frequency transport
 -> critical |eta| Fourier current
 -> nonconormal L2 seam Liouville law.                  (21)
```

Corpus search found no previous theorem with `(9)`--`(14)`.  Targeted searches for
“logarithmic Laplacian Wiener--Hopf”, half-line Gamma factorization, and logarithmic boundary
trace found the general logarithmic-Laplacian, extension, boundary-regularity, and fractional
Hadamard literature, but no matching Gamma-skew current or seam Liouville theorem.  This supports
but does not certify priority.

## 9. Lean decision

The paper theorem is dependency-closed.  Its source-bearing formal core is `(9)`: an arbitrary
real Gamma multiplier and arbitrary self-adjoint bounded seam coupling contribute only a
skew term, so the weighted norm current is conserved.  Formalization should certify that exact
current and its zero-current consequence without introducing an abstract proposition equivalent
to `(14)`.

**`(9)` and its cancellation `(11)` are now formal**, in

```text
formal/GaloisForLFunctions/HTGeometry/SkewFrequencyCurrent.lean
```

```text
inner_self_im_eq_zero_of_isSelfAdjoint            ⟪S v, v⟫ is real
re_inner_I_smul_isSelfAdjoint_eq_zero             (11): Re⟪i • S v, v⟫ = 0
re_inner_real_smul_I_smul_isSelfAdjoint_eq_zero   the (c·i) shape the equation produces
re_inner_real_smul_self                           Re⟪(r:ℝ) • x, x⟫ = r ‖x‖²
hasDerivAt_normSq_path                            d/dt ‖f t‖² = 2 Re⟪f'(t), f(t)⟫
hasDerivAt_radialCurrent                          (9): d/dη [η ‖f η‖²] = 0
radialCurrent_const_of_hasDerivAt                 constancy on an open preconnected set
radialCurrent_const_Ioi, radialCurrent_const_Iio  (10): |η| ‖f η‖² is constant on each
                                                  half-line
```

The cancellation is stated for an arbitrary bounded self-adjoint `S`, which is the card's own
point: the exact Gamma multiplier is not estimated, smoothed, or declared lower order — it
survives in full and still contributes no radial mass, and the same holds for the literal prime-seam
adjacency.

The one remaining Lean item on this card is `(14)`, the `L²` Liouville conclusion: from `(10)`,
`‖f η‖² = C/η` on the positive ray, and `∫_1^∞ C/η dη` diverges unless `C = 0`, so square
integrability forces `f = 0` on each half-line.  The divergence is `integrableOn_Ioi_rpow_iff` at
exponent `-1`.  Neither needs the Bochner Fourier transform,
the logarithmic jump multiplier, or the completed seam carrier; those are needed only for the
separate transform passage from `(1)` to `(8)`.

## Gates

- [x] exact whole-line Gamma jump multiplier computed
- [x] differentiated weak seam equation transformed without dropping a source term
- [x] Gamma and self-adjoint prime coupling proved exactly skew in frequency
- [x] critical Fourier current proved
- [x] \(L^2\) homogeneous Liouville theorem proved
- [x] nonconormal high-frequency homogeneous escape removed
- [x] explicit Gamma propagator and first strip singularity identified
- [x] hostile source-domain and \(H^1\) limits recorded
- [x] formalize frequency-current theorem in Lean
- [ ] construct literal completed self-adjoint valuation seam carrier
- [ ] prove trace-zero homogeneous component is \(L^2(dL;X)\)
- [ ] prove forced Gamma-strip decay \(e^{-\sigma L}\), \(\sigma>1/2\)
- [ ] conclude `SUZUKI-TRACE-ZERO-H1`
- [ ] prove corona no-return
- [ ] prove raw Evans positivity
- [ ] RH

