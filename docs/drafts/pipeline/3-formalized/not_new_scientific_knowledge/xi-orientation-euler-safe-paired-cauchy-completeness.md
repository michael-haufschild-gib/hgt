# The Xi orientation sector is complete on an absolute-Euler paired Cauchy quadrant

- **ID:** `xi-orientation-euler-safe-paired-cauchy-completeness`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[TOP-DOWN INTERFACE DISCHARGE]`, `[VALUE RELATION]`
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal parents:**
  `RHTower/XiHurwitzOrientationWeilSector.lean`,
  `RHTower/XiHurwitzOrientationPositivePairedSource.lean`,
  `RHTower/XiWeilResolventSource.lean`
- **Paper parents:**
  `critical-logderivative-euler-safe-cauchy-loss-law.md`,
  `critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`
- **Statement:** The canonical Xi--Hurwitz orientation vector lies in the real Hilbert closure of
  Schwarz-paired Cauchy vectors whose two poles are entirely in absolute Euler convergence.  One
  fixed open quadrant, and hence one countable Gaussian-rational grid in it, is complete.  Thus
  the Euler-safe Cauchy-loss criterion only has to be proved on real conjugation-odd finite
  packets; continued-strip poles, a high-frequency cutoff, and the low-frequency quartet band are
  unnecessary for this source interface.

## Setup

Put

```text
X(w)=xi(1/2+w),
L(w)=X'(w)/X(w).                                           (1)
```

Fix `a>1/2` and let

```text
H_a^+={w in C : Re(w)>a and Im(w)>0}.                     (2)
```

Every `w in H_a^+` satisfies `Re(1/2+w)>1`, as does its conjugate.  Hence `L(w)` and
`L(conj(w))` are given by the ordinary absolutely convergent prime--Gamma formula

```text
L(w)
 =1/s+1/(s-1)-1/2 log(pi)+1/2 psi(s/2)
  -sum_(n>=2) Lambda(n)n^(-s),
s=1/2+w.                                                   (3)
```

In the centered spectral coordinate write

```text
z=-i*w,
z#=-conj(z)=-i*conj(w),
C_z(q)=1/(alpha_q-z),
P_w=C_z-C_(z#),                                           (4)
```

where `alpha_q=xiSpectralPoint(q)` and multiplicity copies are retained.  Both `z` and `z#`
correspond through `s=1/2+i*z` to the two conjugate absolute-Euler points
`1/2+w` and `1/2+conj(w)`.

Let `J` be ordinary Schwarz conjugation on the multiplicity-exact Xi `ell^2` carrier, as in
`xiWeilSchwarzLp`.  The formal corpus proves

```text
J(C_z)=-C_(z#),                                           (5)
```

and consequently

```text
J(P_w)=P_w.                                               (6)
```

The canonical orientation vector `v_Xi` is real-valued, constant on every exact multiplicity
fiber, and invariant under ordinary Schwarz conjugation.  Thus it belongs to the closed real
fiber-constant fixed sector

```text
H_fib^J={v : v is fiber-constant and J(v)=v}.             (7)
```

## Absolute-Euler paired completeness theorem

`[PROVED]` The closed real span of

```text
{P_w : w in H_a^+}                                       (8)
```

contains `H_fib^J`.  In particular,

```text
v_Xi in closure_R span_R {P_w : w in H_a^+}.             (9)
```

The same closure is obtained if `w` is restricted to

```text
Q(i) intersect H_a^+.                                    (10)
```

No zero is selected in `(8)` or `(10)`, and the pole domain is fixed before inspecting the Xi
divisor.

### Proof

It is enough to prove that the real orthogonal complement of `(8)` inside `H_fib^J` is zero.  Let
`v` belong to that complement and define its Cauchy transform

```text
F_v(z)=<v,C_z>.                                           (11)
```

The reciprocal-square summability of the Xi divisor and Cauchy--Schwarz give locally uniform
convergence of `(11)` off the centered divisor.  Hence `F_v` is meromorphic, with at most simple
poles at the distinct spectral fibers.  Because `v` is fiber-constant, the residue at a fiber
`alpha` is a nonzero fixed scalar multiple of that fiber coefficient of `v`.

The antiunitary law `(5)` and `J(v)=v` give

```text
F_v(z#)=-conj(F_v(z)).                                    (12)
```

Real orthogonality to `P_w=C_z-C_(z#)` therefore gives

```text
0=Re <v,P_w>
 =Re(F_v(z)-F_v(z#))
 =2 Re(F_v(z))                                            (13)
```

on the nonempty open quadrant corresponding to `H_a^+`.  A holomorphic function whose real part
vanishes on an open set is constant there.  Analytic continuation makes `F_v` the same constant
on the connected complement of the discrete centered divisor.

Along a ray going vertically away from the spectral strip, the Cauchy vectors tend to zero in
`ell^2`.  This follows by separating finitely many bounded spectral fibers and dominating the
tail by the summable reciprocal-square divisor mass.  Hence the constant is zero.  Every residue
of `F_v` is zero, and fiber constancy then gives `v=0`.  This proves `(9)`.

The map `w |-> P_w` is norm-continuous on `H_a^+`.  Gaussian rationals are dense there, so `(10)`
has the same closed real span.

## Exact absolute-Euler value kernel

Define on `H_a^+`

```text
K_pair(w,u)
 =2 Re(
    (L(w)+conj(L(u)))/(w+conj(u))
    -(L(w)+L(u))/(w+u)).                                  (14)
```

`[PROVED]` For every finite family `w_j in H_a^+` and real coefficients `r_j`,

```text
xiWeilHilbertQuadratic(sum_j r_j P_(w_j))
 =sum_(j,k) r_j r_k K_pair(w_j,w_k).                      (15)
```

### Proof of the value relation

Let `T(z)=XiC'(z)/XiC(z)`.  Since `XiC(z)=X(i*z)`,

```text
T(-i*w)=i*L(w).                                          (16)
```

The target-side Cauchy polarization is the divided difference of the Xi relative trace.  Its
Schwarz and even reflections replace the apparently unsafe values at `conj(z)` and `-z` by the
conjugate and the negative of the safe value at `z`.  Substituting `z=-i*w` and `q=-i*u` in the
four-block paired kernel gives

```text
(conj(T(q))-T(z))/(z-conj(q))
  =(L(w)+conj(L(u)))/(w+conj(u)),

(T(q)+T(z))/(z+q)
  =-(L(w)+L(u))/(w+u).                                   (17)
```

Adding the conjugate blocks yields `(14)`--`(15)`.  Formula `(3)` then shows that every entry is
an absolute-Euler prime--Gamma value.  Meromorphic continuation into the critical strip is not
used by the criterion.

The kernel `(14)` is real and symmetric.  Positivity on real coefficient vectors is therefore
equivalent to its ordinary complex positive semidefiniteness.

## Countable absolute-Euler criterion

For any fixed rational `a>1/2`, define

```text
XiEulerSafePairedPassivity(a) :=
  for every N,
      w_1,...,w_N in Q(i) intersect H_a^+,
      r_1,...,r_N in Q,
  0 <= sum_(j,k) r_j r_k K_pair(w_j,w_k).                 (18)
```

`[PROVED]`

```text
XiEulerSafePairedPassivity(a)
  <-> RH.                                                 (19)
```

Indeed, `(18)` extends by coefficient and node continuity to the real algebraic paired core.
Equation `(9)` and continuity of the bounded Weil Hilbert quadratic then give

```text
0<=xiWeilHilbertQuadratic(v_Xi).                          (20)
```

The formal one-vector Weil theorem identifies `(20)` with RH.  Conversely RH makes the complete
square-summable Xi Weil form nonnegative, so it gives every matrix inequality in `(18)`.

This is not claimed as an RH proof: `(18)` is the remaining source positivity assertion.  The
gain is the strict reduction of its test domain and values.

## Restricted Cauchy--Laplace observability

The Euler-safe Cauchy-loss card defines, on `Re(w)>a`,

```text
K_0(w,u)=(L(w)+conj(L(u)))/(w+conj(u))                   (21)
```

and proves that its finite quadratic form is the Cauchy--Laplace observability deficit.  The
kernel `(14)` is exactly the doubled conjugation-odd restriction of `(21)`.  For
`w_j in H_a^+` and real `r_j`, use the doubled nodes

```text
(w_j,conj(w_j)) with coefficients (r_j,-r_j).            (22)
```

Thus the formerly required observability inequality for arbitrary complex packets can be
replaced by the same inequality only for

```text
G(t)=sum_j r_j(
       1/(w_j-a-i*t)-1/(conj(w_j)-a-i*t)),               (23)

G_x(t)=sum_j r_j(
       exp(-w_j*x)/(w_j-a-i*t)
       -exp(-conj(w_j)*x)/(conj(w_j)-a-i*t)).             (24)
```

Equivalently, after the tail-Laplace conjugation, the stationary completed Weil form only has to
be proved nonnegative on the damped sine packets

```text
f(y)=sum_j r_j(exp(-w_j*y)-exp(-conj(w_j)*y))
    =-2*i*sum_j r_j exp(-Re(w_j)*y) sin(Im(w_j)*y).       (25)
```

All parameters and coefficients in `(23)`--`(25)` may be rational.  This is a genuine weakening
of the earlier Euler-safe task: arbitrary finite exponential packets are no longer required.

## What is discharged

The source-positivity chain can now be written

```text
absolute-Euler paired passivity on one rational quadrant
 -> positivity on the real paired Cauchy core
 -> v_Xi belongs to its Hilbert closure
 -> xiWeilHilbertQuadratic(v_Xi)>=0
 -> RH.                                                    (26)
```

Compared with the previous positive-paired continued-source theorem, `(26)` removes:

- analytically continued prime sums inside the critical strip;
- the exterior threshold `R`;
- the low-frequency off-line-quartet accretive band;
- arbitrary complex coefficient packets;
- arbitrary unpaired Euler-safe exponentials.

The remaining theorem is positive and precise:

```text
prove the explicit absolute-Euler Cauchy--Laplace inequality
only on the rational damped-sine packet class (25).       (27)
```

Horizontal Xi monotonicity proves the positive density used in that inequality but does not prove
the paired multi-node domination.  The de-Poissonization theorem also shows that moving farther
right cannot make `(27)` perturbative: the safe damping is exactly cancelled in the stationary
critical form.

## Formalization target

1. Define the absolute-Euler paired pole type and `P_w` using `xiWeilCauchyLp`.
2. Prove `J(P_w)=P_w` from `xiWeilSchwarzLp_continuedCauchy` after extending that elementary
   identity from the continued subtype to arbitrary regular points.
3. Formalize the real fixed fiber sector and the meromorphic Cauchy-transform completeness
   argument.
4. Prove `(14)`--`(15)` from `xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference`,
   `XiC_conj`, `XiC_even`, and the absolute source identity.
5. State the countable rational criterion `(19)` and the restricted observability splice.

No Lean theorem is claimed by this card.  Under the active no-computation boundary, no build,
lint, scratch evaluation, or numerical experiment was run.

## Literature calibration

The analytic ingredients are classical: uniqueness of meromorphic Cauchy transforms, the open
mapping theorem, density of reproducing kernels indexed by a uniqueness set, and the
Caratheodory/Herglotz realization of a positive-real function.  The contribution is the exact
collision of those facts with the formal Xi orientation sector and the absolute-Euler
prime--Gamma value formula.  It is conservatively classified as proof infrastructure rather than
new scientific knowledge.

## Gates

- [x] absolute-Euler conjugate-pair domain identified
- [x] paired Cauchy vectors shown Schwarz-fixed
- [x] open-quadrant Cauchy-transform completeness proved
- [x] high-frequency cutoff and quartet-band inputs removed
- [x] exact absolute-Euler paired kernel derived
- [x] countable Gaussian-rational reduction proved
- [x] arbitrary packets reduced to real damped-sine packets
- [x] exact chain to the formal one-vector Weil criterion proved
- [ ] formalize the completeness and value identities in Lean
- [ ] prove paired absolute-Euler passivity `(18)`
- [ ] deduce RH

## Log

- 2026-07-15 -- Codex: obtained by combining the newly formalized positive-paired orientation
  sector with absolute-Euler Cauchy-loss values and replacing local pole collision by global
  Cauchy-transform uniqueness.  No computation or Lean build was used.

## Lean formalization (complete and unconditional)

- `formal/GaloisForLFunctions/RHTower/XiCauchyTransformCompleteness.lean` — the Cauchy transform of
  a square-summable divisor vector is holomorphic off the divisor, decays along a vertical ray, and
  is killed by a vanishing real part on any divisor-free ball.
- `formal/GaloisForLFunctions/RHTower/XiEulerSafePairedCompleteness.lean` — the absolute-Euler pole
  type, the paired vector `P_w` and its Schwarz fixedness `(6)`, the real pairing formula `(13)`,
  and the completeness theorem: a Schwarz-fixed fibre-constant vector orthogonal to every paired
  vector of the quadrant is zero.
- `formal/GaloisForLFunctions/RHTower/XiEulerSafePairedClosure.lean` — the closed real Schwarz-fixed
  fibre-constant sector `(7)`, membership of the canonical orientation vector, equation `(9)`, and
  the criterion `(26)` `riemannHypothesis_iff_xiEulerSafePairedPassivity`.
- `formal/GaloisForLFunctions/RHTower/XiEulerSafePairedValueKernel.lean` — the absolute-Euler
  logarithmic derivative, the four Schwarz blocks of the paired Weil polarization, the exact paired
  value kernel `(14)`, the packet identity `(15)`, the observability kernel `(21)` and the doubled
  conjugation-odd splice `(22)`.
- `formal/GaloisForLFunctions/RHTower/XiEulerSafePairedRationalCriterion.lean` — density of the
  Gaussian rationals, the countable completeness theorem, and the criterion `(19)`
  `riemannHypothesis_iff_xiEulerSafePairedRationalPassivity`.
