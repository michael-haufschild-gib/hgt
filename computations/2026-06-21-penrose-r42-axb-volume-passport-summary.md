# R42 - affine ax+b volume passport

Status: non-reducing gatekeeper finding.

Random source chain:
- incoming RandomNode: determinant gives squared volume, so near-linear dependence among selected feature vectors suppresses joint probability
- broad topic RNG: 7, Lyapunov spectrum volume contraction in chaotic attractors
- NODE RNG: 2, volume contraction is given by the sum of Lyapunov exponents over the relevant tangent subspace
- target-file RNG: 2, `docs/consolidated/01-landscape-and-geometry.md`
- target-topic RNG: 3, affine `ax+b` geometry and the universal curvature
- scientific-method RNG: 17, representation
- perturbation-method RNG: 12, invariant

## Finding

For a finite boundary-mode block `S` with basis vectors `e_m`, the affine
archimedean generator

```text
partial_s e_m = -(m . log p) e_m
```

induces on the determinant line `Lambda^{|S|} V_S` the character

```text
tr(partial_s | V_S) = - sum_{m in S} m . log p.
```

Likewise

```text
det(sigma_p | V_S) = p^{-sum_{m in S} m_p}.
```

Thus every affine tangent-volume observable factors through the finite
passport

```text
Pi(S) = ( |S|, sum_{m in S} m ).
```

The universal curvature seen by this determinant line is only the passport
shift law

```text
tr(partial_s | V_{S+e_p}) - tr(partial_s | V_S)
    = - |S| log p.
```

This is the Lyapunov NODE transferred to the affine weld: "sum of exponents
over the relevant tangent subspace" becomes the determinant character of the
mode block, and that character forgets all shape inside the fiber of `Pi`.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r42-axb-volume-representation.py
```

Two distinct blocks have the same determinant passport `(3,(2,2,0))` and
therefore the same affine tangent-volume contraction:

```text
S1={(0,0,0),(2,0,0),(0,2,0)}
S2={(1,0,0),(0,1,0),(1,1,0)}
trace_D(S1)=trace_D(S2)=-3.583518938456
shape(S1)=(1.777777777777778, 0.888888888888889, 5.333333333333333)
shape(S2)=(0.4444444444444445, 0.22222222222222224, 1.3333333333333333)
```

The universal shift check is exact to displayed precision:

```text
shift by e_2: delta_trace=-2.079441541680, -dim(S)log(2)=-2.079441541680
shift by e_3: delta_trace=-3.295836866004, -dim(S)log(3)=-3.295836866004
shift by e_5: delta_trace=-4.828313737302, -dim(S)log(5)=-4.828313737302
```

Invariant-fiber growth in the finite search space:

```text
k=2: passports=143, nontrivial_fibers=113, max_fiber=9,    max_shape_spread=4.000000, max_trace_spread=1.776e-15
k=3: passports=373, nontrivial_fibers=325, max_fiber=69,   max_shape_spread=5.333333, max_trace_spread=1.776e-15
k=4: passports=749, nontrivial_fibers=661, max_fiber=340,  max_shape_spread=4.500000, max_trace_spread=3.553e-15
k=5: passports=1265, nontrivial_fibers=1151, max_fiber=1471, max_shape_spread=4.800000, max_trace_spread=3.553e-15
```

## Consequence

Any experiment that only measures affine determinant volume, summed Lyapunov
exponents, or compound determinant contraction is guaranteed to be
RH-blind/holonomy-blind at the `ax+b` layer. It can at most recover `Pi(S)`.

The first meaningful seam experiment has to quotient out this determinant
passport and inspect trace-free fiber data: covariance of mode clouds,
non-affine holonomy, or another normalized observable that survives after
the universal `-|S| log p` curvature term is removed.

This is not RH content. It is a gatekeeper: determinant-volume evidence is
admissible only after reporting and subtracting the affine volume passport.
