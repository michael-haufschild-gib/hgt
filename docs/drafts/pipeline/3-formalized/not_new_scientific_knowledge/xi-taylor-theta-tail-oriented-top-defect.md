# Xi Taylor theta-tail oriented top-defect decomposition

- **ID:** `xi-taylor-theta-tail-oriented-top-defect`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent target:**
  `../../1-in-progress/xi-taylor-oriented-finite-coefficient-sublinear-flux.md`

## Statement

For a complex polynomial `P`, write

```text
J_P(z) = Im(P'(z) conjugate(P(z))).
```

Let `c_k` and `Q_d` be the finite theta-tail coefficients and polynomial from the coefficient
telescope, and set

```text
U_d(z) = 1/2 - (z^2+1/4) Q_d(-z^2),
E_d(z) = ((-1)^(d+1)c_(d+1)/4) z^(2d+2).
```

Then the actual canonical Xi Taylor polynomial satisfies the exact finite source splitting

```text
P_(2d+3)(z) = U_d(z) - E_d(z).                           (1)
```

For every real `a`, natural `m`, and `Im z >= 0`,

```text
J_(a z^m)(z)
  = -m a^2 |z|^(2m-2) Im z <= 0.                        (2)
```

In particular, the explicit top defect has favorable upper-half-plane orientation:

```text
J_(E_d)(z) <= 0.                                         (3)
```

The exact polarization identity gives

```text
J_(U-E)
 = J_U
   - Im(U' conjugate(E))
   - Im(E' conjugate(U))
   + J_E.                                                (4)
```

Consequently, on `Im z >= 0`,

```text
J_(P_(2d+3))(z)
 <= J_(U_d)(z)
    + |U_d'(z)| |E_d(z)|
    + |E_d'(z)| |U_d(z)|.                                (5)
```

Thus the top defect cannot itself create positive upper flux.  The remaining finite problem is
exactly the orientation of the theta-tail core and the two explicit cross-interference terms.

## Proof

The coefficient telescope gives `(1)` after the substitution `w=-z^2`.  For the monomial
`M(z)=a z^m`,

```text
M'(z) conjugate(M(z))
 = m a^2 z^(m-1) conjugate(z)^m
 = m a^2 |z|^(2m-2) conjugate(z).
```

Taking imaginary parts proves `(2)` and `(3)`.  Expanding
`(U'-E') conjugate(U-E)` proves `(4)`.  Apply
`|Im w| <= |w|`, multiplicativity of the complex norm, and `(3)` to obtain `(5)`.

No zero location, real-rootedness, anti-Herglotz condition, or limiting measure enters the proof.

## Lean realization

File:

```text
formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailOrientedDefect.lean
```

Principal declarations:

```text
evenMagnitudeLift
xiCTaylorPolynomial_oddCutoff_eq_evenMagnitudeLift
orientedPolynomialCurrent_monomial
orientedPolynomialCurrent_monomial_nonpos
orientedPolynomialCurrent_sub_exact
orientedPolynomialCurrent_sub_le
xiCTaylorPolynomial_oddCutoff_succ_eq_thetaTailCore_sub_topDefect
xiCTaylorThetaTailTopDefect_current_nonpos
xiCTaylor_orientedCurrent_le_thetaTailCore_add_interference
```

The module builds with no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

## Gates

- [x] exact source core/top-defect splitting proved on paper
- [x] monomial orientation formula and upper-half-plane sign proved
- [x] exact current polarization proved
- [x] interference upper bound proved
- [x] all statements formalized in Lean
- [ ] theta-tail core current proved sublinear on the anisotropic mesh
- [ ] cross-interference proved negligible relative to the Taylor value there
