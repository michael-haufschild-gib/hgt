# Monogenic law-discriminant observer-shadow theorem — formalized

- **ID:** `monogenic-law-discriminant-observer-shadow-theorem-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `monogenic-law-discriminant-observer-shadow-theorem.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicShadow` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/MonogenicShadow.lean` |
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler` | shared infrastructure |

Both wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — cotangent complex and Fitting ideal:

1. `kaehlerEquivMonogenic` (in `MonogenicKaehler`) — **card `(4)`**: `Ω[A⁄B] ≅ A/(f'(t)) dt`.
2. `range_mulLeft_rootDifferent` — the image of the presentation map `·f'(t)` is the different
   ideal.
3. `conormalCokerEquiv` — **card `(3)`**, degree-zero part: the cokernel of `A →^{f'(t)} A` is
   `Ω[A⁄B]`.
4. `mem_ker_mulLeft_rootDifferent` — **card `(5)`**: the degree-one homology of the conormal
   complex is the annihilator of `f'(t)`.
5. `norm_rootDifferent_eq_det` — the determinant of the square presentation of `Ω[A⁄B]` over `B` is
   the norm `N_{A/B}(f'(t))`; this is the zeroth Fitting ideal generator of card `(6)`.
6. `discr_eq_norm_different` — **card `(6)`**, the resultant identity:
   `Disc = (−1)^{n(n−1)/2} N(f'(t))` for a separable power basis.

Theorem 2 — split observer determinant:

7. `characterObserver_matrix` — **card `(8)`**: in the monomial basis the character observer is the
   Vandermonde matrix `(r_i^{j})`.
8. `det_characterObserver` — **card `(9)`**: `det V_f = ∏_{i<j}(r_j − r_i)`.
9. `fibreDiscriminant`, `sq_det_characterObserver` — **card `(10)`**: `(det V_f)² = Disc(f)`.
10. `det_characterObserver_ne_zero_iff` — the observer is invertible exactly when the roots are
    distinct, i.e. off the discriminant locus.

Corollary 3 — determinant conditioning:

11. `abs_det_characterObserver` — **card `(11)`**: `|det V_f| = |Disc f|^{1/2}`.  The product of the
    singular values of a square matrix is `|det|`, so this is exactly the stated product-conditioning
    law; the card itself notes that the smallest singular value is *not* determined by the
    discriminant, and nothing stronger is claimed here.

Five-shadow dictionary `(12)`–`(13)`:

12. `fibreOrientation_forgets` — positive magnitude forgets the orientation of the root product.
13. `fibreSupport_forgets` — support forgets the magnitude.
14. `fibreShadow_tower` — the support shadow factors through the magnitude shadow.

Items 1–4 realize the "relative law geometry" row, 8 the "root orientation" row, 7 and 11 the
"framed spectral observer" row, 9 and 12 the "positive magnitude" row, and 10 and 13 the
"topology/support" row of the card's table `(12)`.

## Corpus check

Before writing, `formal_tools.py research` and a grep over every module mentioning
`KaehlerDifferential` confirmed that the corpus had no computation of `Ω` for a monogenic algebra;
the corpus's existing Vandermonde/discriminant work (`DiscriminantPolynomial`,
`GenericPolynomialSeparable`, `CenteredDiscriminantIdentification`) is about the generic polynomial
and its symmetric functions, not about the observer matrix of a split fibre.

The RH specialization boundary:

- `mateQuad`, `mateQuad_eq_expand`, `eval_derivative_mateQuad`, `eval_derivative_mateQuad_one`,
  `discriminant_mateQuad`, `eval_derivative_mateQuad_eq_zero_iff`,
  `discriminant_mateQuad_eq_zero_iff` — **card `(14)`**: for the quadratic mate law
  `f(T) = (T−1)(T−δ)` the root different is `δ−1` at the moving root and `1−δ` at the fixed one,
  the discriminant is `(δ−1)²`, and both vanish **exactly** at `δ = 1`.  This locates the wall and
  the two-character collision; as the card insists, it does *not* force `δ = 1` — the statement is
  an iff about `δ`, with no arithmetic input.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/MonogenicShadow.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                               # green
```
