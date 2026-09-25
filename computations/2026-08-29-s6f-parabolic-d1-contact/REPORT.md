# S6F direct-D1 parabolic-cone hostile test

## Question

The projective-drift route is stronger than needed: native rank-three D1 only has to stay positive.
Does the already Lean-proved parabolic physical cone itself lie in the positive D1 chamber? If so,
is there a small geometric reduction that can replace a raw coefficient certificate?

Diagnostic only. No coefficient, digest, factorization output, root count, or corner value in this
folder is admissible in a Lean proof.

## Computation

RunPod host: 128 CPUs; Python/SymPy environment recorded in `environment.txt`. Scripts rebuild the
source-positive jets through order eight from the exact three-state Lie recursion, form D1 as the
literal `3×3` Hankel determinant, and transform to

```text
X = R², w = z², v = zy,
X = 191/10 + (147/20)w + S,
y = 13/32 + w/32 + eta(1/160 + 5w/96),
S >= 0, 0 <= w <= 9/100, 0 <= eta <= 1.
```

Power basis is used in unbounded scale slack `S`; exact Bernstein bases are used in `w` and
`eta`. Independent jobs run across multiple cores. `verify_results.py` independently reconstructs
D1 as a matrix determinant and uses a separate staged Bernstein transform.

## Outcomes

- **Direct-cone route survives.** The normalized D1 polynomial has degrees `(12,12,24)` and 819
  terms before cone substitution. All 13,975 exact half-prism Bernstein coefficients are strictly
  positive. This is stronger than projective-drift positivity for the finite gate: it places the
  whole formal cone directly inside the positive rank-three chamber.
- **Scale geometry is one-sided.** `∂D1/∂S` has all 12,750 coefficients positive and
  `∂²D1/∂S²` has all 11,550 positive. Thus the diagnostic minimum is at zero scale slack.
- **Clock-square geometry is concave.** `∂²D1/∂w²` has all 13,325 coefficients negative, while
  `∂³D1/∂w³` has all 13,000 positive. Hence a conceptual concavity proof would reduce `w` to its
  two endpoint faces.
- **Higher alternating hierarchy is false.** The sign-corrected fourth derivative is already mixed
  (`5,071` negative, `7,604` positive); every tested order through 24 remains mixed. The survivor
  is genuinely second-order, not Stieltjes/complete-monotone.
- **Wall interpolation is not globally monotone or concave.** First and second `eta` derivatives
  have mixed Bernstein signs. The third derivative is nonnegative, but this does not yield the
  desired minimum by itself.
- **Boundary reduction is exact.** At `w=0`, D1 is independent of `eta` and positive. At
  `w=9/100`, zero scale slack, the degree-24 `eta` polynomial has no derivative root in `[0,1]`;
  its derivative is negative at both endpoints, so it is strictly decreasing and its minimum is
  the upper outer corner.
- **Naive factorization route is dead.** D1 and its leading rank-two minor have no nonconstant
  factor over `QQ` in either source-positive `(U,B,Q)` or reconstructed
  `(U+B,B,16Q+6-6B²)` coordinates. Parabolic localization is essential.
- Independent verification passed:

```text
verified: direct D1 positive and scale-increasing; clock concavity survives, order-4 hierarchy fails; outer minimum is upper corner
```

## Consequences

This opens a better finite S6F route than projective drift. A computation-free proof can target:

1. scale monotonicity of D1 on the physical cone;
2. strict concavity in `w`;
3. positivity of the already formal seam face;
4. monotonicity and positivity of the single outer upper face.

That chain would prove D1 directly and avoids proving drift positivity everywhere. It also explains
why determinant geometry, not complete monotonicity, is the right invariant.

The computation additionally exposed the upper clock ratio and scale as dangerous directions.
Independent paper algebra then proved the sharper source cone

```text
v < (33/80+z²/16)z,
191/10+(37/5)z² < X,
```

now formalized without using any output from this folder. The stronger cone only shrinks the domain,
so the direct-D1 diagnostic survives a fortiori. Remaining open core is a conceptual proof of the
four-item direct-determinant reduction above, preferably via determinant second variation rather
than coefficient enumeration.
