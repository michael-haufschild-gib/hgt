# Route U: hard-edge reciprocal-clearing root classification

## Status

Formalized in Lean. Exact checked-in source compiles in an isolated `/tmp` object tree; theorem
surface and axiom audit pass from that scratch object. Module is wired into the Route-U umbrella.

- **Stage:** 3-formalized
- **Type:** BRIDGE / ROUTE-U POSITIVE SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Lean artifact:**
  `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeReciprocalClearingHyperbolicity.lean`
- **Axiom audit:** only `propext`, `Classical.choice`, `Quot.sound`

## Obstacle and pivot

The fixed-carrier scalar-budget conjecture fails. Existing exact countermodels satisfy the
sector, radius, moment, and global-energy constraints while producing either first-crossing
orientation. No tightening of that scalar package can close Route U.

The positive survivor is the canonical first-contact mixed source/null-line geometry. Its paper
compactness theorem uses a Möbius/reciprocal hard-edge numerator and needs exact preservation of
real-rootedness. The corpus has reciprocal clearing and real-simple Hankel null polynomials, but
not their complex root classification after clearing.

## Conjecture U-HERC

For `P ∈ ℝ[X]`, `deg P ≤ N`, mass `y ∈ ℝ`, and

`S(U) = (P.reflect N)(U + y) = (U+y)^N P((U+y)⁻¹)`,

every complex zero `u` of `S` obeys exactly one of the following alternatives:

1. `u + y = 0`, the exceptional pole root, possible exactly when `coeff P N = 0`;
2. `u + y ≠ 0` and `(u+y)⁻¹` is a zero of `P`.

Consequently, if every complex zero of `P` is real, every complex zero of `S` is real. Applied to
the canonical shifted-Xi first-singular Hankel null polynomial, the hard-edge cleared carrier has
only real complex zeros.

## Exact paper proof

Let `w = u+y` and map coefficients from `ℝ` to `ℂ`. Polynomial map commutes with reflection,
composition, and evaluation, so `S(u) = (P_ℂ.reflect N)(w)`.

If `w = 0`, evaluation at zero selects coefficient zero of the reflected polynomial. By the exact
reflection coefficient law and `revAt N 0 = N`, this is `P.coeff N`. This proves the exceptional
branch.

If `w ≠ 0`, give `w⁻¹` its field invertibility structure and apply the reflection zero equivalence
at `x = w⁻¹`. Since the inverse-of-inverse is `w`,

`(P_ℂ.reflect N)(w) = 0 ↔ P_ℂ(w⁻¹) = 0`.

For root reality, the exceptional branch gives `u = -y`, hence `Im u = 0`. In the nonexceptional
branch, root reality of `P` gives `Im(w⁻¹) = 0`. The identity

`Im(w⁻¹) = - Im(w) / normSq(w)`

and `normSq(w) > 0` force `Im(w) = 0`; because `y` is real, `Im u = 0`.

The shifted-Xi specialization uses the existing finite-moment theorem: a nonzero null vector on a
singular block with positive-definite predecessor produces a polynomial whose every complex zero
is real. Its degree is exactly the predecessor size, so clearing at that exact depth has no
exceptional pole root, although the generic classification does not need this strengthening.

## Hostile audit

- No sign, energy, or numerical premise occurs.
- No finite sample or computation certifies the statement.
- Exceptional degree-drop root is retained, not silently divided away.
- Result alone does not prove compactness or RH. It closes the exact finite-root preservation gap
  needed before a Laguerre-Pólya first-contact limit can be formalised.
- Generic reciprocal root transport is classical algebra. Corpus novelty is the exact theorem and
  its canonical shifted-Xi hard-edge specialization, previously present only as a paper step.

## Lean artifact and audit

`GaloisForLFunctions.RHTower.XiShiftedHardEdgeReciprocalClearingHyperbolicity` contains:

1. mapped complex evaluation identity;
2. exact value at the reciprocal-chart pole;
3. exact exceptional/nonexceptional zero classification;
4. generic root-reality preservation;
5. canonical first-face pole exclusion and reciprocal-zero classification;
6. canonical first-face real-rootedness specialization.

Verification used no project or umbrella build. Exact source was compiled with Lean into
`/tmp/route_u_reciprocal_clearing_source.olean`, then a scratch audit imported that object and
checked all six exported theorems. `#print axioms` reports only the standard mathlib axioms listed
above. Umbrella import is present in `formal/GaloisForLFunctions/RHTower.lean`.
