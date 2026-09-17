# Route P — real-axis ambient-Hilbert obstruction: facts

## Certified facts

- `PrimeLogThetaRealAxisAmbientHilbertObstruction.lean` proves
  `‖primeLogCriticalLaplaceFeatureL2 p‖² = log p / p`.
- For every half-line Hilbert vector `b` and real axis coordinate `x`, it proves
  ```text
  <b, phi_p> / r_x(p) -> 0
  ```
  on the cofinite prime filter, with the explicit squared bound
  ```text
  |<b, phi_p> / r_x(p)|² <= ‖b‖² / (4 (log p)^3).
  ```
- Consequently no pair
  ```text
  a in l2(Primes),  b in L2((0,infinity))
  ```
  satisfies `r_x(p) = a(p) + <b, phi_p>` for every prime.  The proof uses the
  real-axis reporter's exact nonsummable mass and a finite-head/cofinite-tail
  comparison, not an asymptotic assumption about primes.
- Every `StrongDual ℂ Graph(cl primeLogCriticalLaplaceSynthesis)` reader is now
  excluded on the literal one-prime graph points.  Hahn--Banach extends it to the
  ambient Banach product; restrictions to the two coordinate inclusions yield two
  continuous Hilbert functionals, and separate Riesz representations reduce its
  prime values to the excluded source-plus-feature form.
- The product is a Banach product in this corpus, not an inner-product product.
  The certified reduction therefore does **not** use a nonexistent product Riesz
  vector: it uses the two coordinate restrictions.  This is a verified correction
  of the initially tempting but invalid one-vector formulation.

## Exact scope / survivor

- Route P cannot close through any ordinary continuous complex-linear reader of
  `Graph(cl primeLogCriticalLaplaceSynthesis)` that agrees with literal real-axis
  theta on all literal one-prime cores.  This entire category, not merely ambient
  Hilbert readers, is now formally eliminated.
- The survivor is exact: a non-continuous/distributional Calderón-type boundary
  morphism, or a changed source/target topology outside this closed-graph Banach
  category.  It must still preserve the four Wronskian levels and labelled mixed
  terms; calling it a continuous graph reader is formally impossible.

## Verification

- Source: `lake env lean GaloisForLFunctions/RHTower/PrimeLogThetaRealAxisAmbientHilbertObstruction.lean`.
- The extension theorem is `no_continuousClosedGraphReader_primeLogTheta_realAxis`.
- Target OLean: `lake build GaloisForLFunctions.RHTower.PrimeLogThetaRealAxisAmbientHilbertObstruction`.
- Axiom audit of the extension theorem: only `propext`, `Classical.choice`, and
  `Quot.sound`.
