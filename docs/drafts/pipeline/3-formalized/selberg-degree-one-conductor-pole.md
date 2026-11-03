# Degree-one conductor or pole

- **ID:** selberg-degree-one-conductor-pole
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Γ33
- **Statement:** Every extended degree-one Selberg function has presentation conductor `q ≥ 2m₀` or a genuine pole at one, where `m₀` is its first nonzero coefficient index. In the full class, `q ≥ 2` or a genuine pole at one.

## Proof

Suppose the meromorphic order at one is nonnegative. The analytic punctured germ makes the polar residue in the cusp expansion zero. Rescaling the cusp coordinate gives an analytic extension `G` of `φ(z) = Σa(n)e^(−nz)` to `|z| < 2πm₀/q`.

If `q < 2m₀`, the extension radius exceeds `π`. The identity theorem propagates `G(z+πi) = G(z−πi)` across the overlap disk. Choose a rectangle with real coordinates `−a,a` and imaginary coordinates `−π,π` inside the extension disk, with `a > 0`. Integrating `G(z)e^(nz)` cancels the horizontal edges. Fourier orthogonality on the right edge extracts `2πa(n)`; boundedness on the compact left edge gives `|a(n)| ≤ C e^(−an)`.

Thus the Dirichlet series converges absolutely at zero. The unconditional positive-degree abscissa theorem excludes this. Consequently `q ≥ 2m₀` or the meromorphic order at one is negative. The full-class normalization `a(1)=1` gives `m₀=1`.

## Lean certificate

Namespace `GaloisForLFunctions.SelbergClass`:

- `degreeOne_conductor_bound_or_pole`: extended-class dichotomy.
- `full_degreeOne_conductor_bound_or_pole`: normalized full-class dichotomy.
- `exists_degreeOne_disk_extension_of_order_nonneg`: cusp continuation with the polar part discharged.
- `degree_eq_zero_of_disk_extension`: an ordinary generating function extending analytically to a disk of radius greater than `π` forces degree zero.

Sources: `SelbergClass/DegreeOneConductorPole.lean`, `DiskContinuationCoefficientDecay.lean`, and `OrdinaryFourierExtraction.lean`; all imported by `SelbergClass.lean`. Canonical checks passed. Six transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

The extended-class theorem needs neither an Euler product nor the Ramanujan bound. Meromorphic order avoids dependence on the totalized value or pole-clearing exponent at one. The degree-one classification and Γ15 selection problem remain open.
