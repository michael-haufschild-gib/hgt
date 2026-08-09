# UV corner NC-torus attack, step 1 done (2026-08-09)

Card: docs/drafts/pipeline/1-in-progress/universal-law-field/uv-corner-noncommutative-torus-charter.md (ULF-FIELD-3)

## Proved on paper (A–D)
A: U f(u) = √2 e^{u/2} f(e^u) intertwines dilation-by-p with translation-by-log p EXACTLY
   (no multiplier); central window ↦ half-line u ≤ log a; corner = WH cross-compression, AP
   frequency group Γ = ℤlog p + ℤlog q. (Corpus dilation convention: (D_r f)(x) = √r f(rx).)
B: log q/log p irrational for p ≠ q primes (unique factorization).
C: Γ dense; corpus's noncompactness shell-witness = dense-semigroup no-minimal-element
   mechanism; wall is categorical, not one failed comparison.
D: ℝ-order on Γ = ordering of prime powers p^m q^n vs 1 = ordered K₀(A_θ), θ = log q/log p
   (Rieffel/Pimsner–Voiculescu import). This is the E2 one-sided invariant at the UV wall:
   unconditional, non-trace-class, phase-locked. Phase-locking opening ≡ E2 transport ≡ this
   K-order — ONE invariant.

## Corpus facts used (verified in-tree this session)
- archimedeanPrimeEulerQuadraticCorner = (corner_p)† ∘L corner_q, Euler scalar (−1/√p)(−1/√q),
  unitary push via archimedeanDualHardyTitchmarshUnitary.
- isCompactOperator_centralFourierPhysicalBlock (Landau–Pollak) ⟹ Calkin Sonin projection =
  1 − p_time − p_band.
- Essential-norm lower bound = Euler coefficient product 1/√(pq) — must equal the AP symbol
  modulus under the gated identification (consistency check).

## Gates before promotion
Murphy (Ordered groups and Toeplitz algebras, JOT 1987); Muhly–Renault (WH groupoid, exact
no-compacts statement); Ji/Ji–Xia (Toeplitz extensions of irrational rotation algebras);
Douglas–Howe quarter-plane (falsifier 1: band-side gluing may replace the torus);
corpus Calkin modules (SoninEssentialNormExtensions, SchattenApproximation,
XiPrimeSeamCalkinGram); Laca–Raeburn BC phase-transition collision check.
