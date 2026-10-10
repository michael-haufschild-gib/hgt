# TG — the Gaussian Chebyshev conjecture (prime sign law)

- **ID:** TG-CHEB-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Source:** TG-BUD-1 / TG-EXP-1 (central budget, growth law), Mertens' first theorem (corpus `Mertens.mertens_first`)
- **Statement:** Π(y) = Σ_p (log p) p^{-1/2} e^{-yp²}, C(y) = ∫₁^∞ u^{-1/2}e^{-yu²}du, Q(y) = Σ Λ(m) m^{-1} e^{-ym⁴},
  D = P − Π (higher prime powers of the central mass P).
  (a) Gaussian quartic Mertens: |Q(y) − ¼log(1/y)| ≤ 2(log 2 + 3(log 4 + 4)) on (0,1].
  (b) Sandwich Q ≤ D ≤ 2Q.
  (c) RH ⇒ Π(y) − C(y) ≤ K − ¼log(1/y) on (0,1].
  (d) RH ⟺ Π(y) − C(y) → −∞ (y → 0⁺) ⟺ Π(y) < C(y) eventually ⟺ Π − C eventually bounded above.

## Proof
(a) N = ⌊y^{-1/4}⌋. Lower: e^{-v} ≥ 1−v on m ≤ N, Mertens, ψ(N) ≤ (log 4+4)N. Upper: dyadic
blocks (N2^k, N2^{k+1}], each Mertens mass ≤ log 2 + 2(log 4+4), Gaussian weight ≤ e^{-16^k/16} ≤ e^{-k}.
(b) Squares m² of prime powers give exactly Q (Λ(m²) = Λ(m)); every odd higher prime power p^{2j+1}
is minFac(m)·m² for m = p^j, the map m ↦ minFac(m)·m² is injective, and its term is ≤ the m² term.
(c) P ≤ C + K₀ (central budget), Π = P − D ≤ P − Q.
(d) Eventual Π − C ≤ B ⇒ P − C ≤ B + 2Q = O(log(1/y)) ≤ B_ε y^{-ε} ⇒ growth law ⇒ no zero right of ½+2ε, ∀ε.

## Lean
`RHTower/GaussianPrimeChebyshevBias.lean` (727 lines), wired after GaussianGapSignAbscissa. Key:
`abs_gaussianQuarticMertensMass_sub_log_le`, `gaussianQuarticMertensMass_le_primePowerDefect`,
`primePowerDefect_le_two_mul_gaussianQuarticMertensMass`, `minFac_mul_sq_injective`,
`exists_gaussianPrimeOnlyGap_le_of_riemannHypothesis`, `riemannHypothesis_iff_tendsto_gaussianPrimeOnlyGap_atBot`,
`riemannHypothesis_iff_eventually_gaussianPrimeOnlyMass_lt`. Build exit 0, no warnings; no declaration > 3 s;
axioms [propext, Classical.choice, Quot.sound].

## Reading
ζ-analogue of the Hardy–Littlewood–Landau theorem on Chebyshev's conjecture (χ₋₄): over primes the
Gaussian bias is the prime-square drift −¼log(1/y) (plus the archimedean −0.686 of TG-BIAS-1), so
the prime sum is eventually below the continuum exactly under RH. Sieve-side TG target: one
eventual upper bound Π ≤ C + B for the PRIMES alone is RH.
