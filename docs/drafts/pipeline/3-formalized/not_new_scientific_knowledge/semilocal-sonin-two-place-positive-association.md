# Semilocal Sonin two-place positive association

- **ID:** semilocal-sonin-two-place-positive-association
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); formal core in Lean
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Lean core:** `formal/GaloisForLFunctions/RHTower/SoninSemilocalTwoPlaceAssociation.lean`
- **Parent source:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Theorem 3.1 and Section 4.3

## Statement

Let

`dmu_infinity(s) = (2 pi)^(-3/2) |Gamma(1/4 + i s/2)|^2 ds`.

This is the probability spectral measure of the archimedean cyclic pair. For a prime `p`, put

`r_p = p^(-1/2)`, `ell_p = log p`, and

`G_p(s) = |1 - r_p exp(i ell_p s)|^(-2)`.

For any two distinct primes `p,q`,

`int G_p G_q dmu_infinity > (int G_p dmu_infinity)(int G_q dmu_infinity)`.

Equivalently, if

`Z_T = int prod_(p in T) G_p(s) dmu_infinity(s)`,

then

`Z_{p,q} Z_empty > Z_p Z_q`

and hence

`log Z_{p,q} - log Z_p - log Z_q + log Z_empty > 0`.

Thus the unnormalized degree-zero Gram mass has a strictly positive two-place mixed logarithmic
cross-effect. This is a true source identity, but it is not an invariant of the normalized cyclic
pair and does not change the orthogonal-polynomial grading by itself.

## Proof

The classical Gamma Fourier integral, with the normalization above, gives the characteristic
function

`phi(t) = int exp(i t s) dmu_infinity(s) = (cosh t)^(-1/2)`.

For `u,v>0`, evenness gives

`int cos(us) cos(vs) dmu_infinity(s)
   = (phi(u+v) + phi(u-v))/2`.

Write

`X = cosh(u) cosh(v)`, `Y = sinh(u) sinh(v)`.

Then `X>Y>0`, `cosh(u+v)=X+Y`, and `cosh(u-v)=X-Y`. The function
`x |-> x^(-1/2)` is strictly convex on `(0,infinity)`, so

`(phi(u+v)+phi(u-v))/2 > X^(-1/2) = phi(u)phi(v)`.

Therefore every pair of positive cosine frequencies has strictly positive covariance. The Lean
theorem `semilocalArchimedean_twoFrequencyAssociation_pos` formalizes exactly this strict inequality.

For `0<r<1`, the Poisson expansion is uniformly absolutely convergent:

`|1-r exp(i theta)|^(-2)
   = (1-r^2)^(-1) (1 + 2 sum_(n>=1) r^n cos(n theta))`.

Consequently Tonelli's theorem and uniform absolute convergence give

`Cov(G_p,G_q)
 = 4 / ((1-r_p^2)(1-r_q^2))
     sum_(m,n>=1) r_p^m r_q^n
       Cov(cos(m ell_p s), cos(n ell_q s))`.

Every summand is strictly positive by the preceding inequality, and every coefficient is positive.
Hence the covariance is strictly positive. Taking logarithms yields the determinant cross-effect.

## Decisive attack and limits

- `[PROVED]` The strict cross-ratio excludes factorization of the unnormalized partition mass.
- `[REFUTED AS A ROUTE-B INVARIANT]` A cyclic pair uses a unit cyclic vector, so its spectral measure
  is normalized to total mass one. Multiplying a measure by a positive scalar does not change its
  orthogonal polynomials, Jacobi matrix, or number operator. The degree-zero Gram determinant is
  therefore removable normalization data, not a prolate naturality defect.
- `[REFUTED AS NEW SCIENTIFIC KNOWLEDGE]` The proof combines standard Gamma Fourier and Poisson
  identities into a correct inequality, but after normalization it neither distinguishes the
  semilocal grading nor advances the Sonin cutoff problem. It fails the significance half of the
  novelty--significance gate.
- `[PROVED]` The mixing is archimedean-mediated. If the Gamma spectral measure were replaced by a
  product law making the cosine modes independent, the argument would collapse.
- `[PROVED]` No zero divisor, RH assumption, numerical experiment, prime exhaustion, or limiting
  cutoff enters the proof.
- `[OPEN CORE]` The result concerns the cyclic spectral measure before Sonin cutoff. It does not prove
  that the mixed term survives the Sonin projection, the prolate naturality corner, a relative
  resolvent, or a determinant-line boundary.
- `[OPEN CORE]` It supplies no positivity theorem for the full Weil functional and therefore does not
  imply RH.

## Novelty and significance audit

- **Proof gate:** complete above; the strict analytic core is checked in Lean.
- **Significance gate:** failed. The claimed mixed quantity is erased by the normalization required
  for the source cyclic pair and cannot by itself affect `N_S` or `W_{lambda,S}`.
- **Parent-theory gate:** the Gamma Fourier integral, Poisson kernel, and strict convexity are known.
  Their combination into the canonical semilocal two-place determinant cross-effect is the claimed
  content; none of the ingredients alone states it.
- **Literature gate:** the parent paper explicitly defers the general finite-place Jacobi-coefficient
  computation. Searches of the Connes--Consani--Moscovici, Connes trace-formula, Burnol Sonin/conductor,
  hyperbolic-secant, and Poisson-kernel literature found no statement of this strict two-place
  association or determinant cross-ratio.
- **Rediscovery gate:** the logarithmic commutator/conductor mechanism and the semilocal trace formula
  were found in the parent literature and were excluded from the novelty claim.

The associated scale-invariant successor is the normalized all-even Jacobi residue tower in
`semilocal-all-even-jacobi-prolate-residue-tower.md`.

## Next move

Do not transport this scalar normalization through the Sonin cutoff. Use the normalized Jacobi
coefficient and its explicit low-mode prolate naturality residue instead.

## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/RHTower/SoninSemilocalTwoPlaceCovariance.lean`
(namespace `RHTower.SemilocalTwoPlace`, wired into the `GaloisForLFunctions.RHTower` umbrella).
The card's own "Lean core" line named only the strict convexity step; the whole theorem — the
actual measure, the Poisson expansion, the Tonelli interchange, and the covariance — is now
proved unconditionally.

Reused from the corpus (not rebuilt):

| Existing input | Where |
|---|---|
| the measure `dμ_∞ = (2π)^{-3/2}\|Γ(1/4+is/2)\|² ds` and `∫ e^{its} dμ_∞ = (cosh t)^{-1/2}` | `RHTower/SoninSemilocalGammaMeasureCharacteristic.lean` |
| `IsProbabilityMeasure` for that measure | `RHTower/CCMMetaplecticGammaMomentDeterminacy.lean` |
| the real cosine transform `∫ cos(ts) dμ_∞ = φ(t)` | `RHTower/GammaEvenBoundaryParityNoGo.lean` |
| strict convexity of `x ↦ x^{-1/2}` and `φ(u)φ(v) < (φ(u+v)+φ(u−v))/2` | `RHTower/SoninSemilocalTwoPlaceAssociation.lean` |

| Card step | Lean name |
|---|---|
| `G_p(s) = \|1 − r_p e^{i ℓ_p s}\|^{-2}` | `primeFactor`, `primeFactor_eq_normSq_inv`, `primeFactor_eq_norm_zpow` |
| `∫ cos(us)cos(vs) dμ_∞ = (φ(u+v) + φ(u−v))/2` | `integral_cos_mul_cos_gamma` |
| every pair of positive cosine frequencies has strictly positive covariance | `gammaCosCovariance`, `gammaCosCovariance_pos` |
| a zero frequency contributes zero covariance | `gammaCosCovariance_zero_left/right`, `gammaCosCovariance_nonneg` |
| the Poisson expansion `\|1−re^{iθ}\|^{-2} = (1−r²)^{-1}(1 + 2Σ_{n≥1} r^n cos nθ)` | `hasSum_poissonExpansion`, `hasSum_primeFactor`, `hasSum_pfMode` |
| uniform absolute convergence ⟹ termwise integration | `integral_tsum_gamma` (from `MeasureTheory.integral_tsum`) |
| `∫ G_p dμ_∞` termwise | `integral_primeFactor` |
| `∫ G_p G_q dμ_∞` as a double series (Tonelli) | `hasSum_pfMode_prod`, `integral_primeFactor_mul` |
| the product of the one-place masses as the same double series | `integral_mul_integral_primeFactor` |
| `Cov(G_p,G_q) = 4 c_p c_q Σ_{m,n≥1} r_p^m r_q^n Cov(cos mℓ_p, cos nℓ_q)` | `covariance_eq_tsum` |
| every summand strictly positive ⟹ strictly positive covariance | `covariance_pos` |
| `Z_{p,q} Z_∅ > Z_p Z_q` | `semilocal_twoPlace_association` (with `integral_one_gamma : Z_∅ = 1`) |
| `log Z_{p,q} − log Z_p − log Z_q + log Z_∅ > 0` | `semilocal_twoPlace_log_crossEffect` (with `integral_primeFactor_pos`) |
| **the theorem for two primes** (`r_p = p^{-1/2}`, `ℓ_p = log p`) | `semilocal_prime_twoPlace_association` |

Two remarks on the formal statement.

* **Distinctness of `p, q` is not used.**  The proof needs only `0 < ℓ_p`, `0 < ℓ_q` and
  `r_p, r_q ∈ (0,1)`, so the Lean theorems are stated for arbitrary positive frequencies and
  radii; the primes enter only through `primeRadius_pos`, `primeRadius_lt_one`, `primeLog_pos`.
  This matches the paper proof, where the strict inequality `φ(u)φ(v) < (φ(u+v)+φ(u−v))/2` holds
  for all `u,v > 0` including `u = v`.
* **The `m = 0` or `n = 0` rows are handled, not excluded.**  The Poisson expansion is carried as
  a single sum over all `n ≥ 0` with weights `w_0 = 1`, `w_n = 2r^n` (`poissonWeight`), so the
  constant rows appear in the double series; `gammaCosCovariance_zero_left/right` show they
  contribute exactly `0`, which is what makes the term-by-term subtraction of the two double
  series legitimate.

**Not formalized (and not an obligation of this card).**  Both `[OPEN CORE]` items — survival of
the mixed term through the Sonin projection / prolate naturality corner, and any positivity
theorem for the full Weil functional — are stated on the card as open, not proved.  The
`[REFUTED AS A ROUTE-B INVARIANT]` and `[REFUTED AS NEW SCIENTIFIC KNOWLEDGE]` verdicts are
scientific-status judgements about normalization and significance, not mathematical propositions.

Verification: `lake build GaloisForLFunctions.RHTower.SoninSemilocalTwoPlaceCovariance` — PASS;
`#print axioms` on all 20 named results reports only `[propext, Classical.choice, Quot.sound]`.

## Formalization gate

- [x] 2 → 3 formalized: the full two-place association theorem is proved unconditionally in Lean,
      narrow build green, axiom audit clean.

## Log

- 2026-08-17 — formalized in Lean; the paper proof's Poisson expansion, Tonelli interchange and
  covariance assembly are all closed unconditionally; card moved to stage 3.
