# Uniform finite heads for the entire Haar prime source

- **ID:** acs-full-haar-prime-source-finite-heads
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Statement:** Approximate the entire original prime form on balanced
  complete cells by one finite coefficient head, in the original complete
  profile's Gamma norm, uniformly in the upper horizon.

## Target

For every ε>0, find A independent of q,d,X such that

`|haarPrimeEnergy d X − haarPrimeEnergy (fun a => if a<A then d(a) else 0) X|
  ≤ ε levyEnergy (completePairProfile q d X)`.

Every actual prime power, including first powers, must remain in the left
side. The head must be the original coefficient truncation. The existing
fixed logarithmic relative bound does not prove this approximation.

The desired consequence is an absolute, arbitrarily small Gamma error for
the full detail source after one fixed head, leaving the original Gamma
energy available for the unpaid coarse and first-prime mixed source.
This does not itself prove their sign or close ACS.

## Corpus evidence

- `HaarCellPrimeCompression.inner_shift_haarAtom` identifies the exact
  surviving incidence `(2a+1)m=2b+1`.
- `HaarCellPrimeBound.haarPrimeEnergy_matrix` retains the full prime form.
- Its outgoing rows have mass at most `16 haarMass(a)`; incoming rows
  use the exact von Mangoldt divisor identity.
- Complete-cell Gamma variance pays the weighted detail mass without
  suppressing arbitrary pair averages.

## Paper proof

Split prime multipliers at a fixed N. For m≥N, the incoming column bound
improves to `log(2b+1) haarMass(b)/sqrt(N)`, while the outgoing row bound
stays uniform. Weighted Cauchy–Schwarz therefore makes this entire
large-multiplier form small in logarithmic detail energy. This is a
uniform quadratic-form estimate, not convergence for fixed coefficients.

For the remaining finite multiplier set, translated Haar interactions
are bounded in square mass. Removing a large coefficient head makes their
error small because Gamma controls the remaining detail mass uniformly.
Combining the two cutoffs gives the literal full-source statement.

Here are the uniform estimates and quantifiers. Put
`w=cellGammaWeight(1)>0`, `E=Γ(completePairProfile q d X)`,
`M=Σ haarMass(a)d(a)²` and `D=Σ cellGammaWeight(a)haarMass(a)d(a)²`.
The actual variance theorem gives `w M≤D≤E`. Also
`L=Σ log(2a+1)haarMass(a)d(a)²≤D+2M≤(1+2/w)D`.

For any set of multipliers m≥N≥2, its incidence matrix K has
`Σ_b K(a,b)≤16 haarMass(a)` and
`Σ_a K(a,b)≤log(2b+1)haarMass(b)/sqrt(N)`.
The second inequality follows because each m has at most one preimage a,
and every surviving m divides 2b+1. It uses the exact identity
`Σ_{m|n} Λ(m)=log n`, not an estimate for primes in intervals.

Let t_A retain coefficients a≥A. For any τ>0, weighted Young gives

`τ |2Σ_ab K(a,b)d(a)t_A(b)|
 ≤16 τ² M + L/sqrt(N)
 ≤[16 τ²/w+(1+2/w)/sqrt(N)]D`.

Given δ>0, take τ=δ w/32 and then choose N so large that
`(1+2/w)/sqrt(N)≤τδ/2`. The entire large-multiplier pairing is at most
δD, uniformly in A,d,X.

For the finite remaining multipliers m<N, choose B≥1 and A=N(B+1).
Incidence `(2a+1)m=2b+1` with b≥A forces a≥B. Thus the pairing of the
full detail with t_A equals the pairing of t_B with t_A. Translation is
contractive in the original half-line L² space, and
`cellGammaWeight(B) ||t_B||²≤D`,
`cellGammaWeight(B) ||t_A||²≤D`. Cauchy–Schwarz/Young gives
`cellGammaWeight(B) |Re⟨T_m t_B,t_A⟩|≤D`.
Write `C_N=Σ_{2≤m≤N} 2Λ(m)/sqrt(m)`. Choose B with
`cellGammaWeight(B)≥2C_N/ε`, using its divergence. The finite part is
at most εD/2; use δ=ε/2 for the large part.

Finally, incidence sends indices only upward. In the exact quadratic
prime sum, the full form minus its head form therefore equals
`Σ_m 2Λ(m)/sqrt(m) Re⟨T_m h,t_A⟩`. No source term is replaced.
The preceding estimates first bound the error by εD, then by εE, with
one A for every q,d,X. Applying the εD bound to t_A, whose head is zero
and whose logarithmic mass is at most D, also gives
`|haarPrimeEnergy(t_A,X)|≤εΓ(completePairProfile q d X)` in the
original untruncated energy.

This is uniform finite-head approximation of the full compressed prime
form, including exponent one. The argument does not estimate the
opposite coarse/detail first-prime block.

## Consequence: retain the complete Gamma source

Write `F=g+h` and let `R=fullPolarNonfirstSourceForm q d X`. Its exact
definition is

`R=Γ(F)+2 gammaHardyPhaseRate(0) ∫h²−haarPrimeEnergy(d)
   −squarePrimeMixedSource(q,d)−oddHigherPrimePowerMixedSource(d,q)+P(F)`.

For every ε>0 there is one finite detail head A, independent of q,d,X,
such that d(a)=0 for a<A implies

`|R−(Γ(F)+P(F))|≤ε Γ(F)`.

Proof: give ε/4 of the original Γ(F) to each of the four terms in
the displayed remainder. The new full Haar prime tail estimate pays
the prime diagonal. `exists_uniform_small_squarePrimeMixed_tail` pays
the actual mixed even-power source; `exists_oddHigherPrimePower_gamma_small_tail`
pays precisely the disjoint mixed odd exponents at least three.
For the constant detail mass, choose a fourth head B with
`cellGammaWeight(B)≥8 |gammaHardyPhaseRate(0)|/ε`; the actual variance
bound pays `2 |gammaHardyPhaseRate(0)| ∫h²≤ε Γ(F)/4`.
Take A to be the maximum of these four heads. Every smaller-head tail
of d is exactly d, so all four estimates use the same original Γ(F).
The triangle inequality proves the absolute estimate.

In particular,

`R+2 sinhHalfMoment(F)² ≥ (1−ε)Γ(F)+2 coshHalfMoment(F)²`.

This retains arbitrarily close to all of the **complete** Gamma energy,
including its original coarse/detail coupling. It strengthens the
previous fixed logarithmic-detail share plus coarse-Gamma estimate.
This source R excludes coarse prime terms. The existing joint whole-square
extension pays the coarse even powers. Coarse first-prime and odd higher-power
sources, coarse archimedean mass, first-prime mixing, and finite head/moment
index costs remain open on the full ACS route.

## Lean declarations and verification

- `TheHaarPrimeMultiplierTailIsGammaSmall.lean`:
  `haarPrimeMatrixOn_column_le`, `haarPrimePairOn_tail_young`,
  `exists_haarPrime_multiplier_tail_small`. Direct source check passed.
  Its missing olean was produced for the finite-head importer.
- `TheFullHaarPrimeSourceHasUniformFiniteHeads.lean`:
  `exists_haarPrime_finite_head_logMass`,
  `exists_uniform_finite_head_for_haar_prime`,
  `exists_haarPrime_tail_small_originalGamma`. Direct source check passed.
  Its missing olean was produced for the complete-Gamma application.
- `TheFullNonfirstSourceRetainsAlmostAllGamma.lean`:
  `exists_fullPolarNonfirst_gamma_approximation`,
  `exists_fullPolarNonfirst_completeGamma_reserve`. Direct source check passed.

All three files passed their exact `lake --old env lean` source checks.
Only the two missing dependency oleans needed by these importers were built.
The modules are imported by `ArithmeticIndexDescent.lean`; the umbrella was
not compiled. No analytic hypothesis was added to either endpoint.

## Completion gates

- [x] Source and target fixed; no assumed analytic cancellation input.
- [x] Complete dependency-closed paper proof.
- [x] Exact Lean formalization and direct `lake --old env lean` check.
- [x] Umbrella and frontier updates after successful verification.

No web search, novelty checks, numerical computations or axiom checks.
