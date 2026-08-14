# Gamma transport and prime-normal flow have the same physical corona, formalized

- **ID:** `suzuki-gamma-prime-normal-corona-equivalence`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-gamma-prime-normal-corona-equivalence.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaCoronaSequence.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaDistributionalHalfLine.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPrimeNormalCoronaComparison.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiGammaHalfLineClassification.lean`
  - `formal/GaloisForLFunctions/HTGeometry/HalfLogTraceNonIntegrable.lean`
  - `formal/GaloisForLFunctions/HTGeometry/InverseSqrtPerturbation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/DistributionalLinearODE.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ConjugatedTransportRepresentation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialTwist.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialTwistInversion.lean`
  - `formal/GaloisForLFunctions/HTGeometry/IntervalTestSeparation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PointSupportGammaForm.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CentralBinomialSeries.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPrimeNormalBinomialSeries.lean`

## Formal content

| Card | Lean |
|---|---|
| the homogeneous sector `𝒢_T` is exactly `\|η\|^{-1/2}Q(η)c_±` | `gamma_tempered_classification`, `exists_channel_vector_positive`, `exists_channel_vector_negative` |
| the channel vectors are unique | `channel_vector_unique_distributional` |
| no additional distribution at `η = 0` | `eq_zero_of_pointSupport_gammaForm` |
| `(3)` half-log asymptotic of the carrier | `norm_gammaProfile_sub_halfLog_le` |
| `(9)`, claim 1: `τ` is onto | `halfLogScatter_surjective` |
| `(4)`, `(11)`–`(14)`, claim 2: `ker τ = 𝒢_T ∩ N` | `halfLog_trace_zero_iff_integrableOn_sq` |
| `(13)` the reverse-triangle lower bound | `norm_ge_of_halfLog_asymptotic` |
| `(14)` nonzero trace destroys square integrability | `not_integrableOn_sq_of_halfLog_trace` |
| `(5)`, claim 3: the corona sequence | claims 1 and 2 together |
| `(6)`, `(15)` the prime-normal cross-section | `primeNormalSection` |
| `(16)` continuous functional calculus remainder | `norm_cfc_invSqrt_sub_one_le`, `norm_cfc_binomialSymbol_sub_one_le` |
| `(17)` `P_T(β)(L) = L^{-1/2}β + O(L^{-3/2})` | `norm_primeNormalSection_sub_halfLog_le` |
| `(7)`, `(18)`, claim 4: `F - P_T(τF) ∈ N` | `integrableOn_sq_sub_of_halfLog` |
| `(19)` the binomial expansion of the cross-section | `hasSum_primeNormalSection` |
| the scalar generating function behind it | `ringChoose_neg_half`, `hasSum_centralBinom` |
| the operator form of the expansion | `cfc_binomialPartial`, `hasSum_cfc_binomialSymbol` |

## What the card actually closes

The homogeneous Gamma sector is now a theorem, not a description.  A tempered `X`-valued
distribution satisfying the Gamma frequency equation is, on each open frequency half-line, exactly
`|η|^{-1/2}Q(η)c_±` for one channel vector, that vector is unique, and no nonzero solution is
carried by the origin.  The proof route is new: an `X`-valued tempered distribution cannot be
multiplied by an operator-valued function, so the classical integrating factor `η^{1/2}Q(η)^{-1}`
has no distributional meaning.  It is replaced by the **exponential twist**

```text
(E_A u)(φ) = ∑_n (-A)^n u(η^n φ)/n!,
```

which converges because the values of a tempered distribution along the coordinate powers of a
compactly supported test function grow at most geometrically.  The twist of a solution of
`u' = A u` has vanishing derivative, so the du Bois-Reymond lemma makes it a constant multiple of
Lebesgue measure, and the opposite twist inverts it — the inversion is Fubini for the double family
indexed by `(k,n)`, regrouped by total degree, where the coefficient collapses to the alternating
binomial sum.

On top of that classification the corona statements are exact.  The trace map `τ` is onto because
one positive channel already realises any prescribed `β`.  Its kernel is exactly the physical
`L²` sector: the easy direction is the `O(L^{-1})` remainder of the scattering asymptotic, and the
hard direction is the reverse-triangle bound `‖F(L)‖ ≥ ‖β‖L^{-1/2}/2`, which makes
`∫‖F‖² ≥ (‖β‖²/4)∫dL/L` diverge.  The prime-normal binomial resolvent differs from the pure
half-log term by `L^{-1/2}` times a first-order functional-calculus remainder of norm at most
`‖T‖/(2L)`, so `F - P_T(τF)` is `O(L^{-1})` and square integrable on every terminal ray: the Gamma
jump changes the `N`-representative of a corona class and nothing else.

## Hypotheses

Object data only: `T` bounded and self-adjoint; the frequency remainder `r` continuous,
nonnegative, even-monotone (`r' ≥ 0` on the positive ray, `r' ≤ 0` on the negative ray) with
`Rint 0 = 0` and `Rint` smooth; the scale conditions `‖T‖/2 < L` and `L > 0`.  These are the
properties of the literal Suzuki Gamma remainder, carried as coordinates of the statement exactly as
in the homogeneous classification.  No RH, no spectral premise, no `sorry`, `axiom`, `opaque`, or
`unsafe`.  Every theorem named above audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

Section 4's binomial expansion `(19)` is formal: the generalised binomial coefficient at `-1/2` is
`(-1)^n C(2n,n)/4^n`, so the resolvent symbol is the central binomial series in `t/(2L)`, which
converges uniformly on the spectrum once `‖T‖ ≤ L`; continuity of the functional calculus in the
symbol turns it into the operator series, and every prime descendant appears at its own grade.  The
nuclearity remark of that section refers to the `ℓ¹` valuation realisation of another card and is
not part of this one.

What stays open is what the card itself declares open: constructing the literal completed
exterior/Feshbach forcing `G_ext`, proving forced `L²`-domain solvability of `(21)` with the two
matched endpoint counterterms, the exact cutoff-equation intertwining, the identification of the
two-ended corona packet with the raw Evans packet, and RH or a whole-program no-go.
