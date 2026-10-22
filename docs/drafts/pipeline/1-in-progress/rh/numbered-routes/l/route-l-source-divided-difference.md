# Route L: complete two-parameter source comparison

- **ID:** RH-L-C60
- **Stage:** 1-in-progress
- **Target:** Full-source fixed physical-reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.
C59 identified a scalar subtraction but did not lift it to the complete source or establish physical-reader compatibility. This turn tests the two-parameter source expression with counterterm variation and all native-depth terms retained.

## Outcome: agreement remains open

No new Lean theorem or RH implication has been closed. The tests below establish which terms and domain conditions a two-parameter comparison must retain; they do not construct the fixed physical-reader agreement. Route L remains live.

## Actual-source divided difference

Write `X_k(w) = iteratedDeriv k XiC w`, `h_m = deningerGammaSixHalfWeight m`, and `M_m(w) = mobiusThetaPrimeNormalResidualMultiplier 6 m w`. These are the existing quantities, not a newly chosen source or normalization.

At a fixed honest depth and admitted parameter (`|Im w| < 1` and `1/m < Re(1/2 + I*w)`), the literal source transform is

`h_m M_m(w) X_k(w)`.

The complete tensor remainder has transform

`F_m(w,z) = h_m^2 (M_m(w) M_m(z)-1) X_k(w) X_l(z)`.

Both leading–tail cross terms and the tail–tail term are admitted separately by `deningerGammaSixInternalJetTensorRemainder_cross_integrable`. This is the existing source theorem in `formal/GaloisForLFunctions/RHTower/Deninger/DeningerGammaSixTensorRemainderXiJets.lean`, not a replacement by the leading jet.

For distinct admitted `w,v`, put `Delta_wv f = (f(w)-f(v))/(w-v)`. Direct subtraction gives

```
Delta_wv F_m(·,z) = h_m^2 X_l(z) *
  ((M_m(w) M_m(z)-1) Delta_wv X_k
    + M_m(z) X_k(v) Delta_wv M_m).
```

Proof: subtract the two displayed formulas for `F_m`, add and subtract `(M_m(w) M_m(z)-1) X_k(v)`, then divide by `w-v`. The integrand difference is integrable because both original integrands are integrable. No differentiation under an integral or new convergence assertion is used.

There is also an exact source-series description of the last term. With

`c_j(w) = 6^(m*(1/2+I*w)) * LSeries.term mu (m*(1/2+I*w)) (6+j)`,

the existing absolute-summability theorem at `w` and `v` allows

`Delta_wv M_m = sum'_j (c_j(w)-c_j(v))/(w-v)`.

Here `c_j` denotes the literal `mobiusThetaPrimeNormalResidualSpectralCoefficient`, including its Möbius coefficient. The `j=0` coefficient is constant `mu(6)=1`; thus its divided difference is zero and all multiplier variation lies in the retained strict tail. Neither this observation nor pointwise convergence `M_m(w) → 1` justifies erasing the tail at fixed native depth or exchanging a full-Xi sum with a limit.

**Proof status:** paper algebra and linearity consequences of existing source identities; not a new kernel-checked module. A resolvent product identity for one fixed physical operator, with this source-series term retained, is still missing. C59's subtraction `F=A+Xi*P6` likewise contributes `Delta A` in a two-parameter comparison.

## Attempted positivity transfer and pivot

Conjecture tested: the existing prime–Gamma Cauchy divided difference directly supplies a Hermitian positive kernel for the complete reader.

`xiWeilPolarization_cauchy_eq_primeArchSource_dividedDifference` in `XiWeilResolventSource.lean` uses both `Re(1/2+z*I)>1` and `Re(1/2+conj(w)*I)>1`. On `w=z` these require respectively `Im z < -1/2` and `Im z > 1/2`. They are incompatible. The off-diagonal formula remains meaningful; its absolute-convergence domain does not supply this diagonal positivity argument.

The continued theorem in the same file requires positive real parts, exclusion of the pole, and nonvanishing of both corresponding zeta factors. Those explicit premises cannot supply nonvanishing or positivity on the unresolved domain. The formula retains all Xi multiplicity copies but does not identify the anchored Gamma reader.

Pivot tested: source Hankel factorization. The private `hankel_laplace` lemma in namespace `RHTower.SelbergThetaTotientHankel` factors that module's reflected correlation into two Laplace sources. Its source-dependent cancellation and first mean derivative are already proved there. No identity identifies that correlation with the Gamma-six source above. `suzukiCanonicalPositiveHankel_intervalSource_ae` does identify a literal physical kernel, but its theorem assumes `omega > 1/2`; it supplies no critical limiting comparison. Generic resolvent laws require actual inverses or resolvent-set membership, and spectral heat-kernel factorization requires its spectral/orthogonality and summability hypotheses. None supplies the missing source identification.

These are failures of the stated proof attempts, not a no-go for all operator-valued realizations. In particular a compressed resolvent can retain additional channels; a scalar divided-difference test does not exclude such a construction.

## Broad literature screen

Newest-first, single-word arXiv search: `semigroup`. Read the statement and proof of Theorem 0.1 in Coine–Laforge–Ricard, [Schur tests and estimates for positive semigroups on non commutative L_p](https://arxiv.org/html/2609.09339), submitted 8 September 2026. Its weighted bounded maps start from a bounded positive map on finite von Neumann `L_p` spaces. The proof introduces positive corrections and obtains weights through norm attainment for the corrected map; the conclusion bounds weighted forms of the original map. This is potentially useful after constructing the required positive source map. It neither constructs that map for Gamma nor proves that the weights preserve the fixed reader and horizontal anchor. No result from the paper has been applied as a theorem here.

## Corpus audit and next attack

- `route-l-source-divided-difference-search.json`: deep search, 120-second budget, cached index, generation `880118`.
- `route-l-hankel-resolvent-source-search.json`: same settings and generation.
- Both returned partial results; coverage reports `status: pending`. No earlier coverage counts are inherited. Both sets of 20 candidate lemmas and 20 source-method entries, including their assumptions, were inspected. Both have empty proof-idea and ingredient-set arrays. The second also reports a local reranking deadline. These are useful partial searches, not exhaustive absence claims.
- Both search processes terminated successfully. No Lean process was started; no Lean file, heartbeat setting, umbrella, or axiom-audit command was changed or run.

Next mathematical target: derive an actual two-parameter source-operator identity controlling the strict-tail divided difference in the same fixed physical pairing. Any candidate must retain original prime provenance, native Tate depth, every multiplicity copy, nonzero Xi coefficient, Gamma normalization and horizontal anchor. A bound for a different Hankel source, or an assumed positive/contractive realization, does not close this target. No new route-independent fact warrants an addition to `universal-law-field/STATUS.md` this turn.
