# Prime-pole coherence and the sector cost

- **ID:** critical-rigidity-prime-pole-coherence
- **Stage:** 2-fully-proven
- **Type:** THEOREM; Lean verification pending
- **Statement:** Determine the exact norm of the pole reading of the actual prime generator on prime-supported packets, and identify the mandatory conductor cost in relative prime estimates.

## Sharp law

For normalized packets supported on primes `p≤Q`, the proposed pole response is

`P_Q(a)=Σ_p log p / sqrt(p−1) · a_p`.

The exact adjunction weight is `L_p=p log p/(p−1)`. Weighted Cauchy–Schwarz predicts the sharp law

`P_Q(a)² ≤ B_Q Σ_p L_p a_p²`, where `B_Q=Σ_(p≤Q)log p/p`.

The coefficient choice `a_p=sqrt(p−1)/p` gives both `P_Q(a)=B_Q` and adjunction mass `B_Q`, so the constant cannot be reduced. Mertens' theorem gives `B_Q=log Q+O(1)`.

## Source identification

The packet itself has zero constant mode. The complete prime generator is the divisor jet minus diagonal adjunction. Its constant mode is exactly `P_Q(a)`, since the period mean of the divisor jet is `Λ(m)`. Thus input with zero complete-period mean can generate a coherent constant output whose squared norm has a mandatory logarithmic cost. Complete-period centering is distinct from orthogonality to the finite-horizon Weil pole.

## Dependency-closed proof

Let `G_Q a` be the convergent actual sum `Σ_k Λ(k)/k [F_a(kn)−F_a(n)]`, identified by the proved dilation identity with the divisor jet minus diagonal adjunction. Every prime-supported input has period mean zero. The jet of conductor `m` has period mean `Λ(m)`; periodic repetition transfers this identity to `Q!`. Consequently `mean G_Q(primeOnly a)=P_Q(a)`.

For a prime `p`, `L_p=log p+log p/(p−1)=p log p/(p−1)`. Apply Cauchy–Schwarz in weights `w_p=log p/p` to `x_p=p a_p/sqrt(p−1)`. This gives `P²≤B L`. Setting all `x_p=1` gives the stated extremizer and equality. The corpus's explicit prime Mertens theorem gives `|B_Q−log Q|≤(log 4+4)+(8+mertensTail)`.

Every finite prime head has period square mean at most `A_Q L`. Pointwise convergence of the proved generator sum and finiteness of the averaging period preserve this inequality in the limit. Jensen's finite inequality gives `(mean G)²≤mean G²`. Thus every constant valid in `mean G_Q(primeOnly a)²≤C L_Q(primeOnly a)` must satisfy `B_Q≤C`, while `A_Q` suffices. Both assertions concern the literal arithmetic generator.

The optimal pole-row inequality, its extremizer, and the source identification are the positive survivor. A further question is whether subtracting the output pole removes every logarithmic loss, or whether composite conductor fibres reproduce coherence in nonconstant rows. That stronger question is not settled by this proof.

## Exact finite-horizon pole transfer

For the physical profile `x_a(n)=F_a(n)/sqrt n`, set `t=−harmonicSum_N(x_a)/harmonicMass_N` and add `t` to conductor one. The resulting profile is exactly the existing arithmetic `poleProj_N(x_a)`, hence lies on the actual harmonic pole hyperplane for `N≥1`. This adjustment leaves both adjunction energy and the complete prime generator unchanged: the conductor-one weight and its divisor jet vanish.

Apply this adjustment to the explicit prime extremizer. For every `Q≥2` and `N≥1`, the corrected packet is literally harmonic-pole-neutral, still has adjunction mass `B_Q`, and still has complete-period generator mean `B_Q`. Thus the necessary generator-sector cost `B_Q` survives actual finite-horizon pole projection. Its output norm is still the complete-period generator norm; no statement about the complete Weil form follows.

## Positive content and scope

The survivor is the exact optimal constant-row inequality, its explicit extremizer, its logarithmic scale, and a source-preserving realization on every actual harmonic pole hyperplane. This identifies the source of a necessary loss in the complete-period generator norm. It does not obstruct cancellation with the global pole or Gamma terms in the complete form.

## Corpus leads

- `SuccessorShellArithmetic.TopBand.RamanujanDivisorMoments.periodMean_ramanujanLogDivisorJet`.
- `ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit.tameDifferent_prime_pow`.
- `RHTower.MertensFirst`: `RHTower.Mertens.mertens_first_prime` gives an explicit bounded difference between `B_Q` and `log Q`.
- Current relative prime-head bound is `A_Q L_Q(a)`, where `A_Q=Σ_(p≤Q)log p/(p−1)`. The candidate lower bound has the same logarithmic order.

## Lean targets

`CriticalScaleArithmeticRigidity/PrimePoleNorm.lean`, `PrimeGeneratorPole.lean`, and `HarmonicPoleCentering.lean`. Direct Lean audits pending; the mathematical statement above is not yet a formalized result.
