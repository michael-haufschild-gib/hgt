# SQB: actual spectral source comparison

Status: analytical candidate with retrieved source ingredients verified in Lean. The safe-half-plane Mellin calculation below has been derived from the literal theta atoms and the complete row formula. Its Lean admission, spectral-boundary transfer, and native phase cancellation are not proved. The proposed positive boundary multiplier alone does not settle the phase cancellation. No new mathematical theorem or RH proof is asserted by this card.

Full chain: theta source -> normalized full-native residual packets at each Xi target -> occurrence -> critical line -> RH. Hardest target: a source comparison retaining the signed arithmetic contribution, strong enough to orient the native scalar response. The current candidate uses the actual scattering phase rather than replacing the Möbius remainder by its absolute majorant.

## Literal-source calculation

Use `f(y)=sqrt(y) Phi(log(y)/2)`, `J=horizontalWeight`, `g=radialProjection`, and `a=sqrt(y)` from `SelbergThetaHorizontalArithmetic`. Let `Lambda(s)=pi^(-s/2) Gamma(s/2) zeta(s)` and `xi(s)=s(s-1)Lambda(s)/2`.

For `Re z>0`, the proposed exact source symbol is

    integral_0^infinity a^(z-1) J(a^2) da
      = xi(z+3/2) * (1 + Lambda(z+1)/Lambda(z+2)).

Derivation: the all-complex bilateral Phi transform is already available from `HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all` and `thetaBilateralLaplace_eq_XiC`, together with Xi reflection: `integral exp(w x) Phi(x) dx = xi(w+1/2)`. Rebuilding that transform from the seed is unnecessary. Reflection gives the radial field `G(r)=r^-1 Phi(log r)`. Polar coordinates then give

    Mellin(g)(s) = sqrt(pi) Gamma(s/2)/Gamma((s+1)/2) * xi(s+1/2).

The complete totient series contributes `zeta(z+1)/zeta(z+2)`. Its angular Gamma factor completes that ratio to `Lambda(z+1)/Lambda(z+2)`. The parabolic row contributes the additional `xi(z+3/2)` term; it must not be dropped.

Absolute admission in the safe half-plane should follow by choosing the actual source power bound sufficiently large, then applying Tonelli to the norm at `Re z`. This has not yet been implemented in Lean. The existing inverse-cube bound alone only covers a bounded range of Mellin exponents; arbitrary source powers are available upstream.

## Candidate boundary comparison

The residue at `z=0` is `C=6 xi(3/2)/pi`, consistent with the proposed arithmetic main term `LB`. Put

    k(x)=exp(-x)*(J(exp(2x))-C).

At `z=-1+it`, formal continuation of the symbol gives

    Fourier(k)(t)=XiC(t)*(1+Lambda(it)/Lambda(1+it)),

up to the chosen Fourier sign (irrelevant after taking the even part). Functional equation and conjugation give `Lambda(it)=conj(Lambda(1+it))` for real nonzero t. The denominator is nonzero there by the one-line zero-free theorem and Gamma nonvanishing. Consequently the even-part multiplier is

    w(t)=1+Re(conj(Lambda(1+it))/Lambda(1+it)),
    0 <= w(t) <= 2.

The removable value suggested at t=0 is w(0)=0. Identifying the literal k with this boundary Fourier transform requires a genuine boundary-limit argument, not mere meromorphic continuation. This admission is open. Its usefulness for RH also requires an additional source cancellation beyond the displayed multiplier bound.

For `p''+z_q^2 p=Phi`, the native pairing formula and Parseval would then yield

    m(q)=1/(4 pi) integral_R XiC(t)^2 w(t)/(t^2-z_q^2) dt

when `z_q^2` is nonreal. This retains a concrete nonnegative density, rather than an unspecified Gram/Herglotz premise. Its norm comparison would be bounded by the corresponding ordinary source integral. It has not been proved for the native source, and the sign displayed is compatible with the existing self-adjoint Gram displacement law; no contradiction or RH implication follows from the proposed bound alone.

## Conjecture checks and search joins

Direct critical Möbius annihilation does not match the literal radial coefficient: the known theta inversion uses critical half-power translation weights, while the full horizontal mean has its own denominator/Jacobian weight. Any use of `XiCTaylorThetaTailMobiusConstraint` must retain this difference.

`ThetaCuspWignerProductFiberNormalForm` supplies complete positive-shell reassembly and divisor-ratio phases, including a fully coupled cone current. Its real-frequency reality theorem cannot be substituted for the native complex-energy orientation. The full coupled integral, rather than one fixed-product sign, is the available survivor.

Broad OR searches used theta/divisor/Mellin/radial, Möbius/theta/Poisson, signed/quadrature, and scattering/Plancherel/contraction. Deep searches remained partial; the second returned source arguments and the newly indexed SQB quadrature theorem but no decisive bound. Search failure is not evidence of corpus absence. No computation or frontier-map edit is part of this construction.

## Verified ingredient matches

The following exact interfaces were checked together by `lake env lean /tmp/sqb41_retrieved_interfaces.lean` (exit 0). The six nontrivial results selected for `#print axioms` use only `propext`, `Classical.choice`, and `Quot.sound`. This checks existing results; it does not audit the conjectural calculation above.

| Source result | Match to this problem | Remaining mathematical join |
| --- | --- | --- |
| `HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceIntegrand_all`, `thetaCuspFourierLaplace_eq_XiC_all`; `thetaBilateralLaplace_eq_XiC` | Literal full theta source; arbitrary complex parameter. The old strip restriction is already removed. | Radial projection and complete horizontal mean are different transforms. |
| `SelbergThetaTotientHankel.transform_kernel` | Complete totient sum, angular integral, and completed-zeta ratio, with absolute admission. | Its input is the dyadic tilted-profile Hankel correlation, not the common-forcing response profile `p_q`. |
| `SelbergThetaTotientHankel.kernel_mean_abel_limit` | Genuine right Abel limit of the full kernel at every Xi copy. | This is a limit at its mean pole; it is not the proposed real-frequency boundary integral for native `m(q)`. |
| `thetaCuspTailSecondDensityAtom_one_eq_tsum_moebius_translate` | Signed critical Möbius inversion of the actual differentiated theta density. | Proved for `x >= 0`; its half-power weights and source must be transported to the full native radial remainder. |
| `DeletionMixedRefinement.norm_unitFullFourierSource_even_le` | Complete complex Bernoulli-source reflection bound, quadratic in horizontal displacement. | Different source and measure; its Hardy-amplitude consequence supplies selected horizontal segments, not all-zero native orientation. |
| `Sieve.eventually_norm_sum_moebiusTwist_div_lt` | Unconditional `o(N)` cancellation, uniform over the explicitly admitted growing twist range. | Supplies neither a critical square-root saving nor the required bound for the signed radial quadrature. |

The all-complex theta identity is an actual retrieval gain: following references outside the initially inspected transform module found its existing producer. Source conclusions, measures, exponents, and quantified domains distinguish usable ingredients from similarly named receivers. The broad deep intertwining query retained 25 candidate lemmas and 25 source arguments, but reported interrupted retrieval stages, pending coverage, and no generated ingredient sets; it is not an exhaustive corpus audit.

The unresolved SQB assertion remains reality of the literal corrected scalar response

    S(q) - M^2 / ((1+z_q^2)*V),

or another source-derived estimate forcing the normalized full-native residual to vanish. None of the verified matches above supplies that assertion by the identities currently proved. The safe Mellin calculation remains a possible input to such an estimate, rather than a closure of it.
