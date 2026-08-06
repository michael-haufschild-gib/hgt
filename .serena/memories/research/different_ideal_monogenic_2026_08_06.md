# The different of a monogenic extension (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **47**.
Continues [[research/adjoin_fraction_transport_complete_2026_08_06]].

## `DifferentIdealMonogenic.lean`

**`differentIdeal_eq_span_aeval_derivative`** — with `conductor A x = ⊤` and
`Algebra.adjoin K {algebraMap B L x} = ⊤`:

    differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))}

From `conductor_mul_differentIdeal` + `Ideal.top_mul`.  Both hypotheses are supplied by modules
45 and 46.

## Instance bundle actually required (recorded — it is larger than the mathlib docstring suggests)

    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsFractionRing B L]
    [IsDedekindDomain B] [Module.IsTorsionFree A B]

The last two are **not** in the section `variable` block of `Different.lean` near the lemma; they
come from further up the file and only surface as synthesis failures.  `Ideal.top_mul`, not bare
`top_mul`.

## Remaining to reach `differentIdeal A B = (maximalIdeal B)^(e−1)`

Identify `natDegree (minpoly A x) = e` (= ramification index = `Module.finrank A B` for a totally
ramified extension).  Route: `Algebra.adjoin.powerBasis` on `A[x] = B` gives
`pb.dim = natDegree (minpoly A x)` and `PowerBasis.finrank` gives `finrank A B = pb.dim`.
Then module 41's `span_eval_derivative_of_monic_uniformizer_root` applies to `minpoly A x`.

## Remaining for Theorem A

1. The degree identification above.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
