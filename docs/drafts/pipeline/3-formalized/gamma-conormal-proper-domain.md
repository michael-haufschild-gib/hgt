# Gamma's factorial conormal has a proper raw-clock domain

- **ID:** `gamma-conormal-proper-domain`
- **Stage:** 3-formalized
- **Type:** GAMMA SOURCE-DOMAIN NO-GO / POSITIVE NECESSITY THEOREM
- **Scientific status:** `[LEAN-FORMALIZED] [SIGNIFICANT POSITIVE RESIDUE] [PARENT ANALYSIS]`
- **Parent:** `../1-in-progress/source-rigged-clock-domain.md`
- **Statement:** The factorial-tail Gamma conormal is not summable on every raw sequence, so the
  Gamma source object necessarily includes a proper summability domain in addition to a topology.

## Theorem

Define

```text
lambda_n=1/(n+1)!,
a_n=(n+1)!.
```

Lean proves `lambda_n a_n=1` for every `n`, and therefore

```text
not Summable (lambda_n a_n).
```

The proof uses no asymptotic estimate: the summand is exactly the nonsummable constant sequence.

## Positive conclusion

The actual conormal pairing cannot be a functional on all of `C^N` defined by its factorial
series. It must live on a proper source-selected sequence domain containing the analytic periodic
tangent. A topology refinement alone is insufficient because it cannot define an otherwise
divergent pairing.

The positive domain is also formalized. Define

```text
E_Gamma={b | for every k,
  Summable (b_(n+k)/(n+1)!)}.
```

This is a complex submodule, it is stable under the tail shift `b_n -> b_(n+1)`, and every finite
periodic Fourier packet lies in it. Hence the no-go leaves a concrete maximal domain carrying the
whole cyclic family of differentiated shift conormals.

On this domain Lean constructs

```text
lambda_k(b)=sum_(n>=0)b_(n+k)/(n+1)!,
lambda_k(Tb)=lambda_(k+1)(b),
lambda_k(Fourier packet)=0.
```

So the positive residue is an actual cyclic conormal representation, not only a convergence set.

## Lean declarations

`GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona` contains:

- `gammaPeriodicConormalCoefficient`;
- `gammaFactorialRawClock`;
- `gammaPeriodicConormalCoefficient_mul_factorialRawClock`;
- `gammaPeriodicConormal_not_summable_on_all_rawClocks`;
- `gammaCoronaClockDomain`;
- `gammaCoronaClockTail`;
- `gammaCoronaClockDomain_tail`;
- `gammaPeriodicModeTail_mem_coronaClockDomain`;
- `gammaPeriodicFourierTail_mem_coronaClockDomain`.
- `gammaCoronaConormal`;
- `gammaCoronaConormal_tail`;
- `gammaCoronaConormal_fourierTail`.

The touched source passed direct Lean verification; its cached object existed, so no build was
run. The two audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Scientific boundary

The divergence argument is elementary. Its role is structural: it rules out the raw product as
the analytic carrier and forces domain data into the definition of the HT field. Completeness, the
source-framed subdomain, and minimality of the canonical Gamma topology remain open.
