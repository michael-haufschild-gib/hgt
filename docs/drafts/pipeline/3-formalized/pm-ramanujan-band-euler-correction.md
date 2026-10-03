# Route PM: actual local factors and analytic band correction

- **ID:** pm-ramanujan-band-euler-correction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `PMRamanujanBandEulerCorrection.lean`, fifteen public declarations.
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact result

For epsilon>=0 and each prime p, put

    a=p^(-1-epsilon), b=p^(s-z-1), c=p^(-z),
    H_p(z,s)=1+(b-a)(c-b)/[(1-a)(1-c)].

The prime product H_epsilon(z,s)=product_p H_p(z,s) converges absolutely for Re(z)>=3/8 and Re(s)<=9/16. It converges locally uniformly on the corresponding open region in both variables, is jointly continuous there, and is holomorphic in z for each fixed s in that region. At every critical diagonal point z=s with Re(z)=1/2, its value is nonzero; it remains nonzero in a joint neighborhood of that point.

For epsilon>0, prime p and Re(z)>0, the correction satisfies the source-specific identity

    [alpha+a_epsilon(p)*J_s(p)*p^(epsilon+s-z)]*(1-p^(s-z-1))
      = alpha*(1-p^(-z))*H_p(z,s).

Here alpha and a_epsilon(p) are the literal PM density and Ramanujan weight, and J_s is the audited finite primitive Mellin symbol. This is a prime identity, not yet the infinite arithmetic-series identity.

## Dependency-closed paper proof

The actual prime-weight recursion and J_s(p)=p^(1-s)-1 give the displayed identity by the positive-base complex-power law. Expanding its numerator gives

    H_p=(1-a+b-c)(1-b)/[(1-a)(1-c)].

On Re(z)>=3/8, Re(s)<=9/16, we have |a|<=1/p<=1/2, |b|<=p^(-13/16), |c|<=p^(-3/8). The denominator norm is at least (1/2)*(1-2^(-3/8)), while the numerator of H_p-1 has norm at most 4*p^(-19/16). Thus

    |H_p-1| <= [8/(1-2^(-3/8))]*p^(-19/16).

The prime sum of this majorant converges. The locally uniform product theorem supplies joint continuity; locally uniform limits of holomorphic finite products supply holomorphy in z. At s=z, b=1/p and 0<=a<=b. Hence 1-a+b>=1>|c|, so the local numerator cannot vanish. The absolutely summable product of these nonzero factors is nonzero. Joint continuity supplies the neighborhood statement.

## Frontier contribution and limits

The correction cannot automatically erase a critical-zero residue near the diagonal. This discharges a genuine analytic input of the complete-band spectral argument. The literal infinite Euler identity, paired Hilbert continuation, spectral escape theorem and complete small-damping energy ceiling remain open. No RH proof or falsification follows from this leaf.

## Audit — 2026-10-02

- Scratch proof passed; deprecated alias replaced with its canonical name.
- `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandEulerCorrection`: exit 0; only this new leaf built (240 seconds).
- Final actual-file `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandEulerCorrection.lean`: exit 0, no diagnostics.
- All fifteen public declarations passed `/tmp` axiom queries; only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired once; no umbrella build. Global lint reports thirteen unrelated unreachable modules, with no own-module finding.
- No added axiom, sorry, RH premise, numerical experiment, raised heartbeat or subagent.

Search132 returned partial semantic retrieval with a complete inventory and mixed compiler freshness. All20 candidate statements and all20 source arguments were inspected. Generic finite character corrections do not identify this source; the exact actual prime identity was proved directly.
