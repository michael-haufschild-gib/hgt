# Suzuki--Mangoldt macroscopic prime-block surplus

- **Status:** Promoted through Stage 3; targeted build and axiom audit pass
- **Labels:** `[NEW]` `[SUZUKI]` `[SOURCE-SPECIFIC]` `[UNCONDITIONAL-TARGET]`
- **Open core:** `SUZUKI-APEX-BLOCK-TRANSPORT`
- **Novelty claim:** no matching theorem was found in the internal corpus, Suzuki's 2026 screw-function paper, the 2026 finite Guinand--Weil dictionary, Ramaré--Zuniga Alterman's harmonic Mangoldt paper, or transport-majorization literature.  Classical Chebyshev supply and generic majorization are `[KNOWN]`; their exact weld to the aligned Suzuki moving tent is the proposed `[NEW]` theorem.

## Frontier isolated

The formalized width-`log 2` dyadic flank theorem gives a sharp positive surplus, but its absolute
scale is only `n^(-1/2)`.  A sharp future/past splice duplicates a target interval of fixed lag
length near an aligned apex whose height is `sqrt n`; its moving-tent mass is therefore on the
`sqrt n` scale.  A single flank, or any uniformly bounded collection of comparable Mangoldt atoms,
cannot pay that seam.  The missing source object must be a macroscopic multiplicative prime block.

## Conjecture C1: fivefold aligned prime-block law

Put

```text
L5       = log 5,
a5(n)    = log(5n)/2,
tau(n)   = 2 log n,
A_n(t)   = exp(t/4) C_{L5,a5(n)}(t/2),
P_n      = {p prime : 2n < p <= 5n},
w_p      = 2 log(p)/p,
q5       = sqrt(2) * (1 - log(2)/log(5)).
```

Target theorem: there is a concrete symbolic threshold (initial target `exp(20) <= n`) such that

```text
0 < q5 < 1,
sum_(p in P_n) w_p >= 1/10,
A_n(tau(p)) <= q5 A_n(tau(n))              for every p in P_n,
sum_(p in P_n) w_p (A_n(tau(n))-A_n(tau(p)))
  >= ((1-q5)/10) sqrt(n) log(5) > 0.
```

Every statement is to be proved unconditionally.  `exp(20) <= n` is a proved size domain, not an
arithmetic or RH hypothesis.  No numerical verification is admissible.

## Mechanism

1. Exact aligned sampling should give
   `A_n(tau(m)) = sqrt(m) max(0, log 5 - |log(m/n)|)`.
2. The universal right-flank tilted tent
   `R_{beta,L}(d)=exp(beta d)(1-d/L)` is antitone on `[0,L]` whenever `beta L <= 1`.
   For `beta=1/2`, `L=log 5<2`, every `p>2n` contracts by the explicit factor `q5`.
3. Chebyshev's formalized bounds give
   `theta(5n)-theta(2n) >= n/4` beyond the symbolic threshold.
4. Since `p<=5n`, the log-Haar mass satisfies
   `sum_(p in P_n) 2log(p)/p >= (2/(5n))(n/4)=1/10`.
5. Multiplying uniform contraction by macroscopic mass yields the `sqrt n` surplus.

## Hostile tests

- **Not a disguised RH deficit.**  C1 uses only pointwise aligned-tent algebra, Chebyshev theta
  bounds, and positivity of prime weights.  No pairing with `t-F(t)`, zero sum, Weil positivity,
  or RH-equivalent sign occurs.
- **Correct scale.**  C1 upgrades the existing dyadic `n^(-1/2)` lower bound to `sqrt n`; ratio is
  linear in `n`.  This is the first source theorem in the lane with seam-scale surplus.
- **Width restriction is structural.**  `log 5<2` makes the exponentially tilted right tent
  decreasing from the apex.  Width `log 2` cannot provide Chebyshev-macroscopic supply from the
  formalized coarse theta constants; width `log 5` is a clean unconditional supply/contraction
  compromise.
- **No target-capacity claim yet.**  C1 does not by itself prove that its explicit coefficient pays
  the exact bicausal overlap after all unused completed-kernel mass is accounted for.  That scalar
  comparison is the next hostile gate, not to be stated as an application unless proved.

## Promotion gate

- [x] dependency-closed paper proof of right-flank antitonicity
- [x] dependency-closed paper proof of symbolic Chebyshev mass floor
- [x] exact aligned Suzuki specialization
- [x] Lean proof with no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] axiom audit contains only Lean/mathlib foundations
- [ ] compare explicit macroscopic surplus with exact sharp-splice reserve
