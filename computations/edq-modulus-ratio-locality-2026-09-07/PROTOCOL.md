# EDQ complete flux: modulus-ratio localization diagnostic

Status: frozen before execution. This is a diagnostic of the missing signed
bound, not a proof, primary universal-law conjecture, or numerical Lean input.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic
separation → off-line exclusion → RH.

## Question and frozen prediction

Does the actual complete reciprocal flux concentrate at comparable divisor
sizes, or does its small value require cancellation with distant divisor sizes?
The prior sign experiment enclosed the full flux but did not measure this
decomposition. The temporal-range experiment used a different variable.
Kernel inverse-square decay gives a reason to test localization, but its
absolute tail bound is too large to predict the answer after Möbius cancellation.

Frozen working prediction [BRIDGE]: the ratio-at-most-four part approximates
the full flux within one quarter of its magnitude at every listed cutoff.
A failure is useful: it rejects this particular finite localization claim and
directs the next estimate toward the signed complementary ratio ranges.

Use N=32,48,64,96,128,192,256,384,512. Use ratio cutoffs L=2,4,8,16,32,64.
Do not change either list, classification thresholds, or the full-flux baseline
after seeing the results. No larger scan follows a surviving prediction.

## Literal object and complete remainder

For positive d,e set P_e(k)=(k mod e)*((k mod e)-e)/(2e) and
K(d,e)=sum_(j>=1)P_e(d*j)/(d*j)^2. The complete flux has the exact paper
identity R_N=-sum_(d>N,e<=N)mu(d)*mu(e)*K(d,e), including its mean correction.
Define

```
S_L(N)=-sum_(e=1..N) sum_(N<d<=L*e) mu(d)*mu(e)*K(d,e),
T_L(N)=R_N-S_L(N).
```

Thus L measures d/e, not d/N or temporal separation. Every K retains its
infinite j series. The infinite d remainder T is obtained by subtracting the
computed finite part from the saved full-flux enclosure; it is not discarded.
Reuse kernel_bounds.npz and results.json from edq-complete-flux-sign-2026-09-07
as immutable inputs. They contain floating evaluations of analytic enclosures,
not certified interval arithmetic. Maintain a separate 1e-8 numerical margin.

Periodicity gives K(d,e)=(r/d)^2*K(r,e) for r=d mod e>0, and K(d,e)=0
for r=0. This permits all new pairs to use the saved kernel bounds.
Sum with each actual Möbius sign before reporting signed values. Record every
ratio band S_L-S_(L/2), S_L, T_L and the lower/upper enclosure for |T_L|/R_N.
The saved R_N bounds are positive at all chosen cutoffs.

## Predeclared classification

Evaluate in this order, using outward analytic intervals plus the separate
numerical margin (not a proof of floating-point error):

1. LOCAL if all nine upper bounds for |T_4|/R_N are at most 1/4.
2. CROSS-RATIO CANCELLATION if at least five lower bounds exceed 1.
3. MIXED otherwise.

A lower bound above 1/4 at any cutoff reverses the working prediction;
if no such lower bound exists but LOCAL fails, report unresolved.
These finite outcomes do not prove an asymptotic law or an RH ceiling.

## Validation, resource limit and artifacts

Run only on the authorized RunPod. Eight independent cutoff workers, native
numerical threads one, 120-second external timeout. No Lean build is needed.

- Verify immutable input hashes before executing the script.
- Validate Möbius coefficients by direct factorization for every n<=256 and
  every n in 32700..32768, and verify all needed finite divisor identities.
- Require every saved periodic-rescaling identity among indices <=512 to
  have overlapping enclosures, and every divisibility-zero entry to vanish.
- Compare new K(d,e) values for (513,511),(1025,512),(2039,127),(32767,31)
  with independently summed j<=4096 series plus e/(8*d^2*4096) tail bounds.
- For e=2,7,31, check complete Möbius columns through d=32768, with the
  absolute omitted tail e*zeta(2)/(8*32768), enclose P_e(1).
- Check N=2,L=2 and L=4 against the derived formulas
  pi^2/(32*9) and pi^2/32*(1/9+1/25+1/49), respectively.
- Download the complete results, log and output hashes. Keep script, protocol,
  copied immutable inputs and report in this directory. Verify downloaded hashes
  and remove only owned remote files after confirming the process ended.

The next proof action depends on the classification: LOCAL focuses on a
balanced-ratio arithmetic estimate; CROSS-RATIO CANCELLATION focuses on an
exact compensation across ratio ranges; MIXED requires retaining the measured
exceptional ranges. No finite classification licenses dropping the remainder.
