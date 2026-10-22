# CCM-FU: signed initial-gcd interval budget

- **Type:** [BRIDGE], sufficient source-bound candidate.
- **Status:** Rejected by already archived numerical source data; planned computation cancelled before execution. No new formal refutation.
- **Goal:** Actual divisor-source cancellation → uniform signed Abel bound → CCM-FU → RH.
- **Related:** [Positive gcd budget](../../ccm-fu-positive-gcd-budget.md), [prime-neighbor compensation](../../ccm-fu-one-prime-gcd-compensation.md).

## Frozen question

For the literal channels `C_d(M)`, diagonal `D(M)=sum C_d(M)^2`, and exact
ordered cross groups `G_r(M)`, put

```text
A_R(M) = sum_(1 <= r <= R) G_r(M).
```

Test the sufficient claim

```text
A_R(M) <= D(M), for every M and every R.
```

At `R=M`, the existing identity gives `S(M)^2=D(M)+A_M(M)`. The proposed
bound would therefore imply `S(M)^2<=2D(M)<=1444M^2` and supply the required
linear Abel bound. The coefficient one and natural gcd ordering are fixed
before execution; no regrouping or coefficient change follows a failure.

This is not the failed positive-part budget: each interval retains all its
negative groups. It is not an increasing-prime energy history either. The
already proved obstruction to that history does not decide these gcd
interval sums. A finite pass would not establish this universal claim.

The saved source has large positive and negative groups, including positive
groups at small gcds. Their complete sum is known numerically, but those data
have not been reduced to every initial-gcd interval in the cited studies.
Neither individual sign failures nor the full total determines the largest
intermediate interval sum. This is the unresolved diagnostic, not another
confirmation of the previously tested endpoints.

## Exact arithmetic readout

For `1<=k<M`, let

```text
H_k = sum_(k divides d, 1<=d<M) C_d,
B_k = H_k^2 - sum_(k divides d, 1<=d<M) C_d^2,
a_R(k) = sum_(r divides k, 1<=r<=R) mu(k/r).
```

Partitioning the ordered pairs by their exact gcd gives
`B_k=sum_(k divides r)G_r`. Finite Möbius inversion and interchange therefore
give the complete identity

```text
A_R = sum_(1<=k<M) a_R(k)*B_k
    = sum_(1<=k<M) a_R(k)*H_k^2 - sum_(1<=d<=R) C_d^2.
```

For the second equality, the coefficient of `C_d^2` is
`sum_(k divides d)a_R(k)=1_(d<=R)`, by the divisor sum of Möbius.
These finite algebraic identities supply an independent audit algorithm.
They do not bound the signed quadratic sum. In particular `a_R(1)=1` for
positive R, so the original head `H_1=S` remains present. Removing that term
would remove the quantity to be bounded. These identities are paper
derivations here, not new Lean certificates.

## Frozen experiment

**Cancelled.** The source file
`../2-fully-proven/computations/ccm-fu-positive-gcd-budget-2026-09-08/cutoff_1024.json`
already records

```text
G_1(1024) = 1369.1347858392138005,
D(1024)   = 1249.1097676908449106.
```

Since `A_1=G_1`, these archived values already violate the frozen bound.
There is no reason to rerun the proposed screen to rediscover that failure.
The unexecuted script has been removed. These are earlier RunPod floating
results, not a new computation, an independent high-precision audit of G_1,
or a Lean inequality certificate. No larger constant is substituted.

The same archive records a negative complete cross sum through its head and
diagonal. Thus this witness requires compensation from nonprimitive gcd
groups even for the weaker allowance of one full diagonal. The already formal
complete gcd decomposition and coprime-column transport retain that reserve;
this numerical witness adds no new unconditional upper bound. No formal
route retirement or newly proved positive survivor is claimed.

The unexecuted protocol below is retained to identify the cancelled test.

1. Use exactly the 165 saved `cutoff_M.npz` arrays from
   `../2-fully-proven/computations/ccm-fu-positive-gcd-budget-2026-09-08`:
   every M from101 through256 and powers of two from512 through131072.
   Do not regenerate source arrays or extend the screen cutoffs.
2. On RunPod, use four cutoff workers, one BLAS thread, and a 60-second
   internal deadline. Compute every prefix including the empty prefix,
   record all prefixes, their maximum, its smallest attaining R, and all
   violations of `A_R-D > 1e-10*max(1,D)`. Preserve every G term.
3. Check the terminal reconstruction against `S^2-D` at tolerance
   `1e-12*max(1,D)`. At every M from101 through112, independently group all
   channel pairs by gcd and compare every prefix with the saved-array route.
4. Select the first failing M and its first failing R. If no failure exists,
   select the largest `max_R A_R/D`, breaking ties by smallest M and then R.
   Independently reconstruct the selected source at80 decimal digits and
   evaluate the divisor-coefficient identity above. Use four workers and a
   separate 90-second deadline; report partial audit if that deadline expires.
   Compare every reconstructed channel with the saved source and retain the
   selected prefix, diagonal and full head. No numerical value enters Lean.
5. Save script, input hashes, all outputs and interpretation under
   `2-fully-proven/computations`; download and verify hashes, then remove
   owned remote files and processes. Do not rerun at larger cutoffs after a pass.

A failure identifies an initial gcd interval requiring compensation from
outside that interval. A pass leaves the uniform arithmetic bound unproved.
Neither outcome by itself decides SD1, adaptive prime ordering, or RH.

## Corpus search and present execution limit

An unrestricted `--mode deep --any` search for `Ramanujan` returned278 matches
in38 modules. It reported partial semantic coverage and a disconnected
semantic worker. Candidate lemmas, source arguments, proof ideas and the
proposed ingredient set were inspected. The generated modular-form identity
chain concerned Eisenstein derivatives, not the required gcd-source estimate.
[Full response](../../ccm-fu-gcd-prefix-budget/ramanujan-search.json).

`MobiusRamanujanTwoLevelConservation` proves exact two-level primitive Fourier
reconstruction with arbitrary weights. It retains the complete Möbius sum;
it does not bound its amplitude. `KloostermanSameModulusRamanujanQuadratic`
retains a Ramanujan main term, a same-modulus completion remainder and a
distinct-modulus quadratic. Its remainder bound alone does not establish
the literal divisor-source inequality. `DivisorStationaryKernelPositivity`
classifies positivity by its incidence coefficients; those coefficients are
not automatically nonnegative for a signed gcd cutoff.

SSH to the supplied host and port returned `Connection refused` before any
experiment was started. A current endpoint was requested, but this particular
experiment is now cancelled regardless of endpoint availability. No local
substitute computation, new numerical result, new Lean declaration or
frontier-map edit was made.
