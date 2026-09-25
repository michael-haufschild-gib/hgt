# Actual Weil pole entry barrier: two failed propagation tests

**Status: exploratory numerical evidence, not a mathematical or Lean proof.** No numerical result from this folder is used in Lean. RH and the actual pole-energy sign remain open.

## Mathematical question

The direct target is nonnegativity of the actual even Weil pole energy `Y(a)`. Together with the actual odd signs, this closes the existing pole-positivity → integrated prime-error bound → resolvent → RH chain.

Inside a late prime-power gap, write `v=Y'`, `F=Y''>0` and consider

`B=Y-v²/(2F)`.

A proof of `B≥0` would imply `Y≥0`, and `B=Y` at an interior minimum. Between entries, differentiation gives `B'=v²F'/(2F²)`. At the entry `a=log(n)/2`, the exact corpus atom laws give continuous value and one-sided curvature, and a velocity jump `v_after=v_before-J`, with

`J=4Lambda(n)(1+1/sqrt(n))²`.

Thus

`Delta B=J(2v_before-J)/(2F)`.

Two proposed direct proofs were tested:

1. Every actual entry preserves or increases `B`.
2. If some entries decrease `B`, all their decreases can be paid by the initial barrier and continuous growth, without needing positive jump contributions.

Both mechanisms fail in the evaluated actual source. Positivity of `B` itself is a separate unresolved claim.

## Scope and method

- Host: user-specified Runpod, 32 visible CPUs; eight worker processes, one numerical thread per worker.
- Every genuine prime-power entry from the corpus's explicit late-curvature threshold through `n≤2,000,000` was evaluated: **148,798 entries**. The threshold is approximately `a=3.9605875668`, hence the integer cutoff starts at 2756; the first nonzero entry is 2767.
- A sieve generated primes. Every prime power `p^k` received its actual weight `log(p)`. Ordinary, reciprocal, and weighted logarithmic Mangoldt sums retained all these entries.
- The exact corpus expressions supplied the incoming derivative, actual energy, and common one-sided curvature. The Gamma boundary primitives were evaluated by elementary antiderivatives. The cross boundary used `pi²/6-Li₂(1/n)`; in the vector scan, twelve series terms have omitted tail at most `(1/n)^13/[169(1-1/n)]`.
- The main scan uses floating-point arithmetic. Fifteen selected entries were recomputed with 80-digit arithmetic and fresh finite prime-power summation using the generated prime list. Two boundary evaluations were also checked by direct quadrature of the original integral primitives; printed differences were zero at the working precision.
- The main scan and selected high-precision checks completed in about 2.5 seconds. A second script analyzed the saved entry data, without rerunning the source scan.

The source formulas come from `CCMRestrictedWeilPoleFirstJets`, `CCMRestrictedWeilPoleBoundaryPrimitives`, `CCMRestrictedWeilPoleBoundaryDifferential`, `CCMRestrictedWeilPoleParityCurvature`, `CCMRestrictedWeilPoleEntrySlopes`, and `CCMRestrictedWeilPoleLogMoment`.

## Results

**Monotone entry propagation fails numerically at 67,155 of the 148,798 entries.** At the first tested entry, `n=2767`, the 80-digit recomputation gives approximately

| Quantity | Value |
|---|---:|
| Incoming velocity | -32.4294654893 |
| Positive jump magnitude | 32.9188829693 |
| Curvature | 22990.5278708 |
| Actual even energy | 5.79269737546 |
| Incoming barrier | 5.76982555977 |
| Outgoing barrier | 5.69982420025 |
| Barrier jump | **-0.0700013595258181** |

The most negative scanned jump is approximately `-0.144264322005471` at `n=2861`, also checked at 80 digits.

**Continuous growth cannot pay all negative jumps by itself.** Starting immediately before entry 2767, discard all positive jump credits and retain the actual initial barrier and all between-entry increments. This remaining budget first becomes negative at `n=4733`:

- initial barrier: `5.76982555977`;
- accumulated continuous growth: `0.026065375061`;
- accumulated negative jump debt: `5.80542627215`;
- budget after discarding positive jumps: **`-0.00953533731249`**;
- actual outgoing barrier, including positive jump credits: `5.38080548529`.

At the final entry `n=1,999,993`:

| Accumulated quantity | Value |
|---|---:|
| Positive jump credits | 548.068182813 |
| Negative jump debt | 396.958964108 |
| Net signed jump credit | 151.109218705 |
| Continuous growth | 0.306891458467 |
| Final outgoing barrier | 157.185935724 |

The decomposition reconstructs the saved barrier with maximum floating-point discrepancy below `7.5e-12`. No between-entry endpoint increment below `-1e-7` was observed.

No scanned actual even energy or outgoing barrier was negative. The smallest outgoing barrier in the scan was approximately `3.20710154118` at `n=3089`. These are statements about the scanned entries, not proofs at all apertures or at unbounded height.

## Interpretation and consequence

The proposed proof by monotone prime-entry propagation is rejected as an experimental lead. The fallback that pays every adverse entry solely from continuous convexity is also rejected. The actual positive jump contributions must remain in any successor estimate; taking only losses destroys the available margin in this scan.

The exact surviving balance is

`B_final=B_initial+continuous_growth+positive_jump_credit-negative_jump_debt`.

Proving this balance nonnegative uniformly still requires control of the signed arithmetic action. The experiments do not establish that control, a global lower bound for `B`, or any RH conclusion. No new closed Lean theorem or mathematical route retirement is claimed.

## Reproduction and files

On the Runpod, execute `python3 entry_barrier.py`, then `python3 analyze_balance.py`, in a fresh output directory containing both scripts. They write:

- `entries.csv.gz`: all scanned entry values;
- `summary.json`: scan counts and extrema;
- `selected.csv` and `high_precision.json`: selected values and 80-digit recomputations;
- `boundary_checks.json`: independent integral evaluations;
- `balance_summary.json`: accumulated jump and continuous balances.

All outputs have been downloaded here. Both foreground remote processes completed and their worker pools joined.
