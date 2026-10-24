# Trans-Threshold Pair Correlation

Trans-Threshold Pair Correlation asks which **signed correlations of close
prime pairs** improve a rank–trace certificate for zeros on the critical line.
It works beyond the Dirichlet mean-value diagonal $X\approx T$, where the
prime polynomial is longer than the height interval observing it.

Its target is a better zero proportion, especially $3/4$, rather than RH.
The programme reduces that target to a normalized prime-pair budget and
separates the parts already paid from the remaining actual-prime correlation.

## Objects and the target constant

At height $T$, choose bandwidth $\lambda$ and prime length
$X=(T/2\pi)^\lambda$. A band-limited profile gives an explicit-formula Gram
matrix. Rank–trace inertia converts an upper bound $\kappa$ on its normalized
Frobenius norm into a critical-line proportion $2-\kappa$.

The norm splits into an explicitly evaluated **core** and a **surplus**
containing off-diagonal prime pairs, prime–pole interactions and grid end effects.
The difference-frequency pair sum has the form

$$
\sum_{n\ne m\le X}a_na_m\,A^-(\log n,\log m),
$$

where $a_n$ contains the von Mangoldt weight and $A^-$ retains the height
oscillation. **Coalescent pairs** satisfy $|\log(n/m)|\lesssim1/T$: their
frequencies cannot be separated by observation on $[T,2T]$.

For the specified subthreshold method, the core is
$\kappa(\lambda)=1/\lambda+\lambda/3$. Its minimum on $0<\lambda\le1$ is
$4/3$, giving $2/3$. At $\lambda=4/3$, the core drops to $43/36$.
A normalized surplus at most $1/18+o(1)$ would give $\kappa\le5/4$ and hence
$3/4$. This is the arithmetic budget; the reductions do not assert it.

## Foundational mechanisms

**Kernel parity.** The difference-frequency kernel splits into cosine and sine
parts. In the sine part, a difference of Lipschitz moments cancels the apparent
close-pair denominator. Expanding into absolute values before this cancellation
would invent a singular cost absent from the exact expression.

**Mean-value reduction.** The remaining kernel is a mixed mean value of prime
Dirichlet polynomials. Below the diagonal, frequency separation permits
Montgomery–Vaughan control. Above it, size-only bounds lose a factor comparable
to $X/T$ on close pairs. The missing input is their signed correlation, not a
stronger use of the same coefficient-size bound.

**Localization of the surplus.** Smooth and Jackson-type weights control far
pairs, end effects and noncoalescent contributions. The actual-zeta
smooth-window certificate places the remaining budget on the coalescent band:
its base proportion is $29/36$, before subtracting the normalized surplus.
Paying $1/18$ leaves $3/4$.

**Prime-power and parity reduction.** Proper prime powers have a paid tail.
The remaining problem can be expressed using distinct odd primes and even
integer shifts. This retains the parity constraint that an unsigned sieve
estimate can lose.

**Ramanujan models.** Truncated singular-series calculations supply an exact
candidate main term, including signed pole cancellation. Their role is to
identify the correct approximation to the prime-pair measure. A model
asymptotic becomes an estimate on actual primes only after its weighted error
is bounded uniformly in the moving cutoff.

**The form-factor dictionary.** On the zero side, the same surplus is measured
by a weighted integral of the pair-correlation form factor beyond $\alpha=1$.
This gives an exchange rate between bandwidth, surplus and certified
proportion. It is useful for intermediate gains as well as the $4/3$ target.

## The remaining arithmetic problem

Approximate the actual odd-prime pair measure by the truncated singular series
**inside the signed coalescent kernel**, with integrated error below the chosen
surplus budget. This is a sharper demand than a nonnegative pair-count bound.
The height phase, normalization and truncation dependence are part of it.

The main questions are:

- Can this signed approximation reach the $1/18$ budget at bandwidth $4/3$?
- Can a smaller extension beyond bandwidth $1$ give a rigorously quantified
  improvement over $2/3$?
- Which averaging or dispersion estimate controls the moving-kernel error
  while preserving the parity and prime–pole cancellation?
- Can the kernel or test profile be improved to make the required arithmetic
  estimate more accessible, with the resulting proportion computed exactly?

Prime-power tails, unsigned sieve terms and signed model sums already have
bounds. The unresolved step is the actual-prime surplus at the required
constant. Neither a model evaluation nor an unnormalized close-pair estimate
pays it.

## Place in the wider research

[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md)
supplies rank–trace inertia and its Gram-only information barrier.
[Square-Root Threshold](../SquareRootThreshold/README.md) explains the
aperture–height diagonal.
[Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md)
asks related prime-ratio questions at one height; TTPC uses a height average.
[Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) supplies
large-sieve and signed arithmetic tools, with a different receiver to be paid.

Start with the normalization and $1/18$ budget, then the kernel decomposition.
The [programme umbrella](../TransThresholdPairCorrelation.lean) maps the
localization, prime-power elimination and singular-series modules.
