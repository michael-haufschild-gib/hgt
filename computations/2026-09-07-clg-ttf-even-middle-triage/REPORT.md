# CLG/TTF even middle interval: Runpod sign triage

**Status:** Numerical guidance only. No interval certificate, certified infinite-source tail, negative theorem, or Lean premise follows.

**Question:** Does the fixed canonical correction, or either endpoint of its proved rational coefficient band, show a sign failure in the remaining middle interval? This was not known before the run.

**Execution:** Runpod `root@157.157.221.29:27094`; Python with mpmath 1.3.0, 100 decimal digits, 16 worker processes on 32 logical CPUs. Runtime reported by the script: approximately 0.101 seconds. Results were downloaded. The task's remote scratch directory was removed after completion.

## Source and normalization

The script follows `ThetaCuspFinitePrimeSource.lean` and `ThetaCuspFirstAtomReflectionJets.lean`. With `q=π exp(2x)`, each atom has the form `exp(x/2−n²q)P₀(n²q)`, where `P₀(z)=4z²−6z` and

`P_(j+1)=(1/2)P_j+2z P_j′−2z P_j`.

Finite sums through atom 12 and through atom 18 supply the source jets. The reflected moments retain all Leibniz terms. The matrix entries are divided by `φ₁²q^k`; its Schur complement is therefore `S/(φ₁²q⁶)`. The added correction is `C G/(φ₁²q⁶)`. The approximate canonical coefficient is obtained from the atom-18 seam using its defining source formula, not imposed as an input sign.

## Results

The scan uses 65 equally spaced centers from `8/95` through `6/5`. Every sampled corrected Schur value is positive for each of the three coefficient choices. The atom-18 minima are:

| Coefficient | Minimum sampled normalized margin | Center |
|---|---:|---:|
| `10^12` | `90,663,208.6267` | `0.3631578947` |
| Approximate canonical `2,418,362,512,313.4617` | `39,081,801.6255` | `0.3631578947` |
| `3·10^12` | `17,929,465.9433` | `0.3631578947` |

`results.json` retains every center, both atom truncations, the normalized uncorrected Schur complement, correction and head determinant. The script supplies no certified tail or rounding bound. Positive samples do not prove positivity between centers or for the full infinite source.

**Consequence for research:** Continue the finite two-atom comparison with the corpus's complete derivative/error bounds through twelve. A source-valid signed interval estimate must still pay the complete matrix and correction error. There is no sampled indication that the fixed coefficient band needs replacement.

## Complete error-budget triage

`error_budget.py` tests a different unknown: whether the already proved complete entry and correction majorants leave room for the finite two-atom lower comparison. It ran on the same Runpod host with 16 workers and 100 decimal digits in approximately 0.060 seconds. Outputs are in `error-budget-results.json`; remote scratch was removed after download.

The script follows `ThetaCuspDeepTailCoolingTwelve`, `ThetaCuspTwoAtomSourceTwelve`, `ThetaCuspTwoAtomReflectedTwelve`, `ThetaCuspTwoAtomCompensationError` and `ThetaCuspEvenFourTwoAtomError`. It retains the exact first-atom derivatives, the two-atom likelihood-partition derivatives, both reflected cross terms, quadratic tail products and the complete correction error. Entry `k` is divided by `φ₁²(32q)^k`, a positive diagonal congruence and mass scaling.

Let `L` be the retained matrix with last correction `min(10^12 G[T],3·10^12 G[T])`, and `E` the complete nonnegative error matrix. At every one of the 65 centers, all four leading principal minors of each `L−D_s E D_s` are numerically positive, for all eight sign vectors `s=(1,±1,±1,±1)`. Simultaneous reversal of all four signs gives the same matrix, so these represent all sign cases. This is a sufficient comparison for `vᵀL v−|v|ᵀE|v|>0`: choose the sign vector of `v`, up to simultaneous reversal.

No sampled center failed this sufficient matrix comparison. This is stronger guidance than a scan of the retained or canonical determinant alone: the existing complete error majorants appear compatible with a proof. The script still supplies no certified arithmetic or between-center bound. The next mathematical obligation is uniform positivity of the finite signed comparison matrices over the entire middle interval.
