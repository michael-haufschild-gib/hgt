# Pre-divisor relative-operator route: Runpod audit

- **Date:** 2026-09-03
- **Compute host:** Runpod `root@213.173.111.70:31066`, Ubuntu 20.04, Python 3.8.10
- **Decision:** **RETIRE the proposed Step 1--6 relative-projection route.**
- **Related failed card:**
  `docs/drafts/pipeline/5-failed/universal-law-field/direct-subunit-anchor/integral-nuclear-prime-mixed-homotopy-defect.md`

## What was run

Six diagnostics were run sequentially in the foreground on Runpod. No Lean process, local
mathematical computation, background job, or parallel numerical process was used.

1. `scripts/numerics/predivisor_gamma_valuation_schur_audit.py`
   tested exact Gamma valuation Gram subtraction and deliberate over-subtractions on the first
   1 through 128 primes. Threshold arithmetic used 800 decimal digits.
2. `scripts/numerics/two_step_wild_saddle_trace_relocation_audit.py`
   compared the first 2,000 critical-line Xi ordinates with the corpus two-step wild-saddle source.
   The append-only zero cache makes the run restartable.
3. `scripts/numerics/predivisor_cubic_green_polar_surplus_audit.py`
   evaluated the exact CCM/Route-P cubic-Green fracture through `N = 50,000,000`, enumerating
   3,001,134 primes and 3,002,195 prime-power events.
4. `scripts/numerics/predivisor_cubic_green_completed_tail_audit.py`
   restored the literal Gamma density omitted from diagnostic 3, removed the first-prime boundary
   atom according to strict lower-window convention, and evaluated the signed completed scalar
   tail through `N = 50,000,000` at 100 decimal digits.
5. `scripts/numerics/integral_nuclear_homotopy_defect_audit.py` was rerun on the replacement
   Runpod through 5,000,000 as a reproducibility smoke check of the stronger 50,000,000 audit in
   the sibling `integral-nuclear-prime-mixed-homotopy-defect` computation folder.
6. `scripts/numerics/restricted_hardy_cubic_exponential_hankel_audit.py` evaluated the full finite
   cyclic Gram of the positive exponential-Hankel surrogate through `p^k <= 10,000`.  Unlike a
   diagonal coefficient budget, this retains every mixed three-frequency term.

Principal commands:

```text
python3 predivisor_gamma_valuation_schur_audit.py \
  --sizes 1,2,3,4,6,8,12,16,24,32,48,64,96,128 \
  --alphas 1,1.000000000001,1.000000001,1.000001,1.001,1.01,1.1,2 \
  --dps 800 --output gamma-valuation-schur-results.json

python3 two_step_wild_saddle_trace_relocation_audit.py \
  --count 2000 --dps 50 --checkpoints 10,25,50,100,250,500,1000,1500,2000 \
  --zero-cache critical-zero-cache.jsonl --output wild-saddle-results.json

python3 predivisor_cubic_green_polar_surplus_audit.py \
  --cutoffs 2,3,10,100,1000,10000,100000,1000000,10000000,50000000 \
  --dps 100 --output cubic-green-polar-surplus-results.json

python3 predivisor_cubic_green_completed_tail_audit.py \
  --cutoffs 2,3,10,100,1000,10000,100000,1000000,10000000,50000000 \
  --dps 100 --output cubic-green-completed-tail-results.json

python3 integral_nuclear_homotopy_defect_audit.py \
  --prime-limit 5000000 --depth-max 20 \
  --output integral-nuclear-homotopy-defect-results.json

OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
python3 restricted_hardy_cubic_exponential_hankel_audit.py \
  --cutoffs 2,3,10,100,1000,3000,10000 \
  --output restricted-hardy-cubic-exponential-hankel-results.json
```

## Results and interpretation

### 1. Exact Gamma subtraction cannot create index one

For `q_p = 1/p` and `d_p = sqrt(q_p)(1-q_p)`, the completed finite Gram is

```text
K_ij = d_i d_j / (1-q_i q_j).
```

Literal Gamma subtraction has coefficient `alpha = 1` and leaves

```text
K - f_0 f_0* = sum_{e>=1} f_e f_e* >= 0.
```

Every tested exact-subtraction section was positive up to floating-point conditioning. A negative
direction occurs only after replacing the source coefficient by `alpha > 1`. Exact finite
threshold is

```text
alpha_crit = 1 / (1 - product_p q_p^2).
```

At 128 primes, `alpha_crit - 1` is about `1.0153533325e-596`: arbitrarily tiny deliberate
oversubtraction can manufacture one negative direction at large finite rank, but arithmetic source
supplies exactly `alpha = 1`. Therefore proposed Gamma-vacuum mechanism has no lawful negative
index. Tiny numerical zero/negative eigenvalues at `alpha = 1` are ill-conditioning of the Cauchy
matrix, not mathematical negative spectrum.

### 2. Wild-saddle relocation is subunit-looking but index-blind

At 2,000 zeros:

```text
signed two-copy S1 partial       = 0.5888975393880009
signed two-copy trace partial    = 0
one-sided signed trace partial   = 0.14133562497190344
last-half one-sided L1 mass      = 0.006740549130939971
```

Trace of signed doubled operator is identically zero by construction at every cutoff. Its finite
trace norm remains below one and its tail decays on this range, but it cannot specialize to trace
one. It also uses only ordered critical-line ordinates and is insensitive to hypothetical
horizontal displacement. This closes it as missing pre-divisor defect; data do not certify
infinite trace norm.

### 3. Literal polar completion leaves a stable positive surplus

Exact cubic-Green fracture is

```text
polar mass - truncated Route-P base budget.
```

At `N = 50,000,000`:

```text
polar mass                       = 1.2427142049873618...
truncated Route-P base budget    = 0.40322974946892837
polar surplus                    = 0.8394844555184334...
prime / polar ratio              = 0.3244750465156461...
```

Surplus stabilizes near `0.83948446` from `N = 1,000` onward; computed infinite polar mass is
`1.2431119579116424...`. This diagnostic intentionally omitted Gamma and used the full interval
from zero. It proves that prime/polar subtraction alone does not cancel, but it does **not** decide
the Gamma-completed open tail studied next.

### 4. Gamma completion exposes a genuine signed scalar survivor

For strict lower wall `L = log 2`, first atom is excluded and literal densities are

```text
prime open tail = sum_(2 < p^k) 1/(4 p^k k^3 log(p)^2),
polar           = integral_L^H (1+exp(-h))/(4h^3) dh,
Gamma           = integral_L^H exp(-h)/(4h^3(1-exp(-2h))) dh.
```

At `N = 50,000,000`:

```text
first prime atom                  = 0.26017112262570097...
open prime mass                   = 0.14305862684322739...
polar tail                        = 0.34702437134134662...
Gamma tail                        = 0.10482079256564872...
prime - polar + Gamma             = -0.09914495193247051...
absolute value                    = 0.09914495193247051...
```

This changes positive-salvage verdict, not failed operator-route verdict. Exact paper proof and
Lean module now establish unconditionally that infinite signed scalar completion has absolute
value `< 1`; see
`GaloisForLFunctions.RHTower.CCMRoutePCompletedCubicGreenTailSubunit`. Scalar cancellation is not
a nuclear-norm estimate: absolute values inside trace norm may destroy it.

Direct operator test is also closed exactly in Lean. Scaling existing unit-trace prime-Hodge
nuclear defect by completed scalar gives trace norm `<1`, but trace becomes scalar and is neither
`1` nor `-1`; see
`GaloisForLFunctions.RHTower.CCMRoutePCompletedCubicGreenIntegralDefectNoGo`. Thus scalar amplitude
renormalization cannot preserve index integrality.

### 5. Post-audit exact relative-curvature survivor

The strongest lawful version of the proposed “two divergent metrics, finite relative defect” idea
was subsequently constructed without divisor input. The literal theta Mellin-six survival shift
has compact positive incoming and outgoing metrics, neither Schatten-one, while their exact
self-commutator difference is positive Schatten-one with trace `1`, trace norm `1`, and operator
norm `1/3`. Its normalized Stokes all-prime lift preserves nonzero cross-prime entries and the
same trace/norm laws. Lean capstones are
`RHTower.primeHodgeHistoryRelativeCurvature_closed` and
`RHTower.primeHodgeHistoryRelativeCurvaturePrimeLift_closed`.

This confirms the relative-metric mechanism but also pinpoints its limit: small operator norm does
not imply small trace norm. Positivity plus trace `1` forces trace norm exactly `1`. Therefore this
survivor cannot be substituted for the missing signed coefficient-faithful nuclear completion.
Its full paper and formal status are recorded in stage-3 card
`theta-survival-relative-curvature-reconstruction.md`.

### 6. Replacement-host finite-source rerun reproduces the retired obstruction

The 5,000,000-prime-limit rerun reproduced the stronger prior audit's structural outputs:

```text
coherent equal-factor defect trace norms     = 0 at packet sizes 1 through 8
nested rank-difference-one trace norm         = 1.0000000000000007
best natural grading residual, zero clock     = 0.08894048823857957
best natural grading residual, mixed clock    = 0.11476719579237721
half-base rigorous upper at this cutoff       = 0.2096548419650482
```

The finite source and collision Grams agree on their diagonal ratio but not off diagonal: the
mixed-clock off-diagonal ratios have nonzero imaginary part and the best scalar fit retains
relative residual `0.1137942643498194`.  Thus diagonal rescaling does not provide the required
matrix-complete factorization.  This rerun is weaker in cutoff than the existing 50,000,000 audit
and changes no theorem or verdict; it only verifies reproducibility on the replacement host.

### 7. Full cyclic exponential-Hankel surrogate has margin but is not the missing bridge

For each prime-power event `n = p^k`, the diagnostic formed

```text
a_n = log(n),
c_n = Lambda(n) / (2 n log(n)^2),
H_X = sum_(n <= X) c_n |exp(-a_n x)><exp(-a_n x)|.
```

Its feature Gram is `G_ij = sqrt(c_i c_j)/(a_i+a_j)`.  Therefore `Tr H_X` is exactly the
truncated Route-P base budget and `Tr(H_X^3) = Tr(G_X^3)` retains the complete cyclic triple
interaction.  At `X = 10,000` (1,280 prime-power events):

```text
Tr H_X                                  = 0.40215445468965655
||H_X||                                 = 0.3855625981008574
Tr(H_X^3)                               = 0.057320757311682395
2 Tr(H_X^3)                             = 0.11464151462336479
margin below 1                          = 0.8853584853766352
mixed cyclic share of Tr(H_X^3)         = 0.686809074484133
```

The tiny negative minimum Gram eigenvalue (`-1.05e-18`) is floating-point roundoff.  Numerically,
the positive surrogate has ample cubic margin.  But `68.68%` of its cubic trace comes from mixed
cyclic terms, which confirms the exact two-mode obstruction to diagonal-only estimates.  More
importantly, corpus audit found no identity equating this surrogate with the anomaly-subtracted
arithmetic Hardy seam.  Literal ordinary-prime endpoint atoms are not absolutely nuclear, the
one-prime scattering defect has no compactness theorem, and the proved successor carrier has
strict anti-Hankel curvature that no additive Hankel boundary can repair.  Consequently these data
support continued investigation only of a genuinely renormalized, non-Hankel cross-term
transgression.  They do not revive the retired relative-projection route and do not prove an index
or infinite Schatten bound.

## Final route decision

Retire proposed Step 1--6 relative-projection route because its proposed operator producers fail:

- exact Gamma subtraction is positive and has index zero;
- wild-saddle relocation has signed trace zero and no horizontal sensitivity;
- prime/polar-only cubic completion retains a large positive surplus;
- adding literal Gamma repairs signed scalar size but supplies no trace-class factorization or
  index-one landing.

Positive rank-at-most-two projective-gauge carrier in Lean corpus does not change verdict: exact
source recovery is nonlinear quotient by a decaying gauge, so its trace-class carrier norm does not
bound recovered source reporter. Separately, any projection difference with trace one has trace
norm at least one. These are structural obstructions, not cutoff effects.

Positive survivor: signed scalar prime--polar--Gamma completion is genuinely and unconditionally
subunit. It is formalized as `RHTower.abs_ccmRoutePCompletedCubicGreenTail_lt_one`. Remaining open
search class is a coefficient-faithful nuclear lift whose cancellation survives the nuclear norm,
acts nontrivially on finite source witnesses, and lands full multiplicity-sensitive Xi conormal
index. Such operator has not been constructed. This is a new producer obligation, not revival of
retired Step 1--6 projection route.

The later exponential-Hankel calculation does not alter that decision.  It shows a separate
restricted-Hardy cubic surrogate has enough numerical norm margin if an exact source identity can
be proved.  Current continuation gate is therefore algebraic/operator-theoretic, not numerical:
construct the missing non-Hankel scattering transgression or retire that distinct surrogate too.

Subsequent exact operator audit sharpened that obligation.  For the restricted-Hardy candidate
`T=(U*PU-P)^3`, its nuclear norm is exactly the sum of the cubes of the two chiral Hankel
Schatten-three norms.  Duhamel bounds this by the additive phase-current commutator with constant
one, but a two-mode Hankel block already disproves constant-one domination by separate diagonal
coefficient cubes.  Existing Route-P source/zero Cauchy-Gram domination is independently known to
be RH-equivalent.  Future work must therefore construct a finite-stage, coefficient-faithful
factorization of the additive boundary Hankel operator through the full source cyclic Gram; a
scalar budget or post-completion zero-Gram comparison cannot close the route.

## Artifacts and checksums

```text
6bd5bb205ae4c9dd32f8cba2c607e22270ddbd07d18e3cc483b58bb3ec8ad940  critical-zero-cache.jsonl
31ffe99051e0f53197b5b2aaaee9001defdd549600f84e55edae891a7fde4b95  cubic-green-polar-surplus-results.json
59caf57c05f1b8fb489aa3acfe23724e354b19f7b1961e5738ae0df972fc55e0  cubic-green-completed-tail-results.json
e50ac3472cad56f674c83942fae0d2098ff1d76b50a8f5feda6220bc4b951d11  gamma-valuation-schur-results.json
ee29b88c05b57d97c365bce844a4f17c8d37fe137e27c71e1f333608f4259342  wild-saddle-results.json
764b752bc2265127d0bff7ab09242456878b1d9ee40ebfddd81a9f9e57fd63a0  integral-nuclear-homotopy-defect-results.json
2543cfa5e4bfcd1e1390130a4bf27cad5f5fb77f51a6eb5b8a916553009d1ff4  restricted-hardy-cubic-exponential-hankel-results.json
```

Remote and downloaded hashes matched before cleanup. Results are numerical evidence, not interval
certificates or substitutes for exact unconditional Lean locks cited by failed-route card.
