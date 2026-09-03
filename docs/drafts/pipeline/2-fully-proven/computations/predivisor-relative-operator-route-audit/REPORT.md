# Pre-divisor relative-operator route: Runpod audit

- **Date:** 2026-09-03
- **Compute host:** Runpod `root@213.173.111.70:31066`, Ubuntu 20.04, Python 3.8.10
- **Decision:** **RETIRE the proposed Step 1--6 relative-projection route.**
- **Related failed card:**
  `docs/drafts/pipeline/5-failed/universal-law-field/direct-subunit-anchor/integral-nuclear-prime-mixed-homotopy-defect.md`

## What was run

Three diagnostics were run sequentially in the foreground on Runpod. No Lean process, local
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
`1.2431119579116424...`. Thus literal scalar prime/polar completion does not cancel. A new coupled
operator short would have to remove this positive surplus before taking absolute values. Existing
corpus results already prove that finite-limit scalar polar countercurrent cannot uniformly
renormalize cofinal coordinate traces, so larger scalar scan cannot repair route.

## Final route decision

Retire proposed route because its three plausible producers fail independently:

- exact Gamma subtraction is positive and has index zero;
- wild-saddle relocation has signed trace zero and no horizontal sensitivity;
- literal cubic-Green completion retains a large positive polar surplus.

Positive rank-at-most-two projective-gauge carrier in Lean corpus does not change verdict: exact
source recovery is nonlinear quotient by a decaying gauge, so its trace-class carrier norm does not
bound recovered source reporter. Separately, any projection difference with trace one has trace
norm at least one. These are structural obstructions, not cutoff effects.

Positive survivor: retain only open search class for a genuinely coupled, coefficient-faithful
prime--polar--Gamma relative operator whose cancellation occurs before absolute value, acts
nontrivially on finite source witnesses, and lands full multiplicity-sensitive Xi conormal Gram.
Such operator has not been constructed. It is a new producer obligation, not reason to continue or
formalize retired Step 1--6 route. No Lean module should be added from this audit.

## Artifacts and checksums

```text
6bd5bb205ae4c9dd32f8cba2c607e22270ddbd07d18e3cc483b58bb3ec8ad940  critical-zero-cache.jsonl
31ffe99051e0f53197b5b2aaaee9001defdd549600f84e55edae891a7fde4b95  cubic-green-polar-surplus-results.json
e50ac3472cad56f674c83942fae0d2098ff1d76b50a8f5feda6220bc4b951d11  gamma-valuation-schur-results.json
ee29b88c05b57d97c365bce844a4f17c8d37fe137e27c71e1f333608f4259342  wild-saddle-results.json
```

Remote and downloaded hashes matched before cleanup. Results are numerical evidence, not interval
certificates or substitutes for exact unconditional Lean locks cited by failed-route card.
