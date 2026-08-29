# Direct fixed-action C5 Jacobian: seam and shape attack

## Scope

Diagnostic computation only. No numerical value or computed sign may enter a Lean proof.

For reflected log action `q(u,t)` and direct normalized C5 balance
`F(t,q,q_t,q_tt)`, the fixed-action Jacobian is

`J = F_u q_t - F_t q_u`.

Reflection gives `q_u(0,t) = F_u(0,t) = 0`. Differentiating once in centre and
cancelling the `F_q` terms gives the exact scalar seam invariant

`M(t) = J_u(0,t)`

`= q_t (F_a q_tuu + F_b q_ttuu)
   - q_uu (F_t + F_a q_tt + F_b q_ttt)`.

This identity was derived algebraically before the numerical run. The computation tested its
sign, extracted its first formal Taylor coefficient, checked it against `J(u,t)/u`, and attacked
monotonicity of the desingularized Jacobian.

## Run

- Host: supplied RunPod, Linux 6.8, Python 3.12.3.
- 128 foreground workers; one thread per worker for BLAS/OpenMP.
- 240 decimal digits for production scan.
- `633,332` distinct deterministic/random values on `10^-8 <= t <= 100`.
- Selected checkpoints at 80, 160, 240, and 480 decimal digits.
- Runtime: about 102 seconds.

Reproduce on a suitable multicore host:

```sh
python3 run_experiments.py --output results --workers 128 --dps 240 \
  --points 250000 --random-points 250000 --series-order 6
python3 verify_results.py
```

## Outcomes

1. **No seam counterexample found.** All `633,332` production values were strictly positive;
   no zero or negative value was reported.

2. **First nonzero displacement term is order five.** If
   `L_k = (d^k/dx^k) log Phi(x)|_(x=0)`, exact symbolic series algebra gives

   `M(t) = c5 t^5 + O(t^7)`,

   `c5 = -(18 L2^3 L6 - 36 L2^2 L4^2 + L2^2 L8
           - 5 L2 L4 L6 + 4 L4^3) / (18 L2^2)`.

   In reflected curvature notation `A=-L2`, `B=-L4`, `C=-L6`, `D=-L8`, its numerator is

   `A^2 D - 18 A^3 C + 36 A^2 B^2 - 5 A B C + 4 B^3`.

   The already formalized reverse velocity law `A C < 2 B^2` contributes the strictly positive
   block `18 A^2 (2 B^2 - A C)`. Thus the old velocity-transport obstruction does not propagate
   to direct C5 transport; it helps its leading seam orientation.

3. **The scalar formula is the actual seam derivative.** At seven selected `t` values,
   `J(u,t)/u` converged quadratically to `M(t)` as `u` decreased from `10^-6` to `10^-18`.
   Relative errors at `u=10^-18` were below `10^-25` in every check.

4. **Low precision manufactures a counterexample.** At `t=50`, 80-digit arithmetic reported a
   negative sign. The 160-, 240-, and 480-digit values agree exactly to the 50 stored digits and
   are positive. At `t=100`, 240 and 480 digits agree. Tail sign searches below about 160 digits
   are not trustworthy for this invariant.

5. **Simple centre monotonicity is false.** At `t=10^-3`, `(J/u)/M` drops from approximately
   `1` near the seam to `0.2523` at `u=0.5`, rises to `0.7827` at `u=1`, `21.2444` at `u=2`,
   and `1.237652e6` at `u=5`, then collapses in the far tail. Therefore neither global
   nondecreasing nor global nonincreasing transport can reduce the two-variable sign to `M(t)`.

## Research consequences

- Direct fixed-action Jacobian route survives its compulsory seam boundary.
- New exact local target is positivity of the displayed eighth-order seam polynomial.
- Best current proof architecture is a three-region split: bivariate local Taylor chamber near
  `(u,t)=(0,0)`, compact middle sign theorem, and first-atom tail estimate.
- Do not revive the naive velocity-current decomposition or any global centre-monotonicity claim.
- Strong next paper task: obtain an exact modular-ODE certificate for the eighth-order seam
  polynomial, then prove `M(t)>0` by local/tail estimates plus a compact analytic inequality.

## Files

- `run_experiments.py`: exact symbolic series, multicore high-precision scan, derivative check,
  and shape attack.
- `results.json`: machine-readable result.
- `run-output.txt`: complete stdout from production run.
- `verify_results.py`: structural result checks.
- `SHA256SUMS`: integrity manifest.
