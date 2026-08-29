# S6F thin-clock-cone hostile test

## Question

Does exact ODE-motivated restriction

`2/5 <= y = v/z <= 1/2`

turn S6F normalized projective-drift certificate into materially smaller sign problem? Does
positivity persist for full scale half-ray `X >= 191/10`, eliminating previously assumed upper
bound `X <= 20`?

Diagnostic only. No coefficient, sign table, or numerical output here is admissible in Lean.

## Computation

Reconstructed literal source-positive projective drift, transformed it exactly to

`projectiveDrift / R = z * C(X,z,y)`.

Used six RunPod worker processes. On thin box substituted

`X = 191/10 + (9/10)S`, `z = (3/10)T`, `y = 2/5 + (1/10)Y`.

Computed exact tensor-Bernstein signs for `C`, first partials, and `-d²C/dY²`. For half-ray,
substituted `X = 191/10 + S`, expanded in power basis `S >= 0`, and independently converted every
coefficient polynomial to tensor-Bernstein basis in `(T,Y)`. Separate verifier reconstructs all
polynomials and Bernstein tables with independent conversion code and checks hashes.

## Outcome

- Direct `y` monotonicity remains false: both `dC/dY` and `-dC/dY` have negative Bernstein
  coefficients.
- `C` is concave in `y` on thin cone: all 9,828 Bernstein coefficients of `-d²C/dY²` are
  nonnegative (728 zero).
- Stronger result: on entire half-ray `X >= 191/10`, all 10,584 hybrid power/Bernstein
  coefficients of `C` are strictly positive.
- On same half-ray, `dC/dX` is strictly positive, `-dC/dz` is nonnegative, and `-d²C/dy²` is
  nonnegative.
- Both fixed `y` walls have 378 strictly positive hybrid coefficients.
- Exact clock-wall vector-field numerators simplify to
  - lower wall: `3*(9*X*z^2 - 5*X + 100)/100`;
  - upper wall: `(4*X*z^2 - 3*X + 36)/12` for derivative of `v-z/2`.
- Independent exact verifier passed.

## Interpretation

Previous `X <= 20` localization is unnecessary for S6F if actual orbit is placed in thin clock
cone. Computation suggests sharpened route:

1. prove actual ODE orbit satisfies `2z/5 < v < z/2` on missing interval;
2. independently prove `C > 0` on simple semialgebraic half-cone
   `X >= 191/10`, `0 < z < 3/10`, `2/5 < y < 1/2`;
3. use existing projective derivative bridge and seam positivity.

Step 1 has since been independently derived and formalized without computational input. Step 2
remains open: copying hybrid coefficient certificate into Lean is forbidden. Concavity provides
fallback paper route reducing `y` direction to two wall polynomials.
