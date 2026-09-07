# EDQ completed coprime kernel column: Euler main and decaying error

Stage: formalized in Lean 4; targeted leaf and new-declaration axiom audits passed.
The target remains the complete EDQ signed growth bound and ultimately RH.

For positive m,b, retain the actual kernel K(a,b)=sum_(j>=1)P_b(a*j)/(a*j)^2
and define the completed coprime numerator column

```
C(m,b)=sum_(a>=1, gcd(m,a)=1)mu(a)*K(a,b),
E_alpha(m)=prod_(p|m)(1-p^(-alpha))^(-1).
```

The sum is absolutely convergent: |P_b|<=b/8 bounds its full double series
by a constant times the product of two reciprocal-square sums. Grouping k=a*j
and applying the corpus's complete coprime divisor inversion gives exactly

```
C(m,b)=sum_(k>=1, every prime dividing k divides m) P_b(k)/k^2.
```

This identity retains both the actual Möbius coefficients and every time term.
It is the completed column; restricting a above or below a cutoff changes it.

## Uniform main term

For 0<alpha<1,

```
0 <= C(m,b)+E_1(m)/2 <= E_alpha(m)*b^(alpha-1)/2.
```

Indeed set D_b(k)=P_b(k)+k/2. For b,k>0 the exact residue formula gives
`0<=D_b(k)<=min(k/2,k^2/(2b))`: when k<=b, the second upper bound is an
equality; when k>=b, P_b<=0 supplies it. For the lower bound, k mod b<=k
and P_b(k)>=-(k mod b)/2. Consequently

```
0 <= D_b(k)/k^2 <= min(1/(2k),1/(2b))
                 <= b^(alpha-1)*k^(-alpha)/2.
```

Sum over the exact prime support. Its reciprocal mass is E_1(m), and its
alpha mass is E_alpha(m), by `DeletionCoprimeColumn.hasSum_supportedRpow`.
At squarefree m, the corpus also identifies E_1(m)=m/phi(m).

`exists_supportedEulerMass_le` supplies, for every delta>0, a constant
C_(alpha,delta) with E_alpha(m)<=C_(alpha,delta)*m^delta uniformly in m.
Thus the completed column has a positive error of size
`O_(alpha,delta)(m^delta*b^(alpha-1))` after the explicit Euler main.
No numerical calculation or Möbius cancellation hypothesis enters the proof.

## Effect on the unresolved rectangle

Lean proves the stronger full-rectangle statement: for every epsilon>0,
there is a positive C_epsilon such that, for every natural N,

```
sum_(1<=r,b<=N) |C(r*b,b)+E_1(r*b)/2|/r <= C_epsilon*N^epsilon.
```

Here no coprimality mask or outer Möbius sign is needed. The physical triangle
r*b<=N is contained in this rectangle. To prove the bound, choose
`delta=alpha=min(epsilon/5,1/2)`. The uniform column error gives

```
|C(r*b,b)+E_1(r*b)/2|/r <= A*N^(3*delta)/(r*b).
```

Indeed r,b<=N and b^(delta-1)=b^delta/b. The double harmonic sum is at most
`(1+log N)^2`, which is at most `(1+1/delta)^2*N^(2*delta)` for N>=1.
Finally 5*delta<=epsilon. N=0 is the empty sum. This proof bounds every
column's error absolutely, so no cancellation is discarded in the error estimate.

The numerator tail needed by EDQ is `C(r*b,b)` minus the finite numerator
head a<=floor(N/r). That subtraction still has its actual Möbius signs.
The explicit completed Euler main is not an estimate of that finite head.
In particular, the result does not prove the large-reduced-denominator tail
small, the complete flux ceiling, or RH.

For the following paper consistency check, write M(N)=sum_(n<=N)mu(n) and
H(N)=sum_(n<=N)mu(n)/n; H here is the signed reciprocal Möbius sum.
Summing the Euler mains over coprime r,b
with r*b<=N gives -M(N)/2: at each squarefree prime the two allocations have
coefficients 1/(p-1) and -p/(p-1), whose sum is -1. Completing all columns
already gives -(M(N)-H(N))/2, so the complete signed sum of their errors is
exactly H(N)/2. This cancellation does not control the retained finite head.

## Lean declarations and validation

Module: `GaloisForLFunctions.RHTower.EulerDeletionCompletedColumnMain`.
Namespace: `RHTower.DeletionFlux`.

- `coprimeKernelColumn_eq_supported`: exact absolutely convergent source identity.
- `coprimeKernelColumn_main_bounds`: positive error and its decaying bound.
- `exists_coprimeKernelColumn_error_bound`: uniform subpower modulus cost.
- `kernelEulerMass_one_eq_totientRatio`: Euler main at squarefree moduli.
- `exists_completedColumnErrorMass_subpower`: full-rectangle absolute error bound,
  including the empty N=0 case.

The scratch check passed without warnings. The final command was
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionCompletedColumnMain`;
the new leaf built in 12 seconds. Dependencies were replayed, and the new leaf
was the only own-project olean modified in the audit window. All eight new
public declarations, including the three definitions, were axiom-audited from
an external scratch file: only `propext`, `Classical.choice`, and `Quot.sound`.
No numerical input or added axiom enters the proofs. The module is wired into
`RHTower.lean`; no umbrella build was run.

The exact reduced-coordinate identification of the full reciprocal flux, the
finite-head estimate, and the consistency-check Euler-main summation above
are not claimed as new Lean theorems. RH remains unresolved.

Integration check: `scripts/formal_tools.py index` refreshed the generated
indexes once. `scripts/formal_tools.py lint` reported one unrelated wiring
failure for the concurrently added `RHTower.LorentzianComplexShiftProduct`;
the new EDQ module is reachable from its umbrella. That foreign module was
not modified. Scratch files were removed and no owned Lean/Lake process
remained. This task made no frontier-map edit; concurrent changes to that
file were preserved.
