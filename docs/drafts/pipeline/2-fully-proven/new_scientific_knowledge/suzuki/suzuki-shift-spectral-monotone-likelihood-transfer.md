# Suzuki shift-spectral monotone-likelihood transfer

- **ID:** `suzuki-shift-spectral-monotone-likelihood-transfer`
- **Stage:** 2-fully-proven
- **Type:** SOURCE-SPECTRAL THEOREM / NEGATIVE-STIELTJES PRODUCER
- **Scientific status:** `[PAPER-PROVED] [LEAN CROSS-WRONSKIAN CORE] [CANDIDATE NOVEL APPLICATION] [NOT RH]`
- **Parent:**
  `../../1-in-progress/suzuki-negative-stieltjes-central-flux-colligation.md`
- **RH used:** no
- **Computation used:** no

## Problem closed

The source card conjectures normalized Euler--Gamma shift jet is negative Stieltjes.  Direct
formula is quotient of cross-resolvent matrix elements, not ordinary Donoghue function:

```text
q(lambda)=N(lambda)/D(lambda).
```

Checking `q'<=0`, then every alternating derivative, is not viable source principle.  The theorem
below replaces whole hierarchy by one spectral monotone-likelihood law.

## Theorem A: finite monotone spectral ratios are anti-Pick

Let real nodes satisfy `t_1<...<t_n`, let `w_j>0`, and let responses `r_j` be nondecreasing in
nodes.  Put

```text
D(z)=sum_j w_j/(t_j-z),
N(z)=sum_j w_j*r_j/(t_j-z),
q(z)=N(z)/D(z).
```

`D` has positive imaginary part in upper half-plane, hence never vanishes there.  Direct
symmetrization gives exact diagonal Pick identity

```text
Im q(z)/Im z
 =-[1/(2*|D(z)|^2)]
   sum_(j,k) w_j*w_k*(r_j-r_k)*(t_j-t_k)
   /(|t_j-z|^2*|t_k-z|^2).                            (1)
```

Every summand after minus sign is nonnegative before that sign.  Therefore

```text
Im q(z)<=0,  Im z>0.                                  (2)
```

Thus `q` is anti-Herglotz in shift variable.  Since `D` has one real zero between consecutive
nodes and no nonreal zeros, rational Herglotz partial-fraction theorem yields

```text
q(z)=ell-sum_k nu_k/(sigma_k-z),
nu_k>=0,                                               (3)
```

where `sigma_k` are uncancelled zeros of `D` and
`ell=(sum_j w_j*r_j)/(sum_j w_j)`.  Equation `(3)` is exactly negative-Stieltjes law conjectured
in parent card.  Constant responses produce zero measure, as required.

## Theorem B: measure and real-axis cross-Wronskian form

For positive base measure `mu`, spectral node `t`, and response `r` monovarying with `t`, define

```text
D(lambda)=integral (t-lambda)^(-1) dmu,
N(lambda)=integral r(t)(t-lambda)^(-1) dmu.
```

For `lambda` below support, quotient rule numerator is

```text
N'(lambda)D(lambda)-N(lambda)D'(lambda).               (4)
```

Squared resolvent reweights toward lower nodes.  Exact two-sample identity is

```text
(t_x-lambda)^(-2)(t_y-lambda)^(-1)
 -(t_y-lambda)^(-2)(t_x-lambda)^(-1)
 =(t_y-t_x)/[(t_x-lambda)^2(t_y-lambda)^2].            (5)
```

Multiplying `(5)` by `r(t_y)-r(t_x)` and integrating product measure proves `(4)<=0`.  Same
symmetrization as `(1)` gives anti-Pick property under standard integrability.  If quotient has
finite constant plus `O(1/z)` at infinity and is analytic off `[lambda_a,infinity)`, Herglotz
representation gives negative-Stieltjes measure supported there.

## Exact Suzuki instantiation

At aperture `a`, source card derived

```text
R_lambda=(A_a-lambda)^(-1),
e=e^x,
d=2(1+x),
h=h_a,

D_a(lambda)=<R_lambda e,d>,
N_a(lambda)=<R_lambda e,h>,
q_norm,lambda^EG=N_a(lambda)/D_a(lambda).              (6)
```

For real eigenbasis `A_a phi_j=t_j phi_j`, put

```text
w_j=<e,phi_j><d,phi_j>,
r_j=<h,phi_j>/<d,phi_j>.                               (7)
```

Whenever denominators in `(7)` are nonzero, `(6)` has form of Theorem A exactly.  Therefore
negative-Stieltjes conjecture is discharged by two source-pure spectral statements:

```text
w_j>=0,
(r_j-r_k)*(t_j-t_k)>=0.                                (8)
```

This is stronger and more falsifiable than derivative sign `(S36.9)`.  One violating eigenpair
kills transfer.  If `(8)` holds through compact-resolvent limit with required tightness, resulting
Stieltjes atoms are zeros of `D_a`, with nonnegative residues forced by `(1)`.

## RH frontier after theorem

Theorem closes abstract implication

```text
positive common cross-spectral measure + monotone source response
 -> negative-Stieltjes shift jet.
```

It does not establish actual Suzuki hypotheses `(8)`.  Remaining source work is exact:

1. prove `(8)` from prime--Gamma restricted-Weil operator, or exhibit first violating mode and
   retire Stieltjes route;
2. prove resulting Stieltjes chord mass reaches `ell_a-c_Xi` for one intrinsic nonescaping pair;
3. upgrade central scalar inequality to full normalized jump Pick kernel in spectral variable;
4. invoke existing Xi-pole theorem to conclude RH.

## Hostile tests

- Ground eigenfunction positivity alone does not imply `(8)` for excited modes.
- Positivity-preserving resolvent cannot be assumed; corpus has a breakdown theorem at large
  aperture.
- Ordinary Donoghue measure is in spectral variable `z`, not shift variable `lambda`.
- Near-ground Cayley and far-negative free limits remain forbidden schedules.
- Orbit-inserted FE--Schwarz countermodels must fail `(8)`, mass gap, or full jump kernel before Xi
  divisor identification.

## Formalization

`formal/GaloisForLFunctions/RHTower/SuzukiShiftSpectralMonotoneRatio.lean` proves `(5)`, integrated
cross-Wronskian inequality, and exact quotient-rule nonpositivity from monotone-likelihood kernel.
Complex anti-Pick identity `(1)`, rational partial fractions `(3)`, and concrete eigenvector
instantiation `(7)--(8)` remain paper-level.

## Novelty audit

Monotone-likelihood ordering and ratios of Cauchy transforms are classical.  Candidate novelty is
their exact use on Suzuki Euler--Gamma cross-resolvent quotient, identification of coefficient
laws `(8)` as complete negative-Stieltjes producer, and connection to chord-mass RH threshold.
External priority remains unverified.

## Gates

- [x] finite anti-Pick identity proved
- [x] negative-Stieltjes partial-fraction consequence proved
- [x] measure cross-Wronskian transfer proved
- [x] exact Suzuki eigen-coefficient conditions isolated
- [x] real-axis algebraic core formalized in Lean
- [ ] prove or falsify actual source coefficient laws `(8)`
- [ ] prove chord-mass gap for one source-selected pair
- [ ] prove full normalized jump Pick kernel
- [ ] RH
