# Route L: original regulator--depth crossover

- **ID:** L-C29
- **Date:** 2026-09-11
- **Stage:** 3-formalized; targeted build, complete axiom audit and global lint passed
- **Type:** THEOREM (paper and Lean); 25 theorems audited
- **Depends on:** [C28 complete integrand admission](route-l-complete-integrand-admission.md)
- **Lean:** `GaloisForLFunctions.RHTower.DeningerGammaSixRegulatorDepthCrossover`
- **RH status:** unproved; no source-to-fixed-reader agreement supplied

## Exact source and conclusions

Keep the original spectral point `w`, internal orders `k,l`, ordinary
coordinates `a=n+216`, fixed dilation six, and C28's actual tail operator
`T_M=E_(6^M)*(T_kl(w,w)-c*Q)`. Here

`c=XiC^(k)(w)*XiC^(l)(w)`,
`N_M=mobiusThetaSuccessorSpectralNormalizer(6,M,s(w))`,
`q=N_1^(-1)`, `A=2*mu(successor(6))`, `B=log(6)/6`,
`K=log(6)*c*(1-q)^(-1)*A*B`.

Assume only the source admission region `|Im(w)|<1`, `Re(s(w))>0`.
Every original Xi divisor satisfies these inequalities by existing
unconditional theorems; no reflection or horizontal relocation is used.
For a sequence of eventually positive regulators `epsilon_M -> 0`, put

`D_M=N_M*AbelDefect(epsilon_M,6,T_M)/epsilon_M^2`,
`b_M=6^(-M*epsilon_M)`.

The strongest asymptotic statement is

`D_M/b_M -> K`.

This explicitly different diagnostic normalization is not a replacement
for the fixed reader. It determines the original reader's regimes:

- If `M*epsilon_M -> tau` is finite, then `D_M -> 6^(-tau)*K`.
- If `M*epsilon_M -> +infinity`, then `D_M -> 0`.
- At every original multiplicity-top Xi jet, `K` and every finite-product
  limit are nonzero. The actual unnormalized top defect is nonzero at
  every sufficiently late depth along every such regulator path,
  including the infinite-product regime.
- The adjacent lower/top internal jets give an exact zero/nonzero pair
  of actual regulated defects at every sufficiently late depth.
- Any repair with finite ordinary diagonal support disappears from the
  literal defect at sufficiently late cutoffs, uniformly over regulators
  and ordinary dilations. It therefore preserves the finite-product
  crossover. This is not a finite-rank repair theorem.

A vanishing joint limiting measurement can therefore coexist with a
retained nonzero source conormal pair. Critical top sources satisfy the
same retention law. These statements do not select the critical line.

## Dependency-closed paper proof

### 1. Regulate the complete admitted source before integrating

Multiply C28's original masked integrand by `a^(-epsilon)` and the
ordinary divisibility indicator `6 divides a`. For `epsilon>=0` and
`a=n+216`, the weight has modulus at most one. Thus C28's summable
integrated-norm majorant still bounds all original regulated integrands.
Every regulated integrand is integrable; their complete pointwise sum
is integrable, and its integral equals the sum of the integrals.
No unadmitted early-depth integral enters this interchange.

At a sufficiently late cutoff, the mask is exactly `a>=6^M`, and each
regulated term is the integral of this same source. The actual projected
Gibbs trace equals the integral of the complete regulated source sum.
This supplies the operator bridge, rather than assuming a shell model.

### 2. Exact shell factor and uniform bounds

For literal shell depth `m`, define

`H_m(epsilon)=sum_(6^m<=a<6^(m+1),6 divides a) a^(-epsilon)/a`,
`G_m(epsilon)=sum_(same a) (a/6^m)^(-epsilon)/a`.

Real-power multiplication gives the exact identity

`H_m(epsilon)=6^(-m*epsilon)*G_m(epsilon)`.

Since every shell ratio lies in `[1,6]`, for nonnegative epsilon,

`6^(-epsilon)*H_m(0) <= G_m(epsilon) <= H_m(0)`.

C27 proves `H_m(0)->B`. These masses form a bounded sequence. Therefore
`G_m(epsilon)` has one uniform bound for `m>=1`, `epsilon>=0`, and the
sandwich gives `G_(d_M)(epsilon_M)->B` whenever `d_M->infinity` and
`epsilon_M->0`. Every original integer coordinate and its divisibility
condition remain in these sums.

### 3. Exact actual-operator factorization

The source-derived summable diagonal admits `T_M` into its actual Gibbs
domain. Compression minus projection gives

`AbelDefect(epsilon,6,T_M)/epsilon^2`
`= [(6^epsilon-1)/epsilon] * [1/(epsilon*Z_epsilon)]`
`  * sum_(6 divides a) a^(-epsilon)*diag(T_M)(a)`.

The gain is `6^epsilon-1`, and `Z_epsilon` is the original partition at
`(1+epsilon)/2`. Both are retained. On each admitted original coordinate,
`diag(T_M)(a)=c*C_m/a`, where `C_m` is the full tensor remainder
multiplier. Absolute summability permits exact fibre regrouping by
`m=M+j`; the finite shell shift retains `n+216` and its original cutoff.

Use `q^j*N_(M+j)=N_M` and the shell factor to obtain

`D_M=[(6^epsilon_M-1)/epsilon_M] * [1/(epsilon_M*Z_epsilon_M)]`
`    * c*b_M*S_M`,

where

`S_M=sum_j q^j*6^(-j*epsilon_M)*[N_(M+j)*C_(M+j)]*G_(M+j)(epsilon_M)`.

This is an identity for the actual operator after its complete source
admission, not a limiting identification of different readers.

### 4. Moving-array convergence and the coupled regimes

The actual normalized multiplier sequence `N_m*C_m` tends to `A`, hence
has a uniform norm bound. Also `|q|<1` throughout the positive source
chamber, `|6^(-j*epsilon_M)|<=1`, and the shell masses have the uniform
bound above. Their product is dominated by a fixed summable geometric
sequence in `j`. Each fixed-`j` term tends to `q^j*A*B`, so dominated
summation gives

`S_M -> (1-q)^(-1)*A*B`.

The existing actual Gibbs partition residue is
`epsilon*Z_epsilon -> 1`, and the actual gain slope tends to `log(6)`.
Since `b_M` is always strictly positive, exact cancellation in the
factorization proves `D_M/b_M -> K` without an assumption on the limit
of `M*epsilon_M`.

For finite product limit tau, continuity gives `b_M->6^(-tau)`.
For infinite product, the real-power limit gives `b_M->0`. Multiplying
these limits with the convergent remaining factors proves both regimes.
No order of limits is silently exchanged.

### 5. Original Xi jets and finite repairs

At multiplicity `r`, the original derivative `XiC^(r)(w)` is nonzero,
while `XiC^(r-1)(w)=0`. The existing exact nonzero constant theorem
therefore gives `K(r,r,w)!=0`. Convergence of `D_M/b_M` implies eventual
nonvanishing of the actual top defect: an exact zero defect would make
this quotient zero. The adjacent lower source has `c=0`; the exact
factorization, nonzero normalizer, and positive regulator give an exact
zero lower defect. This proves the retained conormal pair without a
finite-product assumption.

The Abel reader, its compression and its divisibility projection depend
only on the original diagonal. A finite diagonal support lies below
`6^M` for every sufficiently late M. The original cutoff consequently
removes that repair's diagonal from all three expressions. This yields
pointwise equality of literal defects for every regulator and dilation,
before any limits, and hence the stated repair invariance.

## Formal audit

`lake env lean /tmp/route_l_regulator_depth_crossover.lean` completed
successfully without errors or warnings for all 25 theorems and five
definitions. The finished module is wired into `RHTower`.

`lake build GaloisForLFunctions.RHTower.DeningerGammaSixRegulatorDepthCrossover`
completed successfully; the new module built in 15 seconds. Existing
dependency messages were replayed. No full or umbrella build was run.

`lake env lean /tmp/route_l_crossover_axioms.lean` completed successfully.
Every one of the 25 source theorem names matched its printed axiom
entry; only `propext`, `Classical.choice`, and `Quot.sound` occur. The
new module contains no `sorry`, `admit`, added `axiom`, `opaque`,
`unsafe`, `#eval`, or `native_decide`. All owned Lean processes have
completed. `scripts/formal_tools.py lint` completed with exit status zero
and `formal lint passed`; remaining diagnostics are repository warnings.
The previous unrelated reachability errors are cleared. No full or
umbrella build was run.

## Search, failed transfers, and positive survivor

Two deep/method searches were inspected, each with 20 candidate
statements and 20 source-method arguments. The latest coverage was
partial: generation `823349`, semantic `2196271/2337170`, 56,615 files,
56,021 inventoried, and 523 pending/stale files. Refresh was deferred at
its deadline. Suggested modified-Hurwitz/cutoff-exponent and geometric-
tail/exponential-decay ingredient sets provide useful bounds but do not
preserve this source's coupled normalizer or identify a fixed reader.
Those proposed transfers were rejected. Current-corpus dominated
summation, exact real-power identities, and the actual C25--C28 source
and operator theorems instead discharge the proof.

Broad recent searches for adiabatic, resonance, homogenization and
dilation mechanisms returned the July [dressed-frame counterdiabatic
paper](https://arxiv.org/html/2607.28383v1), September [Fuchsian resonance
connection paper](https://arxiv.org/html/2609.00942v1), and July
[automorphic Nelson dilation paper](https://arxiv.org/abs/2607.14372).
The inspected constructions respectively change an effective generator,
continue the same analytic ODE solution into an independently fixed
boundary basis, and dilate an already strictly contractive matrix. They
do not supply this source's fixed-reader agreement. Actual generator
transport, common-source continuation with a nonzero boundary
Wronskian, or contractivity would remain separate obligations. No such
external hypothesis is imported.

The positive survivor is the exact original-operator attenuation law,
complete regulated source identity, and persistence of the actual
conormal pair even when a joint measurement tends to zero. Regulator
suppression alone cannot supply source annihilation. The remaining RH
obstacle is an independently derived source-to-fixed-Burnol/Deninger
comparison at the original anchor, with arithmetic actions, prime,
depth, multiplicity and nonzero internal coefficient retained.
