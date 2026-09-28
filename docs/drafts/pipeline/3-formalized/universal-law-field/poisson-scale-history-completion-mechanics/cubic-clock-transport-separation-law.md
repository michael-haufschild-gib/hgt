# Clock cubing and transport differentiation are different operations

- **Stage:** 3-formalized

- ID: ULF-CTRS-001
- Status: `[PAPER-PROVED] [BRIDGE] [LEAN-PROVED] [NOT RH]`.
- Parent: ULF-CDMA-001, auditing ULF-CCEL-001 / ULF-PHCCED-001.
- Exact significance: distinguishes two proposed cubic mechanisms and proves recovery of the
  ordinary positive-clock splitting problem, with its full trace-class correction set retained.
- Lean: formalized; see the Lean certificate below.

## 1. Algebra and the transport jet

Let `X,E` be finite-dimensional complex vector spaces, `A:E->E`, `B:X->X`, and `F:X->E` linear.
On `Hom(X,E)` put `L(F)=AF`, `R(F)=FB`, and `delta=L-R`. Associativity gives `LR=RL`.
Define `omega_1=delta F` and `omega_pow3=A^3F-FB^3`. Then

```text
omega_pow3=(L^2+LR+R^2)omega_1,                              (1)
J_3=delta^3F=(L^2-2LR+R^2)omega_1,                         (2)
omega_pow3-J_3=3A omega_1 B.                                (3)
```

Proof: expand each product, cancel adjacent terms, and use `LR=RL`. The function
`F(u)=exp(uA)F exp(-uB)` satisfies `F'(u)=delta F(u)`. Differentiating three times proves
`F'''(0)=J_3`. All functions are entire matrix functions, so no domain or convergence interchange
is involved. Equations (1)--(3) also hold algebraically for arbitrary linear maps; their
identification with a derivative in infinite dimensions requires a separately justified orbit.

For the unipotent clock `A(v,w)=(v+w,w)`, `B=id`, `F_h(z)=(hz,z)`, write `A=1+N` with `N^2=0`.
Then `omega_1(z)=(z,0)`, `omega_pow3(z)=(3z,0)`, whereas
`exp(uA)F_h exp(-uB)(z)=((h+u)z,z)` and `J_3=0`. This is the exact example in CCEL.
In the other direction, `A=omega id`, `B=id`, `F=id`, for `omega^3=1`, `omega!=1`, gives
`omega_pow3=0`, `J_3=(omega-1)^3 id !=0`. Thus neither expression determines the other without
extra clock information.

For a quotient `q:E->Q` intertwining `A` and `A_Q`, the correct quotient condition for the
transport third jet to land in `ker q` is `(L_{A_Q}-R_B)^3(qF)=0`.
The condition `A_Q^3(qF)=(qF)B^3` alone is insufficient, as the scalar example with `q=id` shows.

## 2. Exact splitting corrections for positive finite clocks

Let `I=C^r`, `X=C^s`, with diagonal clocks `A=diag(a_i)`, `B=diag(b_j)`, all `a_i,b_j>0`.
For any matrix `K:X->I`, put

```text
D_E = [ A K ],       f=id_X,       F_0(x)=(0,x).
      [ 0 B ]
```

The first extension defect of `F_0` is `K`; multiplying the block matrices shows its powered-clock
defect is `K_3=A^2K+AKB+KB^2`. Every lift is `F_H(x)=(Hx,x)`. Its first defect is `K+AH-HB`;
its powered-clock defect is `K_3+A^3H-HB^3`. For every pair of indices,

```text
m_ij=a_i^2+a_i b_j+b_j^2>0,
(K_3+A^3H-HB^3)_ij=m_ij (K+AH-HB)_ij.                     (4)
```

Consequently the two defects vanish for exactly the same matrices `H`. This includes resonance
`a_i=b_j`: both require `K_ij=0`, and the multiplier is `3a_i^2`, never zero.
Equivalently, the Schur map `M(Y)_ij=m_ij Y_ij` is an invertible map carrying the first
coboundary range to the powered-clock coboundary range and the first extension class to the
powered-clock class. It induces an isomorphism of their cokernels. This is a positive-clock
statement; the complex cube-root example explains why positivity cannot be omitted here.

## 3. Countable trace-class recovery with a sharp bound

Let `I,J` be finite or countable sets, `a_i,b_j>=c>0`, and let `S1(J,I)` denote trace-class
operators `ell2(J)->ell2(I)`. There is a bounded coefficient-preserving map

```text
R:S1(J,I)->S1(J,I),    (RY)_ij=Y_ij/(a_i^2+a_i b_j+b_j^2),
||R Y||_1 <= (3c^2)^(-1)||Y||_1.                            (5)
```

The constant is sharp across this class, attained when `I=J={1}` and `a_1=b_1=c`.

Here is a complete construction without assuming that arbitrary bounded Schur symbols act on
trace class. Define

```text
kappa = (integral_0^infinity t^(-2/3)/(1+t) dt)^(-1)>0.
```

The integral is finite: at zero compare with `t^(-2/3)`, at infinity with `t^(-5/3)`.
Substitution `t=xu` proves for `x>0`

```text
x^(1/3)=kappa integral_0^infinity t^(-2/3) x/(x+t) dt.
```

Subtract the formulas at `x,y>0`, divide by `x-y`, and simplify. For `x=y`, differentiate under
the integral; on a compact positive interval the derivative is dominated by a constant times
`t^(1/3)/(d+t)^2`, which is integrable. Taking `x=a^3,y=b^3` gives

```text
1/(a^2+ab+b^2)
  = kappa integral_0^infinity t^(1/3)/((a^3+t)(b^3+t)) dt.   (6)
```

This includes `a=b`, where the value is `1/(3a^2)`.
Let `R_A(t)=diag((a_i^3+t)^(-1))`, `R_B(t)=diag((b_j^3+t)^(-1))`. Their operator norms are at
most `(c^3+t)^(-1)`. Define the Bochner integral in `S1(J,I)`

```text
R(Y)=kappa integral_0^infinity t^(1/3) R_A(t) Y R_B(t) dt.    (7)
```

Resolvent identities make the integrand norm-continuous for `t>0`. The ideal inequality bounds
its trace norm by `t^(1/3)(c^3+t)^(-2)||Y||_1`. Formula (6) at `a=b=c` proves integrability and
(5). Each matrix-coordinate functional is continuous on trace class, so applying it to (7)
and then (6) gives the asserted entries. This proves existence, the exact bound, and retention
of every coefficient. Uniqueness follows because matrix entries determine a bounded operator.
The same proof works in operator norm and in any Schatten norm; only trace class is needed here.

## 4. Cofinal correction-set rigidity on maximal coefficient domains

For `H` in `S1(J,I)`, define the first and powered-clock defects entrywise:

```text
(delta_1 H)_ij=(a_i-b_j)H_ij,
(delta_pow3 H)_ij=(a_i^3-b_j^3)H_ij.
```

Their maximal trace-class domains consist of the `H` for which these arrays are entries of a
trace-class operator. No assertion about compositions of unbounded operators is built into this
definition. Let `K_3` be any trace-class matrix and `K_1=R(K_3)`. Then

```text
{H in Dom_max(delta_pow3): K_3+delta_pow3 H=0}
  = {H in Dom_max(delta_1): K_1+delta_1 H=0}.                (8)
```

Proof: factor `a_i^3-b_j^3=(a_i-b_j)m_ij`. If either equation holds, division or multiplication
by nonzero `m_ij` proves the other entrywise. The other defect equals `-K_1` or `-K_3`, already
trace class; hence the required domain membership follows rather than being assumed. Equality
of all matrix entries gives equality of the operators. No uniform lower bound on `|a_i-b_j|`
is used, so cofinal near-resonances do not invalidate (8).

This result also identifies the exact limitation: replacing maximal coefficient domains by
smaller physically imposed graph domains may alter the correction set. Proving that such a
smaller domain is forced by literal theta completion is additional mathematics. Formula (8)
does not authorize enlarging that domain or erasing its boundary conditions.

The forward multiplier `M` need not preserve trace class. For example `a_i=b_i=i` and
`K_1=diag(i^-2)` give `M K_1=3 id`, which is not trace class on an infinite index set.
Thus (5) is one-way regularity recovery; it is not an isomorphism of all of `S1` under `M`.
Equation (8), with `K_3` trace class, is the exact stronger conclusion that survives.

## 5. Interpretation and hostile review

For prime or prime-depth positive clocks the lower bound `c=log 2` is available. This does not
identify the completed theta clock with a positive diagonal clock, nor identify any arithmetic
source with `K_3`. It only rules out gaining a new splitting selector by cubing such clocks once
the same coefficient domains and defect are fixed.

Checks: unequal and resonant clocks; complex cube-root counterexample; unipotent extension;
unbounded positive clocks; arbitrarily small spectral differences; forward trace-class failure;
sharp lower-bound constant; exact correction witnesses rather than only equal dimensions.
None uses a zero, RH, a new axiom, or a postulated arithmetic landing.

Parent theory is ordinary commuting left/right multiplication and the cube-root divided
difference; see [operator-monotone integral representations](https://arxiv.org/html/1305.2471v1).
This is a dependency-closed paper bridge and a correction to the proposed interpretation, not
accepted AI proof, a new universal theory, or an RH implication. Its precise Lean formalization
remains pending under the current read-only instruction.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CubicClockTransportJet`, `GaloisForLFunctions.HTGeometry.PositiveClockExtensionSplitting`, `GaloisForLFunctions.HTGeometry.CubeRootDividedDifferenceIntegral`, `GaloisForLFunctions.HTGeometry.TraceClassClockSchurRecovery`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.CubicClockTransportJet` (36 constants), `GaloisForLFunctions.HTGeometry.PositiveClockExtensionSplitting` (29), `GaloisForLFunctions.HTGeometry.CubeRootDividedDifferenceIntegral` (24), `GaloisForLFunctions.HTGeometry.TraceClassClockSchurRecovery` (117); axiom audit clean.

| Claim | Lean declaration |
|-|-|
| §1 `δ = L - R`, `ω₁ = δF`, `ω₃ = A³F - FB³`, `J₃ = δ³F` | `clockTransport`, `clockTransportCLM`, `clockCubeDefect`, `clockTransportJet3` |
| §1 (1) `ω₃ = (L² + LR + R²) ω₁` | `clockCubeDefect_eq` |
| §1 (2) `J₃ = (L² - 2LR + R²) ω₁` | `clockTransportJet3_eq` |
| §1 (3) `ω₃ - J₃ = 3 A ω₁ B` | `clockCubeDefect_sub_jet3` |
| §1 orbit `F(u) = exp(uA) F exp(-uB)`, `F' = δF`, `F'''(0) = J₃` | `clockTransportOrbit`, `clockTransportOrbit_zero`, `hasDerivAt_clockTransportOrbit`, `deriv_clockTransportOrbit`, `iteratedDeriv_three_clockTransportOrbit` |
| §1 unipotent clock: `ω₁(z) = (z,0)`, `ω₃(z) = (3z,0)`, orbit `((h+u)z, z)`, `J₃ = 0` | `unipotentClock`, `unipotentLift`, `unipotent_clockTransport`, `unipotent_clockCubeDefect`, `unipotent_clockTransportOrbit`, `unipotent_clockTransportJet3`, `unipotent_cube_ne_zero_jet_eq_zero`, `exp_smul_of_mul_self_eq_zero` |
| §1 cube root `ω`: `ω₃ = 0`, `J₃ = (ω-1)³ ≠ 0` | `cubeRoot_cube_eq_zero_jet_ne_zero`, `exists_cubeRoot_ne_one` |
| §1 quotient: `J₃ ∈ ker q` iff `(L_{A_Q} - R_B)³(qF) = 0`; the powered condition alone is insufficient | `comp_clockTransportJet3`, `clockTransportJet3_mem_ker_iff`, `cube_condition_not_sufficient` |
| §2 extension clock, lifts, first defect of `F_0` is `K`, powered defect `K₃ = A²K + AKB + KB²` | `extensionClock`, `extensionLift`, `cubeCoupling`, `extensionClock_pow_three`, `extensionClock_lift_defect`, `extensionClock_cube_lift_defect`, `extensionClock_zero_lift_defects` |
| §2 (4) entrywise `m_ij` identity, `m_ij > 0`, resonance `3a²` | `cubeDefect_entry`, `clockCubeMultiplier`, `clockCubeMultiplier_ne_zero`, `clockCubeMultiplier_self`, `cube_sub_cube_eq_multiplier` |
| §2 same vanishing lifts | `cubeDefect_eq_zero_iff` |
| §2 Schur map invertible, carries coboundary range and class, cokernel isomorphism | `clockCoboundary`, `clockSchurEquiv`, `clockSchurEquiv_comp_coboundary`, `clockSchurEquiv_coupling`, `map_range_clockCoboundary`, `clockCokernelEquiv`, `clockCokernelEquiv_mk` |
| §2 positivity cannot be omitted (cube root) | `cubeRoot_splitting_counterexample` |
| §3 `κ` finite and positive; `x^{1/3} = κ ∫ t^{-2/3} x/(x+t) dt` | `cubeRootKernelMass`, `cubeRootKernelMass_pos`, `cubeRootKappa`, `cubeRootKappa_pos`, `integrableOn_cubeRootKernel`, `integral_rpow_mul_div_add`, `rpow_third_eq_kappa_mul_integral` |
| §3 divided difference and (6) `1/(a²+ab+b²) = κ ∫ t^{1/3}/((a³+t)(b³+t))`, including `a = b` | `rpow_third_sub_eq`, `continuousAt_integral_cubeRootDividedKernel`, `one_div_sq_add_mul_add_sq_eq`, `one_div_three_mul_sq_eq` |
| §3 (7) Bochner integral in trace class; resolvent norms `≤ (c³+t)⁻¹`; ideal inequality; norm continuity | `PositiveClock`, `PositiveClock.resolvent`, `PositiveClock.norm_resolvent_le`, `PositiveClock.continuous_resolvent`, `schattenSandwich`, `traceNorm_sandwich_le`, `schurIntegrand`, `continuousOn_schurIntegrand`, `integrableOn_schurIntegrand`, `clockSchurRecovery` |
| §3 (5) `‖RY‖₁ ≤ (3c²)⁻¹‖Y‖₁` and entries `Y_ij / m_ij` (square) | `norm_clockSchurRecovery_le`, `ellTwoEntry_clockSchurRecovery` |
| §3 `R : S₁(J,I) → S₁(J,I)` rectangular: trace class, bound (5), coefficients, uniqueness, linearity | `rectClockSchurRecovery`, `PositiveClockPair`, `rectClockSchurRecovery_law`, `memRectSchattenClass_rectClockSchurRecovery`, `rectTraceNorm_rectClockSchurRecovery_le`, `ellTwoEntry_rectClockSchurRecovery`, `eq_rectClockSchurRecovery_of_entries`, `ellTwoEntry_ext`, `rectClockSchurRecovery_add`, `rectClockSchurRecovery_smul` |
| §3 sharpness at `I = J = {1}`, `a = b = c` | `rectClockSchurRecovery_bound_sharp` |
| §4 (8) correction-set equality on maximal trace-class coefficient domains | `correctionSet_eq`, `memRectSchattenClass_one_neg` |
| §4 forward multiplier fails trace class (`a_i = b_i = i`, `K₁ = diag(i⁻²)`, `M K₁ = 3·id`) | `forwardMultiplier_not_traceClass` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
