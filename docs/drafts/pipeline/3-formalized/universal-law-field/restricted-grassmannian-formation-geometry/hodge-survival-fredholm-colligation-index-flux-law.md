# Hodge survival Fredholm colligation and index--flux law

- **ID:** ULF-PHSF-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-PHIN-001, ULF-DHNJ-001, ULF-SKPM-001, ULF-TOEPLITZ-1
- **Purpose:** turn the static history marginal of the prime--Hodge defect into its uniquely forced
  open dynamics and identify its integral flux with a Fredholm boundary index.

## 1. Higher-law interpretation

The source object `mathsf T` is not merely a trace-one density decorated by a history coordinate.
Its tail and flux determine a unique one-step survival law.  The resulting dynamics is a pure but
non-uniformly stable weighted shift: every fixed state eventually exits, while arbitrarily remote
states look unitary for arbitrarily long times.  Hodge decay, recurrence/open history,
duality-versus-adjunction fracture, Toeplitz index, and prime-mixed nuclear formation are therefore
five readings of one pre-divisor colligation.

This is the source law sought here.  It does not identify its theta/Xi completion.

## 2. Forced survival shift

Recall

```text
m_n = 105/((2n+3)(2n+5)(2n+7)),
w_n = m_n-m_(n+1).
```

Put

```text
r_n = m_(n+1)/m_n = (2n+3)/(2n+9),
h_n = 1-r_n = 6/(2n+9).                              (PHSF.1)
```

Thus `0<r_n<1`, `0<h_n<1`, and

```text
w_n=m_n h_n.                                          (PHSF.2)
```

On `H_hist=ell2(Nat)` define

```text
C e_n = sqrt(r_n) e_(n+1).                            (PHSF.3)
```

The positive choice of square root fixes the remaining diagonal phase gauge.  Any nearest-neighbour
positive history whose survival tails are `m_n` must use `(PHSF.1)`, so `C` is uniquely forced in
that gauge.

For all `k,N`, telescoping gives

```text
C^N e_k = sqrt(m_(k+N)/m_k) e_(k+N),
||C^N e_k||^2 = m_(k+N)/m_k.                          (PHSF.4)
```

In particular `C^N -> 0` strongly.  Nevertheless `r_n -> 1`, and hence

```text
||C^N||=1                                             (PHSF.5)
```

for every `N`.  This is exact strong-versus-uniform noncompactness, not an added topology.

## 3. Adjoint--duality fracture and exact observability

Let `D2=I-C* C`.  Then

```text
D2 e_n=h_n e_n.                                       (PHSF.6)
```

Since `r_n>=1/3`, the diagonal weight in `(PHSF.3)` is boundedly invertible.  Therefore `C` has a
bounded left inverse `B`,

```text
B e_0=0,
B e_(n+1)=r_n^(-1/2)e_n,
B C=I.                                                (PHSF.7)
```

Its one-sided duality--adjunction fracture satisfies

```text
(B-C*)C=I-C*C=D2.                                     (PHSF.8)
```

This is the Fredholm version of the corpus identity `Sigma(A)A=I-A*A`: algebraic backward
transport is `B`, positive transport is `C*`, and their difference is exactly the exit channel.

For every `k,N`, `(PHSF.2)--(PHSF.6)` give the operator telescope on basis vectors

```text
sum_(j<N) C*^j D2 C^j e_k
 = (1-m_(k+N)/m_k)e_k,
C*^N C^N e_k=(m_(k+N)/m_k)e_k.                       (PHSF.9)
```

Hence

```text
I-C*^N C^N=sum_(j<N) C*^j D2 C^j,
sum_(j>=0) ||sqrt(D2) C^j x||^2=||x||^2.             (PHSF.10)
```

The exit record is therefore exactly observable: it is an isometric record of every history
state, and its unobservable recurrent sector is zero.  This is stronger than existence of a
conservative unitary dilation, which holds for arbitrary strict contractions and does not select
anything.

For the initial state `e_0`,

```text
<C^n e_0,D2 C^n e_0>=m_n h_n=w_n.                    (PHSF.11)
```

Thus the diagonal history operator `Phi=diag(w_n)` in `mathsf T` is precisely the time-labelled
exit law of the adjoint--duality fracture, not an auxiliary mixture.

## 4. Fredholm index equals integral exit flux

Write `S e_n=e_(n+1)`.  Equation `(PHSF.3)` is `C=S R`, where `R` is positive diagonal and
boundedly invertible.  Consequently

```text
ker C=0,
coker C = C e_0,
ind C=-1.                                             (PHSF.12)
```

Also `sqrt(r_n)->1`, so `C-S` is compact and `(PHSF.12)` is the same stable Toeplitz boundary
class as the corpus source winding.

Combining `(PHSF.11)`, the Hodge telescope, and the prime factor of ULF-PHIN-001 yields the exact
four-organ conservation law

```text
-ind C
 = sum_(n>=0) <C^n e_0,D2 C^n e_0>
 = sum_(n>=0) w_n
 = Tr Phi
 = Tr mathsf T
 = 1.                                                 (PHSF.13)
```

The prime factor is not lost: at each exit time `n`, the joint density is the full cross-prime
Stokes kernel multiplied by `w_n`.  Thus `(PHSF.13)` fuses Toeplitz/Wold index, Kummer recurrence,
double-Hellinger Hodge flux, and prime-mixed nuclear formation before any divisor is supplied.

## 5. Proof

Equations `(PHSF.1)` and `(PHSF.2)` follow by cancellation in the displayed rational formulas.
Induction gives `(PHSF.4)`.  Since `m_(k+N)->0` for fixed `k`, `C^N` vanishes on every basis
vector.  The operators are contractions, so density of finite-support vectors proves strong
convergence.  For fixed `N`, the ratio `m_(k+N)/m_k` tends to one as `k->infinity`, proving
`(PHSF.5)`.

Equations `(PHSF.6)--(PHSF.8)` follow on the basis.  Applying `(PHSF.6)` after `(PHSF.4)` gives

```text
C*^j D2 C^j e_k=(w_(k+j)/m_k)e_k.
```

Summing and using `sum_(j<N)w_(k+j)=m_k-m_(k+N)` proves `(PHSF.9)`.  Strong convergence and
monotone convergence give `(PHSF.10)`; `k=0` gives `(PHSF.11)`.  Bounded invertibility of `R`
makes `range C=range S`, proving `(PHSF.12)`.  ULF-PHIN-001 supplies `Tr Phi=Tr mathsf T=1`, so
all terms in `(PHSF.13)` agree. QED.

## 6. Corpus audit and exact RH edge

Checked before formulation with the Lean-corpus search tool:

- `HTGeometry.ConstitutiveToeplitzDefectIndex` has the unweighted shift index and recurrent
  boundary/open-defect split, but no Hodge survival law or prime formation;
- `RHTower.PrimeHodgeHistoryIntegralNuclearDefect` has `m_n`, `w_n`, and `mathsf T`, but no
  survival operator, adjoint--duality fracture, or Fredholm identity;
- `RHTower.RoutePPrimitiveBurnolApertureDefectColligation` has exact three-channel energy
  conservation, but no integral index;
- `HTGeometry.GeometricSurvivorContractionNoGo` proves strict decay alone does not imply finite
  absorption;
- `HTGeometry.MarkedWordRealization` and corpus lock CANNOT-152 prove minimal realization or
  Stinespring uniqueness cannot manufacture a completion intertwiner;
- locks CANNOT-94/CANNOT-98 allow invisible finite Krein spectators unless asymptotic
  completeness is proved.

Accordingly `(PHSF.13)` is a source theorem, not RH.  The exact surviving completion theorem is:

> literal integer/Poisson self-duality identifies the anomaly-subtracted theta completion with a
> record-complete intertwiner of the explicit colligation `(C,D2,B,mathsf T)`, retaining its
> cyclic prime formation and exhausting the completed relation horizon.

Record completeness would preserve the zero residual survival projection in `(PHSF.10)`.  Corpus
`xiRightPrimeMixedHorizonDefect` assigns every strict-right copy a rank-one residual horizon of
trace one.  Exhaustion would therefore exclude every strict-right copy; functional-equation
reflection excludes strict-left copies; RH follows.  The producer is the stated Poisson
intertwining/exhaustion theorem.  Requiring only a unitary dilation, CP conservation, scalar
functional equation, or equality of one response is insufficient by the cited locks.

## 7. Lean status

Certified in
`formal/GaloisForLFunctions/RHTower/PrimeHodgeHistorySurvivalFredholmColligation.lean`:

- forced survival ratio, exit hazard, tail products, and conditional scalar telescope;
- weighted survival shift, positive adjoint defect, bounded canonical left inverse, and exact
  duality--adjunction fracture `(B-C*)C=I-C*C`;
- finite operator exit-record telescope `sum_(j<N) E_j+R_N=I`;
- equality of the time-`n` initial-state exit readout, `w_n`, and the full prime-fibre marginal of
  `mathsf T`;
- kernel/range computation, Fredholm index `-1`, and exact index--exit--Hodge--nuclear trace
  conservation `(PHSF.13)`.

The strong-limit, exact operator-norm, compact-perturbation, and square-root observability
corollaries in `(PHSF.4)--(PHSF.10)` remain paper-certified but are not used by the Lean capstone.
They must not be cited as Lean-certified facts until separately formalized.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.PrimeHodgeHistorySurvivalFredholmColligation`, `GaloisForLFunctions.HTGeometry.HodgeSurvivalShiftDynamics`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.RHTower.PrimeHodgeHistorySurvivalFredholmColligation` (corpus: survival ratio, hazard, weighted shift, exit defect, left inverse, fracture, kernel/range, index, conservation) and `GaloisForLFunctions.HTGeometry.HodgeSurvivalShiftDynamics` (33 constants: the powers, strong and uniform behaviour, exit-record operator identities, observability, compactness, gauge uniqueness), both axiom-audit clean. `C = primeHodgeHistorySurvivalShift`, `D2 = primeHodgeHistoryExitDefect`, `B = primeHodgeHistorySurvivalLeftInverse`, `e_n = historyCoord n`.

| Claim | Lean declaration |
|-|-|
| (PHSF.1) `r_n = m_{n+1}/m_n = (2n+3)/(2n+9)`, `h_n = 6/(2n+9)`, `0 < r_n, h_n < 1` | `PrimeHodgeHistory.survivalRatio_formula`, `PrimeHodgeHistory.exitHazard_formula`, `survivalRatio_pos`, `survivalRatio_lt_one`, `exitHazard_pos`, `exitHazard_le_one` |
| (PHSF.2) `w_n = m_n h_n` | `PrimeHodgeHistory.w_eq_m_mul_exitHazard` |
| (PHSF.3) `C e_n = √r_n e_{n+1}`; positive gauge forced by the tails `m_n` | `primeHodgeHistorySurvivalShift`, `primeHodgeHistorySurvivalShift_basis`, `survivalWeight_forced` |
| (PHSF.4) `Cᴺ e_k = √(m_{k+N}/m_k) e_{k+N}`, `‖Cᴺ e_k‖² = m_{k+N}/m_k`, `Cᴺ → 0` strongly | `survivalShift_pow_basis`, `norm_survivalShift_pow_basis_sq`, `tendsto_survivalShift_pow_apply` |
| (PHSF.5) `‖Cᴺ‖ = 1` for every `N` | `norm_survivalShift_pow`, `tendsto_m_add_div_m` |
| (PHSF.6) `D2 = I - C*C`, `D2 e_n = h_n e_n` | `primeHodgeHistoryExitDefect_eq_adjoint_fracture`, `primeHodgeHistoryExitDefect` |
| (PHSF.7) `r_n ≥ 1/3`, bounded left inverse `B`, `BC = I` | `PrimeHodgeHistory.one_third_le_survivalRatio`, `primeHodgeHistorySurvivalLeftInverse`, `primeHodgeHistorySurvivalLeftInverse_comp_shift` |
| (PHSF.8) `(B - C*)C = I - C*C = D2` | `primeHodgeHistory_dualityAdjunctionFracture_mul` |
| (PHSF.9) `C*ʲD2Cʲ = diag(w_{k+j}/m_k)`, `C*ᴺCᴺ = diag(m_{k+N}/m_k)` | `adjoint_survivalShift_pow_exitDefect`, `adjoint_survivalShift_pow_comp`, `primeHodgeHistoryExitRecordAt`, `primeHodgeHistorySurvivalRemainder` |
| (PHSF.10) `I - C*ᴺCᴺ = ∑_{j<N} C*ʲD2Cʲ`; `∑_j ‖√D2 Cʲ x‖² = ‖x‖²` | `survival_exit_operator_telescope`, `primeHodgeHistory_operator_exit_telescope`, `sqrtExitDefect`, `hasSum_norm_sqrtExitDefect_survival` |
| (PHSF.11) `⟨Cⁿe_0, D2 Cⁿe_0⟩ = w_n` | `inner_survivalShift_pow_exitDefect_initial` |
| (PHSF.12) `ker C = 0`, `range C = e_0^⊥`, `ind C = -1`; `C - S` compact | `ker_primeHodgeHistorySurvivalShift`, `range_primeHodgeHistorySurvivalShift`, `primeHodgeHistorySurvivalShiftIndex_eq_neg_one`, `isCompactOperator_survivalShift_sub_shift` |
| (PHSF.13) `-ind C = ∑ w_n = Tr Φ = Tr 𝖳 = 1` | `primeHodgeHistory_index_exitFlux_integralNuclear_conservation`, `hasSum_primeHodgeHistoryExitEnergy` |
| Summary | `hodge_survival_shift_dynamics`, `primeHodgeHistorySurvivalFredholmColligation_closed` |

§1 and §6 are interpretation. The completion theorem of §6 is stated as open and is not claimed.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
