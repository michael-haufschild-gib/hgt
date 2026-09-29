# Prime--Hodge history integral nuclear defect

- **ID:** ULF-PHIN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-SCIN-001`, `ULF-EWHC-001`, `ULF-SKPM-001`, `ULF-DHNJ-001`
- **Purpose:** construct one object carrying prime formation, integral orientation, nuclearity,
  phase homotopy, Hodge completion data, and open-history flux before any divisor is supplied.

## 1. Object nobody asked for

Let `mathsf T_form(t)` be the source Stokes cubic defect of `ULF-SCIN-001` on
`H_P=ell2(Primes)`. Let

```text
m_n=105/((2n+3)(2n+5)(2n+7)),
w_n=m_n-m_(n+1)
   =630/((2n+3)(2n+5)(2n+7)(2n+9)).                 (PHIN.1)
```

On history space `H_hist=ell2(Nat)`, define the diagonal operator

```text
Phi e_n=w_n e_n.                                     (PHIN.2)
```

The requested single defect is

```text
mathsf T(t)=Phi tensor mathsf T_form(t)               (PHIN.3)
```

on `H_hist tensor H_P` for `t!=0`, with fixed-chart value zero at `t=0`.

Its full matrix is

```text
mathsf T(t)_((n,p),(k,q))
 =1_(n=k) w_n sign(t)
   sqrt(pi_|t|(p)pi_|t|(q)) kappa(log p,log q).       (PHIN.4)
```

Nothing in `(PHIN.1)--(PHIN.4)` uses a zero, divisor copy, Xi eigenvector, chosen ordinate, or
RH. The history weights are forced by the Kummer homotopy jets of the literal prime kernel; they
are not auxiliary damping parameters.

## 2. Theorem A: integral, nuclear, and prime-mixed

For every `t!=0`,

```text
mathsf T(t)*=mathsf T(t),
sign(t) mathsf T(t)>=0,
mathsf T(t) is Schatten-one,
Tr mathsf T(t)=sign(t) in Z,
||mathsf T(t)||_1=1,
mathsf T(-t)=-mathsf T(t).                           (PHIN.5)
```

At every retained history grade and for every two primes,

```text
mathsf T(t)_((n,p),(n,q)) !=0.                        (PHIN.6)
```

Thus history grading does not diagonalize or square away literal cross-prime formation.

**Proof.** `ULF-DHNJ-001` gives `w_n>0` and `sum_n w_n=1`, so `Phi` is positive trace-class with
trace and trace norm one. `ULF-SCIN-001` gives the corresponding signed properties for
`mathsf T_form(t)`. Trace, trace norm, adjoint, and positivity factor under tensor products of
trace-class operators, proving `(PHIN.5)`. Formula `(PHIN.4)`, strict positivity of `w_n`, all
wall weights, and the cubic Cauchy coherence prove `(PHIN.6)`. QED.

## 3. Theorem B: homotopy is a tail observable

Let `Q_n` project history space onto grades `k>=n`. For `t>0`,

```text
Tr((Q_n tensor 1) mathsf T(t))=m_n.                  (PHIN.7)
```

At the comoving wall, write `A` for the exponential cubic operator and
`mathsf A=Phi tensor A`. Then

```text
Tr((Q_n tensor 1) mathsf A)
 = ||ad_X^n(A)||_2^2/((2n)!||A||_2^2).               (PHIN.8)
```

The grade flux is recovered by adjacent tail difference,

```text
Tr(((Q_n-Q_(n+1)) tensor 1) mathsf A)=w_n,           (PHIN.9)
```

and the full integral orientation is the sum of these local fluxes:

```text
sum_n Tr(((Q_n-Q_(n+1)) tensor 1) mathsf A)=1.       (PHIN.10)
```

**Proof.** Tail trace of `Phi` is `sum_(k>=n)w_k=m_n`; tensor with a trace-one formation
operator gives `(PHIN.7)`. `ULF-DHNJ-001` identifies `m_n` with the normalized commutator energy,
giving `(PHIN.8)`. Adjacent subtraction and summation give `(PHIN.9)--(PHIN.10)`. QED.

This is joint reconstruction: the history marginal recovers every Kummer homotopy jet, while
every history fibre retains the entire prime-mixed kernel.

## 4. Theorem C: canonicality

`Phi` is the unique positive diagonal trace-class operator whose history-tail traces are the
normalized commutator energies in `(PHIN.8)`.

**Proof.** If diagonal weights `a_n>=0` have tail sums `m_n`, adjacent subtraction forces
`a_n=m_n-m_(n+1)=w_n` for every `n`. QED.

Consequently `(PHIN.3)` is not an arbitrary tensor enlargement. Its new factor is uniquely
reconstructed from the intrinsic phase homotopy of `mathsf T_form`.

## 5. Theorem D: stronger direct sub-unit anchor

The largest history weight is `w_0=2/3`, so

```text
||Phi||=2/3.
```

Since `||A||<=4/sqrt(35)`,

```text
||mathsf A||<=8/(3sqrt(35))<1.                       (PHIN.11)
```

The object therefore has integral trace one but no eigenvalue of unit size. Its charge is
necessarily distributed across both prime and history directions. This is a direct sub-unit
anchor with no amplification.

**Proof.** Formula `(PHIN.1)` is strictly decreasing, hence `||Phi||=w_0=2/3`. Operator norm is
multiplicative on Hilbert tensor products. The bound and strict inequality follow. QED.

## 6. Theorem E: two incompatible wall closures

In the fixed prime chart,

```text
mathsf T(t) ->0 strongly as t->0 from either side,
```

while its trace norm remains one. In the source-comoving chart it lands in trace norm at

```text
+mathsf A=+Phi tensor A  from the right,
-mathsf A=-Phi tensor A  from the left.               (PHIN.12)
```

**Proof.** Strong convergence of the uniformly bounded prime factor to zero implies strong
convergence of the tensor product first on elementary tensors and then by density. Trace norm is
`||Phi||_1||mathsf T_form(t)||_1=1`. Comoving trace-norm convergence follows from
`||Phi tensor (A_d-A)||_1=||Phi||_1||A_d-A||_1`. QED.

## 7. Higher mechanism: diffuse flux versus relation horizon

The corpus target object `xiRightPrimeMixedHorizonDefect` already proves that one off-line copy
creates a prime-mixed rank-one nuclear unit, but only **after divisor specialization**, as the
multivalued vertical horizon of a closed relation. `mathsf T` is its missing pre-divisor source
counterpart. Their structural difference is now exact:

```text
source:    one normal trace unit = sum of decaying positive history fluxes;
off line:  one unit appears as a multivalued completion horizon.
```

This suggests a completion index not based on signed Fredholm parity or one-marginal graph
closure. It measures failure of anomaly-subtracted completion to be bistochastic on the joint
history--prime operator system: the amount by which completion concentrates the diffuse source
unit into a rank-one vertical horizon.

RH would follow from the following still-open, non-circular formation theorem:

> literal integer/Poisson self-duality makes anomaly-subtracted completion a positive unital,
> trace-preserving map on the marked history--prime operator system, preserves `(PHIN.9)` grade
> by grade, and sends its completed divisor specialization to the relation-horizon defect.

Positive unital maps contract operator norm. Therefore `(PHIN.11)` would force every completed
image of `mathsf A` to have norm strictly below one. But every strict-right copy has a rank-one
projection of norm one and trace one by `xiRightPrimeMixedHorizonDefect_apply_horizon` and
`opTrace_xiRightPrimeMixedHorizonDefect`. Identifying that projection as the completed image would
be a contradiction, excluding the copy. On every finite cutoff, a unital trace-preserving
completely positive realization also contracts Hilbert--Schmidt norm by the corpus
bistochastic-channel law, while the target projection again has Hilbert--Schmidt norm one; an
infinite-cutoff use requires the corresponding normal limit theorem.

Normality alone is insufficient: an ordinary normal trace-preserving channel may concentrate a
diffuse density into a pure state. The necessary source law is bistochasticity plus the marked
formation/horizon identification. This is the precise source-to-target edge, and `(PHIN.3)` does
not supply it by itself.

The theorem must act on the correlated history--prime state. Existing no-gos prove that compact
fixed-chart observers lose the unit, ordinary Hellinger coface closure saturates, constant charge
on vanishing grades produces a nonclosed graph, and signed reflection index misses unsigned
escape multiplicity. Corpus also proves the existing fixed Möbius--Gamma/Xi source map is
expansive near the critical ray, so it cannot be reused as this bistochastic transport; the joint
history carrier and anomaly subtraction must change the map itself.

## 8. Lean status

`formal/GaloisForLFunctions/RHTower/PrimeHodgeHistoryIntegralNuclearDefect.lean` constructs the
literal joint kernel on `ell2(Nat x Primes)`. Lean proves its exact positive history flux,
telescoping tail reconstruction, finite-block positivity, full-operator positivity,
Hilbert--Schmidt and Schatten-one membership, trace `1`, trace norm `1`, and nonzero cross-prime
entries on every history fibre. `primeHodgeHistoryIntegralNuclearDefect_closed` is the
hypothesis-free unit-aperture capstone.

`formal/GaloisForLFunctions/RHTower/PrimeHodgeHistoryIntegralNuclearHomotopyDefect.lean` now
constructs the signed two-sided family as one Lean term and proves reflection oddness, oriented
positivity, Schatten-one membership, `Tr mathsf T(t)=sign(t)`, `||mathsf T(t)||_1=|sign(t)|`,
off-wall cross-prime mixing, recovery of the unit-aperture object, and the exact signed
theta-flux/unsquared-prime-density diagonal. Chamberwise trace-norm continuity, completed
formation-to-horizon transport, and the all-order analytic commutator identification in
`ULF-DHNJ-001` remain outside this Lean certificate.

## 9. Theorem F: first-exit transgression from relative curvature

The object has an intrinsic construction from the relative metric anomaly; it is not an added
trace-one density.  Let

```text
kappa_0=r_0,                 kappa_n=r_n-r_(n-1)  (n>0),
r_n=sum_(j<=n) kappa_j,
m_n=product_(j<n) r_j,
F(kappa)_n=m_n(1-r_n).                              (PHIN.13)
```

Here `kappa` is the diagonal of the positive prime-mixed relative curvature
`K=A_out-A_in`, where `A_out` and `A_in` are compact non-trace-class metrics.  Then

```text
F(kappa)_n=w_n,
mathsf F(K)=mathsf T(1),
kappa_n mathsf T(1)_((n,p),(n,q))
  =w_n K_((n,p),(n,q))                              (PHIN.14)
```

for every grade `n` and ordered pair of primes `(p,q)`.  The last identity retains the complete
unsquared cross-prime kernel, so `(PHIN.14)` is stronger than equality of traces.

**Proof.** The relative-curvature reconstruction gives
`r_n=sum_(j<=n)kappa_j`.  Its survival colligation gives
`m_n=product_(j<n)r_j` and `w_n=m_n(1-r_n)`, proving the first identity.  Both `K` and
`mathsf T(1)` lift their respective history weights through the same normalized Stokes kernel
`A_form(p,q)`.  Thus their grade-`n` blocks are `kappa_n A_form` and `w_n A_form`; cross
multiplication proves the last identity and the exact operator identification. QED.

This is the missing addition-versus-multiplication mechanism at source level: additive curvature
is cumulatively integrated to survival, ordered multiplication forms open history, and the next
boundary emits the integral nuclear unit.  It does not identify the Xi completion.  The remaining
RH edge is functoriality of this first-exit transgression under the already forced polar--Gamma
completion, followed by exhaustion of the completed relation horizon.

Lean module
`formal/GaloisForLFunctions/RHTower/PrimeHodgeHistoryFirstExitTransgression.lean` formalizes
`(PHIN.13)--(PHIN.14)` and the signed family for every wall parameter.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.HistoryTensorOperators`, `GaloisForLFunctions.HTGeometry.PrimeHodgeHistoryTensorDefect`, `GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect`, `GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect`, `GaloisForLFunctions.RHTower.PrimeHodgeHistoryFirstExitTransgression`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.HistoryTensorOperators` (45 constants: the history tensor `a ⊗ B` on `ℓ²(ℕ; E) = ℓ²(ℕ) ⊗ E`, product Hilbert basis, Hilbert–Schmidt, trace, trace-norm and strong-convergence laws) and `GaloisForLFunctions.HTGeometry.PrimeHodgeHistoryTensorDefect` (57), both axiom-audit clean, together with the corpus modules `GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect`, `GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect` and `GaloisForLFunctions.RHTower.PrimeHodgeHistoryFirstExitTransgression` (joint kernel on `ℓ²(ℕ × Primes)`). The canonical unitary `primeHistoryUnitary : ℓ²(ℕ × Primes) → ℓ²(ℕ; ℓ²(Primes))` identifies the corpus joint defect with the history tensor `Φ ⊗ T_form(t)`, so every corpus statement and every new statement concerns the same object. `T_form` is the SCIN unit `stokesCubicUnit`; `A` is the EWHC wall operator; `A_d`, `A_0` are the SCIN landings.

| Claim | Lean declaration |
|-|-|
| (PHIN.1) `m_n`, `w_n = 630/((2n+3)(2n+5)(2n+7)(2n+9))` | `PrimeHodgeHistory.m`, `PrimeHodgeHistory.w`, `PrimeHodgeHistory.w_formula`, `homotopyEnergy_eq_m` |
| (PHIN.2) `Φ e_n = w_n e_n` | `primeHodgeHistoryFluxOperator`, `fluxTensor` |
| (PHIN.3) `T(t) = Φ ⊗ T_form(t)`; corpus joint kernel is the same operator | `historyDefect`, `primeHistoryUnitary`, `primeHistoryUnitary_conj`, `primeHodgeHistoryIntegralNuclearHomotopyDefect` |
| (PHIN.4) full matrix `1_{n=k} w_n sign(t) √(π(p)π(q)) κ(log p, log q)` | `inner_historyDefect_single`, `primeHodgeHistoryDefectKernel` |
| Thm A (PHIN.5): self-adjoint, `sign(t)T(t) ≥ 0`, Schatten-one, `Tr = sign t`, `‖·‖₁ = 1`, odd | `historyDefect_integral_nuclear`, `adjoint_historyDefect`, `historyDefect_neg`, `primeHodgeHistoryIntegralNuclearHomotopyDefect_closed` |
| (PHIN.6) every same-grade cross-prime entry nonzero | `inner_historyDefect_single_ne_zero`, `primeHodgeHistoryIntegralNuclearHomotopyDefectKernel_sameHistory_ne_zero` |
| Thm B (PHIN.7) `Tr((Q_n ⊗ 1)T(t)) = m_n` | `historyTailProjection`, `opTrace_historyTail_historyDefect`, `hasSum_tailFlux` |
| (PHIN.8) `Tr((Q_n ⊗ 1)𝖠) = ‖adⁿ_X(A)‖²₂/((2n)!‖A‖²₂)` | `historyWallOperator`, `opTrace_historyTail_historyWallOperator`, `jetKernel` (DHNJ) |
| (PHIN.9) `Tr(((Q_n - Q_{n+1}) ⊗ 1)𝖠) = w_n` | `opTrace_historyGrade_historyWallOperator` |
| (PHIN.10) `∑_n Tr(((Q_n - Q_{n+1}) ⊗ 1)𝖠) = 1` | `hasSum_opTrace_historyGrade_historyWallOperator` |
| Thm C: `Φ` is the unique nonnegative diagonal with tails `m_n` | `eq_historyFlux_of_tails` |
| Thm D (PHIN.11): `‖Φ‖ = 2/3`, `‖𝖠‖ ≤ 8/(3√35) < 1` | `norm_historyWallOperator_le`, `norm_primeHodgeHistoryFluxOperator`, `PrimeHodgeHistory.subunit_constant`, `norm_historyMap_le` |
| Thm E: fixed chart `T(t) → 0` strongly, `‖T(t)‖₁ = 1` | `tendsto_historyDefect_apply`, `tendsto_historyMap_apply`, `historyDefect_integral_nuclear` |
| Thm E (PHIN.12): comoving chart `1 ⊗ U_d` gives `±Φ ⊗ A_d`, landing at `±Φ ⊗ A_0` in trace norm; `Φ ⊗ A_0` is the quantile transport of `𝖠` | `historyComovingChart`, `historyComovingChart_conj`, `historyDefect_comoving_landing`, `tendsto_traceNorm_neg_fluxTensor_wallLanding`, `fluxTensor_quantileWallOperator`, `traceNorm_historyMap_sub_le` |
| Thm F (PHIN.13)–(PHIN.14): first-exit transgression `F(κ)_n = w_n`, `𝖥(K) = T(1)`, grade-wise kernel conservation | `PrimeHodgeHistory.curvatureFirstExitWeight_eq_w`, `primeHodgeHistoryCurvatureFirstExitOperator_eq_defectOperator`, `primeHodgeHistory_firstExit_curvature_kernel_conservation`, `primeHodgeHistoryCurvatureFirstExitHomotopyDefect_closed` |
| Summary | `prime_hodge_history_tensor_defect`, `primeHodgeHistoryIntegralNuclearDefect_closed` |

§7 (diffuse flux versus relation horizon, the conditional completion route) is interpretation and states an open theorem it does not claim.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
