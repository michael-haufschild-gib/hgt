# Signed Euler–Poisson rigidity and arithmetic cusp order

- **ID:** CHMD-SIGNED-SOURCE-RIGIDITY-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CHMD complete theta source; corpus-only research, 2026-10-18.
- **Statement:** The two complete Euler–Poisson parity readouts uniquely determine all signed arithmetic weights from any unbounded set of integer samples; the first differing coefficient determines eventual strict order of forward-source samples.

## Goal

Close the signed-cancellation loophole in source-preserving arithmetic reweighting. Existing order-rigidity theorems require coefficientwise comparison with the von Mangoldt weights. Here arbitrary compensating signs are allowed, and the original coefficients are still forced. The positive result provides exact recovery, an explicit error bound, and an order classification.

## Gates

- [x] 0 → 1: specified actual theta kernel and actual Euler–Poisson source.
- [x] 1 → 2: complete paper proof below; no open mathematical dependency.
- [x] 2 → 3: targeted builds and all four actual-file Lean checks passed; all 61 new declarations have only standard axioms.
- [ ] 3 → 4: not requested; no external novelty or publication audit performed.

## Exact statements

Write `Theta = riemannKernelReal`, `E(t)=exp(9t/2-pi*exp(2t))`, `q_n=n+2`, and let `L,U>0` be the corpus theta-envelope constants. For signed coefficients `c_n`, admissibility means

`sum_n |c_n| Theta(log q_n) < infinity`.

This is equivalent to `sum_n |c_n| E(log q_n)<infinity`; it imposes neither positivity nor polynomial growth. Put `a_n=c_n E(log q_n)` and

`A_n(x)=Theta(x+log q_n)/E(log q_n)`,

`F_c(x)=sum_n c_n Theta(x+log q_n)=sum_n a_n A_n(x)`.

For every `m>=0` and `x>=0`,

`|sum_{n>=m} a_n A_n(x)/A_m(x)-a_m|`

`<= (U/L) exp(-pi*(2m+5)*(exp(2x)-1)) sum_{n>m}|a_n|`.

Consequently every coefficient is recovered recursively by

`c_m = lim_{N→infinity} (F_c(N)-sum_{n<m} c_n Theta(N+log q_n))/Theta(N+log q_m)`.

If `c,d` differ first at `m`, the sign of `F_d(N)-F_c(N)` eventually equals the sign of `d_m-c_m`. Equality on an unbounded set of natural-number samples forces `c=d`. The sign statement is proved for integer samples; no continuous-sample sign theorem is claimed.

For weights `w_n` on the original natural-number index, require `w_0=w_1=0`, and convergence of the symmetric arithmetic series at every nonnegative integer sample. Define the existing readouts

`S_w(x)=sum_n w_n [Theta(x+log n)+Theta(x-log n)]`,

`O_w(x)=sum_n w_n [Theta(x-log n)-Theta(x+log n)]`.

If `(S_w(N),O_w(N))=(S_vM(N),O_vM(N))` on an unbounded sample set, then `w_n=vonMangoldtAtom(n)` for every `n`. The theorem `unique_signed_parity_source` states existence and uniqueness together, with all convergence requirements for the actual arithmetic source proved.

## Dependency-closed paper proof [PROVED HERE]

1. **Known envelope.** The corpus proves `L E(t)<=Theta(t)<=U E(t)` for `t>0`. Since `log q_n>0`, this applies at every `x+log q_n` with `x>=0`. It also proves strict positivity of `Theta` and `E`.
2. **Exact separation.** Direct exponential algebra gives
   `E(x+log q_n)/E(log q_n)=exp(9x/2-pi*q_n^2*(exp(2x)-1))`.
   Dividing upper and lower envelope inequalities gives
   `A_n(x)/A_m(x)<=(U/L) exp(-pi*(q_n^2-q_m^2)*(exp(2x)-1))`.
3. **Summation with arbitrary signs.** Each `A_n(x)<=U exp(9x/2)`, so the signed source converges absolutely for `x>=0`. For `n>m`, `q_n^2-q_m^2>=2m+5`. Remove the head and the `m`th term, apply the triangle inequality, and sum the preceding ratio bound against `|a_n|`. This proves the displayed quantitative estimate, without a positivity assumption on `a`.
4. **Recovery and order.** The exponential error tends to zero along integer samples. Dividing by the fixed positive `E(log q_m)` recovers the original coefficient. For two distinct sequences, choose their least differing index. Their finite heads cancel. The normalized difference tends to the nonzero difference of the two coefficients. Positivity of the normalizing atom gives eventual strict order. Such a difference cannot vanish on an unbounded sample set.
5. **Actual complete source.** Existing `oneSided_source_equation` proves that the actual forward von Mangoldt series equals
   `-archConstantReal*Theta(x) + integral_{u>0} gammaSourceTerm(x,u) + integral_{u>0} 2*cosh(u/2)*Theta(x+u) - x*Theta(x)`.
   Existing prime-source summability admits the actual coefficients to the recovery class. Thus the fixed theta, Gamma, and pole source has exactly one admissible signed realization, and its coefficients are recovered from that source alone.
6. **Both parity identities.** Positivity of each theta factor bounds the absolute directed summands by the absolute symmetric summands, so both directed series converge. Termwise addition and subtraction give `S_w-O_w=2F_w`. Agreement of both parity readouts gives agreement of forward sources. Symmetric convergence at zero gives forward admissibility at zero; remove the zero and one slots and apply step 4. The actual von Mangoldt sequence satisfies the support convention and all convergence requirements, proving the closed existence-and-uniqueness statement.

## Corpus delta

- `CHMDPrimeTailSelection.primeTail_selects_first` already isolates the first term of the actual nonnegative von Mangoldt tail. This contribution does not claim that special-case limit as new.
- `EulerPoissonChiralDriftAndPrimeShiftRigidity` already excludes coefficientwise upward perturbations. The present result excludes arbitrary signed compensations preserving both complete readouts, including agreements confined to an unbounded sample set.
- Quantitative signed-tail isolation, lexicographic order, sparse uniqueness, and the exact characterization of admissibility are the positive additions.

## Scope and open core

The primitive resolvent bound at `1/2` remains open. This result does not establish RH, positivity of the original signed energy, rigidity from either parity readout alone, or stable numerical inversion. It identifies the original arithmetic data and excludes a particular proposed repair of that data.

The earlier possible Landau argument for eventual signs of resolvent eigenvectors was not proved and is not used. No claim about eigenvector oscillation is made here. No web search, numerical experiment, external novelty audit, full build, umbrella build, or heartbeat increase was used.

## Lean implementation

- `formal/GaloisForLFunctions/RHTower/CHMDArithmeticThetaIsolation.lean`: quantitative estimate and recursive recovery.
- `formal/GaloisForLFunctions/RHTower/CHMDArithmeticThetaOrder.lean`: eventual order and uniqueness on unbounded sample sets.
- `formal/GaloisForLFunctions/RHTower/CHMDSignedEulerPoissonRigidity.lean`: natural admissibility, actual source uniqueness, recovery of `vonMangoldtAtom`.
- `formal/GaloisForLFunctions/RHTower/CHMDSignedParitySourceRigidity.lean`: complete signed parity rigidity and closed existence-and-uniqueness theorem.

## Log

- 2026-10-18 — Corpus-first conjecture loop; found earlier actual-tail selection and narrowed claimed delta to arbitrary signed recovery and complete source rigidity. Paper proof and formalization completed.
- 2026-10-18 — Complete parity bridge built successfully. Final targeted build and all four `lake env lean` source-file checks passed. Formal index refreshed. Earlier prime-gap and eigenvector-sign ideas are not used and are not claimed proved.

## Verification record

- `lake --old build GaloisForLFunctions.RHTower.CHMDSignedParitySourceRigidity`: passed, including the four new leaves in its dependency graph; no umbrella build.
- `lake env lean` on each of the four final `.lean` files: passed, no warnings or errors.
- Scoped `/tmp/chmd_final_name_checks.lean`: exited 0. All 61 new definitions and theorems report only subsets of `propext`, `Classical.choice`, and `Quot.sound`; the audit covered the entire declaration list. Mathlib name checks passed. All four `.olean` artifacts were verified newer than their final source files.
- `scripts/formal_tools.py index`: passed; API, gaps, overview, and search index refreshed.
- `scripts/formal_tools.py lint`: **failed on three unrelated repository findings**: `RHTower/ChronologicalSelbergCoefficientMass.lean` and `RHTower/Sieve/TotientCubicMean.lean` are unreachable from their theorem-area umbrella; `GaloisForLFunctions/TransHorizonIncidenceMechanics.lean` is a research leaf at package root. No new-module lint error or prohibited proof declaration was reported. These unrelated files were not changed by this task.
- All four new modules are imported by `formal/GaloisForLFunctions/RHTower.lean`. The RH frontier map was not edited by this task.
