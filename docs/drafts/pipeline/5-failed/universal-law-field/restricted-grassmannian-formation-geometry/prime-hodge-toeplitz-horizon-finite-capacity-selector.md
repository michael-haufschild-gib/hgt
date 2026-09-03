# Prime--Hodge Toeplitz-horizon finite-capacity selector

- **ID:** ULF-PHTH-002
- **Stage:** 5-failed
- **Verdict:** `[FALSIFIED]`; observer-to-harmonic-history lift was selected, not derived
- **Parent:** ULF-PHSTH-001
- **Positive survivor:** PHSTH-G harmonic/first-exit lift bifurcation

## Proposed selector

The proposal asked for a pre-divisor positive finite-trace completion `X` satisfying

```text
X-mathcal U*Xmathcal U=T_cap,
```

and asserted that every strict-right rank-one horizon `p_q` contributes the shift-harmonic block

```text
I tensor p_q <= X-G_cap.
```

ULF-PHSTH-001 would then force `X=G_cap`, contradicting `p_q!=0`.

## Exact killing mechanism

The second line has no source justification and conflicts with the actual formation grammar.

1. `[CORPUS]` `IntegralNuclearRelationIncidenceHorizon` proves that a supplied strict-right copy
   yields one positive rank-one prime-mixed horizon `p_q` with trace and trace norm one.
2. `[CORPUS]` `PrimeHodgeHistoryFirstExitTransgression` and ULF-PHSG-001 prove the literal history
   lift of any prime operator `p` is

   ```text
   E_p=Phi tensor p=(G tensor p)-U*(G tensor p)U.
   ```

   It is positive trace class and has trace `Tr p`.
3. The proposed harmonic lift

   ```text
   H_p=I tensor p
   ```

   is also natural with respect to the shift and is noncompact, but it is not the first-exit
   formation. Both encode the same closed observer through different recovery operations.

Thus the proposal chose `H_p` precisely because its repeated mass contradicts finite capacity.
Choosing `E_p` gives finite mass and no contradiction. Closed observer data alone do not determine
the lift.

`PHTH-F5` from the original card is therefore established: the observer is not source-forced to
lift shift-harmonically.

## Why same-displacement does not repair it

The equation `X-U*XU=T_cap` classifies completions once `T_cap` is fixed, but does not prove that
an actual Xi relation horizon is a Toeplitz fixed component of `X`. Demanding that identification
is another form of the retired source-to-target completion transport. It is not derived by the
Brown--Halmos theorem or by finite Euler trace.

## Relentless-interrogation chain

### Replacement 1: noncommutative Poisson boundary

Treat `p_q` as a positive harmonic boundary component of the shift CP map.

**Verdict:** `[REDISCOVERED] [CIRCULAR]`. The corpus already contains Wold--Toeplitz boundary
quotients, all-prime Calkin characters, source-relative completion classes, and the theorem that
bounded finite-core coherence erases completion-born horizons. Naming the fixed sector a Poisson
boundary does not make the Xi horizon land there.

### Replacement 2: unbounded Fredholm/graph completion

Retain the horizon in an unbounded graph topology while importing the finite source nuclear
budget.

**Verdict:** `[CIRCULAR]`. The failed ULF-INHD-001 card proves the bounded/singular dichotomy:
bounded finite-core landings erase the horizon; singular landings lose the Hilbert--Schmidt budget.
Existing graph/Fredholm cards show choosing a graph norm that retains the Xi fibre is the missing
selection premise.

### Replacement 3: modular trace pairing

Pair pre-divisor `T` directly with the recovered character `p^(-2|t|)`, which is strictly subunit
for `t!=0`, and demand integrality.

**Verdict:** `[CIRCULAR]`. `DenseArithmeticLorentzLatticeRigidity` already proves that integral
descent of the full dense prime-weld modular action forces `t=0`. What is missing is precisely the
source-generated common integral frame. The trace pairing itself supplies no integrality.

### Replacement 4: profinite divisibility

Use finite-stage null-homotopies to make an off-line integer divisible at every level.

**Verdict:** `[REDISCOVERED] [CIRCULAR]`. `LedgerTelescope`, `CompletionParityTower`, Big-Witt,
cyclotomic, and integral Tate modules already prove the divisibility-to-zero mechanisms. Existing
failed cards locate the missing arrow: physical coefficient-faithful integral descent is itself
critical-line strength.

## Positive survivor

**PHSTH-G (two-lift law).** Every finite-rank positive observer `p` has at least two exact,
inequivalent histories:

```text
harmonic:   H_p=I tensor p,      U*H_pU=H_p,       noncompact/infinite trace;
first exit: E_p=Phi tensor p,    E_p=delta_U(G tensor p), S1/trace Tr p.
```

The observer is recovered from grade-zero compression of `H_p` and from total exit flux of `E_p`.
Therefore “closed observer, open history” is not one law but a lift-selection problem.

## Representation lesson

The missing universal field cannot assign histories from endpoint observers alone. Its primitive
must include the boundary operation that distinguishes harmonic retention from first-exit
emission. Any capacity contradiction that first chooses the nonsummable lift is theatre.

## Lean status

The target rank-one horizon and source first-exit lift are already Lean-proved in separate modules.
PHSTH-G is dependency-closed on paper but was not formalized during this Lean-read-only research
pass. The failed selector must not be formalized.
