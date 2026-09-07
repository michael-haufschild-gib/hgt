# CCM-FU: nonempty-energy contraction

- **Stage:** 5-failed
- **Type:** unconditional local contraction obstruction; exact source steering survivor
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** no claim of RH, SD1, PE4 or complete energy control.

## Frozen claim and arithmetic witness

For `V_P=Q_P-H_P^2`, test whether every prime merger contracts V. Stored-state evidence first rejects this at cutoff M=21, processed set P={2}, next prime 5. V rises from approximately 0.0896410813 to 0.0974192969. These values are guidance only. A separate reachability check finds some complete V-nonincreasing path at every stored cutoff through 32; that is also numerical only and does not control the final head.

The literal change at the witness is

`V_{2,5}(21)-V_{2}(21)=2*(C_3(21)+C_6(21))*C_15(21)-(C_5(21)+C_10(21))^2`.

Exact homothety gives `C_3(21)+C_6(21)=-sqrt(3)*(C_1(7)+C_2(7))>0.04` from the existing analytic seven-channel boxes. The first quotient block gives `C_15(21)>0.1`. Explicit quotient blocks using only divisor defects at 1,2,3,4 give `abs(C_5(21)+C_10(21))<0.08`. Those rational analytic bounds imply a strict V increase greater than 1/1000. The exact energy identity and all three analytic bounds are closed in Lean; no numerical premise enters the proof.

## Strong positive survivor

For every unprocessed prime p, the exact nonempty-energy update is the negative removed singleton square plus twice the signed overlap between nonempty p-free fibres and their p-containing partners. The complete head cancels from this law. A late-prime block L therefore satisfies exactly

`V_(P union L)=V_P-sum_(p in L)C_p^2`.

For any other unprocessed prime q, put `t_L=sum_(p in L)K_p>=0`. Comparing its energy change before and after that late block gives

`delta_q Q(P union L)=delta_q Q(P)-2*t_L*F_(M,P)({q})`.

Thus late-prime consumption improves a next step with nonnegative retained singleton coefficient and worsens a next step with nonpositive coefficient. This is an exact one-variable effect on the full energy, retaining the nonempty overlap and removed squares. It does not make nonempty energy monotone or construct a complete bounded path. The all-cutoff identities and both sign comparisons are formal. They retain the arithmetic control available to a growing interleaving and the nonempty interference it must still handle.


## Lean closure and remaining boundary

- `MobiusDivisorNonemptyEnergy.lean`: one definition and nine public theorems. Nonempty energy is exactly the sum of nonempty fibre squares and is nonnegative; the full and nonempty prime updates retain their exact paired products. The late-block law, its unconditional nonempty-energy decrease, full-energy steering identity and both signed comparisons are closed at every cutoff.
- `MobiusDivisorNonemptyEnergyObstruction.lean`: five public theorems. Analytic quotient-block bounds at 21, the positive reflected singleton from cutoff seven, the exact single-pair energy change, its increase greater than 1/1000, and the negation of universal prime-step contraction are closed.

The full-energy steering law is `delta_q Q(P union L)=delta_q Q(P)-2 t_L F_P({q})`. The nonempty law also shows why inserting late primes cannot change the nonempty energy gain of a fixed other prime: subtract the same removed late-singleton squares before and after that step. This is a decomposition, not an upper bound for the remaining signed products.

The stored-state diagnostic tests 41409 edges, of which 2472 increase nonempty energy. Its first is M=21, P={2}, prime five. A nonempty-energy nonincreasing complete path exists in every saved cutoff through 32, but this remains numerical guidance and does not bound the final head. Recovered heads from different isolated late-prime anchors agree within approximately 4.2e-14; reconstruction roundoff permits values down to approximately -2.0e-14 at zero-energy endpoints. These are diagnostics, not Lean inputs. Complete data and input hash are in `nonempty-reanalysis.json` in the existing computation directory.

This retires universal stepwise nonempty-energy contraction only. Existence of a suitable nonempty-energy path, the full original-diagonal ceiling, common-cutoff compatibility and SD1 remain open. A source proof must control the nonempty mixed products together with the signed singleton that determines whether late consumption helps or harms the next full-energy step.

## Verification

Both new leaves passed scratch checks and foreground `lake env lean <leaf> -o <exact olean>`. All fifteen new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. Both leaves are wired once into `RHTower.lean`. No previously audited theorem was re-audited; no umbrella, full or dependency build ran. Formal indexes were regenerated after adding the declarations.

The single global lint run reported five unrelated concurrent modules missing umbrella imports: `ThetaCuspDeepTailCalibration`, `ThetaCuspDeepTailCooling`, `ThetaCuspTwoAtomReflectedApproximation`, `ThetaCuspTwoAtomReflectedBounds` and `ThetaCuspTwoAtomSourceApproximation`. Neither new leaf was flagged, and no proof-debt error was reported. Those concurrent modules were not edited or built by this work.
