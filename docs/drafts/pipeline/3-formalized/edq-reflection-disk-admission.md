# EDQ simultaneous admission to the complete response disks

- **ID:** EDQ-RDA
- **Stage:** 3-formalized
- **Type:** quantitative source theorem and scoped obstruction; paper proof and Lean audited
- **Sources:** [full response](../3-formalized/edq-full-reflection-response.md), [height decay](../3-formalized/edq-logarithmic-response-height.md), [cubic height error](../3-formalized/edq-reflection-error-height.md)

## Full chain and scope

Euler deletion → exact full complex zero balance → signed arithmetic comparison → exclusion of off-line zeros → RH. This component tests whether the two current necessary disks supply separation. It does not retire EDQ, the exact balance, or stronger future source estimates.

Let `delta=Re(s)-1/2`, `u=abs(Im(s))`, `epsilon=1/2-abs(delta)`, and

`V(s)=i*Im(s)/normSq(conj(s)*(1-conj(s)))-1/[12*(conj(s)+1)*(2-s)]`.

Write `L(t)` for the actual complete critical logarithmic response, and `B(epsilon)` for the existing cubic height cost. Actual off-line strip zeros obey both `norm(L+V)<=delta^2/12` and `norm(L+V)<=delta^2*B(epsilon)/(2*u)` at nonzero height.

## Positive survivor: quantitative enclosure of the actual source

For every complex `s` with `u>=1`, both quadratic norm factors in the first denominator are at least `u^2`, and both linear factors in the second denominator have norm at least `u`. Consequently

`norm(V)<=1/u^3+1/(12*u^2)<=13/(12*u)`.

The proved source flux estimate gives `norm(L)<=19/(9*u)`, hence

`norm(L+V)<=115/(36*u)<4/u`.

For `0<Re(s)<1` and `abs(delta)>=1/4`, `0<epsilon<=1/4`, so `B(epsilon)>=256` and `delta^2>=1/16`. The height disk radius is at least `8/u`. The actual source therefore lies strictly inside that disk with additive slack `4/u` whenever `u>=1`. For `u>=1536`, it also lies inside the older disk with additive slack `1/384`. These are simultaneous inequalities for all actual source points in these regions, independent of any zeta-zero condition.

## Actual nonzero witnesses

At any prescribed large height on `Re(s)=3/4`, isolated zeta zeros in the open strip give a positive punctured neighborhood of nonvanishing. Perturb upward by a positive imaginary increment smaller than its radius. This preserves real part, increases height, and gives an actual nonzero witness satisfying both strict disk inequalities. No numerical zero/nonzero certificate is involved.

## Exact limitation

Admission to these two disks, even simultaneously at arbitrarily large heights, cannot certify a zero or exclude off-line zeros in the admitted region. The necessary inequalities remain valid. The replacement must use additional actual arithmetic information, such as a signed comparison for the retained source/flux, or prove substantially sharper separating bounds. Nonselectivity of these particular estimates is not a theorem that every possible norm method fails.

## Gates

- [x] Existing source bounds and isolated-zero theorem inspected.
- [x] Dependency-closed symbolic paper proof, including quantitative positive survivor.
- [x] Scratch proof of enclosure, simultaneous strict admission, and actual cofinal nonzeros.
- [x] Leaf wiring, targeted build, new-only axioms, lint run, both ledgers.
- [x] Index refreshed once; all owned processes exited; four temporary source/probe files removed.
- [ ] Global lint clean: two unrelated concurrent modules remain unwired.
- [ ] Additional signed source comparison excluding every off-line zero; RH.

## Lean inventory and final audit

Leaf: `GaloisForLFunctions.RHTower.ArithmeticReflectionDiskAdmission`, namespace `RHTower.DeletionMixedRefinement`. 177 lines, eight theorems and one definition.

- `reflectionDiskSource`: the actual response and full complex target, including both mean factors.
- `reflection_target_normSq_lower`, `reflection_target_mean_norm_lower`: exact denominator height bounds.
- `norm_reflectionDiskSource_le`, `norm_reflectionDiskSource_lt`: quantitative enclosure of the actual source without a zero premise.
- `reflectionCubicHeightCost_outer_lower`: explicit canonical cost in both outer quarters.
- `reflection_height_disk_admission`, `reflection_fixed_disk_admission`: simultaneous strict admission with explicit positive slack.
- `exists_nonzero_reflection_disks_admitted`: actual cofinal nonzero witnesses on `Re(s)=3/4`, retaining both strict inequalities.

Foreground scratch passed without messages. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticReflectionDiskAdmission` compiled only this leaf in 58 seconds; all dependencies were cached. Its umbrella import is wired. No full or umbrella build ran. All nine new declarations were audited once and use only `propext`, `Classical.choice`, and `Quot.sound`; no old declaration was re-audited. No numerical experiment or computational certificate was used.

Formal lint reported exactly two unrelated umbrella reachability errors, for `MobiusHalfSelectionEulerCorrection` and `MobiusHalfSelectionEulerProduct`. The new leaf has no lint error. Those concurrent files were left untouched; global lint is not clean. Logs: `/tmp/edq_disk_admission.{check,build,axioms,lint,index}.log`, with the initial API probe in `/tmp/edq_disk_probe.log`.

The corpus index was refreshed once (seven changed modules, including concurrent work). All owned Lean processes exited; the four temporary scratch, probe, witness, and axiom source files were removed. Logs remain available.

Only the [present disk-only shortcut](../5-failed/edq-current-reflection-disks-as-selector.md) is retired. The exact arithmetic balance and its signed flux survive. No separating comparison or RH proof/falsification follows.
