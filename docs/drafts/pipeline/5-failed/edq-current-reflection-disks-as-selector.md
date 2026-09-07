# EDQ: using the two present reflection disks alone as a selector

- **Status:** FAILED shortcut; EDQ remains open.
- **Exact scope:** simultaneous use of the current bounds `norm(L_full+V)<=delta^2/12` and `norm(L_full+V)<=delta^2*B(epsilon)/(2*abs(t))` as a separating test. No claim against stronger norm estimates or the retained exact complex source balance.

## Obstruction and positive survivor

Every actual source in the open strip with `abs(delta)>=1/4` and `abs(t)>=1536` satisfies both inequalities with strict quantitative slack. Actual nonzeros on `Re(s)=3/4` satisfy them above every prescribed height. Thus these inequalities cannot exclude that region.

The positive survivor is the unconditional source enclosure `norm(L_full+V)<=115/(36*abs(t))<4/abs(t)` for `abs(t)>=1`, together with explicit simultaneous admission margins `1/384` and `4/abs(t)`. Its proof retains both quadratic height factors, both linear mean factors, and the complete critical logarithmic source. The second pass retains both disks, not only the newer one, and uses actual cofinal nonzero witnesses rather than auxiliary compatible models.

Dependency-closed paper proof and Lean scratch proof are complete. Final audit is recorded on the [formalized survivor card](../3-formalized/edq-reflection-disk-admission.md). Exact source and derivative integrals remain available. A replacement must derive additional signed arithmetic information or a sharper source comparison; neither has been proved here. RH remains unproved and unfalsified.
