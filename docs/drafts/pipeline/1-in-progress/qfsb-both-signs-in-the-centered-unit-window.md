# Both signs in the centered unit window

- **Stage** 1-in-progress

Use the [exact two-endpoint formula](../3-formalized/qfsb-the-centered-unit-window-detects-the-prime-error.md) with \(E=\vartheta-\mathrm{id}\) and \(K(X)=\lfloor X/(b(X)+1)\rfloor\). 

**Critical endpoint.** Both signs of the centered unit band reach Littlewood size on sequences common to all proper-power choices. Write \(L(t)=\log\log\log t\). For either sign \(s\), take an arbitrarily large Littlewood witness \(x\) for \(sE(x)\), and maximize \(sE(m)/\sqrt m\) over the positive integers through \(\lfloor x\rfloor\). Flooring \(x\) costs less than one. These maximizing indices escape every finite set, and their normalized error is at least \(cL(x)\). At such an index,
\[
 s(E(m)-E(K(m)))\ge (1-2^{-1/2})\,sE(m).
\]
The floor residues cost \(o(\sqrt m)\) and all proper-power edits together cost \(O(\sqrt m)\). Since \(L(x)\ge L(m)\) at large arguments, the signed band exceeds \(c'\sqrt m L(m)\) simultaneously for every edit. In particular its exact square-root bound fails in both directions.
