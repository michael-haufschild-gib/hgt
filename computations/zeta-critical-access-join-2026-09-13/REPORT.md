# Joining the critical graph to the access map

This mixed experiment combined two independent numerical datasets: a graph whose edges connect the zero endpoints of critical-point inverse branches, and the finite/escape-like access classification near the value 1. It required only a small graph calculation; no artificial parallel workload was added.

The 42 observed critical points give 22 graph components on labels 1–64. Under each of the three approach directions, 18 components contain exactly one escape-like vertex. Four contain none: the isolated vertices 29, 38, 55 and 59. No component contains multiple escape-like vertices. Removing the nonadjacent edge 57–60 creates a fifth component without an escape-like vertex.

The frozen claim that every observed component contains exactly one escape-like vertex therefore fails. Its positive residue is unusually specific: four isolated finite-access vertices account for all exceptions. They provide targets for an independent, access-guided search for critical points missed by the original Newton starts. Missing edges remain a hypothesis, not an explanation already established.

Although the total access counts stay at 18 and 46, 27 zero labels change classification when the approach direction changes. Thus the access type is not, in this sample, a direction-independent attribute of a zero. That distinction matters for any proposed arithmetic labelling of inverse branches.

For RH, this supplies a possible computational dictionary between critical incidences and asymptotic accesses, with explicit failures to test. It supplies no theorem converting that dictionary into critical-line confinement. Both the graph and access classes remain finite numerical objects; a complete critical-point census and an infinite-tract certificate are absent.

Run `python guard.py experiment.py`. Exact input datasets, hashes, all six comparisons and source-method search are retained. No Lean builds or random sampling.
