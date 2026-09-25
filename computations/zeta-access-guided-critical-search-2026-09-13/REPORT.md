# Access information repairs a critical-point graph

The earlier mixed experiment isolated four zeros whose graph components had no escape-like vertex: labels 29, 38, 55 and 59. That discrepancy supplied the search locations for this experiment; it did not establish that missing edges existed.

The 120 prescribed starts produced 22 successful two-branch lifts and 98 Newton domain escapes. Four numerically distinct critical points were new relative to the original search. Their inverse branches reached the pairs 29–27, 38–40, 55–54 and 59–57. Thus every previously isolated vertex acquired a connection to an existing component. Three new edges are nonadjacent in height order.

Adding these four observed edges gives 46 edges and 18 connected components on the 64 sampled zero labels. Each component then contains one escape-like vertex for each of the three tested access directions. This last count follows from the combined finite data; it is not an independent theorem or a complete critical-point census. All four new edges passed a separate 16-run challenge at 100/160 digits, with two starting displacements, finer steps and independent Euler–Maclaurin checks. This selective validation does not make the graph complete.

The larger scientific gain is a working interaction between two viewpoints: an access map identified omissions in a local critical-point search. This suggests an adaptive reconstruction method and a precise finite graph/access dictionary. The dictionary's global status remains unknown.

For RH, reconstruction from cached critical-line zeros cannot prove that all zeros lie there. A proof would need a source-based construction covering the entire divisor, control of all critical and asymptotic accesses, and a theorem forcing critical-line confinement. The present result supplies a useful investigative method and explicit nonlocal connections, not those missing implications.

Reproduce with `python guard.py experiment.py`. All starts, failures, duplicate roots, critical values, paths and source inputs are retained. No Lean builds.
