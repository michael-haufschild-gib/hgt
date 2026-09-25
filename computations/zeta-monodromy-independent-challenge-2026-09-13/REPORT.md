# Independent inverse-geometry validation

All 14 selected runs completed and retained the endpoint identities found at 50 digits. Repeats used 100 and 160 digits, smaller continuation steps, and an independently implemented Euler–Maclaurin formula at saved path locations. The critical-point experiment also varied the displacement used to start its two inverse branches.

The largest independently evaluated target residual was 3.479e-86 at 100 digits and 8.189e-148 at 160 digits. Two Euler–Maclaurin truncations were compared. These numbers measure residuals; they are not certified error bounds or counts of correct digits. Formula checks cover selected path locations, not every point between them.

The selected connections therefore survive precision, step-size and evaluator challenges. They provide finite geometric information about actual zeta zeros. They do not prove that every inverse path was followed without a sheet change, establish a global connection graph, or confine all nontrivial zeros to the critical line.

For the larger RH problem, the missing step is a source-derived rigidity law for the fibre zeta(s)=0. Connections passing through nonzero target values do not supply such a law. The positive result is a reproducible set of finite connections that can now be tested against changes of access path and arithmetic carrier.

Run `python guard.py experiment.py` to reproduce the bounded experiment. Inputs, exact environment, original checksums, full paths and independent formula checks are included. No Lean build or unconditional proof claim was made.
