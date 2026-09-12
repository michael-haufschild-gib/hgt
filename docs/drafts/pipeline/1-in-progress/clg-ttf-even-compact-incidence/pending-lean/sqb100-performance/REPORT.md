# SQB100 Lean resource audit

The installed proof is `HTGeometry.evenCompactUnitLastRow_at_one_ge` in
`formal/GaloisForLFunctions/HTGeometry/PolynomialODEEvenCompactLastRowAtOne.lean`.
For `r=1` and `0≤t,v≤1`, one signed last-row expression, including the complete
source correction, is at least `1/100`. The other signed rows, remaining drift
values, compact matrix positivity, all-rank extension, and RH remain open.

The proof shares integer coefficient certificates through public modules,
reconstructs monomials symbolically, and checks 117 scalar signs in nine separate
columns. This replaces the stopped four-variable expansion. All coefficient
normalization occurs in Lean with retained equality proofs.

| Check | Result | Sampled physical footprint |
| --- | --- | --- |
| 24 separate installed `lake env lean` checks | All pass | Maximum 502.9 MiB |
| Original-source capstone check | Pass, 5.91 s | 451.7 MiB |
| Exact capstone `lake build` | Pass, 10.94 s | 453.3 MiB |
| Formal lint | One unrelated unreachable module: `HTGeometry.InversePowerCancellation` | — |

Each check used one Lean worker, a 90-second wall-time cutoff, and the attached
guard's 512 MiB sampled physical-footprint cutoff. The guard reads macOS
`proc_pid_rusage` counters at roughly 0.1-second intervals; values are sampled
peaks, not a guarantee about between-sample transients. The final Lake audit
registered only the capstone root and reused existing dependency artifacts.
No full or umbrella build ran. All 25 completed check records report no remaining
owned processes; a final process check also found none.

`sqb100_install_map.json` maps scratch names to installed modules. The
`sqb100_install_*.json` records and matching logs cover all installed checks;
`sqb100_final_audit_guard.*` covers the exact leaf audit. The complete lint output
is `sqb100_formal_lint.log`. Earlier scratch records retain their own outcomes
and measurement limitations; the installed records above are authoritative for
the final proof architecture.
