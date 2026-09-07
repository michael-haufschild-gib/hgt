# Middle-prime energy with the fixed scalar reserve removed

RunPod-only diagnostic, 2026-09-07. No numerical result is a Lean premise.

## Question and method

After processing the core of primes below eight, process remaining primes in
increasing order up to the square-root threshold. Subtract from nonempty
energy the complete fixed scalar reserve carried by primes p with M<8p.
Does this remaining field contract, or stay below the original diagonal in
the inspected range? Existing diagnostics through cutoff 32 do not answer
this question at the growing middle-prime stages.

The exact clipped channel formula from the corpus's earlier `screen.py` is
used with NumPy long-double arithmetic. Oriented coordinates remove only
Möbius label parity; their squares equal the actual retained fibre squares.
Each stage uses `v_R <- v_R-v_(pR)` and deletes the absorbed coordinates.
Every stage checks the independent nonempty-energy identity
`delta V=-2 sum_(R nonempty) v_R v_(pR)-v_p^2`.

The fixed geometric sample contains 21 cutoffs from 1024 through 1048576. All
stages in each selected increasing order are retained. No subset cube or
exhaustive order search is performed. The diagnostic also separates
nonscalar labels and records leading source-labelled mixed contributions.

## Execution and artifacts

- Host: `ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519`.
- Execution directory (removed after verified download): `/root/ccm_fu_middle_prime_energy_20260907_01a077d3`.
- Foreground command: `timeout 180s python3 screen.py`.
- Eight forked workers on a 16-core host; shared read-only source arrays;
  BLAS/OpenMP restricted to one thread per worker.
- Completed in 1.653 seconds, NumPy 1.24.4. No timeout or background job.
- Downloaded [stages.csv](stages.csv), [summary.json](summary.json), and
  [report.md](report.md). The exact script is [screen.py](screen.py).
- All four local SHA-256 hashes matched their remote originals. The remote
  script, outputs, and execution directory were then removed; no owned
  computation process remains.

## Findings and limits

At the sampled cutoff 655360, the maximum remaining energy is about 1.03109
of the original diagonal; at 1048576 it is about 1.20762. This is not a claim
about the first failing integer cutoff. At 1048576 the maximum occurs after
prime 293; its remaining energy is about 0.00143047 M², while its nonscalar
part is much smaller. There are 60 increasing middle-prime steps there.
The largest step is prime 47; its dominant positive energy contributions
pair negative oriented singleton parents with positive joint partners.
The maximum absolute error in the stage identity at that cutoff is below
`5.7e-10`, against energies on the order of `1e9`.

These observations disfavor an original-diagonal bound for this particular
middle order, even after consuming every fixed scalar coordinate. They do
not prove divergence, failure of a larger fixed quadratic bound, or failure
of adaptive orders. The independent analytic proof establishes
nested child-head amplification at cutoffs 64N², with all primes below 4N
processed and retained primes in (8N,9N]. It proves divergence beyond every
fixed quadratic ceiling uniformly over all fixed scalar-reserve selections.
The [closed obstruction and positive survivor](../../../5-failed/ccm-fu-increasing-middle-scalar-reserves.md)
contain its complete paper proof and seven audited Lean theorems. General
adaptive orders and RH remain open.
