# Pairwise doctrine compatibility implies joint realizability — failed

- **Stage:** 5-failed
- **Claim killed:** If every pair among two mandatory-identification formations and one fidelity
  doctrine has a common realization, then all three have a common realization.
- **Countermodel:** `P={0,1,2}`, conflict task `delta_0` versus `delta_2`, first formation
  `0~1`, second formation `1~2`.
- **Failure mechanism:** Each identification separately avoids the conflict edge.  Their generated
  join contains the path `0~1~2` and therefore collapses the conflict edge.  Every common observer
  loses total variation strictly, from `1` to `0` in the minimal model.
- **Positive survivor:** ULF-LSM-5 classifies joint realizability exactly: the equivalence closure of
  mandatory identifications must contain no task-conflict pair.  Every failure has a finite critical
  path, and compatible residual observer width is the chromatic number of the quotient conflict
  graph.
- **Do not reattempt as:** pairwise commuting closure operators.  ULF-LSM-3 already proves that
  strict pairwise-commuting formations have exact joint repair.  The countermodel uses a third,
  antitone separation doctrine rather than three commuting closures.
