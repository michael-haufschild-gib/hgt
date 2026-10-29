# Affine unit averages for successor corrections

Status: proof design; formalization pending. No prime asymptotic claimed.

For the actual Ramanujan sum `c_m`, prove the finite identity

`Σ_{0≤r<m, (r,m)=1} c_m(r n+h) = c_m(n)c_m(h)`.

The normalized Ramanujan mode is consequently an eigenfunction of unit-averaged
successor dilation, with eigenvalue `c_m(h)/φ(m)` after averaging. This is the
finite arithmetic input required by the proposed overlap correction. It is a
classical finite-character identity, not a new estimate of prime correlations.

Proof: express `c_m(rn+h)` as a sum over primitive roots. For each primitive
root `ζ`, its powers `ζ^r` over reduced residues permute all primitive roots.
Sum first over `r` and factor the remaining root sum. Existing corpus source
`ArithmeticEffectivityTheory/TheArchimedeanComputationOfTheLogTorsion.lean:69`
contains the relevant image parametrization; adapt its argument to arbitrary
primitive roots and complex-valued sums. The complex-to-real bridge is already
in `TransThresholdPairCorrelation/ParitySensitiveRamanujanStabilizerTransfer`.

Planned module: `CriticalArithmeticCorrelationTheory/UnitAveragesDiagonalizeSuccessorCorrections.lean`.
No positivity or weighted-prime limit follows without additional source work.
