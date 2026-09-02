Brick 143 completed for Route E E3 shared Kloosterman frontier.

New leaf:
formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalCollisionInterval.lean

Public theorems:
- sum_normSq_kloostermanSourceResidue_Icc_le_interval
- kloostermanGlobalFrequencyCollisionEnergy_Icc_le_elementary

First theorem cancels the common positive modulus factor from existing
kloostermanSourceResidueEnergy_Icc_le_intervalBudget:
raw residue normSq sum <= exact residueMultiplicity(q,N) * source L2 on Finset.Icc 1 N.

Capstone substitutes both source legs into brick 142, retaining exact #Q*(#Q-1), weights,
(q+1)^2*(r+1), both exact occupancies, and both source energies.
No support, injectivity, size, coprimality, or analytic premise.
Direct lake env lean check passed.
Targeted build passed 13507/13507.
Both axiom audits only [propext, Classical.choice, Quot.sound].
Leaf wired into RHTower umbrella; umbrella not built.
Cofactor, forbidden-support, and E3 programme docs updated.
Remaining core unchanged: collective Kuznetsov saving, Lemma 3.5(ii), amplification, Theorem 1.2.