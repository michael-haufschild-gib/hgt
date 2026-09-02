Brick 144 completed.

New leaf:
formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalCollisionWeighted.lean

Public theorems:
- normSq_kloostermanGlobalCollisionTimeTransform_le_weightPairResponseEnergy
- kloostermanGlobalFrequencyCollisionEnergy_le_weightPair
- kloostermanGlobalFrequencyCollisionEnergy_Icc_le_weightPair

Dependent erased-pair Cauchy separates modulus weights before period averaging:
normSq timeTransform <= WeightPairEnergy * sum response pair normSq.
Then brick 142 pair averages give:
E_global <= WeightPairEnergy * sum_(q != r) (q+1)^2*(r+1)*Eq*Er.
Literal Icc theorem substitutes exact residue multiplicities from brick 143.

This complements, rather than universally dominates, raw pair-cardinality brick 142.
Direct check passed. Targeted build 13508/13508 passed.
All 3 new theorem axioms: [propext, Classical.choice, Quot.sound].
Umbrella wired, not built. Docs updated.
Remaining: collective signed Kuznetsov saving, Lemma 3.5(ii), amplification, Theorem 1.2.