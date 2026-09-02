Brick 142 completed for Route E E3 shared Kloosterman frontier.

New leaf:
formal/GaloisForLFunctions/RHTower/Sieve/KloostermanGlobalCollisionElementary.lean

Public theorems:
- card_sigma_erase_eq_card_mul_pred
- normSq_kloostermanGlobalModulusTimeResponse_le
- average_normSq_kloostermanGlobalModulusTimeResponse_mul_le
- kloostermanGlobalFrequencyCollisionEnergy_le_elementary

Capstone:
E_global <= (#Q * (#Q - 1)) times the ordered erased-diagonal sum of normSq weights and
(q+1)^2*(r+1)*source-residue energies.

This is an unconditional exact elementary fourth-moment baseline, not a Kuznetsov saving.
Direct lake env lean check passed.
Targeted leaf build passed 13506/13506.
All four public theorem axiom audits returned only [propext, Classical.choice, Quot.sound].
Leaf wired into formal/GaloisForLFunctions/RHTower.lean; umbrella not built.
Cards and matomaki-teravainen-e3-lean-programme updated.
Remaining core: collective cross-modulus Kuznetsov saving over this baseline, then Lemma 3.5(ii),
amplification, and Theorem 1.2.