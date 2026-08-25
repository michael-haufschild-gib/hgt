Created formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingAIMEHorizonReciprocity.lean and imported it from RHTower.lean. No git used.

Novel mechanism:
- Raw d4 topological BH QNM branches have angular momentum z/2+i/4.
- Opposite branch-graded imaginary co-dilation omega_+ -> omega_+-ic, omega_- -> omega_-+ic preserves trace/common decay.
- Requiring physical QNM mirror relation omega_-=-conj(omega_+) on real centered z uniquely forces c=1/4. Canonical corrected branches are z/2-id and -z/2-id; gap is z.
- Horizon energy flux of a seed QNM decays at twice amplitude rate: Gamma_+=2d-Im z, Gamma_-=2d+Im z.
- Unit-absorbed-mass Duhamel projection across corrected gaps +/-z has denominators 2d-2 Im z+i Re z and 2d+2 Im z-i Re z.
- Reduced gain defect is exactly 16 d Im z/(D_+ D_-), where D_± are positive squared denominator norms at Xi points.
- Hence reduced reciprocal gain iff Im z=0; global all-Xi reciprocity iff RH.
- If full return is reciprocal, every tilted Xi sector requires nonzero unresolved-channel correction; closed two-branch return impossible off line.
- Hostile caveat: this does not prove full nonlinear Einstein-Teukolsky dynamics selects the quarter co-dilation or reduced reciprocity. Unit absorbed-mass/Jost-residue normalization is essential; raw spatial AIME weights can otherwise obscure the temporal defect.

Verification:
- targeted Lean compile passed.
- all 19 new theorems #print axioms: only propext, Classical.choice, Quot.sound.
- scripts/formal_tools.py lint recognizes module; only unrelated unreachable modules reported: HTGeometry.DenseFeatureGramUnitary, HardyDiskLineCayleyUnitary, SecondOrderConstraintDescent.
- /tmp scratch files removed.
Source basis: Birmingham-Mokhtari hep-th/0609028 exact d4 branches; Sberna et al. arXiv:2112.11168 Eq. 27 horizon flux exp(2 Im omega v), Eqs. 32/41 exponential mass history/AIME.
