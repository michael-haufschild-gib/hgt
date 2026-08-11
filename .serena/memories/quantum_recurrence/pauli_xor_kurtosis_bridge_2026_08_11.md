# Fixed-locality Pauli XOR kurtosis bridge (2026-08-11)

Formal module: `formal/GaloisForLFunctions/HTGeometry/PauliXorIncidenceHypercontractivityLaw.lean`, wired into `HTGeometry.lean`.

Result: An elementary phase-free XOR autocorrelation identity plus four-linear Cauchy--Schwarz tensorization proves `fourthIncidence c <= (9^q sqrt(cubeEnergy c))^4` for nonnegative coefficients supported on Pauli weight `<=q`. Exact Pauli multiplication/regrouping and Hilbert--Schmidt orthogonality then prove every real weight-q Pauli Hamiltonian has normalized spectral kurtosis `<= (9^q)^4`, independent of n. Composed Choi law: infidelity `<=1/(16(9^q)^4)` to any commuting target forces the shortcut into the half-energy commutator tube.

Verification: direct `lake env lean` pass; final module-only build pass; `scripts/formal_tools.py lint` pass; headline axioms only propext/Classical.choice/Quot.sound. Card: `docs/drafts/pipeline/3-formalized/pauli-xor-incidence-hypercontractivity-law.md`.

Hostile boundary: constant is deliberately weaker than standard sharp quantum hypercontractivity (`9^q` fourth-moment factor), so no external novelty claim for numerical strength. This closes only dimension-independent robust Choi-to-tube localization. Brown growth remains selector-aware quenched Bellman escape inside the low-defect sector after explicit return and fast-forwardable-carrier removal.