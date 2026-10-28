# The archimedean place pays the tower deficit

- **ID:** rapt-archimedean-place-pays-the-tower-deficit
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RAPT open topic 2 ("who pays the tower deficit"), B3.28 (small-prime deficits `2d_p`);
  `RenormalizedArithmeticPotentialTheory/TheFinitePartIsTheTowerForm.lean`,
  `TheSignOfTheTowerFinitePart.lean`; ALG `TheMetzlerDichotomy.lean`.
- **Statement:** On every combination `x = Σ_{j ≤ J} a_j w_j^{(M)}` of `p`-adic class pole vectors,
  eventually in `M`, `P_M(x) ≤ (log M − γ + η)|x|²`; the pole vector attains `log M − γ`. In
  normalized coordinates `F_p(b) + Σ_j j log p · b_j² ≥ (γ + γ_p)|b|²`.

## Mechanism

The horizon counterterm on class `j` is `log(M/p^j) + γ_p`; the archimedean self-energy is
`log(1/w)` on every atom. Against the latter the prime form keeps the valuation potential
`j log p`. With masses `m_j = |w_j|²`:

1. `m_{j+1} ≤ m_j/p` exactly: `m_j = U(⌊M/p^j⌋)/p^j` with `U` the `p`-coprime harmonic sum.
2. The matrix with diagonal `−m_j(j + 1/(p−1))` and off-diagonal `m_{max(j,j')}` is Metzler, and its
   row sums against the constant weight are `−m_j/(p−1) + Σ_{j'>j} m_{j'} ≤ 0` by (1). The Metzler
   stability regime gives `Σ_{j≠j'} a_j a_{j'} m_{max} ≤ Σ_j a_j² m_j (j + 1/(p−1))`.
3. RAPT's class finite part: `P_M(x) = Σ_j (a_j m_j)²/δ_j − 2γ_p Σ a_j² m_j + log p Σ_{j≠j'} a_j a_{j'} m_{max} + O(η m + C)`
   and `m_j/δ_j ≤ log M − j log p + γ_p + η`. The `−j log p` of (3) cancels the `j` of (2), and
   `γ_p − log p/(p−1) = γ` remains.
4. Normalized coordinates (`m_j = p^{−j}`): `log p(K_q − I)(b) ≤ log p Σ_j b_j²(j + 1/(p−1))`.

Exact eigenvector (paper, numerically confirmed): `H_p = diag(j log p) + γ_p + log p − log p K_{p^{−1/2}}`
satisfies `H_p v = γ v` for `v_j = p^{−j/2}` on the infinite tower; Z-matrix with positive
eigenvector, so `γ` is its ground energy.

## Significance

RAPT's sign law leaves the deficit `2d_p > 0` for `p ≤ 43`. Matched against the archimedean place
instead of the class-wise horizon counterterm, no deficit remains: every `p`-class profile has
prime finite part at most that of the pole vector (`−γ` relative to `log M`). The pole is the
extremal class profile; the critical spacing constant on class profiles is decided by the pole
alone, where the pole term `2C²` acts.

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheArchimedeanPlacePaysTheTowerDeficit.lean`.
Declarations: `sum_cross_le_valuation`, `classMass_succ_le`, `towerFinitePart_add_valuation_ge`,
`eventually_atomicWeilForm_classCombination_le`, `eventually_atomicWeilForm_truncPole_ge`.

Open: several primes at once (Kronecker sum `H_Q = Σ_q H_q − (|Q|−1)γ`, ground energy `γ`), the
archimedean cross terms on class profiles, and transfer from class profiles to all atomic tests.
