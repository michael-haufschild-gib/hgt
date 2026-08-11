# Choi shortcut fidelity forces energy-defect localization

- **ID:** `choi-shortcut-energy-defect-kurtosis-law`
- **Stage:** 3 — formalized
- **Type:** theorem / robust-shortcut bridge / gap-free approximate centralizer
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [FRONTIER BRIDGE] [NOVELTY UNVERIFIED] [NOT BROWN GROWTH]`
- **Date:** 2026-08-11

## Result

Let `H=H*` act on a nonzero `D`-dimensional space and define its normalized spectral kurtosis

\[
 \kappa_4(H)=
 {D\,\operatorname{tr}(H^4)\over \operatorname{tr}(H^2)^2}.
\]

Let `T` and `W` be unitary, with `HT=TH`, and let

\[
 F_{\rm Choi}(T,W)=
 {\left|\operatorname{tr}(T^*W)\right|^2\over D^2}.
\]

Then

\[
 \boxed{
 \|HW-WH\|_{HS}^4
 \le
 16\,\kappa_4(H)\,\operatorname{tr}(H^2)^2
       \bigl(1-F_{\rm Choi}(T,W)\bigr). }
 \tag{1}
\]

Equivalently,

\[
 \boxed{
 \|HW-WH\|_{HS}^2
 \le
 4\,\operatorname{tr}(H^2)
 \sqrt{\kappa_4(H)(1-F_{\rm Choi}(T,W))}. }
 \tag{2}
\]

Therefore

\[
 1-F_{\rm Choi}(T,W)\le {1\over16\kappa_4(H)}
 \quad\Longrightarrow\quad
 \boxed{\|HW-WH\|_{HS}^2\le\operatorname{tr}(H^2).}
 \tag{3}
\]

No minimum gap, nondegeneracy, operator-norm approximation, or dictionary-size assumption occurs.

## Exact transport proof

Diagonalize `H`, write its eigenvalues as `E_i`, and put `V=T^*W`.  The unistochastic matrix

\[
 p_{ij}={|V_{ij}|^2\over D}
\]

is a coupling of the uniform spectral measure with itself.  Its off-diagonal mass `q` obeys

\[
 q=1-{1\over D}\sum_i|V_{ii}|^2
 \le 1-{\left|\sum_iV_{ii}\right|^2\over D^2}
 =1-F_{\rm Choi}(T,W),                                      \tag{4}
\]

by Cauchy–Schwarz.  The commutator defect is its quadratic transport cost:

\[
 {1\over D}\|HV-VH\|_{HS}^2
 =\sum_{i,j}(E_i-E_j)^2p_{ij}.                              \tag{5}
\]

Because the diagonal contributes zero, Cauchy–Schwarz and
`(a-b)^4 <= 8(a^4+b^4)` give

\[
 \left(\sum_{i,j}(E_i-E_j)^2p_{ij}\right)^2
 \le q\sum_{i,j}(E_i-E_j)^4p_{ij}
 \le16q\,{\operatorname{tr}(H^4)\over D}.                 \tag{6}
\]

Multiplying by `D^2` proves `(1)`.  Since `T` commutes with `H`, left multiplication by `T^*`
preserves the Hilbert–Schmidt commutator energy, so the bound for `V` is exactly the bound for `W`.

## Fixed-locality consequence and remaining Lean obligation

The quantum Bonami–Gross–Beckner inequality of Montanaro–Osborne gives, for every Hermitian Pauli
polynomial of degree at most fixed `q`,

\[
 \|H\|_{4,\mathrm{norm}}\le3^{q/2}\|H\|_{2,\mathrm{norm}},
 \qquad \kappa_4(H)\le9^q.                                \tag{7}
\]

Thus the dimension-independent resolution

\[
 1-F_{\rm Choi}(T,W)\le {1\over16\,9^q}                   \tag{8}
\]

forces every robust fixed-`q` Choi shortcut into the half-energy tube.  Equation `(7)` is external
established mathematics, but it is not yet present in the Lean corpus.  It may not be used in a
final unconditional theorem until the finite Pauli hypercontractive corollary is formalized and
axiom-audited.

## Conjecturing loop and hostile audit

1. `[FALSIFIED]` Choi closeness plus the operator-norm estimate
   `||[H,W]||_HS <= 2||H||_op||W-T||_HS` is sufficient.  For extensive local Hamiltonians this
   loses the effective-rank factor and makes fixed robust error deteriorate with system size.
2. `[PROVED]` The right replacement is not a spectral gap but the spectral-tail profile.  Fourth
   moment already gives the dimension-free law `(1)`.
3. `[PROVED]` The result is selector-compatible: it applies to every selected circuit endpoint
   individually and contains no circuitwise probability union.
4. `[NOT PROVED]` Low defect does not itself make a circuit hard.  The autonomous target lies in the
   zero-defect sector identically, and fast-forwardable carriers remain possible there.
5. `[OPEN CORE]` After return and named carrier removal, prove quenched Bellman escape for the
   circuit selector restricted to this now legitimately certified low-defect sector.
6. `[NOVELTY]` Schatten/trace fidelity, unistochastic couplings, Cauchy–Schwarz, and quantum
   hypercontractivity are established separately.  Targeted searches found no prior theorem with
   the exact Choi-fidelity-to-Hamiltonian-commutator transport law `(1)`.  Priority remains
   unverified; no novelty claim is promoted.

## Lean certification

Module:

- `GaloisForLFunctions.HTGeometry.ChoiShortcutEnergyDefectKurtosisLaw`

Headline declarations:

- `doublyStochastic_quadraticTransport_sq_le_offDiag_fourth`;
- `finiteUnitaryDiagonal_commutatorEnergy_sq_le_fourthMoment_traceDefect`;
- `finiteUnitaryDiagonal_commutatorEnergy_le_traceEnergy_of_kurtosis`;
- `finiteUnitary_commutatorEnergy_le_traceEnergy_of_eigenKurtosis`;
- `finiteUnitary_choiShortcut_commutatorEnergy_le_traceEnergy_of_eigenKurtosis`.

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/ChoiShortcutEnergyDefectKurtosisLaw.lean` — pass;
- `lake build GaloisForLFunctions.HTGeometry.ChoiShortcutEnergyDefectKurtosisLaw` — pass;
- all five headline `#print axioms` results contain only `propext`, `Classical.choice`, and
  `Quot.sound`.

