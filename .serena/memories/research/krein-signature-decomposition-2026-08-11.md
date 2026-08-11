# Attempt 10: the square-realization construction, executed — Krein decomposition (2026-08-11)

Module `RHTower/GaussHodgeWeilKreinDecomposition.lean` (wired, built, axiom-clean, 7 theorems).
Card hodge-sign-wall-constructed-pairing, attempt 10.

The user asked for the square realization of xiWeilPolarization. Building it directly IS RH
(by the socket iff), so the honest execution formalizes what the construction produces and its
exact obstruction:
- Unconditional **Krein signature decomposition**: 4·Re W(F,F) = Σ‖pair sum‖² − Σ‖pair dif‖²
  for every square-summable test (both sector energies convergent). The Weil form is a
  Pontryagin-space form; positive sector = reflection-coherent evaluations, negative sector =
  reflection differences.
- The negative sector IS the loop's mass sector: its energy density at the prime test equals
  the centered cosh defect.
- The square realization exists ⟺ the negative sector is annihilated on every square-summable
  test ⟺ RH (elementary indicator witness at an off-line spectral point for the converse).

This closes attempt 2's Krein-definitizability survivor into theorems and gives the final
formal shape of Gate II: a producer (compressed trace, intersection form, spectral
realization) must rigidify this Pontryagin structure — force the negative sector empty — and
the socket + loop carry it to RH. Session total: 9 modules, 60 theorems, all axiom-clean.
Concurrent-session coordination: the frontier-map socket paragraph was reworded by another
agent ("receiver socket, not a square-realization theorem") and
GaussReciprocalCharacterAdmission.lean (virial normalization of the H-mass) joined the lane.
