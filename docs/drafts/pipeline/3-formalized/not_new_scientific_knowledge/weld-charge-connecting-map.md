# T2: the connecting homomorphism from the weld cohomology to the deck-charge group

- **ID:** weld-charge-connecting-map
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` + formalized, axiom-clean
- **Source:** ../../door/bucket-the-seam-archimedean-obstruction.md · ../../door/G4-multi-q-picard-vessiot-and-langlands-group.md (compute-omega-h2-gl); builds on OmegaObstruction + DeckChargeCalculus
- **Statement (delivered):** `[PROVED HERE]`
  - `connectingHom T : H²(G,A) →+ A` — the connecting map `δ`: a coboundary-annihilating chain evaluates cohomology classes and the pairing descends (QuotientAddGroup.lift) to a genuine group homomorphism out of `secondConstraintCohomology`. Detects the obstruction (`δ class ≠ 0 ⟹ class ≠ 0`).
  - `chargeConnectingHom T n : H²(G,ℤ) →+ ZMod n` — composite with `ℤ ↠ ℤ/n`; its value on any class is a deck charge `wCharge n (T.eval ω)`.
  - `exists_weldClass_chargeConnectingHom_eq`: for every `n` and `idx`, `wCharge n idx` is `δ_charge` of an EXPLICIT weld class (the symplectic 2-cocycle `ω(g,h)=idx·g₁·h₂` on ℤ², whose commuting-pair antisymmetry is `idx`). The whole deck-charge calculus lies in the image of `δ`.
- **Lean:** `GaloisForLFunctions.RHTower.connectingHom`, `chargeConnectingHom`, `chargeConnectingHom_obstructionClass`, `exists_weldClass_chargeConnectingHom_eq` in `formal/GaloisForLFunctions/RHTower/WeldChargeConnecting.lean`. `#print axioms` = {propext, Classical.choice, Quot.sound}. `lake build` green.

## Terminalized verdict on the literal "two-faced obstruction"
The literal conjecture — that one class δ identifies the specific `𝓜⁺` weld obstruction with `ξ`'s ladder charge — is NOT asserted, and is presumed FALSE by the banked decoupling (`ω = 0 ⇏ RH`; DSS and RH are independent seam-joined apexes). If a homomorphism sent the weld class to the ladder charge, `weldClass = 0` would force `ladderCharge = 0` ⟹ a rung of RH — contradicting decoupling. What IS true and now proven: the connecting map `δ` exists as a genuine homomorphism, its target is exactly the deck-charge group, and the entire charge calculus is realized in its image. The weld obstruction and the deck charge are two faces of one **framework** (cocycle-evaluation charges), not one class. This refines T2 from a (false) identity to a (true) shared-mechanism theorem.

## Log
- 2026-07-07 — created directly in 3-formalized (connecting hom built + realization proved + Lean).
