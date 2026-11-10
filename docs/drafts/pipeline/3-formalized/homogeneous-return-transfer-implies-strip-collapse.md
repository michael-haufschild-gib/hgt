# Homogeneous return transfer implies strip collapse

- **ID:** A75
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The proposed uniform S3 return-to-window transfer implies `Θ<1 → RH`, hence `Θ<1 → Θ=1/2`.

## Proof

A strip of depth `h<1/2` gives `log t≥c y^d` for heavy identity returns, where `d=1/2−h>0`. Set `A=2/d` and retain the exact cutoff `y=⌊T^A⌋`. Eventually `y≥T^A/2`, so every return has `log t≥c2^{-d}T²>ηT`. Thus no heavy return occurs in `[T₁,exp(ηT)]`. The proposed transfer supplies a uniform absolute prime-trace bound on every late log-square window. The signed window criterion gives RH.

The theorem proves the implication from the transfer; it does not assert or prove the transfer.

## Formalization

- Module: `SignFreePurityMechanisms/HomogeneousReturnTransferImpliesStripCollapse.lean`.
- Declarations: `eventually_noHeavyIdentityReturn_of_strip`, `homogeneousReturnWindowTransfer_implies_quasiRH_collapse`, `homogeneousReturnWindowTransfer_implies_abscissa_collapse`.
- Direct `lake --old env lean` audit passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `SignFreePurityMechanisms.lean`.
