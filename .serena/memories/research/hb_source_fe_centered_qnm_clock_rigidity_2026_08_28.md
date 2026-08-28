HC57 formalized in `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECenteredQNMClockRigidity`.

Result: after subtracting the fixed BM QNM overtone/redshift offset, centered frequency is `xiSpectralPoint/2`. Literal anti-linear source-FE transport `T_FE` has exact centered-clock anticommutator coefficient
[
i(\operatorname{Re}(Rr)-1/2)\,\kappa(Rr)\,\overline{x(Rr)}
]
at output copy `r`. Source cocycle is nowhere zero by its involutive law. Defect vanishes on a unit basis packet iff its Xi zero lies on critical line; global packet defect vanishing, equivalently `T_FE Gbar = -Gbar T_FE`, iff RH.

Files:
- formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSourceFECenteredQNMClockRigidity.lean`
- formalized card: `docs/drafts/pipeline/3-formalized/hb-source-fe-centered-qnm-anticommutator-rigidity.md`
- umbrella import: `formal/GaloisForLFunctions/RHTower.lean`

Audits: direct Lean passed; target-only build passed 11925/11925; all 11 public theorems depend only on propext, Classical.choice, Quot.sound; lint has no HC57 issue and only pre-existing unrelated umbrella-reachability failures.

Next hard producer: derive vanishing of this exact anticommutator from augmented Einstein/Teukolsky source dynamics, or prove a sharp unconditional obstruction and extract its strongest positive survivor. Frontier map remains read-only.