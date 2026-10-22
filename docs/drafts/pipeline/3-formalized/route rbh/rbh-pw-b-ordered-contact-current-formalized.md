# RBH / PW-B ordered contact-current compatibility — Lean certificate

- **Paper card:** `rbh-pw-b-ordered-contact-current.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsOrderedCurrent`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old env lean` clean; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| source contact `C(s,a;t,b) = -C(t,b;s,a)` face by face | `liftContact_ctp_swap` |
| completed angular current skew | `liftAngularCurrent_ctp_swap` |
| Einstein current skew, from `EinsteinCurrent + SourceContact = AngularCurrent` | `liftCurrent_ctp_swap` |
