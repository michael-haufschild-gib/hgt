# Validation of trivial-root components and reserved heights

All 14 selected repetitions completed. At both 100 and 160 digits, the large target circle fixed −2, exchanged the tested members of −6/−8 and −14/−16, fixed −18, and carried positive zeros 128 and 320 to their predecessors. The small circle carried −2 to −4.

These paths used smaller steps than discovery. An independent Euler–Maclaurin implementation checked nine spread locations with two truncations and 70 guard digits. The largest 160-digit independent target residual was 3.518e-148. This is selective numerical validation, not a certified enclosure of an entire path or a proof of the complete finite map.

The geometric lesson is that one loop has different kinds of zero components: fixed roots, exchanges and a long sampled predecessor chain. A global RH argument cannot identify all components with one observed pattern. The surviving question is what arithmetic determines those components and whether it constrains the distinguished zero fibre. No such rigidity was established here.

Run `python guard.py experiment.py` with the recorded environment. Inputs, raw paths, independent checks and original checksums are included. No Lean builds.
