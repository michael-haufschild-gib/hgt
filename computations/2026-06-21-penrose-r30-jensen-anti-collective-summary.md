# Penrose R30 — Jensen Anti-Collective Margin Ordering

Random path:
- Seed RandomNode: `Correlations between reactants can alter effective reaction rates`.
- Step 1/2 topic: `Noise-induced phase transitions` (rng 5).
- Step 3/4 NODE: `Spatial coupling can convert local noise-induced bistability into a genuine collective phase transition` (rng 4).
- Standing-order target: `docs/consolidated/08-conjectures-required.md` (rng 1), candidate 16 (rng 16): `Jensen TP-defect = 2κ₋`.

Node validation:
- Coupled bistable lattice with fixed noise:
  - coupling `0.00`: domains `82`, nearest-neighbor sign correlation `-0.1714`.
  - coupling `0.35`: domains `20`, correlation `0.7143`.
  - coupling `0.90`: domains `8`, correlation `0.8857`.
- Coupling turns local bistable noise into coherent domains, validating the NODE constraint.

Step 8:
- Levenshtein selected `spatially_coupled_nonreal_jensen_roots` (`39`) over `noise_induced_jensen_tp_domain_transition` (`41`) and `coupled_jensen_defect_lattice_kappaminus` (`44`).

Step 9, method 9 (`Test small cases`):
- Built small cubic Jensen-section lattices from `J_3(X;t)` for `Ξ`, with local coefficient perturbations amplified at low hyperbolicity margin.
- Compared actual `t`-ordered margin field to shuffled-margin control.
- Result: actual order generally produced **fewer** non-real-root/TP defects than shuffled order.
  - `nsites=24`, `eps=1.1`, `length=2`: true count `3.922`, shuffled `4.744`.
  - `nsites=48`, `eps=1.1`, `length=5`: true count `7.411`, shuffled `9.156`.
  - `nsites=48`, `eps=1.3`, `length=8`: true count `8.378`, shuffled `10.278`.

Step 11, method 13 (`Find a monotone quantity`):
- Monotone quantity: suppression ratio `true_count / shuffled_count`; ratio `<1` means the actual Jensen margin order suppresses collective TP defects.
- Battery over windows `[5,80]`, `[80,155]`, `[155,230]`, lattice sizes `24,48`, eps `.9,1.1,1.3`, coupling lengths `0,2,5,8`; also compared sorted-margin adversarial order.
- Summary ratios:
  - `nsites=24`, `eps=.9`: `0.217,0.257,0.296,0.253`.
  - `nsites=24`, `eps=1.1`: `0.273,0.286,0.296,0.285`.
  - `nsites=24`, `eps=1.3`: `0.257,0.257,0.298,0.315`.
  - `nsites=48`, `eps=.9`: `0.319,0.294,0.230,0.266`.
  - `nsites=48`, `eps=1.1`: `0.307,0.282,0.307,0.274`.
  - `nsites=48`, `eps=1.3`: `0.345,0.338,0.350,0.298`.
- Later windows are almost protected in actual order while shuffled/sorted controls still create defects; e.g. `[80,155]`, `nsites=48`, `eps=1.3`, `length=8`: true count `0.278`, shuffled `3.533`, sorted `4.333`.

Promptability audit:
- Cold prompt predicted the generic NODE direction: coupling/aggregation should sharpen local Jensen ambiguity into an even-valued collective TP defect matching `2κ₋`.
- The computed result is the reverse: in actual `Ξ` cubic Jensen-section margin order, coupling does **not** nucleate the collective TP-defect phase as readily; shuffled or sorted margins do. The non-promptable content is this anti-collective ordering of the actual Jensen margin landscape.

Finding:
- `[EXPERIMENTAL FINDING / CONJECTURE]` The `Ξ` Jensen hyperbolicity-margin landscape appears anti-collective under local noise-induced TP defects: spatial coupling that would normally organize local bistability into domains instead sees the natural `t`-order suppress defect counts relative to shuffled/adversarial margin order. In target language, the Jensen TP-defect carrier has a margin-order firewall before the integer `2κ₋` phase can nucleate.
