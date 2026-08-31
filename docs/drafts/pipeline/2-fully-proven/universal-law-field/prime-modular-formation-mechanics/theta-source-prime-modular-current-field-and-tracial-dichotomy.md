# Theta-source prime-modular current field and tracial dichotomy

- **ID:** ULF-PMFM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md`; ULF-ODTM-5/6; theta prime translation; seam-spectrum density; source-modular superselection
- **Statement:** The theta root-current reflection double carries an exact prime-modular action commuting with current recovery, and its group-completed prime modular spectrum is either the singleton `{1}` on the critical line or all positive scales off it.

## Goal

Construct one route-independent object combining four previously separate organs:

1. the functional-equation action on complete theta-source root blocks;
2. the nonzero conormal/socle current with exact global recovery;
3. the literal reciprocal energies of normalized prime translation;
4. the dense prime-log weld spectrum.

The resulting object must explain why reflection, positivity, bounded current sewing, and reciprocal
energy conservation do not themselves select the critical line. It must also isolate a stronger
formation law that would select it without disguising an RH-equivalent receiver as a producer.

## Gates

- [x] 0 → 1 in-progress: source-pure objects, exact intervention action, and Door passport identified
- [x] 1 → 2 fully-proven: complete proof below; all dependencies already proved in the corpus
- [x] 2 → 3 formalized: `HedenmalmThetaSourcePrimeModularCurrentField`; named leaf build and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit pending

## Construction

Let `rho` be one multiplicity-exact Xi divisor copy, let

`t_rho = 2 Re(rho) - 1`,

and let `mu_rho` be its nonzero theta-source reciprocal spectral point. Write

`P_rho = G_(mu_rho) ⊕₂ G_(-mu_rho)`

for the oriented functional-equation root-block double. The earlier root-current transport and
global sewing laws provide:

- a unitary involution `J_rho` exchanging the two blocks;
- a nonzero bounded diagonal conormal current `D_rho`;
- exact current covariance `J_rho D_rho J_rho = chi_rho D_rho`;
- exact recovery of the unnormalized local current from the global field.

For a prime `p` and a real formation rate `t`, define the positive modular dilation

`Delta_(p,t)(v,w) = (p^(-t/2) v, p^(t/2) w)`.

At `t=t_rho`, the squared amplitudes are exactly the literal normalized theta-source translation
energies of `rho` and its functional-equation partner.

Let `Lambda = <log p : p prime>_Z` be the group-completed prime-formation rate lattice and define

`Sigma_rho = closure { exp(t_rho lambda) : lambda in Lambda }` inside `R_(>0)`.

This is the positive modular spectrum of the source-formation sector. “Type III” below is only an
analogy to modular-spectrum shape; no von Neumann factor is asserted or assumed.

## Theorem `[PROVED HERE]`

For every theta-source Xi sector `rho` and every prime `p`:

1. **Reversibility:** `Delta_(p,t) Delta_(p,-t) = 1`.
2. **Modular reflection:** `J_rho Delta_(p,t) J_rho = Delta_(p,-t)`.
3. **Current compatibility:** `D_rho Delta_(p,t) = Delta_(p,t) D_rho`.
4. **Literal source-energy law:**

   `||Delta_(p,t_rho)(v,w)||² = E_p(rho)||v||² + E_p(rho*)||w||²`,

   where `E_p(rho)=p^(-t_rho)`, `E_p(rho*)=p^(t_rho)`, and their product is one.
5. **Prime modular-spectrum dichotomy:**

   - if `Re(rho)=1/2`, then `Sigma_rho={1}`;
   - if `Re(rho)≠1/2`, then `Sigma_rho=R_(>0)`.

Hence `Sigma_rho={1}` iff `Re(rho)=1/2`. There is no intermediate closed positive modular phase.

## Proof

Items 1–3 are fibrewise identities. Multiplying the two diagonal amplitudes gives

`p^(-t/2)p^(t/2)=1`,

so the inverse is `Delta_(p,-t)`. The functional-equation involution exchanges the two summands;
therefore it exchanges the two amplitudes and conjugates `t` to `-t`. The conormal current acts
diagonally and complex-linearly on each summand, so scalar modular dilation commutes with it.

For item 4, the `L²` product norm gives

`||Delta_(p,t)(v,w)||² = p^(-t)||v||² + p^t||w||²`.

The theta prime-translation theorem identifies these two coefficients at `t=t_rho` with the
literal source energies at `rho` and its reflected copy. This is not a fitted character.

For item 5, the corpus proves that `Lambda` is dense in `R`: already `log 2` and `log 3` have
irrational ratio, hence their integer span is dense. If `t_rho≠0`, multiplication by `t_rho` is a
homeomorphism of `R`, so `t_rho Lambda` remains dense. Exponentiation is a homeomorphism from `R`
to `R_(>0)`, hence `exp(t_rho Lambda)` is dense in every positive scale and its closure is all of
`R_(>0)`. If `t_rho=0`, every value is `exp(0)=1`, so the closure is `{1}`. Finally,
`t_rho=0` iff `Re(rho)=1/2`.

All arguments are unconditional. The proof uses no RH premise, no zero enumeration, no
divisor-dependent metric, and no assumed boundedness of a nonunitary orbit.

## Fusion and prediction

This law fuses structurally different organs rather than identifying their scalar endpoints:

- **operator/root organ:** complete generalized theta root blocks and their terminal Jordan current;
- **functional-equation organ:** information-neutral unitary reflection;
- **arithmetic intervention organ:** literal normalized prime translation energies;
- **weld/hypertranscendental organ:** gapless dense prime-log formation history.

It predicts a new theorem in the modular-superselection organ: a single off-wall source charge does
not create a small deformation of the tracial sector. Group-completed prime formation immediately
fills every positive modular scale. Thus all local reciprocal, Krein, KMS, positivity, and bounded
current constructions are local gauges of one nontrivial modular sector; their no-gos are shadows
of trying to turn modular conservation into traciality.

## Exact remaining selection law

Global tracial collapse

`for all rho, Sigma_rho={1}`

is equivalent to the global critical-line statement and therefore is a receiver, not yet a source
producer. The new field changes the open question:

> Construct a divisor-independent source-formation trace/descent law that is faithful on the
> recovered conormal current and forces the prime modular spectrum to be trivial.

Such a theorem cannot be replaced by positivity, reciprocal conservation, an invariant Krein form,
bounded normalization, or functional-equation symmetry: all coexist with the maximally noncompact
off-wall modular sector proved above. A viable producer must derive traciality from formation
incidence/properness before selecting a divisor point.

## Door passport

- **Source purity:** theta kernel, its root blocks/current, literal integer/prime translations, and
  the prime-log weld lattice only.
- **Multiplicity:** retained by complete generalized root blocks and conormal current.
- **Reflection:** internal unitary involution; no copy is discarded.
- **Prime labels:** retained before group completion; all-prime completion is used only for the
  spectrum theorem.
- **Non-circularity:** modular dichotomy is unconditional. Global singleton spectrum is explicitly
  labeled RH-equivalent and is not assumed.
- **Novel output:** exact current-compatible modular action plus the singleton/all-positive-scale
  dichotomy; no intermediate source modular phase.

## Log

- 2026-08-31 — complete paper proof; promoted directly to Stage 2 after corpus overlap audit
- 2026-08-31 — formalized in Lean; capstones use only `propext`, `Classical.choice`, and `Quot.sound`
