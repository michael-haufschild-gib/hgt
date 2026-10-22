# HB modular-superselection charged-unitary bypass no-go

- **ID:** HC87
- **Stage:** 3-formalized
- **Type:** CONJECTURE / REPRESENTATION-FRACTURE NO-GO
- **Source:** read-only `rh-current-frontier-map.md` · HC86 charged double-KMS escape · existing Hawking modular-superselection endpoint

## Goal

Attack the hardest surviving objection to HC86. Existing source-modular superselection proves that,
at positive Hawking charge, no finite-Rees-moderate scalar operator family sews the reflected prime-
valuation profiles. Determine whether that obstruction also forbids charge conjugation in the
actual doubled thermofield Hilbert space.

Construct the coordinate-transposition unitary on `lp (fun _ : ℕ × ℕ => ℂ) 2`. Prove it maps the
HC86 visible charged double-KMS half-density exactly—not merely coefficientwise or up to phase—to
the partner half-density for every resonance and prime. Then prove this exact bounded unitary swap
coexists, at every positive-charge resonance, with the full Xi source-modular superselection
certificate and with failure of occupation-preserving alignment. Finally combine the exact unitary
swap with the existing no-finite-Rees scalar-sewing theorem in one unconditional statement.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` `ThetaCuspHawkingModularSuperselectionEndpoint` constructs an actual positive-charge
  Xi right-half copy and proves both a complete source-modular certificate and failure of every
  finite-Rees-moderate scalar sewing family.
- `[CORPUS]` `XiSourceModularTypeSuperselectionLaw` separates the scalar valuation profiles at
  charges `q` and `-q`; it does not assert irreducibility of every representation containing them.
- `[CORPUS]` HC86 constructs normalized visible and partner vectors in the same doubled
  `lp (ℕ × ℕ) 2` space and proves coefficient isospectrality under `(k,l) ↦ (l,k)`.
- `[CORPUS]` `HTGeometry.WoldThermofieldStandardForm.lpReindexEquiv` turns every index equivalence
  into an exact linear isometric equivalence of `lp` spaces.
- `[CORPUS NEGATIVE]` mandatory searches found no theorem connecting the Hawking modular
  superselection certificate to an irreducibility/no-charge-swap conclusion, and no theorem proving
  coexistence of finite-Rees scalar no-sewing with an exact doubled-sector unitary conjugation.

## Conjecture HC87-A: exact charged-sector unitary

Let `S` be `lpReindexEquiv (Equiv.prodComm ℕ ℕ)`. Prove

`S (visibleChargedDoubleKMS r p) = partnerChargedDoubleKMS r p`

as equality of actual `lp` vectors, for every resonance `r` and prime `p`. This strengthens HC86
from equality of squared coefficients after a swap to exact unitary equivalence.

## Conjecture HC87-B: positive-charge certificate coexists with the bypass

For every positive-charge resonance, construct the Xi right-half zero copy supplied by the corpus
and prove simultaneously:

- spectral and charge identification;
- physical port-dissipation identity;
- full source-modular superselection certificate;
- exact unitary charged-sector swap for every prime;
- failure of occupation-preserving alignment for every prime.

## Conjecture HC87-C: representation fracture

For every positive-charge resonance, every finite Rees grade `K`, every Rees-moderate scalar family
`R`, and every prime `p`, prove simultaneously:

- `R` cannot sew the positive and negative prime-valuation profiles;
- the doubled-space unitary `S` exactly maps the visible vector to its partner.

Thus scalar superselection no-sewing and bounded charged-sector conjugation are compatible facts,
not contradictory alternatives.

## Paper proof

For `(k,l)`, `lpReindexEquiv` for product commutation evaluates the input vector at `(l,k)`.
HC86 defines the visible coefficient there as the product of partner-indexed factors in reverse
order relative to the partner coefficient at `(k,l)`; commutativity of complex multiplication gives
pointwise equality. `lp.ext` gives exact vector equality, and the reindexing equivalence is unitary
by construction.

At positive charge, instantiate the existing modular-superselection certificate. HC86 classifies
occupation-preserving alignment iff horizon charge is zero, so positivity refutes it for every
prime. The existing finite-Rees theorem supplies scalar no-sewing for arbitrary grade and moderate
family. Pairing these closed theorems with the exact unitary equality proves coexistence.

## Hostile checks

- Use the actual corpus `lp` linear isometric equivalence, not an abstract existential unitary.
- Prove equality of vectors, not only norms, spectra, or squared coefficients.
- Preserve the distinction between scalar finite-Rees sewing and doubled-space coordinate
  conjugation; do not claim the former theorem is false.
- Do not infer that every physical source admits a charged doubled representation. Conclusion is a
  logical no-go: current modular certificate alone does not exclude the explicit HC86 escape.
- No RH premise, computation, finite cutoff, new axiom, `sorry`, or `admit`.

## Expected route impact

If proved, HC87 kills source-modular superselection by itself as the missing HB charge-sector
eliminator. The obstruction is representation-relative: it separates scalar reflected profiles but
does not forbid their exact unitary conjugation after doubled charge completion. A surviving RH
producer must establish a source-faithful representation-selection or phase/Ward law that rules out
the doubled swap, rather than cite superselection alone.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Doplicher--Haag--Roberts,
  [*Local Observables and Particle Statistics I*](https://doi.org/10.1007/BF01877742), develops
  superselection sectors and charge conjugation in local quantum field theory, not this arithmetic
  finite-Rees/doubled-`lp` coexistence theorem.
- `[LITERATURE]` Guido--Longo--Roberts--Verch,
  [*Charged sectors, spin and statistics in quantum field theory on curved spacetimes*](https://arxiv.org/abs/math-ph/9906019),
  treats conjugate charged sectors and modular covariance near bifurcate horizons, without the
  theta-source/Hawking charge or finite-Rees obstruction here.
- `[LITERATURE]` Chapman--Chen,
  [*Charged Complexity and the Thermofield Double State*](https://doi.org/10.1007/JHEP02(2021)187),
  gives charged thermofield-double factorization, not a theorem comparing it to an arithmetic
  modular-superselection sewing obstruction.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining scalar finite-grade superselection no-sewing, exact unitary doubled-sector conjugation,
  and the source-specific charge/RH classification. This is a bounded audit, not an exhaustive
  literature claim.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingModularSuperselectionChargedUnitaryBypassNoGo`.

- `thetaCuspHawkingChargedDoubleKMSSwapUnitary` is the explicit corpus `lp` reindexing unitary for
  product-coordinate transposition.
- `thetaCuspHawkingChargedDoubleKMSSwapUnitary_visible_eq_partner` proves equality of the actual
  visible and partner vectors after applying that unitary, not only equality of coefficient norms.
- `thetaCuspHawking_positiveCharge_scalarNoSewing_and_chargedUnitarySwap` proves scalar finite-Rees
  no-sewing and exact doubled-space conjugation simultaneously.
- The closed theorem `thetaCuspHawkingModularSuperselectionChargedUnitaryBypass` packages the full
  positive-charge Xi modular certificate, physical charge/dissipation identities, exact unitary
  swap at every prime, failure of occupation-preserving alignment, and arbitrary-grade scalar
  no-sewing.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingModularSuperselectionChargedUnitaryBypassNoGo`
passed all 10,999 jobs. Representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules and
no HC87 finding. Module is wired into the `GaloisForLFunctions.RHTower` umbrella without running a
full umbrella build.

## Open core after HC87

Source-modular superselection alone is dead as the charge-sector eliminator: its strongest scalar
no-sewing theorem coexists with exact unitary conjugation in the charged doubled representation.
The remaining hard producer must select the physical representation or retain phase information
destroyed by occupation probabilities. Next audit targets the corpus phase-sensitive chiral Ward
and tilted-backreaction laws: determine whether they exclude the swap, or whether a conjugate
phase twist gives another exact escape.
