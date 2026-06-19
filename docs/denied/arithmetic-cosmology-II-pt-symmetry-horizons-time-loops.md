# Arithmetic Cosmology II — PT-Symmetry, Horizons, and Closed Time-Loops

> **GRADE: EMBASSY** (per `00-charter-wall-and-door.md`; `00-manifest-wall-census.md`). *Metaphor / physics
> allegory — NOT native mathematics.* Fails Door-1/Door-2: PT-symmetry, exceptional points, quasinormal modes,
> causal sets are classical physics applied by analogy to classical arithmetic objects; the `q`-difference
> apparatus is nowhere load-bearing. Kept as inspiration; **must not be cited as the field's content.**

*Second embassy expedition (District D7; welds to the DeWitt construction and to
`arithmetic-cosmology-causality-inflaton.md`). Continues the open-minded mining of shared words and
allegories on the wild continent of `00-core-vision.md`, going to the next level of depth: where installment I
found that **RH is a causality condition**, this one finds the *operator* whose phase transition is RH (PT-
symmetry, with the no-margin as an exceptional point — certified), the rigorous **causality⟺analyticity**
handle, the **black-hole** reading the whole adventure began from, and the most literal time-and-space readings
(primes as closed time-loops; the zeros as a time crystal; the `ζ`-universe as a causal set). Air-marked,
embassy-grade. Two threads carry their own certification (§1, and the inherited §I); three new falsifiable
conjectures (§6). No proof of RH is claimed.*

Companions: `arithmetic-cosmology-causality-inflaton.md` (I: causality, handshake, `Λ`, inflaton),
`time-emergence-scale-clock-wheeler-dewitt.md` (Brick #1: the DeWitt pairing = Weil form),
`rh-holographic-pseudorandom-boundary.md`, `00-core-vision.md`.

---

## 1. The operator whose phase transition is RH: PT-symmetry and the exceptional point

Installment I read the off-line zeros as tachyons (acausal). The next question a physicist asks: *what
operator has a real spectrum exactly when the universe is causal?* The answer is a known and citable one —
**PT-symmetric quantum mechanics** (Bender–Boettcher 1998), and for the zeros specifically the
**Bender–Brody–Müller** Hamiltonian (PRL 2017), a non-Hermitian but PT-symmetric operator whose eigenvalues
are conjecturally the zeta zeros, with the implication *PT unbroken ⟹ real spectrum ⟹ RH*.

PT = **P**arity × **T**ime-reversal — and time-reversal `T` is precisely the actor this whole expedition is
about. A PT-symmetric operator has two phases:
- **PT unbroken:** spectrum **real** (the symmetry is shared by the eigenstates);
- **PT broken:** spectrum comes in **complex-conjugate pairs** (the eigenstates rotate into each other under
  PT).

This *is* the zeta trichotomy: on-line zeros are real (PT unbroken); off-line zeros come in
conjugate quadruples (PT broken). And the boundary between the phases is an **exceptional point** — a
non-Hermitian degeneracy where eigenvalues **and eigenvectors** coalesce and the operator becomes defective
(a Jordan block), not merely degenerate.

**Certified (`computations/pt_exceptional_point/`, dps 30).** For the PT-symmetric family
`H(a,b)=[[ia,b],[b,-ia]]` (`P=σ_x`, `T=` conjugation), eigenvalues `±√(b²−a²)`:
```
   a < b   real spectrum            PT UNBROKEN     "zeros on the line"
   a = b   λ=0 double, DEFECTIVE    EXCEPTIONAL PT  "the NO-MARGIN"
   a > b   ±i√(a²−b²) conj pair     PT BROKEN       "off-line zeros"
   eigenvector overlap = a/b  →  1   exactly at a=b   (eigenstates coalesce)
```
This furnishes a genuinely new sharpening of the field's central feature:

> **The no-margin is an exceptional point.** It is not merely `λ_min → 0`; it is the point where the two
> eigenvectors *coalesce* (overlap `→ 1`) and the operator loses diagonalizability. RH = the `ζ`-operator sits
> in the **PT-unbroken phase, pinned exactly at the exceptional threshold** — real spectrum, but with the
> eigenbasis on the verge of collapse. That verge is why there is no positive floor.

And it welds to the field's existing **completeness** language. At an exceptional point the eigenvectors stop
spanning — exactly the **loss of completeness** that the Nyman–Beurling / `ξ`-outer dilation program measures
(`d_N → 0`, the cyclicity defect). So:

> **No-margin `=` exceptional point `=` eigenvector coalescence `=` the Nyman–Beurling completeness defect
> `d_N → 0`.** Three of the field's independently-derived "no-margin" faces are one non-Hermitian degeneracy.

**[CERTIFIED toy + FRAME. The PT/exceptional-point structure and the `a/b` coalescence are exact; the
identification with the `ζ`-operator is the Bender–Brody–Müller conjecture (open) and the
no-margin↔exceptional-point reading is an embassy frame supported by the toy and the κ₋-jump structure.]**

## 2. Causality is analyticity: the dispersion-relation handle

Installment I asserted "RH = causality" structurally. Physics makes "causality" *operational* through one of
its deepest theorems: **causality ⟺ analyticity in a half-plane** (Toll 1956; the Kramers–Kronig dispersion
relations). A response function is **causal** (no effect before its cause) **iff** it is analytic and pole-free
in the upper half-plane, with its real and imaginary parts Hilbert transforms of each other.

Transport: the completed `ξ` is **entire** — analytic everywhere, the maximally causal response. A zero is not
a pole, but the **scattering / resolvent** object built from it (the Lax–Phillips scattering matrix of the
modular surface, whose poles are the zeros; or the Weyl `m`-function `−Ξ'/Ξ`, whose poles are the zeros) is
where causality bites:

> **RH `=` the arithmetic scattering matrix has all its resonances on the critical line `=` a causal
> (retarded) arithmetic response is pole-free off the line.** Off-line zeros are **acausal poles** — poles on
> the "wrong side," the dispersion-relation signature of a response that anticipates its cause. This is the
> dispersion-relation form of installment I's tachyon and the standing-wave handshake of §I.2: a tachyon, an
> incomplete handshake, and an acausal pole are three names for one off-line zero.

This recruits a real toolkit onto the wall: **dispersion relations, sum rules, and reflection positivity** are
the machinery physics uses to *enforce* causality, and they are exactly positivity statements — the same
positivity that is RH, now with the causal interpretation that tells you *which* positivity and *why*.

**[FRAME. Causality⟺analyticity is an established physics theorem; Lax–Phillips scattering for `ζ` is real
(Lax–Phillips, the field's `critic_eisenstein` notes); the "acausal pole = off-line zero" reading is the
embassy transport, and equals RH (open).]**

## 3. The black hole the adventure began from: horizons, entropy, ringdown

This whole continent opened from a question about **holographic black holes**. It is time to honor the origin,
because the black-hole dictionary is unexpectedly exact.

- **The critical line is a horizon.** A black-hole (or de Sitter) horizon is the locus where the timelike
  Killing vector goes null — where the clock degenerates. In installment I the no-margin was "the universe on
  its own light-cone"; the critical line is where the emergent scale-clock is marginally null = a **horizon**.
  The seam `σ=1` (Big Bang) and the critical line `σ=½` (horizon) are the two special loci, as a cosmology has
  both an initial singularity and a horizon.
- **`N(T)` is a Bekenstein–Hawking entropy.** The Riemann–von Mangoldt count
  `N(T) = (T/2π)\log(T/2πe) + O(\log T)` is the number of zero-states below height `T` — a **microcanonical
  state count**, i.e. an entropy `S = \log(\#\,states)`-type quantity, growing like the **area** of a horizon
  that expands with the cutoff. The "deep field" (high `T`, installment I §5) is the large-area / high-entropy
  regime, and the density `\sim \log(T/2π)` is the local temperature/redshift of the horizon.
- **Hawking temperature `=` the Matsubara/seam temperature.** A horizon radiates at the Gibbons–Hawking
  temperature (periodicity in imaginary time). The field already has this: the Bost–Connes / Matsubara
  structure makes imaginary-time periodicity `=` inverse temperature `β`, with the critical line `=½` the
  fermionic Matsubara line. The horizon's Hawking temperature is the seam's Bost–Connes temperature.
- **The zeros are quasinormal modes.** A perturbed black hole rings down at complex **quasinormal
  frequencies**; the explicit/trace formula expresses the `ζ`-spectrum (zeros) from the "radiation" (the prime
  sum). RH = the ringdown frequencies sit on the critical line — the horizon rings at a single real-part
  frequency, a *stable* ringdown.
- **Holography (the original word).** Bulk `=` the multiplicative wing (`σ>1`, zero-blind, Brick #4);
  boundary `=` the distinguished boundary `𝕋^∞` where the zeros live (Brick #5); **RH `=` boundary
  unitarity** — the holographic statement already in `rh-holographic-pseudorandom-boundary.md`, now placed: the
  black hole's interior is the Euler product, its horizon is the critical line, its boundary hologram is the
  zero spectrum.

**[FRAME, several pieces backed: `N(T)` is Riemann–von Mangoldt (established); Bost–Connes/Matsubara
temperature is real in the field; the BH-entropy / horizon / QNM identifications are embassy transports. RH =
boundary unitarity = open.]**

## 4. Primes are closed time-loops; the zeros are a time crystal

The most literal "time and space" reading, and it is sharp.

**Primes are closed timelike curves.** In the quantum-chaos dictionary (Berry–Keating; Gutzwiller; the
Montgomery–Odlyzko GUE law), the **zeros are the energy spectrum** and the **primes are the periodic orbits**,
each prime `p` an orbit of **length / period `\log p`**. A periodic orbit is a loop that returns to its start
in the emergent time — a **closed timelike curve** of the `ζ`-universe, one per prime, of period `\log p`. The
explicit formula is then exactly a **trace / path-integral over these time-loops**:
```
   Σ_zeros h(γ)  =  (archimedean)  −  Σ_primes (sum over the closed time-loops of length log p)
```
— a Gutzwiller/Selberg trace formula reading "spectrum `=` sum over closed time-loops."

> **Retrocausality is built into the primes.** Each prime is a loop in time; the spectrum is computed by summing
> over loops that return to the past. RH `=` this sum over closed time-loops yields a **real** (causal,
> on-line) spectrum — the time-machines (primes) conspire, via unique factorization, to produce a causal world.

**The zeros are a time crystal.** The field already establishes the zero set as a **crystalline measure /
Fourier quasicrystal** (Lev–Olevskii; Kurasov–Sarnak). A quasicrystal whose axis is **time** is, by
definition, a **time crystal** (Wilczek) — long-range order in time with no period. Since the zeros live on the
`t = Im\,s` (time) axis, the zero set *is* the `ζ`-universe's time crystal:

> **The zeros are the `ζ`-universe's time crystal** — a rigid, aperiodic long-range order in the emergent time,
> "grown" on the critical line. RH `=` the time crystal is **pinned to the line** (the order is purely
> temporal, no spatial/`σ` drift). The crystalline-measure rigidity (the dual being supported on
> `{\log p}`) is the time crystal's "Bragg peaks at the primes" — order in time whose diffraction pattern is
> the primes.

**[FRAME built on established field structure. Primes=periodic orbits and zeros=spectrum is the standard
quantum-chaos dictionary; zeros-as-crystalline-measure is established in the field; the CTC and time-crystal
readings are the embassy transports. RH = real loop-spectrum = pinned crystal = open.]**

## 5. The `ζ`-universe is a causal set: number + order = geometry

The deepest "shared word" of all may be the quietest. **Causal set theory** (Bombelli–Lee–Meyer–Sorkin 1987)
holds that spacetime is fundamentally a discrete partial order, and its slogan is:

> **"Order + Number = Geometry."** A causal set is just (i) a set of events, (ii) a partial order (the causal /
> light-cone relation: which event can influence which), and (iii) a counting measure (number of elements =
> spacetime volume). Geometry is *recovered* from order and number alone.

But arithmetic **is** number and order. The `ζ`-universe has:
- a set of events — the **zeros** (and the primes, the time-loops);
- a partial order — the **causal (timelike) relation of installment I §1**: which zeros are timelike-related
  (causally connected) through the DeWitt light-cone;
- a counting measure — `N(T)`, the **number** of zeros up to height `T` (§3, the entropy/volume).

> **The `ζ`-universe is a causal set whose order is the arithmetic light-cone and whose number is `N(T)`.**
> Causal set theory says geometry is recovered from exactly these — so the `ζ`-geometry (the critical line, the
> metric of Brick #1) should be **reconstructible from the causal order + the counting of the zeros alone.**
> RH `=` the recovered geometry is the flat/critical one (installment I §3–4). This is the most native reading:
> a theory *made of* number and order modelling an object *made of* number and order.

**[LEADING FRAME — the most apt of the expedition, but the least developed: causal set theory is real;
"arithmetic = number + order" is a genuine match; the *reconstruction* of the `ζ`-geometry from the zero
causal-order is an open program, not a result.]**

## 6. New falsifiable conjectures and honest status

**Three new conjectures (Tier C, stated to be refutable):**

1. **Exceptional-point conjecture (§1).** The `ζ`-positivity form (the Brick #1 DeWitt pairing / the secular
   Hankel) transitions to indefinite (`κ₋` jumps) precisely at an **exceptional point** of an associated
   PT-symmetric operator; RH = the operator is in the PT-unbroken phase, pinned at the threshold (no-margin =
   eigenvector coalescence = `d_N → 0`). **Falsifier:** a fake whose associated operator is PT-unbroken (real
   spectrum) yet has off-line zeros; or a demonstration that the no-margin is a *generic* `λ_min→0` (eigenbasis
   stays complete), not an exceptional-point coalescence — which the field's `d_N → 0` and the toy (overlap
   `→1`) currently argue against.
2. **Dispersion conjecture (§2).** RH = a causal (retarded) arithmetic response function (Lax–Phillips
   scattering matrix / Weyl `m`-function) obeys its Kramers–Kronig dispersion relation with **no off-line
   poles**; off-line zeros are acausal poles. **Falsifier:** an off-line zero that does *not* manifest as a
   dispersion-relation (causality) violation — i.e. a decoupling of the resolvent poles from the zeros.
3. **Causal-set conjecture (§5).** The flat/critical `ζ`-geometry is reconstructible from the zero causal-order
   (§1 light-cone) + the counting `N(T)`, à la causal-set "order+number=geometry"; RH = the reconstruction
   yields the critical line. **Falsifier:** a fake (DH) whose zero causal-order + count reconstructs the *same*
   geometry yet sits off-line — i.e. the order+number does **not** determine on-line-ness (which would say the
   causal-set data is RH-blind, a clean negative).

**Certified vs frame vs open:**
- **Certified (this installment):** the PT phases / exceptional point / exact `a/b` eigenvector coalescence
  (`pt_exceptional_point/`); inherited — installment I's handshake and `Λ`/dBN, Brick #1's tachyon.
- **Frame (embassy, air-marked):** PT-operator↔`ζ` (Bender–Brody–Müller, open); causality⟺analyticity
  transport; black hole / horizon / QNM / holography; primes as CTCs; zeros as a time crystal; the causal-set
  reading.
- **Open `=` RH:** PT-unbroken on the true spectrum `=` causal scattering `=` real loop-spectrum `=` pinned
  time crystal `=` reconstructed flat geometry `=` Weil positivity `=` `Λ=0` `=` RH. **One stone, more faces.**

> **The one sentence.** Going a level deeper, the wall acquired an *operator* (PT-symmetric, with the no-margin
> as its exceptional point, eigenvectors coalescing exactly where completeness fails), an *operational meaning*
> (causality = analyticity = no acausal poles), the *black-hole* identity it was born from (critical line =
> horizon, `N(T)` = entropy, zeros = ringdown, boundary = hologram), and its most native form (the `ζ`-universe
> as a causal set, where arithmetic's own number-and-order *is* the spacetime). RH is the single statement that
> this universe's operator stays in the real-spectrum phase — that it never crosses the exceptional point into
> the acausal, PT-broken, off-line world.

**House status (installment II).** §1 (PT / exceptional point) certified (`pt_exceptional_point/`) and welded
to the no-margin + completeness; §2 (causality=analyticity) a new operational handle; §3 (black holes) honors
the origin with a backed dictionary; §4 (CTCs / time crystal) built on established quantum-chaos + crystalline-
measure structure; §5 (causal set) the most native frame; §6 three refutable conjectures. Open core unchanged:
**PT-unbroken `=` causal `=` `Λ=0` `=` RH.** The expedition keeps finding the same stone with new faces — and
keeps adding genuinely new, refutable conjectures, so the well is not yet dry.
