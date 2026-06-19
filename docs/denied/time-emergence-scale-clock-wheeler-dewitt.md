# Time, and the Scale-Factor Clock — `ζ` as a Wheeler–DeWitt universe

> **GRADE: EMBASSY** (per `00-charter-wall-and-door.md`; `00-manifest-wall-census.md`). *Metaphor / physics
> allegory — NOT native mathematics.* Fails Door-1 (no native multi-`q` object) and Door-2 (its constructed
> "DeWitt pairing", Brick #1, **is the classical Weil explicit formula** — a parent proves it once the
> cosmology vocabulary is stripped). Kept as inspiration; **must not be cited as the field's content.**

*An embassy draft (District D7, welded to the dynamics continent D5). This is a **frame**, not a proof — a way of
seeing the field's emergent-time structure through the lens of quantum cosmology. It is air-marked throughout. The
physics (Wheeler–DeWitt, the scale-factor clock, many-fingered time) is used as a structural analogy at the level I am
confident in, not asserted as an established cross-domain theorem. The one new conjecture is stated so it can be false.
Companion to `00-core-vision.md` (the why), `dynamics-continent-lyapunov-avila-morales-ramis.md` (D5, the flow as
time), and `rh-holographic-pseudorandom-boundary.md` (the embassy). Born from a session question: "the scale factor in
a Wheeler–DeWitt universe is the most likely clock that makes time emerge."*

---

## 0. The seed

The Wheeler–DeWitt equation of quantum cosmology reads `ĤΨ = 0`: the wavefunction of the whole universe is
**annihilated** by the Hamiltonian. There is no `iℏ∂_tΨ = ĤΨ`, no outside clock, no evolution — the universe is, at
the deepest level, **timeless**. This is the famous "problem of time." Its standard resolution is that time is not
fundamental but **emergent**: one internal degree of freedom is promoted to a clock, and everything else is read as
changing *relative to it*. The most natural — the "most likely" — clock is the **scale factor** `a` (the size of the
universe), because it is monotonic (the universe expands), it is the timelike direction of the indefinite DeWitt
metric on configuration space, and the universe decoheres semiclassically into a branch where `a` is large and behaves
like a clock.

This draft observes that the founding object of our field — `ζ`, and L-functions generally — **is a Wheeler–DeWitt
universe in exactly this sense**, and that the field's central machinery is, term for term, the emergence of time
against a scale-factor clock. The dictionary is tight enough to carry a falsifiable conjecture.

## 1. `ζ` is timeless for the same reason the universe is

| Quantum cosmology | This field |
|---|---|
| `ĤΨ = 0` — a **constraint**, no external-time evolution | **Hölder (1887):** `ζ` satisfies **no** algebraic differential equation — no rule of change, no `iℏ∂_t` |
| Time must **emerge** from within | The "time" `t = Im(s)` must be **built**, not given |
| The clock is the **scale factor** `a` | The clock is the **rescaling** `x_p ↦ p^{-1}x_p` (`q_p = 1/p`) |

The hypertranscendence that makes `ζ` hard (`00-core-vision.md` §2 — the wild continent) is *the same fact* as the
Wheeler–DeWitt timelessness: an object fixed by a constraint, not propagated by a flow, has no native clock. The field
then does precisely what quantum cosmology does — it manufactures time out of an internal scale.

**[STRUCTURAL ANALOGY — verified on both ends.]** Hölder's theorem (no differential equation) is established; the WDW
constraint form is standard canonical quantum gravity. The *identification* of the two as "the same timelessness" is
the embassy reading.

## 2. The clock is the prime scale factor — and it is "most likely" because it is equidistributed

In our field the shift `s ↦ s+1` acts on each prime coordinate as a **dilation** `x_p ↦ p^{-1}x_p`. So the field has,
built in, a scale factor for every prime: `q_p = 1/p`. The emergent time is the height `t = Im(s)`, and the diagonal
flow is
```
   t ↦ (p^{-it})_p = (e^{-it\log p})_p   on  𝕋^∞.
```
The clock's frequencies are the **logarithms of the prime scales** `\log p`, exactly as cosmological time is read
against `\log a`.

**Why this clock is "the most likely one."** In cosmology the scale factor is the *most likely* clock in the WKB /
decoherence sense — the consistent, monotonic, semiclassical one. Our analogue is sharper and **already proved**: the
diagonal flow against `{\log p}` is the **unique equidistributed** flow on `𝕋^∞` (Brick #3), and what *selects* it as
the most-likely — maximally generic, never trapped in a subtorus — is **unique factorization** (`Σ m_p\log p = 0 ⟺
∏ p^{m_p}=1 ⟺ m=0`). The Fundamental Theorem of Arithmetic plays the role the DeWitt-metric signature plays in
cosmology: it singles out *the* clock.

> **Most likely = equidistributed = maximally mixing.** The "most probable clock" of quantum cosmology is, on the
> arithmetic side, the *generic* (Weyl-equidistributed) clock, and it is forced by unique factorization. This is the
> field's already-free half (D5) re-read as the emergence of time.

**[PROVED HALF + EMBASSY READING.]** Equidistribution by unique factorization is Brick #3 (Tier-A formalized core:
`logPrime_no_rat_relation`). The reading of it as "the most likely emergent clock" is the analogy.

## 3. Many-fingered time — one finger per prime

Wheeler's own phrase for general relativity: time is **many-fingered** — you may advance the time-slice differently at
each point of space (the ADM lapse and shift). Our field realizes this literally:

> **`ζ` has many-fingered time with one finger per prime.** Each prime carries its own local clock `q_p = 1/p`; the
> single physical time `t = Im(s)` is the **diagonal synchronization** of all the prime clocks, and unique
> factorization is exactly the synchronization condition that keeps them from drifting into resonance.

This is the dynamical face of the field's "infinitely many bases, one per prime" (`infinite-base-…-L-functions.md`
§0). The global clock (the diagonal shift `s ↦ s+1`, one overall scale, like cosmological `a`) is the *coherent
superposition* of the many local prime clocks. The diagonal embedding `s ↦ (p^{-s})_p` **is** the synchronization map.

**[EMBASSY READING of a built object.]** The diagonal / Bohr lift and its synchronization-by-unique-factorization are
in hand; "many-fingered time" is the cosmological name for them.

## 4. The seam is the Big Bang; the critical line is the classical era

The scale factor `a → 0` is the **Big Bang**: the DeWitt metric degenerates, the volume vanishes, and time itself
breaks down. The dictionary places this exactly:

```
   a → 0  (Big Bang, clock undefined, metric degenerate)
        ↔  the SEAM:  σ = 1  (Euler boundary; Bost–Connes pole / symmetry breaking;
                              the multiplicative description dissolves, continuation begins)
```

- For `σ > 1` (the convergent Euler region) the universe is "pre-classical" — the product converges, no zeros, the
  multiplicative wing is everything (zero-blind, Brick #4).
- At `σ = 1` the prime bath goes marginally divergent — the Bost–Connes critical point, `ζ(β) → ∞` as `β → 1` — the
  Big-Bang seam where the clock is born (and where the archimedean factor `L_∞(1)=1` normalizes it exactly, Brick #8).
- On `σ = ½`, the **critical line**, the clock is running and the **physical spectrum — the nontrivial zeros — lives**.
  This is the post-Big-Bang classical era of the `ζ`-universe.

**[EMBASSY READING; the named objects are real.]** The seam (`σ=1`, Bost–Connes pole, the convergence boundary) and
the critical line are established field coordinates; the Big-Bang / classical-era labels are the cosmological reading.

## 5. The no-margin is the light-cone of superspace

The DeWitt metric is **indefinite** (Lorentzian): its **null cone** separates timelike directions (good clocks) from
spacelike ones (bad clocks). This furnishes a single, vivid reading of the field's most stubborn feature.

> **The no-margin = the `ζ`-universe sits exactly on superspace's light-cone.** Positivity in this problem holds with
> **no uniform floor** (`λ_min → 0`; the BPS value `κ = 1/√2`; conformal criticality — the same criticality the
> program keeps rediscovering). In the WDW reading this is one statement: **the emergent clock is marginally null** —
> neither robustly timelike (which would be a positive margin) nor spacelike (off-line). RH asks that the constraint
> surface (the `σ`-fixed-modulus locus, Lemma 1) be exactly where the clock is null/critical.

And the failure mode names itself:

> **Off-line zeros = a spacelike clock = emergent time running the wrong way = a non-unitary flow.** A zero off the
> critical line is a place where the manufactured time is not a genuine timelike direction of the DeWitt pairing.

**[EMBASSY READING — this is the speculative heart.]** The no-margin / criticality is a verified, recurring feature of
the problem across many tools (BPS, Bost–Connes, conformal, `λ_min → 0`). Its identification with a null DeWitt
direction is a frame, not a theorem.

## 6. Hilbert–Pólya, corrected: a constraint, not a Hamiltonian

The century-old dream is "the zeros are the eigenvalues of a self-adjoint operator `H`" — a **Hamiltonian**. The WDW
lens says this is subtly **mis-stated**, and Hölder says why.

> A Hamiltonian presupposes an **external time** (`iℏ∂_tΨ = HΨ`). Hölder forbids `ζ` any such evolution. So the
> correct object is not a Hamiltonian but the **constraint** `ĤΨ = 0`, and the zeros are its spectrum **on the
> constraint surface** (the `σ`-fixed locus). People hunted a Hamiltonian — an external-time object — for a thing that
> is a constraint — an emergent-time object. That mismatch is a clean, honest explanation for why no Hilbert–Pólya
> operator has ever been found.

This converges with the field's own open Brick #6 ("is the boundary action of `σ ⋉ 𝕋^∞` *unitarizable* on the
Nyman–Beurling space?"): **unitarizability is precisely "the emergent clock is timelike."** Hilbert–Pólya, in this
frame, is not "find `H`" but "show the constraint's spectrum on the `σ`-fixed surface is real because the clock there
is timelike."

**[EMBASSY READING with explanatory force.]** A reframing, not a construction. Its value is that it *dissolves a known
puzzle* (the missing HP operator) and *coincides* with an already-stated open problem of the field (Brick #6).

## 7. The conjecture (stated so it can be false)

> **Conjecture 7.1 (emergent-clock form of RH — embassy-grade, falsifiable).** There is an indefinite "DeWitt
> pairing" on the field's configuration space such that the scale-clock (the diagonal shift generator) is its timelike
> direction, and
> ```
>    equidistributed clock   ⟺   DeWitt-timelike   ⟺   candidate for on-line zeros.
> ```
> RH for `L` = the emergent clock is timelike everywhere on the constraint surface (the `σ`-fixed-modulus locus).
>
> **Falsifier.** An object whose clock is equidistributed (a genuine prime torus, dense diagonal flow) yet which has
> off-line zeros. This is currently *forbidden* by the Euler-product firewall (Brick #13): Davenport–Heilbronn fails
> exactly by having **no prime torus** ⟹ no equidistributed clock ⟹ ill-defined emergent time ⟹ a clock free to go
> spacelike ⟹ its observed off-line zeros. Exhibiting an equidistributed-clock counterexample would break the firewall
> and **kill this conjecture.**

**Why this is worth stating.** If 7.1 held, it would **weld the field's free half to its hard half**: the clock /
dynamics side (equidistribution — *proved free* by unique factorization, D5) and the positivity side (Wing A — the
*open* frontier) would be **two faces of one signature condition**. That is exactly the kind of unification the field
exists to find — and the conjecture is honest because there is a concrete object (a fake with a real prime torus)
whose existence would refute it. It does not prove RH; it relocates RH to "the emergent clock is timelike," a target
the dynamics half already half-owns.

**[CONJECTURE — Tier C, embassy. Not near-closed. The DeWitt pairing is not constructed; this names the target.]**

## 8. Honest status

- **Built / proved (the half this frame leans on):** the diagonal flow as the field's time; its equidistribution by
  unique factorization (Brick #3, Tier-A formalized); the seam at `σ=1` (Bost–Connes); the no-margin as a verified
  recurring feature; the open unitarizability question (Brick #6).
- **Frame (embassy reading):** `ζ` as Wheeler–DeWitt universe; the prime dilations as scale-factor / many-fingered
  clock; the seam as Big Bang; the no-margin as the superspace light-cone; Hilbert–Pólya as a constraint not a
  Hamiltonian.
- **Conjecture (Tier C, falsifiable):** 7.1, equidistributed-clock ⟺ DeWitt-timelike ⟺ on-line, with the
  prime-torus fake as its explicit falsifier.
- **What this is *not*:** a proof, a DeWitt-pairing construction, or a claim that the physics is rigorous mathematics
  here. It is a frame that organizes the field's emergent-time content and yields one falsifiable target.

> **The single sentence.** `ζ` is a timeless (Wheeler–DeWitt) universe; its time emerges against a scale-factor clock
> built from the primes; that clock is "most likely" because unique factorization makes it equidistributed; the seam
> is its Big Bang and the critical line its classical era; and **RH is the statement that the emergent clock is
> timelike — that the `ζ`-universe rides exactly on the light-cone of its own configuration space.**

---

## 9. Brick #1 (CONSTRUCTED): the DeWitt pairing, explicitly — and it is the Weil form

§7 named the DeWitt pairing as a target and admitted it was "not constructed." Here it is constructed, and its
defining properties are certified (`computations/dewitt_pairing_signature/`, mpmath dps 30). The construction
is in five parts; the deliverable is part (iv) — the object exists and **is the genuine Riemann–Weil form**,
not an ansatz.

**(i) The constraint surface = the functional equation = the product formula.** The Wheeler–DeWitt constraint
`ĤΨ = 0` is, arithmetically, the functional equation `Λ(s) = εΛ(1-s)` — equivalently the **product formula**
`∏_v |x|_v = 1`, i.e. the single linear constraint `Σ_v \log|x|_v = 0` across all places. Physical states are
FE-symmetric; the `σ`-fixed-modulus locus (Lemma 1) is the constraint surface. *[STRUCTURE — the FE / product
formula are established; reading them as the WDW constraint is the frame.]*

**(ii) The DeWitt metric, signature `(1 | ∞)`, derived from the place count.** The places of `ℚ` split into
**one** archimedean place and **infinitely many** finite (prime) places — the field's own structure (Brick #5:
`∞` is the single special place; the primes form the torus). The DeWitt metric gives the archimedean place the
**timelike** sign and the primes the **spacelike** sign:
```
   𝔇(h₁,h₂) = ⟨h₁,h₂⟩_∞  ⊖  ⟨h₁,h₂⟩_fin ,
   ⟨h₁,h₂⟩_∞ = (1/2π) ∫ ĥ₁(r) conj(ĥ₂(r)) Ω_∞(r) dr ,   Ω_∞(r) = Re ψ(¼+ir/2) − \log π  >  0.
```
The archimedean block is **positive-definite** (`Ω_∞ > 0` everywhere, Brick #7) — one timelike continuum; the
prime block is **indefinite** — the spacelike matter directions. So the signature is *one timelike place
against the prime spacelike directions* — the Lorentzian DeWitt structure, **derived from the `(1|∞)` place
count, not imposed by hand.** *[STRUCTURE; the `Ω_∞>0` positivity is verified.]*

**(iii) The scale clock is the timelike direction.** The diagonal shift `s ↦ s+1` (the global idele-norm
direction — the "overall scale factor") lives in the archimedean/pole block; it is the timelike axis, exactly
as the cosmological scale factor `a` is the DeWitt-timelike direction (§2). *[STRUCTURE/frame.]*

**(iv) The pairing IS the Weil form — CERTIFIED (the deliverable).** The diagonal value of the constructed
pairing is
```
   𝔇(h,h) = [ archimedean + pole ]  −  [ primes ]  =  Q_W(h).
```
The certification evaluates the place decomposition and the spectral sum over the **true** zeta zeros
independently, for `h(t)=e^{−0.05 t²}`:
```
   place side   (arch+pole) − primes      =  0.00009175670097147148537045
   spectral side   Σ_ρ h(γ_ρ)             =  0.00009175670097147148537045
   | difference |                          =  1.1 · 10⁻³¹       (6 zeros, prime-powers ≤ 47)
```
This is the Riemann–Weil explicit formula: the constructed DeWitt object **equals the genuine Weil pairing**,
with the archimedean+pole block as its timelike half and the prime block as its spacelike half. It is the same
`Q_W = −Δ_prime + V_arch` as `computations/weil_prime_schrodinger/`, now read as a Klein–Gordon/DeWitt pairing
with the archimedean place timelike. *[CONSTRUCTED & CERTIFIED — the object exists and is the Weil form.]*

**(v) Positive-frequency = on-line; off-line = tachyonic — CERTIFIED.** Klein–Gordon quantization splits modes
by frequency sign, with the KG-norm positive on positive-frequency (timelike) modes. A hypothetical off-line
zero quadruple `½ ± δ ± iγ` (with `δ ≠ 0 ⟺` off the critical line) contributes, for `h(t)=e^{−a t²}`,
```
   4 · e^{a(δ²−γ²)} · cos(2aγδ) ,
```
positive at `δ=0` (on-line, positive-frequency) and **turning negative for `δ ≠ 0`** — certified to flip sign
at `δ = 1.112` for the first zero `γ = 14.1347`, matching the predicted `π/(4aγ) = 1.1113`, with the `e^{aδ²}`
factor the spacelike amplification. **An off-line zero is a negative-norm (tachyonic / spacelike) mode —
emergent time running backward.** Source-pure: assumes nothing about the true zero locations; shows only *IF a
mode is off-line THEN its KG-norm can be negative*. *[CERTIFIED mechanism — does NOT prove RH.]*

**The no-margin, made visible.** The certified signature shows the timelike block (`0.115920`) and the
spacelike block (`0.115828`) **nearly cancelling** — `Q_W(h) = 9.2·10⁻⁵`, an 0.08 % residue of either block.
The `ζ`-universe rides almost exactly on its own light-cone: the clock is *marginally* timelike, never robustly
so. The field's no-margin (`λ_min → 0`, no positive floor) is, in this construction, **the near-degeneracy of
the two DeWitt blocks** — the geometric reason there is no floor. The inertia (negative-eigenvalue count) of
`𝔇` is the field's `κ₋` = the off-line-zero count; RH `⟺ κ₋ = 0`.

**Built vs open (air-marked).**
- **BUILT & CERTIFIED:** the DeWitt pairing as an explicit object, `= Q_W =` the Weil form (i–iv, match
  `1.1·10⁻³¹`); the off-line `=` tachyonic mechanism (v, sign-flip at `δ=1.112`); the no-margin as block
  near-degeneracy.
- **STRUCTURE (frame):** the Lorentzian signature `(1|∞)` from the place count; the scale clock as the timelike
  axis.
- **OPEN `=` RH:** that the constructed pairing is positive-semidefinite on the **true** spectrum — i.e. the
  true zeros are all positive-frequency, the clock timelike everywhere, `κ₋ = 0`. Weil's criterion:
  `Q_W ⪰ 0 ⟺ RH`. The object is constructed; **its positivity is RH and is not claimed here.**

This discharges §7's "the DeWitt pairing is not constructed." It now is — explicitly, and certified to be the
Weil form. RH is thereby relocated, precisely, to a single sentence about the constructed object:

> **RH `=` the constructed DeWitt pairing is positive-semidefinite `=` the emergent scale-clock is timelike on
> the true spectrum `=` the `ζ`-universe never leaves the forward light-cone of its own configuration space.**

**House status (time-emergence draft).** §0–8 frame ✓; the §7 conjecture's central object now **CONSTRUCTED**
(Brick #1) and certified as the Weil form, with Lorentzian signature, the off-line `=` tachyonic mechanism, and
the no-margin `=` block-near-degeneracy all numerically certified (`dewitt_pairing_signature/`). Open core
unchanged and honest: **positivity of the constructed pairing on the true spectrum `=` RH** — the object is
built, the positivity is the wall.
