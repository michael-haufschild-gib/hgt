# Arithmetic Criticality Theory (`GaloisForLFunctions.ArithmeticCriticalityTheory`)

Positive solutions, ground-state representations and criticality of the arithmetic jump operator
whose nonnegativity on odd tests is the Riemann Hypothesis.

Origin: [docs/reports/review-1910/fable.md](../../../docs/reports/review-1910/fable.md), Section 4.
Pipeline card: `docs/drafts/pipeline/1-in-progress/act-arithmetic-criticality-theory-2026-10-19.md`.

---

## 1. Why this programme exists

The corpus owns an RH-equivalent inequality of Hardy type
(`RHTower.riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`,
`TransHorizonIncidenceMechanics.riemannHypothesis_iff_odd_primeChain_poincare`):

    RH  ⟺  for every odd v ∈ C²_c(ℝ):   ∫ Θ(x) cosh(x/2) v(x)² dx  ≤  E_arch(v) + E_prime(v),

where `Θ` is Riemann's kernel (`riemannKernelReal`, even, positive, super-exponentially decaying),

    E_arch(v)  = ∫_{t>0} ω(t) ∫_ℝ Θ(x)Θ(x+t) (v(x) − v(x+t))² dx dt,     ω(t) = e^{−t/2}/(1 − e^{−2t}),
    E_prime(v) = Σ_{n≥2} Λ(n) n^{−1/2} ∫_ℝ Θ(x)Θ(x+log n) (v(x) − v(x+log n))² dx.

Equivalently, with `markovEnergy (Θ v) = E_arch(v) + E_prime(v) − ∫ Θ cosh(x/2) v²`
(`phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass`), RH is the statement that the
Schrödinger-type form "jump energy minus potential" is nonnegative on odd tests.

Every previous programme attacked this (and its cousins) by bounding sums: identities, finite
classifications, nonselective positivity on restricted families. None produced a sign. In the theory
of Dirichlet forms the sign question has a different shape: a form `E − ρ` is nonnegative if and only
if a **positive supersolution** `ω` of `Lω ≥ ρ ω` exists (Allegretto–Piepenbrink), and the proof is an
exact identity, the **ground-state representation**. Arithmetic Criticality Theory develops this
mechanism for the arithmetic jump operator. It replaces a bounding problem by an existence problem for
one positive function.

**What is new.** Criticality theory exists for local Schrödinger operators and for jump processes
with translation-invariant kernels. It does not exist for a kernel whose jump lengths are the
logarithms of prime powers, whose rates are `Λ(n) n^{−1/2}`, and whose potential is the pole of the
zeta function. The corpus searches (`research "Allegretto Piepenbrink ..."`, `"ground state
representation ..."`) return nothing relevant.

---

## 2. Objects and language

All functions below are in **Doob coordinates**: a test is `f = Θ · v`, and `v` is the object. The
corpus's "secondary odd profile" `m_a` is a test; its Doob coordinate is `f_a = m_a / Θ`
(`oddPolarFunction a`). Never mix the two coordinates.

| Object | Definition | Lean |
|---|---|---|
| Riemann kernel | `Θ(u) = Σ_{n≥1} e^{u/2}(4π²n⁴e^{4u} − 6πn²e^{2u}) e^{−πn²e^{2u}}`, even, `Θ > 0` | `riemannKernelReal` |
| Jump measure | `dm(t) = ω(t) dt + Σ_n Λ(n) n^{−1/2} δ_{log n}` on `t > 0` | `archLevyDensity`, `vonMangoldtAtom` |
| Single-shift jump | `J_v(t) = ∫_ℝ Θ(x)Θ(x+t)(v(x) − v(x+t))² dx` | `phiDoobArchShiftJump` (integrated) |
| Potential | `ρ(x) = Θ(x) cosh(x/2)` | `phiDoobCoshMass (v²)` is `∫ ρ v²` |
| Same-side ground jump | `Θ(x)Θ(x+t) ω(x)ω(x+t) (u(x) − u(x+t))²` on `x > 0` | `sameSideGroundJump` |
| Reflected ground jump | `Θ(x)Θ(t−x) ω(x)ω(t−x) (u(x) + u(t−x))²` on `0 < x < t` | `reflectedGroundJump` |
| Folded (Neumann) shift generator | `Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(|x−t|))]` | `foldedShiftGenerator` |
| Two-sided (Dirichlet) shift generator | `Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(x−t))]` | `twoSidedShiftGenerator` |
| Folded generator | `(𝓛_N ω)(x) = ∫ dm(t) foldedShiftGenerator ω t x` | `foldedGenerator` |
| Two-sided generator | `(𝓛_D ω)(x) = ∫ dm(t) twoSidedShiftGenerator ω t x` | `twoSidedGenerator` |
| Shifted ground state | `ω_a(x) = (Θ(x−a) − Θ(x+a)) / Θ(x)`, odd, `> 0` on `(0,∞)` for `a > 0` | `shiftedGroundState` |
| Reflected collar mass | `C_a(x) = ∫_0^∞ ω(x+s)(Θ(s−a) − Θ(s+a)) ds + Σ_{log n > x} Λ(n)n^{−1/2}(Θ(log n − x − a) − Θ(log n − x + a))` | `reflectedCollarMass` |
| Finite jump energy | `E_K(v) = ½ Σ_{i,j} K_{ij} (v_i − v_j)²` | `jumpEnergy` |
| Finite generator | `(L_K ω)_i = Σ_j K_{ij}(ω_i − ω_j)` | `generator` |
| Schrödinger matrix | `A = diag(Σ_k K_{ik} − ρ_i) − K`, so `vᵀAv = E_K(v) − Σ ρ_i v_i²` | `schroedingerMatrix` |

Terminology (Pinchover). A form `Q = E − ρ` is **supercritical** if it takes a negative value,
**critical** if it is nonnegative but admits no nonzero Hardy weight `W ≥ 0` with `Q ≥ ∫ W v²`, and
**subcritical** if such a weight exists. RH says the odd-sector arithmetic form is not supercritical.

---

## 3. Mechanisms

### 3.1 The pointwise ground-state identities (pure algebra)

For reals `ω_x, ω_y, u_x, u_y`:

    (ω_x u_x − ω_y u_y)² = ω_x ω_y (u_x − u_y)² + (ω_x − ω_y)(ω_x u_x² − ω_y u_y²)        (difference)
    (ω_x u_x + ω_y u_y)² = ω_x ω_y (u_x + u_y)² + (ω_x − ω_y)(ω_x u_x² − ω_y u_y²)        (sum, Neumann form)
    (ω_x u_x + ω_y u_y)² = −ω_x ω_y (u_x − u_y)² + (ω_x + ω_y)(ω_x u_x² + ω_y u_y²)      (sum, Dirichlet form)

The second factor of the last term is antisymmetric under `x ↔ y`, so after summation against a
symmetric kernel it becomes `2 Σ u² ω (Lω)`: the potential produced by the generator applied to `ω`.

### 3.2 The folded ground-state representation (GSR-N) for the odd sector

Let `v` be odd, continuous, compactly supported, and write `v = ω u` on `(0,∞)` with `ω` odd and `u`
even. Fold each shift integral onto the half line
(`integral_phiDoobArchShiftJump_eq_halfLine_of_odd`): the full-line jump at shift `t` equals twice the
same-side half-line jump plus the origin-crossing collar `∫_{0<x<t} Θ(x)Θ(t−x)(v(x) + v(t−x))²`.
Applying the difference identity to the same-side part and the Neumann sum identity to the collar gives,
exactly,

    J_v(t) = 2∫_{x>0} sameSideGroundJump + ∫_{0<x<t} reflectedGroundJump + 2∫_{x>0} u(x)² ω(x) foldedShiftGenerator ω t x dx.

Integrating against `dm(t)` and subtracting the potential:

    markovEnergy(Θ v) = R_N(ω, u) + 2 ∫_{x>0} u(x)² ω(x) [ (𝓛_N ω)(x) − Θ(x) cosh(x/2) ω(x) ] dx,     R_N ≥ 0.

**Consequence (sufficiency).** If `ω` is odd, positive on `(0,∞)`, and `𝓛_N ω ≥ Θ cosh(x/2) ω` on
`(0,∞)`, then `markovEnergy(Θ v) ≥ 0` for every odd test factoring through `ω`, hence RH.

**Reading of `𝓛_N`.** On `(0,∞)`, `foldedShiftGenerator ω t x` is the two-sided generator applied to the
**even reflection** `|ω|`. So the condition is: the even function `|ω|` is a supersolution away from
the origin. At the origin `|ω|` has a kink; that is where the Dirichlet condition `v(0) = 0` of the odd
sector lives.

### 3.3 The two generators and their difference

    (𝓛_D ω)(x) − (𝓛_N ω)(x) = 2 Θ(x) ∫_{t>x} dm(t) Θ(t−x) ω(t−x)      (x > 0, ω odd, ω > 0 on (0,∞)).

The two-sided generator is the larger one, by exactly the mass that returns from the reflected side.
The Dirichlet sum identity gives a second exact representation (GSR-D) with `𝓛_D` in the potential,
but its remainder contains `−Θ(x)Θ(t−x)ω(x)ω(t−x)(u(x) − u(t−x))²` and is indefinite. Only GSR-N has a
nonnegative remainder. A `𝓛_D`-supersolution therefore proves nothing by itself; a `𝓛_N`-supersolution
proves RH.

### 3.4 The equation of motion and the shifted ground states

The corpus proves the pointwise harmonic identity of `Θ` (`theta_harmonic_identity`): the symmetric
prime shift sum of `Θ` equals `cosh(x/2)` up to the archimedean correction. In Doob coordinates this
says `𝓛_D 1 = 0` with the constant `1` a **subsolution** (`0 < ρ`): the even sector is supercritical,
and its negative direction is the pole (`markovEnergy(Θ) = −1/2`, from `∫ Θ cosh(x/2) = 1/2`).

Subtracting the identity at `x − a` and `x + a` (`oddProfile_harmonic_identity`) gives the exact
source equation of the shifted ground state `ω_a`:

    (𝓛_D ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 sinh(a/2) sinh(x/2) Θ(x)      for all x,

positive on `(0,∞)`: every `ω_a` (`a > 0`) is a strict `𝓛_D`-supersolution on the half line. By 3.3,

    (𝓛_N ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 Θ(x) [ sinh(a/2) sinh(x/2) − C_a(x) ],

with `C_a` the reflected collar mass. So `ω_a` is a `𝓛_N`-supersolution at `x` exactly when
`C_a(x) ≤ sinh(a/2) sinh(x/2)`. The prime part of `C_a(x)` is a smoothed count of prime powers in a
window of bounded logarithmic width above `e^x`; by the prime number theorem it is asymptotic to
`e^{x/2} ∫_0^∞ e^{s/2}(Θ(s−a) − Θ(s+a)) ds`, while the source is asymptotic to `sinh(a/2) e^{x/2}/2`.
Write `κ(a) = ∫_0^∞ e^{s/2}(Θ(s−a) − Θ(s+a)) ds`, `I(a) = ∫_a^∞ e^{u/2}Θ`, `J(a) = ∫_a^∞ e^{−u/2}Θ`, so that
`κ(a) = e^{a/2}(1/2 − J(a)) − e^{−a/2} I(a)` (using `∫_ℝ e^{u/2}Θ = 1/2`). The asymptotic ratio of
collar to source is `R(a) = 2κ(a)/sinh(a/2)`, and

    2κ(a) − sinh(a/2) = ½[ e^{a/2}(1 − 4J(a)) − e^{−a/2}(4I(a) − 1) ] > 0   for every a > 0,

because `J(a) ≤ J(0) = 1/4 − σ` and `I(a) ≤ I(0) = 1/4 + σ` with `σ = ∫_0^∞ Θ(u) sinh(u/2) du > 0`, so
`e^{a}(1 − 4J(a)) ≥ 4σ e^{a} > 4σ ≥ 4I(a) − 1`. The ratio tends to `1 + 8Θ(0) + 4σ` as `a → 0`
(about eight) and to `2` as `a → ∞`. **Every shifted ground state fails to be a folded supersolution
on a neighbourhood of infinity, by a factor that is a pure constant of Riemann's kernel.** This is
the exact content of the corpus's "factor two between `μ = 1/2` and `μ = 1`" and of THIM's residual
`θ · sourcePair`. The Lean modules prove the exact identities; the asymptotic statement uses the
prime number theorem through a smooth window and is a paper theorem on the card.

### 3.5 The finite model (Perron–Frobenius)

For a finite symmetric nonnegative kernel `K` and any potential `ρ`, the form `E_K − Σ ρ v²` is
nonnegative if and only if a nonnegative nonzero `ω` with `L_K ω ≥ ρ ω` exists; under connectivity,
`ω > 0`. Both directions are unconditional theorems of the programme
(`FiniteJumpFormAllegrettoPiepenbrink`). The hard direction uses the minimiser of the Rayleigh quotient
on the unit sphere and the fact that replacing a vector by its absolute value does not increase the
form. This is the template that the arithmetic problem must be measured against: the arithmetic form on
the odd sector is **not** of Z-type (the reflected collar enters the operator with a plus sign), which
is precisely why the hard direction is open there.

---

## 4. Traps and sharp boundaries

| Trap | Why it fails, and the correct statement |
|---|---|
| Looking for an even positive supersolution on all of `ℝ` | It cannot exist: it would give `markovEnergy(Θ v) ≥ 0` for even `v`, but `markovEnergy(Θ) = −1/2`. The supersolution must vanish at `0` (odd, or even with a kink), and the identity must be applied only to odd tests. |
| Using `𝓛_D` (two-sided generator) as the supersolution operator | The GSR with `𝓛_D` has an indefinite remainder. Only `𝓛_N` (folded, Neumann) gives a nonnegative remainder. |
| Reading `ω_a > 0` with positive `𝓛_D`-source as a proof of RH | It is a `𝓛_D`-supersolution, not a `𝓛_N`-supersolution; the reflected collar `C_a(x)` exceeds the source asymptotically. |
| Defining the generator through a "total jump rate" | `∫ dm(t)(Θ(x+t) + Θ(x−t))` diverges (the archimedean density has a `1/t` singularity, the prime sum has `Σ Λ(n)n^{−1/2} = ∞`). Only differences `ω(x) − ω(x+t)` converge. Never split a generator into rate minus average. |
| Confusing test and Doob coordinates | `m_a` is a test; `f_a = m_a/Θ` is the Doob coordinate. Potentials, generators and supersolutions live in Doob coordinates. |
| Requiring `v/ω` to be `C²` | The ground-state identities need no derivatives. The RH criterion needs `v ∈ C²_c`; the quotient `u = v/ω` only needs to be continuous and bounded on `(0, R]`, which holds when `ω` vanishes at most linearly at `0`. |
| Applying Perron–Frobenius to the odd sector directly | The odd-sector operator has positive off-diagonal entries from reflected jumps. Z-type arguments apply to the even sector (supercritical, pole) and to the folded operator `𝓛_N` acting on `|ω|`, not to the odd form as a whole. |
| `1 < 2 exp(−2|a|)` in THIM's gauge | The corpus's odd polar vectors require `a < (log 2)/2`, and the absorption ratio `2M cosh(R/2)/(Θ(R) sinh(a/2))` grows like `exp(πe^{2R})`. Supersolution statements here are stated pointwise in `x` and carry no aperture window. |

---

## 5. Research topics and milestones

1. **M1 (Lean, done when this README was written):** pointwise identities; finite GSR; finite
   Allegretto–Piepenbrink in both directions; the folded GSR for the actual Doob forms; the sufficiency
   theorem `folded supersolution ⟹ RH`.
2. **M2 (Lean):** even-sector calibration: `𝓛_D 1 = 0`, `markovEnergy(Θ) = −1/2`, the even sector is
   supercritical with the pole as negative direction.
3. **M3 (Lean, exact part):** the source equation of `ω_a` and the folded defect identity with the
   reflected collar mass `C_a`. **(Paper, then Lean):** the asymptotic failure `C_a(x) > sinh(a/2)
   sinh(x/2)` for large `x`, from the prime number theorem with a smooth window; the limiting ratio
   `R(a) = 2κ(a)/sinh(a/2)` exceeds `1` for every `a > 0` (Section 3.4), so no shifted ground state is
   a folded supersolution near infinity. Lean status: exact identities done
   (`ShiftedGroundStateSourceEquation`, `ShiftedGroundStateReflectedCollarDefect`); the window
   prime number theorem transport is open.
4. **M4 (paper, partly settled):** on the cone of odd functions positive on `(0,∞)`, both the
   two-sided generator and the reflected collar are linear, so the folded defect of a positive
   superposition `ω = Σ c_j ω_{a_j}` (`c_j ≥ 0`) is `Σ c_j · (folded defect of ω_{a_j})`. With M3 every
   summand is eventually negative: **no positive finite superposition of shifted ground states is a
   folded supersolution near infinity.** Open: signed superpositions that stay positive on `(0,∞)`,
   and supersolutions outside the span of the shifted ground states (the forced asymptotics of any
   odd folded supersolution at infinity).
5. **M5 (answered negatively for the folded operator, 19 October 2026):** no folded supersolution
   exists. In test coordinates `g = Θω` the folded defect is exactly
   `Θ(x)[𝒜g(x) − 2c g(x) − Σ_n Λ(n)n^{−1/2}(g(x+log n) + g(|x−log n|))]`; at the origin `g(0) = 0` makes
   it `−2Θ(0)[∫ω g + Σ Λ(n)n^{−1/2} g(log n)] < 0` for every odd profile, and at infinity the reflected
   prime mass `e^{x/2}∫_0^∞ e^{r/2} g` dominates for every admissible profile. For `ω_a` the origin
   failure is in Lean (`ShiftedGroundStateOriginFailure`, using the prime `2` alone). So the hypothesis
   of `riemannHypothesis_of_foldedSupersolution` is never met, and the hard direction of
   Allegretto–Piepenbrink fails for the odd arithmetic form. **Positive survivor:** the folded
   ground-state representation with `ω = ω_a` is an exact *remainder-dominates-defect* identity
   (`markovEnergy_phiDoob_shiftedGroundState_eq`): Markov positivity is
   `4∫_{x>0} u² ω_a Φ (C_a − sinh(a/2) sinh(x/2)) ≤ groundRemainder(ω_a, u)`, both sides explicit and
   nonnegative in the relevant region. Positivity, if RH holds, is carried by the remainder, never by
   the generator; the programme continues on this inequality (THIM's absorption problem in closed
   form) and on its two-sided twin, where `ω_a` is an exact strict supersolution and the remainder
   carries the negative reflected square `−Φ(x)Φ(t−x)ω(x)ω(t−x)(u(x) − u(t−x))²`.

Selectivity gate for every result: state what it says for `ζ(s−a)ζ(s+a)` (two poles; the potential
changes) and for a Beurling system. The identities of Sections 3.1–3.3 hold for any even positive
kernel; the arithmetic content enters only through the equation of motion of `Θ` (Section 3.4).

---

## 6. Navigation and discipline

- Search first: `scripts/formal_tools.py research "foldedShiftGenerator"`,
  `research "shiftedGroundState reflectedCollarMass"`, `research "theta_harmonic_identity"`.
- Umbrella: [`GaloisForLFunctions/ArithmeticCriticalityTheory.lean`](../ArithmeticCriticalityTheory.lean).
  Wire new modules by appending an import line.
- Build one module at a time:
  `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/ArithmeticCriticalityTheory/<Module>.olean -i .lake/build/lib/lean/GaloisForLFunctions/ArithmeticCriticalityTheory/<Module>.ilean GaloisForLFunctions/ArithmeticCriticalityTheory/<Module>.lean`.
- No `sorry`, `axiom`, raised heartbeats, or numerical experiments. Integrability hypotheses are stated
  explicitly as structure fields and discharged for concrete `ω`; an RH-strength premise is never a
  hypothesis.
- Namespace: `GaloisForLFunctions.ArithmeticCriticalityTheory`; corpus objects are used through
  `open RHTower` and the `RHTower.CHMDPolar` namespace.

## 7. Module map

| Module | Content |
|---|---|
| `GroundStateRepresentationAlgebra` | pointwise identities; finite jump form, generator, finite ground-state representation; easy Allegretto–Piepenbrink |
| `FiniteJumpFormAllegrettoPiepenbrink` | Schrödinger matrix; Rayleigh form; hard direction via minimiser and absolute value; neighbour-closed zero set; connectivity ⟹ strict positivity; the finite equivalence |
| `DoobJumpFoldedGroundStateRepresentation` | `foldedShiftGenerator`, `twoSidedShiftGenerator`, ground jumps; comparison of the two generators; folded ground-state representation of one Doob shift jump |
| `OddSupersolutionCriterion` | `foldedGenerator`, `groundRemainder`, `FoldedAdmissible`; folded ground-state representation of `markovEnergy (Θ v)`; `riemannHypothesis_of_foldedSupersolution` |
| `ShiftedGroundStateSourceEquation` | `shiftedGroundState`, `twoSidedGenerator`; exact source equation `𝓛_D ω_a − Θ cosh ω_a = 2 sinh(a/2) sinh(x/2) Θ` |
| `ShiftedGroundStateReflectedCollarDefect` | `shiftedCollarMass`; integrability and summability of the collar; `𝓛_N ω_a = 𝓛_D ω_a − 2Θ C_a`; folded defect and the supersolution criterion for `ω_a` |
| `EvenSectorPoleCalibration` | constants are strict subsolutions of both generators; pole mass `1/2`; degenerate shift `a = 0` |
| `ShiftedGroundStateOriginFailure` | prime-`2` lower bound for the collar; `ω_a` is a strict folded subsolution near the origin; remainder-dominates-defect identity and its nonnegativity criterion |
| `ShiftedGroundStateSuperposition` | linearity of the folded generator on the span of shifted ground states; folded defect of a combination; a nonnegative nonzero combination is a folded supersolution at `x` only if a constituent is |
