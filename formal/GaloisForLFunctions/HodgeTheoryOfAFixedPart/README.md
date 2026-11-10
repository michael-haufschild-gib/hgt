# Hodge Theory of a Fixed Part (HFP)

Namespace `GaloisForLFunctions.HodgeTheoryOfAFixedPart`; umbrella `HodgeTheoryOfAFixedPart.lean`.
Specification: §2.9 of
[the review-1011 summary](../../../docs/reports/review-1011/obstacles-summary.md); card
`docs/drafts/pipeline/1-in-progress/hfp-hodge-theory-of-a-fixed-part-programme.md`.

Status: **Lean** = proved in this folder; **corpus** = proved elsewhere in the corpus;
**open** = no theorem.

## 1. Motivation

A Hodge index theorem turns a statement in law into a statement at every zero. The known proofs
get the sign from one of three sources.

- **A family.** Monodromy and weights over a base. `ζ` has no moduli: a Dirichlet series with its
  functional equation is a multiple of it, and every arithmetic family sees only its variable
  part. `ζ` is the fixed part of all of them.
- **A surface.** An ample class and a count of sections on a two-dimensional object. The square
  of `Spec ℤ` is a curve: the union of the Frobenius graphs, glued along the primes.
- **A Frobenius with zero derivative.** Simultaneous vanishing at the primes of a window costs
  the count of the window.

HFP is the Hodge theory of the one object that is left: the pairing of the degree points of the
arithmetic square. Its entries are finite parts, not intersection numbers of a surface:

  `Γ_m · Γ_n = jets + contacts` off the diagonal, `Γ_n · Γ_n = −log(n/2π)`.

The contacts are orders of schemes `Γ_m ∩ Γ_n`; the jets are traces of the same Frobenius on the
archimedean fibre; the self-intersection is the logarithm of the density of the comb that
contains the point, over `2π`. On packets of degree points the pairing tends to
`2 d₁ d₂ − Z(f)`, twice the product of the degrees minus the sum over the zeros, and the
inequality of Castelnuovo and Severi `D · D ≤ 2 d₁ d₂` for all packets is the Riemann
hypothesis.

The programme asks what an index theorem for this object can rest on, when no family, no surface
of finite type and no cheap Frobenius exists: which comb, which classes are effective, which
count, which second axiom, and at which scale the statement is local.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Degree point | `n : ℕ`, `n ≥ 1` | the graph `Γ_n` of `F_n` on the arithmetic square, at `log n` |
| Real divisor | `c : ℕ → ℝ` on a finite set `S` | `D = Σ c_n γ_n`, `γ_n` the graph in the unitary normalization with the mass `1/n` of its cell: `c_n = f_n/√n` for a packet `f` |
| Jet | `jet m n` | `½(1/|m − n| + 1/(m + n))`, the trace of `V_m F_n` on the archimedean fibre, normalized |
| Contact | `contact m n` | `Λ(n/m)` for `m ∣ n`, `m < n`: the logarithm of the order of the contact, with the gcd as multiplicity |
| Counterterm | `counterterm n` | `log(n/2π)`: the density of the comb of all degree points at `n`, over `2π` |
| Comb pairing | `combPairing S c` | `Σ_{m≠n} c_m c_n jet + 2 Σ_{m∣n, m<n} Λ(n/m) c_m c_n − Σ c_n² log(n/2π)` |
| Degrees | `degOne c`, `degTwo c` | `d₁ = Σ c_n/n`, `d₂ = Σ c_n`; the pole term is `2 d₁ d₂` |
| Comb form | `combForm S c` | `2 d₁ d₂ − D·D`: Weil's form on the comb |
| Potential | `combPotential S n` | the rate of the jumps out of `n` inside `S`, jets and contacts, minus the counterterm |
| Window | `Ioc N (N + L·N)` | the degree points of ratio at most `1 + L` above the scale `N` |
| Flat tail | `flatTail A` | the divisor `Σ_{n ≤ A} γ_n`; in the limit the packet `e^{u/2}` on `u ≤ log a` |
| Gluing index | corpus `necklaceMatrix`, `Nat.factorial` | the index of the restriction lattice of the first `N` graphs, `N!` |
| Carry cocycle | `carryCocycle M N` | `log C(M + N, M)`: the defect of additivity of the logarithm of the gluing index |
| Tower of lines | corpus `orbitBaseRing`, `orbitSection` | the orbit ring with a base: `τ(M)` lines at the level `M`, exact count of sections |
| Count form | `towerCountForm` | the quadratic form whose values are the logarithms of the exact counts on the lines |
| Zero sum, defect | corpus `zeroSum`, `offLineDefect` | `Z(f)`; the nonnegative sum over the zeros off the line |
| Curve comb | `curveComb` | the degree points `qⁿ` of a curve datum, with its point counts as contacts and `2 − 2g` on the diagonal |

## 3. Language

- **Comb**: a locally finite set of degree points with masses. **Density**: the reciprocal of the
  mass, in the logarithmic coordinate. **Counterterm**: `log(density/2π)`. **Finite part**: the
  pairing of the jets minus the masses times the counterterm.
- **Contact**: a point of two graphs; it carries the mass of the lower one. **Jet**: a density on
  pairs of degree points; it carries both masses.
- **Packet**: a function `f ∈ C²_c` in the logarithmic coordinate, sampled at a scale `N`.
  **Real divisor**: any real vector on finitely many degree points, with no smoothness.
- **Effective**: a divisor with nonnegative coefficients; a class with a section.
- **Degrees** `d₁, d₂`: the pairings with the two rulings; `2 d₁ d₂` is the pole plane.
- **Index**: the number of positive squares of the pairing on a space of divisors together with
  the two rulings. **Defect** of a splitting `E + E^♯`: the divisor `W` with
  `|W^♯ E^♯| ≤ |W E|` right of the line; its degree bounds the zeros right of the line.
- **Window**: degree points of bounded ratio at one scale. **Logarithmic window** at `T`:
  `|log n − T| ≤ 32 log(T + 2)`. **Exception**: a set of at most `C e^{δT}` primes of a window,
  `δ < 1`.
- **Finite scale**: a statement at one `N` for all real divisors, as opposed to a limit on
  packets.
- **Gluing index**, **carry**, **level**, **line**: as in `AbsoluteGeometryOfSpecZ`.

## 4. Mechanisms

Built on (corpus):

1. **Contacts plus jets.** `Γ_m · Γ_{mk}/√(m·mk) = Λ(k)/√k + ω(log k)`; on a packet the jets
   carry both masses and a contact one.
2. **Comb finite parts.** The jets on a comb are a Lévy–Khintchine form; their finite part with
   the counterterm of the comb is Weil's archimedean form of a packet. The counterterm belongs
   to the comb, not to the point.
3. **The pairing weighs the zeros.** Jets plus twice the contacts minus the counterterm tend to
   `2 d₁ d₂ − Z(f)`; `Z(f) ≥ −D(f)` with `D(f) ≥ 0` supported on the zeros off the line.
4. **A section count with Riemann–Roch and Bézout is the Hodge index**; each axiom alone is
   free.
5. **The index law.** A Hermite–Biehler sum with a defect of degree `κ` has at most `κ` zeros
   right of the line; the bound passes to locally uniform limits. The negative squares of
   Weil's form of a configuration are its distinct right zeros.
6. **Locality in scale.** One inequality per prime on arbitrarily late logarithmic windows,
   outside power-thin exceptional sets, is the Riemann hypothesis.
7. **The comb selects the contacts.** With the jets and the counterterm of the comb of the
   integers, Bézout holds for a system of contact weights iff the weights are `Λ` and the
   Riemann hypothesis holds.

Developed here:

8. **The normal form.** In the coordinates `c_n = f_n/√n` the pairing is one exact matrix on the
   degree points: jets `½(1/|m − n| + 1/(m + n))`, contacts `Λ(n/m)`, diagonal `−log(n/2π)`,
   pole `1/m + 1/n`. It is defined at every finite scale and on every real divisor.
9. **Zariski's lemma on a comb.** Off the diagonal the pairing is nonnegative, so
   `D·D = Σ c_n² V(n) − ½ Σ_{m≠n} (jet + contact)(c_m − c_n)²` with the potential `V` of
   mechanism 8. The contacts of `Γ_n` with the graphs below it sum to `log n`, the divergent
   part of the counterterm.

## 5. Questions

| # | Question | Answer | Status |
|---|---|---|---|
| Q1 | Which comb is canonical on a window? | | open |
| Q2 | What is the second axiom that turns the exact section count into Bézout? | | open |
| Q3 | Is the index of the degree-point pairing at most one on every window? | In the limit on packets: on windows of width at most `181/250` (corpus); on every window iff RH (corpus) | open at finite scale |
| Q4 | How do the carries, the defect between the Λ-structure and addition, enter the pairing? | | open |
| Q5 | Why does the argument fail for integer-norm monoids, which the square does not see? | The comb sees them: Bézout on the comb of the integers selects `Λ` (corpus) | corpus |

## 6. Tools

| Tool | Content | Status |
|---|---|---|
| T1 | Calculus of comb finite parts: the normal form, Lévy–Khintchine and Zariski on a comb, potentials | open |
| T2 | Section counts on towers of lines: counts with vanishing conditions, the gluing index in Riemann–Roch | open |
| T3 | The index law at infinite rank: the index of the pairing on a window, at finite scale and in the limit | open |
| T4 | Window locality with exceptional sets, in the language of the pairing | open |
| T5 | The carry cocycle as a term of the pairing | open |
| T6 | Ordered approximations: finite scales, subcombs, the arithmetic clock | open |

## 7. Criteria

A mechanism of the field must pass every row.

| # | Criterion | Reading |
|---|---|---|
| K1 | Reproduce Weil's proof for curves, where the comb is `q^ℤ` | |
| K2 | Reproduce the Lagarias–Suzuki line law as an index-one statement | |
| K3 | Fail on the golden datum, the integer-norm one-offs, the approaching Euler product, the `cosh` models, the heat family and the non-tempered pair | |
| K4 | Use the coefficient size exactly | |
| K5 | Not be uniform in real characters unless it excludes exceptional zeros | |
| K6 | Be pointwise | |
| K7 | Respect the no-gos: no finite type, no glued invariant carrier, no duality between contacts and jets, no diagonal attached to a point | |

## 8. Milestones

| # | Milestone | Status |
|---|---|---|
| M1 | Contacts, jets, comb finite parts, the section-count theorem, windows, the pairing with limit `2 d₁ d₂ − Z(f)`, Bézout at aperture `≤ 1/130` | corpus |
| M2 | The pairing on classes of the tower | open |
| M3 | The statement over a curve in comb language | open |
| M4 | Bézout at larger bounded apertures, against the verified windows | open |
| M5 | Castelnuovo–Severi for combs (RH) | open |

## 9. Pillar theorems

| Theorem | Lean |
|---|---|
| The pairing of the degree points on a packet is `2 d₁ d₂ − Z(f)` | corpus `AbsoluteGeometryOfSpecZ.tendsto_degreePairing_degrees_sub_zeroSum` |
| The inequality up to the defect of the zeros off the line; RH iff the defect vanishes | corpus `tendsto_degreePairing_le_degrees_add_offLineDefect`, `riemannHypothesis_iff_offLineDefect_eq_zero` |
| The inequality on packets of width `≤ 181/250` | corpus `tendsto_degreePairing_le_degrees_of_width` |
| The comb selects the contacts | corpus `combBezout_iff` |
| A section count with Riemann–Roch and Bézout is the Hodge index | corpus `ArithmeticCorrespondencePositivity.hodgeIndex_iff_exists_sectionCount` |
| The index law of a Hermite–Biehler sum | corpus `InfiniteRankPurityTheory.hermiteBiehler_index_general` |
| Logarithmic windows with exceptional sets | corpus `SurfaceOfSpecZ.ScaleLocality.riemannHypothesis_iff_prime_logarithmic_windows_off_finset` |

## 10. Traps

| Trap | Truth |
|---|---|
| The pairing is a limit object | in the normal form it is an exact matrix at every finite scale |
| The self-intersection of `Γ_n` is a number of the point | it is the density of the comb; on the multiples of `g` it is larger by `log g` |
| Bézout for effective divisors is the content | for effective divisors without common graphs it is free: jets and contacts are nonnegative. The content is Riemann–Roch for classes with a packet component |
| A count of sections gives the sign | on the tower the count sees the two rulings of each line and no packet |
| Contacts lower the pairing | they raise it; the inequality bounds jets plus contacts from above by the pole |
| A positive potential helps | the potential is positive and the Dirichlet form enters with the minus sign: the form is frustrated |

## 11. Context

| Programme | Interface |
|---|---|
| AbsoluteGeometryOfSpecZ | the square, contacts, jets, comb finite parts, the tower of lines, the pairing of the degree points and its limit |
| ArithmeticCastelnuovoSeveri | polar surfaces, the scaling surface, curve data and fakes, Pontryagin laws, the degree filtration |
| ArithmeticCorrespondencePositivity | the section-count theorem |
| InfiniteRankPurityTheory | the index law, its semicontinuity, the line law, the fixed part of a family |
| ArithmeticWeightTheory | the fixed-part theorem for arithmetic families |
| SurfaceOfSpecZ | scale locality: logarithmic windows, exceptional sets, effective prime classes |
| HyperbolicArakelovTheory | the arithmetic clock and its ordered energies |
| SelectivePositivityAndThresholdLaws, VerifiedHeightRungs | Weil positivity on bounded windows |

## 12. Success criteria and contributions

HFP succeeds when each of Q1–Q5 has a theorem-level answer, each tool T1–T6 is a module with
theorems that another programme can import, each criterion K1–K7 is decided on the mechanisms of
§4, and the milestones M2–M4 are theorems. M5 is the Riemann hypothesis.

A **contribution** must be unconditional; act on the pairing of the degree points or on a
count of sections of the tower; say which question, tool, criterion or milestone it addresses;
and be one of: an exact identity of the normal form, an inequality at finite scale, an index
statement, a calibration on a curve or on a fake, or a no-go with its strongest positive
survivor. Equivalences with the Riemann hypothesis that restate the inequality on packets are
not contributions.
