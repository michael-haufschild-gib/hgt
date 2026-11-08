# Counting holography (CTH) — programme card

- **ID:** cth
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0711/obstacles-summary.md §2.7, §2.10
- **Statement:** a count law is a Born rule (quadratic, covariant under the delay: the functional equation) plus a count (nonnegative: universal damping); over ℤ the Born rule holds and the count is RH.

## Goal
Develop the field of §2.10: objects, tools, answers to its six questions, calibration on true curves,
fakes, throats, the genus-two graph and Farey counts. Lean folder
`formal/GaloisForLFunctions/CountingHolography/`, umbrella `CountingHolography.lean` (in `MainTheorems`),
README there.

## Gates
- [x] 0 → 1  in-progress: questions and tools fixed by §2.10
- [x] 1 → 2  every answered question has a proof
- [x] 2 → 3  every answer formalized, each module checked with `lake --old env lean`

## Questions and tools (status)

| Item | Answer | Lean |
|---|---|---|
| First rung | level one ⟺ `q ≤ 19`; every level ⟺ `q ≤ 3`; Born rules `c₁𝒬₁ ⊕ c₂𝒬₂`, positive ⟺ `q ≤ 3` | `TheGenusTwoRung`, `TheBornRuleAtGenusTwo` |
| Every genus | tower count law ⟺ unitary ⟺ crude count; count law on every odd-degree hyperelliptic curve; Rosati height = trace-form Born rule; Born rules of any bank (Krein + Wronskian, Hermitian per trace class, hyperbolic off-circle quadruples) | `TheCountLawAtEveryGenus`, `TheCountLawOfATrueCurveAtEveryGenus`, `TheRosatiHeightIsTheBornRule`, `TheBornRulesOfAnOscillatorBank` |
| §2.7 candidates | linear counts never obey the law; a count through one linear count is degenerate | `LinearCountsAreDegenerate`, `shellCount_add` |
| Q1 | RH ⟺ `Q` is the Tate limit of a count; Gram = function of `m/n`; Hecke dilation isometry | `TheTateLimitOfACount` |
| Q2 | nondegenerate Born rule ⇒ partner law; genus one unique; throat `b ≠ 2` none | `TheBornRuleOfABlackHole` |
| Q3 | integrality + sharp trivial zeros + FE + first law do not force the tower law | `firstCountLaw_does_not_force_damping` |
| Q4 | boundary square ⟺ `t² ≤ 4q` ⟺ probe ring in `ℂ`, count = area | `TheBoundarySquareIsTheOscillation` |
| Q5 | Hecke supplies conservation at `1 ± πⁿ`, holds on fakes | `HeckeSuppliesConservationNotTheLaw` |
| Q6 | horocycle mean = Farey count; RH ⟺ square-root Farey law | `TheFareyReadingOfTheHorocycle`, `TheHorocycleRateIsTheSquareRootFareyLaw` |
| Second physical question | zero-free strip `Re ρ ≤ 1 − 2δ` ⟺ rate `y^{1/2+δ−ε}`; zero-free half-plane ⟺ polynomial lower bound of `ζ` | `zeroFreeStrip_iff_fareyCount_rate`, `zeroFree_iff_zeta_lower_bound` |
| A32 (genus two through Jacobians) | bielliptic `y² = h(x²)`: sum of Manin's two height counts is the genus-two count law; Hasse–Weil `16q` at every level | `TheJacobianCountOfABiellipticGenusTwoCurve` |
| Every hyperelliptic curve (A32 extension) | even-degree RH proved: unit of nonsquare norm kills high degree sums for every squarefree f; trivial root χ(lc) from infinity; descent from splitting field through the odd model; count law at every level for every hyperelliptic curve, every genus-two curve | `TheCountLawOfEveryHyperellipticCurve` |
| Fail for non-arithmetic groups | every Hecke group `G_q`, `q ∉ {3,4,6}`: Niven + Dickson give a second real place of `ℚ(λ_q²)` where the count of `γₙ²` is negative; `G₃, G₄, G₆` one place | `TheCountFailsAtTheSecondPlaceOfAHeckeTriangleGroup` |
| Boundary operator algebra (tool) | `R[π]/(π²−tπ+q)` with partner involution: GNS form = Krein square for every state; positive state ⟺ `*`-rep on ℂ ⟺ damped; bank faithful ⟺ strictly damped; Hilbert involution positive on every black hole (C* blindness) | `TheBoundaryAlgebraOfABlackHole` |
| Sharp shells | horoball count = Möbius sum of quarter-disc lattice sums; unconditional rate `y^{1/2} log(1/y)`; exact three-term error | `TheRateOfASharpShell` |

## Open
Count over ℤ (= RH); a height producer on simple genus-two Jacobians (the count law itself is proved for every genus-two curve); Farey reading of non-arithmetic Hecke groups;
RH rate for sharp shells (`Σ μ(d) E(X/d) = O(X^{1/2+ε})`).

## Log
- 2026-11-07 — created; 14 modules formalized
- 2026-11-08 — 19 modules: Jacobian count at genus two, Hecke groups, sharp shells, boundary algebra, every hyperelliptic curve
