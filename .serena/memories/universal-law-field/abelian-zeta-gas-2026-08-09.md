# Abelian zeta gas cycles 1–3 — 2026-08-09 (Claude)

## Structural identification (the load-bearing fact)

ULF-EQG-1's Euler q-Gamma source IS the zeta-Gibbs measure `P(A) = C_sigma |A|^{-sigma}` on
finite abelian groups (normalization = Erdős–Szekeres `prod_j zeta(j sigma)`), equivalently
independent geometric occupations of prime-power modes (p,j) with ratio p^{-j sigma},
equivalently the unique KMS_sigma state of the prime-power Toeplitz gas with energies `j log p`
(H = log|A|). Euler's q-binomial identity = the change of observer. Corpus integer M = SOCLE
ORDER |soc A|.

## Stage-2 cards (all paper-proved, NO LEAN yet)

**ULF-GAS-1** `abelian-zeta-gas-two-observable-divisor-dictionary-and-condensation-wall-law.md`:
zeta-Gibbs law + two-parameter family (|A|^{-sigma}|soc A|^{-tau}, Z = prod_j zeta(j sigma+tau));
grand response prod_j zeta(j(sigma+u)+v)/zeta(j sigma); EQG.13 = telescoping; KMS existence AND
uniqueness at EVERY sigma>0 (monomial-killing proof) — NO BC-type simplex transition, walls are
OBSERVABLE CONDENSATION; sharp fan: depth-g condenses at sigma = 1/g, critical abscissa =
squarefull wall, genus chambers = non-condensation; translation vs dilation divisor calculi
(joint divisor = line arrangement in C^2, depth = slope; dilation has natural boundary
Re u = -sigma; per-depth clean landing NOT unconditional there); RG: delta_d gives
phi_sigma o iota_d = phi_{d sigma}; entropy D+D-bar = sigma sum Lambda(n)n^{-sigma}. PRD-E gate
passed at paper level.

**ULF-GAS-3** `condensed-phase-probabilistic-death-modulus-budget-and-gaussian-fluctuation-law.md`:
for 1/2 < sigma <= 1 the socle prime series converges for NO centering (symmetrization + BC-II +
Levy) — probabilistic organ dies at the condensation wall = PRD-C instantiated; exact fan-graded
defect -log|phi_p| = sum_{j,r} q^{jr}(1-cos r theta)/r; modulus budget diverges (Mertens + PNT),
no unimodular gauge, genus-one counterterm pays budget EXACTLY; "phase cannot pay a modulus
debt" = quantitative history-polarization, exchange rate A_P - Re B_P; unconditional Lindeberg
CLT, variance ~ sigma^2 P^{1-sigma} log P/(1-sigma); NOT the Selberg model (over-claim caught).

**ULF-GAS-4** `parity-duality-rg-shell-splitting-and-multiplicative-resolution-cap-law.md`:
parity mass = Z(2 sigma)/Z(sigma)^2; signed ladders have doubled arguments (parity lives in the
delta_2 shell); fermionic (distinct-factor) gas ≡ odd-depth bosonic sector ON THE ORDER ORGAN AT
THE LEVEL OF LAWS (Euler distinct=odd), separated by the socle organ at p^3 — exact arithmetic
instance of ULF-CFL-1 intervention separation; fan splits: fermionic shells {1,1/3,1/5,...} skip
1/2; 1/2 = delta_2(pole wall), invisible to fermions; multiplicative resolution cap: order-tilt
Markov certificates are 4^U-invariant under multiplicative fattening ⇒ short-interval (MR-type)
events undecidable by the solvable cone. MR wall and solvable calculus disjoint BY THEOREM in
both directions (with GAS-3).

## Failed

ULF-GAS-2 → `5-failed/universal-law-field/grand-response-positivity-locus-conjecture.md`.
FALSE as stated: obstruction is ONE-POINT dispersion, not MRBilinear; analytic continuation
already existed (EQG 9.1) and is divisor-blind. Do not re-attempt.

## Stage-1 open

**ULF-GAS-5** `automorphism-moment-organ-and-moment-horizon-charter.md`: fourth organ = moment
observer (#Sur/#Hom). PROVED calibration: sharp moment horizon — E[#Sur(A,(Z/p)^r)] < ∞ iff
r < sigma (Euler PGF radius p^sigma) — zeta gas is OUTSIDE the moment-determined CL/Sawin–Wood
universality class; horizon = abscissa. Frozen hunch: sub-horizon moment indeterminacy. MANDATORY
read-first: Fulman–Kaplan 1803.03722, Fulman 1403.0473/1307.0879, Sawin–Wood 2210.04278,
2402.16625, Van Peski thesis. Step one of next cycle: check Sawin–Wood growth hypotheses BEFORE
constructing anything.

## Parents (cite, do not re-derive)

Julia primon gas; Bost–Connes; Erdős–Szekeres/Kendall/Ivić; Estermann/Kurokawa/Bhowmik–Essouabri;
Fristedt; Chair 1306.5415; Marcolli–Ren 1704.06367; Cohen–Lenstra; Spector fermionic primon;
Loève/Kahane; Lindeberg–Feller. Internal: ULF-EQG-1, ULF-IPKMS-1, ULF-QGPRH-1, ULF-CFL-1,
ConstitutiveHistoryPolarization.

## Next moves (not yet frozen beyond GAS-5)

- Execute GAS-5 step one (Sawin–Wood hypothesis check).
- PRD-A prolongation/non-Noetherianity front remains untouched.
- A fourth organ coupling law (moment ↔ fan/divisor) is the anti-theatre demand.
- Lean targets when Lean sessions resume: GAS 2.1/3.1/5.1, GAS.12, GAS3.1, GAS3-T1.1, GAS4.3,
  GAS5.1/5.2 (finite layers first).

## Session directive

Goal loop (hgtl7): no Lean writing this session; stage-2 cards await certification per
`_LEAN-CERTIFICATION.md`.
