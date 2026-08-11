# The explicit-formula organ: card, scoping, brick 1 (2026-08-11)

Card: `docs/drafts/pipeline/1-in-progress/xic-order-one-growth-organ.md`.

## Synergy audit verdict (frontier map, all routes)
- No Frankenstein assembly closes an RH endpoint: endpoint-iff composition through RH is vacuous;
  map §3 merger no-gos (longitudinal–transverse conservation, residue-promotion anomaly) close
  wiring-level splices; §6's five distinct missing theorem classes remain.
- HOSTILE CHECK result: the O ↔ xiWeilPolarization "dictionary" is NOT definitional — O's
  `ccmPublishedRestrictedWeilMatrix` is built from prime/archimedean pairings
  (`criticalMellinStieltjesPairing` − archimedean), the polarization is a zero-side sum. Their
  identification IS Guinand–Weil. Recorded on the card as dead.
- Real secondary splices: (i) T×U share the fixed Cassini source — U item 19 jet dictionary
  (formal) + T's Wold pole carrier/continuation (formal) → arithmetic constraint on U's first
  crossing location (not yet built); (ii) T's prime-gap premise could be discharged by
  formalizing Ingham density on PNTPlus's ZetaBounds (large).
- THE shared missing organ (four lanes: C1/Gauss producer, O ground space, U item 48 boundary
  equation, T prime side): the Guinand–Weil explicit formula.

## The cornerstone reduction (verified interface points)
Target: `∃ B, ∀ z, ‖XiC z‖ ≤ exp(B(1+‖z‖)log(2+‖z‖))`. Route WITHOUT Stirling/PL:
`completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2)/2`; `WeakFEPair.Λ₀ = mellin f_modif`
(`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`); f_modif decays rapidly at BOTH ends
(∞: `isBigO_atTop_evenKernel_sub`; 0: `hf_modif_FE` folds to g_modif at 1/x). So
‖Λ₀(s)‖ ≤ ∫ t^{Re s−1}‖f_modif‖ ≤ C·(Gamma-type tails).
**Capstone needing NO Cartan: `∃ ρ, xi ρ = 0`** (first formal nontrivial zero): empty divisor ⇒
`xiCanonicalProduct ≡ 1` (empty tprod) ⇒ quotient = XiC ⇒ `xiHadamardQuotient_has_log` +
growth + `xiHadamardQuotient_constant_of_log_reBound` ⇒ XiC constant ⇒ contradiction with
`xi 0 = 1/2`, `xi 2 = π/6` (`riemannZeta_two`, `Real.pi_gt_three`).
Downstream (later cards): Cartan min-modulus for the canonical product → Hadamard constancy →
partial fractions of XiC′/XiC → glue with prime side (−ζ′/ζ = ΣΛn^{−s}) → explicit formula.
Mathlib ALSO owns Jensen (`MeromorphicOn.circleAverage_log_norm`) → growth ⇒ N(r) counting.

## Brick 1 [LEAN-PROVED]
`formal/GaloisForLFunctions/HTGeometry/MellinGrowthBounds.lean` (wired, umbrella green,
axiom-clean): `rpow_mul_exp_neg_pi_le`, `integrableOn_rpow_mul_exp_neg_pi`,
`integral_rpow_mul_exp_neg_pi_le` (∫₁^∞ t^a e^{−πt} ≤ (2a²+9)^a + 1),
`log_gammaTail_bound_le` ((1+a)(1+3log(3+a)) shape).

## Next bricks (in order)
2. f_modif majorant for hurwitzEvenFEPair 0: extract constants from BigO at atTop + continuity
   sup on [1,T₀]; transport to (0,1) by `hf_modif_FE` (‖f_modif t‖ = t^{−1/2}‖g_modif(1/t)‖).
3. Mellin-norm assembly: ‖mellin f_modif s‖ ≤ ∫ t^{σ−1}‖f_modif‖, substitution u = 1/t on (0,1),
   both pieces ≤ Gamma tails (brick 1 with shifted exponents; e^{−πt} vs rate v: adjust brick or
   rescale — brick 1 is stated for rate π; general rate version may be needed).
4. xi/XiC wrap: xi = s(s−1)/2·Λ₀ + 1/2, XiC z = xi(1/2+zI); polynomial factor absorbed into B.
5. Nonemptiness capstone as above.

## Lean traps
`Real.pi_gt_three` needs `import Mathlib.Analysis.Real.Pi.Bounds`. `Real.log_le_log (hx : 0 < x)`
current. `exp_neg_integrableOn_Ioi c (h : 0 < b) : IntegrableOn (fun x => exp(−b*x)) (Ioi c)`.
`integral_exp_neg_Ioi c : ∫_{Ioi c} exp(−x) = exp(−c)`. positivity can't do `0 < π/2`
(use `half_pos Real.pi_pos`) nor rpow-nonneg of a variable real base (supply `Real.rpow_nonneg`).
