# Step 41: rational-node criterion — RH as a countable family [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/XiResolventRationalNodeCriterion.lean`, wired after
`XiResolventNodalSingleMinorCriterion` in RHTower.lean. All declarations audit to
[propext, Classical.choice, Quot.sound]; olean-built; compile warning-free.

## Capstone

`riemannHypothesis_iff_forall_rational_nodal_single_minor {X} (hX : 0 ≤ X)`:
RH ⟺ ∀ (j m : ℕ) (c : Fin j → ℚ), (∀ i, 0 < c i ∧ (c i : ℝ) ≤ 1) →
0 ≤ Re(M_p(0)M_p(2) − M_p(1)²) for p = `Polynomial.X ^ m * finNodalPolynomial (fun i => (c i:ℝ))`.
Index family countable: `rational_nodal_index_countable : Countable ((j : ℕ) × ℕ × (Fin j → ℚ))`.

## Chain

rational tuples → (stability + density) real tuples → (enumeration bridge) Finset nodal → RH
(step-40b nodal criterion). Forward a fortiori from step-36 forward.

## Stability ladder (all explicit constants, S = mass bound)

- `norm_sub_node_le`: nodal factor ≤ 2 on unit disk.
- `norm_evalRealPolynomial_shiftedFinNodal_le`: eval ≤ 2^j; `_sub_le`: ≤ j·2^j·ε via corpus
  `GaloisForLFunctions.norm_prod_sub_prod_le` (HTGeometry/PrimeEulerProductAperture, bound
  card·C^card·δ).
- `norm_xiPolyMoment_shiftedFinNodal_le`: ≤ S·4^j; `_sub_le`: ≤ S·j·2^(2j+1)·ε.
- `abs_re_datum_shiftedFinNodal_sub_le`: datum Lipschitz ≤ 8j·S²·16^j·ε.
- `finNodal_datum_re_nonneg_of_rational`: density — rationals chosen in
  (max(c_i−ε, c_i/2), c_i) via exists_rat_btwn stay in (0,1]; ε = δ/(L+1);
  le_of_forall_pos_le_add closes.
- Enumeration bridge: nodalPolynomial R = finNodalPolynomial (orderIsoOfFin enumeration) via
  `← Finset.prod_coe_sort` + `Equiv.prod_comp`.

Numeric pre-cert: 300 random configs, worst ratio 5e-3 of the bound.

## Lean traps

- `have h := lemma args` (no expected type) cannot infer an implicit appearing only inside a
  polynomial argument of the conclusion — pass `(m := m)`.
- `calc ‖_ + _‖ * ...` placeholder heads are parse errors — use plain `exact` on the rewritten
  goal or `refine le_trans ... (le_of_eq ?_)`.

## Audit / significance

Countability of an RH criterion is not itself new (Li's criterion); the content is the
structure: single 2×2 Hankel minors of nodal reweightings at ONE interior point, density powered
by our own effective constants. Provisional [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] as part of the
steps 36-41 arc. Next: nodal supply via two-scale bridge; window optimality vs step-38 masking
config; order/lattice structure on the rational family. Card: xic-order-one-growth-organ.md.
