# SQB: full closed-period product does not collapse

RH remains UNPROVED. Active goal stays open. Frontier map is READ ONLY; this work did not edit it. No experiment, numerical proof input, added axiom, or commit/push. All owned Lean/Lake processes collected; final scan had none.

## Full chain and exact new result
Original modular source → independent current comparison or full-Xi spectral occurrence → critical-line classification → RH. The new result controls the singular resistance/current product, without claiming the quotient-area quarter inequality or independent spectral occurrence.

Canonical module: formal/GaloisForLFunctions/RHTower/SelbergMaassClosedPeriodProduct.lean (21 public theorems), importing only SelbergMaassSliceRigidity. Wired once into RHTower.lean. Depends on mem:selberg/sqb-maass-slice-rigidity-2026-09-09 and previous full-current/path results.

For the actual nonzero principal-congruence Maass cusp eigenform with 0<mu<1/4, every y>0 has r>0 and c>8 such that 0<e<=r implies c <= (N+1)^2 R_e(y) E_e(y). R_e is the ORIGINAL unit-period reciprocal-radius integral. E_e is the COMPLETE original horizontal current: (pairEnergy_x + phaseCurrent_x^2 + e^2 directionalEnergy_x)/radius^3, integrated over unit period. No zero-free period, nodal order, positive E0 or bounded product is added.

The full augmented unit vector u_e=(e,F_q)/radius closes after w=N+1; scalar integrands 1/radius and H_e have period ONE. Keep this distinction. Two complementary arcs between a<b<a+w have same squared chord d. Their Cauchy bounds d<=R1 E1 and d<=R2 E2 give d(R1+R2)<=R1R2(E1+E2), then 4d<=(R1+R2)(E1+E2), using d(R1-R2)^2>=0. Exact integral splitting/integer-period scaling identify full product as w^2 R_e E_e.

Slice rigidity supplies D>0 somewhere at EVERY positive height. Original zero means produce negative correlation kappa<0 at a point within centered level period. With Q=radius_1(z)radius_1(t)>0, delta=-kappa/Q>0 and r=min(1,sqrt(-kappa)/2)>0, e<=r implies e^2<=-kappa/4 and radius_e(z)radius_e(t)<=Q. Actual correlation identity gives augmented chord >=2+delta. Thus c=8+4delta>8 works. Ordered endpoints remain strictly inside a level period.

Consequences: actual product never tends to zero; EVERY finite limit L obeys 8<w^2 L; eventual E_e >8/(w^2 R_e); zero-free exact R0 E0 limit has same strict bound. If E0=0, E_e still tends to zero while retaining this full product floor and inverse-resistance lower rate. No product finite limit is asserted. Common flat nodes and zero current remain unexcluded. Positive product with divergent resistance does NOT imply E0>0. Constant 8 is a proved threshold; no optimality claim.

Main symbols/lines: source_period_product_floor:226, finite_product_limit_strict_lower:258, zero_current_retains_product_floor:279. Other main symbols: two_arc_effective_resistance, four_chord_le_level_product, uniform_chord_margin_of_negative_correlation, period_product_not_tendsto_zero.

## Broad discovery
Research tool OR searches, no per-module cap, full metadata retrieval: joint limit/effective resistance/capacity/closed curve/two arcs/periodic Poincare/finite order zero = 2517 rows/367 modules; weighted mean/zero mean/chord/loop energy/Wirtinger/Lyapunov inequality =1004 rows/276 modules. Files /tmp/sqb22_capacity_broad.json and /tmp/sqb22_loop_broad.json. These are METADATA counts, not all-proof inspections. Inspected HTGeometry/StokesCartanCoronaCapacity.lean finite-current parallel_completion algebra as a lead; new theorem directly proves original two arcs without importing tree abstraction. CirclePoincareWirtinger only located, not read or used. Selected source reads: augmented source/correlation, chord Cauchy, unipotent exact periods and slice rigidity. No nodal-order experiment or toy asymptotic proved.

## Full audit PASS
Scratch /tmp/sqb22_product.lean via lake env lean, then canonical source lake env lean; both clean logs /tmp/sqb22_product.log and /tmp/sqb22_product_source.log. Preflight lake --no-build build GaloisForLFunctions.RHTower.SelbergMaassClosedPeriodProduct showed ONLY intended leaf stale. Final lake build of that leaf passed in 4.3s; 8822 dependency jobs other than leaf cached. No full/umbrella build. Logs /tmp/sqb22_product_{preflight,build}.log.
All21 separately #print axioms in /tmp/sqb22_axioms.lean: only propext/Classical.choice/Quot.sound. /tmp/sqb22_axioms.log; names /tmp/sqb22_audit_names.txt. Index/lint PASS /tmp/sqb22_{index,lint}.log; lint only existing large-file warnings. All21 indexed exactly once /tmp/sqb22_indexed_declarations.json. Whitespace PASS; process scan /tmp/sqb22_processes.txt had no Lean/Lake processes.

Paper proof and complete audit: docs/drafts/pipeline/3-formalized/sqb-closed-period-current-product.md. Stage1 card same basename. Universal-law STATUS has route-independent coupled-singular-limits constraint. Shared peer changes preserved (peer inserted temporal-switching entry during work; patch was retried against updated header).

## Lean implementation notes
Augmented `unit` conflicts with Set.unit when unfolding: use SelbergMaassAugmentedDirection.unit. distanceSq_comm in chord module is PRIVATE; new augmented_distance_symm is public. Prove symmetry via normSq_apply/sub_re/sub_im/ring. No normSq_sub_comm API. mul_le_mul_right is monotonicity, not iff; positive cancellation uses (mul_le_mul_iff_left_0 hp).mp with actual Lean subscript ₀. Integer period j is ((N+1:Nat):Int); simp Int.cast_natCast and one-period identities. All APIs scratch verified.

## Next unresolved issue
Product collapse is now excluded, but not zero-current limiting bands or actual flat nodes. Further work must quantitatively remove/control resistance or obtain original-source rigidity/quarter area comparison. Analytic/PDE nodal geometry or a stronger full-source comparison could be relevant; no proof of these has been found here. Independent full-Xi occurrence remains separate and open.