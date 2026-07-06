- `RHTower/PinnedWindow.lean`: added `xi_window_pinned_of_single_circle_pair_chain`. Big picture: carrier-vs-linear and ξ-vs-carrier bounds on the same two boundary circles now combine by triangle inequality into direct pinning of ξ against the linear critical-line reference; this is the actual one-circle-pair constraint endpoint, not a recentered flow.
- `RHTower/PinnedWindow.lean`: added `xi_window_pinned_of_emCarrier_single_circle_pair` and `riemannHypothesis_of_emCarrier_single_circle_pair_windows`. Big picture: EM remainder, finite `emCarrier`/`gN` closeness, and a LOW floor on one boundary-circle pair now suffice when the carrier is within `< 1/3` of the linear reference; the per-zero RH certificate is one pair of circles plus a static floor constraint.
- `RHTower/PinnedWindow.lean`: added `xi_window_pinned_of_double_domination_circles` and `riemannHypothesis_of_double_domination_circles_windows`. Big picture: the older double-domination route now has a circle-data version, but it uses an outer pair centered at `ρ₀` to locate the carrier zero and a recentered pair around the resulting `ρ'` to pin ξ; this connects the two existing circle maximum-principle nodes without pretending they are the same circles.
- `RHTower/PinnedWindow.lean`: added `xi_completedGN_linear_bound_of_emCarrier_circles` and rewired `xi_window_pinned_of_emCarrier_single_circle_pair` through it. Big picture: finite EM/circle floor data now yields a reusable linear-reference-scale bound `‖ξ−completedGN‖ ≤ ((1+ηC)/2)‖c(z−ρ₀)‖`; the same-circle RH route no longer hides this bridge inside its endpoint proof.
- `RHTower/PinnedWindow.lean`: weakened `xi_window_pinned_of_emCarrier_single_circle_pair` and `riemannHypothesis_of_emCarrier_single_circle_pair_windows` from closed-ball strip data to the exact circle-side hypothesis `0 < z.re ∧ z ≠ 1` on `sphere ρ₀ r₀ ∪ sphere ρ₀ R`. Big picture: the same-circle certificate now asks only for the boundary constraint it actually uses, making the per-zero RH burden strictly smaller and more one-dimensional.
- `RHTower/PinnedWindow.lean`: added `xi_window_pinned_of_linear_relative_circles` and rewired `xi_window_pinned_of_single_circle_pair_chain` through it. Big picture: the actual primitive boundary target is now explicit: a single relative bound for ξ against `c(z−ρ₀)` on two circles pins the whole window; finite-carrier circle data is just one way to produce that constraint.
- `RHTower/PinnedWindow.lean`: added `riemannHypothesis_of_linear_relative_circle_windows`. Big picture: RH now has a terminal gate whose per-zero certificate is only a critical-line linear reference plus a two-circle relative ξ bound, separating the final boundary constraint from the EM/completed-carrier machinery that may feed it.
- `RHTower/PinnedWindow.lean`: added `xi_linear_relative_bound_of_single_circle_pair` and rewired `xi_window_pinned_of_single_circle_pair_chain` through it. Big picture: the triangle step from carrier-vs-linear plus ξ-vs-carrier to the primitive ξ-vs-linear circle constraint is now a reusable theorem, so future same-circle certificate producers can stop at the direct relative bound.
- `RHTower/PinnedWindow.lean`: added `xi_linear_relative_bound_of_emCarrier_circles` and rewired `xi_window_pinned_of_emCarrier_single_circle_pair` through the primitive linear-relative pinning theorem. Big picture: finite EM remainder, finite `emCarrier`/`gN` closeness, LOW floor, and carrier-vs-linear control now directly produce the boundary constraint consumed by the RH gate; completed-carrier machinery is separated as an input producer, not the endpoint.
- `RHTower/PinnedWindow.lean`: rewired `riemannHypothesis_of_emCarrier_single_circle_pair_windows` through `riemannHypothesis_of_linear_relative_circle_windows` using `xi_linear_relative_bound_of_emCarrier_circles`. Big picture: the EM/floor same-circle RH endpoint now factors through the primitive linear-reference circle gate; finite completed-carrier data is cleanly a producer of the boundary constraint, and the RH step is centralized in the smallest circle interface.
- `RHTower/PinnedWindow.lean`: weakened `xi_window_pinned_of_emCarrier_single_circle_pair` and `riemannHypothesis_of_emCarrier_single_circle_pair_windows` from the normalized carrier budget `ηC < 1/3` to the exact total-budget constraint `ηC + (1+ηC)/2 < 1`. Big picture: the same-circle EM route now exposes the actual inequality consumed by the primitive linear-reference circle gate, so nonstandard certificate producers can use any budget split that makes the total boundary constraint contractive.
- `RHTower/DpolyBallFloor.lean`: added `riemannHypothesis_of_emCarrier_center_floor_pinned_windows_of_circles`. Big picture: the circle-data EM pinned RH gate can now consume one critical-line `dpoly` center floor plus the ball variation and reflected-χ budgets, with the chart and boundary-circle `CarrierFloorOn` inputs discharged internally by `carrierFloorOn_charts_spheres_of_center`.
- `RHTower/DpolyBallFloor.lean`: added `riemannHypothesis_of_emCarrier_single_circle_pair_center_floor_windows`. Big picture: the exact-budget same-circle EM route now accepts the same critical-line `dpoly` center-floor certificate language; the boundary-circle LOW floor is produced from the line carrier instead of being carried as an independent hypothesis.
- `RHTower/GNCarrierBridge.lean`: added `dirichletPoly_criticalLine_eq`, and `RHTower/DpolyBallFloor.lean` now uses the one-dimensional `dpoly` line carrier in `window_floor_cofinal_of_line_cofinal` and the center-floor RH gates. Big picture: finite density/cofinality outputs now feed the circle floor and RH endpoints in their native `dpoly` language, without a manual `dirichletPoly` translation step at each critical-line center.
- `RHTower/DpolyBallFloor.lean`: added `carrierFloorOn_charts_spheres_of_line_center` and routed the cofinal floor and center-floor RH gates through it. Big picture: the line-carrier center floor is now a first-class producer of both chart and boundary-circle LOW floors, so the `dpoly`-to-`dirichletPoly` translation is centralized instead of repeated at each consumer.
- `RHTower/RouteBFullSupport.lean`: added `four_phase_pi_le_randomShift` and `four_phase_pi_le_randomShift_of_caustic`. Big picture: the caustic four-phase estimate now applies with a finite measurable complement center, so isolated large-prime blocks can be used inside a full-support carrier without treating the composite remainder as a constant.
- `RHTower/FloorFailureCofinal.lean`: added `good_height_cofinal_of_native_Icc_model_lt_one` and `good_height_cofinal_of_native_Icc_randomShift`. Big picture: a model small-ball bound below density one, including the isolated random-shift full-support bound, now produces cofinally many native critical-line floors for `dpoly (n^-1/2) (Icc 1 N)`, which is the floor language consumed by the circle-window gates.
- `RHTower/SecondMoment.lean`: added `exists_dpoly_floor_in_window` and `exists_native_dpoly_floor_in_window`. Big picture: the basepoint-uniform mean value now yields a floor height inside EVERY prescribed interval `[T, T+U]` (not merely cofinally, and with no probabilistic model): if the modulus stayed ≤ t₀ the window second moment would be ≤ t₀²U, below the diagonal main term minus the off-diagonal constant.
- `RHTower/DpolyBallFloor.lean`: added `window_floor_in_every_interval` (+ SecondMoment import). Big picture: chart and boundary-circle carrier floors can now be anchored within `U` of ANY height — the placement shape the per-zero RH gates require — with the center found by the every-window second moment and spread by the existing variation/reflected-χ budgets.
- Constraint identified (no code): the every-window floor needs window length `U ≳ B_N/log N` with the elementary off-diagonal constant `B_N ~ N log N`, while certificate balls must have radius ≤ 1/2 to stay in the strip; so second-moment floors alone cannot anchor bounded-radius windows at large `N`. Bounded-radius placement needs a zero-count/minimum-modulus mechanism for the finite carrier (Jensen box count + Cartan-type minimum modulus) — that is the named next analytic target for the floor lane.
- `RHTower/CarrierSlope.lean` (new, in umbrella): `analyticAt_dslope_of_analyticAt`, `slope_deviation_ball_bound`, `exists_online_carrier_zero_of_sign_change`, `completedGN_linear_domination_of_slope_data`. Big picture: the first producer of the carrier-vs-linear circle face — the carrier is real on the critical line, so two signs give an on-line zero (IVT); at that zero the difference quotient is analytic, and Schwarz turns one slope sup `Δ` on one circle of radius `P` plus a derivative floor `κ` into the tangent-line domination `ηC = R·Δ/(P·κ)` on both certificate circles.
- `RHTower/CarrierSlope.lean`: added `xi_window_pinned_of_slope_circles` and `riemannHypothesis_of_slope_circle_windows`. Big picture: an RH gate whose per-zero carrier face is fully low-dimensional — an on-line carrier zero, one derivative floor at one point, one circle sup — composed with the EM/closeness/floor circle data; the previously unproduced `hcarrier` hypothesis of the same-circle gates is discharged by the tangent-line theorem.
- `RHTower/ZetaCarrier.lean`: added `zetaChi_norm_on_line`. Big picture: on the critical line the reflection `1−s` is the conjugate of `s`, so the χ-factor is exactly unimodular there — the reflected carrier term has on-line modulus equal to its Dirichlet part, anchoring all χ-budget estimates at the value 1 on the line.
- `RHTower/DpolyBallFloor.lean`: added `reflected_chi_budget_of_circle`, `re_lt_one_of_mem_closedBall_line`, and `riemannHypothesis_of_emCarrier_single_circle_pair_center_floor_circle_windows`. Big picture: the reflected term `χ(z)·D_N(1−z)` is analytic on strip balls, so the maximum principle supplies its ball budget from the boundary circle; with `R < 1/2` the strongest same-circle RH gate now consumes ONLY one-dimensional per-zero data (circles, one line value, scalars) — the certificate surface has no remaining 2D input. Residual for unconditional (non-certificate) discharge of the χ-budget: the vertical Stirling anchor named in `DigammaBounds`.
- `RHTower/MinimumModulus.lean` (new, in umbrella): `norm_lower_bound_of_anchor` and `carrierFloorOn_of_single_zero_anchor`. Big picture: the minimum-modulus engine — a zero-free analytic function's modulus cannot dip below its center anchor by more than `(M/m)^{2r/(R−r)}` (analytic log on the ball + Borel–Carathéodory); applied to the zero-free cofactor of a one-zero carrier window it produces `CarrierFloorOn` at LOGARITHMIC budget `log(M/m)`, replacing the `Σ log n·n^σ` Lipschitz spreading whose linear-in-carrier-length budget could not close at bounded window radius. The floor lane's quantitative obstruction is now a solved interface: floors need one anchor, one sup, one zero-distance.
- `RHTower/CarrierSlope.lean`: added `deriv_completedGN_of_factor` and `deriv_completedGN_floor_of_anchor` (+ MinimumModulus import). Big picture: the derivative-floor interface `κ ≤ ‖completedGN′(ρ')‖` introduced by the slope gates is now itself produced — at a one-zero window the completed derivative equals `archFactor·h` at the zero, and the minimum-modulus engine floors the zero-free cofactor from one anchor and one sup; `κ = a₀·m·(m/M)^{2r/(R−r)}`-scale from three scalars. Both remaining floor interfaces of the pinning route (carrier floor, derivative floor) now route through the same anchor/sup/zero-distance data.
- `RHTower/JensenCount.lean` (new, in umbrella): `simple_zero_structure_of_jensen` and `gN_one_zero_window_of_jensen`. Big picture: mathlib's Jensen inequality (`sum_divisor_le`) turns the scalar certificate `log(M/‖f c‖)/log(R/r) < 2` into the one-zero window structure — the known zero is the ONLY inner-ball zero, it is simple (order-of-derivative arithmetic), and the difference quotient is zero-free — which is exactly the input tuple of the minimum-modulus floor and the derivative-floor producers. The one-zero hypothesis of the pinning route is no longer an assumption: one anchor, one sup, two radii certify it.
- `RHTower/CarrierSlope.lean`: added `dslope_norm_le_of_boundary_sup` and `slope_deviation_of_boundary_sup`. Big picture: difference-quotient sups transfer from carrier sups — the quotient through a removable zero is bounded by `M/(P−dρ)` on the whole ball (max principle through the zero) and the slope deviation on the zero's circle by `2M/P`; the slope-gate input `Δ` is thereby derivable from one carrier sup, keeping every certificate datum anchored at the known window center.
- `RHTower/JensenCount.lean`: added `carrier_one_zero_package_of_signs_jensen`. Big picture: two line signs + one anchor + one circle sup + a Jensen quotient below two now produce, in one theorem, the located on-line zero of BOTH carriers together with its complete one-zero window structure (zero-free difference quotient, exact factorization, nonvanishing derivative) — the full carrier-side package of the pinning route from purely center-anchored 1D data.
- `RHTower/MinimumModulus.lean`: added `norm_le_on_closedBall_of_sphere` (generic maximum-principle sup transfer, circle to closed ball).
- `RHTower/ScalarCertificate.lean` (new, in umbrella): `xi_window_pinned_of_center_scalars` and `riemannHypothesis_of_center_scalar_windows`. Big picture: the first RH gate whose per-zero certificate is anchored entirely at a KNOWN critical-line center — two signs bracket the carrier zero, a Jensen quotient below two makes it unique and simple, the minimum-modulus engine converts one anchor and one sup into the derivative floor and the boundary-circle carrier floors, and the difference-quotient transfer converts one completed sup into the slope budget. No datum refers to the (uncomputable) zero position: the certificate is scalars, signs, and sups over known regions — the shape a finite verification or an asymptotic estimate must discharge.
- `RHTower/DpolyBallFloor.lean`: added `gN_line_anchor_of_dpoly_floor` and `exists_gN_line_anchor_in_window_of_secondMoment`. Big picture: the banked every-window second-moment floor now feeds the center-scalar gate's exact anchor `m_J ≤ ‖gN N c‖` once the reflected center term is below the reserve `t₀ - m_J`; the next analytic inequality chain is therefore explicit in the same scalars used by `ScalarCertificate`.
- `RHTower/ScalarCertificate.lean`: added `jensen_quotient_lt_of_anchor_floor` and `gN_jensen_budget_of_anchor_floor`. Big picture: the Jensen budget in the center-scalar gate can now be checked using only the certified anchor floor `m_J`, not the unknown actual value `‖gN N c‖`; this turns another ScalarCertificate input into an explicit scalar inequality fed by the second-moment anchor bridge.
- `RHTower/ScalarCertificate.lean`: added `xi_window_pinned_of_center_floor_scalars` and `riemannHypothesis_of_center_floor_scalar_windows`. Big picture: the center-scalar gate now has a canonical floor form where the minimum-modulus inputs are fixed as `m_J / rz` and `M_J / (rJ - rz)`, and Jensen is checked against the certified floor `m_J`; the remaining analytic work is the explicit scalar inequality chain on these floor/sup quantities, not auxiliary witness selection.
- `RHTower/ScalarCertificate.lean`: added `xi_window_pinned_of_center_floor_canonical_kappa` and `riemannHypothesis_of_center_floor_canonical_kappa_windows`. Big picture: the center-floor gate no longer quantifies the derivative-floor scalar `κ`; it is fixed internally to the canonical minimum-modulus value `a₀ * (m_J / rz) * exp(...)`, so the remaining slope budget is a direct inequality in the anchor floor, carrier/completed-carrier sups, radii, and archimedean floor.
- `RHTower/ScalarCertificate.lean`: added `slope_budget_of_cross_mul`, `xi_window_pinned_of_center_floor_cross_slope`, and `riemannHypothesis_of_center_floor_cross_slope_windows`. Big picture: the canonical center-floor gate can now consume the slope budget as the product inequality `6 * R * M_G < P^2 * κ` with `κ` fixed to the canonical minimum-modulus derivative floor, replacing the nested `η + (1 + η) / 2 < 1` division constraint by a direct scalar inequality.
- `RHTower/DpolyBallFloor.lean`: imported `ScalarCertificate` and added `xi_window_pinned_of_line_floor_cross_slope` plus `riemannHypothesis_of_line_floor_cross_slope_windows`. Big picture: the newest cross-multiplied center-floor scalar gate can now be fed by the one-dimensional critical-line `dpoly` floor and reflected center reserve, replacing the primitive `m_J ≤ ‖gN N c‖` anchor with the banked line-floor language.
- `RHTower/DpolyBallFloor.lean`: added `riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows`. Big picture: the cross-multiplied line-floor scalar RH gate can now choose its critical-line center height from the every-window second-moment floor internally; the remaining non-floor data are required uniformly over the chosen interval, making the next analytic burden a uniform scalar/circle estimate on `[T,T+U]` rather than a supplied center.
- `RHTower/DpolyBallFloor.lean`: added `line_center_closedBall_strip` and `riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip`. Big picture: the second-moment-selected cross-slope RH gate no longer needs a raw uniform strip hypothesis for critical-line centers; the scalar radius condition `RJ < 1/2` now supplies `0 < Re z < 1` on the known center balls automatically.
- `RHTower/DpolyBallFloor.lean`: added `line_point_mem_closedBall_line_center_of_abs_sub_le`, `line_interval_mem_closedBall_line_center_of_endpoint_bounds`, and `riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket`. Big picture: the second-moment-selected scalar RH gate no longer needs raw bracket containment data; the endpoint inequalities `T+U-rz ≤ t₁` and `t₂ ≤ T+rz` certify that the whole sign bracket lies in every possible selected center ball.
- `RHTower/DpolyBallFloor.lean`: added `point_mem_line_center_ball_of_quadratic` and `riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket_quadratic_target`. Big picture: the second-moment-selected scalar RH gate no longer needs raw target-zero ball membership; the target containment can now be supplied by the scalar inequality `(ρ.re-1/2)^2 + (ρ.im-τ)^2 < R'^2` uniformly over the admissible center interval.
- `RHTower/DpolyBallFloor.lean`: added `interval_abs_le_of_endpoint_abs_le`, `quadratic_target_of_endpoint_abs_im_bounds`, and `riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket_endpoint_target`. Big picture: the target-zero containment in the second-moment-selected scalar RH gate is now finite endpoint data: bounds on `|ρ.im-T|` and `|ρ.im-(T+U)|`, plus one quadratic radius budget, imply the former uniform target inequality over all selected centers.
- `RHTower/DpolyBallFloor.lean`: added `reflected_center_norm_eq_line_dpoly` and `not_line_dpoly_floor_and_reflected_reserve`. Big picture: the old attempt to turn a critical-line `dpoly` floor into a `gN` anchor by requiring a smaller reflected χ-term is formally void for positive reserve: on the critical line the reflected term has exactly the same norm as the Dirichlet part, so the anchor producer must use `gN`/Hardy phase or sign structure directly.
- `RHTower/DpolyBallFloor.lean`: imported `HardyCarrier` and added `gN_line_anchor_of_hardy_floor`, `xi_window_pinned_of_hardy_floor_cross_slope`, and `riemannHypothesis_of_hardy_floor_cross_slope_windows`. Big picture: the replacement anchor producer is now direct: a finite Hardy-amplitude floor `m_J ≤ |H_N(τ)|` supplies `m_J ≤ ‖gN N(1/2+iτ)‖`, avoiding the formally void reflected-reserve route while keeping the same cross-multiplied scalar certificate surface.
- `RHTower/DpolyBallFloor.lean`: added `riemannHypothesis_of_window_hardy_floor_cross_slope_endpoint_target`. Big picture: the direct Hardy-anchor route now has the same finite window geometry surface as the scalar endpoint gates: a witness `τ ∈ [T,T+U]` with `m_J ≤ |H_N(τ)|` supplies the center anchor, while target containment, bracket containment, strip control, and circle/EM budgets are scalar endpoint or uniform window inequalities.
- `RHTower/DpolyBallFloor.lean`: added `exists_abs_floor_in_window_of_l2`, `exists_hardy_floor_in_window_of_l2`, and `riemannHypothesis_of_window_hardy_l2_cross_slope_endpoint_target`. Big picture: the endpoint Hardy gate no longer needs a primitive point witness when a strict interval second-moment inequality is available; `m_J^2 U < ∫_T^{T+U} H_N(τ)^2 dτ` now produces the required center anchor `m_J ≤ |H_N(τ)|`, so the remaining analytic core is the explicit Hardy L2 lower-bound versus scalar budget chain over each window.
- `RHTower/HardyCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added squared-Hardy regularity (`H_N(τ)^2 = ‖gN N(1/2+iτ)‖^2`, continuity, interval integrability) and tightened the Hardy L2 RH gate so it no longer asks for an integrability premise. Big picture: the remaining Hardy-window input is now only the strict scalar lower bound `m_J^2 U < ∫_T^{T+U} H_N(τ)^2 dτ`; regularity is discharged from the finite carrier itself.
- `RHTower/DpolyBallFloor.lean`: added `exists_hardy_floor_in_window_of_gN_line_l2` and `riemannHypothesis_of_window_gN_line_l2_cross_slope_endpoint_target`. Big picture: the window L2 input can now be stated directly as the phase-free line carrier inequality `m_J^2 U < ∫_T^{T+U} ‖gN N(1/2+iτ)‖^2 dτ`; the Hardy-amplitude gate is recovered internally from the squared-line identity, aligning the remaining analytic budget with the same `gN` scalar surface used by the circle estimates.
- `RHTower/HardyCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `norm_add_sq_complex`, `norm_gN_line_sq_eq_dirichlet_cross`, `exists_hardy_floor_in_window_of_gN_line_l2_split`, and `riemannHypothesis_of_window_gN_line_l2_split_cross_slope_endpoint_target`. Big picture: the phase-free window L2 input is now unfolded into the exact scalar integrand `2‖D_N(1/2+iτ)‖^2 + 2 Re(χ(1/2+iτ)·conj(D_N(1/2+iτ))^2)`, so the remaining anchor question is precisely whether the banked every-window second moment beats this explicit main-plus-interference budget while the circle/EM inequalities close.
- `RHTower/DpolyBallFloor.lean`: added `exists_hardy_floor_in_window_of_gN_line_l2_split_bounds`. Big picture: the split line-`L²` Hardy anchor can now be produced from three scalar inequalities — a lower bound for the Dirichlet main moment, a lower bound for the FE-interference integral, and the budget `m_J^2 U < mainFloor - crossLoss` — with integrability discharged internally from finite-carrier continuity.
- `RHTower/HardyCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `continuous_gN_line_crossTerm` and `exists_hardy_floor_in_window_of_gN_line_l2_split_pointwise_cross`. Big picture: the FE-interference side of the split line-`L²` anchor can now be controlled by a segment-wise scalar bound `-crossDensity ≤ 2 Re(χ·conj(D_N)^2)`, converting it to the explicit loss `crossDensity * U` in the anchor budget.
- `RHTower/DpolyBallFloor.lean`: added `dirichlet_line_main_moment_lower_bound` and `exists_hardy_floor_in_window_of_secondMoment_pointwise_cross`. Big picture: the split line-`L²` Hardy anchor now consumes the banked Dirichlet second-moment lower bound directly; the remaining analytic input is a segment-wise lower bound for the FE-interference density plus the explicit budget `m_J^2 U < mainSecondMomentFloor - crossDensity * U`.
- `RHTower/HardyCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `gN_line_crossTerm_lower_bound_of_dirichlet_norm_sq_le` and `exists_hardy_floor_in_window_of_secondMoment_cross_sup`. Big picture: the FE-interference budget can now be certified by a window envelope `‖D_N(1/2+iτ)‖^2 ≤ Dsup`; the split Hardy anchor consumes the banked main second moment minus the explicit loss `(2 * Dsup) * U`.
- `RHTower/HardyCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `gN_line_crossTerm_lower_bound_of_dirichlet_norm_le` and `exists_hardy_floor_in_window_of_secondMoment_norm_sup`. Big picture: the FE-interference loss is now fed by the scalar window envelope `‖D_N(1/2+iτ)‖ ≤ Dnorm`, giving the explicit anchor budget `m_J^2 U < mainSecondMomentFloor - (2 * Dnorm^2) * U`; the next analytic node is therefore the direct inequality between the banked second-moment floor and a line-norm envelope, with no separate `Dsup` witness.
- `RHTower/DpolyBallFloor.lean`: added `riemannHypothesis_of_secondMoment_norm_sup_cross_slope_endpoint_target`. Big picture: the full endpoint/cross-slope RH gate can now be fed directly by the banked second-moment floor plus the scalar segment envelope `‖D_N(1/2+iτ)‖ ≤ Dnorm`; the remaining per-window anchor inequality is the explicit finite budget `m_J^2 U < mainSecondMomentFloor - (2 * Dnorm^2) * U`, alongside the existing known-circle `gN`, `completedGN`, and `emCarrier` budgets.
- `RHTower/HardyCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `hardyOrthogonalCarrier`, `gN_line_crossTerm_eq_hardy_components`, `gN_line_crossTerm_lower_bound_of_hardyOrthogonal_le`, `exists_hardy_floor_in_window_of_secondMoment_orthogonal_sup`, and `riemannHypothesis_of_secondMoment_orthogonal_sup_cross_slope_endpoint_target`. Big picture: the FE-interference budget is now controlled by the Hardy-phase quadrature scalar `Im(conj(w) * D_N)`, giving the sharper loss `(2 * Ysup^2) * U`; the next window inequality targets the component invisible to the `gN` Hardy amplitude rather than the full Dirichlet norm.
- `RHTower/HardyCarrier.lean`: added `dirichlet_norm_sq_eq_hardy_components` and `dirichlet_main_eq_hardy_components`. Big picture: the banked Dirichlet main density now has the exact Hardy-phase scalar split `‖D_N‖^2 = H_N^2/4 + Y_N^2` and `2‖D_N‖^2 = H_N^2/2 + 2Y_N^2`; the remaining every-window anchor comparison can be stated directly as in-phase Hardy energy versus quadrature energy, rather than only through the FE cross term.
- `RHTower/DpolyBallFloor.lean`: added `exists_hardy_floor_in_window_of_main_orthogonal_energy` and `exists_hardy_floor_in_window_of_secondMoment_orthogonal_energy`. Big picture: the Hardy anchor can now be produced from an averaged quadrature-energy budget `∫ 4 * Im(conj(w) * D_N)^2 ≤ orthLoss`, with scalar condition `m_J^2 * U < 2 * mainSecondMomentFloor - orthLoss`; this is less brittle than a pointwise quadrature envelope and exposes the next analytic comparison as a segment-energy estimate.
- `RHTower/SecondMoment.lean`, `RHTower/HardyCarrier.lean`, and `RHTower/DpolyBallFloor.lean`: added `secondMoment_upper_bound`, `hardyOrthogonalCarrier_sq_le_dirichlet_norm_sq`, `dirichlet_line_norm_sq_moment_upper_bound`, `orthogonal_energy_le_dirichlet_energy`, and `orthogonal_energy_le_dirichlet_upper_bound`. Big picture: the quadrature-energy input now has a certified crude ceiling from the same Montgomery-Vaughan off-diagonal constant as the main floor; this exposes the next analytic target as a real saving below total Dirichlet energy, not another supplied loss parameter.
- `RHTower/DpolyBallFloor.lean`: added `exists_hardy_floor_in_window_of_secondMoment_orthogonal_saving`. Big picture: the averaged quadrature target can now be stated as a saving below the crude total-energy ceiling; the diagonal cancels against the banked main floor, leaving the explicit finite requirement `m_J^2 * U < saving - 8 * offdiag`, so the next analytic task is to produce that saving on each admissible segment.
- `RHTower/DpolyBallFloor.lean`: added `riemannHypothesis_of_secondMoment_orthogonal_saving_cross_slope_endpoint_target`. Big picture: the full endpoint/cross-slope RH gate now consumes the averaged quadrature saving directly; each window must provide the finite inequality `∫ 4Y_N^2 ≤ 4 * (U * diagonal + offdiag) - saving` plus `m_J^2 * U < saving - 8 * offdiag`, while the known-circle `gN`, `completedGN`, and `emCarrier` budgets remain unchanged.
- `RHTower/ScalarCertificate.lean`: added `minmod_exp_ratio_eq_power`, `canonical_minmod_exp_eq_power`, `canonical_cross_budget_of_power_floor`, and `canonical_em_budget_of_power_floor`. Big picture: the canonical minimum-modulus budget can now be estimated in power-law form `x * (x/A)^θ` instead of exponential-log form, so the remaining anchor-vs-radius inequalities are cleaner scalar estimates while the existing `gN`, `completedGN`, and `emCarrier` gate signatures stay unchanged.
- `RHTower/ScalarCertificate.lean`: added `canonical_anchor_ratio_pos_lt_one_of_engine`, `minmod_radius_exponent_mono`, `canonical_anchor_ratio_rpow_antitone_radius`, and `canonical_em_power_le_cross_power`. Big picture: the engine inequality is now exposed as the dimensionless ratio `(m_J/rz)/(M_J/(rJ-rz)) < 1`, and the radius loss is monotone, so the outer EM floor is formally recognized as the stricter power-budget face than the inner cross-slope floor.
- `RHTower/ScalarCertificate.lean`: added `canonical_cross_em_budgets_of_outer_power_floor`. Big picture: the certificate's cross-slope and EM floors can now be fed by one outer-radius power floor; the EM-radius power factor is formally below the inner cross-slope factor, so future window estimates can target a single stricter scalar floor rather than two separate exponential-log budget shapes.
- `RHTower/DpolyBallFloor.lean`: added `xi_window_pinned_of_hardy_floor_outer_power`. Big picture: the local Hardy-anchor certificate can now consume the single outer-radius power floor from `ScalarCertificate`, so future window estimates only need the Hardy anchor plus one stricter scalar power budget before the existing `gN`, `completedGN`, and `emCarrier` hypotheses apply.
- `RHTower/DpolyBallFloor.lean`: added `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target`. Big picture: the top second-moment/quadrature-saving RH gate now exposes the stricter outer-radius power budget directly; the legacy exponential cross-slope and EM inequalities are derived internally, leaving the analytic core as one saving inequality, one outer-power floor inequality, and the existing known-circle estimates.
- `RHTower/ScalarCertificate.lean`: added `outer_power_budget_pair_of_max_floor` and `canonical_cross_em_budgets_of_outer_power_floor_max`. Big picture: the two canonical cross/EM outer-power budget inequalities can now be certified by one normalized max comparison against the outer minimum-modulus floor.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to expose the single normalized max outer-power budget directly. Big picture: the top gate now asks for one simultaneous anchor-vs-budget scalar inequality, plus the quadrature-saving anchor and known-circle estimates.
- `RHTower/ScalarCertificate.lean`: added `completedGN_bound_of_arch_gN_sphere_bound`. Big picture: a completed-carrier closed-ball sup is now produced from an archimedean closed-ball sup and a boundary `gN` sup, using the maximum-principle transfer already present for the carrier.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to use `A_G * M_J` in the outer budget and derive the `completedGN` bound internally. Big picture: the top gate no longer asks for a primitive completed-carrier regional estimate; it asks for `gN`, `archFactor`, and `emCarrier` estimates on known regions.
- `RHTower/EMCarrier.lean`: added `emCarrier_gN_norm_le_of_components` and `emCarrier_gN_close_on_of_components`. Big picture: finite `emCarrier`/`gN` closeness can now be certified from three explicit finite budgets: Dirichlet-block drift, EM pole size, and the reflected χ-half.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to derive `emCarrier`/`gN` closeness from those three finite budgets. Big picture: the top gate now exposes the finite comparison as visible scalar pieces instead of one opaque regional closeness hypothesis.
- `RHTower/EMCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `emPole_norm_le_line_closedBall` and tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to replace the quantified EM pole budget with the scalar inequality `(M : ℝ)^(1/2+RJ)/(1/2-RJ) ≤ δP`. Big picture: one more `emCarrier`/`gN` comparison face is now a finite radius-and-height budget; the remaining finite comparison pieces are Dirichlet-block drift and the reflected χ-half.
- `RHTower/EMCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `dirichletPoly_sub_norm_le_tail_of_re_ge` / `dirichletPoly_sub_norm_le_tail_line_closedBall` and tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to replace the quantified Dirichlet-drift budget with `N ≤ M` plus the scalar finite-tail inequality `∑_{i∈[N,M)} (i+1)^(-(1/2-RJ)) ≤ δD`. Big picture: the `emCarrier`/`gN` comparison now has Dirichlet drift and EM pole both reduced to explicit finite scalar budgets; the reflected χ-half is the remaining comparison face still quantified over the disk.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the reflected χ-half budget is required only on the boundary circle `sphere(1/2+iτ,RJ)`, with the closed-ball estimate derived internally by `reflected_chi_budget_of_circle`. Big picture: the `emCarrier`/`gN` comparison face is now entirely sourced from finite tail, pole radius-gap, and known-circle reflected-χ data rather than opaque disk comparison assumptions.
- `RHTower/EMCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added reflected Dirichlet finite-sum and chi-envelope product lemmas, and tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to replace the reflected chi product-circle budget with a chi circle envelope plus the scalar finite-sum budget `chiB * sum_{n <= N} n^{-(1/2-RJ)} <= deltaChi`. Big picture: the reflected comparison face is now split into the archimedean chi envelope and an explicit finite Euler sum, leaving the next analytic node as bounding chi on known circles.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the reflected chi envelope is no longer stated as a raw `zetaChi` norm bound; it is now the exact Gamma-ratio envelope `pi^(Re z - 1/2) * ||Gamma((1-z)/2)|| / ||Gamma(z/2)|| <= chiB`, with the old norm bound derived internally. Big picture: the archimedean reflected face is now positioned for a Stirling/digamma circle estimate instead of an opaque chi input.
- `RHTower/RouteBChiDecay.lean`: added `norm_zetaChi_le_left_line`, an explicit left-strip upper bound for `||zetaChi(σ+it)||` from the vertical digamma estimate and FTC for `log ||Gamma||`. Big picture: the reflected chi envelope now has its high-growth left-arc estimate banked; the next Lean node is the circle-geometry bridge from `sphere(1/2+iτ,RJ)` to this vertical-line bound.
- `RHTower/RouteBChiDecay.lean`: added `line_sphere_re_im_bounds` and `norm_zetaChi_le_left_line_sphere`, turning the left half of `sphere(1/2+iτ,RJ)` into a finite scalar chi budget `K` with `exp(RJ*K) <= chiB`. Big picture: the high-growth left arc of the reflected chi envelope is no longer pointwise complex data; it is now a radius/height inequality, leaving the right-arc decay bridge as the next matching piece.
- `RHTower/RouteBChiDecay.lean`: added `norm_zetaChi_le_right_line_sphere` and `norm_zetaChi_le_line_sphere`, turning the right half and then the full boundary `sphere(1/2+iτ,RJ)` into finite scalar χ-envelope data. Big picture: the reflected χ budget consumed by the EM/gN gate can now be supplied from two explicit radius/height inequalities, one growth-side bound and one bottom-height decay bound, plus `1 <= χB`.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to replace the raw Gamma-ratio circle envelope with scalar χ-circle hypotheses: line-height separation, left-arc growth scalar nonnegativity and budget, right-arc bottom-height decay, and `1 <= chiB`. Big picture: the top RH gate now consumes the completed χ envelope from explicit radius/height inequalities rather than a quantified archimedean norm assumption on every boundary point.
- `RHTower/RouteBChiDecay.lean` and `RHTower/DpolyBallFloor.lean`: added `norm_zetaChi_le_left_line_sphere_of_K_bound` and `norm_zetaChi_le_line_sphere_window`, then tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the χ face uses one window-level top/bottom scalar package instead of per-height χ inequalities. Big picture: the archimedean reflected budget is now a finite window datum: top height controls left-arc growth, bottom height controls right-arc decay, and the endpoint consumes those scalars directly.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by removing the slack variables `deltaD`, `deltaP`, and `deltaChi`; the EM/gN comparison now uses the single direct scalar inequality `tail + pole + chiB * reflectedSum <= delta`. Big picture: the endpoint's finite comparison face is now one visible budget rather than three chosen reserves plus a summation reserve, matching the finite scalar gate shape more closely.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by inlining the direct EM/gN comparison budget into the outer-power max budget, removing the separate `delta` witness from the endpoint input. Big picture: the top gate now asks for one simultaneous scalar inequality where the Hardy/Jensen anchor beats both the completed-carrier cross budget and the explicit EM comparison budget.
- `RHTower/ScalarCertificate.lean`: added `canonical_outer_power_floor_mono_anchor` and `canonical_outer_power_budget_of_anchor_le`, proving that the canonical outer-power floor is monotone in the certified anchor height. Big picture: the second-moment anchor can now be compared against the fused endpoint budget through a genuine threshold monotonicity lemma rather than by rechoosing scalar data by hand.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by splitting the outer-power budget threshold `m0` from the selected Hardy/Jensen anchor `m_J`, using monotonicity to lift the fused budget from `m0` to `m_J`. Big picture: the top gate now asks for an explicit threshold-overlap chain: second-moment saving supplies a large enough anchor while the finite scalar budgets need only close at a lower certified threshold.
- `RHTower/DpolyBallFloor.lean`: further tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the Jensen quotient is checked at the lower threshold `m0` and transported to the selected anchor `m_J` by the existing log-monotonicity lemma. Big picture: two lower-bound faces now share the same threshold datum; the selected anchor only still carries the saving and upper-engine constraints.
- `RHTower/ScalarCertificate.lean` and `RHTower/DpolyBallFloor.lean`: added `canonical_threshold_budgets_of_anchor_le` and used it in `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to bundle Jensen and outer-power promotion from `m0` to `m_J`. Big picture: the threshold-overlap step is now a named scalar certificate, so the remaining analytic problem is isolated to producing an anchor inside the interval allowed by the saving and engine upper constraints.
- `RHTower/ScalarCertificate.lean` and `RHTower/DpolyBallFloor.lean`: added `selected_anchor_upper_constraints_of_le_cap` and tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so saving and engine inequalities are certified at an upper cap `m_hi` and transported downward to the selected anchor `m_J`. Big picture: the top gate now exposes a two-sided scalar interval `m0 <= m_J <= m_hi`; lower budget faces close at `m0`, upper faces close at `m_hi`, and the remaining analytic task is to place the second-moment anchor level inside that interval.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by eliminating the separate selected-anchor witness `m_J`; the theorem now requires only `0 < m0` and `m0 <= m_hi`, then selects `m0` internally as the Hardy/Jensen anchor level. Big picture: the top gate's anchor-placement burden is now the scalar interval nonemptiness condition between the lower budget threshold and the upper saving/engine cap.
- `RHTower/DpolyBallFloor.lean` and `RHTower/ScalarCertificate.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to remove the slack witnesses `saving` and `m_hi`; the endpoint now consumes one direct averaged quadrature-energy inequality at the anchor `m_J`, and stale threshold/cap transport lemmas were removed. Big picture: the top gate no longer asks for an invented saved amount or cap interval; the remaining Hardy-anchor face is the exact segment-energy budget against the banked second-moment floor, alongside the finite Jensen, engine, outer-power, EM, and chi scalar budgets.
- `RHTower/DpolyBallFloor.lean`: normalized `exists_hardy_floor_in_window_of_secondMoment_orthogonal_energy` and the top RH endpoint to the additive budget `m_J^2 * U + orthogonalEnergy < 4 * (U * diagonal - offdiag)`. Big picture: the Hardy-anchor face is now a single scalar budget ledger: anchor demand plus quadrature-energy cost must fit under the banked second-moment supply, matching the finite gate form more directly.
- `RHTower/DpolyBallFloor.lean`: tightened the top RH endpoint's archimedean lower face from a critical-line slice through each `rz`-ball to the real segment floor `a0 <= ||archFactor(linePt u)||` on `[T-rz,T+U+rz]`, with line-center geometry deriving the old input internally. Big picture: one more certificate face is now a known-segment scalar condition rather than a disk-filtered complex quantifier.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the top endpoint consumes the `completedGN` upper bound `M_G` directly on the known `RJ` balls. The previous `archFactor` upper face and derived product bound `A_G * M_J` were removed from this endpoint. Big picture: the remaining top certificate is closer to the advertised finite window data: `gN` on known circles, `completedGN` on known balls, `emCarrier` closeness, and scalar budgets tying them together.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the top endpoint consumes direct `emCarrier`/`gN` closeness `delta` on the known `RJ` balls. The internal Dirichlet-tail, pole, and reflected-chi derivation plumbing was removed from this endpoint. Big picture: the top certificate now presents the advertised ledger faces directly: `gN` on known circles, `completedGN` on known balls, `emCarrier` closeness on known balls, the segment archimedean lower face, and the scalar budget tying them to the second-moment anchor.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the top endpoint requires `completedGN` only on the known boundary circles `sphere(1/2+i*tau,RJ)`. The closed-ball bound needed by the lower engine is now derived internally by the maximum principle and strip analyticity. Big picture: another certificate face has moved from disk data to circle data, leaving the endpoint closer to a finite window ledger of circle and segment inequalities.
- `RHTower/EMCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `emCarrier_analyticAt_of_ne_one` and tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the top endpoint requires `emCarrier`/`gN` closeness only on the known boundary circles `sphere(1/2+i*tau,RJ)`. The closed-ball closeness needed by the lower engine is derived internally by the maximum principle, using the strip to avoid the EM pole at `1` and the gamma pole. Big picture: the top certificate now has both `completedGN` and `emCarrier` comparison faces on known circles, with the archimedean lower face on a known segment and the remaining burden concentrated in the scalar budget chain.
- `RHTower/EMCarrier.lean` and `RHTower/DpolyBallFloor.lean`: added `em_remainder_norm_le_line_closedBall_of_center_bound` and tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the EM remainder face is supplied by the scalar center-height inequality `(||1/2+i*tau||+RJ) * M^(-(1/2-RJ)) / (1/2-RJ) <= epsilon1` on the window segment. Big picture: the top certificate has moved its remaining EM disk majorant to a segment scalar, so the analytic load is now concentrated into circle data plus the explicit scalar budget chain around the second-moment anchor.
- `RHTower/DpolyBallFloor.lean`: added endpoint-max critical-line norm geometry and `em_remainder_norm_le_window_closedBall_of_endpoint_bound`, then tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` so the EM remainder face is one window scalar `(max ||linePt T|| ||linePt (T+U)|| + RJ) * M^(-(1/2-RJ)) / (1/2-RJ) <= epsilon1` instead of a per-height segment family. Big picture: the top certificate's EM majorant is now a finite endpoint datum, so the remaining inequality chain is closer to a literal per-window scalar ledger around the second-moment anchor.
- `RHTower/DpolyBallFloor.lean`: added `linePt_add_radius_mem_sphere` and tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by removing the primitive `0 <= epsilon1 + delta` input. The proof now derives `epsilon1 >= 0` from the endpoint EM scalar and `delta >= 0` from a concrete sample point on the known comparison circle. Big picture: the top gate has one fewer free sign assumption; nonnegativity of the error budget is now forced by the visible scalar/circle data already required by the certificate.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by removing the free `Rtau` witness and its two endpoint-distance hypotheses. The theorem now uses the single scalar quadratic target budget `(rho.re - 1/2)^2 + max(|rho.im-T|, |rho.im-(T+U)|)^2 < R'^2`, then reconstructs the old `Rtau` internally for the lower gate. Big picture: target containment is now a direct endpoint-max window scalar, reducing the remaining data to fewer chosen slack parameters.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by removing the free `R'` target-radius witness. The theorem now asks directly for `rz < R` and the scalar clearance `(rho.re - 1/2)^2 + max(|rho.im-T|, |rho.im-(T+U)|)^2 < (R-rz)^2`, then instantiates the lower gate with `R-rz`. Big picture: target containment now has no auxiliary radius slack variable; it is a direct window-clearance inequality against the same radius budget used by the pinning disk.
- `RHTower/DpolyBallFloor.lean`: added `exists_gN_line_anchor_in_window_of_secondMoment_orthogonal_energy` and rewired `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` to feed the selected critical-line center directly into `riemannHypothesis_of_center_floor_cross_slope_windows`. Big picture: the banked second-moment floor now appears in the advertised carrier form `m_J <= ||gN N (1/2+i*tau)||`, so the final endpoint passes a concrete center anchor rather than routing through a Hardy-floor window wrapper.
- `RHTower/DpolyBallFloor.lean`: tightened `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` by removing the `epsilon1` witness. The endpoint now inserts the explicit EM remainder majorant `(max ||linePt T|| ||linePt (T+U)|| + RJ) * M^(-(1/2-RJ)) / (1/2-RJ)` directly into the fused outer-power budget and instantiates the lower gate's error reserve internally. Big picture: the top certificate has one fewer slack variable; the EM remainder face is now a literal window endpoint scalar in the main budget chain.
- `RHTower/DpolyBallFloor.lean`: added `completedGN_norm_le_line_closedBall_of_sphere` and `emCarrier_gN_norm_le_line_closedBall_of_sphere`, then rewired `riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target` through these named circle-to-disk producers. Big picture: the final certificate's `completedGN` and `emCarrier` comparison faces are now explicitly reusable known-circle inputs; the closed-ball data consumed by the scalar pinning engine is produced by maximum principle lemmas rather than inline proof plumbing.
- `RHTower/HardySignChange.lean` (new, registered in the umbrella): added `exists_sign_bracket_of_abs_integral_lt` (a strict gap `|∫F| < ∫|F|` on a segment forces an ordered sign bracket `F(t₁)·F(t₂) ≤ 0`, with no continuity or integrability hypotheses), `exists_sign_bracket_of_moment_gap` (second-moment floor `S ≤ ∫F²` + sup `|F| ≤ M_line` + first-moment cancellation `M_line·|∫F| < S` produce the bracket via `∫F² ≤ M_line·∫|F|`), `continuous_completedGN_line`, `exists_completedGN_sign_bracket_of_moments` (the instantiation at the real-valued completed carrier on the critical line), and the endpoint `riemannHypothesis_of_integral_ledger_endpoint_target`. Big picture: this is Hardy's 1914 mechanism in certificate form — the sign face was the last face of the top RH gate that referenced carrier values at two secret interior heights; it is now produced from a moment triple (short-segment second-moment floor, line sup, first-moment cancellation) on the explicitly named bracket segment `[T+U−rz, T+rz]`. Every face of the new top endpoint is an integral, sup, or scalar inequality over known segments and circles; the genuinely open analytic core is now visibly the short-interval moment pair — exactly the Hardy–Littlewood engine for zeros in short intervals — plus the long-window second-moment anchor already banked.
- `RHTower/HardySignChange.lean`: added `riemannHypothesis_of_decoupled_integral_ledger_endpoint_target`. Big picture: the fixed-bracket endpoint hides a fatal quantitative coupling — its bracket segment `[T+U−rz, T+rz]` is nonempty only when `U ≤ 2rz < 1`, while the banked mean-value supply of a length-`N` carrier is positive only on windows of length comparable to `N`, so no certificate family could discharge it at large heights. The decoupled endpoint quantifies the sign-face moment triple per height (`∀ τ` in the window: second-moment floor and first-moment cancellation on `[τ−rz, τ+rz]`, one sup on the expanded segment) and produces the bracket locally around the anchor-selected height, so the anchor window may now be as long as the mean-value supply demands. The remaining analytic load is exactly Hardy–Littlewood-shaped: a long-window mean-value anchor plus short-interval moment control of the completed carrier, both stated as integrals of explicit finite objects.
- `RHTower/FirstMoment.lean` (new, registered in the umbrella): added `norm_integral_mul_exp_le` / `abs_integral_re_mul_exp_le` (integration by parts against the explicit antiderivative `exp(−iλu)/(−iλ)` bounds any modulated C¹-envelope first moment by `(2M₀+(β−α)M₁)/|λ|`), the cpow normal forms `natCast_cpow_neg_linePt` / `natCast_cpow_neg_one_sub_linePt`, the named object `carrierLineTerm` with `completedGN_line_term_decomp` (the completed carrier on the line is the finite sum of coefficient `n^{−1/2}` times two archimedean-envelope oscillations at frequencies `±log n`), and the endpoint producer `abs_integral_re_completedGN_line_le`. Big picture: the first-moment cancellation face of the sign-bracket certificates is no longer an opaque assumption — it is now bounded by `Cmain + Σ_{2≤n≤N} n^{−1/2}·2(2M₀+(β−α)M₁)/log n`, where every oscillating term gains its frequency `log n` and the whole analytic content is concentrated into `Cmain` (the non-oscillating `n = 1` moment `‖∫ archFactor + ∫ archFactor·χ‖`, Hardy's resonance integral, which decays by the archimedean factor and the rotating χ-phase) plus two envelope-derivative sups on the segment (digamma-type data already targeted by the `DigammaBounds` lane).
- `RHTower/ArchEnvelope.lean` (new, registered in the umbrella): added `archFactor_mul_zetaChi` (on the strip the χ-twisted envelope collapses: `archFactor·χ = archFactor(1−·)`, so both carrier envelopes are one function at reflected arguments — no quotient rule, no separate χ branch), `digamma_continuousOn_re_pos`, `hasDerivAt_Gammaℝ_of_re_pos` (the closed logarithmic form `Γ_ℝ′ = Γ_ℝ·(ψ(s/2) − log π)/2`), the canonical derivative `archFactorDeriv` with `hasDerivAt_archFactor_of_re_pos` and `continuousOn_archFactorDeriv`, the line-path derivatives, and the producer `abs_integral_re_completedGN_line_le_of_sups`. Big picture: every differentiability and derivative-continuity face of the carrier first-moment bound is now discharged by theorem; the certificate inputs for the sign-face cancellation are reduced to five closed-form scalars — sups of `archFactor` and of `archFactorDeriv` (digamma-scale data, matching the existing DigammaBounds/DigammaAsymptotic estimates of `Re ψ` on vertical lines) along the segment, and one non-oscillating resonance moment `‖∫ archFactor(linePt) + ∫ archFactor(1−linePt)‖`.
- `RHTower/FirstMoment.lean`: added `norm_integral_mul_exp_phase_le`, the van der Corput first-derivative engine: for a C¹ amplitude and a C² real phase with `|φ′| ≥ m > 0`, the oscillatory integral obeys `‖∫ g·e^{iφ}‖ ≤ 2Mg/m + (β−α)·(Mg′/m + Mg·Mφ″/m²)`, by integration by parts against `e^{iφ} = (e^{iφ})′/(iφ′)`. Big picture: this is the master oscillation tool for every remaining cancellation face — it subsumes the linear-frequency engine and accepts the nonlinear phases native to the completed carrier: the archimedean rotation `θ(u)` (whose derivative `(Re ψ(1/4+iu/2) − log π)/2 ≈ ½·log(u/2π)` is floored by the banked digamma vertical bounds, giving the resonance moment its `1/log τ` gain) and the Riemann–Siegel shifted frequencies `u·log n ± 2θ(u)` away from their stationary point `n ≈ √(u/2π)`.
- `RHTower/ArchEnvelope.lean`: added `digamma_analyticOnNhd_re_pos`, `continuousOn_deriv_digamma_re_pos` (the trigamma layer `ψ′ = deriv digamma`, analytic hence continuous on `re > 0`), and `archFactorDeriv2` with `hasDerivAt_archFactorDeriv_of_re_pos`: substituting `Γ_ℝ′ = Γ_ℝ·Ψ` into the product rule collapses the second derivative of the envelope onto the single factor `Γ_ℝ`, giving `archFactor″ = Γ_ℝ·(1 + (2s−1)Ψ + PΨ² + Pψ′(s/2)/4)`. Big picture: the envelope is now C² with closed-form derivatives whose only transcendental ingredients are `ψ` and `ψ′` at `s/2` — exactly the data needed to drive the van der Corput engine with the archimedean winding phase, whose frequency is `Re ψ/2 − log√π` and whose curvature is trigamma-scale.
- `RHTower/ArchWinding.lean` (new, registered in the umbrella): added the winding calculus of the archimedean envelope on the critical line — `archWinding = archFactor′/archFactor` with its derivative, the real `windingRate` (phase velocity), its curvature `windingRateDeriv` (continuous through the trigamma layer), the FTC phase primitive `windingPhase`, and the capstone `norm_integral_archFactor_line_le_of_winding_floor`: a floor `m ≤ |windingRate|` on the segment forces `‖∫ archFactor(linePt u) du‖ ≤ 2M₀/m + (β−α)(Mim/m + M₀·Mp/m²)`, where the amplitude face `Mim` bounds `‖archFactor‖·|Im w|` — the modulus variation only, because dividing by the winding character cancels the rotation exactly. Big picture: this is Hardy's resonance-integral cancellation as a theorem — the winding rate equals `(Re ψ(1/4+iu/2) − log π)/2 ≈ ½log(u/2π)`, floored by the banked digamma vertical bounds, so the non-oscillating face `Cmain` of the carrier's first moment now decays like `1/log τ` against the second-moment mass, which is the exact mechanism that makes the sign-bracket face closable at large heights.
- `RHTower/WindingFloor.lean` (new, registered in the umbrella): added `archWinding_eq` (the winding datum in rational-plus-digamma form), `windingRate_eq` (on the line the rational part `(2s−1)/(s(s−1))` is purely imaginary, so the winding rate is exactly `(Re ψ(1/4+iu/2) − log π)/2`), `windingRate_ge` (the banked vertical digamma bound floors it by `(log(u/2π) − 4/u² − π/u)/2`), the monotone segment floor `windingRate_uIcc_floor`, and the capstone `norm_integral_archFactor_line_le_explicit`. Big picture: the winding-rate floor face of the resonance-moment cancellation is now a THEOREM with fully explicit constants — the archimedean envelope's first moment on any segment above height `2πe^{ε}` is bounded by `≈ 4M₀/log(α/2π)` plus curvature terms; Hardy's `1/log τ` decay of the resonance integral is machine-checked end to end, leaving only the amplitude faces (`Im ψ` and trigamma sups on the quarter-line — the same lane's next estimates) between the sign-bracket certificate and unconditional discharge of its `Cmain` face.
- `RHTower/WindingAmplitude.lean` (new, registered in the umbrella): added `im_inv_shift` and `im_digamma_natCast_add_one` (`ψ(N+1)` is real), `im_digamma_vertical_anchor_tendsto` (`Im ψ(σ+it+N) → 0` from the Gauss-limit shift bound), the two-sided vertical bound `im_digamma_vertical_bound` (`0 ≤ Im ψ(σ+it) ≤ 1/t + π/2` for `σ ≥ 0, t > 0`, via the digamma recurrence turning `Im ψ` into a limit of positive partial sums controlled by the banked arctan comparison), and the consumer `archWinding_im_abs_le` (`|Im w(u)| ≤ 3/u + π/4`). Big picture: the modulus-variation amplitude face `Mim` of the resonance-moment cancellation is now an explicit function of the height alone — `Mim = M₀·(3/α + π/4)` works on any segment above height `α` — so of the three van der Corput faces of the `Cmain` bound, two (floor and amplitude) are theorems; only the curvature face `Mp` (a trigamma sup, `|Im ψ′|`-type on the quarter-line) remains to make Hardy's resonance decay fully unconditional.
- `RHTower/TrigammaVertical.lean` (new, registered in the umbrella): added `deriv_digamma_add_nat_tendsto` (far-field decay `ψ′(z+N) → 0`, by applying the Schwarz quotient estimate `Complex.norm_dslope_le_div_of_mapsTo_ball` to the recentred digamma on unit-scale disks where the Gauss-limit shift bound makes it uniformly `O(1/N)`), `deriv_digamma_apply_add_nat` (the differentiated recurrence `ψ′(z+N) = ψ′(z) − Σ_{n<N}(z+n)⁻²`, by `HasDerivAt.unique` on the two sides of the digamma recurrence), and `norm_deriv_digamma_vertical_le` (`‖ψ′(σ+it)‖ ≤ 1/t² + π/(2t)` for `σ, t > 0`). Big picture: the trigamma layer now has the same vertical bound as digamma itself, from the same arctan comparison — this is the curvature-scale datum of the archimedean winding, the last transcendental input of the resonance-moment cancellation; what remains is pure calculus: differentiating the rational-plus-digamma form of the winding datum to bound `|windingRateDeriv u| ≤ 3/u² + π/(4u)`, which makes all three van der Corput faces of Hardy's resonance decay theorems.
- `RHTower/WindingCurvature.lean` (new, registered in the umbrella): added `archWindingDeriv_eq` (differentiating the rational-plus-digamma form identifies the winding derivative as `(ratDeriv + ψ′(s/2)/4)·i` along the line, by `HasDerivAt.unique`), `windingRateDeriv_abs_le` (`|windingRateDeriv u| ≤ 3/u² + π/(4u)` — on the line the rational derivative has real numerator `2u²−½` over `(¼+u²)²`, and the trigamma vertical bound controls the rest; crucially this exploits the exact cancellation `aFD2/arch − w² = w′`, avoiding the lossy `(log u)²` triangle bound), and the crown `norm_integral_archFactor_line_le_all_explicit`: above the explicit winding threshold, `‖∫ archFactor(linePt u) du‖` is bounded by a closed-form function of the envelope sup `M₀` and the segment height alone. Big picture: Hardy's `1/log` decay of the archimedean resonance moment is now UNCONDITIONAL — all three van der Corput faces (floor, amplitude, curvature) are theorems; the `Cmain` face of the sign-bracket certificate needs only the elementary envelope sup `M₀` (Stirling-type modulus data), completing the winding arc begun with the phase-primitive construction.
- `RHTower/ResonanceClosedForm.lean` (new, registered in the umbrella): added `norm_Gamma_le_Gamma_re` (the Euler-integral modulus bound `‖Γ(z)‖ ≤ Γ(Re z)` on the right half plane), `norm_archFactor_line_le` (`‖archFactor(linePt u)‖ ≤ (¼+u²)/2·π^{−1/4}·Γ(¼)` — the explicit envelope sup), `archFactor_conj` and `integral_archFactor_reflected_eq_conj` (the reflected resonance integral is the conjugate of the direct one, via `conjCLE` commuting with the interval integral), and the capstone `resonance_moment_le_closed_form`: above the explicit winding threshold, the full resonance moment `‖∫ arch(linePt) + ∫ arch(1−linePt)‖` is bounded by a closed-form expression in the segment endpoints alone. Big picture: the `Cmain` face of the completed carrier's first moment — the non-oscillating half of Hardy's sign-change mechanism — is now a THEOREM with no free analytic data: combined with the termwise oscillation bound, the first-moment cancellation face of the sign-bracket certificates is discharged down to elementary segment arithmetic, closing the arc from the van der Corput engine through winding floor, amplitude, curvature, and envelope sup.
- `RHTower/EnvelopeDerivBound.lean` (new, registered in the umbrella): added `norm_Gammaℝ_line_le` (`‖Γ_ℝ(linePt u)‖ ≤ π^{−1/4}Γ(¼)` from the Euler-integral modulus bound), `norm_digamma_quarter_le` (`‖ψ((linePt u)/2)‖` bounded by combining both banked vertical digamma bounds through `‖z‖ ≤ |Re z| + |Im z|`), and `norm_archFactorDeriv_line_le` (`‖archFactorDeriv(linePt u)‖ ≤ π^{−1/4}Γ(¼)·(u + (¼+u²)/2·(ψ-bound/2 + log√π))` — a closed-form function of the height). Big picture: the `M₁` face was the last non-theorem input of the completed carrier's first-moment producer; with it discharged, every face of the first-moment cancellation bound — `M₀` (Euler integral), `M₁` (this), `Cmain` (winding arc) — is a closed-form theorem, so the sign face of the decoupled ledger endpoint reduces to exactly two open analytic quantities: the short-interval second moment `S_b` and the line sup `M_line` of the completed carrier — the faces where the genuinely open mathematics lives.
- `RHTower/CarrierLineSup.lean` (new, registered in the umbrella): added `sum_rpow_neg_half_le` (the square-root telescope `Σ_{n≤N} n^{−1/2} ≤ 2√N`), `norm_dirichletPoly_line_le` (`‖h_N‖ ≤ 2√N` on the line), `norm_gN_line_le` (`‖g_N‖ ≤ 4√N`: the reflected part is a conjugate, χ is unimodular), and `abs_re_completedGN_line_le` (`|Re Φ̃_N(linePt u)| ≤ (¼+u²)/2·π^{−1/4}Γ(¼)·4√N`). Big picture: the `M_line` face of the sign-bracket certificate is a closed-form function of height and carrier length — with `M₀`, `M₁`, `Cmain`, and now `M_line` all theorems, the sign face of the decoupled ledger endpoint rests on exactly ONE open analytic face: the short-interval second moment `S_b ≤ ∫_{τ−rz}^{τ+rz} (Re Φ̃_N)²`, the localized mass of the completed carrier, which is now the single named integral inequality carrying the route's remaining depth.
- `RHTower/CarrierLineSup.lean` and `RHTower/HardySignChange.lean`: added the named closed-form `completedGNLineSupBudget`, its positive-segment control theorem, and a decoupled integral-ledger RH endpoint with the free `M_line` witness instantiated to that explicit scalar. Big picture: the sign-bracket face now needs only the local completed-carrier second moment and first-moment cancellation against a known segment-height formula, pushing one more budget input into the finite scalar ledger around the second-moment anchor.
- `RHTower/FirstMoment.lean`, `RHTower/ArchEnvelope.lean`, `RHTower/CarrierLineSup.lean`, and `RHTower/HardySignChange.lean`: added the named `completedGNFirstMomentBudget`, its sup-data producer, nonnegativity of the closed line-sup budget, and `exists_completedGN_sign_bracket_of_firstMomentBudget`. Big picture: the local sign-bracket face can now be certified by the scalar inequality `completedGNLineSupBudget * completedGNFirstMomentBudget < S_b`, replacing the raw first-moment cancellation integral with a finite envelope/resonance budget plus the short completed-carrier second moment.
- `RHTower/ResonanceClosedForm.lean`, `RHTower/EnvelopeDerivBound.lean`, and `RHTower/HardySignChange.lean`: named the closed archimedean envelope and resonance budgets, proved the reflected derivative has the same norm as the direct derivative, and added `exists_completedGN_sign_bracket_of_resonanceBudget_oneDerivSup`. Big picture: the local Hardy sign face now reduces to one derivative-envelope sup, one short completed-carrier second moment, and the scalar inequality using closed resonance/line-sup budgets; the separate reflected-envelope, reflected-derivative, and resonance-moment inputs are no longer independent analytic faces.
- `RHTower/EnvelopeDerivBound.lean` and `RHTower/HardySignChange.lean`: added `archDerivLineBudget`, `archDerivSegmentBudget`, the segment derivative-envelope bound, and `exists_completedGN_sign_bracket_of_closedFirstMomentBudget`. Big picture: the local Hardy sign face now has a fully closed first-moment side; after the winding threshold, a sign bracket follows from only the short completed-carrier second-moment floor beating the explicit scalar product of line-sup and first-moment budgets.

- `RHTower/HardySignChange.lean`: added `abs_integral_re_completedGN_line_le_closedFirstMomentBudget` and `riemannHypothesis_of_decoupled_integral_ledger_closedFirstMoment_endpoint_target`, deriving the decoupled ledger's first-moment cancellation from the closed first-moment scalar budget. Big picture: the full decoupled RH certificate no longer carries a raw completed-carrier first-moment integral or free line-sup witness; its sign face is now the short completed-carrier second-moment floor plus a fully explicit scalar first-moment budget above the winding threshold.
- `RHTower/HardySignChange.lean`: added variable-floor versions of the decoupled Hardy sign-change endpoints: `riemannHypothesis_of_decoupled_integral_ledger_variable_moment_endpoint_target`, `riemannHypothesis_of_decoupled_integral_ledger_variable_explicit_line_sup_endpoint_target`, and `riemannHypothesis_of_decoupled_integral_ledger_variable_closedFirstMoment_endpoint_target`. The certificate no longer needs one uniform short second-moment floor across the whole anchor window; the long-window argument selects one center, and the local sign bracket consumes only the floor at that selected center.
- `RHTower/HardySignChange.lean`: consolidated the decoupled Hardy ledger endpoints so the center-dependent short-moment floor theorem is the proof core, and the older uniform-floor endpoint is a constant-function specialization. Big picture: the local sign face is now organized around the actual data consumed at the selected anchor height, while preserving the previous public endpoint name for downstream certificates.
- `RHTower/HardySignChange.lean`: shortened the uniform explicit-line-sup and closed-first-moment endpoints to specialize the corresponding variable-floor endpoints. Big picture: the Hardy sign-change ledger now has one center-dependent spine, with the uniform interfaces retained only as compatibility corollaries rather than parallel proof paths.
- `RHTower/HardySignChange.lean`: strengthened the decoupled Hardy ledger so the proof core accepts center-dependent line-sup data as well as center-dependent short moment floors, and added local line-sup / local closed-first-moment RH endpoints using `completedGNLineSupBudget N (τ+rz)`. Big picture: the sign face now consumes scalar budgets attached to the selected short segment itself, rather than forcing the closed line-sup through the far endpoint of the whole anchor window.
- `RHTower/CarrierLineSup.lean` and `RHTower/HardySignChange.lean`: added monotonicity of `completedGNLineSupBudget` on nonnegative heights and rerouted the older global-line-sup Hardy endpoints through the local `τ+rz` endpoints. Big picture: certificates stated with the coarser window endpoint `T+U+rz` are now formally recognized as special cases of the selected-short-segment budget, so the proof net has a single local sign-face path plus compatibility interfaces.
- `RHTower/HardySignChange.lean`: normalized the closed first-moment Hardy endpoint interfaces to use the actual selected-segment length `2*rz` instead of `(τ+rz)-(τ-rz)`. Big picture: the closed sign-face budget now exposes the short scale directly, making the certificate shape less dependent on incidental endpoint arithmetic while preserving the same local segment proof.
- `RHTower/HardySignChange.lean`: strengthened the uniform closed-first-moment Hardy endpoint so its scalar budget uses the selected short-segment line sup `completedGNLineSupBudget N (τ+rz)` rather than the coarser full-window endpoint. Big picture: the public uniform certificate now matches the local sign-face geometry instead of preserving a global-budget detour.
- `RHTower/HardySignChange.lean`: added `completedGNFirstMomentBudget_closed_nonneg`, a named nonnegativity invariant for closed completed-carrier first-moment budgets, and reused it where local/global line-sup prefactors are compared. Big picture: the closed sign-face scalar budget now has an explicit Prop interface, so endpoint proofs no longer rederive budget nonnegativity from the absolute first-moment estimate inline.
- `RHTower/CarrierLineSup.lean`: refactored `abs_re_completedGN_line_le_segment_budget` to use the named monotonicity theorem `completedGNLineSupBudget_mono_nonneg` instead of repeating the height-growth algebra. Big picture: the completed-carrier line-sup stack now has one monotonicity proof core, and segment bounds are explicit consumers of that scalar-budget interface.
- `RHTower/FirstMoment.lean` and `RHTower/HardySignChange.lean`: added the general scalar invariant `completedGNFirstMomentBudget_nonneg` and rebuilt the closed Hardy budget nonnegativity theorem on it, dropping the unnecessary `1 ≤ N` hypothesis. Big picture: nonnegativity of first-moment budgets is now owned by the first-moment layer itself, so closed Hardy endpoints consume a weaker, cleaner Prop interface.
- `RHTower/FirstMoment.lean` and `RHTower/ArchEnvelope.lean`: added monotonicity of `completedGNFirstMomentBudget` in length, envelope sup, derivative sup, and resonance term, plus a relaxed named-budget arch-envelope theorem consuming it. Big picture: the first-moment cancellation face now supports coarse scalar budgets as a proven Prop interface, instead of forcing exact local scalar names at every call site.
- `RHTower/ResonanceClosedForm.lean`, `RHTower/EnvelopeDerivBound.lean`, and `RHTower/HardySignChange.lean`: added named nonnegativity and monotonicity Prop interfaces for the closed envelope, resonance, and derivative scalar budgets, then rebuilt closed Hardy first-moment budget nonnegativity from those interfaces. Big picture: the closed sign-face budget now exposes its scalar positivity through the budget layers themselves, instead of reusing analytic estimates inline at the Hardy endpoint.
- `RHTower/HardySignChange.lean`: added relaxed closed first-moment and sign-bracket interfaces that consume any coarser scalar first-moment budget above the closed local envelope, derivative, resonance, and length inputs, and refactored the exact closed sign bracket as the reflexive specialization. Big picture: closed Hardy sign certificates can now be stated with deliberately coarse scalar budgets while retaining the fully proven local analytic face.
- `RHTower/EMCarrier.lean`: added `raw_domination_of_emCarrier_close_floor`, the set-level Prop bridge from EM remainder bounds, finite `emCarrier`/`gN` closeness, and a LOW floor to raw finite-carrier domination, and refactored the finite-side rung endpoint to consume it. Big picture: the EM finite-data layer now exposes the domination premise as a named interface rather than rebuilding the same pointwise inequality inside transport proofs.
- `RHTower/EMCarrier.lean`: added `completed_domination_of_emCarrier_close_floor`, the set-level EM finite-data bridge from EM remainder, finite `emCarrier`/`gN` closeness, and a LOW floor to completed-carrier domination, then refactored the seam L-transport endpoint to consume it. Big picture: EM finite-data certificates now expose both raw and completed domination premises as named interfaces before entering transport theorems.
- `RHTower/WindowProducer.lean` and `RHTower/DpolyBallFloor.lean`: added `windowLinePackage_of_ball_online_cover`, the per-window Prop interface `SecondMomentOrthogonalSavingOuterPowerWindowData`, and `windowLinePackage_of_secondMoment_orthogonal_saving_outer_power_endpoint_target`; refactored the strongest Dpoly/Hardy RH endpoint to route through cofinal `WindowLinePackage`s. Big picture: the outer-power Hardy/Dpoly gate now emits a reusable window-producer node before RH, so downstream ladder/deck/window consumers can use the same certified empty-window intermediate instead of only a terminal RH theorem.
- `RHTower/SeamCongruence.lean`, `RHTower/HardySignChange.lean`, `RHTower/DiscCensus.lean`, and `RHTower/DeckWindow.lean`: added a closed-bracket seam reader for non-strict Hardy sign brackets, a Hardy-moment/EM-floor window-certificate theorem, subwindow DISC-bit-to-certificate bridges, and a deck-triviality equivalence through subwindow congruences. Big picture: Hardy moment data, EM finite-data domination, DISC finite-carrier bits, and deck monodromy now meet at the `WindowCertificate`/subwindow-congruence layer instead of terminating in separate total-window or RH-only endpoints.
- `RHTower/HardySignChange.lean` and `RHTower/DiscCensus.lean`: added `IntegralLedgerOuterPowerWindowData -> WindowLinePackage` and a subwindow finite-deck bridge that derives finite DISC-bit vanishing from completedGN deck-line equality. Big picture: the strongest Dpoly/Hardy window route no longer has to assume an explicit point-pair sign bracket when moment ledger data is available, and DISC/deck transport can now consume per-subwindow deck certificates rather than precomputed finite census zeros.

## formal/GaloisForLFunctions/RHTower/CarrierMassFloor.lean (new)

Point-to-mass conversion: `sq_integral_floor_of_anchor_slope` (an anchor `c ≤ |f τ|` plus a
derivative sup `D` on `[τ−rz, τ+rz]` force the square-integral floor
`(c/2)²·2·min rz (c/(2D))`), instantiated for the completed carrier via
`hasDerivAt_re_completedGN_line` (the carrier's critical-line slope, computed termwise from
the envelope calculus) and `norm_carrierLineSlope_le` (closed-form slope budget
`4√N·(M₁ + M₀·log N)`).  `anchor_re_completedGN_line_of_floors` converts the certificate's
existing arch-floor × carrier-anchor product into the pointwise anchor (reality of `Φ̃_N` on
the line), and `exists_completedGN_sign_bracket_of_anchor_slope` closes the loop: a sign
bracket in `[τ−rz, τ+rz]` from anchor, envelope sups, line sup, and a first moment below the
anchor-generated mass floor.

Big picture: the short-interval second-moment face `S_b` — previously the sole open analytic
face of the sign-bracket route — is no longer an independent input.  It is manufactured from
the anchor face the window certificates already carry, so anchor and mass have collapsed into
one quantity; the sign face now rests on anchor + first-moment cancellation alone, with every
envelope constant a closed-form theorem.

## formal/GaloisForLFunctions/RHTower/CarrierMassFloor.lean (endpoint added)

`riemannHypothesis_of_decoupled_integral_ledger_anchor_mass_endpoint_target`: an RH gate whose
per-zero window certificate carries NO independent short-interval second-moment face.  The
long-window energy budget selects the anchor height, the archimedean floor upgrades
`m_J ≤ ‖g_N‖` to the pointwise anchor `a₀·m_J ≤ |Re Φ̃_N|`, and the point-to-mass converter
manufactures the local mass floor `(a₀m_J/2)²·2·min rz (a₀m_J/(2·4√N(M₁+M₀log N)))` from the
envelope calculus.

Big picture: compared to the earlier decoupled ledger endpoints, the `S_b` supply and
positivity faces are gone.  The sign face of the per-zero certificate is now a single strict
scalar comparison — local first moment below the anchor-generated mass floor — with every
other sign-face input an envelope sup already bounded by a closed-form theorem
(`norm_archFactor_line_le`, `norm_archFactorDeriv_line_le`, `abs_re_completedGN_line_le`).
- `RHTower/HardySignChange.lean` and `RHTower/DiscCensus.lean`: cofinalized the window-level integral-ledger route into a direct RH producer, and named/cofinalized the subwindow finite deck-line provider into ladder/RH consumers. Big picture: the two main remaining producer gaps are now exposed as cofinal data interfaces: analytic integral ledgers for `WindowLinePackage` supply, and per-rung subwindow finite completedGN deck-line data for DISC transport through congruences.
- `RHTower/CarrierMassFloor.lean`: lifted the anchor-mass endpoint to `AnchorMassOuterPowerWindowData -> WindowLinePackage`, added a cofinal anchor-mass RH producer, and refactored the older terminal RH theorem through that window interface. Big picture: the strongest Hardy/Dpoly window route can now target anchor plus closed slope-envelope data instead of an independent short completed-carrier second-moment floor `S_b`, so the remaining analytic producer is a sharper cofinal anchor-mass ledger.
- `RHTower/DiscCensus.lean`: added `SubWindowFiniteDeckLineTwoSignData`, which derives the finite-deck transport congruences from EM/LOW domination and two sign tables before feeding the existing subwindow deck-line provider, plus cofinal ladder/RH consumers. Big picture: the DISC/deck route no longer has to assume the raw total and line congruences `hD/hL` when the local seam supplies peeled factorizations, domination, and xi/completedGN sign tables; those congruences are now formal outputs of the seam transport layer.

## formal/GaloisForLFunctions/RHTower/MollifiedCarrier.lean (new)

Carrier abstraction for the whole critical-line sign-face arc: `mollPoly b N =
Σ_{n≤N} b_n·n^{−s}` with arbitrary real coefficients, χ-symmetrized (`mollG`) and
completed (`completedMollG`).  Re-instantiated for general `b`: Schwarz reality, the
exact even FE on the strip, reality on the line, the termwise line decomposition and
line slope (reusing the sharp termwise objects with coefficient multipliers), slope
budget `mollWeight·2(M₁+M₀·log N)` with `mollWeight = Σ|b_n|n^{−1/2}`, line sup
`2M₀·mollWeight`, anchor bridge, point-to-mass floor, and the anchor-driven sign
bracket.  `completedMollG_one`/`mollWeight_one_le` identify the sharp carrier as the
instance `b ≡ 1`.

Big picture: the sign-face machinery is no longer married to the sharp truncation,
whose short-window anchor faces inherit the refuted Route C-direct premise
(unbounded local variance).  The same gate now serves any designed-coefficient
carrier — in particular a mollified one with bounded local variance, where the
anchor and energy faces can be drawn from mean-value theory whose premises hold.
The sharp arc survives unchanged as the `b ≡ 1` instance.

## formal/GaloisForLFunctions/RHTower/AnchorSupply.lean (new)

Carrier-free anchor instruments plus the general-coefficient anchor supply.
`norm_add_chi_mul_conj_eq`/`_sq_split`: for ANY `w : ℂ`, the χ-symmetrized shape
`w + χ·conj w` on the line collapses to `|2Re(ω̄w)|` with energy split
`4‖w‖² − 4Im(ω̄w)²` (ω = Hardy phase) — pure phase identities, no carrier.
`exists_norm_floor_in_window_of_secondMoment`: any continuous detector whose window
second moment exceeds `m²U` clears the floor `m` in that window — generic MV floor.
Instances: `mollPoly_line_eq_dpoly` identifies the general carrier on the line with
the mean-value theory's `dpoly` at coefficients `b_n·n^{−1/2}`, and
`exists_re_completedMollG_anchor_in_window_of_orthogonal_energy` chains energy face →
carrier floor → archimedean upgrade → pointwise anchor `a₀·m ≤ |Re Φ̃ᵇ|` in every
window, for arbitrary designed coefficients.

Big picture: the instruments (phase collapse, energy split, MV floor) are now stated
route-free — they serve the sharp carrier, the mollified carrier, and any future
detector with the χ-symmetrized shape, so pivoting between routes replaces only the
thin endpoint layer.  For the mollified lane specifically, the anchor face is now
producible wherever the coefficient design makes the diagonal dominate its
off-diagonal — the exact regime (κ² = O(1)) in which the living Route B′ operates.

## formal/GaloisForLFunctions/RHTower/ShortWindowNoGo.lean (new)

Global no-go for the sharp MV-anchored certificate family.
`pinning_geometry_short_window`: the quadratic containment face plus the radii chain
force every anchor window to length `U < 1` — a property of the constraint system, not
of any instance.  `sharp_offDiagonal_ge`: the sharp coefficients' mean-value
off-diagonal is `≥ N−1` (adjacent pairs alone).  `harmonic_Icc_le_one_add_log` caps the
diagonal at `U(1+log N)`.  Capstone `sharp_pinning_certificate_depth_lt_four`: ANY
certificate carrying both the pinning geometry and the sharp energy face has `N ≤ 3`.

Big picture: this is a machine-checked verdict about the certificate system as a whole
— for every zero, every height, every parameter choice, the sharp-carrier mean-value
anchor is incompatible with the pinning geometry beyond depth 3.  The entire decoupled
ledger endpoint family is formally vacuous in its sharp MV instantiation; a live
instantiation must supply anchors from designed coefficients whose off-diagonal is
controlled at short windows (the general-coefficient interface banked in
MollifiedCarrier/AnchorSupply) or from non-mean-value sources (ball floors).  The
informal Route-C-grade scaling objection is now a theorem, not a note.

## formal/GaloisForLFunctions/RHTower/ResidualFaces.lean (new)

The residual enumeration: `riemannHypothesis_of_residual_faces` — an RH gate in which EVERY
analytic estimate of the sign face is supplied internally by closed-form theorems (envelope
sup + reflection, derivative segment budget, resonance moment, line sup, line slope,
anchor-generated mass floor, sign bracket).  No `S_b`, no `M_line`, no `M₀/M₁/Cmain`
witnesses, no MV energy face.  The per-zero certificate retains exactly seven faces beyond
window geometry: (R1) an anchor height where `m_J ≤ ‖g_N‖` on the line; (R2) ONE scalar
inequality between explicit formulas (closed line sup × closed first moment < anchor mass
floor); (R3) Jensen data (sphere sup `M_J`, quotient < 2, engine); (R4) archimedean floor
`a₀`; (R5) completed-carrier sphere sup `M_G`; (R6) the outer cross/EM scalar budget;
(R7) EM closeness `δ` on window spheres.  Helpers: winding-floor monotonicity in height,
positivity of the envelope and slope budgets.

Big picture: this is the formal answer to "what exactly does this constraint still ask of
the world?"  RH now follows from a per-zero certificate whose only non-formula content is
carrier data — one line floor (R1), two sphere sups (R3a/R5), one closeness (R7) — plus
four scalar comparisons among named quantities.  Combined with ShortWindowNoGo (the anchor
cannot come from the sharp MV budget at any admissible window), the open content of the
whole pinning route is now enumerated and machine-checked: whoever supplies (R1)–(R7), from
any source — designed coefficients, ball floors, or a future route — gets RH; and any
global obstruction to them is a formal dead-end verdict.

## formal/GaloisForLFunctions/RHTower/AnchorZeroBudget.lean (new)

The zero budget of the anchored disc — what any (R1) anchor supplier owes the Jensen tier.
`gN_line_zero_of_sign_bracket`: every sign bracket of `Re Φ̃_N` on the line yields a zero of
the finite carrier `g_N` itself (IVT + nonvanishing archimedean envelope).
`anchor_jensen_faces_false_of_second_zero`: a second carrier zero in the anchored inner disc
refutes the face triple (center floor `m_J`, sphere sup `M_J`, Jensen quotient `< 2`).
Capstone `anchor_jensen_faces_false_of_two_sign_brackets`: two sign brackets in disjoint
line subintervals of the anchored disc refute the faces — the anchored disc admits AT MOST
ONE sign change of the completed carrier.

Big picture: this quantifies the residual face (R1) as part of the whole system rather than
in isolation.  An anchor floor at height `T` is certifiable only at disc radii below the
local sign-change spacing of the completed carrier (heuristically `~2π/log T`, the scale the
banked winding floor measures); at larger radii the faces (R1)+(R3) are jointly false no
matter how the anchor is produced.  So "supply (R1)" now has an exact meaning: a carrier
floor at the carrier's own oscillation scale, with the window geometry `rz` shrinking like
the zero spacing — the residual gate's parameters are height-coupled, and any proposed
anchor mechanism can be pre-screened against this coupling before any window engineering.

## formal/GaloisForLFunctions/RHTower/WindingRigidity.lean (new)

The quantitative half of the anchor-disc coupling law, part 1 of 2.
`archFactor_line_polar`: exact polar factorization of the archimedean envelope along the
line — basepoint value × exp(windingModulus) × exp(i·windingPhase), where `windingModulus`
(new primitive, FTC'd) integrates the winding datum's imaginary part and `windingPhase`
integrates the banked winding rate.  `gN_line_winding_rigidity` (UNCONDITIONAL): the finite
carrier times the envelope's polar data equals the real value of the completed carrier —
reality of `Φ̃` on the line in exact closed form.  `carrier_ray_of_sign_constant`: on any
segment where `Re Φ̃ > 0`, the winding-rotated carrier `arch(γ)·e^{iΘ(τ)}·g_N(linePt τ)` is a
positive real — the carrier's phase anti-rotates the winding phase EXACTLY.

Big picture: the phase velocity of the finite carrier on every sign-constant segment is
locked to `−windingRate`, whose explicit floor `(log(u/2π) − 4/u² − π/u)/2` is a banked
theorem — so between consecutive sign changes the carrier's phase must fall at least at rate
`≈ ½·log(T/2π)`.  A sign change is the only mechanism that can interrupt the lock.  The
remaining half of the spacing law is an argument-variation bound for the carrier factor
(Borel–Carathéodory grade, using the Jensen-face zero budget): together they will force
`sign-change spacing ≲ 2π/windingRate-floor` inside any face-satisfying disc — the explicit
`rz(T) ≲ 1/log T` scale at which any (R1) anchor supplier must certify its floor.

## formal/GaloisForLFunctions/RHTower/ArgumentVariation.lean (new)

The Borel–Carathéodory argument-variation brick — the second half of the anchor-disc
coupling law.  `borel_caratheodory`: for analytic `g` on `ball c R` with `Re g ≤ A`,
`‖g z − g c‖ ≤ 2‖z−c‖/(R−‖z−c‖)·(A − Re g(c))` (Schwarz–Pick applied to the Möbius
transport of the half-plane into the unit disc).  `exists_analyticOnNhd_exp_eq_ball`:
analytic logarithm of a zero-free analytic function on a disc (continuous branch on the
simply connected disc + the tree's analytic upgrade).  Integrality gluing:
`im_eq_int_mul_two_pi_of_exp_pos` (exp = positive real ⟹ Im ∈ 2πℤ) and
`continuousOn_int_mul_two_pi_const` (continuous 2πℤ-valued on an interval is constant).
Capstone `abs_windingPhase_le_of_sign_constant_zero_free`: on a sign-constant line segment
inside a zero-free disc with modulus data `(M, ‖g_N(center)‖)`,
`|Θ(b) − Θ(a)| ≤ (BC(a) + BC(b))·log(M/‖g_N(center)‖)` — the winding-phase advance is
capped by the carrier's Borel–Carathéodory budget.

Big picture: the two halves of the quantitative coupling law now exist as theorems.  The
phase lock (WindingRigidity) forces the winding phase to advance at rate ≥ the banked floor
`≈ ½log(T/2π)` on every sign-constant stretch; this module caps that same advance by the
carrier's modulus-ratio budget, a height-free constant once the Jensen-type faces fix
`M/m`.  Chaining them: sign-constant length × ½log(T/2π) ≤ BC budget — the explicit
`rz(T) ≲ 1/log T` law.  The one wiring step left is the substitution of `windingRate_ge`
into `windingPhase a b ≥ (b−a)·floor` (integral monotonicity), which turns the capstone
into the closed-form segment-length bound consumed directly by the residual gate's
geometry faces.

## formal/GaloisForLFunctions/RHTower/ArgumentVariation.lean (completed) + WindingFloor.lean (lemma moved in)

The coupling law closed in explicit form.  `windingPhase_ge_of_floor`: the winding phase
advances at least `(b−a)·floor(a)` (integral monotonicity over the banked pointwise floor;
`winding_floor_expr_mono` relocated from ResidualFaces to WindingFloor, its proper layer).
Capstone `sign_constant_segment_length_le`: on a zero-free carrier disc with modulus data
`(M, ‖g_N(center)‖)`, every sign-constant line segment satisfies

  b − a ≤ (BC(a) + BC(b)) · log(M/‖g_N(center)‖) / windingFloor(a),

with every quantity a closed formula.  At height `T` the floor is `≈ ½log(T/2π)` and the
BC prefactors and modulus ratio are fixed by the certificate's radii and Jensen-type faces:
sign-constant stretches — hence the admissible anchor radii of the residual gate — shrink
like `1/log T`.

Big picture: the anchor-disc coupling law announced qualitatively by AnchorZeroBudget is
now a quantitative theorem chain: phase lock (WindingRigidity) + argument-variation cap
(Borel–Carathéodory) + winding floor = the explicit `rz(T) ≲ 1/log T` scale carried by the
gate itself.  Any (R1) anchor supplier now has its working scale as a formula, and the
residual gate's geometry faces can be pre-screened against it at any proposed height.

## formal/GaloisForLFunctions/RHTower/ArgumentVariation.lean (one-zero law added)

The segment-length law extended to the discs the residual gate actually permits — one
carrier zero.  `exists_unit_re_pos_linear_factor`: a line segment avoiding `ρ'` admits a
unit rotation `u ∈ {±1, ±i}` placing `u·(linePt τ − ρ')` in the open right half-plane, so
`Complex.log` is a continuous branch and the linear factor's argument variation is `< π`.
`abs_windingPhase_le_of_sign_constant_one_zero`: on a sign-constant segment of a disc where
`g_N = (z−ρ')·dslope` with nowhere-zero difference quotient (exactly the package the banked
Jensen structure lemma `gN_one_zero_window_of_jensen` produces), the winding-phase advance
is `≤ π + BC-budget(dslope)`.  `sign_constant_segment_length_le_one_zero`: hence
`b − a ≤ (π + BC·log(Md/‖dslope(center)‖))/windingFloor(a)`.

Big picture: the `1/log T` radius law now covers the exact zero-budget the gate's Jensen
face allows (≤ 1 carrier zero per disc), not just the zero-free case.  The threading chain
is now: Jensen faces ⟹ one-zero factorization (banked) ⟹ segment law (this) ⟹ radius
scale.  What remains before the scaled endpoint is honest (i.e., its scale face provably
redundant rather than an added assumption): the "≤ 1 sign change ⟹ a sign-constant
subinterval of length ≥ half the window" pigeonhole, and dslope modulus data from the
banked boundary-sup lemmas — then the gate's own faces force `rz·windingFloor(T) ≤ π + BC`
as a theorem, and the scaled endpoint rejects mis-scaled certificates at typecheck without
loss of generality.

## RadiusScaleForcing.lean — the gate's faces force the 1/log T radius scale (threading capstone; lane closes here)
- Sign-generalized the argument-variation chain in place: `im_eq_int_mul_pi_of_exp_real` + `continuousOn_int_mul_pi_const` (πℤ-integrality/constancy, ArgumentVariation §3) and `carrier_ray_of_sign_ne_zero` (WindingRigidity) let both winding-phase capstones and both segment-length laws run on `Re Φ̃ ≠ 0` instead of `0 < Re Φ̃` — negative-sign segments now come free, no duplicated proofs.
- `exists_offzero_subinterval`: an interval with at most one zero of f contains, for every margin ε, an off-zero closed subinterval of length ≥ half − ε (pure pigeonhole; the unique zero leaves one flank with half the length).
- `anchor_window_margin_scale`: at one anchor height, the faces {anchor m_J, sphere sup M_J at RJ, Jensen quotient < 2, winding threshold} force (rz − ε)·windingFloor(T−rz) ≤ π + (4rz/(rJ−rz))·(log(M_J/(RJ−rJ)+1) − log m_J). All modulus data discharged from the faces themselves: dslope sup = M_J/(RJ−rJ) by the maximum principle from the sphere sup (`dslope_norm_le_of_boundary_sup`); dslope center value ≥ m_J/rJ from the anchor through the linear factorization; carrier ball sup by the maximum principle. Case split zero-free/one-zero consumes `gN_one_zero_window_of_jensen`; the ≤1-zero input is `anchor_jensen_faces_false_of_two_sign_brackets`.
- `residual_faces_force_radius_scale`: margin elimination — the residual gate's face subset {geometry, winding threshold, (R1) anchor, (R3) Jensen tier} forces rz·windingFloor(T−rz) ≤ π + (4rz/(rJ−rz))·(log(M_J/(RJ−rJ)+1) − log m_J), unconditionally. A certificate whose anchor radius is out of scale with 1/log T refutes its own face list: the height coupling is a THEOREM about the gate, not an extra face — no scaled endpoint needed, none added.
- Verified: build green, axioms [propext, Classical.choice, Quot.sound] for all new + regeneralized theorems (incl. re-check of `riemannHypothesis_of_residual_faces`), lint passed.
- `RHTower/BandEdgePairing.lean` (new, in umbrella): added `FixedPointFreePairing`, `BandEdgePairing`, `fixedPointFreePairing_two_dvd_card`, `fixedPointFreePairing_card_zmod_two_eq_zero`, and `bandEdgeUnitFlux_zmod_two_eq_zero`. Big picture: W4's band-edge contribution is now a formal finite-parity consumer: once regular lateral crossing events carry a fixed-point-free involutive pairing, their unit flux is zero in `ZMod 2`. The analytic/research burden is cleanly isolated to constructing the event pairing; the parity algebra is discharged.

## UPlaneLadder.lean — simply connected u-plane ladder and far-anchor surface
- Added `RHTower/UPlaneLadder.lean` and registered it in the `RHTower` umbrella.
- Generalized the all-level dyadic-root obstruction from convex domains to open preconnected domains:
  `nonvanishing_of_exists_roots_all_two_powers_preconnected`,
  `coherentTower_of_exists_roots_all_two_powers_preconnected`, and
  `coherentTower_iff_exists_roots_all_two_powers_preconnected`.
- Specialized the simply connected root/tower machinery to `xiDescent` on arbitrary regions contained in
  `slitPlane`: `xiDescent_root_of_nonvanishing_on`,
  `xiDescent_twoPower_root_of_nonvanishing_on`,
  `xiDescent_coherentTower_iff_nonvanishing_on`, and the roots-to-coherent-tower equivalence.
- Added the reusable far-field u-plane anchor facts `xiDescent_far_anchor_mem_slitPlane` and
  `xiDescent_far_anchor_ne_zero`, plus
  `xiDescent_coherentTower_iff_nonvanishing_on_far_anchor` and
  `xiDescent_coherentTower_of_RH_on_far_anchor`.  This turns OC3(c) into a global slit-plane-region
  interface: any open simply connected preconnected `U ⊆ slitPlane` containing `(9:ℂ)/4` carries the
  coherent dyadic `xiDescent` tower exactly when `xiDescent` is zero-free on `U`.
- Verified: `lake env lean GaloisForLFunctions/RHTower/UPlaneLadder.lean`,
  `lake env lean GaloisForLFunctions/RHTower.lean`, `lake build GaloisForLFunctions.RHTower`, and
  `/tmp` `#print axioms` for the new capstone declarations, all with axioms
  `[propext, Classical.choice, Quot.sound]`.

## UPlaneLadder.lean — roots/zero-free equivalence capstones
- Added direct equivalences so W5 consumers do not have to compose the lower-level tower API by hand:
  `xiDescent_roots_all_two_powers_iff_nonvanishing_on`,
  `xiDescent_coherentTower_iff_roots_all_two_powers_on_far_anchor`, and
  `xiDescent_roots_all_two_powers_iff_nonvanishing_on_far_anchor`.
- Added the RH-to-root-region consumer `xiDescent_roots_all_two_powers_of_RH_on_far_anchor`, parallel to
  `xiDescent_coherentTower_of_RH_on_far_anchor`.
- Verified: `lake env lean GaloisForLFunctions/RHTower/UPlaneLadder.lean`,
  `lake env lean GaloisForLFunctions/RHTower.lean`, `lake build GaloisForLFunctions.RHTower`, and `/tmp`
  `#print axioms`; the new capstones use only `[propext, Classical.choice, Quot.sound]`.

## RHTower/BandEdgePairing.lean — W4 contrapositive diagnostics
- Extended the finite event-pairing algebra with `bandEdgeUnitFlux_eq_card`,
  `not_fixedPointFreePairing_of_card_zmod_two_ne_zero`, and
  `not_bandEdgePairing_of_unitFlux_ne_zero`.
- Big picture: W4 now has both the forward consumer (a fixed-point-free pairing kills unit flux in
  `ZMod 2`) and the failure diagnostic (nonzero unit flux rules out the pairing interface). This keeps
  the analytic burden exactly where it belongs: constructing or statically certifying the regular
  lateral event parity.

## RHTower/WindowSymmetryNoGo.lean — FE/reality height-line no-go
- Added the finite `FESymmetry` action (`id`, FE, conjugation, and `lineReflect`) and proved
  `FESymmetry.preserves_height_line_iff`: on any nonzero height line, the only FE/reality symmetries
  preserving that line are `id` and `lineReflect`.
- Big picture: doc 106's W4 exhaustion claim now has a Lean anchor. The visible geometric symmetry budget
  inside a positive-height window is exhausted by the reflection already consumed by `(ID)`; any remaining
  band-edge parity must come from arithmetic/static window data.

## LedgerReduction.lean — W3: anchored even-flux ledgers force the rungs (constraint front)
- `LedgerChain` (inductive): piecewise-generic deformation on the slit annulus charts — dominated steps (`‖next−cur‖ < ‖cur‖` on charts) and transversal jumps in/out (enclosed configuration gains/loses one zero of multiplicity m inside the hole); index = net signed flux ∈ ℤ.
- `deckClass_step_annulus`: the conservation step ported to annulus charts (any basepoints; ratioRoot transport).
- `ledgerChain_transport`: roots transport along any chain and the deck class multiplies by exactly exp(2πi·flux/n) — identity (L) in transport form, jumps handled by monomial×correction root multiplication/division (`deckClass_mul_mono_corr` / `deckClass_div_mono_corr`, no factored-form knowledge of the member needed, unlike `deckClass_jump`).
- `AnchoredLedger` (Prop interface): chain from a nonvanishing member (charge computably zero via its global root) to f with n ∣ flux.
- `anchoredLedger_deckClass_eq_one`: under an anchored even-flux ledger ANY roots of f have trivial class (root-independence transfer).
- `xi_deckClass_annulus`: ξ's annulus-chart class = exp(2πi·m/n) below the peel radius (singleton instance of `deckClass_multi_zero`).
- **Capstone `rhLadder_of_anchoredLedgers`**: if every off-line ξ-zero admits anchored even-flux ledgers at arbitrarily small radii at level 2^k, then `RHLadder k`. Conservation, additivity, jump, anchor all discharged; the open burden is exactly the flux-parity clause — the formal (P-flux) interface the seam-parity (W1) and band-edge-pairing (W4) packages must supply.
- Verified: build green, axioms [propext, Classical.choice, Quot.sound] × 5, lint passed.
- `RHTower/SeamCrossingRigidity.lean` (new, in umbrella; W2 of 105-constraint-front-plan, OC2 quantitative): the forced-oscillation layer for the seam, consuming ArgumentVariation + WindingRigidity + RadiusScaleForcing read-only. Reality bridges `gN_line_eq_zero_of_completedGN_re_eq_zero` / `completedGN_re_eq_zero_of_gN_line_eq_zero` / `completedGN_line_eq_zero_of_re_eq_zero` identify, on the critical line, a real-part zero of `completedGN` with a genuine carrier zero (archFactor never vanishes on the line). `seam_edge_forced_online_zero_one_zero` / `_crossing_` / `_completedGN_zero_` are the **contrapositive of the one-zero segment-length law**: a seam segment longer than `(π + BC-budget)/windingFloor` cannot be crossing-free, so it carries an on-line carrier zero (the on-seam zero the ledger charges). `zerofree_seam_edge_length_le` is the dual rigidity — a zero-free carrier disc forces its seam segment short (its crossing-free hypothesis is automatic, `online_re_ne_zero_of_zero_free`). Big picture: the segment-length cap becomes an existence-of-crossing statement — OC2's seam charge is not a magnitude estimate but a forced discrete event on any long enough edge.
- `RHTower/SeamCrossingRigidity.lean`: the oscillation scale and crossing count. `seam_no_long_sign_constant_stretch_one_zero` upgrades the per-segment cap to a **uniform** one — no crossing-free sub-stretch of a window exceeds `Λ = (π + (4ρmax/(R−ρmax))·(log Md − log‖dslope center‖))/windingFloor(a)` — via BC-prefactor monotonicity in the endpoint distance (`prefactor_mono`) and winding-floor monotonicity in height. Packaged as the interface `SeamNoQuietStretch` (produced per one-zero disc by `seamNoQuietStretch_of_disc_one_zero`). Two combinatorial counters turn crossings into a tally of strictly ordered on-line carrier zeros: `exists_strictMono_zeros_of_no_long_gap` (uniform-gap form: a segment longer than `n·Λ` carries ≥ n ordered zeros — cut into n slots each longer than Λ with small gaps) and `exists_strictMono_zeros_of_slot_zeros` / `seam_crossing_count_of_slots` (the non-degenerate multi-box form: n pairwise strictly separated boxes each forcing a crossing give n distinct ordered zeros — distinct boxes, distinct single carrier zeros). Since `Λ ≍ 1/windingFloor ≍ 1/log T`, a fixed-length seam segment tiled by forced boxes carries `≳ (B−A)·log T` crossings: the seam oscillates at the `1/log T` scale. All axiom-clean `[propext, Classical.choice, Quot.sound]`; `lake build MainTheorems` green (9176 jobs); lint + index pass.

## SeamParity.lean — W1: the mod-2 seam ledger is boundary data
- `seamSign f t₁ t₂` — the endpoint sign product (f(linePt t₁)).re·(f(linePt t₂)).re of a line segment.
- `seamSign_pos_of_ne_zero`: a carrier real and nonvanishing along a segment has positive seam sign (IVT engine `endpoint_sign_product_pos`).
- `seamSign_one_zero_iff_even` — **the parity law**: for a real-on-line carrier factoring through one on-line zero of multiplicity m interior to the segment (nonvanishing analytic cofactor on a disc ⊇ segment), 0 < seamSign ↔ Even m. Mechanism: linePt τ − linePt τ₀ = i(τ−τ₀) is purely imaginary, so the rotated cofactor i^m·h is real-valued (off-point by reality of f, at the point by one-sided limit through nhdsWithin) and of constant sign; the real factor (τ−τ₀)^m leaves sign (−1)^m across the zero.
- `seam_jump_sign_readoff` — **the wiring**: at level 2 the seam-jump multiplier is exp(2πi·m/2) = (−1)^m, so for any bank roots the left seam ratio equals ±(right seam ratio) with the sign read off from `seamSign` — the mod-2 seam contribution to a box ledger (doc 15 OC2) is computed from two point evaluations, no zero counting, no argument principle. Composes with `LedgerChain`'s jump constructors: an on-line crossing's flux parity is certified by boundary data.
- Verified: build green, axioms [propext, Classical.choice, Quot.sound] × 3, lint passed.

## LedgerReduction.lean (extension) — the event-typed ledger: doc 106 §9 handoff executed
- `LedgerChainE`: the ledger chain with its transversal events reified — the list index records the signed jump multiplicities in order (+m entering, −m leaving); `ledgerChainE_toChain` recovers the flux chain with flux = list sum.
- `LedgerFluxPaired L`: the paired-flux interface — L splits (up to permutation) into even events and odd events whose positions carry `BandEdgePairing (Fin odds.length)` (the W4 finite pairing structure, consumed via `fixedPointFreePairing_two_dvd_card`). `ledgerFluxPaired_two_dvd_sum`: paired flux is even (odd-event sum ≡ odd-event count mod 2).
- `AnchoredEventLedger` + `anchoredLedger_two_of_eventLedger` + capstone **`rhLadder_one_of_anchoredEventLedgers`**: RHLadder 1 from event-certified ledgers at every off-line zero. The k = 1 parity burden is now split along doc 106's event classes INSIDE the formal statement: even events = the seam class (certified by SeamParity's `seamSign_one_zero_iff_even`, forced to exist by SeamCrossingRigidity's oscillation scale), paired odd events = the band-edge class (W4's open arithmetic pairing, geometric route closed by WindowSymmetryNoGo).
- Verified: build green, axioms [propext, Classical.choice, Quot.sound] × 4, lint passed.

## IncidenceCarrier.lean — the Euler incidence carrier (doc 106 prediction 3, construction; doc 107)
- Builds on the banked generic `incidence`/`pencil` (MirrorPencil): the anchored ledger pencil's zero dynamics = level sets of ONE meromorphic function ι = −Λ₂/Λ₁; real deformation paths live on the real locus of ι.
- `incidence_mirror`: the FE pair acts on incidence values as the Möbius involution r ↦ (ε'/ε)/r — the parameter-space mirror identity.
- `incidence_im_eq_zero_on_line`: for real-FE carriers the critical line is CONTAINED in the real locus of ι — the seam is the degeneration locus of the transversal event structure (prediction 3's first half, exact).
- `incidence_eq_zero_iff`: an anchored pencil's incidence omits ∞ and vanishes only on the target's zeros.
- `real_pencil_ne_zero_of_im_incidence_ne` (quiet edge: Im ι ≠ 0 silences every real-ratio member at once), `bandSign` + `bandSign_pos_of_im_ne_zero` + `exists_real_member_zero_of_bandSign_neg` (the band-edge analogue of seamSign: two endpoint evaluations of Im ι certify quiet or force a transversal event — consumes the now-public `endpoint_sign_product_pos`).
- Doc 107 carries the SEARCH layer: order-pairing evades the §6 geometric no-go; the (0,∞)-fiber refinement gap = mirror image under the Möbius action [closed-sweep telescope conjecture]; ports = critical points of ι|seam [next Lean target]; Euler frontier = odd-winding question for the positive-coefficient Euler TAIL Im part on lateral edges; wild layer (phyllotaxis three-gap interleaving of fibers; sourdough self-restoring ratio ⟹ orientation alternation) with pre-registered predictions against banked data.
- Verified: build green, axioms [propext, Classical.choice, Quot.sound] × 6, lint passed. (SeamParity's `endpoint_sign_product_pos` made public for reuse.)

## IncidenceRamification.lean — Target 1: ι|seam real-analytic + ports = critical points (full ramification classification)
- `seamIncidence Λ₁ Λ₂ τ = (incidence Λ₁ Λ₂ (linePt τ)).re`; `seamIncidence_analyticAt`: real-analytic where Λ₁≠0 (ι holomorphic ∘ ℝ-analytic linePt ∘ reCLM; restrictScalars + CLM analyticity).
- `seam_deriv_eq_zero_iff_incidence_deriv_zero`: critical point of the real seam restriction ⟺ ι'(linePt τ₀)=0. Mechanism = the seam rotation: the line tangent is i, so the complex seam derivative is i·ι'; reality of ι on the line (banked `incidence_im_eq_zero_on_line`) forces it real, vanishing iff ι' does. (imCLM/reCLM comp_hasDerivAt + real-valued⟹derivative-real.)
- `member_order_ge_two_iff_incidence_deriv_zero`: the on-line member (ratio = incidence value) has a zero of order ≥ 2 (a multiple on-line zero, a PORT) ⟺ ι'=0. Via `deriv(member) = -Λ₁·ι'` at the fiber (member = Λ₁·(r−ι)) + `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` (n=2).
- **`seam_critical_iff_port`**: critical point of ι|seam ⟺ port. The transversal event structure degenerates exactly where ι ramifies (doc 107 §3, the ramification half).
- **`member_order_eq_two_iff_incidence_deriv_zero`** + **`seam_simple_port_iff`**: SIMPLE port (order exactly 2) ⟺ ι'=0 ∧ member Hessian ≠ 0 ⟺ simple seam critical point. The generic port = two event branches merging transversally (n=3 iteratedDeriv characterization + ℕ∞ order=2 split via `Order.le_of_lt_succ`).
- Verified: axioms [propext, Classical.choice, Quot.sound] × 6, lint passed, MainTheorems green.

## LedgerTelescope.lean — Target 2: the closed-sweep telescope
- `exp_two_pi_mul_int_div_eq_one_iff` (ℤ version), `int_eq_zero_of_forall_pos_nat_dvd`.
- `ledgerChain_trans` / `ledgerChainE_trans`: chains concatenate with additive flux / appended event lists.
- **`ledgerChain_closed_flux_dvd`**: a closed chain (f→f) has flux divisible by every level n at which f admits chart roots — transport multiplies the deck class by exp(2πi·flux/n), root-independence pins it to 1.
- `ledgerChain_closed_flux_eq_zero` (conditional, all-n roots) + **`ledgerChain_closed_flux_eq_zero_of_enclosed`** (UNCONDITIONAL for factored members via banked `exists_annular_roots_of_enclosed` + `isSimplyConnected_chartRA/LA`): a deformation loop crosses zero net multiplicity.
- **`ledgerChain_window_back_two_dvd`** + **`ledgerChainE_window_back_two_dvd`**: a projective sweep splits into window (f→g) + back-sweep (g→f); the closed loop's even flux forces window flux ≡ back flux mod 2 — the positive-fiber and complement event classes are ONE (doc 107 §3 mirror reduction), collapsing the band-edge pairing to a single class.
- Verified: axioms [propext, Classical.choice, Quot.sound] × 8, lint passed.

## EulerTailWinding.lean — Target 3: the Euler-tail winding lemma fed to the winding-floor instruments
- **`exists_im_zero_of_phase_advance`** (general topological core): a carrier r·exp(iθ) whose phase advances by ≥ π has Im = 0 somewhere (phase passes through kπ, a sine zero; ⌈θa/π⌉ + IVT + `Real.sin_int_mul_pi`).
- `incidence_real_member_zero_of_im_zero`: Im ι = 0 with Λ₁≠0 ⟹ the real-ratio member vanishes (a band event).
- **`exists_bandEvent_of_incidence_phase_advance`**: winding of the incidence carrier by ≥ π forces a transversal band event — winding, not an endpoint sign bracket.
- **`incidence_phase_of_factor_phases`** (the Euler-tail decomposition): the incidence phase = target phase − anchor phase (θ_ξ − θ_P̂); the anchor subtracts the head of the Euler constraint, leaving the tail.
- **`exists_bandEvent_of_euler_tail`** + **`exists_bandEvent_of_target_winding_floor`**: end-to-end — a target-phase floor net of a bounded anchor phase, exceeding π, forces a band event. `windingPhase_ge_pi_of_long` feeds the banked `windingPhase_ge_of_floor` archimedean floor in the exact form consumed; `euler_tail_advance_of_floor_ceiling` is the floor−ceiling arithmetic. The frozen-lane winding-floor instruments apply verbatim to the DIFFERENT (incidence) carrier.
- Verified: axioms [propext, Classical.choice, Quot.sound] × 9, lint passed, MainTheorems green (9184 jobs).

## LateralWindingFloor.lean — the off-line archimedean winding floor (doc 107 addendum's open core closed)
- `stripPt σ τ` — the vertical-edge parameterization at abscissa σ; `stripPt_one_half` welds it to `linePt`, and `stripWinding/stripWindingRate/stripWindingPhase _one_half` weld the whole off-line instrument family to the banked line instruments at σ = 1/2.
- `stripWinding_eq` — the winding datum `archFactor′/archFactor` at σ+iτ in rational-plus-digamma form (the σ-generalization of `archWinding_eq`).
- **The rational budget, both regimes**: off the line `(2s−1)/(s(s−1)) = 1/s + 1/(s−1)` is no longer purely imaginary; `strip_rational_re_ge` bounds its real part below by `(σ−1)/τ²` in the strip (σ ≤ 1), `strip_rational_re_le` above by `σ/τ²`, and `strip_rational_re_nonneg` shows it costs NOTHING for σ ≥ 1 — the abscissa dichotomy.
- **`stripWindingRate_ge`** — the off-line floor: `Re(archFactor′/archFactor)(σ+iτ) ≥ stripFloor σ τ = (log(τ/2π) − 4/τ² − π/τ)/2 − (1−σ)/τ²`. The digamma vertical bound (`re_digamma_ge`) holds at EVERY abscissa x ≥ 0 — only the rational term pays for leaving the line. `stripWindingRate_ge_of_one_le`: for σ ≥ 1 the full line floor with zero concession. `stripWindingRate_le`: the explicit ceiling (two-sided control of arg ξ_arch′/ξ_arch off the line).
- `stripFloor_mono_height` / `stripFloor_mono_sigma` / **`stripFloor_pos`** (positive for ALL σ ≥ 0 from height 12 on, via log(6/π) ≥ 1 − π/6 and π < 3.15) / `stripFloor_le_line_floor`.
- **`stripWindingPhase_ge_of_floor`** — the phase of the archimedean envelope advances at least `(b−a)·stripFloor σ a` along any lateral edge.
- **The polar transport engine** (generic, a mathlib gap): `path_transport_exp_logDeriv` — a path with `G′ = G·ω` transports as `G(τ) = G(a)·exp(∫ω)` (the `G·exp(−∫ω)`-has-zero-derivative argument, componentwise primitives via `integral_hasDerivAt_right`); `polar_presentation_of_logDeriv` — every such path is a real modulus (driven by Re ω) times a unimodular phase (driven by Im ω) from the endpoint's polar data `norm_mul_exp_arg_mul_I`. No nonvanishing hypothesis needed for the presentation itself.
- **`archFactor_lateral_polar`** — the envelope along a lateral edge in exact polar form: phase advance = the lateral winding phase. This is the hypothesis shape `EulerTailWinding` consumes.
- **`exists_bandEvent_of_lateral_edge`** + **`_completedGN`** + **`exists_bandEvent_of_long_lateral_edge`** — the end-to-end firing: on a vertical edge at 0 < σ ≤ 1, height a ≥ 12, of length ≥ `(π + C₁ + C_D)/stripFloor σ a`, with anchor phase budget C₁ and Dirichlet phase budget C_D, a real-ratio member of the anchored pencil is FORCED to vanish (a transversal band-edge event). Every archimedean quantity is explicit and unconditional; the residual hypotheses are finite Dirichlet phase data on the edge.
- Verified: module compiles standalone; `lake build GaloisForLFunctions.RHTower` green; axioms `[propext, Classical.choice, Quot.sound]` × 18 endpoints; umbrella import added.
- (completion) `polar_data_of_logDeriv` — the full anchor-hypothesis package from two inputs: a path with `G′ = G·ω` and ONE nonvanishing point carries nonvanishing real modulus + polar factorization + continuous phase + advance identity `θ(τ)−θ(a) = ∫ Im ω` (transport propagates nonvanishing along the whole edge). `phase_advance_bound_of_im_bound` — a pointwise band `|Im ω| ≤ B` converts to the two-sided budget `(b−a)·B`. Together they reduce the lateral event theorem's anchor burden to: log-derivative on the edge + nonvanishing at one point + a rate band. Axiom-clean ×3; MainTheorems 9189 jobs; lint + index pass.
- `RHTower/SignatureParity.lean` (new, in umbrella): the reduction of the integer zero-index (the signature) to the mod-n deck class (the parity), and the exact measure of what it discards. `deckRed n k = exp(2πi·k/n)` is a homomorphism `(ℤ,+)→(ℂ,×)` with kernel exactly `nℤ` (`deckRed_eq_one_iff`), fibers the cosets `k+nℤ` (`deckRed_eq_iff`), factoring through `ZMod n` (`deckRed_eq_iff_zmod`). `box_charge_eq_deckRed` rewrites the banked `deckClass_multi_zero` box charge as `deckRed n (Σ mᵢ)` — the deck class is literally the reduction of the integer total order of the enclosed zeros. Big picture: the parity front's datum IS the mod-2 image of the full off-line-zero index; the deck class sees `index mod n` and nothing else.
- `RHTower/SignatureParity.lean`: the discard, made exact. `parity_blind_to_pairs` (adding any even total order leaves the deck class fixed — interior pair events are free, doc-15-§3 as a theorem); `deckRed_emod` (the deck class is exactly the reduction of the residue `k % n`); `parity_discards_full_line` (each deck class value has an injective `ℤ`-family of preimages — the discard is a free `ℤ`, the pair/cycle count); `parity_one_bit_retained` (at n=2, `k = 2·(k/2)+(k%2)`: one retained bit `k%2`, discarded pair count `k/2`). Big picture: the reduction retains a finite `ZMod n` (one bit at n=2) and discards a full `ℤ` — this is precisely how much the parity front throws away.
- `RHTower/SignatureParity.lean`: reflection ⟹ discarded. Built `even_sum_of_fpf_involution` (mathlib gap: a fixed-point-free involution matching multiplicities forces even total order, by pairwise removal induction); `reflection_paired_deckRed_two_eq_one` (a reflection-paired configuration has even index, so its deck class at n=2 is trivial — the parity is blind to reflection-paired off-line zeros); `reflection_fixed_deckRed_two_eq_one` (the even order forced at the reflection's fixed point, `analyticOrderAt_even_of_reflection`, is also in the kernel). Big picture: the entire reflection-symmetric part of the index — exactly the off-line mass the Weil signature counts (quadruples/pairs) plus the ramified fixed point — is discarded by the parity; the parity's nonzero signal comes only from genuinely unpaired, unramified order. All axiom-clean `[propext, Classical.choice, Quot.sound]`; `lake build MainTheorems` green (9194 jobs); lint + index pass.

## AnchorHead.lean — the finite Euler head anchor and its phase budget C₁
- `eulerHeadAnchor P s = ∏_{p∈P} (1 − p^{−s})` — a Dirichlet-computable entire function; `eulerHeadAnchor_ne_zero`: nonvanishing on the open right half plane (each factor's modulus `|p^{−s}| = p^{−σ} < 1` for σ>0, p≥2, reverse triangle).
- `logDeriv_eulerHeadAnchor`: the log-derivative is the finite prime sum `∑_{p∈P}(log p)p^{−s}/(1−p^{−s})` (via `logDeriv_prod` on the entire factors).
- **`norm_logDeriv_eulerHeadAnchor_le` / `abs_re_logDeriv_eulerHeadAnchor_le`**: the modulus (hence the real part = the phase-advance rate) is bounded, UNIFORMLY IN THE HEIGHT, by `eulerHeadBound P σ = ∑_{p∈P}(log p)p^{−σ}/(1−p^{−σ})`. This is the anchor budget C₁ — a height-independent constant. `eulerHeadBound_nonneg`.

## IncidenceEdgeCount.lean — a growing count of forced events from a pointwise incidence-rate floor
- **`exists_strictMono_events_of_rate_floor`** (the monotone-phase multi-crossing engine): a polar carrier `r·exp(iθ)` whose phase obeys a uniform positive lower rate `ρ₀` (advances by ≥ ρ₀·(y−x) across any subinterval) crosses every multiple of π; on an edge advancing by n·π there are n STRICTLY ORDERED points where Im = 0. Construction = the multiples `(⌈θa/π⌉+i)π ∈ [θa,θb]`, IVT preimages, strict monotonicity of θ giving ordered distinct preimages, `Real.sin_int_mul_pi` killing Im.
- `rate_floor_of_phase_advance`: a pointwise rate floor `ρ₀ ≤ g` on the phase primitive `θ τ − θ a = ∫ₐ^τ g` lifts to the difference floor (interval additivity + `integral_mono_on`).
- **`logDeriv_incidence`**: `logDeriv(incidence Λ₁ Λ₂) = logDeriv Λ₂ − logDeriv Λ₁` (quotient rule + `logDeriv_const_mul` for the −1).
- **`exists_edge_events_of_incidence_rate_floor`**: for Λ₁,Λ₂ analytic nonvanishing on an open U covering a vertical edge, with `Re(logDeriv Λ₂ − logDeriv Λ₁) ≥ ρ₀ > 0` on the edge, there are n strictly ordered points where a real-ratio pencil member vanishes — n forced transversal band-edge events, SUPPLIED by the rate floor. Chains the polar engine (`polar_data_of_logDeriv`) → rate floor → the multi-crossing engine → `incidence_real_member_zero_of_im_zero`.

## EdgeEventSynthesis.lean — the three-part rate floor and the subcriticality
- `logDeriv_archFactor_stripPt` / `re_logDeriv_archFactor_stripPt`: on the edge the archimedean log-derivative IS the strip winding datum, real part = `stripWindingRate`.
- `archFactor_analyticOnNhd_re_pos`, `gN_analyticOnNhd_re_lt_one`, `completedGN_analyticOnNhd_strip`, `archFactor_ne_zero_strip`: analyticity/nonvanishing scaffolding on the open strip.
- **`incidence_rate_floor_completedGN`** (the three-part floor): for the pencil `(eulerHeadAnchor P, completedGN N)`, `Re(logDeriv Λ₂ − logDeriv Λ₁) ≥ stripFloor σ a − eulerHeadBound P σ − B_D` — via `logDeriv(archFactor·gN) = logDeriv archFactor + logDeriv gN`, the archimedean floor `stripWindingRate ≥ stripFloor` (grows like ½log a), the gN budget B_D, and the anchor prime-sum budget C₁. Requires gN nonvanishing on the edge with `|Re(logDeriv gN)| ≤ B_D`.
- **`exists_edge_events_completedGN`**: the forced-event count for the completed pencil — n events for n·π ≤ (b−a)·ρ₀ once `ρ₀ ≤ stripFloor σ a − eulerHeadBound P σ − B_D`.
- **`exists_height_net_rate_ge`** (subcriticality made explicit): because `stripFloor σ a → ∞` in the height while the anchor prime sum and the Dirichlet budget are fixed, for ANY target ρ₀ there is an explicit height A above which the net rate `stripFloor σ a − eulerHeadBound P σ − B_D ≥ ρ₀`. Proof pins the pure log term `log(a/2π) ≥ 2C+4` via `Real.tendsto_log_atTop` and bounds the corrections at height ≥ 12. This is "C₁ + C_D grows slower than (b−a)·log a", formal.

## EdgeEventLedger.lean — the events supplied to LedgerFluxPaired
- **`ledgerFluxPaired_replicate_one`**: `Nonempty (BandEdgePairing (Fin n)) → LedgerFluxPaired (List.replicate n 1)` — the n forced simple crossings are the odd class (n copies of multiplicity 1), flux-paired exactly when the n events carry a fixed-point-free pairing.
- **`exists_edge_events_of_high_edge`**: forced events on a high edge (net rate normalised to 1); event density 1/π per unit edge length.
- **`exists_edge_events_supply_fluxPaired`** (capstone): on a high edge with a subcritical Dirichlet budget, the winding forces n strictly ordered band-edge events AND, given the pairing on the n events, their event list carries paired flux. The analytic content — existence of the events — is discharged unconditionally; the pairing is the only remaining band-edge arithmetic input. The paired-flux interface handed its odd event class with events SUPPLIED, not hypothesized.
- `exists_forcing_height`: the explicit height above which every edge forces events.
- All four modules axiom-clean [propext, Classical.choice, Quot.sound]; umbrella import added; MainTheorems 9198 jobs green; lint + index pass.

## (completion) C_D discharged from carrier data — no abstract budget hypothesis
- `IncidenceEdgeCount.abs_re_logDeriv_le_of_bounds`: a modulus floor `m ≤ ‖f z‖` and a derivative sup `‖deriv f z‖ ≤ M₁` give `|Re(logDeriv f z)| ≤ M₁/m` (‖·‖-dominates Re, `logDeriv = deriv/f`, `div_le_div₀`). Turns sup/floor carrier data directly into the phase-rate budget.
- `EdgeEventLedger.exists_edge_events_supply_fluxPaired_of_carrier_bounds`: the capstone with `B_D` REPLACED by `M₁/m` supplied by a `gN` modulus floor `m>0` and derivative sup `M₁` on the edge. Every budget on the route (C₁ = eulerHeadBound, C_D = M₁/m) is now computed from carrier data; the pairing is the sole remaining input. Axiom-clean; MainTheorems 9198 jobs; lint + index pass.
- `RHTower/FoldonFrustration.lean` (new, in umbrella): the formalizable core of the foldon-frustration route. Built the mathlib-gap tool `card_group_dvd_weighted_sum` — a free finite-group action divides the invariant weighted sum (`|G| ∣ Σ mᵢ`), via orbit decomposition (each orbit has `|G|` points with `m` constant). Ladder-depth arithmetic: `deckRed_eq_one_of_two_pow_dvd` (`2^k ∣ index ⟹ deckRed(2^k)=1`, invisible at rung k), `deckRed_two_pow_next_visible` (`deckRed(2^{k+1})(2^k)=−1`, a pure `2^k`-orbit first visible at rung k+1), `deckRed_eq_one_below_depth`. Big picture: the frustration (= the integer off-line zero index, `foldonFrustration`) is discarded by the parity ladder up to its 2-adic symmetry depth.
- `RHTower/FoldonFrustration.lean`: the crown, `frustration_invisible_below_reflection_depth` — a configuration invariant under a FREE reflection group of order `2^k` (matching multiplicities) has frustration divisible by `2^k`, hence trivial deck class at every rung `j ≤ k`: the deeper the reflection symmetry of the off-line buckling, the higher the ladder must climb to detect it. Base case `frustration_invisible_rung_one` (reflection pair, from `even_sum_of_fpf_involution`); `frustration_orbit_visibility` pairs the below-depth blindness with the rung-`k+1` visibility. Verdict: the folding route's frustration functional IS the off-line index (reduces to the signature/deck work); the genuinely new formalizable content is this symmetry-depth blindness; the recursion contractivity / locality fork is RH-adjacent open analytic mathematics (needs the AFE), the named boundary. All axiom-clean `[propext, Classical.choice, Quot.sound]`; `lake build MainTheorems` green (9200 jobs); lint + index pass.

## BandEdgePairingConstruction.lean — the pairing IS the evenness
- `consecutivePairing m : BandEdgePairing (Fin (2m))` — the consecutive-crossing involution (swap within each adjacent pair, via `Fin (2m) ≃ Fin 2 × Fin m` and `Equiv.swap 0 1` on the first factor; `Involutive.toPerm`). Fixed-point-free, squares to one.
- **`nonempty_bandEdgePairing_iff_even`**: `Nonempty (BandEdgePairing (Fin n)) ↔ 2 ∣ n`. The forward direction is `fixedPointFreePairing_two_dvd_card`; the reverse is `consecutivePairing`. The paired-flux interface's odd class is closed EXACTLY when the crossing count is even — the entire remaining route content is a single parity fact.

## EdgeEventLedger.lean (extension) — the pairing discharged for an even count
- **`exists_edge_events_fluxPaired_even`**: for an even count `2m`, the forced band-edge events exist AND their event list carries paired flux, with the consecutive-crossing pairing CONSTRUCTED (no `BandEdgePairing` hypothesis). The abstract pairing hypothesis is removed; only the parity of the count remains.

## EdgeEventParity.lean — the parity criterion: the pairing's boundary condition
- **`sin_pos_iff_even_floor`**: `sin x ≠ 0 → (0 < sin x ↔ Even ⌊x/π⌋)` — the sign of `sin` on `(mπ,(m+1)π)` is `(−1)^m` (via `sin_add_int_mul_pi` + `sin_pos_of_pos_of_lt_pi`).
- **`exists_crossing_enum_parity`**: for a positive-modulus, strictly-monotone-phase, continuous carrier with non-crossing endpoints, the points where `Im = 0` are a strictly ordered family `e : Fin n → [a,b]` that EXHAUSTS all crossings, and `Even n ↔ (0 < Im F a ↔ 0 < Im F b)`. The crossings biject to the multiples of π in `[θa,θb]`; the count `⌊θb/π⌋ − ⌊θa/π⌋` is even iff the endpoints agree in orientation. This is doc 106 §5's "consecutive crossings pair by IVT when boundary data agrees" made exact.
- **`crossings_fluxPaired_of_endpoints_agree`**: agreeing endpoints ⟹ even count ⟹ pairing ⟹ `LedgerFluxPaired (replicate n 1)`, with the pairing constructed.
- **`exists_incidence_edge_events_fluxPaired`** (the route terminus): on a lateral edge of the incidence pencil (analytic nonvanishing, rate floor ρ₀>0), IF the two endpoint orientations of the incidence carrier agree, the forced band-edge events come in an even number and their event list carries paired flux. The entire paired-flux burden is discharged into a SINGLE boundary datum — the agreement of the endpoint orientations. Uses the refactored `incidence_edge_polar_data` (shared polar-data setup) + `strictMonoOn_of_phase_advance`.
- Companion refactor: `IncidenceEdgeCount.incidence_edge_polar_data` extracts the incidence polar-data setup (0<R, polar form, θ continuous, difference rate floor) shared by the count and parity theorems; `polar_data_of_logDeriv` strengthened to `0 < R τ`.
- All axiom-clean [propext, Classical.choice, Quot.sound]; MainTheorems 9201 jobs; lint + index pass.

## IncidenceMirrorOrientation.lean — positive-real FE mirror reverses orientation

- `im_real_div_eq_neg_normSq`: the reciprocal mirror algebra, `Im((lam : ℂ)/z) = -lam * Im z / normSq z`.
- `im_real_div_pos_iff_neg`, `im_real_div_neg_iff_pos`, and `im_real_div_mul_im_neg`: for `lam > 0`, the reciprocal map sends lower to upper, upper to lower, and nonreal values to opposite imaginary orientation.
- `incidence_mirror_im_pos_iff_neg_of_real_pos`, `incidence_mirror_im_neg_iff_pos_of_real_pos`, and `incidence_mirror_im_product_neg_of_real_pos`: composing the algebra with `incidence_mirror`, a positive-real FE mirror constant gives opposite orientation between `s` and `1-s`. This records the boundary obstruction precisely: FE mirror orientation is an opposite-edge rule, not the same-edge endpoint agreement required by `EdgeEventParity`.
- Verification: `lake env lean GaloisForLFunctions/RHTower/IncidenceMirrorOrientation.lean`; `lake env lean GaloisForLFunctions/RHTower.lean`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.

## ReflectedSaddleLattice.lean — saddle lattice to parity interface

- `reflectedSaddle T k = T/(2π(k+1))`, `reflectedPhase T k x = -2π(k+1)x + T log x`, with named first and second derivative expressions.
- `reflectedPhase_hasDerivAt`, `reflectedPhaseDeriv_hasDerivAt`: the reflected phase differentiates to `-2π(k+1)+T/x`, then to `-T/x²` away from zero.
- `reflectedPhaseSecond_independent`: the curvature is independent of the Fourier mode. This is the formal version of the R7 observation that the second-derivative estimate is uniform in `n`.
- `reflected_saddle_pos`, `reflectedPhaseDeriv_saddle_eq_zero`, `reflectedPhaseDeriv_eq_zero_iff`: for `T>0` and `x>0`, the unique stationary point of the negative reflected mode is exactly `T/(2π(k+1))`.
- `reflectedSaddleModes`, `reflectedSaddleFluxList`, `reflectedSaddleFluxList_sum`: finite carrier and unit event list for saddle modes in a bounded interval.
- `reflectedSaddleFluxPaired_of_even`, `reflectedSaddleFluxList_two_dvd_sum_of_even`: even saddle-mode count feeds the existing consecutive-pairing/event-ledger interface and yields even total unit flux.
- Verification: `lake env lean GaloisForLFunctions/RHTower/ReflectedSaddleLattice.lean`; `lake env lean GaloisForLFunctions/RHTower.lean`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.
- Boundary left open: the theorem does not assert the physical reflected saddle carrier has even cardinality. It isolates that exact parity/charge-bridge obligation.

## ReflectedGridParity.lean — integer-grid saddle collisions have square-only parity

- `reflectedGridCollisions C = C.divisorsAntidiagonal`: the finite carrier of saddle/grid collisions at normalized height `T=2πC`.
- `reflectedGridSwap`: the factor-swap reflection `(n,m) ↦ (m,n)`, with `reflectedGridSwap_mem` and `reflectedGridSwap_involutive`.
- `reflectedSaddle_two_pi_nat_eq_nat_iff`: `reflectedSaddle (2πC) k = m ↔ (k+1)m=C`, tying the analytic stationary point exactly to the integer divisor equation.
- `reflectedGridCollision_iff_saddle_grid`: membership in the collision carrier is equivalent to the saddle hitting the integer grid, plus the nonzero condition from `Nat.divisorsAntidiagonal`.
- `reflectedGridCollisions_even_of_no_pos_square`, `reflectedGridCollisions_nonfixed_even`, `reflectedGridCollisions_fixed_eq_singleton`, `reflectedGridCollisions_odd_of_pos_square`, `reflectedGridCollisions_odd_iff_pos_square`: all nonfixed collisions pair; the ordered collision count is odd exactly at a positive-square fixed point.
- `reflectedGridCollisionFluxList`, `reflectedGridCollisionFluxPaired_of_no_pos_square`, `reflectedGridCollisionFlux_two_dvd_sum_of_no_pos_square`: no positive square fixed point means the unit collision list supplies `LedgerFluxPaired` and has even total flux.
- Verification: `lake env lean GaloisForLFunctions/RHTower/ReflectedGridParity.lean`; `lake env lean GaloisForLFunctions/RHTower.lean`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.
- Boundary left open: the physical AFE/reflection charge carrier still has to be reduced to this grid-collision carrier, or its off-grid/noncollision events must be shown to cancel in pairs.

## ReflectedGridCharge.lean — weighted reflected charge is even under swap symmetry and even fixed weight

- `reflectedGridWeightedCharge C q = ∑_{x∈reflectedGridCollisions C} q x`: the weighted charge of the reflected saddle/grid collision carrier.
- `reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed`: if `q(reflectedGridSwap x)=q x` on the carrier and diagonal fixed collisions have even weight, then the total weighted charge is even.
- `reflectedGridWeightedCharge_deckRed_two_eq_one_of_swap_invariant_even_fixed`: the same theorem in deck language, `deckRed 2 (charge)=1`.
- `reflectedGridWeightedCharge_even_of_swap_invariant_no_fixed` and deck form: with no positive square fixed point, swap-invariance alone forces even weighted charge.
- `reflectedGridWeightedCharge_even_of_swap_invariant_square_fixed_even` and deck form: when `C=r²`, it suffices that the singleton fixed weight `q(r,r)` is even.
- Verification: `lake env lean GaloisForLFunctions/RHTower/ReflectedGridCharge.lean`; `lake env lean GaloisForLFunctions/RHTower.lean`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.
- Boundary left open: define the physical AFE/reflection charge weight on this carrier and prove its swap-invariance plus even fixed weight; any off-grid/noncollision event class must be separately paired.

## Fail-fast audit modules (F1/F3)

Three new modules, all axiom-clean `[propext, Classical.choice, Quot.sound]`, umbrella-imported:

* `RHTower/EdgeScaleNoGo.lean` — `short_window_engine_no_events`: for `ρ₀(b−a) < π` a
  carrier pair satisfies EVERY forcing-engine hypothesis (rate floor attained, endpoint
  orientations agreeing) while NO real-ratio pencil member vanishes on the segment; with
  the positive direction the forcing threshold is bracketed at the phase-π quantum
  `π/ρ₀` exactly. Helper `pencil_real_member_ne_zero_of_im_ne_zero`.
* `RHTower/IsolatingAnnulusRung.lean` — the `∀ε` clause of the ladder rung eliminated:
  `xi_peel_isolating_ball` (global peel cofactor nonvanishing on any isolating ball),
  `xi_deckClass_annulus_isolating` (deck class counts central multiplicity on any
  isolating annulus), `rhLadder_of_isolating_anchoredLedgers` and
  `rhLadder_one_of_isolating_anchoredEventLedgers` (the rung from ONE isolating annulus
  per off-line zero), `xi_exists_isolating_radius` (isolating radii exist).
* `RHTower/MirrorEdgeSymmetry.lean` — line reflection `s ↦ 1−s̄` on the incidence pencil:
  `incidence_lineReflection`, `im_incidence_mirror_edge` (Im odd across the line),
  `bandEvent_mirror_iff`, `mirror_orientation_reversal`, `mirror_pool_fluxPaired`
  (mirror-pooled event families are doubled with a FREE flux pairing — mirror-symmetric
  parity certificates assert nothing), `completedGN_lineReflection` +
  `completedGN_im_mirror_edge` (the concrete carrier is equivariant; its trivial pencil
  is mirror-blind), `cosh_add_mul_I_im`, and `hagree_not_determined_by_symmetry`
  (two carriers in the same FE+reality class realise agreement AND disagreement of the
  endpoint orientations on the same edge — the boundary datum is strictly finer than the
  symmetry class).

Verdicts and the D–H stress table: doc 108.

## ReflectedGridAnalyticCharge.lean — analytic local order supplies the fixed-square parity

- `reflectedGridAnalyticCharge C F center`: weighted reflected-grid charge with weight `(analyticOrderAt (F x) (center x)).toNat`.
- `reflectedGridAnalyticCharge_even_of_swap_order_even_fixed`: if analytic local orders are invariant under factor swap and diagonal fixed germs are analytic, reflection-symmetric, and finite-order, then total analytic charge is even.
- `reflectedGridAnalyticCharge_deckRed_two_eq_one_of_swap_order_even_fixed`: deck form, `deckRed 2 (analytic charge)=1`.
- `reflectedGridAnalyticCharge_even_of_swap_order_square_reflection`: in the square case `C=r²`, the singleton fixed weight is even by `analyticOrderAt_even_of_reflection`; only swap-invariance of off-diagonal local orders remains.
- `reflectedGridAnalyticCharge_deckRed_two_eq_one_of_swap_order_square_reflection`: square-specialized deck form.
- Verification: `lake env lean GaloisForLFunctions/RHTower/ReflectedGridAnalyticCharge.lean`; `lake env lean GaloisForLFunctions/RHTower.lean`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.
- Boundary left open: instantiate `F` with the actual AFE/reflection charge germs, prove local-order swap-invariance, and show any off-grid event class is paired.

## ReflectionParity.lean + ReflectedGridCompletedCharge.lean — completed carrier supplies reflected-grid analytic charge parity

- `analyticOrderAt_even_of_reflection_eventually`: local reflection parity for analytic germs. Eventual symmetry `f(2c-s)=f(s)` near `c`, analytic-at-`c`, and finite order imply the local order is even. This localizes the earlier global `analyticOrderAt_even_of_reflection` theorem.
- `reflectedGridCompletedCharge C N center`: the reflected-grid analytic charge instantiated with the concrete completed finite carrier `completedGN N`.
- `completedGN_eventually_reflection_half`: `completedGN N` is locally reflection-symmetric at the FE fixed point `1/2`.
- `reflectedGridCompletedCharge_even_of_center_swap`: if factor swap sends centers to `1-center`, centers lie in the open strip, diagonal centers are `1/2`, and local orders are finite, then the completed-carrier reflected charge is even.
- `reflectedGridCompletedCharge_deckRed_two_eq_one_of_center_swap`: deck form, `deckRed 2 (completed charge)=1`.
- Verification: `lake env lean GaloisForLFunctions/RHTower/ReflectionParity.lean`; `lake env lean GaloisForLFunctions/RHTower/ReflectedGridCompletedCharge.lean`; `lake env lean GaloisForLFunctions/RHTower.lean`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.
- Boundary left open at this stage: construct the actual AFE saddle/grid center map, prove finite-order at those centers, and account for off-grid/noncollision events. The canonical ratio-center case and its finite-order side condition are discharged in the next entry.

## ReflectedGridCenter.lean — canonical ratio center geometry

- `reflectedGridRatioCenterR x = x.1/(x.1+x.2)` and `reflectedGridRatioCenter x`: the canonical center attached to a reflected grid collision, placed on the real axis of the complex plane.
- `reflectedGridCollision_fst_pos` and `reflectedGridCollision_snd_pos`: both divisor-antidiagonal factors of a collision are positive.
- `reflectedGridRatioCenterR_swap` and `reflectedGridRatioCenter_swap`: factor-swap sends the ratio center to `1-center`.
- `reflectedGridRatioCenter_strip`: every ratio center lies in the open critical strip.
- `reflectedGridRatioCenterR_diag` and `reflectedGridRatioCenter_diag`: diagonal fixed collisions land at `1/2`.
- `dirichletPoly_ofReal_eq`, `dirichletPoly_ofReal_re_pos`, `zetaChi_ofReal_eq`, `zetaChi_ofReal_re_pos`, `gN_ofReal_re_pos`, and `completedGN_orderAt_ofReal_ne_top`: on real strip points, `completedGN N` has finite local order for `N ≥ 1` because it is nonzero there.
- `reflectedGridCompletedCharge_finite_of_ratio_center`: the finite-order side condition is automatic at ratio centers for `N ≥ 1`.
- `reflectedGridCompletedCharge_even_of_ratio_center_of_one_le`: for the canonical ratio center, `N ≥ 1` implies even completed reflected-grid charge.
- `reflectedGridCompletedCharge_deckRed_two_eq_one_of_ratio_center_of_one_le`: deck form, `deckRed 2 (completed charge)=1`.
- Verification: `lake env lean GaloisForLFunctions/RHTower/ReflectedGridCenter.lean`; `lake env lean GaloisForLFunctions/RHTower.lean`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.
- Boundary left open: reduce the physical AFE/reflection charge carrier to this completed collision carrier and account for off-grid/noncollision event classes.

## AnchorTilt.lean (the F3 forward object built)

`RHTower/AnchorTilt.lean` — axiom-clean, umbrella-imported. The anchor's phase tilt
`anchorTilt P s = ∑_{p∈P} arg(1−p^{−s})` (well-defined: factors in the right half plane,
`arg_eq_arctan_of_re_pos`), height-uniform budget `abs_anchorTilt_le`, Schwarz oddness
`anchorTilt_conj`, exact polar identity `eulerHeadAnchor_polar` (A = ‖A‖e^{i·tilt}),
mirror defect `anchorMirrorDefect` with product identity `eulerHeadAnchor_mul_mirror`
and quantization-under-equivariance `anchorMirrorDefect_int_of_lineReflection`; THE
angle law `incidence_anchored_mirror` / `im_incidence_anchored_mirror`
(ι(1−s̄) = (‖As‖/‖Ams‖)·e^{−i·defect}·conj ι(s) for the anchored pencil on the strip);
annulus bound `abs_anchorMirrorDefect_le_of_mem_ball` (|defect| ≤ 2·tiltBudget σ₀ on any
ball in the strip); critical-line formula `eulerHeadAnchor_line_im`
(Im = p^{−1/2}sin(τ log p)) and `eulerHeadAnchor_not_lineReflection_on_line` (the anchor
breaks the mirror symmetry at all heights off a discrete set). Doc 108 addendum has the
route reading and the next object (defect steering by choice of P).
- `RHTower/RectangleResidue.lean` (new, in umbrella): the argument principle on a rectangle — a mathlib gap, built from scratch. `rectangle_winding`: the boundary contour integral of the Cauchy kernel `(z−p)⁻¹` around an axis-aligned rectangle enclosing `p` is `2πi`. Mechanism: the three edges where `z−p` avoids `ℝ≤0` use the antiderivative `log(z−p)`; the left edge (where `Re(z−p)<0`) uses the rotated branch `log(−(z−p))`, whose argument lies in the right half-plane — both have derivative `(z−p)⁻¹`, so each edge integral is a branch-value difference (FTC), and the two branches disagree by `πi` at each left corner (arg of a negation), telescoping to `2πi`. Packaged as `rectIntegral` with linearity (`rectIntegral_add`, `rectIntegral_const_mul`, `rectIntegral_finsetSum`), the boundary Cauchy theorem (`rectIntegral_eq_zero_of_analyticOnNhd`, from mathlib's rectangle Cauchy), and congruence.
- `RHTower/RectangleResidue.lean`: the residue theorem. `rectIntegral_logDeriv_single_zero`: for `h` analytic and nonvanishing near the closed rectangle and `ρ` strictly inside, `∮_{∂R} logDeriv((·−ρ)^m·h) = 2πi·m`. `rectIntegral_logDeriv_multi_zero`: for finitely many interior zeros `ρ i` of orders `m i`, `∮_{∂R} f'/f = 2πi·Σ m i`. Proof: peel the zeros (`logDeriv_mul`/`logDeriv_prod`/`logDeriv_fun_pow`) into a finite sum of Cauchy kernels plus `logDeriv h`; the kernels each integrate to `2πi` and the boundary-holomorphic cofactor term vanishes by the rectangle Cauchy theorem. Big picture: a route-independent complex-analysis backbone — the winding of `f'/f` around a box counts the enclosed zeros with multiplicity, the tool a closed-box zero-count/Gate-4 assembly and the `hagree` argument-principle escape both consume. All axiom-clean `[propext, Classical.choice, Quot.sound]`; `lake build MainTheorems` green (9214 jobs); lint + index pass.

## CarrierWeld.lean (milestone M — the weld built, grammar gate answered)

`RHTower/CarrierWeld.lean` — axiom-clean, umbrella-imported (doc 109):
* `ledgerChainE_prod_jumps` — jump extraction: every listed hole-centred zero enters by
  an EXACT monomial jump between consecutive partial products (the structural-pivot gate
  did not fire; reuses the banked `ledgerChainE_trans`).
* `ledgerChainE_to_xi_of_split_domination` — the canonical chain cofactor → ξ: jumps for
  the factors, one dominated move for the gap; event list = ones.
* `enclosed_count_eq_of_split_domination` — Rouché-type counting WITHOUT the argument
  principle: root transport along the chain vs the isolating deck-class identity at level
  m + count + 1 forces count = ord_ρ(ξ).
* `anchoredEventLedger_of_carrier_domination` — the weld: (S)+(D)+Even count ⟹
  AnchoredEventLedger (pairing constructed).
* `rhLadder_one_of_carrier_domination` — milestone M: even split dominating members on
  isolating annuli at all off-line zeros ⟹ RHLadder 1.
* `exists_split_domination_of_isolating` — tightness: the peel is always a split
  dominating member with count = m, so the interface is lossless and its sole content is
  the parity of an independently supplied count.
Open problems now exactly: (D-supply) chart domination for the mollified anchored member,
(S-supply) carrier Hurwitz split, (parity certificate) from carrier boundary data via the
anchored tilt instruments.

## ReflectedGridOffgridBridge.lean — paired off-grid accounting bridge

- `reflectedGridOffgridCharge C N L`: the canonical completed reflected-grid charge at `reflectedGridRatioCenter`, cast to `ℤ`, plus the sum of an off-grid/noncollision integer event list `L`.
- `reflectedGridOffgridCharge_even_of_paired`: `N ≥ 1` and `LedgerFluxPaired L` imply the accounted grid-plus-offgrid charge is even.
- `reflectedGridOffgridCharge_deckRed_two_eq_one_of_paired`: deck form, `deckRed 2 (accounted charge)=1`.
- `reflectedGridOffgridCharge_deckRed_two_eq_one_of_accounted`: if a future physical charge `Q` is proved equal to this accounted expression, then `deckRed 2 Q = 1`.
- Verification: `lake env lean GaloisForLFunctions/RHTower/ReflectedGridOffgridBridge.lean`; `lake build GaloisForLFunctions.RHTower.ReflectedGridOffgridBridge`; `lake build GaloisForLFunctions.RHTower`; `/tmp` axiom checks at `[propext, Classical.choice, Quot.sound]`; `scripts/formal_tools.py index`; `scripts/formal_tools.py lint --check-generated`.
- Boundary left open: this is an accounting bridge, not the physical AFE reduction. The remaining task is to construct the physical carrier charge `Q`, prove `Q = reflectedGridOffgridCharge C N L`, and prove `LedgerFluxPaired L` for its off-grid/noncollision events.

## CarrierSplit.lean + ZetaDominationTransfer.lean (the three supply problems, doc 110)

Axiom-clean, umbrella-imported. Survey reused: ZetaCarrier §7 (completed_domination_iff,
AFEAccurateOn/CarrierFloorOn + assembly), ledgerChainE_trans, exists_peel's
order-preservation clause.
* (S-supply) DISCHARGED: `charts_union_eq_annulus` (slit charts cover the annulus),
  `finite_closedBall_zeros` (compact-accumulation + isolated-zeros alternative),
  `exists_split_of_finite_zeros` (complete peeling, descent on zero-set cardinality),
  `exists_split_of_domination` (domination ⟹ split, unconditional).
* Weld upgraded: `anchoredEventLedger_of_domination`, `rhLadder_one_of_domination_parity`
  — the (S) clause is gone; rung ⟸ domination + parity.
* (parity certificate): `split_deckClass_one_iff_even` — square roots of a split member
  on the charts have deck class exp(2πi·count/2); trivial ⟺ even. The parity IS the
  member's own mod-2 deck cocycle: a carrier-side boundary datum.
* (D-supply) reduced: `rhLadder_one_of_zeta_carrier_close` (raw ‖ζ−gN‖<‖gN‖ on charts)
  and the capstone `rhLadder_one_of_interfaces_parity` — the base rung from
  (AFE) + (LOW) on the charts of one isolating annulus per off-line zero + (PAR).
Residual analytic content of the base rung: exactly (AFE), (LOW on charts — segment→chart
carry over banked second-moment floors), (PAR).
- `RHTower/RectangleResidue.lean` (§8, new): `rectIntegral_logDeriv_boxCount` — the rectangle zero-count in factorization form. For `f = (∏_{i∈t}(·−ρ i)^{m i})·h` on a neighbourhood of the closed box with `h` analytic nonvanishing and each `ρ i` strictly inside, `∮_{∂R} f'/f = 2πi·Σᵢ m i`. Same factorization hypotheses as the deck route `box_charge_eq_deckRed`, so the two are drop-in comparable: the contour recovers the raw integer total order, the deck cocycle only its residue mod n. Proof swaps `logDeriv f` for `logDeriv(product)` on the edges (germ congruence, `f = product` on the open `U`) then applies `rectIntegral_logDeriv_multi_zero`.
- `RHTower/CarrierBoxCount.lean` (new, in umbrella): specialization to the completed carrier. `completedGN_offline_factor` — on a strip region `U` avoiding the Γ_ℝ poles of `s` and `1−s` and the trivial points `{0,1}`, `completedGN N = archFactor·gN` factors as `(∏_{w∈t}(·−w)^{m w})·(archFactor·h_gN)` with the Euler head `archFactor` folded into a nonvanishing analytic cofactor (`archFactor` is zero-free there), peeling `gN`'s box zeros (`exists_multi_peel`); each `m w` is pinned to the intrinsic order `analyticOrderAt (completedGN N) w`. `completedGN_rectIntegral_logDeriv` — the payoff: `∮_{∂R} (completedGN N)'/(completedGN N) = 2πi·Σ_{w∈t}(analyticOrderAt (completedGN N) w).toNat`, the exact integer total order of the enclosed off-line zeros read straight off the contour, a route to the box zero-count independent of the deck cocycle (which gives only its mod-n reduction). Supporting general lemmas: `analyticOrderAt_finset_prod` (order of a finite product = Σ orders, a mathlib gap) and `analyticOrderAt_of_boxFactorization` (order of a boxed factorization at a centre = its multiplicity). All axiom-clean [propext, Classical.choice, Quot.sound]; `lake build MainTheorems` green (9218 jobs); lint + index pass.

## 2026-07-06 — (AFE)+(LOW) discharged unconditionally; ladder transported to finite members (doc 111)

New modules `EMAnnulusSupply.lean`, `SymmetrizedEMCarrier.lean` (umbrella updated; full
gate 9220 jobs exit 0; all 22 endpoints axioms = [propext, Classical.choice, Quot.sound]).

- `xi_zero_re_lt_one`; `completedEM = archFactor·emCarrier`; `completedEM_domination_iff`.
- `zeta_annulus_floor` (compactness+isolation) + EM tail decay ⟹
  `exists_isolating_em_domination`: at EVERY strip point an isolating annulus + N with
  completed-member domination on the slit charts — NO hypothesis.
- `EMSplitData`/`emSplitData_exists`/`emSplitData_count_eq` (count = central order);
  `rhLadder_of_em_split_multiplicity` (all rungs k), `rhLadder_one_of_em_split_parity`,
  `riemannHypothesis_of_em_split_multiplicity`.
- Symmetric lane: `semCarrier = chiSymmetrize zetaChi (emCarrier N)` targets 2ζ
  (`two_zeta_sub_semCarrier_norm_le`); `completedSEM` has exact EVEN FE
  (`completedSEM_one_sub`), Schwarz reality (`completedSEM_conj`), line reflection
  (`completedSEM_lineReflection`), free mirror order pairing
  (`completedSEM_orderAt_one_sub`); generic `exists_domination_of_uniform_decay`;
  `exists_isolating_sem_domination`; `SEMSplitData` + all rungs + RH endpoint.

Rung interface now: RHLadder k ⟸ 2^k ∣ hole count of the finite member's dominating
splits (which exist unconditionally); (AFE)/(LOW) deleted from the interface.

## 2026-07-06 (later) — the three named objects of doc 111, built

`FiniteMemberSteering.lean` (new) + `SymmetrizedEMCarrier.lean` §8/order additions;
umbrella updated; 11 new endpoints axioms = [propext, Classical.choice, Quot.sound].

- Tilt coupling: `anchoredSEM = eulerHeadAnchor · completedSEM`;
  `anchoredSEM_lineReflection_mismatch` (member's mirror mismatch = anchor's, exactly);
  `anchoredSEM_mirror_polar` (reflected value = conj member value rotated by
  anchorMirrorDefect, scaled by anchor moduli); `anchoredSEM_splitData` +
  `anchoredSEM_deckClass_one_iff_even` (anchor is a strip unit — same centres, parity
  reads on the anchored object); `eulerHeadAnchor_analyticAt` + generic
  `analyticAt_finset_prod`.
- Order pairing: `completedSEM_orderAt_conj`, `completedSEM_orderAt_lineReflect`
  (reused banked `analyticOrderAt_conj_of_conjEquivariant` from AnnealWindowRelation —
  survey first, no rebuild).
- N-steering: `sem_uniform_decay_on_compact`,
  `xi_sub_completedSEM_uniform_decay_on_compact` (member → ξ uniformly on strip
  compacts), `splitData_count_rigid` (EM and SEM splits carry the same count),
  `sem_hole_zeros_localize` (∀ ε > 0, all hole zeros within ε of the centre for N
  large: count pinned, support collapsing).

## 2026-07-07 — defect steering quantified + steering supply (doc 112)

`DefectSteering.lean` (new; umbrella updated); 19 endpoints, all axioms =
[propext, Classical.choice, Quot.sound].

- `im_eulerFactor` (Im factor = q^{−Re s}·sin(Im s·log q) at every real part);
  `primeTilt_pos_iff`/`primeTilt_neg_iff` (tilt sign = sine sign).
- Defect walk algebra: `anchorMirrorDefect_empty`/`_singleton`/`_insert` with
  `mirrorTiltIncrement q s = primeTilt q (1−s̄) + primeTilt q s`.
- Steering laws: `mirrorTiltIncrement_pos`/`_neg` (sign = sign sin(τ log q)),
  `mirrorTiltIncrement_ge` (arctan floor), `abs_mirrorTiltIncrement_le` (budget ceiling).
- Root-level turning: `canonicalAnchorRoot` (= √‖A‖·e^{i·tilt/2}), `_sq`, `_ne_zero`,
  `canonicalAnchorRoot_mul_mirror` — mirror pairing rotates by EXACTLY defect/2.
- Rigidity: `anchoredSEM_roots_of_sem_roots` via banked `deckClass_mul_global`:
  anchoring preserves the deck class — phases turn, parity class fixed.
- Steering supply (§6): `exists_prime_log_mem_Ioo` (Bertrand in log windows),
  `exists_prime_tau_log_window`, `exists_prime_sin_pos`/`_neg`,
  `exists_prime_mirrorTiltIncrement_pos`/`_neg` — both step signs at every prime scale
  for heights 0 < Im s < π/log 2; PNT-grade gaps / Chebyshev counting named as the open
  supplies for all heights / full reachability.

## 2026-07-07 (later) — §7 meeting functional domain

- `deckClass_one_iff_signs_agree` (class = two-point sign agreement, generic);
- `sem_even_iff_anchored_signs_agree` (Even hole count ⟺ basepoint signs of the
  anchored member's roots agree — the weld as ONE equation, rigid LHS vs steered RHS).
Gate 9222 jobs exit 0; both endpoints axiom-clean.

## 2026-07-07 (later) — WindowBudget.lean: Chebyshev counts, gap interface, REACHABILITY (doc 113)

14 endpoints, all axioms = [propext, Classical.choice, Quot.sound]; gate 9223 jobs exit 0.

- `windowPrimes` + `sum_log_windowPrimes` (window mass = θ-increment) +
  `windowPrimes_card_ge` (Chebyshev count; threshold L > log 2, counts divergent).
- `PrimeWindowSupply L` interface (PNT-grade gaps as named input);
  `primeWindowSupply_of_log_two_lt` (unconditional region);
  `exists_prime_sin_pos/neg_of_supply` (uniform √2/2 sine floor, quarter-offset
  windows); `exists_prime_mirrorTiltIncrement_pos/neg_of_supply` (steering wheel at
  EVERY height, conditional).
- `anchorMirrorDefect_eq_sum`, `arctan_ge_half_self`, `exists_subset_sum_between`
  (greedy), `rpow_neg_anti`, `log_le_mul_rpow` (filter-free asymptotics).
- **`anchorMirrorDefect_reachable_nonneg`**: for 0 < Im s < π/(2 log 2), every T ≥ 0,
  every ε > 0: ∃ finite prime set P with T ≤ defect(P) ≤ T + ε. Fully explicit
  constants; one Chebyshev window + greedy accumulation.
