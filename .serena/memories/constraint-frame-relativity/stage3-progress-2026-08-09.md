# constraint-frame-relativity → stage 3 progress (2026-08-09)

Goal: unconditionally formalize every proven theorem in
`docs/drafts/pipeline/2-fully-proven/constraint-frame-relativity` (14 cards), wire into
`GaloisForLFunctions.HTGeometry`, write `<id>-formalized.md` companions, `git mv` to
`docs/drafts/pipeline/3-formalized/constraint-frame-relativity/`.

## New Lean area

`formal/GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/` — namespace
`HTGeometry.ConstraintFrameRelativity`.  (Distinct from the existing `ConstraintRelativity/`
folder, which serves a different card folder.)

## Modules GREEN so far

1. `ShellRamificationPower.lean` — `shellIndicator (r*m) (k^r) = shellIndicator m k` (RP.4),
   `mFree_iff_forall_factorization_lt`, squarefree descent (RB.2), `IsRPow`,
   `excess_witness` (`2^(rm)·3`).
2. `BernoulliBooleanGibbs.lean` — product Bernoulli weight/expectation on `Finset ι`,
   `bernoulliExp_prod` (= `Finset.prod_add` backwards), subset-occupation law,
   `bernoulliCov_linearStat` (diagonal covariance of linear statistics).
3. `SchurCapacity.lean` — `capA/capB/capC`, `schurCapacity`, variational `IsLeast`,
   two-row Cauchy–Binet `capA_mul_capC_sub_capB_sq`, positivity, `≤ π² A`.
4. `FiniteTiltResponse.lean` — `wexp/wcov`, `tiltExp/tiltCov`, `hasDerivAt_tiltExp` (RB.16),
   `hasDerivAt_tiltCov` (RB.19), `hasDerivAt_capacityOfMoments`,
   `hasDerivAt_tiltSchurCapacity` (RB.18), fugacity derivative (for RB.21).
5. `ShellExcessDirichlet.lean` — `powerImageStream`/`excessStream`, RP.7
   `lSeries_shell_eq_dilate_add_excess`, excess witness nonzero.

## Lean traps hit

- `convert h using 1` on `HasDerivAt` descends into instance arguments and produces
  `Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup` goals.  Use
  `HasDerivAt.congr_deriv` instead — always.
- `field_simp [someDef]` does not reliably unfold a `def`; use `simp only [theDef]` first.
- `rw [LSeries.term]` fails (match-based); use `LSeries.term_of_ne_zero` / `LSeries.term_zero`.
- `Complex.natCast_cpow_natCast_mul (n m : ℕ) (z) : (n:ℂ)^((m:ℂ)*z) = ((n:ℂ)^m)^z` is the
  reindexing lemma for `S_m(r s)`.
- `rcases h with a | b <;> simp [a, b]` is a name error; use `with h | h <;> simp [h]`.

## Cards PROMOTED to stage 3 (companion written + `git mv` done)

1. `ramification-power-law-event-capacity-extension-law` (RP.4, RP.7, RP.11-RP.18 incl. RP.16).
2. `ramification-diagonal-boolean-descent-route-e-schur-response-law` (RB.2, RB.4-RB.6,
   RB.7-RB.13, RB.16, RB.18-RB.21).
3. `ramification-excess-octahedral-composition-law` (RE.3a-RE.17).
4. `ramification-witt-carry-boolean-hardcore-recurrence-law` (WC.3-WC.13).
5. `ramification-escort-logit-phase-comparison-coherence-law` (EL.2-EL.24 incl. Thm 5.1).
6. `ramification-power-phase-history-time-dilation-law` (PH.6-PH.14) — module
   `PhaseHistoryDilation.lean`; REUSES `primeLogFiniteSlice_linearIndependent` and
   `kronecker_approx` from `HTGeometry/KroneckerWeylDensity` + `PrimeTorusKroneckerDensity`.
   Arbitrarily large return times proved by compactness of the phase torus
   (`IsCompact.tendsto_subseq` on `closedBall (0 : F → ℂ) 1`) + the homomorphism property.

## REMAINING cards (7 not started + 1 WIP)

`ramification-kummer-phase-excess-parseval-law` (hardest analytic: needs Haar on a compact
product group — mathlib v4.32 has NO infinite product measure; plan is `Measure.haarMeasure` on
`∀ p, ZMod r` (compact via Tychonoff) + the translation-invariance proof that a nontrivial
continuous character integrates to zero, then `integral_tsum`),
`ramification-anchor-defect-incidence-interchange-and-bianchi-law`,
`constitutive-jet-factorization-and-withheld-observer-prediction-law`,
`literal-euler-shell-four-axis-flat-frame-and-normalization-exchange-law`,
`monomial-corank-one-four-axis-mixed-chart-law`,
`source-law-base-and-observer-fibre-nonreconstruction-law`,
`static-frame-incompleteness-extension-period-topology-law`,
`valuated-plucker-gram-capacity-exchange-law` (biggest; the Plücker exchange has a short proof:
write b_i in the basis C and use multilinearity of det in one column).

## More GREEN modules

13. `ShellExcessModules.lean` — RE.5-RE.11 free-module split exact sequences,
    `factors_through_shellR_iff`, `quotient_cofiber_equiv`.
14. `WittCarryBoolean.lean` — WC.3-WC.13.
15. `EscortLogit.lean` — EL.2-EL.24 incl. `no_scalar_descent`.

6. `ShellCapacityDepth.lean` — `occVar`, `Aperture` structure, positivity, crude bounds,
   `tendsto_capacity_atTop`, `exists_depth_capacity_lt`.
7. `ShellCapacitySharpScale.lean` — `gram_lower/gram_upper`, `capC_le/capC_ge`, `cLower/cUpper`,
   two-sided scale, `jumpThreshold`, `capacity_lt_of_jumpThreshold_le`.
8. `ShellCapacityAsymptotic.lean` — `tendsto_capacity_div_fug_second` (RP.16).
9. `RamificationBooleanSupport.lean` — `unitalShellIndicator`, `= μ(k)²`, hard core, clock.
10. `BooleanGibbsCapacityResponse.lean` — Gibbs=Bernoulli bridge, Gram entries, ordered ratio,
    `hasDerivAt_booleanTiltCapacity`, `hasDerivAt_fugacitySchurCapacity`.
11. `ShellExcessSupport.lean` — RE.3a/RE.8 support partition, `isRPow` composition, prime arity.
12. `ShellSplitDefectStreams.lean` — RE.11a-RE.11j stream functor, RE.13 Dirichlet cocycle,
    RE.15/RE.16 blindness, witness.

## More Lean traps

- `hλ` / `hτλ` are ILLEGAL identifiers (λ is a token).  Use ASCII names.
- `subst h` with `h : q = p` eliminates `p`, not `q`; use `rw [h]` when `p` is needed later.
- `μ` for Möbius needs `open scoped Moebius` (not `ArithmeticFunction`).
- `Nat.pow_left_injective (hs : s ≠ 0) : Injective (· ^ s)`.
- `div_le_div` is now `div_le_div₀`; `inv_le_inv_of_le` is now `inv_anti₀`.
- `HasDerivAt.sum` gives the Pi-sum function; use `HasDerivAt.fun_sum` for `fun y => ∑ …`.
- `simp only [F.pairTerm_factor]` does not fire on a partially applied `F.pairTerm i j`;
  build the lambda with `funext` first.
- `set k := <expr>` leaves `k` with a BODY; `field_simp` then unfolds it and explodes.  Add
  `clear_value k` (keeping a characterising equation such as `k * (2*a+b) = 2*a`) before any
  `field_simp`.  Same trick with `set u := (1-4*c)^2` to keep denominators opaque.
- `Finset.not_mem_empty` is now `Finset.notMem_empty`; `div_le_div` → `div_le_div₀`.
- Symmetric difference: write `symmDiff S T`, not the `∆` glyph (easy to type the wrong codepoint).
- `omit [Fintype ι] in` must come BEFORE the docstring, not between docstring and `theorem`.

## Remaining

Cards 1–14 of the task list; see TaskList.  Next: shell capacity depth bounds (RP.11–RP.18),
then the Boolean descent card, excess/octahedral, Kummer, Witt, escort, phase history,
anchor-defect incidence, jet factorization, Euler shell, monomial chart, source-law
nonreconstruction, static frame incompleteness, valuated Plücker–Gram.

## Design plans for the 8 remaining cards (worked out, not yet written)

### `ramification-anchor-defect-incidence-…-bianchi-law`
Edge space `F × F → ℝ`, vertex space `F ⊕ F → ℝ`.
`bipartiteCurrent H D e = if e.1 ∈ H ∧ e.2 ∈ D then 1/(|H|*|D|) else 0`.
Needed: mass 1, ℓ¹ = 1, ℓ² = 1/√(|H||D|); boundary `∂J (inl a) = -(∑_p J(a,p))`,
`∂J (inr p) = ∑_a J(a,p)` giving `u_D - u_H`; the convex split
`J_{H,O⊔L} = (d/(d+ℓ)) J_{H,O} + (ℓ/(d+ℓ)) J_{H,L}` for disjoint nonempty `O,L`, whence
`Ω = (ℓ/(d+ℓ))(J_{H,L} - J_{H,O})` and the three norms (AI.10)/(AI.11) and boundary (AI.12).
Bianchi (AI.15) is pure algebra from `Ω = J₁ - J₂ - T J₃` and `T_t T_s = T_{ts}` — expand both
sides to `J_{m,tsr} - J_{srm,t} - T_t J_{rm,s} - T_{ts} J_{m,r}`.
Arithmetic layer: `H_M(N) = F.filter (v_p N = M)`, `D_q(N) = F.filter (¬ q ∣ v_p N)`;
(AI.4) `J = 0 ↔ D_q(N) = ∅ ↔ N is a q-th power` reuses `IsRPow` + `factorization`.
Witness (AI.13) `N = p₀^{srm} p₁^s p₂`.

### `constitutive-jet-factorization-…`
Thm 2.1: `ker A ⊆ ker B ↔ ∃! B̄, B = B̄ ∘ A` — use `LinearMap.range`, `Submodule.liftQ`.
CJ.3 dual form: `LinearMap.range (LinearMap.dualMap B) ≤ range (dualMap A)`; finite-dim.
Cor 2.2 equivariance: pure computation.
CJ.5/CJ.6: bounded factor iff `‖Bv‖ ≤ C‖Av‖`; Moore–Penrose form when `range A` closed.
Countertheorem 3.1: `A (x n) = (λ n * x n)` on `lp 2`; every finite restriction invertible,
`ker A = 0`, no bounded factor since `‖B̄ (A e_n)‖ = 1` while `‖A e_n‖ = λ n → 0`.
Thm 4.1: the shell vertical mode — needs the derivative-at-0 of the normalized Mellin response;
`N₁ = 2^m·3`, `N₂ = 2^m·5`, both have `max v_p = m`, neither is a prime power.

### `literal-euler-shell-four-axis-…`
Thm 2.1: diagonal operators on `F → ℂ`; restriction naturality, commutation, `d/dt U = -iΛU`,
Kronecker recurrence (reuse `PhaseHistoryDilation`), Rees weight
`ℓ_p = 4p³(log p)²/((p+1)²(p-1)(2p-1))`, `ℓ_p ~ 2(log p)²/p → 0`, `sup ‖R_F⁻¹‖ = ∞`.
Thm 4.1: Bastiani derivative (19) = the quotient rule; (20) is `Cov^{bil}`; (21) termwise.
Normalization wall: `m σ = 1` with `m ≥ 12` forces `σ ≤ 1` where the shell measure diverges.

### `monomial-corank-one-four-axis-mixed-chart-law`
`𝒜_n = [D_n | 1]` with `D_n = diag(ρ e^{iθ}, …, ρⁿ e^{i n²θ})`.  Minors (2) by
`Matrix.det_updateCol` / explicit expansion; matroid `U(n,n+1)`; Gram (12) independent of θ;
circuit (7); prolongation vector (10); winding class (11) in `ℤ^{n+1}/ℤ(1,…,1)`;
inverse bounds (4) via `σ_min` and the Rayleigh quotient at `x = (e_{n-1}-e_n)/√2`.

### `source-law-base-and-observer-fibre-nonreconstruction-law`
Thm 1.1: `MvPolynomial ℕ K`, `MvPolynomial.mkDerivation` with `X (j+1)` resp. the truncated
assignment; `D₊^[n] (X 0) = X n`, `algebraicIndependent_X`; `D_m^[m+1] (X 0) = 0`.
Thm 2.1: `Q_j = (1+j)/2 z² + (3-j)/2 t²`; at `j = 1` both coefficients positive, at `j = 4` the
`t²` coefficient is negative; (SL.3) `Q_after - Q_before = -2(k-ℓ) X_U X_V`.
Thm 3.1: state as "for every invariant of the shared tuple, the two objects agree while the
outcomes differ".

### `static-frame-incompleteness-…`
§1 `Γ_v = ℤ + iℤ` closed, `Γ_w` closure `= ℝ + iℤ` (density of `ℤ + √2ℤ`; irrationality of √2).
Same oriented trivially-valuated frame: the six 2×2 minors have signs `(+,+,-)`.
§2 two-atom measures: `s₀ = s₁ = s₂ = 1`, `s₃⁺ = 31/24`, `s₃⁻ = 11/12` — rational arithmetic.
§3 `c₀₀(P)`, `ε(x) = ∑ x_p`: in `ℓ¹` the kernel is closed with quotient `ℂ`; in `ℓ^p`, `1<p<∞`,
and `c₀` the augmentation ideal is dense (the correction `u_N = -S/N` on `N` fresh coordinates).

### `ramification-kummer-phase-excess-parseval-law`
Ω_r = `∀ p : Nat.Primes, ZMod r`, compact (Tychonoff), `Measure.haarMeasure` normalised.
`∫ χ = 0` for a nontrivial continuous character from translation invariance alone.
Then KP.7/KP.8 by `integral_tsum`; KP.13 by orthogonality + double-series interchange;
KP.15 by Cauchy–Schwarz over the `r^d - 1` nontrivial classes; KP.17 carry class in
`H²(ℤ/s; ℤ/r) ≅ (ℤ/r)/s(ℤ/r)`, vanishing iff `gcd(r,s) = 1`.

### `valuated-plucker-gram-capacity-exchange-law`
Plücker exchange has a SHORT proof: write `b_i = ∑_j α_j c_j` in the basis `C`, then
`det(b₁,…,c_j,…,b_r) · α_j det(c) ` summed is `det(c) det(b)` by multilinearity in one column
(`Matrix.det_updateCol_sum`).  Valuated-matroid axiom then follows from
`ν(∑) ≥ min ν`.  Item 4 `Fitt₀(coker T) = I_r(T)`; item 5 Cauchy–Binet
(`Matrix.det_mul_transpose` / `Matrix.det_conjTranspose_mul_self`), leading coefficient
`∑_{B ∈ B_min} |c_B|²`.  Item 6 normal equations, item 7 `λ_min ≥ det/M^{r-1}`.
Thm 3.1 `S` diagonal unitary: `(TS)(TS)* = TT*`, `p_B(TS) = (∏_{j∈B} u_j) p_B(T)`.
Thm 4.1 `σ_∞ > 0 ↔ sup filling < ∞`; diagonal operator closed range iff `inf |λ_j| > 0`.
Thm 5.1 the three explicit diagonal families.

## WIP file (NOT yet imported into the umbrella — the tree is consistent without it)

`formal/GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/AnchorDefectIncidence.lean`
contains the combinatorial core of the anchor--defect card.  GREEN already:
`bipartiteCurrent`, `bipartiteCurrent_nonneg`, `bipartiteCurrent_eq_zero_of_empty`,
`sum_bipartiteCurrent` (mass one), `edgeBoundary`, `interchange_bianchi` (the three-stage
identity, proved from additivity + `T_t T_s = T_{ts}` + two `mul_assoc` rewrites).
STILL FAILING (open goals, all mechanical):
- `sum_sq_bipartiteCurrent` — trailing `ring` has no goals after `field_simp`.
- `edgeBoundary_bipartiteCurrent` — the two `field_simp` branches.
- `bipartiteCurrent_union` — the three `simp only [...]`/`field_simp` branches; the unused
  simp args should be dropped and the `Finset.mem_union` rewriting done first.
- `interchange_defect`, `sum_abs_interchange_defect`, `sum_interchange_defect` — cascade.
Still to add for that card: the arithmetic layer (`H_M(N)`, `D_q(N)`, AI.4, AI.7, the
`p₀^{srm} p₁^s p₂` witness AI.13/AI.14, and the ordered first-failure flags AI.16/AI.17).
