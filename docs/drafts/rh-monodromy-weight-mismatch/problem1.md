What analyticOrderAt xi ρ is

xi is the completed Riemann zeta — entire, order 1, xi s = s(s−1)/2·Λ(s), symmetric under s↦1−s. Its zeros are exactly the nontrivial zeros of ζ; they sit in the critical strip 0 < Re < 1, and RH says they all sit on Re = 1/2.

analyticOrderAt xi ρ is the order of vanishing of xi at ρ — a value in ℕ∞:

- = 0 where xi(ρ) ≠ 0 (almost everywhere),
- = m (a positive integer, the multiplicity) at a zero of order m,
- = ⊤ only if xi were identically zero locally (never happens).

As a function of ρ it is the divisor of xi: it records where the zeros are and how deep each one is. That single object contains RH and more — RH is a statement about the ρ with nonzero order (their real parts), and the multiplicity is the finer data on top.

How the ladder rewrites RH into it

rightHalf = {Re s > 1/2}. The formalized chain (rh_iff_forall_ladder) is:

RiemannHypothesis  ↔  ∀ k, RHLadder k
RHLadder k  :=  ∀ ρ ∈ rightHalf, xi ρ = 0 → 2^k ∣ analyticOrderAt xi ρ

Read RHLadder k literally: every zero in the open right half has multiplicity divisible by 2^k. The equivalence to RH is an arithmetic squeeze — if there were a zero ρ in rightHalf with a finite multiplicity m ≥ 1, then 2^k ∣ m for all k is impossible (eventually 2^k > m); so ∀k forces the zero set in rightHalf to be empty, which is RH. Conversely RH makes rightHalf zero-free, so every clause is vacuous.

Level 1 (k=1) is the softest nontrivial rung: no zero off the line has odd multiplicity — in particular no simple off-line zero.

Three further formalized re-expressions of the same clause, so you see it isn't a trick of phrasing:
- rhLadder_iff_root: RHLadder k ⟺ xi has an analytic 2^k-th root on rightHalf.
- xi_deckClass: around any ρ the deck class of xi's local 2^k-th roots is exp(2πi·m/2^k), m = analyticOrderAt xi ρ.
- xi_deckClass_eq_one_iff_ladder_dvd: that deck class = 1 ⟺ 2^k ∣ analyticOrderAt xi ρ.

So the whole tower — roots, deck monodromy w_k, the ladder — is a faithful re-encoding of one number per zero: m(ρ) = analyticOrderAt xi ρ, and specifically its residue m(ρ) mod 2^k.

Where we get stuck — exactly

We need to force m(ρ) mod 2^k = 0 (equivalently w_k(ρ) = 1) at every off-line zero. Nothing in the constraint structure of xi pins that residue. Here is the census of what constrains m(ρ), all formalized, and why each fails:

- Functional equation (s↦1−s): gives m(ρ) = m(1−ρ) — a pairing of zeros. It never forces a divisibility of either one. (Doc 106: the pinned FE symmetry group is Klein-four, exponent 2 — it can supply parity-of-a-symmetry, not an unbounded weight.)
- Reality (s↦s̄): gives m(ρ) = m(ρ̄) — another pairing, whose fixed axis is the real axis, orthogonal to where the zeros live. (Doc 105: the conjugation shadow is blind to every off-line zero — off-axis zeros pair ρ↔ρ̄ and cancel mod 2.)
- Euler positivity / Landau (Λ(n)≥0): gives zero-free half-planes — inequalities, never congruences on an existing zero. Order-parity is a sign change, not an inequality. (Doc 105.)
- The Euler product / prime side {σ_p}: lives on Re s > 1, where xi has no zeros at all (eulerPartial_zeroSet_eq_empty). The divisor lives in the strip. Disjoint carriers (doc 127) — the two never meet at a point; the only bridge is analytic continuation across Re s = 1, which is a flow the program refuses.

The mechanism we wanted was the q62 "weight mismatch": kill an off-line defect with an automorphism of unbounded order that fixes the constraints and scales the defect by 2^k. The formal results say that automorphism does not exist at the germ: the joint symmetry is exponent-2 (doc 106), the prime action is a unit = a central scalar hence deck-invisible (docs 127, 131 crossBoundary_smul_one), the free reference tower is a coboundary (doc 128), and every pinned-germ model of the σ_p-defect is fake (docs 130–131). The one unbounded-order action available (the Kummer deck itself) has weight = m mod 2^k — the very thing to be proved, i.e. circular.

What, precisely, we cannot solve

Constrain the multiplicity — even the parity — of a hypothetical off-line zero of a specific transcendental function, from that function's defining constraints.

Concretely: m(ρ) is a positive integer attached to a strip point ρ. To even see it you must evaluate the analytically-continued xi at ρ — across the wall Re s = 1 — and the continuation carries the value but hands you no algebraic/arithmetic grip on the integer m(ρ) mod 2^k. There is no generative rule to read it off, because xi is fixed by a constraint (FE, Euler product) and is hypertranscendental — the divisor is not propagated by any recurrence you could reduce mod 2^k. The symmetries that could pin it are all either exponent-2 (parity of a reflection, not 2^k) or supported on the wrong locus (real axis / Re s > 1), never on the strip zeros.

That is why the seam construction is such a clean diagnostic: it reconstructs xi intrinsically — FE and all, from the primes and the archimedean Gaussian, no ζ cited — and then, as I formalized (seamDivisor_eq_xiOrder, seamDivisor_ladder_clause), hands back analyticOrderAt xi ρ and the identical ladder clause 2^k ∣ analyticOrderAt xi ρ. It gives the divisor as zeros of a function, not as eigenvalues of an operator. So it loops precisely back to the one number we cannot constrain. To get unstuck you would need the divisor delivered in a form where the multiplicity is a spectral or cohomological quantity — a 2^k-graded invariant of some operator/complex that is forced by symmetry — rather than "the order to which this specific entire function happens to vanish." Producing that graded, multiplicity-carrying object (a Frobenius whose Lefschetz trace is the divisor, or a Hilbert–Pólya operator whose eigenvalue multiplicities are the m(ρ)) is exactly the apex, and it is the thing none of the pinned-germ, symmetry, positivity, or reconstruct-xi routes deliver.
