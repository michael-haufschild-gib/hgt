# Big-Witt centered-prime-mark / completed-Xi spectral-fiber comparison

- **ID:** big-witt-centered-mark-xi-fiber
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** internal Lean corpus audit; Borger big-Witt Frobenius; Deninger completed-Xi spectrum
- **Statement:** Big-Witt Frobenius is vertical on the centered-prime-mark reporter of every completed-Xi theta fiber, and its orbit on every right-half fiber is injective.

## Goal

Separate the unconditional Big-Witt operation from the missing horizontal completed-Xi fiber
transport.  The result must use the existing source Frobenius, existing centered prime mark, and
existing completed-Xi quotient spectral fiber without assuming any divisor stability, source
admission, RH, or new axiom.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, axiom/lint audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact objects

Put

`s(alpha) = 1/2 + I alpha`,

`U_p(alpha) = [u_p(s(alpha))]` in the big-Witt ring over `C`, and

`O_p(alpha,k) = [u_p(s(alpha))^(2^k)]`.

The completed-Xi theta fiber at `alpha` is the subtype of nonzero `x` satisfying

`Theta x = s(alpha) • x`.

The reporter from that fiber to the big-Witt ring is constant on the vector coordinate and has
value `U_p(alpha)`.  This is a comparison reporter, not a transport of cohomology classes.

## Conjecture / failure loop

1. **[CONJECTURE A] Horizontal Frobenius transport.**  Seek an endomorphism of completed-Xi
   cohomology sending the fiber at `alpha` to the fiber at `2 alpha` and inducing big-Witt
   Frobenius on `U_p(alpha)`.
   **Verdict: CIRCULAR / OPEN.**  Existing big-Witt Frobenius has no action on
   `DeningerEntireH1`.  Such a total fiber transport forces
   `XiC alpha = 0 -> XiC (2 alpha) = 0`, precisely the missing divisor-stability input.

2. **[CONJECTURE B] Finite Frobenius periodicity.**  Seek `a < b` with
   `O_p(alpha,a) = O_p(alpha,b)` on a hypothetical right-half completed-Xi fiber.
   **Verdict: FALSE.**  Teichmüller injectivity reduces this to equality of two powers of the
   nonzero contraction `u_p(s(alpha))`; their norms force `2^a = 2^b`, hence `a=b`.

3. **[CONJECTURE C] Vertical comparison and exact no-go.**  Keep `alpha` fixed and change the
   arithmetic base.  Then Frobenius sends `O_p(alpha,k)` to `O_p(alpha,k+1)`, and
   `O_p(alpha,k)` equals both the base-changed reporter at `p^(2^k)` and the scalar reporter at
   label `(2^k) alpha`.  The first equality is an actual same-fiber operation; the second is only
   a reporter identity and supplies no element of the doubled completed-Xi fiber.
   **Verdict: SURVIVES; [BRIDGE] with a new exact route boundary.**

## Paper proof target

For every `p`, `alpha`, and `k`:

1. `F_2(O_p(alpha,k)) = O_p(alpha,k+1)`.
2. `O_p(alpha,k) = [u_(p^(2^k))(s(alpha))]`.
3. `O_p(alpha,k) = [u_p(s((2^k) alpha))]`.
4. The completed-Xi theta fiber at `alpha` is inhabited iff `XiC alpha = 0`.
5. For every completed-Xi theta eigenpair with `Re(s(alpha)) > 1/2`, the map
   `k |-> O_2(alpha,k)` is injective; equivalently it has no finite preperiodic collision.

## Dependency-closed proof

- Existing `deningerBigWittFrobeniusTwoRingHom_teichmuller` gives
  `F_2([a]) = [a^2]` over every commutative ring.
- Existing `centeredPrimeMark_primePower` gives
  `u_(p^m)(s) = u_p(s)^m`.
- Expanding the centered mark and using `exp(m z) = exp(z)^m` gives
  `u_p(s(m alpha)) = u_p(s(alpha))^m`.
- Apply the Teichmüller Frobenius law with `a = u_p(s(alpha))^(2^k)` and use
  `(a^(2^k))^2 = a^(2^(k+1))`; this proves the successor law.  The two comparison identities
  follow from the preceding base-power and spectral-label laws with `m=2^k`.
- Existing `XiC_eq_zero_iff_exists_deningerEntireTheta_eigenvector` is exactly the fiber
  inhabitation equivalence after packaging witnesses as a subtype.
- On a right-half fiber, existing `centeredPrimeMark_norm_lt_one_iff` at base `2` gives
  `|u_2(s(alpha))| < 1`; exponential nonvanishing gives positive norm.  Equality of orbit terms,
  followed by Teichmüller injectivity and norms, makes the power exponents equal.  Injectivity of
  `k |-> 2^k` gives equality of orbit indices.

No step assumes existence of a right-half fiber.  No step constructs a map between distinct
completed-Xi spectral fibers.

## No-go closure

- **Exact killing theorem/mechanism:** big-Witt Frobenius changes the arithmetic base at fixed
  completed-Xi spectral coordinate; horizontal reinterpretation is scalar aliasing, not fiber
  transport.  Right-half reporter orbits are injective, so finite Frobenius collision is impossible.
- **Strongest positive survivor:** exact vertical orbit/base-change/spectral-label classification
  plus unconditional right-half nonperiodicity.
- **New insight:** equality `u_(p^m)(s(alpha)) = u_p(s(m alpha))` is representation-ambiguous.
  Only the left side is induced by source Frobenius.  Treating the right side as Xi fiber motion is
  the precise unsupported step.
- **Status:** internal and current-primary-literature audits complete; `[PROVED HERE]` with no open
  paper dependency; pending Lean name verification and formalization.

## Log

- 2026-08-18 — created in 1-in-progress after Lean-first corpus search and three conjecture audits.
- 2026-08-18 — hostile proof audit passed; moved to 2-fully-proven as `[PROVED HERE]`.
