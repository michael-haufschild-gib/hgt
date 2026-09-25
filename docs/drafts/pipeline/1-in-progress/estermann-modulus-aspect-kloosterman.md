# The modulus aspect of the Estermann family: Kloosterman mixing

- **ID:** estermann-modulus-kloosterman
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + CANNOT
- **Statement:** The inverse twist of the twisted divisor family has Kloosterman coefficients and
  square-root cancellation in the modulus; the functional equation carries that cancellation to the
  additive twist, giving the divisor function in a progression to a prime modulus the unconditional
  critical-line exponent `9/4`; but the `ζ`-content of every nonzero mode sits a factor `√q` below
  the threshold Weil's theorem certifies, so the mixing cannot constrain `ζ`.

## Goal

CANNOT-384 shows the shifted divisor correlation is not reachable modulus by modulus and demands
cancellation between moduli. This card asks what the modulus aspect of one modulus actually gives,
and whether any of it reaches `ζ`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (all statements below are dependency-closed)
- [x] 2 → 3  formalized (seven modules, all axiom-clean, wired into `GaloisForLFunctions.RHTower`)
- [ ] 3 → 4  not pursued (no stage 4)

## The three pairings

For `a` running over the reduced residues mod `q`:

| pairing | coefficients | size |
|---|---|---|
| `χ(a)` | `τ(χ)L(s,χ̄)²` | diagonal; a restatement of GRH |
| `e(ab/q)` | Ramanujan `c_q(N+b)`; for prime `q`, `q∑_{N≡−b} d(N)N^{−s} − ζ(s)²` | `φ(q)`, no cancellation |
| `e(a⁻¹b/q)` | complete Kloosterman `S(N,b;q)` | `2√q` by Weil |

Only inversion is not a group homomorphism, and it is exactly the map the Estermann functional
equation carries.

## Results

1. `∑_{a} e(a⁻¹b/q) D(s,a/q) = ∑_N d(N)S(N,b;q)N^{−s}` for `Re s > 1`
   (`RHTower.hasSum_kloosterman_estermannZeta`).
2. For an odd prime modulus and `b ≠ 0`, `|S(m,b;p)| ≤ 2√p` for **every** first frequency: the unit
   case is Weil's normalisation and `m = 0` collapses to the Ramanujan value `−1`
   (`RHTower.norm_kloostermanSum_le_weil`). Hence
   `‖∑_a e(a⁻¹b/p)D(s,a/p)‖ ≤ 2√p ∑_N d(N)N^{−σ}` against the trivial `(p−1)∑_N d(N)N^{−σ}`
   (`RHTower.norm_estermann_invTwist_le_weil`, `RHTower.two_sqrt_lt_totient`).
3. The polar decomposition `D(s,a/q) = q^{1−2s}ζ(s)² + q^{−s}R_a(s)` gives every weighted average
   the `ζ`-content `q^{1−2s}ζ(s)²` times the **total weight**; the inverse twist's total weight is
   `−1` (`RHTower.sum_units_stdAddChar_invTwist`), so every mode `b ≠ 0` carries exactly
   `−q^{1−2s}ζ(s)²` and the zero mode carries `φ(q)q^{1−2s}ζ(s)²`
   (`RHTower.sum_invTwist_estermannZeta_zeta_content`,
   `RHTower.sum_estermannZeta_units_zeta_content`).
4. The functional equation exchanges the two twists
   (`RHTower.estermannAddTwist_one_sub`):
   `∑_a e(ab/q)D(1−s,a/q) = A(s)(∑_a e(a⁻¹b/q)D(s,a/q) + cos(πs)∑_a e(−a⁻¹b/q)D(s,a/q))`.
5. Consequently the additive twist has the saved left edge
   `‖∑_a e(ab/p)D(−1+it,a/p)‖ ≤ K p³√p e^{π|t|}`, polynomial form `K p³√p |t|³`
   (`RHTower.norm_estermannAddTwist_left_edge_le`, `..._poly_le`), against `p³φ(p)`.
6. Normalising by `q^{(5/6)(s−2)}` equalises the two edge exponents at `1`; Phragmén–Lindelöf and
   unwinding give
   `‖∑_a e(ab/p)D(1/2+it,a/p)‖ ≤ C p^{9/4}(1+|t|)³`
   (`RHTower.norm_estermannAddTwist_critical_line_le`) against the convexity value
   `φ(p)p^{3/2} ≍ p^{5/2}`.

## No-go closure

- **Exact killing mechanism (CANNOT-387).** The modulus exponent of the `ζ`-content of a nonzero
  mode is `1−2σ`, which is `< 1/2` throughout `σ > 1/4` and is exactly `0` on the critical line,
  while Weil's certified accuracy for that mode has exponent `1/2`
  (`RHTower.norm_cpow_one_sub_two_mul`, `RHTower.zetaContent_modulus_lt_weil`,
  `RHTower.norm_riemannZeta_sq_le_divisorMass`). Square-root cancellation inside one modulus is
  therefore blind to `ζ`. The only weights keeping the `ζ`-content at the size of the bound are
  those with total of order `q`, and for those the coefficients degenerate to Ramanujan sums, which
  provably do not cancel.
- **Strongest positive survivor.** Items 2, 4, 5, 6: an unconditional `√q` saving within the
  modulus, the twist-exchange law, and the critical-line exponent `9/4` for the divisor function in
  a progression to a prime modulus. All Lean-proved and axiom-clean.
- **New insight (MUST-388).** The symmetry of the family is a mixing operator: in the additive
  Fourier basis the inversion has entries `q^{−1}S(m,−n;q)`, flat at scale `2q^{−1/2}` away from the
  zero frequency and of size `1` at it. The one non-flat row is the Ramanujan row, which is where
  `ζ` lives; across moduli that row has generating function `σ_{1−w}(N)/ζ(w)`. At modulus one the
  operator is a scalar, which is why the level-one functional equation carries no information about
  the zeros.
- **Status.** Paper proof and Lean formalization complete for every item; route detail in
  `estermann-uniformity-working-log.md` entries `EK-1`…`EK-7`.

## Open core

Cancellation between moduli. Within a modulus the picture is now closed in both directions: the
nonzero modes are settled by Weil, the zero mode carries all of `ζ` and no cancellation. The
remaining object is the zero mode summed over moduli, whose generating function is `1/ζ(w)` times
explicit zeta factors, and the nonzero modes summed over moduli, whose abscissa Weil moves from `2`
to `3/2` and whose poles are the exceptional eigenvalues.

## Log
- 2026-09-24 — created; items 1–6 proved and formalized; CANNOT-387 / MUST-388 recorded.
