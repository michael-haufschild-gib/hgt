# T2 natural Abel continuation carries the full positive Hardy divisor

- **ID:** T2-NATURAL-ABEL-FULL-CRITICAL-DIVISOR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route T2 after `T2-NATURAL-ABEL-FORCED-WALL-RESIDUE`
- **Statement:** Every holomorphic continuation of the literal natural Wold Abel germ has residue `-m(rho)` at every positive-height critical-line zero `rho` of zeta; consequently no such continuation has only finitely many radial singular heights.

## Goal

Kill T2 continuation mechanisms allowing finitely many exceptional poles or finitely supported
polar repair.  Prior work forces one universal pole.  T2 could still claim that one
pole is removable by a finite correction.  Full-divisor inheritance proves that every admissible
continuation must retain the infinite positive Hardy divisor.  Only an infinite, coefficient-faithful
divisor-bearing unsplit mechanism survives.

## Gates

- [x] 0 → 1 in-progress: exact claim, T2 chain, corpus and literature frontier specified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem and finite-support no-go, targeted build and axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem, Lean certificate, expert priority audit

## Exact conjecture

Write

`A(s) = abelDirichlet woldNatDifferenceCoeff s`,

`M(s) = integerLogMeshContinuation s`, and

`U = {s : ℂ | -1/2 < Re s ∧ Im s > 0}`.

For every `rho` satisfying

`Re rho = 1/2`, `Im rho > 0`, and `ζ(rho)=0`,

and every `F : ℂ → ℂ` holomorphic on `U` with `F=A` on `U∩{Re s>0}`, there exists `m≥1` such that

`lim_{x→0+} x F((rho-1)+x) = -m`.

Define finite radial singular support to mean that some finite set `S⊂ℝ` contains every height
`tau` at which `F(-1/2+i tau+x)` lacks a finite right-radial limit.  No admissible `F` has finite
radial singular support.

## Exact RH proof chain affected

`T2 Wold-specific terminal-control identity`
→ `continuation of literal natural Abel germ`
→ any finite exceptional-pole / finitely supported polar repair
→ **contradiction with full positive Hardy-divisor inheritance**.

This kills every T2 continuation model whose singular correction has finite support.  It does not
kill an infinite unsplit zeta-divisor mechanism, which remains the exact survivor.

## Internal frontier

Required `scripts/formal_tools.py research` audits found:

- unconditional safe natural-Abel identity
  `abelDirichlet_woldNatDifferenceCoeff_eq_wold_sub_mesh`;
- sector identity theorem
  `xiHeatCassiniWoldZetaClearedContinuation_eq_mul_naturalAbel_on_sector`;
- exact residue at every critical-line zero
  `xiHeatCassiniWoldCriticalLaplaceContinuation_zero_residue`;
- isolated zeta zeros
  `eventually_riemannZeta_ne_zero_nhdsNE`;
- Hardy dyadic occurrence
  `exists_riemannZeta_line_zero_dyadic`;
- stronger quantitative critical-line censuses, including
  `exists_many_distinct_line_zeros_dyadic_twoSeventh`.

Corpus currently quantifies over every continuation at one Hardy zero, and over every zero for the
canonical Wold continuation.  It does not quantify over every continuation at every positive
critical-line zero, nor rule out finite radial singular support of the literal natural Abel germ.

## External frontier through 2026-08-30

- `[LITERATURE]` Hardy's theorem gives infinitely many zeta zeros on the critical line; later
  Hardy--Littlewood work gives quantitative lower bounds.
- `[LITERATURE]` Fröberg, *On the prime zeta function*, BIT 8 (1968), 187–202,
  https://doi.org/10.1007/BF01933420, studies prime-zeta continuation and its zeta-zero singularities.
- `[LITERATURE]` Classical logarithmic-derivative theory gives residue equal to zero multiplicity.

Exact-object searches found no natural-cutoff Wold finite-difference Abel germ, no universal
continuation theorem for it, and no finite-radial-singular-support classification.  Novelty claim is
the representation-level inheritance theorem, not Hardy's theorem or the logarithmic-derivative
residue law.

## Hostile conjecture audit

- **Rediscovery attack:** prime-zeta and log-derivative singularities are classical, but they do not
  identify this literal natural Abel germ or quantify over all its continuations.
- **Circularity attack:** no RH hypothesis enters; only unconditional on-line zeros are used.
- **Finite-repair attack:** choosing a Hardy zero above `max S` defeats every finite exceptional set.
- **Cancellation attack:** the integer mesh is holomorphic at each nonreal wall point, so it has
  zero radial residue and cannot cancel the Wold pole.
- **Identity attack:** zeta-clearing identifies any continuation with the canonical Wold germ off
  the isolated zero, throughout one connected upper sector.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## Proof plan

1. Fix arbitrary positive critical-line zero `rho` and admissible continuation `F`.
2. Reuse the global sector identity `Wclear = ζ(s+1)(F+M)`.
3. Along `s=rho-1+x`, isolatedness permits cancellation of `ζ(rho+x)` for all sufficiently small
   `x>0`; hence `F+M=WoldCriticalContinuation` there.
4. Canonical residue is `-m`, `m≥1`; mesh regularity contributes zero after multiplication by `x`.
5. Therefore `xF→-m`, at every chosen `rho`.
6. For finite exceptional set `S`, choose a Hardy dyadic window starting strictly above every member
   of `S`.  Its on-line zero has ordinate `tau∉S`.  Finite-support regularity gives a finite radial
   limit at `tau`, forcing `xF→0`, contradicting `-m≠0`.

## No-go closure target

- **Killing theorem:** no admissible continuation has finite radial singular support.
- **Strongest positive survivor:** exact full positive Hardy-divisor inheritance with quantized
  residue `-m(rho)`.
- **New insight:** singularity is not one removable accident; literal natural Abel representation
  carries an infinite arithmetic divisor under every analytic continuation.
- **Status:** `[LEAN-PROVED]`; full-divisor classification and finite-support branch kill verified.

## Log

- 2026-08-30 — created after prior one-pole theorem exposed full-divisor strengthening.

## Proof

**[PROVED HERE]** Fix `rho` and `F` as in the statement and put `s₀=rho-1`.  The previously proved
sector identity gives

`Wclear(s)=ζ(s+1)(F(s)+M(s))`

throughout `U`.  Independently, whenever `ζ(s+1)≠0`, the canonical cleared identity gives

`Wclear(s)=ζ(s+1)Wcritical(s)`.

Because `0<Re rho=1/2<1`, the zero of zeta at `rho` is isolated.  Therefore
`ζ(rho+x)≠0` for all sufficiently small `x>0`.  Since `Im rho>0` and
`Re(s₀+x)=-1/2+x>-1/2`, these radial points lie in `U`.  Canceling the common nonzero zeta factor
there gives

`Wcritical(s₀+x)=F(s₀+x)+M(s₀+x)`.

The canonical critical-Wold residue theorem supplies `m∈ℕ`, `m≥1`, with

`x Wcritical(s₀+x)→-m`.

Also `Re s₀=-1/2>-1` and `s₀≠0` because `Im s₀=Im rho>0`.  Thus `M` is differentiable at `s₀`,
so `M(s₀+x)` has a finite limit and `xM(s₀+x)→0`.  Subtracting from the preceding radial identity
proves

`xF(s₀+x)→-m`.

This proves the residue statement for every positive critical-line zero and every admissible `F`.

Now suppose one admissible `F` had finite radial singular support `S`.  Hardy's dyadic theorem gives
`T₀>0` such that every `[T,2T]`, `T≥T₀`, contains an ordinate of a critical-line zero.  Choose

`T = T₀ + 1 + ∑_{u∈S}|u|`.

Then every `u∈S` satisfies `u<T`, while Hardy supplies `tau≥T` with
`ζ(1/2+i tau)=0`; hence `tau∉S` and `tau>0`.  Finite-support regularity yields a finite radial limit
`F((linePt tau-1)+x)→L`, so multiplication by `x→0` gives residue zero.  The all-zero theorem gives
residue `-m` with `m≥1`.  Uniqueness of limits forces `m=0`, contradiction.

No additional analytic, arithmetic, or RH premise is used.  The proof is dependency-closed.

- 2026-08-30 — promoted to Stage 2 after full-divisor and finite-support proofs closed.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelFullCriticalDivisor`
- Singular-support definition: `WoldNatAbelFiniteRadialSingularSupport`
- Full-divisor theorem:
  `woldNatAbelContinuation_forced_residue_at_criticalLine_zero`
- Finite-support branch kill: `not_woldNatAbelFiniteRadialSingularSupport`
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/XiHeatCassiniWoldNaturalAbelFullCriticalDivisor.lean`
  passed with no warnings.
- Final audit:
  `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelFullCriticalDivisor` passed.
- Axiom audit: only Lean foundations `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- Forbidden-declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Umbrella: imported by `GaloisForLFunctions/RHTower.lean`.

## Final no-go closure

- **Exact killing theorem/mechanism:** `not_woldNatAbelFiniteRadialSingularSupport`; Hardy supplies a
  critical zero above every finite exceptional set, while full-divisor inheritance forces nonzero
  residue there.
- **Strongest positive survivor:** every admissible continuation carries the complete positive
  critical-line zeta divisor with exact residue `-m(rho)`.
- **New insight:** T2 cannot repair its natural Abel representation with finitely supported polar
  data.  Any surviving continuation must encode an infinite coefficient-faithful
  divisor before terminal extraction.
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`, provisional pending independent
  expert proof and priority review.  Exact-object internal and external searches found no predecessor.

- 2026-08-30 — promoted to Stage 3; finite-singularity continuation branch of T2 retired.
