# Normalized residue modes are total in c₀

- **ID:** normalized-residue-mode-completeness
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** BVI README §5 damping-chain frontier; THIM–BVI programme candidate 002.
- **Statement:** For `v_d(n)=floor((n+1)/d)/(n+1)−1/d`, the span of `v_d`, d≥2,
  is dense in `C₀(ℕ,ℝ)` with its uniform norm. An ℓ¹ row annihilates all these modes
  exactly when it is zero.

## Goal and significance

The finite damping transition already has floor eigenprofiles. What was missing was proof
that their centered, vanishing-at-infinity versions detect every continuous functional on
the infinite state space. This supplies that completeness theorem, not merely a finite
triangular identity or another eigenvector formula. It allows bounded operators and strong
limits on c₀ to be determined on the arithmetic modes. The actual damping-semigroup
application and its infinitesimal generator remain on programme candidate 002; they are not
claimed Lean-certified here and will not receive extra credit merely for applying this tool.

No Schauder-basis property, uniform bound on spectral projections, critical pronic operator
bound, or RH conclusion is asserted.

## Gates

- [x] 0 → 1: exact literal residue profiles; source-pure arithmetic inversion mechanism.
- [x] 1 → 2: complete paper proof below, without analytic cancellation assumptions.
- [x] 2 → 3: final leaf audit and transitive axiom audit passed; umbrella import added.
- [ ] 3 → 4: standalone publication treatment.

## Paper proof [PROVED HERE]

Use positive states x=n+1. The division identity gives
`v_d(x)=−(x mod d)/(dx)` and `|v_d(x)|≤1/x`, so every v_d lies in c₀.
The profiles for d=0,1 are zero and do not change the span.

Let a∈ℓ¹ annihilate the profiles for d≥2. Multiplying the pairing by d gives
`Σ_x a_x d floor(x/d)/x=Σ_x a_x`. The factors `d floor(x/d)/x` lie in [0,1]
and tend pointwise to zero as d→∞. Dominated convergence yields `Σ a_x=0`, hence
`F_d:=Σ_x (a_x/x) floor(x/d)=0` for every d≥1.

For K,m≥0 set `S_K(m)=Σ_{k=1}^K μ(k) floor(m/k)`. If K≥m then Möbius floor
inversion gives `S_K(m)=1` for m≥1 and zero for m=0. If K<m, splitting each floor
into its quotient minus fractional part, using `|μ(k)|≤1` and the unconditional
corpus bound `|Σ_{k≤K} μ(k)/k|≤1`, gives `|S_K(m)|≤m+K≤2m`. Thus `2m` is a
uniform majorant for every K,m, including zero.

Fix d≥1. Finite interchange and nested integer division give
`0=Σ_{k≤K} μ(k)F_{dk}=Σ_x (a_x/x) S_K(floor(x/d))`.
The summands are bounded in absolute value by `2|a_x|/d`. Dominated convergence
therefore gives `T_d:=Σ_{x≥d} a_x/x=0`. Subtraction of consecutive tails gives
`a_d/d=T_d−T_{d+1}=0`; hence a=0. All exchanges have summable majorants.

For completeness of the duality step, let f be any continuous real linear functional on c₀
and let a_n=f(e_n), where e_n is the coordinate unit vector. Applying f to finite sign
vectors of uniform norm at most one gives `Σ_{n∈s}|a_n|≤‖f‖` for every finite s.
Thus a∈ℓ¹. Uniform convergence of finite coordinate truncations of b∈c₀ gives
`f(b)=Σ a_n b_n`; this series converges absolutely. A functional annihilating all v_d
therefore vanishes by the arithmetic inversion just proved. If the closed residue span
were proper, Hahn–Banach on its normed quotient would give a nonzero annihilating
functional, a contradiction. The closed span is all c₀.

## Corpus and dependency audit

- Prior finite arithmetic input: `RHTower.moebius_floor_summatory` and
  `RHTower.abs_sum_moebius_div_le_one`, from `RHTower/MoebiusFloorSummatory.lean`.
  Its source and clean dependency chain passed a plain Lean audit.
- Hybrid queries for centered damping, floor-profile completeness, residue annihilators,
  and c₀ duality found no prior completeness theorem. Exact lexical `residue dense`
  returned 54 hits, inspected through offsets 0,20,40; these concern other residue-density
  notions. Later hybrid search reported complete semantic coverage at its measured snapshot.
- This is one contribution. Truncation bounds, coordinate duality, and the annihilator
  equivalence are proof ingredients and companion formulations, not separate credits.

## Lean certificate

Module: `GaloisForLFunctions.BezoutValuationIncidence.ResidueModeCompleteness`.

Capstones:

- `normalizedResidue_annihilator_iff`
- `normalizedResidueMode_dense_span`

Both transitive `#print axioms` reports contain exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or added axiom.
Audit commands were run sequentially in the foreground. Final command, exit 0:

```text
lake --old env lean GaloisForLFunctions/BezoutValuationIncidence/ResidueModeCompleteness.lean
```

The BVI umbrella imports the new module. No full or umbrella build was run, no `-o`/`-i`
was used, and no heartbeat/recursion limit was raised. Generated corpus indexes refreshed.

## Log

- 2026-10-22 — Paper proof, Lean implementation, final audit, axiom audit, and umbrella wiring
  completed. Damping-spectrum import repair remains a separate unresolved integration issue.
