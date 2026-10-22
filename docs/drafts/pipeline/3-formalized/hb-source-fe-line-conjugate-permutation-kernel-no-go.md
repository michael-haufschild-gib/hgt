# HB source-FE line-conjugate permutation-kernel no-go

- **ID:** HC54
- **Stage:** 3-formalized
- **Type:** THEOREM / CANONICAL SURVIVOR / NONDEGENERATE-KERNEL NO-GO
- **Source:** HC52 arbitrary-kernel Ward classification; HC53 full reflection-orbit extinction;
  Xi-divisor Schwarz and functional-equation symmetries
- **Statement:** Construct a symmetric, reflection-real, algebraically nondegenerate source-FE Ward
  kernel supported on the critical-line conjugation graph, and prove its packet covariance
  unconditionally.

## Corpus-led conjecture

Let `R(s)=1-s`, `S(s)=conj(s)`, and `J=R*S`, so `J(s)=1-conj(s)`. For literal unit BM source
amplitude `A` and source-FE cocycle

```text
kappa(q) = A(Rq) / conj(A(q))
```

away from source extinction, corpus formulas predict

```text
A(Sq) = conj(A(q)),
A(Jq) = conj(A(Rq)),
kappa(Sq) = conj(kappa(q)),
kappa(Jq) = kappa(q)^(-1).
```

The wall case has `A=0` and normalized `kappa=1`, so the reciprocal identity should hold globally.

Define the critical-line-conjugate permutation kernel

```text
K_J(q,r) = 1 if r=Jq, else 0.
```

Because `J` commutes with `R`, this kernel is reflection-real. On its support,
`kappa(q)kappa(r)=1`, so HC52's Ward law holds. Since `J` is an involution, `K_J` is symmetric and
the associated finite-packet form is algebraically nondegenerate: testing against the basis vector
at `Jq` reads the coefficient at `q`.

## Predicted consequences

1. `kappa(Jq) kappa(q)=1` for every actual Xi copy.
2. `K_J` is symmetric, reflection-real, and satisfies the arbitrary-kernel Ward equation.
3. Its packet form is source-FE covariant for every pair of finite packets without RH.
4. Both left and right radicals are zero.
5. At every tilted copy, `Jq` lies outside the two-point FE orbit `{q,Rq}`; hence the kernel obeys
   HC53's full orbit-block extinction while remaining globally nondegenerate.

If proved, this is a sharp no-go: symmetry, reflection reality, and even global algebraic
nondegeneracy of an arbitrary fixed Peierls kernel cannot select RH. The positive survivor is one
canonical cross-orbit pairing forced by the full FE--Schwarz quartet. Remaining HB producer must
select the literal local/diagonal physical pairing, not merely some nondegenerate fixed form.

## Hostile checks

- Treat source extinction separately; never divide by the wall source.
- Prove source Schwarz laws from literal carrier and helicity formulas, not a postulated cocycle.
- Prove copy-level `R`/`S`/`J` commutation including multiplicity indices.
- Establish radical triviality on arbitrary finite packets, not only rowwise nonzero entries.
- Show `Jq != Rq` using the unconditional nonzero Xi height theorem.
- Do not infer RH or assume an off-line zero exists.
- Final Lean theorems must be closed and axiom-audited.

## Novelty boundary as of 2026-08-28

Required corpus searches found FE cocycle involutivity, arbitrary-kernel Ward classification,
FE--Schwarz orbit traces, and Deninger Schwarz monodromy, but no reciprocal source-cocycle law on
the `J` graph and no nondegenerate permutation-kernel construction. Targeted primary-literature
search found reflection-based conserved QNM bilinear forms (Green--Hollands--Sberna--Toomani--
Zimmerman, arXiv:2210.15935) and nonlinear QNM coupling work, but no Xi-source-cocycle
permutation-kernel classification. Search is bounded, not exhaustive.

## Formal result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFELineConjPermutationKernelNoGo`.
Lean proves:

1. functional-equation reflection and Schwarz conjugation commute on multiplicity-exact Xi copies;
2. literal helicity factor, unit carrier, and complete BM unit source obey their exact Schwarz laws;
3. `kappa(Sq)=conj(kappa(q))` and `kappa(Jq)kappa(q)=1`, including source extinction;
4. `K_J` has exact graph support, is symmetric and reflection-real, and satisfies the HC52 Ward law;
5. its finite-packet form is unconditionally source-FE covariant;
6. basis testing at `Jq` reads the coefficient at `q`, so both finite-packet radicals are zero; and
7. on every tilted copy `Jq` is neither `q` nor `Rq`, while HC53's entire within-orbit `2 x 2`
   block still vanishes.

This realizes HC53's surviving distinct-orbit mechanism exactly. Algebraic nondegeneracy,
symmetry, and reflection reality of an arbitrary fixed kernel are insufficient RH producers.
Remaining source theorem must distinguish the literal local/diagonal physical Peierls form from
this canonical nonlocal FE--Schwarz permutation form.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: source symmetry and radical/nondegeneracy paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC53 proved every tilted within-orbit `2 x 2` block vanishes; tested
  surviving distinct-orbit support against full FE--Schwarz quartet and found canonical candidate
  `r=1-conj(q)`.
- 2026-08-28 — Proved literal source Schwarz reality, reciprocal line-conjugate cocycle law, exact
  permutation-kernel Ward covariance, symmetric support, and zero left/right radicals in Lean.
- 2026-08-28 — Direct `lake env lean` and target-only `lake build` passed (`11922/11922`). All 21
  public theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint
  reports no HC54 failure; remaining errors are unrelated pre-existing umbrella reachability gaps.
