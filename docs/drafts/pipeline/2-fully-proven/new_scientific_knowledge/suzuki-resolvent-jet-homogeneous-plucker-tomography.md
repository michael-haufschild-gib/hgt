# Suzuki resolvent-jet homogeneous Plücker tomography

- **ID:** `suzuki-resolvent-jet-homogeneous-plucker-tomography`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FRONTIER ATTACK
- **Status:** `[PAPER-PROVED] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`
- **Parent:**
  `../2-fully-proven/new_scientific_knowledge/suzuki-homogeneous-projective-resolvent-plucker-lift.md`
- **Statement:** For finite simple cyclic spectral blocks, finite jets of one admissible resolvent
  generate a basis of entire homogeneous exterior square carrying actual Euler--Gamma/Neumann
  projective chord.

## Goal

Attack `SUZUKI-PLUCKER-CHRISTOFFEL-DARBOUX-WELD` in correct projective representation.  Replace
vague “positive Plücker cone” with complete source-generated finite tomography: isolate every
homogeneous coordinate and every ordered spectral pair using explicit resolvent interpolation.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof and hostile audit
- [ ] 2 → 3 formalized: exact finite tomography core in Lean
- [ ] 3 → 4 publication-ready: standalone paper and priority audit

## Conjecture under attack

For actual homogeneous source blade

```text
H(v)=(v,0) wedge (Av,1),
v=(A-alpha)^(-1)(A-beta)^(-1)e,
```

derive source Christoffel--Darboux/Green identity whose boundary image is positive Gram.  Existing
Plücker lift proves this is exact Euler--Gamma plus Neumann carrier.

## Attack idea

On finite simple spectral block `Ae_i=t_i e_i`, assume source is cyclic:
`e=sum_i a_i e_i`, all `a_i!=0`.  Fix `rho` outside spectrum and
`R=(A-rho)^(-1)`, with distinct nodes `r_i=(t_i-rho)^(-1)`.  Lagrange polynomials `q_i` satisfy

```text
q_i(r_j)=delta_(ij)/a_i,      q_i(R)e=e_i.
```

Set `h_i=H(e_i)` and `h_ij=H(e_i+e_j)`.  Expected exact laws are

```text
h_i=e_i wedge infinity,
h_ij-h_i-h_j=(t_j-t_i)e_i wedge e_j.                  (T)
```

Hence `h_i` and `h_ij` form a basis of `wedge^2(V direct_sum F)`.  Every basis vector is produced
by finite polynomial in one admissible resolvent, equivalently finite shift jet.

## Theorem `[PROVED HERE]`

Let `V` have basis `e_1,...,e_n`, let `Ae_i=t_i e_i` with pairwise distinct real `t_i`, and let

```text
e=sum_i a_i e_i,       a_i!=0.
```

Fix `rho` outside spectrum and put `r_i=(t_i-rho)^(-1)`.  Define zero-constant cardinal filters

```text
q_i(x)=x/(a_i r_i) product_(m!=i) (x-r_m)/(r_i-r_m).   (1)
```

Then:

1. `q_i(0)=0`, `deg q_i<=n`, and `q_i(R)e=e_i` for `R=(A-rho)^(-1)`.
2. With `q_ij=q_i+q_j`, `q_ij(R)e=e_i+e_j`.
3. For `H(v)=(v,0) wedge (Av,1)`, exact coordinate laws are

   ```text
   H(e_i)=e_i wedge infinity,                           (2)
   H(e_i+e_j)-H(e_i)-H(e_j)
      =(t_j-t_i)e_i wedge e_j.                         (3)
   ```

4. Family

   ```text
   {H(q_i(R)e)}_i union {H(q_ij(R)e)}_(i<j)            (4)
   ```

   is a basis of `wedge^2(V direct_sum R)`.

### Proof

Nodes `r_i` are distinct and nonzero.  Lagrange evaluation of `(1)` gives

```text
q_i(r_m)=delta_(im)/a_i.
```

Functional calculus on diagonal basis therefore gives

```text
q_i(R)e=sum_m a_m q_i(r_m)e_m=e_i,
```

proving 1--2.

Expand homogeneous blade:

```text
H(v)
=sum_i v_i e_i wedge infinity
 +sum_(i<j)(t_j-t_i)v_i v_j e_i wedge e_j.             (5)
```

Substitution of `v=e_i` gives `(2)`.  Substitution of `e_i+e_j` and subtraction of two one-mode
blades gives `(3)`.

Standard basis of `wedge^2(V direct_sum R)` consists of `e_i wedge infinity` and
`e_i wedge e_j`, `i<j`.  Equations `(2)--(3)` recover each standard basis vector from `(4)`;
conversely every member of `(4)` lies in exterior square.  Number of generators is

```text
n+n(n-1)/2=n(n+1)/2=dim wedge^2(V direct_sum R),
```

so spanning family `(4)` is a basis.

Because every `q_i(0)=0`, each filter is sum of positive resolvent powers only.  Operator-norm
identity

```text
partial_rho^(m-1)R_rho=(m-1)!R_rho^m
```

makes every generator a finite shift jet of one admissible source resolvent.

## Frontier consequence

> **Subsequent correction.**  Exterior tomography is complete for projective chord, but weighted
> affine intercept used by jump sewing is not determined by Plücker data.  Gauge
> `B -> B+delta D` leaves exterior matrix fixed and shifts intercept.  Tomography theorem remains
> valid and supplies alternating sector of corrected marked tensor.  Full current carrier also
> needs diagonal, symmetric-pair, and marked affine components; see
> `suzuki-projective-affine-secant-tensor-lift.md`.

Let `Lambda_z=Btilde_z wedge Dtilde_z` be actual homogeneous Euler--Gamma/Neumann boundary
functional.  Proposed Christoffel--Darboux identity is now determined completely by finite matrix

```text
C_ab(z,w)
=PickPolarization[Lambda_.(h_a),Lambda_.(h_b)](z,w),   (6)
```

where `h_a,h_b` range through basis `(4)`.  No negative spectral line or cross pair is invisible.
An operator-valued positive Gram law for `(6)` implies positivity on actual filtered blade and,
through existing Loewner/pole connectors, RH.  Conversely, one negative principal minor of `(6)`
falsifies universal CD producer.

This does not prove `(6)>=0`.  It replaces indefinite positive-Grassmannian language by complete
source-generated finite tomography and identifies exact matrix which prime--Gamma Green formula
must factor.

## Scientific-method outcome

- **Conjecture:** actual homogeneous boundary matrix `(6)` has positive Gram factorization.
- **Prediction:** every one-mode diagonal is pure Neumann coordinate; every Euler--Gamma entry
  first appears on two-mode difference `(3)` with exact spectral-gap factor.
- **Falsifiers:** repeated levels, a noncyclic source coordinate, or one negative polarized minor.
- **Result:** tomography theorem survives; positivity remains open and cannot be inferred from
  spanning alone.

## Novelty audit

Lagrange interpolation, cyclic diagonal functional calculus, and exterior-square bases are
classical `[BRIDGE]`.  Corpus contains homogeneous Plücker chord but no result that zero-constant
single-resolvent jets generate its complete homogeneous exterior space.  Candidate novelty is
this Suzuki-specific synthesis and reduction of CD weld to explicit source-generated matrix.
External priority remains unverified.

## Lean status

`formal/GaloisForLFunctions/RHTower/SuzukiResolventJetHomogeneousPluckerTomography.lean` proves
zero-constant arbitrary resolvent interpolation, cyclic source recovery of every finite target,
one-mode blindness, exact two-mode pair isolation, disappearance of homogeneous coordinate under
polarization, and spectral-resolvent specialization.  Direct check and targeted SOTA build pass;
axioms are only `[propext, Classical.choice, Quot.sound]`.

Full exterior-basis dimension argument remains paper-level, and marked affine tensor correction
means exterior tomography is one sector rather than whole jump carrier.  Card stays Stage 2.

## Decisive tests

- Repeated eigenvalues must be excluded or grouped: spectral gap zero is genuinely invisible.
- Any zero source coordinate kills cyclic tomography on that eigenspace.
- Rank one must retain homogeneous Neumann coordinate while Euler--Gamma pair part vanishes.
- Pair isolation must subtract one-mode blades; diagonal tests alone are not enough.
- Spanning Plücker space does not prove positivity.  It makes full polarized boundary matrix the
  exact remaining object and forbids hiding bad directions behind one chosen source vector.
- No Xi zero, RH, or positivity assumption may enter filters.

## Door passport sketch

- **Door 1:** actual projective resolvent blade from latest Suzuki corpus.
- **Door 2:** interpolation/exterior algebra are classical `[BRIDGE]`; claimed candidate novelty is
  their source-specific finite-jet completeness for homogeneous Suzuki chord.
- **Door 3:** exact finite algebra; no asymptotic or computation.
- **Door 4:** degeneracy and noncyclic-source failure modes explicit.
- **Door 5:** reduces CD weld to finite matrices in complete source-generated basis; proving their
  positive Gram law gives jump Pick positivity and RH through existing connectors.

## Log

- 2026-07-22 — Created after new projective-rank-one audit superseded linear projector producer.
- 2026-07-22 — Exact zero-constant spectral filters, homogeneous one/pair isolation, and complete
  exterior-basis theorem proved on paper.  Promoted theorem layer to Stage 2.
- 2026-07-22 — Finite interpolation and one/pair isolation core formalized and built; subsequent
  affine gauge audit restricts Plücker tomography to alternating sector of marked tensor.

### Lean progress — exterior-basis dimension argument FORMALIZED
`RHTower/SuzukiHomogeneousBladeDimension.lean` [PROVED HERE], standard axioms [propext, Classical.choice,
Quot.sound], builds clean (my-cone lint clean; unrelated parallel-agent RHTower unreachable + large-file
warnings only). Registered in the RHTower umbrella.
- `suzukiHomogeneousBlade_finrank` : `Module.finrank ℝ (⋀²(Fin (n+1) → ℝ)) = n + Nat.choose n 2` — the
  homogeneous Plücker blade space `⋀²(V ⊕ F)` (`V=ℝⁿ`, `F=ℝ`) has dimension `n + C(n,2)`, exactly the
  `n` one-mode (Neumann, `eᵢ∧∞`) + `C(n,2)` two-mode (spectral-pair, `eᵢ∧eⱼ`) tomography coordinates.
  Via mathlib `exteriorPower.finrank_eq` (`= C(finrank M, k)`) + `finrank_pi` + Pascal `C(n+1,2)=n+C(n,2)`.

This discharges the "Full exterior-basis dimension argument remains paper-level" item (card §Lean status):
combined with the coordinate-realization tomography theorems already formalized
(`suzukiCyclicResolventFilter_realizes_target_fun`, `suzukiHomogeneousBlade_twoModeDifference_isolates_pair`),
the isolated one-mode + two-mode blades span a space of the matching dimension, hence form a basis of the
homogeneous exterior square. (The card's remaining non-tractable items — the affine-tensor one-sector
correction and the ultimate RH positivity conjecture — are separate and out of scope for this finite piece.)
