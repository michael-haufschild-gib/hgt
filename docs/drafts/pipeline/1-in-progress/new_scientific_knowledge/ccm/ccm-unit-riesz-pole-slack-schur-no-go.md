# CCM unit-Riesz pole-slack Schur insufficiency

- **ID:** `ccm-unit-riesz-pole-slack-schur-no-go`
- **Stage:** `1-in-progress/new_scientific_knowledge`
- **Type:** SHARP OPERATOR-COMPLETION NO-GO / MINIMAL-SLOW-MASS LAW
- **Status:** `[PAPER-PROVED] [LEAN-PENDING] [NOVELTY UNVERIFIED] [NO RH CLAIM]`
- **Routes:** `CCM-EP`, `CCM-HG`, `CCM-UR`, `CCM-FU`, `G`, `O`, `CCM-GS`
- **Parent:** `ccm-unit-riesz-hankel-boundary-pulse`
- **Statement:** Exact four-unit pole slack cannot fund any normalized one-channel rank-one
  completion of actual FU--UR fast-minus-slow boundary covariance.

## Goal

Classify a full operator-valued repair family left open by the parent card.  Result must use actual
FU--UR coefficients and actual four-unit pole slack, not an arbitrary positive perturbation.  A
negative result advances CCM-EP only if it leaves exact positive survivor identifying minimal new
source mass.

## Gates

- [x] 0 -> 1: exact source coefficients, closed algebraic attack, corpus absence audit
- [x] 1 -> 2: dependency-closed paper proof below
- [ ] 2 -> 3: unconditional Lean theorem in `CCMUnitRieszPoleSlackSchurNoGo.lean`
- [ ] 3 -> 4: standalone exposition and external novelty audit

## 1. Actual four-unit covariance and available slack

Put

```text
r = exp(-u/2),                 0 < r < 1,
f(y) = exp(-y/2),              g(y) = exp(-y/4).
```

After the corpus four-unit normalization `256/3`, the actual FU--UR output-cutoff covariance is

```text
C_u(y,z) = A_u f(y)f(z) - B_u g(y)g(z),
A_u = 8(1-r^2),                B_u = 4(1-r).              (1)
```

The entire difference between incoming pole trace and normalized scalar curvature pulse is

```text
S_u = 4(1-r)^2.                                             (2)
```

Thus, for every positive aperture,

```text
0 < S_u < B_u,                 B_u-S_u = 4r(1-r) > 0.      (3)
```

## 2. Full normalized one-channel repair class

Every real rank-one channel in the two-dimensional fast/slow span whose slow coordinate is
normalized to one has feature

```text
h_kappa(y) = g(y)-kappa f(y).
```

Give it nonnegative amplitude `delta` and define

```text
C_u^(kappa,delta)(y,z)
  = C_u(y,z) + delta h_kappa(y)h_kappa(z).                  (4)
```

In fast/slow coordinates `(x,y)`, its quadratic form is

```text
Q(x,y) = (A_u+delta kappa^2)x^2
         -2 delta kappa x y + (delta-B_u)y^2.              (5)
```

Equation `(5)` already gives the exact positive survivor:

```text
PSD completion forces delta >= B_u.                        (6)
```

Indeed choose a source vector with vanishing fast coordinate and nonzero slow coordinate.  Such a
vector exists on every two-point sample `{0,L}`, `L>0`: coefficients

```text
(c_0,c_1)=(f(L),-1)
```

give `x=c_0 f(0)+c_1 f(L)=0` and
`y=c_0 g(0)+c_1 g(L)=f(L)-g(L) != 0`.  Hence

```text
Q(0,y)=(delta-B_u)y^2.                                     (7)
```

If completion is paid only from available pole slack, `0 <= delta <= S_u`; equations `(3)` and
`(7)` imply `Q(0,y)<0`.  Therefore every member of this full repair class remains indefinite,
independently of `kappa`.

For comparison, full determinant classification is

```text
det coefficient(Q)
  = A_u(delta-B_u)-delta B_u kappa^2.                      (8)
```

When `B_u kappa^2 < A_u`, sharp Schur threshold is

```text
delta_* = A_u B_u/(A_u-B_u kappa^2) >= B_u > S_u;          (9)
```

otherwise no finite nonnegative `delta` repairs the form.  The inequality `delta_*>=B_u` is
strict unless `kappa=0`.

## 3. No-go closure and positive survivor

- **Exact killing theorem:** for every `u,L>0`, every `kappa`, and every
  `delta in [0,S_u]`, the literal two-point completion matrix from `(4)` is not positive
  semidefinite.
- **Strongest positive survivor:** a normalized positive repair must inject at least the full slow
  boundary mass `B_u`, while scalar pole slack supplies only the fraction
  `S_u/B_u=1-exp(-u/2)`.
- **New insight:** missing CCM-EP background cannot be an aperture-local redistribution of unused
  four-unit pole trace inside one fast/slow rank-one channel.  It needs additional completed-source
  slow mass, a higher-rank/nonlocal covariance, or a mechanism outside this reporter span.
- **Status:** paper proof dependency-closed; exact Lean target recorded above.

This is stronger than the parent negative determinant: parent kills bare `C_u`; `(3)--(9)` kill
every normalized one-channel repair that can be paid from all available scalar pole slack.

## 4. Theatre and novelty audit

Internal corpus search was performed before conjecture/proof using `formal_tools.py research` for
the exact combinations “unit Riesz pole slack Schur threshold slow channel completion”, “fast slow
covariance one channel rank one completion”, and “four unit pole slack operator background”.  It
found parent coefficients/slack and generic Suzuki Schur algebra, but no theorem combining them or
the minimal-slow-mass law `(6)`.

Generic rank-one Schur-complement algebra is known and is not claimed as new.  Candidate new
scientific content is source-specific incompatibility `(3)--(9)`: exact CCM pole slack is globally
too small for the entire normalized one-channel fast/slow completion class.  Targeted primary-source
search found no exact unit-Riesz boundary-covariance statement.  No priority claim is made pending
broader expert audit.

Falsifiers:

1. Allowing arbitrary amplitude outside pole budget escapes theorem and is not excluded.
2. Rescaling `h_kappa` without fixing its slow coordinate changes meaning of amplitude; invariant
   statement is required injected slow-coordinate mass `>=B_u`.
3. Higher-rank, nonlocal, or literal prime-frame backgrounds are not excluded.
4. The theorem proves no arithmetic bound and no RH implication.

## Log

- 2026-08-16 — corpus-first absence audit; paper proof completed; Lean target opened.
