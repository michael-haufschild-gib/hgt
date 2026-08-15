# Route P Ward--Herglotz aperture tangent

- **ID:** `route-p-primitive-burnol-ward-herglotz-tangent`
- **Stage:** 3-formalized
- **Type:** POSITIVE STRUCTURE THEOREM
- **Label:** `P-G197`
- **Source:** P-G196 aperture anomaly, Gamma-sewn Xi Ward transport, finite-packet Schur/Pick
  nonexpansivity, strict-right Schwarz-pair response
- **Statement:** The first aperture jet of the actual strict-right Xi Schur defect is a positive
  Herglotz matrix on every finite right-half-plane packet. Each strict-right zero mode splits
  exactly into a resolved rank-one zero channel plus a positive Hardy dressing; hence the two
  resolved columns of every actual Schwarz pair are Loewner-dominated by its Herglotz tangent.

## Conjecture loop

The first P-G197 candidate was a Gram congruence after assuming a landing operator. That was
rejected as theatre: positivity under an assumed landing would add no producer and no new control.

`C197-B` instead differentiated the already-proved finite-aperture Xi Schur/Pick defect at closed
aperture. If `R(w)` is the continued anti-causal Ward response, Lean proves entrywise

```text
a^-1 (1-S_a(w_i) conjugate(S_a(w_j))) / (w_i+conjugate(w_j))
  -> (R(w_i)+conjugate(R(w_j))) / (w_i+conjugate(w_j)).
```

Every finite-aperture matrix on the left is positive semidefinite for `a>0`; closure of the PSD
cone makes the limiting Ward--Herglotz kernel positive semidefinite. This turns P-G196's required
rate-changing anomaly into an actual positive first-order defect channel.

## Exact zero-mode factorization

For a centered strict-right zero `lambda` and packet `w`, define

```text
H_lambda(i,j)
  = (2/(w_i+lambda) + conjugate(2/(w_j+lambda)))
      / (w_i+conjugate(w_j)).
```

The formal identity is

```text
H_lambda
  = 2 C_lambda C_lambda^*
    + 4 Re(lambda) D_lambda K_Hardy D_lambda^*,
```

where `C_lambda(i)=1/(w_i+lambda)`, `D_lambda` is its diagonal matrix, and `K_Hardy` is the
right-half-plane Cauchy Gram. Both summands are positive semidefinite. Summing the two conjugate
zero modes of an actual Schwarz pair gives

```text
H_pair - 2 C_lambda C_lambda^* - 2 C_lambdabar C_lambdabar^* >= 0.
```

Thus literal resolved zero channels occur as positive summands of the actual Xi aperture tangent;
they are not postulated outputs of a hypothetical boundary map.

## Higher principle and next conjecture

P-G195/P-G196 showed any successful source-to-Xi landing must change exponential type through a
noncommuting aperture anomaly. P-G197 shows the actual anomaly is constrained by complete
positivity: its first jet is a Herglotz/Pick kernel and its resolved zero content admits a positive
Hardy dilation. Rate change therefore lives inside a positive defect geometry, not outside it.

The next hard conjecture was coefficient-faithful source domination after polarization across
zero labels. P-G198 performs the crucial audit and falsifies that direct amplification: the
natural two-mode polarization has a strict negative-square determinant unless the modes coincide.
The surviving route keeps resolved modes as separate columns in one common carrier and applies a
source-controlled generator before forming their cross-zero cubic Gram.

## Hostile novelty audit

Corpus already contained scalar first-aperture defect quantization, finite-aperture matrix
nonexpansivity, and the one-factor Cayley/Hardy identity. It did not contain the finite-packet
first-jet limit, positivity of its Herglotz matrix, the exact resolved-plus-dressing mode
factorization at tangent level, or Schwarz-pair resolved-Gram domination. No landing premise, RH
premise, boundedness premise, or new axiom occurs.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/RoutePPrimitiveBurnolWardHerglotzTangent.lean
```

Capstones:

- `tendsto_xiWardPhasePickDefect_div_aperture`;
- `continuedXiWardHerglotzPickMatrix_posSemidef`;
- `xiWardModeHerglotzPickMatrix_factorization`;
- `xiWardSchwarzPairResolvedGram_le_herglotzPick`.

Verification:

- `/tmp/pg197.lean`: `lake env lean /tmp/pg197.lean` passed cleanly;
- repository source check passed cleanly;
- exact leaf build passed; no umbrella/full build run;
- `/tmp/pg197_audit.lean`: capstones depend only on `propext`, `Classical.choice`, `Quot.sound`;
- forbidden-declaration scan clean;
- umbrella import wired without building umbrella.

## Gates

- [x] first aperture jet identified entrywise
- [x] complete finite-packet positivity proved
- [x] exact one-mode resolved-plus-Hardy factorization proved
- [x] actual Schwarz-pair resolved-Gram domination proved
- [x] scratch verification and exact leaf build only
- [x] axiom and forbidden-declaration audit
- [x] umbrella wired without umbrella build
- [x] audit cross-mode polarization (falsified and classified by P-G198)
- [x] identify common generator graph norm carrying cubic conormal charge (P-G199)
- [ ] prove coefficient-faithful primitive-source domination
- [ ] instantiate W-H184 and prove unconditional RH
