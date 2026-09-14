# FZZ one-sided radial/real-compact Ward obstruction

- **ID:** fzz-one-sided-radial-real-compact-ward-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `FZZCigarMarkedRadialReplicaResponse`; `FZZCigarParityTwoMarkedFullAnnularHessianNoGo`; Halder--Jafferis, arXiv:2402.00932, §3.2.3
- **Statement:** Physical one-sided radial mixed response cannot be cancelled by any real compact response.

## Goal

Kill factorized FZZ-P chain
`one-sided radial receiver + real compact Hessian → Ward zero → zero momentum → passivity → RH`.

## Gates

- [x] 0 → 1  in-progress: corpus identified reflected/paired receiver as nonphysical diagnostic
- [x] 1 → 2  fully-proven: reflection, shift, conjugation, and strict hyperbolic inequality
- [x] 2 → 3  formalized: closed Lean proof; targeted audit recorded below
- [ ] 3 → 4  publication-ready

## Result

For every real `q`, Lean proves `Re ψ′(1+iq)>0`; away from zero it proves the exact identity

`2 Re ψ′(1+iq) = q⁻² - π²/sinh²(πq)`.

Thus the physical radial derivative satisfies

`Im(∂p R) = -(c/e^v) Re ψ′(1+i p/e^v) < 0`

at every momentum. Adding any real compact response cannot produce zero. In particular, the exact
full two-marked annular Hessian cannot cancel it for any physical level or annulus geometry.

## Positive survivor

Any viable all-depth compact completion must carry strictly positive imaginary response. Geometry
or real normalization alone cannot repair the Ward identity; source-fixed cross-charge phase is mandatory.

## Scope

Kills physical one-sided radial plus real compact factorization, not FZZ-P. A genuinely complex
all-depth screening response remains live.

## Novelty audit (through 2026-08)

Corpus search found paired-response zero selection and vertical trigamma imaginary orientation, but
no unit-line real-trigamma positivity theorem or one-sided/real-compact no-go. Primary-literature
search found no matching classification. Halder--Jafferis explicitly exclude the reflected wave and
leave the torus one-point completion open. Claim is limited to this exact factorized response model.

## Lean

- Module: `GaloisForLFunctions.RHTower.FZZCigarOneSidedRadialRealCompactWardNoGo`
- Analytic core: `two_mul_re_deriv_digamma_one_add_mul_I`, `re_deriv_digamma_one_add_mul_I_pos`
- Phase survivor: `compact_im_pos_of_fzzOneSidedRadialMixedResponse_add_eq_zero`
- Route kill: `fzzOneSidedRadialRealCompactWardRouteKilled`
- Audit: direct source check PASS; targeted leaf build PASS; axioms
  `[propext, Classical.choice, Quot.sound]`; formal lint PASS
