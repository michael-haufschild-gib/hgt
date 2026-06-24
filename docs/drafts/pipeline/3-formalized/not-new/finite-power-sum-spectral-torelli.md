# Finite power-sum spectral Torelli

- **ID:** finite-power-sum-spectral-torelli
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean certificate split from `../2-fully-proven/lean-claim-review-row-083-spectral-torelli-finite.md`)
- **Owner:** Leaner
- **Lean files:** `formal/GaloisForLFunctions/PowerSumTorelli.lean`; `formal/GaloisForLFunctions/SpectralTorelli.lean`

## Statement

For finite zero configurations `f g : Fin n -> ℂ`, equality of the first `n` secular power sums determines
the multiset of zero values:

```lean
theorem powerSum_torelli_finite (f g : Fin n -> ℂ)
    (hp : ∀ k, k ≤ n -> (Finset.univ.val.map (fun i => f i ^ k)).sum
                      = (Finset.univ.val.map (fun i => g i ^ k)).sum) :
    Finset.univ.val.map f = Finset.univ.val.map g
```

Equivalently, distinct finite configurations are separated by a secular moment of order `≤ n`:

```lean
theorem exists_powerSum_ne_of_ne (f g : Fin n -> ℂ)
    (h : Finset.univ.val.map f ≠ Finset.univ.val.map g) :
    ∃ k, k ≤ n ∧ (Finset.univ.val.map (fun i => f i ^ k)).sum
                 ≠ (Finset.univ.val.map (fun i => g i ^ k)).sum
```

The spectral-polynomial form is:

```lean
theorem spectralTorelli_faithful (s t : Multiset ℂ)
    (h : (s.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      (t.map (fun a => Polynomial.X - Polynomial.C a)).prod) :
    s = t
```

This is the finite faithfulness statement only. It does not formalize the image problem for genuine `xi` zero
sets, infinite reconstruction, RH, DSS, or period-realization constraints.

## Paper Proof

Newton identities in characteristic zero recover the elementary symmetric functions `e_k` from the power sums
`p_k = sum_i f(i)^k`, for `k ≤ n`. Equal first `n` power sums therefore give equal elementary symmetric
functions. Vieta's formula identifies those elementary symmetric functions with the coefficients of the monic
spectral polynomial `prod_i (X - f(i))`. Equal monic spectral polynomials have the same multiset of roots, so
the finite zero multisets agree. The contrapositive gives the separating-moment form.

The direct polynomial form uses the same final step: the inverse of the map
`s ↦ (s.map (fun a => X - C a)).prod` is `Polynomial.roots` on these split monic products.

## Lean Certificate

Verified by scratch file on 2026-06-19:

```lean
#check GaloisForLFunctions.esymm_eq_of_powerSum_eq
#check GaloisForLFunctions.powerSum_torelli
#check GaloisForLFunctions.esymm_eq_of_powerSum_eq_le
#check GaloisForLFunctions.powerSum_torelli_finite
#check GaloisForLFunctions.exists_powerSum_ne_of_ne
#check GaloisForLFunctions.spectralTorelli_faithful
#check GaloisForLFunctions.spectralPoly_coeff_zero
#check GaloisForLFunctions.selfDual_spectralPoly_coeff_real
```

`#print axioms` for `powerSum_torelli_finite`, `exists_powerSum_ne_of_ne`,
`spectralTorelli_faithful`, and `selfDual_spectralPoly_coeff_real` reports only
`[propext, Classical.choice, Quot.sound]`. These theorems are included in `scripts/check_axioms.sh`.

## Gates

- [x] 0 -> 1 in-progress: finite Torelli faithfulness isolated from the full inverse problem.
- [x] 1 -> 2 fully-proven: Newton identities + Vieta + roots of split monic products.
- [x] 2 -> 3 formalized: Lean theorems listed above; scratch `#check` and `#print axioms` passed; audited by
  `scripts/check_axioms.sh`.
- [ ] 3 -> 4 publication-ready: standalone proof note plus Lean certificate.

## Log

- 2026-06-19 — Leaner certified the exact finite spectral Torelli row #83 claim in Lean. The certificate covers
  finite faithfulness only, matching the audited paper scope.
