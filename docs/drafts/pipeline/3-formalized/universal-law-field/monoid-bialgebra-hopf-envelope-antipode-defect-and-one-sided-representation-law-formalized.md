# Monoid bialgebra, Hopf envelope, antipode defect, one-sided representation — Lean certification

- **ID:** ULF-BIALG-1
- **Paper card:**
  `monoid-bialgebra-hopf-envelope-antipode-defect-and-one-sided-representation-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveMonoidBialgebraHopfEnvelope`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

`MonoidBialg k = AddMonoidAlgebra k ℕ` carries mathlib's **group-like** comultiplication, which is
exactly `Δ(t) = t ⊗ t`, `ε(t) = 1`; `polyEquivMonoidBialg : Polynomial k ≃ₐ[k] MonoidBialg k` sends
`X` to the generator, so the object really is `k[t]` with the card's coproduct (not the additive
one).  `HopfEnv k = LaurentPolynomial k` carries mathlib's Hopf structure.  The operator side is
**reused** from `ConstitutiveToeplitzDefectIndex`: `shiftOp`, `backOp`, `backOp_comp_shiftOp`,
`defectOp`, `range_defectOp`, `finrank_defectSubmodule`, `shiftOp_not_surjective`.

## Certified declarations, by clause

| Clause | Lean |
|---|---|
| 1: `B` is a commutative bialgebra with `Δ(t)=t⊗t`, `ε(t)=1` | `MonoidBialg`, `tGen`, `polyEquivMonoidBialg`, `polyEquivMonoidBialg_X`, `isGroupLikeElem_tGen`, `comul_tGen`, `counit_tGen` |
| 2: no antipode | `not_isUnit_tGen`, `no_antipode`, `isUnit_of_isGroupLikeElem` |
| 3: `H = k[t,t⁻¹]` is Hopf with `S(t)=t⁻¹` | `HopfEnv`, `antipode_T_one`, `isUnit_T_one` |
| 4: universal property of `B ↪ H` | `hopfEnvInclusion`, `hopfEnvInclusion_tGen`, `algHom_ext_tGen`, `algHom_ext_T`, `hopfEnvelope_universal`, `hopfEnvelope_universal_comp`, `hopfEnvelope_extension_isGroupLike` |
| 5: `ℕ → ℤ` group completion | `nat_int_group_completion` |
| 6: `ρ(t) = V` does not extend | `shiftOp_zero`, `shiftOp_comp`, `shiftMonoidHom`, `shiftRep`, `shiftRep_tGen`, `shiftRep_not_extends` |
| 7: boundary quotient makes it unitary and extends | `boundary_representation_extends` |
| 8: erased defect `1 − VV* = P_{e₀}` | `defect_eq_rankOne` |

### Notes on two clauses

**Clause 7** is certified in a form that is strictly stronger than, and independent of, the Calkin
statement: for *any* unital algebra map `φ` out of `B(ℓ²)` with `φ(D₁) = 0`, the images of `V` and
`V*` are two-sided inverses, and the representation extends **uniquely** to the Laurent algebra.  The
Calkin quotient is one such `φ`.  Mathlib has no Calkin algebra — the compact operators appear only
as a submodule, not as a two-sided ideal with a quotient ring — so the theorem is stated for the
general defect-killing quotient rather than constructing that ring.

**Clause 4** is certified at the algebra-map level plus group-likeness of every basis image of the
extension.  In a Hopf algebra the image of a group-like element is a unit (`GroupLike.toUnits`), so
the factorization exists and is unique; `hopfEnvelope_extension_isGroupLike` supplies exactly the
data that makes the extension comultiplicative on the basis.  Mathlib's `BialgHom` packaging of the
extension is not constructed.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveMonoidBialgebraHopfEnvelope.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,431 jobs.  `#print axioms` on the eleven
declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`; the group
completion needs only `propext` and `Quot.sound`.

## Exact field consequence

One comultiplication law produces the directed history (`ℕ`), the reversible one (`ℤ`), the antipode
obstruction, a one-sided positive operator realization, and a boundary quotient where the history
becomes unitary — all from the same generator.  But the Hopf envelope is blind to the *size* of what
is erased: the passage `B ↪ H` forgets a rank-one projection, certified here as
`defect_eq_rankOne`.  The bialgebra alone is therefore not a complete field primitive; the
representation and its completion carry information the envelope does not.
