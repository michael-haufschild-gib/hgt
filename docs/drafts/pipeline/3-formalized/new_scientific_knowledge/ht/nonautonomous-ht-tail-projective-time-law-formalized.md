# Nonautonomous HT tails form a projective local system over time — formalized

- **ID:** `nonautonomous-ht-tail-projective-time-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `nonautonomous-ht-tail-projective-time-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/HTGeometry/NonautonomousStableCore.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousTailDichotomy.lean
formal/GaloisForLFunctions/HTGeometry/DifferentialLurothSingleGenerator.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousTailGenerator.lean
formal/GaloisForLFunctions/HTGeometry/JetHypertranscendence.lean
formal/GaloisForLFunctions/HTGeometry/FreeDifferentialFieldPresentation.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousTailHypertranscendence.lean
formal/GaloisForLFunctions/HTGeometry/MutualGeneratorMobius.lean
formal/GaloisForLFunctions/HTGeometry/SchwarzianProjectiveInvariant.lean
formal/GaloisForLFunctions/HTGeometry/NonautonomousProjectiveTimeLaw.lean
formal/GaloisForLFunctions/HTGeometry/FreeDifferentialProtocolTimeLaw.lean
```

## Formal theorem chain

```text
 1  nonautonomousTail                              the phase tail                              (1)
 2  map_nonautonomousTail_eq                       exact phase transport φ_i(T_(i+1)) = T_i    (2)
 3  derivationClosed_nonautonomousTail             each tail is a differential field           (1)
 4  nonautonomousTail_dichotomy                    all tails trivial, or none
 5  differentialLuroth                             Ritt's differential Lüroth theorem
 6  exists_nonautonomousTail_generator             a nontrivial tail is C⟨u⟩
 7  differentialJetEval, differentialJetFieldEval  jet evaluation at a free generator
 8  jetPolyEval_jetDeriv                           it intertwines the derivations on polynomials
 9  jetFieldEval_deriv                             and on fractions
10  jetFieldEval_surjective                        it is onto a differentially generated field
11  hypertranscendentalOver_of_notMem_bot_of_free  every nonconstant element of a free scalar
                                                   differential field is hypertranscendental
12  exists_nonautonomousTail_hypertranscendental_generator
                                                   T_i = C⟨u_i⟩ with u_i differentially
                                                   transcendental                              (3)
13  hasScalarDifferentialOrder_zero_of_mutual      mutual differential generation is order zero
14  mutual_generator_mobius                        two generators of one field are
                                                   fractional-linear in each other
15  mobius_coefficients_unique                     the coefficient matrix is unique up to a
                                                   scalar — uniqueness in PGL₂(C)              (4)
16  map_differentialAdjoin                         a differential hom maps C⟨S⟩ to C⟨φS⟩
17  differentialAdjoin_map_generator               φ_i(u_(i+1)) generates T_i
18  nonautonomousTail_projective_transition        φ_i(u_(i+1)) = (a u_i + b)/(c u_i + d)      (4)
19  schwarzian, schwarzian_mobius                  the Schwarzian and its Möbius invariance    (5)
20  schwarzian_eq_of_differentialAdjoin_eq         S(u) does not depend on the generator       (5)
21  schwarzian_ne_constant_of_hypertranscendentalOver,
    schwarzian_generator_ne_constant               S(u_i) is never a base constant             (5)
22  schwarzian_transport_of_projective_transition,
    nonautonomousTail_schwarzian_transport         φ_i(S(u_(i+1))) = S(u_i)                    (6)
23  differentialAdjoin_jet_zero_eq_top             the free generator generates JetField C Unit
24  deriv_algebraMap_jetField                      the base of JetField C Unit is constants
25  differentialIndependent_jet_zero               the free generator is differentially independent
26  freeDifferentialProtocol_projective_time_law   (1)–(6) in one unconditional theorem
```

## The unconditional capstone

```lean
theorem freeDifferentialProtocol_projective_time_law
    {C : Type*} [Field C] [CharZero C]
    (φ : ℕ → JetField C Unit →ₐ[C] JetField C Unit)
    (hφ : ∀ i x, φ i x′ = (φ i x)′) :
    (∀ i, IntermediateField.map (φ i) (nonautonomousTail φ (i + 1)) = nonautonomousTail φ i) ∧
      ((∀ i, nonautonomousTail φ i = ⊥) ∨
        ∃ u : ℕ → JetField C Unit,
          (∀ i, HypertranscendentalOver C (u i)) ∧
          (∀ i, differentialAdjoin C ({u i} : Set (JetField C Unit)) = nonautonomousTail φ i) ∧
          (∀ i, ∃ a b c d : C, a * d - b * c ≠ 0 ∧ …) ∧
          (∀ i, ∀ a b c d a' b' c' d' : C, … → ∃ t : C, t ≠ 0 ∧ …) ∧
          (∀ i, φ i (schwarzian (u (i + 1))) = schwarzian (u i)) ∧
          (∀ i, ∀ t : C, schwarzian (u i) ≠ algebraMap C (JetField C Unit) t))
```

There is no structural hypothesis: the ambient differential field is *constructed* as the free
differential rational field on one generator, and the facts that its base is a field of constants,
that the generator is differentially independent, and that its jets generate everything are proved
in the same module (`23`, `24`, `25`), not assumed.  The only inputs are the protocol `φ` and the
statement that it commutes with the derivation, which is the definition of a differential protocol.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/FreeDifferentialFieldPresentation.lean   -- clean
lake env lean GaloisForLFunctions/HTGeometry/NonautonomousTailHypertranscendence.lean -- clean
lake env lean GaloisForLFunctions/HTGeometry/MutualGeneratorMobius.lean               -- clean
lake env lean GaloisForLFunctions/HTGeometry/NonautonomousProjectiveTimeLaw.lean      -- clean
lake env lean GaloisForLFunctions/HTGeometry/FreeDifferentialProtocolTimeLaw.lean     -- clean
lake build GaloisForLFunctions.HTGeometry                                             -- success
```

Every declaration named above reports `[propext, Classical.choice, Quot.sound]` under
`#print axioms`.  All five new modules are wired into `GaloisForLFunctions.HTGeometry`, and the
whole area umbrella builds with no error and no new warning.
