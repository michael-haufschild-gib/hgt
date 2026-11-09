# Finite-energy arithmetic rigidity annihilates the defect

- **ID:** euler-fe-finite-energy-defect-annihilation
- **Stage:** 3-formalized
- **Programme:** Euler–FE transport theory.

## Statement

In the finite-energy Beurling theta class, the uncompleted defect is zero almost
everywhere. Thus the classification determines the defect itself as well as the
prime system. The actual Hamburger Laplace transform is injective on `L²`.
In the original Hamburger strip formulation the defect vanishes at every point.

## Proof

For any `g∈L²`, its actual transform is `J_g=ℒψ_g`, where the Mellin source map is
bijective. If `J_g` vanishes on the right half-plane, injectivity of the half-line
Laplace transform gives `ψ_g=0` in `L²(0,∞)`. Source injectivity gives `g=0` in
`L²(ℝ)`, hence almost everywhere for any representative.

The finite-energy arithmetic classification gives the positive-integer counting
measure and pole coefficient `β=½`. Jacobi's theta transformation supplies its
exact zero-defect theta law. Apply the established half-plane Laplace identity
to that exact law and to the original defective law. The measure, dual transform
and pole terms agree, so subtraction gives `J_g(z)=0` for every `Re z>0`.
The preceding injectivity theorem finishes the proof.

For the strip formulation, write `s(t)=½+2it`. Its critical-line identity gives

    Γℝ(s(t))g(t)
      = E(s(t))-E(1-s(t))+β[Γℝ(s(t)-1)-Γℝ(-s(t))].

The right side is continuous: both `E` arguments remain on the closed strip,
and both shifted Gamma arguments have real part `-½`, avoiding all Gamma poles.
It vanishes almost everywhere, so full support of Lebesgue measure makes it zero
everywhere. Since `Γℝ(s(t))` is nonzero, `g(t)=0` for every `t`.

## Lean formalization

`FiniteEnergyRigidityAnnihilatesTheDefect.lean`:

- `ae_eq_zero_of_finiteEnergy_defectLaplace_eq_zero`;
- `beurling_finiteEnergy_defect_ae_eq_zero`;
- `beurling_finiteEnergy_strip_defect_eq_zero`.

Direct `lake --old env lean` verification passes. All three declarations have
transitive axiom lists containing only `propext`, `Classical.choice`, and
`Quot.sound`. The module is wired into the programme umbrella.
No height-replication conclusion is claimed.
