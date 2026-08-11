# Route R C33: functorial polar-reduction no-go (2026-08-11)

Active goal remains: close Route R only by verified Lean RH chain or dependency-closed route death.

Paper theorem recorded in `docs/drafts/pipeline/1-in-progress/route-r-prepolar-horizontal-carrier-annihilation.md`, section C33.

Core:
- Pre-polar dual Gamma source is `V=L⊕L∨` with evaluation/Poincare pairing.
- Hyperbolic source automorphisms `T_λ(x,ℓ)=(λx,λ⁻¹ℓ)` preserve duality, orientations, and retained Kummer atom.
- No positive-definite Hermitian metric can be functorially invariant under all `T_λ`: restriction to nonzero `x∈L` gives `h(x,x)=|λ|²h(x,x)`.
- Fixed-target landing dichotomy: a complex-linear natural landing `F` into a trivial-gauge fixed target satisfies `F T_λ=F`, hence erases each sector. Retaining atom requires transported target gauge, which transports metric and supplies no fixed same-fibre comparison.
- Any source-natural strict topology makes `T_λ` homeomorphisms, so closure/domain/quotient/Fredholm/homology predicates are constant along actual orbit `λ_p(a)=p^(2a)`; they cannot select `a=0`.
- Combined with C32 pure-index blindness and existing fixed-ideal/Schatten/tail-Roos walls, last internal Route-R producer trichotomy is: natural→blind/erasing; non-invariant topology→adds missing polar reduction and admission is endpoint; pure index→blind, metric refinement→imports missing metric.
- Strongest survivor is external full-numerical Euler–Gamma polar reduction / Gate-II ultraviolet Hodge or compressed-trace construction. Need terminal scope audit and Lean formalization after corpus refactor.
- No Lean edits/builds performed per user instruction during refactor.
