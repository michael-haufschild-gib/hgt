# The successor-visible dilation spectrum is absolutely continuous

- **ID:** successor-visible-spectrum-is-absolutely-continuous
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ArithmeticPositiveDuality README, open topic 6; prescribed successor coordinates
- **Statement:** A finite archimedean dilation measure admits a nonblind positive-definite affine extension exactly when its absolutely continuous part is nonzero.

## Goal

Resolve the stated singular-continuous spectrum question by a positive
classification, including realization of every nonzero absolutely continuous
part. The existing atomic blindness theorem and compactly supported
autocorrelation examples leave this distinction open.

Let ν be a finite positive measure on ℝ and let φ be positive definite on
Aff(ℚ), with positive-slope dilation coefficient
`φ(dilation u) = ∫ exp(i γ log u) dν(γ)`.
The proposed quantitative classification is

`|φ(translation b) − φ(translation b')| ≤ 2 ν_ac(ℝ)` for nonzero b,b',

where ν_ac is the Lebesgue absolutely continuous part. In the reverse
direction, every ν with nonzero ν_ac should have such an extension whose
successor coefficient is nonconstant away from zero. Prove the decomposition
underlying the bound; do not insert it as a premise or count blindness alone.

## Gates

- [x] Concrete open question and existing exact interfaces located and read.
- [ ] Corpus novelty audit of regularization and affine spectral decomposition.
- [ ] Dependency-closed paper proof of necessity and positive realization.
- [ ] Exact Lean formalization, individual source checks, transitive axiom audit.
- [ ] Significance audit against the stated APD frontier.

## Existing inputs

`TheSuccessorOscillationIsBoundedByTheContinuousDilationMass` bounds the
oscillation by twice the nonatomic mass and proves atomic blindness.
`AContinuousArchimedeanSpectrumIsSeenByTheSuccessor` constructs nonblind
extensions for autocorrelations of nonzero continuous compactly supported H.
`TheSuccessorSeesOnlyTheContinuousDilationSpectrum` supplies the affine GNS
representation, its dilation spectral norm identity, and finite-atom splitting.
The integer-successor Kronecker-null theorem concerns a different restriction;
it must not be presented as a solution of the singular-continuous question.

## Approach and unresolved dependencies

The dilation-cyclic subspace has a strongly continuous real dilation action
because its coefficients are Fourier transforms of finite measures on ℝ.
Affine conjugation expresses a coefficient at nonzero translation b using
two dilation-orbit vectors and the fixed operators at translations ±1.
This gives continuity off b=0, but does not make the full representation
continuous. That distinction is essential.

Conjectural decomposition: project onto vectors with continuous translation
orbits. The projection commutes with rational affine operations. Its
translation-invariant subspace is blind; its nontrivial translation spectrum
should have absolutely continuous dilation spectrum. The remaining component
should contribute only at translation zero. These assertions still require
proof: neither a real-affine representation theorem nor a regularization
decomposition is currently available as a checked input.

For sufficiency, write dν_ac = w dγ, take an L² inverse Fourier transform of
√w, and extend the existing real-affine vector-state construction from C_c
to L². Its successor is the Fourier transform of a nonzero positive measure
on positive translation frequencies and is nonconstant. Add a blind affine
state carrying ν−ν_ac, using extension from the dilation subgroup. This
would realize exactly the prescribed ν rather than only a dense family.

## No-go closure

Not retired. If the proposed decomposition fails, identify a concrete
singular-continuous nonblind extension and formalize its positive realization.
No contribution is credited while either direction remains conjectural.
