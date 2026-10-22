# Negative restricted-Weil spectrum cannot evacuate cofinally

- **ID:** `ccm-negative-spectrum-no-evacuation-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Date:** 2026-08-13
- **Module:** `formal/GaloisForLFunctions/RHTower/CCM/CCMNestedFloorNoEvacuation.lean`
- **Parent theories:** nested Rayleigh quotients and Suzuki's compact generalized eigenvalue
  formulation
- **Statement:** The lowest restricted-Weil floor is nonincreasing with aperture. Once it is
  negative, its negative magnitude stays uniformly bounded away from zero at every larger
  aperture. Hence a cofinal floor limit zero means that negative spectrum never appears.

## Nested-floor theorem

Let

```text
epsilon_0(a)
 =inf{QW(v,v)/||v||_2^2:
      0!=v in H01(-a,a)}.                                      (1)
```

If `0<a<=b`, zero extension embeds `H01(-a,a)` isometrically into `H01(-b,b)` and preserves the
global Weil form. Therefore

```text
epsilon_0(b)<=epsilon_0(a).                                     (2)
```

Consequently, if `epsilon_0(a_0)=-delta<0`, then

```text
epsilon_0(b)<=-delta
for every b>=a_0.                                                (3)
```

Equivalently,

```text
n(a)=max(0,-epsilon_0(a))                                       (4)
```

is nondecreasing. In particular,

```text
epsilon_0(a_j)->0 for some a_j->infinity
 -> epsilon_0(a)>=0 for every a>0.                              (5)
```

The converse implication follows once the known prolate trial vectors give
`limsup_(a->infinity)epsilon_0(a)<=0`.

## Compact-kernel formulation

Suzuki proves that, for `u=Dv` in the zero-mean space,

```text
QW(v,v)=<G_a u,u>,
||v||_2^2=<K_a u,u>,
K_a=(-Delta_N)^(-1)>0.                                         (6)
```

Thus

```text
epsilon_0(a)=inf_(u!=0)<G_a u,u>/<K_a u,u>,                    (7)
```

where both `G_a` and `K_a` are compact operators with continuous kernels. Define the repair
threshold

```text
eta_a=inf{eta>=0:G_a+eta*K_a>=0}.                               (8)
```

Then

```text
eta_a=max(0,-epsilon_0(a)).                                    (9)
```

Equations `(2)`--`(4)` show that `eta_a` is nondecreasing. Therefore

```text
eta_(a_j)->0 cofinally <-> eta_a=0 for every a>0.               (10)
```

There is no nontrivial mechanism in which a genuine negative spectral component shrinks away as
the aperture grows.

## Positive CCM interpretation

The direct CCM route must have the form

```text
G_a>=0 for every finite aperture a,
and prolate near-radical vectors force epsilon_0(a)->0 from above. (11)
```

The first clause is the full Weil positivity content; the second clause explains the logarithmic
boundary layer and the small CCM eigenvalues. Finite determinants and source approximations can
address the second clause but cannot weaken the first.

## Novelty and significance verdict

The theorem is elementary domain monotonicity plus Suzuki's published generalized eigenvalue
identity. It is a route bridge, not new scientific knowledge.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, Sections 3 and 8.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean status

**Superseded, 2026-08-03.**  Every proved theorem of this card is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCM/CCMNestedFloorNoEvacuation.lean`.

The previous decision objected that "an abstract infimum-monotonicity wrapper would not certify the
analytic embedding".  The objection is answered by choosing the right representation: the trial
domains are taken as *subsets of one fixed function space*,

```text
apertureDomain a = {v : ℝ → ℝ | ∀ x, v x ≠ 0 → x ∈ (-a, a)},
```

so zero extension is literal set inclusion (`apertureDomain_mono`) and no embedding argument is
needed at all.  The energy is the two-variable kernel form `diffBilinForm K v v` of
`SuzukiParityHankelDecomposition.lean`, i.e. `QW(v,v)`, and the mass is `sqMass v = ∫ v²`.

- `rayleighQuotientSet`, `rayleighFloor`, `rayleighFloorNegPart` — definition `(1)` and the negative
  magnitude `(4)`.
- **`rayleighFloor_antitone`** — equation `(2)`: a larger trial domain has a smaller floor.
- **`rayleighFloor_le_of_witness`** — equation `(3)`: one trial vector at aperture `a₀` bounds the
  floor at every larger aperture, so `epsilon_0(a_0) = -delta` forces `epsilon_0(b) ≤ -delta`.
- **`rayleighFloorNegPart_mono`** — equation `(4)`: the negative part is nondecreasing.
- `zero_le_rayleighFloor_iff` — the floor is nonnegative exactly when the energy is nonnegative on
  the domain.
- **`zero_le_rayleighFloor_of_tendsto_zero`** — equation `(5)`, the evacuation theorem: if the floor
  tends to zero along *any* apertures tending to infinity, it is nonnegative at every aperture.  A
  negative component, once present, persists with at least its original magnitude.
- `repairSet`, `repairThreshold` — definition `(8)`; **`repairSet_eq_Ici`** and
  **`repairThreshold_eq_negPart`** — equation `(9)`: the admissible repair set is exactly
  `[max 0 (-epsilon_0), ∞)`, so the threshold equals `max(0, -epsilon_0(a))`.
- **`repairThreshold_mono`** and **`repairThreshold_eq_zero_of_tendsto_zero`** — equation `(10)`:
  the threshold is nondecreasing and vanishes cofinally only if it vanishes identically.
- `restrictedKernelFloor`, **`restrictedKernelFloor_antitone`** — the instantiation on the aperture
  domains with the kernel form.
- **`rayleighQuotientSet_apertureDomain_nonempty`** — a smooth bump supported in `(-a, a)` has
  positive mass, so at every positive aperture the trial set is nonempty and the floor is not a
  junk value.  This is the non-vacuity certificate for the whole family.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem above.

Current audit: direct Lean compile and targeted Lake build pass; ten capstones covering floor
antitonicity, witness persistence, negative-part monotonicity, cofinal evacuation, repair threshold,
concrete aperture monotonicity, and nonvacuity depend only on the standard axiom trio. Module has no
`sorry`, `admit`, `axiom`, `opaque`, or `unsafe`; `RHTower.lean` imports it in `HEAD`. Repository-wide
lint remains blocked only by another agent's concurrent untracked `FactorFramedTensorJacobian.lean`,
with no nested-floor finding.

Not formalized: Suzuki's published generalized eigenvalue identity `(6)` itself, which converts
`QW(v,v)` and `||v||²` into `<G_a u,u>` and `<K_a u,u>` for `u = Dv`.  That is an analytic input of
the source, not a theorem of this card; the abstract statements above are stated for an arbitrary
energy/mass pair, so they apply verbatim to either presentation.

## Gates

- [x] nested-domain floor monotonicity proved
- [x] negative-part monotonicity proved
- [x] compact repair threshold identified
- [x] evacuation mechanism excluded
- [x] positive no-negative-birth formulation isolated
- [x] Lean: floor antitonicity, witness bound and negative-part monotonicity unconditional
- [x] Lean: evacuation theorem `(5)` unconditional
- [x] Lean: repair threshold `(8)`--`(10)` identified with the negative part, unconditional
- [x] Lean: aperture-domain instantiation with nonempty trial set at every positive aperture
- [x] Stage 3 promotion audit complete
