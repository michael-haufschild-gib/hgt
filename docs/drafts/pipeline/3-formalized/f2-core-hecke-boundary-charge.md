# F2 — the unique Hecke boundary charge of an upper-resonant core

- **Stage:** 3-formalized
- **Result:** Every upper-resonant core has a nonzero lower-cusp Hecke trace. Removing exactly that coefficient on `(0,1)` restores whole-axis Haar square integrability.
- **Scope:** Actual source `T₂` and actual PM cores; unweighted Haar measure. No positivity or full Mayer intertwining follows.

## Exact value

Write `w=2s`, `q=2^(−w)`, `Z=ζ(w−1)`, and `b=2Z/(w−1)`. The scattering-state normalization gives `periodValue(w,1)=2Z`; boundary subtraction gives `core_s(1)=2Z−2b`. Modular inversion gives `q core_s(1/2)=core_s(2)`. Consequently,

`T₂ core_s(1)=2 core_s(2)+2q core_s(1)`.

At a resonance, the existing exact Hecke error at `1` is `b(1−4q)`. Substituting and solving gives

`c_s := core_s(2)=Z/(w−1) · (w−2−4q)`.

The shifted zeta factor is nonzero for `0<Re w<1`. The remaining factor is also nonzero whenever `Re w>0`, `Im w>0`: if `w−2=4·2^(−w)`, its norm forces `0<Im w<4`. Then `0<Im w·log2<4log2<π`, so the right side has negative imaginary part and the left side has positive imaginary part. This is an exact inequality argument, without height sampling.

## Lower endpoint

The resonant endpoint theorem gives `|core_s(a)|≤K_s a^β`, `β=1−2 Re s∈(0,1)`. The completed scattering state is holomorphic around physical coordinate `2`; subtracting its explicit boundary powers preserves differentiability there. Modular inversion transports this differentiability to `1/2`. Thus

`q core_s((a+1)/2)−c_s=O(a)`.

The other three Hecke branches are `O(a^β)` near zero: their arguments are `2a`, `a/2`, `2a/(1+a)` and their multipliers have bounded norm. Since `a≤a^β` on `(0,1)`,

`T₂ core_s(a)−c_s=O(a^β)`.

Hence `T₂ core_s(a)→c_s≠0`. A nonzero finite lower limit is incompatible with Haar square integrability, because it bounds the energy below by a positive multiple of `a⁻¹`.

## Exact retained channel

For `r_s=T₂ core_s−c_s 1_(0,1)`, the lower energy is bounded by a constant times `a^(2β−1)`, integrable since `β>0`. The existing source-word estimate gives finite upper Haar energy; measurability and the global decay bound control the intervening compact interval. Therefore `r_s` has finite whole-axis Haar energy.

For any other coefficient `d`, the lower limit of `T₂ core_s−d 1_(0,1)` is `c_s−d`. Finite Haar energy forces this limit to vanish. Thus

`T₂ core_s−d 1_(0,1) ∈ L²((0,∞),da/a) ⇔ d=c_s`.

The obstruction supplies a unique boundary coordinate, even at critical-line resonances. It does not select the critical line or supply a sign for the PM Krein pairing.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/CoreHeckeBoundaryCharge`:

- `mayerPeriodCore_one_eq`
- `mayerPeriodCore_two_eq`
- `mayerPeriodCore_two_ne_zero`
- `hecke_mayerPeriodCore_sub_trace_bound`
- `mayerHeckeBoundaryRemainder_finite_whole_haar`
- `tendsto_hecke_mayerPeriodCore_lower`
- `hecke_mayerPeriodCore_boundary_charge_iff`
- `hecke_mayerPeriodCore_not_finite_whole_haar`

Individual final `lake --old env lean` audit passed without warnings. All eight declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
