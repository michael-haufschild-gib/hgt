import GaloisForLFunctions.RHTower.Deninger.DeningerDepletedPoisson
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusRightInverse
import GaloisForLFunctions.RHTower.Deninger.DeningerEvenPreimage
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrictEmbedding

/-!
# The exact Poisson range as a Möbius regularity domain

The canonical Möbius transform `𝔐_μ h(x) = ∑_{n ≥ 1} μ(n) H_h(nx)` is a *pointwise right inverse*
of positive Poisson summation on every Meyer cochain `h ∈ H_-`, and the double series
`∑_{m,n ≥ 1} ‖H_h(mnx)‖` that legitimises the rearrangement is finite.  Neither statement says that
`𝔐_μ h` extends through the radial origin as a member of `H_∩`; that extra regularity is exactly
what distinguishes the literal Poisson boundary range.

This module records that classification.  The **maximal regular Möbius domain**

`𝒟_μ = {h ∈ H_- : E𝔐_μ h extends as a member of H_∩}`

is proved equal to the image `Z(H_∩)` of the Poisson operator, with `E𝔐_μ` the inverse of `Z`
there, and the Möbius-regular part of the reflected two-collar graph is proved equal to the literal
Poisson boundary graph `{(Zf, Z ℱf) : f ∈ H_∩}`.

* `deningerLogPull_double_summable` : **the double series is finite.**
* `DeningerMobiusRegularDomain` : the maximal regular Möbius domain `𝒟_μ`.
* `deningerPoissonSource_eq_of_ray` : a regular Möbius preimage is a Poisson preimage.
* `deningerMobiusRegularDomain_eq_poissonRange` : **`𝒟_μ = Z(H_∩)`.**
* `deningerMobiusRegularDomain_existsUnique` : **`E𝔐_μ` inverts `Z` on `𝒟_μ`.**
* `deningerReflectedGraphMuRegular_eq` : **the Möbius-regular reflected graph is the Poisson
  boundary graph.**
-/

namespace RHTower

open SchwartzMap ArithmeticFunction

noncomputable section

/-! ## The double series -/

private theorem deningerShiftSq_summable :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℕ) := by
  have hsq : Summable fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hshift : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) :=
    (summable_nat_add_iff 1).mpr hsq
  refine hshift.congr fun n => ?_
  push_cast
  ring

/-- **The double series of the pullback is finite.**  Statement `(3)` of the card: for every
Meyer cochain `h` and every `x > 0`,

`∑_{m, n ≥ 1} ‖H_h(mnx)‖ < ∞`.

The pullback decays like an inverse square in the dilation parameter at *both* ends of the ray, so
the `(m,n)` term is at most `(C/x²)·m^{-2}n^{-2}`.  No cancellation in `μ` is used, which is why the
rearrangement behind the right-inverse identity is legitimate. -/
theorem deningerLogPull_double_summable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) :
    Summable fun q : ℕ × ℕ =>
      ‖deningerLogPull h ((((q.1 + 1) * (q.2 + 1) : ℕ) : ℝ) * x)‖ := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_sq hh
  have hxsq : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
  have hpair : Summable fun q : ℕ × ℕ =>
      (C / x ^ (2 : ℕ)) * ((1 / ((q.1 : ℝ) + 1) ^ (2 : ℕ)) * (1 / ((q.2 : ℝ) + 1) ^ (2 : ℕ))) := by
    refine Summable.mul_left _ ?_
    exact Summable.mul_of_nonneg (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℕ))
      (g := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) deningerShiftSq_summable deningerShiftSq_summable
      (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_norm_bounded hpair fun q => ?_
  have h1 : (0 : ℝ) < (q.1 : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (q.2 : ℝ) + 1 := by positivity
  have hcast : (((q.1 + 1) * (q.2 + 1) : ℕ) : ℝ) = ((q.1 : ℝ) + 1) * ((q.2 : ℝ) + 1) := by
    push_cast
    ring
  have hprod : (0 : ℝ) < (((q.1 + 1) * (q.2 + 1) : ℕ) : ℝ) * x := by
    rw [hcast]
    positivity
  have hterm := (hC ((((q.1 + 1) * (q.2 + 1) : ℕ) : ℝ) * x) hprod).2
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine le_trans hterm (le_of_eq ?_)
  rw [hcast, mul_pow, mul_pow]
  field_simp

/-! ## The maximal regular Möbius domain -/

/-- **The maximal regular Möbius domain** `𝒟_μ`: the Meyer cochains whose even Möbius preimage
`E𝔐_μ h`, with the value `0` prescribed at the radial origin, extends through that origin as a
member of Meyer's space `H_∩`. -/
def DeningerMobiusRegularDomain : Set DeningerExpSchwartz :=
  {h | ∃ f : DeningerMeyerCap, ∀ x : ℝ, x ≠ 0 →
    ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x
      = deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x}

/-- Membership in `𝒟_μ` is agreement with the canonical preimage on the positive ray alone: both
the candidate extension and the even extension are even. -/
theorem mem_deningerMobiusRegularDomain_iff (h : DeningerExpSchwartz) :
    h ∈ DeningerMobiusRegularDomain ↔ ∃ f : DeningerMeyerCap, ∀ x : ℝ, 0 < x →
      ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x
        = deningerMobiusPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun x hx => ?_⟩
    rw [hf x hx.ne', deningerEvenPreimage_of_pos _ hx]
  · rintro ⟨f, hf⟩
    refine ⟨f, fun x hx => ?_⟩
    rcases lt_trichotomy x 0 with hneg | hzero | hpos
    · have hxpos : (0 : ℝ) < -x := by linarith
      rw [← deningerMeyerCap_even f.2 x, hf (-x) hxpos,
        deningerEvenPreimage_of_neg _ hneg]
    · exact absurd hzero hx
    · rw [hf x hpos, deningerEvenPreimage_of_pos _ hpos]

/-! ## The range classification -/

/-- **A regular Möbius preimage is a Poisson preimage.**  If a member `f` of Meyer's space agrees
with the canonical Möbius preimage of `h` on the positive ray, then `Z f = h`: this is exactly the
pointwise right-inverse identity `(4)` read at every point `e^t` of the ray. -/
theorem deningerPoissonSource_eq_of_ray {h : DeningerExpSchwartz} {f : DeningerMeyerCap}
    (hf : ∀ x : ℝ, 0 < x →
      ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x
        = deningerMobiusPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x) :
    deningerPoissonSource f = h := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerPoissonSource_apply, deningerPoissonLog_eq]
  have hxpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hray : deningerPoissonValue ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) (Real.exp t)
      = deningerRaySum (deningerMobiusPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
        (Real.exp t) := by
    rw [deningerPoissonValue, deningerRaySum]
    refine tsum_congr fun n => ?_
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) * Real.exp t := by positivity
    have hcomm : Real.exp t * ((n : ℝ) + 1) = ((n : ℝ) + 1) * Real.exp t := by ring
    rw [hcomm]
    exact hf _ hpos
  rw [hray, deningerMobius_rightInverse h.2 hxpos, deningerLogPull_apply, Real.log_exp]

/-- **The exact Poisson-range classification `(7)`: `𝒟_μ = Z(H_∩)`.**

One inclusion is the corpus's left Möbius inversion on a Poisson boundary, which says that the
canonical preimage of `Z f` *is* `f`; the other is the pointwise right-inverse identity, which says
that any `H_∩` extension of the canonical preimage has Poisson sum `h`.  No estimate of the Mertens
function and no hypothesis on the zeros of zeta enters. -/
theorem deningerMobiusRegularDomain_eq_poissonRange :
    DeningerMobiusRegularDomain = Set.range deningerPoissonSource := by
  refine Set.Subset.antisymm (fun h hh => ?_) (fun h hh => ?_)
  · obtain ⟨f, hf⟩ := (mem_deningerMobiusRegularDomain_iff h).mp hh
    exact ⟨f, deningerPoissonSource_eq_of_ray hf⟩
  · obtain ⟨f, rfl⟩ := hh
    refine (mem_deningerMobiusRegularDomain_iff _).mpr ⟨f, fun x hx => ?_⟩
    exact (deningerMobiusPreimage_poissonSource f hx).symm

/-- **`E𝔐_μ` is the inverse of `Z` on `𝒟_μ`.**  A member of the regular domain has exactly one
`H_∩` extension of its even Möbius preimage, and that extension is its Poisson preimage. -/
theorem deningerMobiusRegularDomain_existsUnique {h : DeningerExpSchwartz}
    (hh : h ∈ DeningerMobiusRegularDomain) :
    ∃! f : DeningerMeyerCap,
      (∀ x : ℝ, x ≠ 0 →
        ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x
          = deningerEvenPreimage ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x)
      ∧ deningerPoissonSource f = h := by
  obtain ⟨f, hf⟩ := hh
  refine ⟨f, ⟨hf, deningerPoissonSource_eq_of_ray fun x hx => ?_⟩, ?_⟩
  · rw [hf x hx.ne', deningerEvenPreimage_of_pos _ hx]
  · rintro g ⟨-, hg⟩
    exact deningerPoissonSource_injective (hg.trans (deningerPoissonSource_eq_of_ray
      (fun x hx => by rw [hf x hx.ne', deningerEvenPreimage_of_pos _ hx])).symm)

/-- **`(12)`: Poisson incidence is exactly canonical Möbius regularity.** -/
theorem deningerPoissonIncidence_iff (h : DeningerExpSchwartz) :
    h ∈ Set.range deningerPoissonSource ↔ h ∈ DeningerMobiusRegularDomain := by
  rw [deningerMobiusRegularDomain_eq_poissonRange]

/-! ## The reflected two-collar graph -/

/-- The Möbius-regular part `Γ_sec^{μ-reg}` of the reflected two-collar graph: the pairs `(h, Jh)`
whose first entry lies in the maximal regular Möbius domain. -/
def DeningerReflectedGraphMuRegular : Set (DeningerExpSchwartz × DeningerExpSchwartz) :=
  {p | p.1 ∈ DeningerMobiusRegularDomain ∧ p.2 = deningerCollarExchange p.1}

/-- The literal two-collar Poisson boundary graph `{(Zf, Z ℱf) : f ∈ H_∩}`. -/
def DeningerPoissonBoundaryGraph : Set (DeningerExpSchwartz × DeningerExpSchwartz) :=
  {p | ∃ f : DeningerMeyerCap,
    p = (deningerPoissonSource f, deningerPoissonSource (deningerMeyerCapFourier f))}

/-- **The reflected-graph Möbius incidence classification `(11)`.**  The Möbius-regular part of the
reflected two-collar graph is exactly the literal Poisson boundary graph: membership of the first
collar in `𝒟_μ` writes it as `Z f`, and Meyer--Poisson reflection turns `J(Zf)` into `Z(ℱf)`. -/
theorem deningerReflectedGraphMuRegular_eq :
    DeningerReflectedGraphMuRegular = DeningerPoissonBoundaryGraph := by
  refine Set.Subset.antisymm (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨hmem, hrefl⟩ := hp
    rw [deningerMobiusRegularDomain_eq_poissonRange] at hmem
    obtain ⟨f, hf⟩ := hmem
    refine ⟨f, Prod.ext hf.symm ?_⟩
    rw [hrefl, ← hf, deningerCollarExchange_poissonSource]
  · obtain ⟨f, hf⟩ := hp
    have h1 : p.1 = deningerPoissonSource f := by rw [hf]
    have h2 : p.2 = deningerPoissonSource (deningerMeyerCapFourier f) := by rw [hf]
    refine ⟨?_, ?_⟩
    · rw [deningerMobiusRegularDomain_eq_poissonRange, h1]
      exact ⟨f, rfl⟩
    · rw [h1, h2, deningerCollarExchange_poissonSource]

/-! ## The regular domain in the nuclear Meyer topology -/

/-- The maximal regular Möbius domain, read inside the Meyer source with its nuclear topology. -/
def DeningerMobiusRegularDomainMeyer : Set DeningerMeyerSource :=
  {h | DeningerMeyerSource.toSource h ∈ DeningerMobiusRegularDomain}

theorem deningerMobiusRegularDomainMeyer_eq_range :
    DeningerMobiusRegularDomainMeyer = Set.range deningerPoissonMeyerLM := by
  ext h
  rw [DeningerMobiusRegularDomainMeyer, Set.mem_setOf_eq,
    deningerMobiusRegularDomain_eq_poissonRange]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, DeningerMeyerSource.toSource.injective ?_⟩
    rw [deningerPoissonMeyerLM_toSource, hf]
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem deningerPoissonMeyerRange_carrier :
    ((LinearMap.range deningerPoissonMeyerLM : Submodule ℂ DeningerMeyerSource) :
      Set DeningerMeyerSource) = DeningerMobiusRegularDomainMeyer := by
  rw [deningerMobiusRegularDomainMeyer_eq_range]
  ext h
  exact LinearMap.mem_range

/-- **`(8)`, first half: the maximal regular Möbius domain is closed in the nuclear Meyer
topology.**  It is the image of the Poisson operator, which is closed because it is the preimage of
the closed radial Poisson image under the continuous radial presentation. -/
theorem deningerMobiusRegularDomainMeyer_isClosed :
    IsClosed DeningerMobiusRegularDomainMeyer := by
  rw [deningerMobiusRegularDomainMeyer_eq_range]
  exact deningerPoissonMeyer_range_isClosed

/-- The continuous inverse **is** the even Möbius transform: a member of `H_∩` extending the even
Möbius preimage of a point of the regular domain is the value of the inverse there. -/
theorem deningerPoissonMeyerRangeEquiv_symm_eq_mobiusExtension
    (x : LinearMap.range deningerPoissonMeyerLM) (f : DeningerMeyerCap)
    (hf : ∀ y : ℝ, y ≠ 0 →
      ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) y
        = deningerEvenPreimage
            ((DeningerMeyerSource.toSource (x : DeningerMeyerSource) : DeningerExpSchwartz) :
              𝓢(ℝ, ℂ)) y) :
    deningerPoissonMeyerRangeEquiv.symm x = f := by
  refine deningerPoissonMeyerLM_injective ?_
  rw [deningerPoissonMeyerRangeEquiv_symm_coe x]
  refine DeningerMeyerSource.toSource.injective ?_
  rw [deningerPoissonMeyerLM_toSource]
  refine (deningerPoissonSource_eq_of_ray (fun y hy => ?_)).symm
  rw [hf y hy.ne', deningerEvenPreimage_of_pos _ hy]

/-- **`(8)`, second half: the inverse `E𝔐_μ : 𝒟_μ → H_∩` is continuous** for the nuclear Meyer
topology on the domain and the Schwartz topology on `H_∩`. -/
theorem deningerMobiusRegularDomain_inverse_continuous :
    Continuous (deningerPoissonMeyerRangeEquiv.symm :
      LinearMap.range deningerPoissonMeyerLM → DeningerMeyerCap) :=
  deningerPoissonMeyerRangeEquiv_symm_continuous

end

end RHTower
