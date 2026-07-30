/-
# The graded Mahler carrier

The dyadic Mahler operator `t ↦ t²` acts on Hahn series over `ℚ` whose coefficients are
rational functions in an auxiliary eigenvariable `ℓ`.  Doubling the exponents while scaling
the eigenvariable by two is a field automorphism `σ` with `σ(t^q) = t^{2q}` and `σ(ℓ) = 2ℓ`.
The eigenvariable will untwist the Euler derivation: `ℓ·(t d/dt)` commutes with `σ` exactly,
which puts the dyadic Mahler equation of the Böttcher velocity jet inside the commuting
difference-differential framework.  This module constructs the carrier, the automorphism,
and the eigenvariable, and proves the exponent-doubling and eigenvalue laws.
-/
import Mathlib
import GaloisForLFunctions.U0.VelocityJetSeries

namespace GaloisForLFunctions

open Polynomial HahnSeries

noncomputable section

/-! ## The coefficient field and its scaling automorphism -/

/-- The scaling `p(ℓ) ↦ p(2ℓ)` on polynomials. -/
def ellPolyScale : ℂ[X] ≃ₐ[ℂ] ℂ[X] :=
  letI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  algEquivCMulXAddC 2 0

theorem ellPolyScale_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : ellPolyScale p ≠ 0 := by
  intro h
  apply hp
  have := congrArg ellPolyScale.symm h
  simpa using this

theorem ellPolyScale_symm_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : ellPolyScale.symm p ≠ 0 := by
  intro h
  apply hp
  have := congrArg ellPolyScale h
  simpa using this

theorem ellPolyScale_mem_comap :
    nonZeroDivisors ℂ[X] ≤ (nonZeroDivisors ℂ[X]).comap ellPolyScale.toAlgHom := by
  intro q hq
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  exact ellPolyScale_ne_zero hq

theorem ellPolyScale_symm_mem_comap :
    nonZeroDivisors ℂ[X] ≤ (nonZeroDivisors ℂ[X]).comap ellPolyScale.symm.toAlgHom := by
  intro q hq
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  exact ellPolyScale_symm_ne_zero hq

/-- The scaling `f(ℓ) ↦ f(2ℓ)` on rational functions, forward direction. -/
def ellScaleHom : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.mapAlgHom ellPolyScale.toAlgHom ellPolyScale_mem_comap

/-- The scaling `f(ℓ) ↦ f(ℓ/2)` on rational functions, backward direction. -/
def ellScaleInvHom : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.mapAlgHom ellPolyScale.symm.toAlgHom ellPolyScale_symm_mem_comap

theorem ellScaleHom_apply_div (p q : ℂ[X]) :
    ellScaleHom (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) =
      algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale p) /
        algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale q) := by
  have hcoe : ellScaleHom (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) =
      RatFunc.map ellPolyScale.toAlgHom ellPolyScale_mem_comap
        (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) :=
    congrFun (RatFunc.coe_mapAlgHom_eq_coe_map _ _) _
  rw [hcoe, RatFunc.map_apply_div]
  rfl

theorem ellScaleInvHom_apply_div (p q : ℂ[X]) :
    ellScaleInvHom (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) =
      algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale.symm p) /
        algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale.symm q) := by
  have hcoe : ellScaleInvHom (algebraMap ℂ[X] (RatFunc ℂ) p /
      algebraMap ℂ[X] (RatFunc ℂ) q) =
      RatFunc.map ellPolyScale.symm.toAlgHom ellPolyScale_symm_mem_comap
        (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) :=
    congrFun (RatFunc.coe_mapAlgHom_eq_coe_map _ _) _
  rw [hcoe, RatFunc.map_apply_div]
  rfl

theorem ellScaleInvHom_ellScaleHom (f : RatFunc ℂ) :
    ellScaleInvHom (ellScaleHom f) = f := by
  conv_lhs => rw [← f.num_div_denom, ellScaleHom_apply_div, ellScaleInvHom_apply_div]
  rw [ellPolyScale.symm_apply_apply, ellPolyScale.symm_apply_apply, f.num_div_denom]

theorem ellScaleHom_ellScaleInvHom (f : RatFunc ℂ) :
    ellScaleHom (ellScaleInvHom f) = f := by
  conv_lhs => rw [← f.num_div_denom, ellScaleInvHom_apply_div, ellScaleHom_apply_div]
  rw [ellPolyScale.apply_symm_apply, ellPolyScale.apply_symm_apply, f.num_div_denom]

/-- The scaling `f(ℓ) ↦ f(2ℓ)` as a ring automorphism of the coefficient field. -/
def ellScale : RatFunc ℂ ≃+* RatFunc ℂ :=
  RingEquiv.ofRingHom ellScaleHom.toRingHom ellScaleInvHom.toRingHom
    (RingHom.ext ellScaleHom_ellScaleInvHom) (RingHom.ext ellScaleInvHom_ellScaleHom)

/-- The eigenvalue law on the eigenvariable: `ℓ ↦ 2ℓ`. -/
theorem ellScale_X : ellScale (RatFunc.X : RatFunc ℂ) = 2 * RatFunc.X := by
  have hX : (RatFunc.X : RatFunc ℂ) =
      algebraMap ℂ[X] (RatFunc ℂ) X / algebraMap ℂ[X] (RatFunc ℂ) 1 := by
    rw [map_one, div_one, RatFunc.algebraMap_X]
  show ellScaleHom _ = _
  rw [hX, ellScaleHom_apply_div]
  simp only [map_one, div_one]
  have hpoly : ellPolyScale (X : ℂ[X]) = 2 * X := by
    letI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
    rw [ellPolyScale]
    simp [algEquivCMulXAddC]
    rw [show (Polynomial.C (2 : ℂ)) = (2 : ℂ[X]) from by
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, map_natCast]
      norm_num]
  rw [hpoly, map_mul, RatFunc.algebraMap_X]
  rw [show (2 : ℂ[X]) = ((2 : ℕ) : ℂ[X]) by norm_num, map_natCast]
  norm_num

theorem ellScale_algebraMap_C (c : ℂ) :
    ellScale (algebraMap ℂ (RatFunc ℂ) c) = algebraMap ℂ (RatFunc ℂ) c := by
  show ellScaleHom _ = _
  rw [ellScaleHom.commutes]

/-! ## The graded Mahler automorphism -/

/-- Exponent doubling on `ℚ`. -/
def qDouble : ℚ →+ ℚ := AddMonoidHom.mk' (fun q => 2 * q) (fun a b => by ring)

theorem qDouble_injective : Function.Injective qDouble := by
  intro a b h
  have h2 : 2 * a = 2 * b := h
  linarith

theorem qDouble_le_iff (a b : ℚ) : qDouble a ≤ qDouble b ↔ a ≤ b := by
  show 2 * a ≤ 2 * b ↔ a ≤ b
  constructor <;> intro h <;> linarith

/-- Exponent halving on `ℚ`. -/
def qHalf : ℚ →+ ℚ := AddMonoidHom.mk' (fun q => q / 2) (fun a b => by ring)

theorem qHalf_injective : Function.Injective qHalf := by
  intro a b h
  have h2 : a / 2 = b / 2 := h
  linarith

theorem qHalf_le_iff (a b : ℚ) : qHalf a ≤ qHalf b ↔ a ≤ b := by
  show a / 2 ≤ b / 2 ↔ a ≤ b
  constructor <;> intro h <;> linarith

/-- Coefficient scaling `ℓ ↦ 2ℓ` applied to every Hahn coefficient, as a ring homomorphism. -/
def hahnCoeffScaleHom (e : RatFunc ℂ →+* RatFunc ℂ) :
    HahnSeries ℚ (RatFunc ℂ) →+* HahnSeries ℚ (RatFunc ℂ) where
  toFun f := f.map e
  map_zero' := by
    ext q
    show e ((0 : HahnSeries ℚ (RatFunc ℂ)).coeff q) = (0 : HahnSeries ℚ (RatFunc ℂ)).coeff q
    simp
  map_one' := by
    ext q
    show e ((1 : HahnSeries ℚ (RatFunc ℂ)).coeff q) = (1 : HahnSeries ℚ (RatFunc ℂ)).coeff q
    rw [HahnSeries.coeff_one]
    rcases eq_or_ne q 0 with rfl | hq
    · rw [if_pos rfl, map_one]
    · rw [if_neg hq, map_zero]
  map_add' := by
    intro x y
    ext q
    show e ((x + y).coeff q) = (x.map e + y.map e).coeff q
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add, map_add]
    rfl
  map_mul' := by
    intro x y
    exact HahnSeries.map_mul (e : RatFunc ℂ →ₙ+* RatFunc ℂ)

/-- Exponent doubling on the carrier. -/
def hahnExpDouble : HahnSeries ℚ (RatFunc ℂ) →+* HahnSeries ℚ (RatFunc ℂ) :=
  HahnSeries.embDomainRingHom qDouble qDouble_injective qDouble_le_iff

/-- Exponent halving on the carrier. -/
def hahnExpHalf : HahnSeries ℚ (RatFunc ℂ) →+* HahnSeries ℚ (RatFunc ℂ) :=
  HahnSeries.embDomainRingHom qHalf qHalf_injective qHalf_le_iff

theorem hahnExpDouble_coeff (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (hahnExpDouble f).coeff (2 * q) = f.coeff q := by
  show (HahnSeries.embDomain ⟨⟨qDouble, qDouble_injective⟩, qDouble_le_iff _ _⟩ f).coeff
    (2 * q) = f.coeff q
  exact HahnSeries.embDomain_coeff (a := q)

theorem hahnExpHalf_coeff (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (hahnExpHalf f).coeff (q / 2) = f.coeff q := by
  show (HahnSeries.embDomain ⟨⟨qHalf, qHalf_injective⟩, qHalf_le_iff _ _⟩ f).coeff
    (q / 2) = f.coeff q
  exact HahnSeries.embDomain_coeff (a := q)

/-- Forward graded Mahler substitution: coefficients scale, then exponents double. -/
def mahlerSigmaHom : HahnSeries ℚ (RatFunc ℂ) →+* HahnSeries ℚ (RatFunc ℂ) :=
  hahnExpDouble.comp (hahnCoeffScaleHom ellScale.toRingHom)

/-- Backward graded Mahler substitution. -/
def mahlerSigmaInvHom : HahnSeries ℚ (RatFunc ℂ) →+* HahnSeries ℚ (RatFunc ℂ) :=
  (hahnCoeffScaleHom ellScale.symm.toRingHom).comp hahnExpHalf

theorem mahlerSigmaHom_coeff (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (mahlerSigmaHom f).coeff (2 * q) = ellScale (f.coeff q) := by
  show (hahnExpDouble ((hahnCoeffScaleHom ellScale.toRingHom) f)).coeff (2 * q) = _
  rw [hahnExpDouble_coeff]
  rfl

theorem mahlerSigmaHom_coeff' (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (mahlerSigmaHom f).coeff q = ellScale (f.coeff (q / 2)) := by
  have h : q = 2 * (q / 2) := by ring
  rw [h, mahlerSigmaHom_coeff]
  norm_num

theorem mahlerSigmaInvHom_coeff (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (mahlerSigmaInvHom f).coeff q = ellScale.symm (f.coeff (2 * q)) := by
  show ellScale.symm ((hahnExpHalf f).coeff q) = _
  have h := hahnExpHalf_coeff f (2 * q)
  rw [show (2 * q) / 2 = q by ring] at h
  rw [h]

theorem mahlerSigmaInvHom_mahlerSigmaHom (f : HahnSeries ℚ (RatFunc ℂ)) :
    mahlerSigmaInvHom (mahlerSigmaHom f) = f := by
  ext q
  rw [mahlerSigmaInvHom_coeff, mahlerSigmaHom_coeff, ellScale.symm_apply_apply]

theorem mahlerSigmaHom_mahlerSigmaInvHom (f : HahnSeries ℚ (RatFunc ℂ)) :
    mahlerSigmaHom (mahlerSigmaInvHom f) = f := by
  ext q
  rw [mahlerSigmaHom_coeff', mahlerSigmaInvHom_coeff, ellScale.apply_symm_apply]
  congr 1
  ring

/-- **The graded Mahler automorphism** of the carrier: `t^q ↦ t^{2q}`, `ℓ ↦ 2ℓ`. -/
def mahlerSigma : HahnSeries ℚ (RatFunc ℂ) ≃+* HahnSeries ℚ (RatFunc ℂ) :=
  RingEquiv.ofRingHom mahlerSigmaHom mahlerSigmaInvHom
    (RingHom.ext mahlerSigmaHom_mahlerSigmaInvHom)
    (RingHom.ext mahlerSigmaInvHom_mahlerSigmaHom)

theorem mahlerSigma_coeff (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (mahlerSigma f).coeff (2 * q) = ellScale (f.coeff q) :=
  mahlerSigmaHom_coeff f q

/-- The action on monomials. -/
theorem mahlerSigma_single (q : ℚ) (r : RatFunc ℂ) :
    mahlerSigma (HahnSeries.single q r) = HahnSeries.single (2 * q) (ellScale r) := by
  ext x
  rcases eq_or_ne x (2 * q) with rfl | hx
  · rw [mahlerSigma_coeff, HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · have hx2 : x / 2 ≠ q := by
      intro h
      apply hx
      rw [← h]
      ring
    show (mahlerSigmaHom (HahnSeries.single q r)).coeff x = _
    rw [mahlerSigmaHom_coeff', HahnSeries.coeff_single_of_ne hx2,
      HahnSeries.coeff_single_of_ne hx, map_zero]

/-- The base variable of the carrier. -/
def mahlerT : HahnSeries ℚ (RatFunc ℂ) := HahnSeries.single 1 1

/-- The eigenvariable of the carrier. -/
def mahlerEll : HahnSeries ℚ (RatFunc ℂ) := HahnSeries.single 0 RatFunc.X

/-- The Mahler law on the base variable: `σ(t) = t²`. -/
theorem mahlerSigma_mahlerT : mahlerSigma mahlerT = mahlerT * mahlerT := by
  rw [mahlerT, mahlerSigma_single, map_one, HahnSeries.single_mul_single, mul_one]
  norm_num

/-- The eigenvalue law on the eigenvariable: `σ(ℓ) = 2·ℓ`. -/
theorem mahlerSigma_mahlerEll : mahlerSigma mahlerEll = 2 * mahlerEll := by
  rw [mahlerEll, mahlerSigma_single, ellScale_X]
  rw [show (2 : HahnSeries ℚ (RatFunc ℂ)) = HahnSeries.single 0 2 from ?_]
  · rw [HahnSeries.single_mul_single, zero_add]
    norm_num
  · rw [show ((2 : RatFunc ℂ)) = ((2 : ℕ) : RatFunc ℂ) by norm_num]
    rw [show ((2 : HahnSeries ℚ (RatFunc ℂ))) = ((2 : ℕ) : HahnSeries ℚ (RatFunc ℂ)) by
      norm_num]
    exact (map_natCast (HahnSeries.C : RatFunc ℂ →+* HahnSeries ℚ (RatFunc ℂ)) 2).symm

/-! ## The untwisted Euler derivation -/

/-- The Euler derivation `θ = t·d/dt` on the carrier: the coefficient at exponent `q` is
scaled by `q`. -/
def eulerDeriv (f : HahnSeries ℚ (RatFunc ℂ)) : HahnSeries ℚ (RatFunc ℂ) where
  coeff q := algebraMap ℚ (RatFunc ℂ) q * f.coeff q
  isPWO_support' := f.isPWO_support'.mono (by
    intro q hq
    rw [Function.mem_support] at hq ⊢
    intro h
    exact hq (by rw [h, mul_zero]))

theorem eulerDeriv_coeff (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (eulerDeriv f).coeff q = algebraMap ℚ (RatFunc ℂ) q * f.coeff q := rfl

theorem eulerDeriv_support_subset (f : HahnSeries ℚ (RatFunc ℂ)) :
    (eulerDeriv f).support ⊆ f.support := by
  intro q hq
  rw [HahnSeries.mem_support] at hq ⊢
  intro h
  rw [eulerDeriv_coeff, h, mul_zero] at hq
  exact hq rfl

theorem eulerDeriv_add (f g : HahnSeries ℚ (RatFunc ℂ)) :
    eulerDeriv (f + g) = eulerDeriv f + eulerDeriv g := by
  ext q
  rw [HahnSeries.coeff_add, eulerDeriv_coeff, eulerDeriv_coeff, eulerDeriv_coeff,
    HahnSeries.coeff_add]
  ring

/-- Leibniz rule for the Euler derivation: exponents add along the convolution. -/
theorem eulerDeriv_mul (f g : HahnSeries ℚ (RatFunc ℂ)) :
    eulerDeriv (f * g) = eulerDeriv f * g + f * eulerDeriv g := by
  ext a
  rw [HahnSeries.coeff_add, eulerDeriv_coeff, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul (x := eulerDeriv f) (y := g),
    HahnSeries.coeff_mul (x := f) (y := eulerDeriv g), Finset.mul_sum]
  have hsub1 : Finset.antidiagonal (eulerDeriv f).isPWO_support g.isPWO_support a ⊆
      Finset.antidiagonal f.isPWO_support g.isPWO_support a := by
    intro x hx
    rw [Finset.mem_antidiagonal] at hx ⊢
    exact ⟨eulerDeriv_support_subset f hx.1, hx.2.1, hx.2.2⟩
  have hsub2 : Finset.antidiagonal f.isPWO_support (eulerDeriv g).isPWO_support a ⊆
      Finset.antidiagonal f.isPWO_support g.isPWO_support a := by
    intro x hx
    rw [Finset.mem_antidiagonal] at hx ⊢
    exact ⟨hx.1, eulerDeriv_support_subset g hx.2.1, hx.2.2⟩
  rw [Finset.sum_subset hsub1 (by
    intro x hx hnx
    rw [Finset.mem_antidiagonal] at hx
    have hz : (eulerDeriv f).coeff x.1 = 0 := by
      by_contra hc
      exact hnx (Finset.mem_antidiagonal.mpr
        ⟨(HahnSeries.mem_support _ _).mpr hc, hx.2.1, hx.2.2⟩)
    rw [hz, zero_mul])]
  rw [Finset.sum_subset hsub2 (by
    intro x hx hnx
    rw [Finset.mem_antidiagonal] at hx
    have hz : (eulerDeriv g).coeff x.2 = 0 := by
      by_contra hc
      exact hnx (Finset.mem_antidiagonal.mpr
        ⟨hx.1, (HahnSeries.mem_support _ _).mpr hc, hx.2.2⟩)
    rw [hz, mul_zero])]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  rw [eulerDeriv_coeff, eulerDeriv_coeff, ← hx.2.2, map_add]
  ring

/-- **The untwisted Mahler derivation** `δ = ℓ·θ`. -/
def mahlerDeriv (f : HahnSeries ℚ (RatFunc ℂ)) : HahnSeries ℚ (RatFunc ℂ) :=
  mahlerEll * eulerDeriv f

theorem mahlerDeriv_coeff (f : HahnSeries ℚ (RatFunc ℂ)) (q : ℚ) :
    (mahlerDeriv f).coeff q = RatFunc.X * (algebraMap ℚ (RatFunc ℂ) q * f.coeff q) := by
  rw [mahlerDeriv, mahlerEll, HahnSeries.coeff_single_zero_mul, eulerDeriv_coeff]

theorem mahlerDeriv_add (f g : HahnSeries ℚ (RatFunc ℂ)) :
    mahlerDeriv (f + g) = mahlerDeriv f + mahlerDeriv g := by
  rw [mahlerDeriv, mahlerDeriv, mahlerDeriv, eulerDeriv_add, mul_add]

theorem mahlerDeriv_mul (f g : HahnSeries ℚ (RatFunc ℂ)) :
    mahlerDeriv (f * g) = mahlerDeriv f * g + f * mahlerDeriv g := by
  rw [mahlerDeriv, mahlerDeriv, mahlerDeriv, eulerDeriv_mul, mul_add]
  ring

/-- `ℚ`-scalars are fixed by the coefficient scaling. -/
theorem ellScale_ratCast (q : ℚ) :
    ellScale (algebraMap ℚ (RatFunc ℂ) q) = algebraMap ℚ (RatFunc ℂ) q := by
  rw [eq_ratCast (algebraMap ℚ (RatFunc ℂ)) q, map_ratCast]

/-- **Exact commutation**: the eigenvariable untwists the Euler derivation, so the graded
Mahler automorphism commutes with `δ = ℓ·θ` on the nose. -/
theorem mahlerSigma_mahlerDeriv (f : HahnSeries ℚ (RatFunc ℂ)) :
    mahlerSigma (mahlerDeriv f) = mahlerDeriv (mahlerSigma f) := by
  ext q
  have hL : (mahlerSigma (mahlerDeriv f)).coeff q =
      ellScale ((mahlerDeriv f).coeff (q / 2)) := mahlerSigmaHom_coeff' _ q
  have hR : (mahlerSigma f).coeff q = ellScale (f.coeff (q / 2)) := mahlerSigmaHom_coeff' _ q
  rw [hL, mahlerDeriv_coeff, mahlerDeriv_coeff, hR, map_mul, map_mul, ellScale_X,
    ellScale_ratCast]
  have hq : algebraMap ℚ (RatFunc ℂ) q = 2 * algebraMap ℚ (RatFunc ℂ) (q / 2) := by
    rw [show (2 : RatFunc ℂ) = algebraMap ℚ (RatFunc ℂ) 2 by
      rw [eq_ratCast (algebraMap ℚ (RatFunc ℂ)) 2]
      norm_num]
    rw [← map_mul]
    congr 1
    ring
  rw [hq]
  ring

/-! ## The fixed field of the coefficient scaling -/

theorem ellPolyScale_apply (p : ℂ[X]) : ellPolyScale p = p.comp (Polynomial.C 2 * X) := by
  letI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  show (algEquivCMulXAddC (2:ℂ) 0) p = _
  rw [algEquivCMulXAddC_apply, map_zero, add_zero, ← comp_eq_aeval]

theorem ellPolyScale_X_eq : ellPolyScale (X : ℂ[X]) = Polynomial.C 2 * X := by
  rw [ellPolyScale_apply, X_comp]

theorem ellPolyScale_eval (p : ℂ[X]) (z : ℂ) :
    (ellPolyScale p).eval z = p.eval (2 * z) := by
  rw [ellPolyScale_apply, Polynomial.eval_comp]
  simp

theorem ellPolyScale_natDegree (p : ℂ[X]) :
    (ellPolyScale p).natDegree = p.natDegree := by
  rw [ellPolyScale_apply, Polynomial.natDegree_comp]
  have h1 : (Polynomial.C (2:ℂ) * X).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul (two_ne_zero), Polynomial.natDegree_X]
  rw [h1, mul_one]

/-- A nonzero polynomial dividing its own dyadic dilation is a monomial. -/
theorem eq_monomial_of_dvd_ellPolyScale :
    ∀ d : ℕ, ∀ p : ℂ[X], p ≠ 0 → p.natDegree = d → p ∣ ellPolyScale p →
      p = Polynomial.C p.leadingCoeff * X ^ p.natDegree := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro p hp hdeg hdvd
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      rw [hdeg, pow_zero, mul_one]
      rw [show p.leadingCoeff = p.coeff 0 from by rw [Polynomial.leadingCoeff, hdeg]]
      exact Polynomial.eq_C_of_natDegree_eq_zero hdeg
    · have hdegpos : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
      obtain ⟨r, hr⟩ := Complex.exists_root hdegpos
      rcases eq_or_ne r 0 with rfl | hr0
      · -- the root is at the origin: peel one factor of `X` and recurse
        have hXdvd : X ∣ p := Polynomial.X_dvd_iff.mpr (by
          rw [Polynomial.coeff_zero_eq_eval_zero]
          exact hr)
        obtain ⟨p₁, hp₁⟩ := hXdvd
        have hp₁0 : p₁ ≠ 0 := by
          intro h
          apply hp
          rw [hp₁, h, mul_zero]
        have hdeg₁ : p₁.natDegree = d - 1 := by
          have := Polynomial.natDegree_mul (Polynomial.X_ne_zero) hp₁0
          rw [← hp₁, Polynomial.natDegree_X] at this
          omega
        have hdvd₁ : p₁ ∣ ellPolyScale p₁ := by
          have hscale : ellPolyScale p = Polynomial.C 2 * X * ellPolyScale p₁ := by
            rw [hp₁, map_mul, ellPolyScale_X_eq]
          have h2 : X * p₁ ∣ Polynomial.C 2 * (X * ellPolyScale p₁) := by
            rw [show Polynomial.C (2:ℂ) * (X * ellPolyScale p₁) =
              Polynomial.C 2 * X * ellPolyScale p₁ by ring, ← hscale, ← hp₁]
            exact hdvd
          have hu : IsUnit (Polynomial.C (2:ℂ)) :=
            Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr two_ne_zero)
          have h3 : X * p₁ ∣ X * ellPolyScale p₁ := (hu.dvd_mul_left).mp h2
          exact (mul_dvd_mul_iff_left (Polynomial.X_ne_zero (R := ℂ))).mp h3
        have hmono := ih (d - 1) (by omega) p₁ hp₁0 hdeg₁ hdvd₁
        have hlc : p.leadingCoeff = p₁.leadingCoeff := by
          rw [hp₁, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X, one_mul]
        calc p = X * p₁ := hp₁
          _ = X * (Polynomial.C p₁.leadingCoeff * X ^ p₁.natDegree) := by rw [← hmono]
          _ = Polynomial.C p₁.leadingCoeff * X ^ (p₁.natDegree + 1) := by ring
          _ = Polynomial.C p.leadingCoeff * X ^ p.natDegree := by
              rw [hlc, hp₁, Polynomial.natDegree_mul Polynomial.X_ne_zero hp₁0,
                Polynomial.natDegree_X, Nat.add_comm 1 p₁.natDegree]
      · -- a nonzero root propagates along the dyadic orbit: impossible
        exfalso
        obtain ⟨v, hv⟩ := hdvd
        have hchain : ∀ n : ℕ, p.IsRoot ((2:ℂ) ^ n * r) := by
          intro n
          induction n with
          | zero => simpa using hr
          | succ n ihn =>
            have heval : p.eval ((2:ℂ) ^ (n+1) * r) = (ellPolyScale p).eval ((2:ℂ) ^ n * r) := by
              rw [ellPolyScale_eval]
              congr 1
              ring
            rw [Polynomial.IsRoot, heval, hv, Polynomial.eval_mul,
              show p.eval ((2:ℂ) ^ n * r) = 0 from ihn, zero_mul]
        have hinj : Function.Injective (fun n : ℕ => (2:ℂ) ^ n * r) := by
          intro m n h
          have hnorm : (2:ℝ) ^ m * ‖r‖ = (2:ℝ) ^ n * ‖r‖ := by
            have := congrArg norm h
            simpa [norm_mul, norm_pow] using this
          have : (2:ℝ) ^ m = (2:ℝ) ^ n := by
            field_simp [norm_ne_zero_iff.mpr hr0] at hnorm
            exact hnorm
          exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this)
        have hinf : {x : ℂ | p.IsRoot x}.Infinite :=
          Set.infinite_of_injective_forall_mem hinj hchain
        exact hinf (Polynomial.finite_setOf_isRoot hp)

/-- Rational functions fixed by the dyadic coefficient scaling are exactly the constants. -/
theorem ellScale_fixed_iff {f : RatFunc ℂ} :
    ellScale f = f ↔ ∃ c : ℂ, f = algebraMap ℂ (RatFunc ℂ) c := by
  constructor
  · intro h
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, by simp⟩
    have hden : algebraMap ℂ[X] (RatFunc ℂ) f.denom ≠ 0 :=
      RatFunc.algebraMap_ne_zero f.denom_ne_zero
    have hden' : algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale f.denom) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (ellPolyScale_ne_zero f.denom_ne_zero)
    have hdiv : algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale f.num) /
        algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale f.denom) =
        algebraMap ℂ[X] (RatFunc ℂ) f.num / algebraMap ℂ[X] (RatFunc ℂ) f.denom := by
      have hL : ellScale f = algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale f.num) /
          algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale f.denom) := by
        show ellScaleHom f = _
        conv_lhs => rw [← f.num_div_denom]
        rw [ellScaleHom_apply_div]
      rw [← hL, h]
      exact f.num_div_denom.symm
    have hcross : ellPolyScale f.num * f.denom = f.num * ellPolyScale f.denom := by
      have h1 := (div_eq_div_iff hden' hden).mp hdiv
      have h2 : algebraMap ℂ[X] (RatFunc ℂ) (ellPolyScale f.num * f.denom) =
          algebraMap ℂ[X] (RatFunc ℂ) (f.num * ellPolyScale f.denom) := by
        rw [map_mul, map_mul]
        exact h1
      exact IsFractionRing.injective ℂ[X] (RatFunc ℂ) h2
    have hco := f.isCoprime_num_denom
    have hnum_ne : f.num ≠ 0 := RatFunc.num_ne_zero hf0
    have hdvd_num : f.num ∣ ellPolyScale f.num := by
      have h1 : f.num ∣ ellPolyScale f.num * f.denom := by
        rw [hcross]
        exact Dvd.intro _ rfl
      exact hco.dvd_of_dvd_mul_right h1
    have hdvd_den : f.denom ∣ ellPolyScale f.denom := by
      have h1 : f.denom ∣ f.num * ellPolyScale f.denom := by
        rw [← hcross]
        exact Dvd.intro_left _ rfl
      exact hco.symm.dvd_of_dvd_mul_left h1
    have hnum_mono := eq_monomial_of_dvd_ellPolyScale f.num.natDegree f.num hnum_ne rfl hdvd_num
    have hden_mono := eq_monomial_of_dvd_ellPolyScale f.denom.natDegree f.denom
      f.denom_ne_zero rfl hdvd_den
    have hCscale : ∀ a : ℂ, ellPolyScale (Polynomial.C a) = Polynomial.C a := by
      intro a
      have := ellPolyScale.commutes a
      rwa [Polynomial.algebraMap_eq] at this
    -- evaluation at 1 turns the cross identity into a scalar identity
    have hkey : f.num.leadingCoeff * f.denom.leadingCoeff * (2:ℂ) ^ f.num.natDegree =
        f.num.leadingCoeff * f.denom.leadingCoeff * (2:ℂ) ^ f.denom.natDegree := by
      have h1 := congrArg (Polynomial.eval 1) hcross
      rw [Polynomial.eval_mul, Polynomial.eval_mul, ellPolyScale_eval, ellPolyScale_eval] at h1
      conv at h1 => rw [hnum_mono, hden_mono]
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, mul_one, one_pow] at h1
      linear_combination h1
    have hlc_num : f.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hnum_ne
    have hlc_den : f.denom.leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero
    have hpow : (2:ℂ) ^ f.num.natDegree = (2:ℂ) ^ f.denom.natDegree :=
      mul_left_cancel₀ (mul_ne_zero hlc_num hlc_den) hkey
    have hdeg_eq : f.num.natDegree = f.denom.natDegree := by
      have hR : ((2:ℝ) ^ f.num.natDegree : ℂ) = ((2:ℝ) ^ f.denom.natDegree : ℂ) := by
        push_cast
        exact_mod_cast hpow
      have hR2 : (2:ℝ) ^ f.num.natDegree = (2:ℝ) ^ f.denom.natDegree := by
        exact_mod_cast hR
      have hN : (2:ℕ) ^ f.num.natDegree = (2:ℕ) ^ f.denom.natDegree := by
        exact_mod_cast hR2
      exact Nat.pow_right_injective (le_refl 2) hN
    have hdeg_zero : f.num.natDegree = 0 := by
      by_contra hne
      have hdpos : 0 < f.num.natDegree := Nat.pos_of_ne_zero hne
      have hXnum : X ∣ f.num := by
        rw [hnum_mono]
        exact dvd_mul_of_dvd_right (dvd_pow_self X (by omega)) _
      have hXden : X ∣ f.denom := by
        rw [hden_mono, ← hdeg_eq]
        exact dvd_mul_of_dvd_right (dvd_pow_self X (by omega)) _
      exact Polynomial.not_isUnit_X (hco.isUnit_of_dvd' hXnum hXden)
    have hden_one : f.denom = 1 := by
      rw [hden_mono, ← hdeg_eq, hdeg_zero, pow_zero, mul_one,
        f.monic_denom.leadingCoeff, Polynomial.C_1]
    refine ⟨f.num.leadingCoeff, ?_⟩
    have hnum_C : f.num = Polynomial.C f.num.leadingCoeff := by
      conv_lhs => rw [hnum_mono, hdeg_zero]
      rw [pow_zero, mul_one]
    have hmap : algebraMap ℂ (RatFunc ℂ) f.num.leadingCoeff =
        algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C f.num.leadingCoeff) := by
      rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (RatFunc ℂ), Polynomial.algebraMap_eq]
    rw [hmap, ← hnum_C]
    conv_lhs => rw [← f.num_div_denom]
    rw [hden_one, map_one, div_one]
  · rintro ⟨c, rfl⟩
    exact ellScale_algebraMap_C c

/-- **The fixed field of the graded Mahler automorphism is the constant field `ℂ`.**
A fixed element has its support closed under halving and doubling of exponents; a nonzero
exponent then generates an infinite strictly decreasing chain in a well-founded support.
The surviving constant coefficient is fixed by the coefficient scaling, hence constant. -/
theorem mahlerSigma_fixed_iff {f : HahnSeries ℚ (RatFunc ℂ)} :
    mahlerSigma f = f ↔ ∃ c : ℂ, f = HahnSeries.single 0 (algebraMap ℂ (RatFunc ℂ) c) := by
  constructor
  · intro h
    have hcoeff : ∀ q : ℚ, f.coeff (2 * q) = ellScale (f.coeff q) := by
      intro q
      conv_lhs => rw [← h]
      exact mahlerSigma_coeff f q
    have hsupp : ∀ q : ℚ, q ≠ 0 → f.coeff q = 0 := by
      intro q hq
      by_contra hc
      rcases lt_or_gt_of_ne hq with hneg | hpos
      · have hchain : ∀ n : ℕ, f.coeff ((2:ℚ) ^ n * q) ≠ 0 := by
          intro n
          induction n with
          | zero => simpa using hc
          | succ n ihn =>
            have h2 : (2:ℚ) ^ (n+1) * q = 2 * ((2:ℚ) ^ n * q) := by ring
            rw [h2, hcoeff]
            intro h0
            apply ihn
            have := congrArg ellScale.symm h0
            simpa using this
        have hanti : StrictAnti (fun n : ℕ => (2:ℚ) ^ n * q) := by
          apply strictAnti_nat_of_succ_lt
          intro n
          have h2 : (0:ℚ) < (2:ℚ) ^ n := by positivity
          have h3 : (2:ℚ) ^ (n + 1) = 2 * 2 ^ n := by ring
          show (2:ℚ) ^ (n + 1) * q < 2 ^ n * q
          rw [h3]
          nlinarith
        exact (Set.isWF_iff_no_descending_seq.mp f.isPWO_support'.isWF) _ hanti
          (fun n => Function.mem_support.mpr (hchain n))
      · have hchain : ∀ n : ℕ, f.coeff (q / 2 ^ n) ≠ 0 := by
          intro n
          induction n with
          | zero => simpa using hc
          | succ n ihn =>
            intro h0
            apply ihn
            have h2 : q / 2 ^ n = 2 * (q / 2 ^ (n+1)) := by
              field_simp
              ring
            rw [h2, hcoeff, h0, map_zero]
        have hanti : StrictAnti (fun n : ℕ => q / (2:ℚ) ^ n) := by
          apply strictAnti_nat_of_succ_lt
          intro n
          show q / (2:ℚ) ^ (n + 1) < q / 2 ^ n
          apply div_lt_div_of_pos_left hpos (by positivity)
          have h2 : (0:ℚ) < (2:ℚ) ^ n := by positivity
          have h3 : (2:ℚ) ^ (n + 1) = 2 * 2 ^ n := by ring
          rw [h3]
          nlinarith
        exact (Set.isWF_iff_no_descending_seq.mp f.isPWO_support'.isWF) _ hanti
          (fun n => Function.mem_support.mpr (hchain n))
    have hf0 : ellScale (f.coeff 0) = f.coeff 0 := by
      have h0 := hcoeff 0
      rw [mul_zero] at h0
      exact h0.symm
    obtain ⟨c, hc⟩ := ellScale_fixed_iff.mp hf0
    refine ⟨c, ?_⟩
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · rw [HahnSeries.coeff_single_same, ← hc]
    · rw [hsupp q hq, HahnSeries.coeff_single_of_ne hq]
  · rintro ⟨c, rfl⟩
    rw [mahlerSigma_single, mul_zero, ellScale_algebraMap_C]

/-! ## The velocity jet inside the carrier -/

/-- Coefficient base change from `ℂ` to rational functions on Hahn series. -/
def hahnBaseChange : HahnSeries ℚ ℂ →+* HahnSeries ℚ (RatFunc ℂ) where
  toFun f := f.map (algebraMap ℂ (RatFunc ℂ))
  map_zero' := by
    ext q
    show algebraMap ℂ (RatFunc ℂ) ((0 : HahnSeries ℚ ℂ).coeff q) =
      (0 : HahnSeries ℚ (RatFunc ℂ)).coeff q
    simp
  map_one' := by
    ext q
    show algebraMap ℂ (RatFunc ℂ) ((1 : HahnSeries ℚ ℂ).coeff q) =
      (1 : HahnSeries ℚ (RatFunc ℂ)).coeff q
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    rcases eq_or_ne q 0 with rfl | hq
    · rw [if_pos rfl, if_pos rfl, map_one]
    · rw [if_neg hq, if_neg hq, map_zero]
  map_add' := by
    intro x y
    ext q
    show algebraMap ℂ (RatFunc ℂ) ((x + y).coeff q) =
      (x.map (algebraMap ℂ (RatFunc ℂ)) + y.map (algebraMap ℂ (RatFunc ℂ))).coeff q
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add, map_add]
    rfl
  map_mul' := by
    intro x y
    exact HahnSeries.map_mul ((algebraMap ℂ (RatFunc ℂ)) : ℂ →ₙ+* RatFunc ℂ)

/-- Formal power series inside the graded Mahler carrier. -/
def toMahlerCarrier : PowerSeries ℂ →+* HahnSeries ℚ (RatFunc ℂ) :=
  hahnBaseChange.comp (HahnSeries.ofPowerSeries ℚ ℂ)

theorem toMahlerCarrier_coeff_natCast (f : PowerSeries ℂ) (n : ℕ) :
    (toMahlerCarrier f).coeff (n : ℚ) =
      algebraMap ℂ (RatFunc ℂ) ((PowerSeries.coeff n) f) := by
  show algebraMap ℂ (RatFunc ℂ) ((HahnSeries.ofPowerSeries ℚ ℂ f).coeff (n : ℚ)) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff]

theorem toMahlerCarrier_coeff_of_ne (f : PowerSeries ℂ) {q : ℚ} (hq : ∀ n : ℕ, (n : ℚ) ≠ q) :
    (toMahlerCarrier f).coeff q = 0 := by
  show algebraMap ℂ (RatFunc ℂ) ((HahnSeries.ofPowerSeries ℚ ℂ f).coeff q) = 0
  rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range, map_zero]
  rintro ⟨n, hn⟩
  exact hq n hn

/-- The base variable is the image of the power-series variable. -/
theorem toMahlerCarrier_X : toMahlerCarrier PowerSeries.X = mahlerT := by
  show hahnBaseChange (HahnSeries.ofPowerSeries ℚ ℂ PowerSeries.X) = mahlerT
  rw [HahnSeries.ofPowerSeries_X]
  ext x
  show algebraMap ℂ (RatFunc ℂ) ((HahnSeries.single (1:ℚ) (1:ℂ)).coeff x) =
    (HahnSeries.single (1:ℚ) (1:RatFunc ℂ)).coeff x
  rw [HahnSeries.coeff_single, HahnSeries.coeff_single]
  rcases eq_or_ne x 1 with rfl | hx
  · rw [if_pos rfl, if_pos rfl, map_one]
  · rw [if_neg hx, if_neg hx, map_zero]

/-- The graded Mahler automorphism restricts to dyadic substitution on power series. -/
theorem mahlerSigma_toMahlerCarrier (f : PowerSeries ℂ) :
    mahlerSigma (toMahlerCarrier f) = toMahlerCarrier (dyadicSubst f) := by
  ext q
  have hσ : (mahlerSigma (toMahlerCarrier f)).coeff q =
      ellScale ((toMahlerCarrier f).coeff (q / 2)) := mahlerSigmaHom_coeff' _ q
  rw [hσ]
  by_cases hq : ∃ n : ℕ, (n : ℚ) = q
  · obtain ⟨n, rfl⟩ := hq
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
    · subst hm
      have hhalf : ((m + m : ℕ) : ℚ) / 2 = (m : ℚ) := by push_cast; ring
      rw [hhalf, toMahlerCarrier_coeff_natCast, toMahlerCarrier_coeff_natCast,
        ellScale_algebraMap_C]
      congr 1
      rw [show m + m = 2 * m by ring, coeff_dyadicSubst_even]
    · have hodd' : n % 2 = 1 := Nat.odd_iff.mp hodd
      have hoddq : ∀ k : ℕ, (k : ℚ) ≠ (n : ℚ) / 2 := by
        intro k hk
        have h2 : (n : ℚ) = 2 * k := by
          field_simp at hk
          linarith
        have hn2 : n = 2 * k := by exact_mod_cast h2
        omega
      rw [toMahlerCarrier_coeff_of_ne f hoddq, map_zero, toMahlerCarrier_coeff_natCast,
        coeff_dyadicSubst_odd _ (by omega), map_zero]
  · push Not at hq
    have hq2 : ∀ n : ℕ, (n : ℚ) ≠ q / 2 := by
      intro n hn
      apply hq (2 * n)
      push_cast
      field_simp at hn
      linarith
    rw [toMahlerCarrier_coeff_of_ne f hq2, map_zero, toMahlerCarrier_coeff_of_ne _ hq]

/-- **The velocity jet's Mahler equation in the carrier**: `σ(A) = 2·A − t²`. -/
theorem mahlerSigma_velocity :
    mahlerSigma (toMahlerCarrier velocityJet) =
      2 * toMahlerCarrier velocityJet - mahlerT * mahlerT := by
  rw [mahlerSigma_toMahlerCarrier, dyadicSubst_velocityJet, map_sub]
  congr 1
  · rw [show (2 : PowerSeries ℂ) * velocityJet = velocityJet + velocityJet from two_mul _, map_add,
      two_mul]
  · rw [show (PowerSeries.X : PowerSeries ℂ) ^ 2 = PowerSeries.X * PowerSeries.X from sq PowerSeries.X,
      map_mul, toMahlerCarrier_X]

/-- The eigenvariable is nonzero. -/
theorem mahlerEll_ne_zero : mahlerEll ≠ 0 := by
  rw [mahlerEll]
  intro h
  have hc : ((HahnSeries.single (0:ℚ)) RatFunc.X).coeff 0 =
      (0 : HahnSeries ℚ (RatFunc ℂ)).coeff 0 := by rw [h]
  rw [HahnSeries.coeff_single_same] at hc
  simp at hc
  exact RatFunc.X_ne_zero hc

theorem hahn_two_ne_zero : (2 : HahnSeries ℚ (RatFunc ℂ)) ≠ 0 := by
  intro h
  have hc : ((2 : HahnSeries ℚ (RatFunc ℂ))).coeff 0 =
      (0 : HahnSeries ℚ (RatFunc ℂ)).coeff 0 := by rw [h]
  have h2 : ((2 : HahnSeries ℚ (RatFunc ℂ))).coeff 0 = 2 := by
    rw [show (2 : HahnSeries ℚ (RatFunc ℂ)) = 1 + 1 from by norm_num, HahnSeries.coeff_add,
      HahnSeries.coeff_one, if_pos rfl]
    norm_num
  rw [h2] at hc
  simp at hc

/-- **The normalized velocity is an additive Mahler primitive**:
`σ(A·ℓ⁻¹) = A·ℓ⁻¹ − t²·(2ℓ)⁻¹`. -/
theorem mahlerSigma_velocityHat :
    mahlerSigma (toMahlerCarrier velocityJet * mahlerEll⁻¹) =
      toMahlerCarrier velocityJet * mahlerEll⁻¹ -
        mahlerT * mahlerT * (2 * mahlerEll)⁻¹ := by
  have hinv : mahlerSigma mahlerEll⁻¹ = (mahlerSigma mahlerEll)⁻¹ :=
    map_inv₀ mahlerSigma mahlerEll
  rw [map_mul, hinv, mahlerSigma_velocity, mahlerSigma_mahlerEll]
  field_simp [hahn_two_ne_zero]

end

end GaloisForLFunctions
