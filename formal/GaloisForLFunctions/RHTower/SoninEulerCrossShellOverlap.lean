/-
The non-matching cross-overlap law for even Sonin dilation corners.

The three-factor law treats chains of two Gram entries through a common middle scale.  This
file computes the composite of two mixed shell translations with independent middle scales:
`T(p,q) . T(r,s)` for arbitrary `p,q,r,s > 1`.  Within one polarization the product is again
exact — a windowed shell translation whose ceiling is `min(pa,(pr/q)a)`, whose floor is the
clamp of `max(a,(p/q)a)`, and whose displacement multiplies.  The class of windowed shell
translations is therefore closed under composition modulo compact operators, with genuine zero
divisors: the composite is compact exactly when the intermediate shells are disjoint, i.e.
`pr <= q` or `qs <= r`.  On the overlap region the composite has a nondegenerate two-polarization
initial shell, so it stays at positive distance from the compact ideal.  Composition of Gram
entries is thus the intersect-and-translate law of the half-line shell groupoid.
-/
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

set_option maxHeartbeats 1000000

/-! ### Min, union, and clamp algebra of cutoffs -/

/-- Two physical cutoffs multiply to the cutoff at the minimum radius. -/
theorem evenIndicatorCutoff_mul_min (s t : ℝ) :
    evenIndicatorCutoff s * evenIndicatorCutoff t = evenIndicatorCutoff (min s t) := by
  rcases le_total s t with h | h
  · rw [min_eq_left h]
    exact evenIndicatorCutoff_mul_of_le s t h
  · rw [min_eq_right h]
    exact evenIndicatorCutoff_mul_of_le_rev t s h

/-- Two Fourier cutoffs multiply to the cutoff at the minimum radius. -/
theorem evenFourierCutoff_mul_min (s t : ℝ) :
    evenFourierCutoff s * evenFourierCutoff t = evenFourierCutoff (min s t) := by
  rcases le_total s t with h | h
  · rw [min_eq_left h]
    exact evenFourierCutoff_mul_of_le s t h
  · rw [min_eq_right h]
    exact evenFourierCutoff_mul_of_le_rev t s h

/-- Inclusion–exclusion for physical cutoffs: the union of two central intervals. -/
theorem evenIndicatorCutoff_union (u v : ℝ) :
    evenIndicatorCutoff u + evenIndicatorCutoff v - evenIndicatorCutoff (min u v) =
      evenIndicatorCutoff (max u v) := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
    abel
  · rw [min_eq_right h, max_eq_left h]
    abel

/-- Inclusion–exclusion for Fourier cutoffs. -/
theorem evenFourierCutoff_union (u v : ℝ) :
    evenFourierCutoff u + evenFourierCutoff v - evenFourierCutoff (min u v) =
      evenFourierCutoff (max u v) := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
    abel
  · rw [min_eq_right h, max_eq_left h]
    abel

/-- Lattice clamp identity for the product of two general shells. -/
theorem shellClamp_eq (α₁ β₁ α₂ β₂ : ℝ) (h₁ : α₁ ≤ β₁) (h₂ : α₂ ≤ β₂) :
    max (min β₁ α₂) (min α₁ β₂) = min (max α₁ α₂) (min β₁ β₂) := by
  rw [max_min_distrib_left (min β₁ α₂) α₁ β₂]
  have hleft : max (min β₁ α₂) α₁ = min β₁ (max α₁ α₂) := by
    rw [max_comm, max_min_distrib_left α₁ β₁ α₂, max_eq_right h₁]
  have hright : max (min β₁ α₂) β₂ = β₂ := by
    rw [max_comm, max_min_distrib_left β₂ β₁ α₂, max_eq_left h₂]
    exact min_eq_right (le_max_left β₂ β₁)
  rw [hleft, hright, min_assoc, min_left_comm β₁ (max α₁ α₂) β₂]

/-- General shell product: two physical shells with independent floors and ceilings multiply
to the intersection shell, encoded by a clamped floor. -/
theorem evenIndicatorCutoff_generalShellProduct
    (α₁ β₁ α₂ β₂ : ℝ) (h₁ : α₁ ≤ β₁) (h₂ : α₂ ≤ β₂) :
    (evenIndicatorCutoff β₁ - evenIndicatorCutoff α₁) *
        (evenIndicatorCutoff β₂ - evenIndicatorCutoff α₂) =
      evenIndicatorCutoff (min β₁ β₂) -
        evenIndicatorCutoff (min (max α₁ α₂) (min β₁ β₂)) := by
  rw [sub_mul, mul_sub, mul_sub, evenIndicatorCutoff_mul_min β₁ β₂,
    evenIndicatorCutoff_mul_min β₁ α₂, evenIndicatorCutoff_mul_min α₁ β₂,
    evenIndicatorCutoff_mul_min α₁ α₂]
  have hu : min (min β₁ α₂) (min α₁ β₂) = min α₁ α₂ := by
    rw [min_min_min_comm β₁ α₂ α₁ β₂, min_eq_right h₁, min_eq_left h₂]
  have hun := evenIndicatorCutoff_union (min β₁ α₂) (min α₁ β₂)
  rw [hu, shellClamp_eq α₁ β₁ α₂ β₂ h₁ h₂] at hun
  have hre : evenIndicatorCutoff (min β₁ β₂) - evenIndicatorCutoff (min β₁ α₂) -
      (evenIndicatorCutoff (min α₁ β₂) - evenIndicatorCutoff (min α₁ α₂)) =
      evenIndicatorCutoff (min β₁ β₂) -
        (evenIndicatorCutoff (min β₁ α₂) + evenIndicatorCutoff (min α₁ β₂) -
          evenIndicatorCutoff (min α₁ α₂)) := by
    abel
  rw [hre, hun]

/-- General shell product, Fourier polarization. -/
theorem evenFourierCutoff_generalShellProduct
    (α₁ β₁ α₂ β₂ : ℝ) (h₁ : α₁ ≤ β₁) (h₂ : α₂ ≤ β₂) :
    (evenFourierCutoff β₁ - evenFourierCutoff α₁) *
        (evenFourierCutoff β₂ - evenFourierCutoff α₂) =
      evenFourierCutoff (min β₁ β₂) -
        evenFourierCutoff (min (max α₁ α₂) (min β₁ β₂)) := by
  rw [sub_mul, mul_sub, mul_sub, evenFourierCutoff_mul_min β₁ β₂,
    evenFourierCutoff_mul_min β₁ α₂, evenFourierCutoff_mul_min α₁ β₂,
    evenFourierCutoff_mul_min α₁ α₂]
  have hu : min (min β₁ α₂) (min α₁ β₂) = min α₁ α₂ := by
    rw [min_min_min_comm β₁ α₂ α₁ β₂, min_eq_right h₁, min_eq_left h₂]
  have hun := evenFourierCutoff_union (min β₁ α₂) (min α₁ β₂)
  rw [hu, shellClamp_eq α₁ β₁ α₂ β₂ h₁ h₂] at hun
  have hre : evenFourierCutoff (min β₁ β₂) - evenFourierCutoff (min β₁ α₂) -
      (evenFourierCutoff (min α₁ β₂) - evenFourierCutoff (min α₁ α₂)) =
      evenFourierCutoff (min β₁ β₂) -
        (evenFourierCutoff (min β₁ α₂) + evenFourierCutoff (min α₁ β₂) -
          evenFourierCutoff (min α₁ α₂)) := by
    abel
  rw [hre, hun]

/-- A physical shell below the central cutoff is annihilated by the complement. -/
theorem evenIndicatorShell_mul_complement_eq_zero
    (u v a : ℝ) (hua : u ≤ a) (hva : v ≤ a) :
    (evenIndicatorCutoff u - evenIndicatorCutoff v) * (1 - evenIndicatorCutoff a) = 0 := by
  rw [mul_sub, mul_one, sub_mul, evenIndicatorCutoff_mul_min u a,
    evenIndicatorCutoff_mul_min v a, min_eq_left hua, min_eq_left hva]
  abel

/-- A Fourier shell below the central cutoff is annihilated by the complement. -/
theorem evenFourierShell_mul_complement_eq_zero
    (u v a : ℝ) (hua : u ≤ a) (hva : v ≤ a) :
    (evenFourierCutoff u - evenFourierCutoff v) * (1 - evenFourierCutoff a) = 0 := by
  rw [mul_sub, mul_one, sub_mul, evenFourierCutoff_mul_min u a,
    evenFourierCutoff_mul_min v a, min_eq_left hua, min_eq_left hva]
  abel

/-- Sandwiching a physical shell between central complements lifts both endpoints to the
cutoff. -/
theorem evenIndicatorCutoff_complementSandwich (a u v : ℝ) :
    (1 - evenIndicatorCutoff a) * (evenIndicatorCutoff u - evenIndicatorCutoff v) *
        (1 - evenIndicatorCutoff a) =
      evenIndicatorCutoff (max u a) - evenIndicatorCutoff (max v a) := by
  have h1 : (1 - evenIndicatorCutoff a) * (evenIndicatorCutoff u - evenIndicatorCutoff v) =
      evenIndicatorCutoff u - evenIndicatorCutoff v -
        evenIndicatorCutoff (min a u) + evenIndicatorCutoff (min a v) := by
    rw [sub_mul, one_mul, mul_sub, evenIndicatorCutoff_mul_min a u,
      evenIndicatorCutoff_mul_min a v]
    abel
  have h2 : (evenIndicatorCutoff u - evenIndicatorCutoff v -
      evenIndicatorCutoff (min a u) + evenIndicatorCutoff (min a v)) *
        (1 - evenIndicatorCutoff a) =
      evenIndicatorCutoff u - evenIndicatorCutoff v -
        evenIndicatorCutoff (min a u) + evenIndicatorCutoff (min a v) := by
    rw [mul_sub, mul_one, add_mul, sub_mul, sub_mul, evenIndicatorCutoff_mul_min u a,
      evenIndicatorCutoff_mul_min v a, evenIndicatorCutoff_mul_min (min a u) a,
      evenIndicatorCutoff_mul_min (min a v) a,
      min_eq_left (min_le_left a u), min_eq_left (min_le_left a v),
      min_comm u a, min_comm v a]
    abel
  have h3 : evenIndicatorCutoff (max u a) - evenIndicatorCutoff (max v a) =
      evenIndicatorCutoff u - evenIndicatorCutoff v -
        evenIndicatorCutoff (min a u) + evenIndicatorCutoff (min a v) := by
    rw [← evenIndicatorCutoff_union u a, ← evenIndicatorCutoff_union v a,
      min_comm u a, min_comm v a]
    abel
  rw [h1, h2, ← h3]

/-- Sandwiching a Fourier shell between central complements lifts both endpoints to the
cutoff. -/
theorem evenFourierCutoff_complementSandwich (a u v : ℝ) :
    (1 - evenFourierCutoff a) * (evenFourierCutoff u - evenFourierCutoff v) *
        (1 - evenFourierCutoff a) =
      evenFourierCutoff (max u a) - evenFourierCutoff (max v a) := by
  have h1 : (1 - evenFourierCutoff a) * (evenFourierCutoff u - evenFourierCutoff v) =
      evenFourierCutoff u - evenFourierCutoff v -
        evenFourierCutoff (min a u) + evenFourierCutoff (min a v) := by
    rw [sub_mul, one_mul, mul_sub, evenFourierCutoff_mul_min a u,
      evenFourierCutoff_mul_min a v]
    abel
  have h2 : (evenFourierCutoff u - evenFourierCutoff v -
      evenFourierCutoff (min a u) + evenFourierCutoff (min a v)) *
        (1 - evenFourierCutoff a) =
      evenFourierCutoff u - evenFourierCutoff v -
        evenFourierCutoff (min a u) + evenFourierCutoff (min a v) := by
    rw [mul_sub, mul_one, add_mul, sub_mul, sub_mul, evenFourierCutoff_mul_min u a,
      evenFourierCutoff_mul_min v a, evenFourierCutoff_mul_min (min a u) a,
      evenFourierCutoff_mul_min (min a v) a,
      min_eq_left (min_le_left a u), min_eq_left (min_le_left a v),
      min_comm u a, min_comm v a]
    abel
  have h3 : evenFourierCutoff (max u a) - evenFourierCutoff (max v a) =
      evenFourierCutoff u - evenFourierCutoff v -
        evenFourierCutoff (min a u) + evenFourierCutoff (min a v) := by
    rw [← evenFourierCutoff_union u a, ← evenFourierCutoff_union v a,
      min_comm u a, min_comm v a]
    abel
  rw [h1, h2, ← h3]

/-! ### The cross shell translation -/

/-- Physical branch of the cross shell translation: the composite of two mixed shell
translations with independent middle scales. -/
def evenPhysicalCrossShellTranslation (a p q r s : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenIndicatorCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
      evenIndicatorCutoff
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
    evenDilationCLM ((p⁻¹ * q) * (r⁻¹ * s))
      (mul_pos (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq))
        (mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) (zero_lt_one.trans hs))) *
    (1 - evenIndicatorCutoff a)

/-- Fourier branch of the cross shell translation. -/
def evenFourierCrossShellTranslation (a p q r s : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenFourierCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
      evenFourierCutoff
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
    evenDilationCLM ((p * q⁻¹) * (r * s⁻¹))
      (mul_pos (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq)))
        (mul_pos (zero_lt_one.trans hr) (inv_pos.mpr (zero_lt_one.trans hs)))) *
    (1 - evenFourierCutoff a)

/-- The cross shell translation: compact-quotient normal form of the composite of two mixed
Gram entries with independent middle scales. -/
def evenSoninCrossShellTranslation (a p q r s : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    evenSubspace →L[Complex] evenSubspace :=
  evenPhysicalCrossShellTranslation a p q r s hp hq hr hs +
    evenFourierCrossShellTranslation a p q r s hp hq hr hs

/-- Exact physical cross law: two physical mixed shell translations with independent middle
scales compose to the physical cross shell translation. -/
theorem physicalShellTranslation_cross_mul
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    evenPhysicalMixedShellTranslation a p q hp hq *
        evenPhysicalMixedShellTranslation a r s hr hs =
      evenPhysicalCrossShellTranslation a p q r s hp hq hr hs := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hs0 := zero_lt_one.trans hs
  let A := evenIndicatorCutoff a
  let Ap := evenIndicatorCutoff (p * a)
  let Ar := evenIndicatorCutoff (r * a)
  let Au := evenIndicatorCutoff (((p * q⁻¹) * r) * a)
  let Av := evenIndicatorCutoff ((p * q⁻¹) * a)
  let U₁ := evenDilationCLM (p⁻¹ * q) (mul_pos (inv_pos.mpr hp0) hq0)
  let U₂ := evenDilationCLM (r⁻¹ * s) (mul_pos (inv_pos.mpr hr0) hs0)
  let U₃ := evenDilationCLM ((p⁻¹ * q) * (r⁻¹ * s))
    (mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hr0) hs0))
  have hE : (1 - A) * (Ar - A) = Ar - A :=
    evenIndicatorCutoff_complement_shellProduct (r * a) a a le_rfl (by nlinarith)
  have hmove : U₁ * (Ar - A) = (Au - Av) * U₁ := by
    have hr' := evenDilationCLM_mul_evenIndicatorCutoff (r * a) (p⁻¹ * q)
      (mul_pos (inv_pos.mpr hp0) hq0)
    have ha' := evenDilationCLM_mul_evenIndicatorCutoff a (p⁻¹ * q)
      (mul_pos (inv_pos.mpr hp0) hq0)
    have hsr : (p⁻¹ * q)⁻¹ * (r * a) = ((p * q⁻¹) * r) * a := by field_simp
    have hsa : (p⁻¹ * q)⁻¹ * a = (p * q⁻¹) * a := by field_simp
    rw [hsr] at hr'
    rw [hsa] at ha'
    change U₁ * Ar = Au * U₁ at hr'
    change U₁ * A = Av * U₁ at ha'
    rw [mul_sub, hr', ha', sub_mul]
  have hcomp : U₁ * U₂ = U₃ :=
    evenDilationCLM_mul (p⁻¹ * q) (r⁻¹ * s)
      (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hr0) hs0)
  have hshell : (Ap - A) * (Au - Av) =
      evenIndicatorCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
        evenIndicatorCutoff
          (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a))) := by
    have h₂ : (p * q⁻¹) * a ≤ ((p * q⁻¹) * r) * a := by
      nlinarith [mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) ha]
    exact evenIndicatorCutoff_generalShellProduct a (p * a) ((p * q⁻¹) * a)
      (((p * q⁻¹) * r) * a) (by nlinarith) h₂
  change (Ap - A) * U₁ * (1 - A) * ((Ar - A) * U₂ * (1 - A)) = _
  calc
    (Ap - A) * U₁ * (1 - A) * ((Ar - A) * U₂ * (1 - A)) =
        (Ap - A) * U₁ * ((1 - A) * (Ar - A)) * (U₂ * (1 - A)) := by
      noncomm_ring
    _ = (Ap - A) * (U₁ * (Ar - A)) * (U₂ * (1 - A)) := by
      rw [hE]; noncomm_ring
    _ = (Ap - A) * ((Au - Av) * U₁) * (U₂ * (1 - A)) := by rw [hmove]
    _ = ((Ap - A) * (Au - Av)) * (U₁ * U₂) * (1 - A) := by noncomm_ring
    _ = _ := by
      rw [hshell, hcomp]
      rfl

/-- Exact Fourier cross law. -/
theorem fourierShellTranslation_cross_mul
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    evenFourierMixedShellTranslation a p q hp hq *
        evenFourierMixedShellTranslation a r s hr hs =
      evenFourierCrossShellTranslation a p q r s hp hq hr hs := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hs0 := zero_lt_one.trans hs
  let R := evenFourierCutoff a
  let Rp := evenFourierCutoff (p * a)
  let Rr := evenFourierCutoff (r * a)
  let Ru := evenFourierCutoff (((p * q⁻¹) * r) * a)
  let Rv := evenFourierCutoff ((p * q⁻¹) * a)
  let U₁ := evenDilationCLM (p * q⁻¹) (mul_pos hp0 (inv_pos.mpr hq0))
  let U₂ := evenDilationCLM (r * s⁻¹) (mul_pos hr0 (inv_pos.mpr hs0))
  let U₃ := evenDilationCLM ((p * q⁻¹) * (r * s⁻¹))
    (mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hr0 (inv_pos.mpr hs0)))
  have hE : (1 - R) * (Rr - R) = Rr - R :=
    evenFourierCutoff_complement_shellProduct (r * a) a a le_rfl (by nlinarith)
  have hmove : U₁ * (Rr - R) = (Ru - Rv) * U₁ := by
    have hr' := evenDilationCLM_mul_evenFourierCutoff (r * a) (p * q⁻¹)
      (mul_pos hp0 (inv_pos.mpr hq0))
    have ha' := evenDilationCLM_mul_evenFourierCutoff a (p * q⁻¹)
      (mul_pos hp0 (inv_pos.mpr hq0))
    have hsr : (p * q⁻¹) * (r * a) = ((p * q⁻¹) * r) * a := by ring
    rw [hsr] at hr'
    change U₁ * Rr = Ru * U₁ at hr'
    change U₁ * R = Rv * U₁ at ha'
    rw [mul_sub, hr', ha', sub_mul]
  have hcomp : U₁ * U₂ = U₃ :=
    evenDilationCLM_mul (p * q⁻¹) (r * s⁻¹)
      (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hr0 (inv_pos.mpr hs0))
  have hshell : (Rp - R) * (Ru - Rv) =
      evenFourierCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
        evenFourierCutoff
          (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a))) := by
    have h₂ : (p * q⁻¹) * a ≤ ((p * q⁻¹) * r) * a := by
      nlinarith [mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) ha]
    exact evenFourierCutoff_generalShellProduct a (p * a) ((p * q⁻¹) * a)
      (((p * q⁻¹) * r) * a) (by nlinarith) h₂
  change (Rp - R) * U₁ * (1 - R) * ((Rr - R) * U₂ * (1 - R)) = _
  calc
    (Rp - R) * U₁ * (1 - R) * ((Rr - R) * U₂ * (1 - R)) =
        (Rp - R) * U₁ * ((1 - R) * (Rr - R)) * (U₂ * (1 - R)) := by
      noncomm_ring
    _ = (Rp - R) * (U₁ * (Rr - R)) * (U₂ * (1 - R)) := by
      rw [hE]; noncomm_ring
    _ = (Rp - R) * ((Ru - Rv) * U₁) * (U₂ * (1 - R)) := by rw [hmove]
    _ = ((Rp - R) * (Ru - Rv)) * (U₁ * U₂) * (1 - R) := by noncomm_ring
    _ = _ := by
      rw [hshell, hcomp]
      rfl

/-- **Cross-overlap law.**  The composite of two mixed shell translations with independent
middle scales is, modulo compact operators, the cross shell translation. -/
theorem evenSoninMixedShellTranslation_cross_compactEq
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    evenSoninMixedShellTranslation a p q hp hq *
        evenSoninMixedShellTranslation a r s hr hs =ₖ
      evenSoninCrossShellTranslation a p q r s hp hq hr hs := by
  have hPP := CompactOperatorEq.of_eq
    (physicalShellTranslation_cross_mul a p q r s ha hp hq hr hs)
  have hFF := CompactOperatorEq.of_eq
    (fourierShellTranslation_cross_mul a p q r s ha hp hq hr hs)
  have hPF : evenPhysicalMixedShellTranslation a p q hp hq *
      evenFourierMixedShellTranslation a r s hr hs =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact
      (isCompactOperator_physicalShellTranslation_mul_fourierShellTranslation
        a p q r s ha hp hq hr hs)
  have hFP : evenFourierMixedShellTranslation a p q hp hq *
      evenPhysicalMixedShellTranslation a r s hr hs =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact
      (isCompactOperator_fourierShellTranslation_mul_physicalShellTranslation
        a p q r s ha hp hq hr hs)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add hPP hPF) (CompactOperatorEq.add hFP hFF)
  dsimp only [evenSoninMixedShellTranslation, evenSoninCrossShellTranslation]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

/-- The composite of two actual Sonin quadratic corners with independent middle scales is,
modulo compact operators, the cross shell translation. -/
theorem evenCentralSoninQuadraticCorner_cross_compactEq
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a r s hr hs =ₖ
      evenSoninCrossShellTranslation a p q r s hp hq hr hs :=
  (CompactOperatorEq.mul
    (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a p q ha hp hq)
    (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a r s ha hr hs)).trans
    (evenSoninMixedShellTranslation_cross_compactEq a p q r s ha hp hq hr hs)

/-- Matching middles recover the three-scale shell translation exactly. -/
theorem evenSoninCrossShellTranslation_matching_eq_triple
    (a p q s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hs : 1 < s) :
    evenSoninCrossShellTranslation a p q q s hp hq hq hs =
      evenSoninTripleShellTranslation a p q s hp hs := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hs0 := zero_lt_one.trans hs
  have hceil : ((p * q⁻¹) * q) * a = p * a := by field_simp
  have hUphys : evenDilationCLM ((p⁻¹ * q) * (q⁻¹ * s))
      (mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hq0) hs0)) =
      evenDilationCLM (p⁻¹ * s) (mul_pos (inv_pos.mpr hp0) hs0) := by
    congr 1
    field_simp
  have hUfour : evenDilationCLM ((p * q⁻¹) * (q * s⁻¹))
      (mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hq0 (inv_pos.mpr hs0))) =
      evenDilationCLM (p * s⁻¹) (mul_pos hp0 (inv_pos.mpr hs0)) := by
    congr 1
    field_simp
  dsimp only [evenSoninCrossShellTranslation, evenPhysicalCrossShellTranslation,
    evenFourierCrossShellTranslation, evenSoninTripleShellTranslation,
    evenPhysicalTripleShellTranslation, evenFourierTripleShellTranslation]
  rw [hceil, min_self, hUphys, hUfour]
  have hfloor : min (max a ((p * q⁻¹) * a)) (p * a) = max a ((p * q⁻¹) * a) := by
    apply min_eq_left
    apply max_le (by nlinarith)
    have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
    nlinarith [mul_pos hp0 ha]
  rw [hfloor]

/-! ### The vanishing dichotomy -/

/-- Disjoint intermediate shells force exact vanishing of the cross translation. -/
theorem evenSoninCrossShellTranslation_eq_zero_of_gap
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s)
    (hgap : p * r ≤ q ∨ q * s ≤ r) :
    evenSoninCrossShellTranslation a p q r s hp hq hr hs = 0 := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hs0 := zero_lt_one.trans hs
  rcases hgap with hgap | hgap
  · -- the first middle dominates: the transported ceiling drops below the floor clamp
    have hCa : ((p * q⁻¹) * r) * a ≤ a := by
      have h1 : (((p * q⁻¹) * r) * a) * q = (p * r) * a := by
        field_simp
      have h3 : (p * r) * a ≤ q * a := mul_le_mul_of_nonneg_right hgap ha.le
      have h2 : (((p * q⁻¹) * r) * a) * q ≤ a * q := by
        rw [h1, mul_comm a q]
        exact h3
      exact le_of_mul_le_mul_right h2 hq0
    have hC : min (p * a) (((p * q⁻¹) * r) * a) = ((p * q⁻¹) * r) * a := by
      apply min_eq_right
      nlinarith
    have hfloor : min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) =
        min (p * a) (((p * q⁻¹) * r) * a) := by
      apply min_eq_right
      rw [hC]
      exact le_trans hCa (le_max_left _ _)
    dsimp only [evenSoninCrossShellTranslation, evenPhysicalCrossShellTranslation,
      evenFourierCrossShellTranslation]
    rw [hfloor, sub_self, sub_self, zero_mul, zero_mul, zero_mul, zero_mul, add_zero]
  · -- the second middle dominates: the trailing complement empties the composite
    have hxpa : ((p⁻¹ * q) * (r⁻¹ * s)) * (p * a) = ((q * s) * r⁻¹) * a := by
      field_simp
    have hypa : ((p * q⁻¹) * (r * s⁻¹))⁻¹ * (p * a) = ((q * s) * r⁻¹) * a := by
      field_simp
    have hqsa : ((q * s) * r⁻¹) * a ≤ a := by
      have h1 : (((q * s) * r⁻¹) * a) * r = (q * s) * a := by
        field_simp
      have h3 : (q * s) * a ≤ r * a := mul_le_mul_of_nonneg_right hgap ha.le
      have h2 : (((q * s) * r⁻¹) * a) * r ≤ a * r := by
        rw [h1, mul_comm a r]
        exact h3
      exact le_of_mul_le_mul_right h2 hr0
    have hCle : min (p * a) (((p * q⁻¹) * r) * a) ≤ p * a := min_le_left _ _
    have hΓle : min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) ≤
        min (p * a) (((p * q⁻¹) * r) * a) := min_le_right _ _
    -- physical branch
    have hphys : evenPhysicalCrossShellTranslation a p q r s hp hq hr hs = 0 := by
      dsimp only [evenPhysicalCrossShellTranslation]
      have hx : (0:ℝ) < (p⁻¹ * q) * (r⁻¹ * s) :=
        mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hr0) hs0)
      have hmoveC := evenIndicatorCutoff_mul_evenDilationCLM
        (min (p * a) (((p * q⁻¹) * r) * a)) ((p⁻¹ * q) * (r⁻¹ * s)) hx
      have hmoveΓ := evenIndicatorCutoff_mul_evenDilationCLM
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
        ((p⁻¹ * q) * (r⁻¹ * s)) hx
      have hzero : (evenIndicatorCutoff
          (((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a)) -
          evenIndicatorCutoff
            (((p⁻¹ * q) * (r⁻¹ * s)) *
              min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
          (1 - evenIndicatorCutoff a) = 0 := by
        apply evenIndicatorShell_mul_complement_eq_zero
        · calc ((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a) ≤
              ((p⁻¹ * q) * (r⁻¹ * s)) * (p * a) :=
                mul_le_mul_of_nonneg_left hCle hx.le
            _ = ((q * s) * r⁻¹) * a := hxpa
            _ ≤ a := hqsa
        · calc ((p⁻¹ * q) * (r⁻¹ * s)) *
              min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) ≤
              ((p⁻¹ * q) * (r⁻¹ * s)) * (p * a) :=
                mul_le_mul_of_nonneg_left (le_trans hΓle hCle) hx.le
            _ = ((q * s) * r⁻¹) * a := hxpa
            _ ≤ a := hqsa
      calc (evenIndicatorCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
            evenIndicatorCutoff
              (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
            evenDilationCLM ((p⁻¹ * q) * (r⁻¹ * s)) _ * (1 - evenIndicatorCutoff a) =
          evenDilationCLM ((p⁻¹ * q) * (r⁻¹ * s)) hx *
            ((evenIndicatorCutoff
              (((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a)) -
              evenIndicatorCutoff
                (((p⁻¹ * q) * (r⁻¹ * s)) *
                  min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
              (1 - evenIndicatorCutoff a)) := by
            rw [sub_mul, hmoveC, hmoveΓ, ← mul_sub, mul_assoc]
        _ = 0 := by rw [hzero, mul_zero]
    -- Fourier branch
    have hfour : evenFourierCrossShellTranslation a p q r s hp hq hr hs = 0 := by
      dsimp only [evenFourierCrossShellTranslation]
      have hy : (0:ℝ) < (p * q⁻¹) * (r * s⁻¹) :=
        mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hr0 (inv_pos.mpr hs0))
      have hmoveC := evenFourierCutoff_mul_evenDilationCLM
        (min (p * a) (((p * q⁻¹) * r) * a)) ((p * q⁻¹) * (r * s⁻¹)) hy
      have hmoveΓ := evenFourierCutoff_mul_evenDilationCLM
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
        ((p * q⁻¹) * (r * s⁻¹)) hy
      have hzero : (evenFourierCutoff
          (((p * q⁻¹) * (r * s⁻¹))⁻¹ * min (p * a) (((p * q⁻¹) * r) * a)) -
          evenFourierCutoff
            (((p * q⁻¹) * (r * s⁻¹))⁻¹ *
              min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
          (1 - evenFourierCutoff a) = 0 := by
        apply evenFourierShell_mul_complement_eq_zero
        · calc ((p * q⁻¹) * (r * s⁻¹))⁻¹ * min (p * a) (((p * q⁻¹) * r) * a) ≤
              ((p * q⁻¹) * (r * s⁻¹))⁻¹ * (p * a) :=
                mul_le_mul_of_nonneg_left hCle (inv_pos.mpr hy).le
            _ = ((q * s) * r⁻¹) * a := hypa
            _ ≤ a := hqsa
        · calc ((p * q⁻¹) * (r * s⁻¹))⁻¹ *
              min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) ≤
              ((p * q⁻¹) * (r * s⁻¹))⁻¹ * (p * a) :=
                mul_le_mul_of_nonneg_left (le_trans hΓle hCle) (inv_pos.mpr hy).le
            _ = ((q * s) * r⁻¹) * a := hypa
            _ ≤ a := hqsa
      calc (evenFourierCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
            evenFourierCutoff
              (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
            evenDilationCLM ((p * q⁻¹) * (r * s⁻¹)) _ * (1 - evenFourierCutoff a) =
          evenDilationCLM ((p * q⁻¹) * (r * s⁻¹)) hy *
            ((evenFourierCutoff
              (((p * q⁻¹) * (r * s⁻¹))⁻¹ * min (p * a) (((p * q⁻¹) * r) * a)) -
              evenFourierCutoff
                (((p * q⁻¹) * (r * s⁻¹))⁻¹ *
                  min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
              (1 - evenFourierCutoff a)) := by
            rw [sub_mul, hmoveC, hmoveΓ, ← mul_sub, mul_assoc]
        _ = 0 := by rw [hzero, mul_zero]
    dsimp only [evenSoninCrossShellTranslation]
    rw [hphys, hfour, add_zero]

/-- Disjoint intermediate shells force compact vanishing of the actual corner composite. -/
theorem evenCentralSoninCrossCorner_compactEq_zero_of_gap
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s)
    (hgap : p * r ≤ q ∨ q * s ≤ r) :
    evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a r s hr hs =ₖ 0 :=
  (evenCentralSoninQuadraticCorner_cross_compactEq a p q r s ha hp hq hr hs).trans
    (CompactOperatorEq.of_eq
      (evenSoninCrossShellTranslation_eq_zero_of_gap a p q r s ha hp hq hr hs hgap))

/-! ### Windowed adjoints and initial projections -/

/-- Inverse dilation composes with the dilation to the identity. -/
theorem evenDilationCLM_inv_mul (x : ℝ) (hx : 0 < x) :
    evenDilationCLM x⁻¹ (inv_pos.mpr hx) * evenDilationCLM x hx =
      (1 : evenSubspace →L[Complex] evenSubspace) := by
  rw [evenDilationCLM_mul]
  have h1 : evenDilationCLM (x⁻¹ * x) (mul_pos (inv_pos.mpr hx) hx) =
      evenDilationCLM 1 zero_lt_one := by
    congr 1
    field_simp
  rw [h1, evenDilationCLM_one]

/-- A physical shell moves across a dilation by scaling both endpoints. -/
theorem evenIndicatorShell_mul_dilation (u v x : ℝ) (hx : 0 < x) :
    (evenIndicatorCutoff u - evenIndicatorCutoff v) * evenDilationCLM x hx =
      evenDilationCLM x hx *
        (evenIndicatorCutoff (x * u) - evenIndicatorCutoff (x * v)) := by
  rw [sub_mul, evenIndicatorCutoff_mul_evenDilationCLM u x hx,
    evenIndicatorCutoff_mul_evenDilationCLM v x hx, ← mul_sub]

/-- A Fourier shell moves across a dilation by inverse-scaling both endpoints. -/
theorem evenFourierShell_mul_dilation (u v y : ℝ) (hy : 0 < y) :
    (evenFourierCutoff u - evenFourierCutoff v) * evenDilationCLM y hy =
      evenDilationCLM y hy *
        (evenFourierCutoff (y⁻¹ * u) - evenFourierCutoff (y⁻¹ * v)) := by
  rw [sub_mul, evenFourierCutoff_mul_evenDilationCLM u y hy,
    evenFourierCutoff_mul_evenDilationCLM v y hy, ← mul_sub]

/-- Adjoint of a windowed physical shell translation. -/
theorem physicalWindow_adjoint (a u v x : ℝ) (hx : 0 < x) :
    ((evenIndicatorCutoff u - evenIndicatorCutoff v) * evenDilationCLM x hx *
        (1 - evenIndicatorCutoff a))† =
      (1 - evenIndicatorCutoff a) *
        (evenDilationCLM x⁻¹ (inv_pos.mpr hx) *
          (evenIndicatorCutoff u - evenIndicatorCutoff v)) := by
  rw [adjoint_mul_clm, adjoint_mul_clm, adjoint_sub_clm, adjoint_sub_clm,
    ContinuousLinearMap.adjoint_one, adjoint_evenIndicatorCutoff a,
    adjoint_evenIndicatorCutoff u, adjoint_evenIndicatorCutoff v,
    adjoint_evenDilationCLM x hx]

/-- Adjoint of a windowed Fourier shell translation. -/
theorem fourierWindow_adjoint (a u v y : ℝ) (hy : 0 < y) :
    ((evenFourierCutoff u - evenFourierCutoff v) * evenDilationCLM y hy *
        (1 - evenFourierCutoff a))† =
      (1 - evenFourierCutoff a) *
        (evenDilationCLM y⁻¹ (inv_pos.mpr hy) *
          (evenFourierCutoff u - evenFourierCutoff v)) := by
  rw [adjoint_mul_clm, adjoint_mul_clm, adjoint_sub_clm, adjoint_sub_clm,
    ContinuousLinearMap.adjoint_one, adjoint_evenFourierCutoff a,
    adjoint_evenFourierCutoff u, adjoint_evenFourierCutoff v,
    adjoint_evenDilationCLM y hy]

/-- Exact initial projection of a windowed physical shell translation. -/
theorem physicalWindow_adjoint_mul (a u v x : ℝ) (hx : 0 < x) (hvu : v ≤ u) :
    ((evenIndicatorCutoff u - evenIndicatorCutoff v) * evenDilationCLM x hx *
        (1 - evenIndicatorCutoff a))† *
      ((evenIndicatorCutoff u - evenIndicatorCutoff v) * evenDilationCLM x hx *
        (1 - evenIndicatorCutoff a)) =
      evenIndicatorCutoff (max (x * u) a) - evenIndicatorCutoff (max (x * v) a) := by
  rw [physicalWindow_adjoint a u v x hx]
  simp only [mul_assoc]
  rw [← mul_assoc (evenIndicatorCutoff u - evenIndicatorCutoff v)
      (evenIndicatorCutoff u - evenIndicatorCutoff v)
      (evenDilationCLM x hx * (1 - evenIndicatorCutoff a)),
    evenIndicatorShell_mul_self v u hvu,
    ← mul_assoc (evenIndicatorCutoff u - evenIndicatorCutoff v)
      (evenDilationCLM x hx) (1 - evenIndicatorCutoff a),
    evenIndicatorShell_mul_dilation u v x hx,
    mul_assoc (evenDilationCLM x hx)
      (evenIndicatorCutoff (x * u) - evenIndicatorCutoff (x * v))
      (1 - evenIndicatorCutoff a),
    ← mul_assoc (evenDilationCLM x⁻¹ (inv_pos.mpr hx)) (evenDilationCLM x hx) _,
    evenDilationCLM_inv_mul x hx, one_mul, ← mul_assoc]
  exact evenIndicatorCutoff_complementSandwich a (x * u) (x * v)

/-- Exact initial projection of a windowed Fourier shell translation. -/
theorem fourierWindow_adjoint_mul (a u v y : ℝ) (hy : 0 < y) (hvu : v ≤ u) :
    ((evenFourierCutoff u - evenFourierCutoff v) * evenDilationCLM y hy *
        (1 - evenFourierCutoff a))† *
      ((evenFourierCutoff u - evenFourierCutoff v) * evenDilationCLM y hy *
        (1 - evenFourierCutoff a)) =
      evenFourierCutoff (max (y⁻¹ * u) a) - evenFourierCutoff (max (y⁻¹ * v) a) := by
  rw [fourierWindow_adjoint a u v y hy]
  simp only [mul_assoc]
  rw [← mul_assoc (evenFourierCutoff u - evenFourierCutoff v)
      (evenFourierCutoff u - evenFourierCutoff v)
      (evenDilationCLM y hy * (1 - evenFourierCutoff a)),
    evenFourierShell_mul_self v u hvu,
    ← mul_assoc (evenFourierCutoff u - evenFourierCutoff v)
      (evenDilationCLM y hy) (1 - evenFourierCutoff a),
    evenFourierShell_mul_dilation u v y hy,
    mul_assoc (evenDilationCLM y hy)
      (evenFourierCutoff (y⁻¹ * u) - evenFourierCutoff (y⁻¹ * v))
      (1 - evenFourierCutoff a),
    ← mul_assoc (evenDilationCLM y⁻¹ (inv_pos.mpr hy)) (evenDilationCLM y hy) _,
    evenDilationCLM_inv_mul y hy, one_mul, ← mul_assoc]
  exact evenFourierCutoff_complementSandwich a (y⁻¹ * u) (y⁻¹ * v)

/-- An adjoint-shaped physical window followed by a Fourier window is compact. -/
theorem isCompactOperator_physicalCoWindow_mul_fourierWindow
    (a u v d e z y : ℝ) (hu : 0 < u) (hv : 0 < v) (hz : 0 < z) (hy : 0 < y) :
    IsCompactOperator
      (((1 - evenIndicatorCutoff a) * (evenDilationCLM z hz *
          (evenIndicatorCutoff u - evenIndicatorCutoff v)) *
        ((evenFourierCutoff d - evenFourierCutoff e) * evenDilationCLM y hy *
          (1 - evenFourierCutoff a)) : evenSubspace →L[Complex] evenSubspace)) := by
  have hmid := isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff u v d e hu hv
  have heq : ((1 - evenIndicatorCutoff a) * (evenDilationCLM z hz *
      (evenIndicatorCutoff u - evenIndicatorCutoff v)) *
      ((evenFourierCutoff d - evenFourierCutoff e) * evenDilationCLM y hy *
        (1 - evenFourierCutoff a)) : evenSubspace →L[Complex] evenSubspace) =
      ((1 - evenIndicatorCutoff a) * evenDilationCLM z hz) *
        ((evenIndicatorCutoff u - evenIndicatorCutoff v) *
          (evenFourierCutoff d - evenFourierCutoff e)) *
        (evenDilationCLM y hy * (1 - evenFourierCutoff a)) := by
    simp only [mul_assoc]
  rw [heq]
  exact ((hmid.clm_comp
      ((1 - evenIndicatorCutoff a) * evenDilationCLM z hz)).comp_clm
    (evenDilationCLM y hy * (1 - evenFourierCutoff a)))

/-- An adjoint-shaped Fourier window followed by a physical window is compact. -/
theorem isCompactOperator_fourierCoWindow_mul_physicalWindow
    (a u v d e z y : ℝ) (hu : 0 < u) (hv : 0 < v) (hz : 0 < z) (hy : 0 < y) :
    IsCompactOperator
      (((1 - evenFourierCutoff a) * (evenDilationCLM z hz *
          (evenFourierCutoff u - evenFourierCutoff v)) *
        ((evenIndicatorCutoff d - evenIndicatorCutoff e) * evenDilationCLM y hy *
          (1 - evenIndicatorCutoff a)) : evenSubspace →L[Complex] evenSubspace)) := by
  have hmid := isCompactOperator_evenFourierDiff_mul_evenIndicatorDiff u v d e hu hv
  have heq : ((1 - evenFourierCutoff a) * (evenDilationCLM z hz *
      (evenFourierCutoff u - evenFourierCutoff v)) *
      ((evenIndicatorCutoff d - evenIndicatorCutoff e) * evenDilationCLM y hy *
        (1 - evenIndicatorCutoff a)) : evenSubspace →L[Complex] evenSubspace) =
      ((1 - evenFourierCutoff a) * evenDilationCLM z hz) *
        ((evenFourierCutoff u - evenFourierCutoff v) *
          (evenIndicatorCutoff d - evenIndicatorCutoff e)) *
        (evenDilationCLM y hy * (1 - evenIndicatorCutoff a)) := by
    simp only [mul_assoc]
  rw [heq]
  exact ((hmid.clm_comp
      ((1 - evenFourierCutoff a) * evenDilationCLM z hz)).comp_clm
    (evenDilationCLM y hy * (1 - evenIndicatorCutoff a)))

/-! ### Polar data and the vanishing dichotomy -/

/-- Initial Calkin projection of the cross translation: the two-polarization shell carried by
the intermediate overlap, pulled back to the source scale. -/
theorem evenSoninCrossShellTranslation_adjoint_mul_compactEq_shell
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    (evenSoninCrossShellTranslation a p q r s hp hq hr hs)† *
        evenSoninCrossShellTranslation a p q r s hp hq hr hs =ₖ
      evenTwoPolarizationShell
        (max (((p⁻¹ * q) * (r⁻¹ * s)) *
          min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a))) a)
        (max (((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a)) a) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hs0 := zero_lt_one.trans hs
  have hx : (0:ℝ) < (p⁻¹ * q) * (r⁻¹ * s) :=
    mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hr0) hs0)
  have hy : (0:ℝ) < (p * q⁻¹) * (r * s⁻¹) :=
    mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hr0 (inv_pos.mpr hs0))
  have hC0 : 0 < min (p * a) (((p * q⁻¹) * r) * a) :=
    lt_min (by nlinarith) (by positivity)
  have hΓ0 : 0 < min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) :=
    lt_min (lt_of_lt_of_le ha (le_max_left _ _)) hC0
  have hΓC : min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) ≤
      min (p * a) (((p * q⁻¹) * r) * a) := min_le_right _ _
  have hyinv : ((p * q⁻¹) * (r * s⁻¹))⁻¹ = (p⁻¹ * q) * (r⁻¹ * s) := by
    field_simp
  have c1 := physicalWindow_adjoint_mul a
    (min (p * a) (((p * q⁻¹) * r) * a))
    (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
    ((p⁻¹ * q) * (r⁻¹ * s)) hx hΓC
  have c4 := fourierWindow_adjoint_mul a
    (min (p * a) (((p * q⁻¹) * r) * a))
    (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
    ((p * q⁻¹) * (r * s⁻¹)) hy hΓC
  rw [hyinv] at c4
  have hadjP := physicalWindow_adjoint a
    (min (p * a) (((p * q⁻¹) * r) * a))
    (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
    ((p⁻¹ * q) * (r⁻¹ * s)) hx
  have hadjF := fourierWindow_adjoint a
    (min (p * a) (((p * q⁻¹) * r) * a))
    (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
    ((p * q⁻¹) * (r * s⁻¹)) hy
  have c2 : ((evenIndicatorCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
      evenIndicatorCutoff
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
      evenDilationCLM ((p⁻¹ * q) * (r⁻¹ * s))
        (mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hr0) hs0)) *
      (1 - evenIndicatorCutoff a))† *
      ((evenFourierCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
        evenFourierCutoff
          (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
        evenDilationCLM ((p * q⁻¹) * (r * s⁻¹))
          (mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hr0 (inv_pos.mpr hs0))) *
        (1 - evenFourierCutoff a)) =ₖ 0 := by
    rw [hadjP]
    exact compactOperatorEq_zero_of_isCompact
      (isCompactOperator_physicalCoWindow_mul_fourierWindow a
        (min (p * a) (((p * q⁻¹) * r) * a))
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
        (min (p * a) (((p * q⁻¹) * r) * a))
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
        ((p⁻¹ * q) * (r⁻¹ * s))⁻¹ ((p * q⁻¹) * (r * s⁻¹)) hC0 hΓ0
        (inv_pos.mpr hx) hy)
  have c3 : ((evenFourierCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
      evenFourierCutoff
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
      evenDilationCLM ((p * q⁻¹) * (r * s⁻¹))
        (mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hr0 (inv_pos.mpr hs0))) *
      (1 - evenFourierCutoff a))† *
      ((evenIndicatorCutoff (min (p * a) (((p * q⁻¹) * r) * a)) -
        evenIndicatorCutoff
          (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))) *
        evenDilationCLM ((p⁻¹ * q) * (r⁻¹ * s))
          (mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hr0) hs0)) *
        (1 - evenIndicatorCutoff a)) =ₖ 0 := by
    rw [hadjF]
    exact compactOperatorEq_zero_of_isCompact
      (isCompactOperator_fourierCoWindow_mul_physicalWindow a
        (min (p * a) (((p * q⁻¹) * r) * a))
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
        (min (p * a) (((p * q⁻¹) * r) * a))
        (min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)))
        ((p * q⁻¹) * (r * s⁻¹))⁻¹ ((p⁻¹ * q) * (r⁻¹ * s)) hC0 hΓ0
        (inv_pos.mpr hy) hx)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add (CompactOperatorEq.of_eq c1) c2)
    (CompactOperatorEq.add c3 (CompactOperatorEq.of_eq c4))
  dsimp only [evenSoninCrossShellTranslation, evenPhysicalCrossShellTranslation,
    evenFourierCrossShellTranslation, evenTwoPolarizationShell]
  rw [adjoint_add_clm, add_mul, mul_add, mul_add]
  refine hsum.trans (CompactOperatorEq.of_eq ?_)
  rw [add_zero, zero_add]

/-- **Vanishing dichotomy.**  The composite of two Sonin quadratic corners with independent
middle scales is compact exactly when the intermediate shells are disjoint. -/
theorem evenCentralSoninCrossCorner_compactEq_zero_iff
    (a p q r s : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hs : 1 < s) :
    (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a r s hr hs =ₖ 0) ↔
      p * r ≤ q ∨ q * s ≤ r := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hs0 := zero_lt_one.trans hs
  constructor
  · intro h
    by_contra hgap
    rw [not_or] at hgap
    obtain ⟨h1', h2'⟩ := hgap
    have hq1 : q < p * r := not_le.mp h1'
    have hr1 : r < q * s := not_le.mp h2'
    have hcross0 : evenSoninCrossShellTranslation a p q r s hp hq hr hs =ₖ 0 :=
      (evenCentralSoninQuadraticCorner_cross_compactEq
        a p q r s ha hp hq hr hs).symm.trans h
    have hadj0 : (evenSoninCrossShellTranslation a p q r s hp hq hr hs)† *
        evenSoninCrossShellTranslation a p q r s hp hq hr hs =ₖ 0 :=
      (CompactOperatorEq.left_mul
        ((evenSoninCrossShellTranslation a p q r s hp hq hr hs)†) hcross0).trans
        (CompactOperatorEq.of_eq (mul_zero _))
    have hshell0 := (evenSoninCrossShellTranslation_adjoint_mul_compactEq_shell
      a p q r s ha hp hq hr hs).symm.trans hadj0
    have hx : (0:ℝ) < (p⁻¹ * q) * (r⁻¹ * s) :=
      mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hr0) hs0)
    have haC : a < ((p * q⁻¹) * r) * a := by
      have heq : (((p * q⁻¹) * r) * a) * q = (p * r) * a := by
        field_simp
      have h3 : a * q < (((p * q⁻¹) * r) * a) * q := by
        rw [heq, mul_comm a q]
        exact mul_lt_mul_of_pos_right hq1 ha
      exact lt_of_mul_lt_mul_right h3 hq0.le
    have hmaxlt : max a ((p * q⁻¹) * a) < min (p * a) (((p * q⁻¹) * r) * a) := by
      apply max_lt
      · exact lt_min (by nlinarith) haC
      · apply lt_min
        · have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
          nlinarith [mul_pos hp0 ha]
        · nlinarith [mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) ha]
    have hΓltC : min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) <
        min (p * a) (((p * q⁻¹) * r) * a) := by
      rw [min_eq_left hmaxlt.le]
      exact hmaxlt
    have haxC : a < ((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a) := by
      have hmin : ((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a) =
          min (((q * s) * r⁻¹) * a) (s * a) := by
        rw [mul_min_of_nonneg _ _ hx.le]
        congr 1
        · field_simp
        · field_simp
      rw [hmin]
      apply lt_min
      · have heq : (((q * s) * r⁻¹) * a) * r = (q * s) * a := by
          field_simp
        have h3 : a * r < (((q * s) * r⁻¹) * a) * r := by
          rw [heq, mul_comm a r]
          exact mul_lt_mul_of_pos_right hr1 ha
        exact lt_of_mul_lt_mul_right h3 hr0.le
      · nlinarith
    have hxΓC : ((p⁻¹ * q) * (r⁻¹ * s)) *
        min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a)) <
        ((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a) :=
      mul_lt_mul_of_pos_left hΓltC hx
    have hf0 : 0 < max (((p⁻¹ * q) * (r⁻¹ * s)) *
        min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a))) a :=
      lt_of_lt_of_le ha (le_max_right _ _)
    have hlt : max (((p⁻¹ * q) * (r⁻¹ * s)) *
        min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a))) a <
        max (((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a)) a :=
      lt_of_lt_of_le (max_lt hxΓC haxC) (le_max_left _ _)
    exact not_isCompactOperator_evenTwoPolarizationShell
      (max (((p⁻¹ * q) * (r⁻¹ * s)) *
        min (max a ((p * q⁻¹) * a)) (min (p * a) (((p * q⁻¹) * r) * a))) a)
      (max (((p⁻¹ * q) * (r⁻¹ * s)) * min (p * a) (((p * q⁻¹) * r) * a)) a) hf0 hlt
      (by simpa only [CompactOperatorEq, sub_zero] using hshell0)
  · intro h
    exact evenCentralSoninCrossCorner_compactEq_zero_of_gap a p q r s ha hp hq hr hs h

end RHTower
