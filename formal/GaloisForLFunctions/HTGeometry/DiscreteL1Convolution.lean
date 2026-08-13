import Mathlib

/-!
# `ℓ¹` convolution of coefficient families on a discrete group

Coefficient families on a discrete additive group convolve by
`(α ⋆ β) ν = ∑' μ, α μ · β (ν - μ)`.  The quantitative layer lives in `ℝ≥0∞`, where every sum
exists and Tonelli is free: the majorant convolution of `‖·‖ₑ`-families dominates the norm of the
complex convolution coefficientwise, its total mass is exactly multiplicative
(the discrete Young identity), majorant powers have mass exactly `M^k`, and the Neumann kernel
`∑ₖ s^{⋆k}` has mass exactly `(1 - M)⁻¹`.

On the complex side, the alternating Neumann series of a kernel of mass `< 1` is summable, is
dominated coefficientwise by the Neumann kernel of any majorant, and is a two-sided convolution
inverse of `δ₀ + r` — the geometric `ℓ¹` resolvent.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal

variable {G : Type*} [AddCommGroup G]

/-- Discrete convolution of complex coefficient families. -/
def discreteConv (α β : G → ℂ) (ν : G) : ℂ := ∑' μ, α μ * β (ν - μ)

/-- The `ℝ≥0∞`-valued majorant convolution. -/
def discreteEConv (s t : G → ℝ≥0∞) (ν : G) : ℝ≥0∞ := ∑' μ, s μ * t (ν - μ)

/-- The `ℓ¹` mass of a majorant family. -/
def discreteMass (s : G → ℝ≥0∞) : ℝ≥0∞ := ∑' ν, s ν

omit [AddCommGroup G] in
theorem le_discreteMass (s : G → ℝ≥0∞) (ν : G) : s ν ≤ discreteMass s :=
  ENNReal.le_tsum ν

/-- The complex convolution is dominated coefficientwise by the majorant convolution of the
enorm families. -/
theorem enorm_discreteConv_le (α β : G → ℂ) (ν : G) :
    ‖discreteConv α β ν‖ₑ
      ≤ discreteEConv (fun μ => ‖α μ‖ₑ) (fun μ => ‖β μ‖ₑ) ν := by
  refine le_trans enorm_tsum_le_tsum_enorm (le_of_eq (tsum_congr fun μ => ?_))
  rw [enorm_mul]

theorem discreteEConv_mono {s₁ s₂ t₁ t₂ : G → ℝ≥0∞} (hs : ∀ ν, s₁ ν ≤ s₂ ν)
    (ht : ∀ ν, t₁ ν ≤ t₂ ν) (ν : G) : discreteEConv s₁ t₁ ν ≤ discreteEConv s₂ t₂ ν :=
  ENNReal.tsum_le_tsum fun μ => mul_le_mul' (hs μ) (ht (ν - μ))

/-- **The discrete Young identity**: the mass of a majorant convolution is exactly the product
of the masses.  Tonelli in `ℝ≥0∞` — no summability hypothesis anywhere. -/
theorem discreteMass_discreteEConv (s t : G → ℝ≥0∞) :
    discreteMass (discreteEConv s t) = discreteMass s * discreteMass t := by
  rw [discreteMass]
  calc ∑' ν, discreteEConv s t ν
      = ∑' (ν) (μ), s μ * t (ν - μ) := rfl
    _ = ∑' (μ) (ν), s μ * t (ν - μ) := ENNReal.tsum_comm
    _ = ∑' μ, s μ * ∑' ν, t (ν - μ) := tsum_congr fun μ => ENNReal.tsum_mul_left
    _ = ∑' μ, s μ * discreteMass t := by
        refine tsum_congr fun μ => ?_
        congr 1
        exact (Equiv.subRight μ).tsum_eq t
    _ = discreteMass s * discreteMass t := by
        rw [ENNReal.tsum_mul_right]
        rfl

/-- The pointwise value of a majorant family is at most its mass; a convolution value is at most
the product of the masses. -/
theorem discreteEConv_le_mass (s t : G → ℝ≥0∞) (ν : G) :
    discreteEConv s t ν ≤ discreteMass s * discreteMass t :=
  le_trans (le_discreteMass (discreteEConv s t) ν)
    (le_of_eq (discreteMass_discreteEConv s t))

variable [DecidableEq G]

/-- The unit coefficient family `δ₀`, as a majorant. -/
def discreteEDelta : G → ℝ≥0∞ := fun ν => if ν = 0 then 1 else 0

/-- The unit coefficient family `δ₀`, complex. -/
def discreteDelta : G → ℂ := fun ν => if ν = 0 then 1 else 0

@[simp] theorem discreteMass_eDelta : discreteMass (discreteEDelta (G := G)) = 1 := by
  rw [discreteMass, tsum_eq_single 0 (fun b hb => by simp [discreteEDelta, hb])]
  simp [discreteEDelta]

theorem enorm_discreteDelta (ν : G) : ‖discreteDelta ν‖ₑ = discreteEDelta ν := by
  by_cases hν : ν = 0 <;> simp [discreteDelta, discreteEDelta, hν]

/-- `δ₀` is a left convolution unit. -/
theorem discreteConv_delta_left (β : G → ℂ) : discreteConv discreteDelta β = β := by
  funext ν
  rw [discreteConv, tsum_eq_single 0 (fun b hb => by simp [discreteDelta, hb])]
  simp [discreteDelta]

omit [DecidableEq G] in
/-- Convolution on an abelian group is commutative — an unconditional reindex. -/
theorem discreteConv_comm (α β : G → ℂ) : discreteConv α β = discreteConv β α := by
  funext ν
  rw [discreteConv, discreteConv, ← (Equiv.subLeft ν).tsum_eq
    (fun μ => β μ * α (ν - μ))]
  refine tsum_congr fun μ => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

/-- Iterated majorant convolution powers. -/
def discreteEConvPow (s : G → ℝ≥0∞) : ℕ → G → ℝ≥0∞
  | 0 => discreteEDelta
  | k + 1 => discreteEConv s (discreteEConvPow s k)

/-- Iterated complex convolution powers. -/
def discreteConvPow (r : G → ℂ) : ℕ → G → ℂ
  | 0 => discreteDelta
  | k + 1 => discreteConv r (discreteConvPow r k)

/-- **Majorant powers have exactly geometric mass.** -/
theorem discreteMass_discreteEConvPow (s : G → ℝ≥0∞) (k : ℕ) :
    discreteMass (discreteEConvPow s k) = discreteMass s ^ k := by
  induction k with
  | zero => simp [discreteEConvPow, discreteMass_eDelta]
  | succ k ih =>
    rw [discreteEConvPow, discreteMass_discreteEConv, ih, pow_succ]
    ring

/-- **Coefficientwise domination of convolution powers** — the induction behind every Neumann
majorant: `|r| ≤ s` coefficientwise gives `|r^{⋆k}| ≤ s^{⋆k}` coefficientwise. -/
theorem enorm_discreteConvPow_le {r : G → ℂ} {s : G → ℝ≥0∞}
    (h : ∀ ν, ‖r ν‖ₑ ≤ s ν) : ∀ k ν, ‖discreteConvPow r k ν‖ₑ ≤ discreteEConvPow s k ν := by
  intro k
  induction k with
  | zero =>
    intro ν
    rw [discreteConvPow, discreteEConvPow, enorm_discreteDelta]
  | succ k ih =>
    intro ν
    exact le_trans (enorm_discreteConv_le _ _ ν) (discreteEConv_mono h ih ν)

theorem discreteEConvPow_le_mass_pow (s : G → ℝ≥0∞) (k : ℕ) (ν : G) :
    discreteEConvPow s k ν ≤ discreteMass s ^ k :=
  le_trans (le_discreteMass _ ν) (le_of_eq (discreteMass_discreteEConvPow s k))

/-- The Neumann majorant kernel `K = ∑ₖ s^{⋆k}`. -/
def discreteNeumannKernel (s : G → ℝ≥0∞) : G → ℝ≥0∞ := fun ν =>
  ∑' k : ℕ, discreteEConvPow s k ν

/-- **The Neumann kernel has exactly geometric mass** `(1 - M)⁻¹`. -/
theorem discreteMass_neumannKernel (s : G → ℝ≥0∞) :
    discreteMass (discreteNeumannKernel s) = (1 - discreteMass s)⁻¹ := by
  rw [discreteMass]
  calc ∑' ν, discreteNeumannKernel s ν
      = ∑' (ν) (k : ℕ), discreteEConvPow s k ν := rfl
    _ = ∑' (k : ℕ) (ν), discreteEConvPow s k ν := ENNReal.tsum_comm
    _ = ∑' k : ℕ, discreteMass s ^ k := tsum_congr fun k => discreteMass_discreteEConvPow s k
    _ = (1 - discreteMass s)⁻¹ := ENNReal.tsum_geometric _

/-- The alternating Neumann series `∑ₖ (-1)^k r^{⋆k}`. -/
def discreteNeumannSeries (r : G → ℂ) : G → ℂ := fun ν =>
  ∑' k : ℕ, (-1 : ℂ) ^ k * discreteConvPow r k ν

/-- **The Neumann coefficient majorant**: the alternating series is dominated coefficientwise by
the Neumann kernel of any majorant. -/
theorem enorm_discreteNeumannSeries_le {r : G → ℂ} {s : G → ℝ≥0∞}
    (h : ∀ ν, ‖r ν‖ₑ ≤ s ν) (ν : G) :
    ‖discreteNeumannSeries r ν‖ₑ ≤ discreteNeumannKernel s ν := by
  refine le_trans enorm_tsum_le_tsum_enorm (ENNReal.tsum_le_tsum fun k => ?_)
  rw [enorm_mul]
  have h1 : ‖(-1 : ℂ) ^ k‖ₑ = 1 := by
    rw [enorm_pow, enorm_neg, enorm_one, one_pow]
  rw [h1, one_mul]
  exact enorm_discreteConvPow_le h k ν

/-! ## The geometric `ℓ¹` resolvent -/

omit [AddCommGroup G] [DecidableEq G] in
/-- A finite total enorm makes a complex family summable. -/
theorem summable_of_tsum_enorm_ne_top {f : G → ℂ} (h : (∑' ν, ‖f ν‖ₑ) ≠ ⊤) :
    Summable f := by
  refine Summable.of_nnnorm ?_
  rw [← ENNReal.tsum_coe_ne_top_iff_summable]
  simpa [enorm_eq_nnnorm] using h

theorem enorm_neumannSeries_term_le (r : G → ℂ) (k : ℕ) (ν : G) :
    ‖(-1 : ℂ) ^ k * discreteConvPow r k ν‖ₑ
      ≤ discreteMass (fun μ => ‖r μ‖ₑ) ^ k := by
  rw [enorm_mul]
  have h1 : ‖(-1 : ℂ) ^ k‖ₑ = 1 := by
    rw [enorm_pow, enorm_neg, enorm_one, one_pow]
  rw [h1, one_mul]
  exact le_trans (enorm_discreteConvPow_le (fun _ => le_rfl) k ν)
    (discreteEConvPow_le_mass_pow _ k ν)

theorem geometricMass_ne_top {m : ℝ≥0∞} (hm : m < 1) : (∑' k : ℕ, m ^ k) ≠ ⊤ := by
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_ne_top.mpr (by simpa using (tsub_pos_of_lt hm).ne')

/-- The Neumann series of a strictly submassive kernel converges absolutely at every
coefficient. -/
theorem summable_neumannSeries_terms {r : G → ℂ}
    (hr : discreteMass (fun ν => ‖r ν‖ₑ) < 1) (ν : G) :
    Summable fun k : ℕ => (-1 : ℂ) ^ k * discreteConvPow r k ν := by
  refine summable_of_tsum_enorm_ne_top
    (ne_top_of_le_ne_top (geometricMass_ne_top hr)
      (ENNReal.tsum_le_tsum fun k => enorm_neumannSeries_term_le r k ν))

/-- Convolving `r` against its Neumann series shifts every power up by one. -/
theorem discreteConv_neumannSeries {r : G → ℂ}
    (hr : discreteMass (fun ν => ‖r ν‖ₑ) < 1) (ν : G) :
    discreteConv r (discreteNeumannSeries r) ν
      = ∑' k : ℕ, (-1 : ℂ) ^ k * discreteConvPow r (k + 1) ν := by
  have hm := ne_top_of_lt hr
  have hswap : Summable (Function.uncurry
      fun (μ : G) (k : ℕ) => r μ * ((-1 : ℂ) ^ k * discreteConvPow r k (ν - μ))) := by
    refine summable_of_tsum_enorm_ne_top ?_
    have hb : (∑' p : G × ℕ, ‖(Function.uncurry
        fun (μ : G) (k : ℕ) => r μ * ((-1 : ℂ) ^ k * discreteConvPow r k (ν - μ))) p‖ₑ)
        ≤ discreteMass (fun μ => ‖r μ‖ₑ) * ∑' k : ℕ, discreteMass (fun μ => ‖r μ‖ₑ) ^ k := by
      rw [ENNReal.tsum_prod']
      calc ∑' (μ : G) (k : ℕ), ‖r μ * ((-1 : ℂ) ^ k * discreteConvPow r k (ν - μ))‖ₑ
          ≤ ∑' (μ : G) (k : ℕ), ‖r μ‖ₑ * discreteMass (fun σ => ‖r σ‖ₑ) ^ k := by
            refine ENNReal.tsum_le_tsum fun μ => ENNReal.tsum_le_tsum fun k => ?_
            rw [enorm_mul]
            exact mul_le_mul' le_rfl (enorm_neumannSeries_term_le r k (ν - μ))
        _ = discreteMass (fun μ => ‖r μ‖ₑ) * ∑' k : ℕ, discreteMass (fun σ => ‖r σ‖ₑ) ^ k := by
            have h1 : ∀ μ : G, (∑' k : ℕ, ‖r μ‖ₑ * discreteMass (fun σ => ‖r σ‖ₑ) ^ k)
                = ‖r μ‖ₑ * ∑' k : ℕ, discreteMass (fun σ => ‖r σ‖ₑ) ^ k := fun μ =>
              ENNReal.tsum_mul_left
            rw [tsum_congr h1, ENNReal.tsum_mul_right]
            rfl
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hm (geometricMass_ne_top hr)) hb
  calc discreteConv r (discreteNeumannSeries r) ν
      = ∑' (μ : G) (k : ℕ), r μ * ((-1 : ℂ) ^ k * discreteConvPow r k (ν - μ)) := by
        refine tsum_congr fun μ => ?_
        rw [discreteNeumannSeries, tsum_mul_left]
    _ = ∑' (k : ℕ) (μ : G), r μ * ((-1 : ℂ) ^ k * discreteConvPow r k (ν - μ)) :=
        hswap.tsum_comm.symm
    _ = ∑' k : ℕ, (-1 : ℂ) ^ k * discreteConvPow r (k + 1) ν := by
        refine tsum_congr fun k => ?_
        have hpull : ∀ μ : G, r μ * ((-1 : ℂ) ^ k * discreteConvPow r k (ν - μ))
            = (-1 : ℂ) ^ k * (r μ * discreteConvPow r k (ν - μ)) := fun μ => by ring
        rw [tsum_congr hpull, tsum_mul_left]
        rfl

/-- **The geometric `ℓ¹` resolvent**: the alternating Neumann series is a right convolution
inverse of `δ₀ + r` for every strictly submassive kernel. -/
theorem discreteConv_delta_add_neumannSeries {r : G → ℂ}
    (hr : discreteMass (fun ν => ‖r ν‖ₑ) < 1) :
    discreteConv (fun ν => discreteDelta ν + r ν) (discreteNeumannSeries r)
      = discreteDelta := by
  funext ν
  have hδ : Summable fun μ : G => discreteDelta μ * discreteNeumannSeries r (ν - μ) := by
    refine summable_of_ne_finset_zero (s := {0}) fun μ hμ => ?_
    have hμ0 : μ ≠ 0 := by simpa using hμ
    simp [discreteDelta, hμ0]
  have hrpart : Summable fun μ : G => r μ * discreteNeumannSeries r (ν - μ) := by
    refine summable_of_tsum_enorm_ne_top ?_
    have hb : (∑' μ : G, ‖r μ * discreteNeumannSeries r (ν - μ)‖ₑ)
        ≤ discreteMass (fun μ => ‖r μ‖ₑ)
            * (1 - discreteMass (fun μ => ‖r μ‖ₑ))⁻¹ := by
      calc ∑' μ : G, ‖r μ * discreteNeumannSeries r (ν - μ)‖ₑ
          ≤ ∑' μ : G, ‖r μ‖ₑ * (1 - discreteMass (fun σ => ‖r σ‖ₑ))⁻¹ := by
            refine ENNReal.tsum_le_tsum fun μ => ?_
            rw [enorm_mul]
            refine mul_le_mul' le_rfl ?_
            refine le_trans (enorm_discreteNeumannSeries_le (fun _ => le_rfl) (ν - μ)) ?_
            exact le_trans (le_discreteMass _ _)
              (le_of_eq (discreteMass_neumannKernel _))
        _ = discreteMass (fun μ => ‖r μ‖ₑ)
              * (1 - discreteMass (fun μ => ‖r μ‖ₑ))⁻¹ := ENNReal.tsum_mul_right
    refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ne_top_of_lt hr)
        (ENNReal.inv_ne_top.mpr (by simpa using (tsub_pos_of_lt hr).ne'))) hb
  have hsplit : discreteConv (fun μ => discreteDelta μ + r μ) (discreteNeumannSeries r) ν
      = (∑' μ : G, discreteDelta μ * discreteNeumannSeries r (ν - μ))
        + ∑' μ : G, r μ * discreteNeumannSeries r (ν - μ) := by
    rw [discreteConv, ← hδ.tsum_add hrpart]
    exact tsum_congr fun μ => by ring
  have hδval : (∑' μ : G, discreteDelta μ * discreteNeumannSeries r (ν - μ))
      = discreteNeumannSeries r ν := by
    rw [tsum_eq_single 0 (fun b hb => by simp [discreteDelta, hb])]
    simp [discreteDelta]
  have hrval : (∑' μ : G, r μ * discreteNeumannSeries r (ν - μ))
      = discreteDelta ν - discreteNeumannSeries r ν := by
    have h1 : (∑' μ : G, r μ * discreteNeumannSeries r (ν - μ))
        = discreteConv r (discreteNeumannSeries r) ν := rfl
    rw [h1, discreteConv_neumannSeries hr ν]
    have hg := summable_neumannSeries_terms hr ν
    have h2 : ∀ k : ℕ, (-1 : ℂ) ^ k * discreteConvPow r (k + 1) ν
        = -((-1 : ℂ) ^ (k + 1) * discreteConvPow r (k + 1) ν) := fun k => by
      rw [pow_succ]
      ring
    rw [tsum_congr h2, tsum_neg]
    have h3 := hg.tsum_eq_zero_add
    have h4 : discreteConvPow r 0 ν = discreteDelta ν := rfl
    rw [discreteNeumannSeries]
    rw [h3]
    simp only [pow_zero, one_mul, h4]
    ring
  rw [hsplit, hδval, hrval]
  ring

/-- The two-sided form, by commutativity. -/
theorem discreteConv_neumannSeries_delta_add {r : G → ℂ}
    (hr : discreteMass (fun ν => ‖r ν‖ₑ) < 1) :
    discreteConv (discreteNeumannSeries r) (fun ν => discreteDelta ν + r ν)
      = discreteDelta := by
  rw [discreteConv_comm]
  exact discreteConv_delta_add_neumannSeries hr

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- Mass is translation invariant. -/
theorem discreteMass_comp_sub {G : Type*} [AddCommGroup G] (s : G → ENNReal) (ρ : G) :
    discreteMass (fun ν => s (ν - ρ)) = discreteMass s :=
  (Equiv.subRight ρ).tsum_eq s

end GaloisForLFunctions.HTGeometry
