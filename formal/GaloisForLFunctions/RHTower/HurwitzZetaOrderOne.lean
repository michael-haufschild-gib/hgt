import GaloisForLFunctions.RHTower.MellinOrderOneEnvelope
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd

/-!
# The completed Hurwitz zeta functions have order at most one

The four Jacobi theta kernels attached to a shift `a` decay exponentially at infinity, uniformly in
the shift after globalising the asymptotic bound over the compact interval `[1, T]`.  Feeding those
bounds through the functional equation of the associated Mellin pair gives the head/tail estimate
of the modified kernel, hence an order-one growth envelope for

* the entire even completion `completedHurwitzZetaEven₀ a`, and
* the entire odd completion `completedHurwitzZetaOdd a`.

These are the two analytic building blocks of the completed Dirichlet `L`-function.
-/

open Filter Set MeasureTheory Complex HurwitzZeta
open scoped Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Two exponential decay estimates can be given a common rate and constant. -/
theorem exists_common_exp_bound {f g : ℝ → ℝ} {L M : ℝ}
    (hf : ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ t : ℝ, 1 ≤ t → |f t - L| ≤ C * Real.exp (-(p * t)))
    (hg : ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ t : ℝ, 1 ≤ t → |g t - M| ≤ C * Real.exp (-(p * t))) :
    ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧
      (∀ t : ℝ, 1 ≤ t → |f t - L| ≤ C * Real.exp (-(p * t))) ∧
      (∀ t : ℝ, 1 ≤ t → |g t - M| ≤ C * Real.exp (-(p * t))) := by
  obtain ⟨C₁, p₁, hC₁, hp₁, hb₁⟩ := hf
  obtain ⟨C₂, p₂, hC₂, hp₂, hb₂⟩ := hg
  have hCm : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left _ _)
  refine ⟨max C₁ C₂, min p₁ p₂, hCm, lt_min hp₁ hp₂, ?_, ?_⟩
  · intro t ht
    have hexp : Real.exp (-(p₁ * t)) ≤ Real.exp (-(min p₁ p₂ * t)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [min_le_left p₁ p₂]
    exact le_trans (hb₁ t ht) (mul_le_mul (le_max_left _ _) hexp (Real.exp_pos _).le hCm)
  · intro t ht
    have hexp : Real.exp (-(p₂ * t)) ≤ Real.exp (-(min p₁ p₂ * t)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [min_le_right p₁ p₂]
    exact le_trans (hb₂ t ht) (mul_le_mul (le_max_right _ _) hexp (Real.exp_pos _).le hCm)

/-- Pointwise exponential decay of the centered even theta kernel. -/
theorem exists_evenKernel_bound (a : UnitAddCircle) :
    ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧
      ∀ t : ℝ, 1 ≤ t →
        |evenKernel a t - (if a = 0 then 1 else 0)| ≤ C * Real.exp (-(p * t)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub a
  obtain ⟨C, hC, hb⟩ := global_exp_bound (evenKernel a) (if a = 0 then 1 else 0) p
    (continuousOn_evenKernel a) hO
  refine ⟨C, p, hC, hp, fun t ht => ?_⟩
  have hbt := hb t ht
  rwa [neg_mul] at hbt

/-- Pointwise exponential decay of the centered cosine theta kernel. -/
theorem exists_cosKernel_bound (a : UnitAddCircle) :
    ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧
      ∀ t : ℝ, 1 ≤ t → |cosKernel a t - 1| ≤ C * Real.exp (-(p * t)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_cosKernel_sub a
  obtain ⟨C, hC, hb⟩ := global_exp_bound (cosKernel a) 1 p (continuousOn_cosKernel a) hO
  refine ⟨C, p, hC, hp, fun t ht => ?_⟩
  have hbt := hb t ht
  rwa [neg_mul] at hbt

/-- Pointwise exponential decay of the odd theta kernel. -/
theorem exists_oddKernel_bound (a : UnitAddCircle) :
    ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧
      ∀ t : ℝ, 1 ≤ t → |oddKernel a t - 0| ≤ C * Real.exp (-(p * t)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_oddKernel a
  have hO' : (fun t => oddKernel a t - 0) =O[atTop] fun t => Real.exp (-p * t) := by
    simpa using hO
  obtain ⟨C, hC, hb⟩ := global_exp_bound (oddKernel a) 0 p (continuousOn_oddKernel a) hO'
  refine ⟨C, p, hC, hp, fun t ht => ?_⟩
  have hbt := hb t ht
  rwa [neg_mul] at hbt

/-- Pointwise exponential decay of the sine theta kernel. -/
theorem exists_sinKernel_bound (a : UnitAddCircle) :
    ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧
      ∀ t : ℝ, 1 ≤ t → |sinKernel a t - 0| ≤ C * Real.exp (-(p * t)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_sinKernel a
  have hO' : (fun t => sinKernel a t - 0) =O[atTop] fun t => Real.exp (-p * t) := by
    simpa using hO
  obtain ⟨C, hC, hb⟩ := global_exp_bound (sinKernel a) 0 p (continuousOn_sinKernel a) hO'
  refine ⟨C, p, hC, hp, fun t ht => ?_⟩
  have hbt := hb t ht
  rwa [neg_mul] at hbt

/-- **Order-one envelope of the entire even Hurwitz completion.** -/
theorem completedHurwitzZetaEven₀_orderOneEnvelope (a : UnitAddCircle) :
    OrderOneEnvelope (completedHurwitzZetaEven₀ a) := by
  obtain ⟨C, p, hC, hp, hbf, hbg⟩ :=
    exists_common_exp_bound (exists_evenKernel_bound a) (exists_cosKernel_bound a)
  have hfval : ∀ t : ℝ, ‖(hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀‖
      = |evenKernel a t - (if a = 0 then 1 else 0)| := by
    intro t
    have hrew : (hurwitzEvenFEPair a).f t - (hurwitzEvenFEPair a).f₀
        = ((evenKernel a t - (if a = 0 then 1 else 0) : ℝ) : ℂ) := by
      show ((evenKernel a t : ℝ) : ℂ) - (if a = 0 then (1 : ℂ) else 0) = _
      split_ifs <;> push_cast <;> ring
    rw [hrew, Complex.norm_real, Real.norm_eq_abs]
  have hgval : ∀ t : ℝ, ‖(hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀‖
      = |cosKernel a t - 1| := by
    intro t
    have hrew : (hurwitzEvenFEPair a).g t - (hurwitzEvenFEPair a).g₀
        = ((cosKernel a t - 1 : ℝ) : ℂ) := by
      show ((cosKernel a t : ℝ) : ℂ) - (1 : ℂ) = _
      push_cast
      ring
    rw [hrew, Complex.norm_real, Real.norm_eq_abs]
  have hk : (1 : ℝ) / 2 ≤ (hurwitzEvenFEPair a).k := le_of_eq rfl
  obtain ⟨C₀, q, hC₀, hq, htail, hhead⟩ :=
    weakFEPair_f_modif_decay (hurwitzEvenFEPair a) hC hp hk
      (fun t ht => by rw [hfval t]; exact hbf t ht)
      (fun t ht => by rw [hgval t]; exact hbg t ht)
  have hmel : OrderOneEnvelope (mellin (hurwitzEvenFEPair a).f_modif) :=
    mellin_orderOneEnvelope_of_decay _ hq hC₀ htail hhead
  have hΛ : OrderOneEnvelope (hurwitzEvenFEPair a).Λ₀ := hmel
  refine ((hΛ.comp_affine (1 / 2) 0).const_mul (1 / 2)).congr fun s => ?_
  show (1 / 2 : ℂ) * (hurwitzEvenFEPair a).Λ₀ ((1 / 2 : ℂ) * s + 0) = _
  have harg : ((1 / 2 : ℂ) * s + 0) = s / 2 := by ring
  rw [harg]
  show (1 / 2 : ℂ) * (hurwitzEvenFEPair a).Λ₀ (s / 2) = (hurwitzEvenFEPair a).Λ₀ (s / 2) / 2
  ring

/-- **Order-one envelope of the entire odd Hurwitz completion.** -/
theorem completedHurwitzZetaOdd_orderOneEnvelope (a : UnitAddCircle) :
    OrderOneEnvelope (completedHurwitzZetaOdd a) := by
  obtain ⟨C, p, hC, hp, hbf, hbg⟩ :=
    exists_common_exp_bound (exists_oddKernel_bound a) (exists_sinKernel_bound a)
  have hfval : ∀ t : ℝ, ‖(hurwitzOddFEPair a).f t‖ = |oddKernel a t - 0| := by
    intro t
    show ‖((oddKernel a t : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, sub_zero]
  have hgval : ∀ t : ℝ, ‖(hurwitzOddFEPair a).g t‖ = |sinKernel a t - 0| := by
    intro t
    show ‖((sinKernel a t : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, sub_zero]
  have hk : (1 : ℝ) / 2 ≤ (hurwitzOddFEPair a).k := by
    show (1 : ℝ) / 2 ≤ 3 / 2
    norm_num
  obtain ⟨C₀, q, hC₀, hq, htail, hhead⟩ :=
    weakFEPair_f_decay (hurwitzOddFEPair a) hC hp hk
      (fun t ht => by rw [hfval t]; exact hbf t ht)
      (fun t ht => by rw [hgval t]; exact hbg t ht)
  have hmel : OrderOneEnvelope (mellin (hurwitzOddFEPair a).f) :=
    mellin_orderOneEnvelope_of_decay _ hq hC₀ htail hhead
  have hΛ : OrderOneEnvelope (hurwitzOddFEPair a).Λ := by
    rw [(isStrong_hurwitzOddFEPair a).Λ_eq]
    exact hmel
  refine ((hΛ.comp_affine (1 / 2) (1 / 2)).const_mul (1 / 2)).congr fun s => ?_
  show (1 / 2 : ℂ) * (hurwitzOddFEPair a).Λ ((1 / 2 : ℂ) * s + 1 / 2) = _
  have harg : ((1 / 2 : ℂ) * s + 1 / 2) = (s + 1) / 2 := by ring
  rw [harg]
  show (1 / 2 : ℂ) * (hurwitzOddFEPair a).Λ ((s + 1) / 2)
      = (hurwitzOddFEPair a).Λ ((s + 1) / 2) / 2
  ring

end RHTower
