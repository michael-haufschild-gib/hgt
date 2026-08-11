import GaloisForLFunctions.HTGeometry.PowerSubstitutionForwardJet
import GaloisForLFunctions.HTGeometry.ClockAnalyticWienerScale
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# Formation-scale receivers

Lean certificate for the mechanism in
`one-norm-impossibility-formal-receiver-collapse-and-wiener-scale-fusion-law.md`.

The first theorem proves that a faithful polynomial generator with `D T = 1` cannot live in a
single normed algebra on which the derivation is bounded.  The remaining theorems certify the
algebraic Adams/ghost/receiver exchange that survives after passing to a scale of receiver spaces.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open Filter
open scoped Topology

noncomputable section

/-! ## An operation-indexed receiver scale -/

/-- One derivative in logarithmic degree is absorbed by any positive analytic collar. -/
theorem linear_mul_exp_neg_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    t * Real.exp (-(δ * t)) ≤ 1 / δ := by
  have hs : 0 ≤ δ * t := mul_nonneg hδ.le ht
  have hbase : δ * t ≤ Real.exp (δ * t) := by
    have h := Real.add_one_le_exp (δ * t)
    linarith
  have hpos : 0 < Real.exp (-(δ * t)) := Real.exp_pos _
  have hcancel : Real.exp (δ * t) * Real.exp (-(δ * t)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [le_div_iff₀ hδ]
  calc
    t * Real.exp (-(δ * t)) * δ =
        (δ * t) * Real.exp (-(δ * t)) := by ring
    _ ≤ Real.exp (δ * t) * Real.exp (-(δ * t)) :=
      mul_le_mul_of_nonneg_right hbase hpos.le
    _ = 1 := hcancel

/-- Exponentially weighted one-sided receiver norm. -/
noncomputable def formationWienerNorm (ρ : ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ, ‖a n‖ * Real.exp (ρ * n)

/-- Admission to a one-sided receiver of logarithmic radius `ρ`. -/
def FormationWienerSummable (ρ : ℝ) (a : ℕ → ℂ) : Prop :=
  Summable fun n : ℕ => ‖a n‖ * Real.exp (ρ * n)

/-- Logarithmic ghost formation multiplies coefficient `n` by its grade. -/
def formationGhost (a : ℕ → ℂ) : ℕ → ℂ := fun n => (n : ℂ) * a n

/-- Pointwise analytic-collar estimate for logarithmic ghost formation. -/
theorem formationGhost_weight_le {ρ' ρ : ℝ} (hρ : ρ' < ρ) (a : ℕ → ℂ) (n : ℕ) :
    ‖formationGhost a n‖ * Real.exp (ρ' * n)
      ≤ (1 / (ρ - ρ')) * (‖a n‖ * Real.exp (ρ * n)) := by
  have hδ : 0 < ρ - ρ' := sub_pos.mpr hρ
  have ht : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkey := linear_mul_exp_neg_le hδ ht
  have hsplit : Real.exp (ρ' * (n : ℝ)) =
      Real.exp (-((ρ - ρ') * (n : ℝ))) * Real.exp (ρ * (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖formationGhost a n‖ * Real.exp (ρ' * n) =
        ((n : ℝ) * Real.exp (-((ρ - ρ') * (n : ℝ)))) *
          (‖a n‖ * Real.exp (ρ * (n : ℝ))) := by
      simp [formationGhost, hsplit]
      ring
    _ ≤ (1 / (ρ - ρ')) * (‖a n‖ * Real.exp (ρ * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hkey (by positivity)

/-- **Scale transport.**  Logarithmic ghost formation maps every larger admitted radius to every
strictly smaller radius. -/
theorem formationWienerSummable_ghost {ρ' ρ : ℝ} (hρ : ρ' < ρ) {a : ℕ → ℂ}
    (ha : FormationWienerSummable ρ a) : FormationWienerSummable ρ' (formationGhost a) :=
  (ha.mul_left (1 / (ρ - ρ'))).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (formationGhost_weight_le hρ a)

/-- Quantitative collar cost of logarithmic ghost formation. -/
theorem formationWienerNorm_ghost_le {ρ' ρ : ℝ} (hρ : ρ' < ρ) {a : ℕ → ℂ}
    (ha : FormationWienerSummable ρ a) :
    formationWienerNorm ρ' (formationGhost a)
      ≤ (1 / (ρ - ρ')) * formationWienerNorm ρ a := by
  rw [formationWienerNorm, formationWienerNorm, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (formationGhost_weight_le hρ a)
    (formationWienerSummable_ghost hρ ha) (ha.mul_left (1 / (ρ - ρ')))

/-- **One-norm impossibility.**  A bounded derivation cannot differentiate a nonnilpotent
generator to the unit in a normed commutative `ℂ`-algebra. -/
theorem no_bounded_derivation_of_generator
    {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
    (D : Derivation ℂ A A) (T : A)
    (hpow : ∀ n : ℕ, 0 < n → T ^ n ≠ 0)
    (hDT : D T = 1)
    (C : ℝ) (hC : ∀ y : A, ‖D y‖ ≤ C * ‖y‖) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 (‖T‖ * C))
  have hnpos : 0 < n := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left 0 (‖T‖ * C)) hn)
  have hDpow : D (T ^ n) = (n : ℂ) • T ^ (n - 1) := by
    rw [D.leibniz_pow, hDT]
    simp [Algebra.smul_def]
  have hTpow : 0 < ‖T ^ n‖ := norm_pos_iff.mpr (hpow n hnpos)
  have hmul : T * D (T ^ n) = (n : ℂ) • T ^ n := by
    rw [hDpow, Algebra.mul_smul_comm]
    congr 1
    rw [← pow_succ']
    congr
    omega
  have hineq : (n : ℝ) * ‖T ^ n‖ ≤ (‖T‖ * C) * ‖T ^ n‖ := by
    calc
      (n : ℝ) * ‖T ^ n‖ = ‖(n : ℂ) • T ^ n‖ := by simp [norm_smul]
      _ = ‖T * D (T ^ n)‖ := by rw [hmul]
      _ ≤ ‖T‖ * ‖D (T ^ n)‖ := norm_mul_le _ _
      _ ≤ ‖T‖ * (C * ‖T ^ n‖) :=
        mul_le_mul_of_nonneg_left (hC (T ^ n)) (norm_nonneg T)
      _ = (‖T‖ * C) * ‖T ^ n‖ := by ring
  have hnle : (n : ℝ) ≤ ‖T‖ * C := le_of_mul_le_mul_right hineq hTpow
  have hgt : ‖T‖ * C < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right 0 (‖T‖ * C)) hn
  exact (not_lt_of_ge hnle) hgt

/-- **Formal receiver collapse.**  If every scalar renormalization of the powers of `T` tends to
zero, then every continuous complex receiver kills `T`.  This is the abstract mechanism behind
the collapse of ordinary continuous receivers on a purely formal `T`-adic completion. -/
theorem continuous_receiver_kills_formal_generator
    {A : Type*} [TopologicalSpace A] [Semiring A] [Algebra ℂ A]
    (χ : A →ₐ[ℂ] ℂ) (hχ : Continuous χ) (T : A)
    (hvanish : Tendsto
      (fun n : ℕ => algebraMap ℂ A ((χ T)⁻¹ ^ n) * T ^ n)
      atTop (𝓝 0)) : χ T = 0 := by
  by_contra hne
  have hzero : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 0) := by
    have hmap := (hχ.tendsto 0).comp hvanish
    convert hmap using 1
    · funext n
      simp [hne]
    · simp
  have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
  have : (0 : ℂ) = 1 := tendsto_nhds_unique hzero hone
  exact zero_ne_one this

/-- Adams intervention on a polynomial receiver: substitute `X^q`. -/
noncomputable def formationAdams (q : ℕ) (p : ℂ[X]) : ℂ[X] :=
  p.comp (X ^ q)

/-- Ramification multiplier generated by differentiating the power receiver. -/
noncomputable def formationScale (q : ℕ) : ℂ[X] :=
  Polynomial.C (q : ℂ) * X ^ (q - 1)

@[simp] theorem eval_formationScale (q : ℕ) (z : ℂ) :
    (formationScale q).eval z = (q : ℂ) * z ^ (q - 1) := by
  simp [formationScale]

/-- **Ghost/Adams/receiver exchange.**  Formal differentiation and Adams intervention commute up
to the exact ramification multiplier `q X^(q-1)`. -/
theorem derivative_formationAdams (q : ℕ) (p : ℂ[X]) :
    (formationAdams q p).derivative = formationScale q * formationAdams q p.derivative := by
  rw [formationAdams, Polynomial.derivative_comp]
  simp [formationScale, formationAdams, Polynomial.derivative_pow]

/-- Receiver evaluation transports by the power map under Adams intervention. -/
theorem eval_formationAdams (q : ℕ) (p : ℂ[X]) (z : ℂ) :
    (formationAdams q p).eval z = p.eval (z ^ q) := by
  simp [formationAdams, Polynomial.eval_comp]

/-- The exchange law is visible pointwise at every receiver. -/
theorem eval_derivative_formationAdams (q : ℕ) (p : ℂ[X]) (z : ℂ) :
    (formationAdams q p).derivative.eval z =
      ((q : ℂ) * z ^ (q - 1)) * p.derivative.eval (z ^ q) := by
  rw [derivative_formationAdams]
  simp [eval_formationScale, eval_formationAdams]

end

end GaloisForLFunctions.HTGeometry
