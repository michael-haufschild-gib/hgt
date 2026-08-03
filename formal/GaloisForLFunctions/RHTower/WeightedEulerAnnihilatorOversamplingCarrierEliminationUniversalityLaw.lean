import GaloisForLFunctions.RHTower.WeightedEulerDualReduction
import GaloisForLFunctions.RHTower.WeightedEulerLambertOversampling
import GaloisForLFunctions.RHTower.WeightedEulerFECarrierSeparation
import GaloisForLFunctions.RHTower.WeightedEulerMobiusRayRecovery

/-!
# Weighted-Euler annihilator oversampling carrier elimination

A weighted-Euler graph annihilator first gives prime-log samples of its
compact-carrier Lambert transform. Unconditional oversampling supplies
one-variable tail decay. Evaluating that tail at every positive integer
multiple of a large base point creates the geometric family needed by
quantitative Möbius recovery. If the resulting decay rate crosses the upper
carrier wall, the entire Fourier--Borel transform and every coordinate-power
value vanish.
-/

noncomputable section

namespace RHTower

open Complex Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Weighted-Euler annihilator oversampling carrier-elimination
universality law.** Prime-indexed graph-annihilator decay past the positive
carrier strip forces global Fourier--Borel and coordinate-power
annihilation. -/
theorem compactFourierBorel_eq_zero_of_primeLog_graph_annihilation
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (lam : ℕ → ℂ)
    {α β σ C : ℝ}
    (hα : 0 < α) (hσ : 0 < σ) (hC : 0 ≤ C)
    (hstrip : ∀ k, α ≤ (s k).re ∧ (s k).re ≤ β)
    (hβκ : β < min σ (α / 2))
    (hgraph : ∀ p : ℕ, p.Prime →
      lam p + L (compactPrimeEulerUnitTangent s p) = 0)
    (hdual : ∀ p : ℕ, p.Prime →
      ‖lam p‖ ≤ C * Real.log p * (p : ℝ) ^ (-σ)) :
    (∀ z : ℂ, compactFourierBorel L s z = 0) ∧
      ∀ m : ℕ, L (s ^ m) = 0 := by
  let M : ℝ := max α ‖s‖
  have hαM : α ≤ M := le_max_left _ _
  have hnorm : ∀ k, ‖s k‖ ≤ M := fun k =>
    le_trans (s.norm_coe_le_norm k) (le_max_right _ _)
  have hsamp : ∀ p : ℕ, p.Prime →
      ‖compactCarrierLambertTransform L s (Real.log p : ℂ)‖
        ≤ C * Real.exp (-(σ * Real.log p)) := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    calc
      ‖compactCarrierLambertTransform L s (Real.log p : ℂ)‖
          ≤ C * (p : ℝ) ^ (-σ) :=
        norm_lambert_primeLog_le_of_graph_annihilation L s hp.two_le
          (hgraph p hp) (hdual p hp)
      _ = C * Real.exp (-(σ * Real.log p)) := by
        rw [Real.rpow_def_of_pos hpR]
        congr 2
        ring
  obtain ⟨C', R₁, hray⟩ :=
    norm_le_ray_of_primeLog_sampled_lambert L s 0 hα hαM
      (fun k => (hstrip k).1) hnorm hσ.le hC hsamp
  set κ : ℝ := min σ (α / 2) with hκdef
  have hκ : 0 < κ := by
    rw [hκdef]
    exact lt_min hσ (half_pos hα)
  let D : ℝ := max C' 0
  have hD : 0 ≤ D := le_max_right _ _
  let R : ℝ := max (max R₁ 0) (Real.log 2 / κ)
  have hR0 : 0 < R := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    exact lt_of_lt_of_le (div_pos hlog2 hκ) (le_max_right _ _)
  have htail : ∀ x : ℝ, R ≤ x →
      ‖compactFourierBorel L s (x : ℂ)‖
        ≤ 4 * D * Real.exp (-(κ * x)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hR0 hx
    set ρ : ℝ := Real.exp (-(κ * x)) with hρ
    have hρ0 : 0 ≤ ρ := Real.exp_nonneg _
    have hρ1 : ρ < 1 := by
      rw [hρ, Real.exp_lt_one_iff]
      nlinarith [mul_pos hκ hx0]
    have hρhalf : ρ ≤ 1 / 2 := by
      rw [hρ]
      have hxlog : Real.log 2 / κ ≤ x :=
        le_trans (le_max_right _ _) hx
      have hlog : Real.log 2 ≤ κ * x := by
        rw [div_le_iff₀ hκ] at hxlog
        simpa [mul_comm] using hxlog
      calc
        Real.exp (-(κ * x)) ≤ Real.exp (-(Real.log 2)) :=
          Real.exp_le_exp.2 (by linarith)
        _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log two_pos]
          norm_num
    have hq : ∀ n : ℕ+,
        ‖compactExponentialTest s ((n : ℂ) * (x : ℂ))‖ < 1 := by
      intro n
      have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.prop
      apply norm_compactExponentialTest_lt_one_of_re_pos s _
        ((n : ℝ) * (α * x))
      · positivity
      · intro k
        have hcast :
            (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
          norm_cast
        calc
          (n : ℝ) * (α * x)
              ≤ (n : ℝ) * (x * (s k).re) := by
                apply mul_le_mul_of_nonneg_left _ hnpos.le
                nlinarith [mul_le_mul_of_nonneg_left (hstrip k).1 hx0.le]
          _ = (((n : ℂ) * (x : ℂ)) * s k).re := by
                rw [hcast]
                simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
                ring
    have hFB : ∀ n : ℕ+,
        ‖compactFourierBorel L s ((n : ℂ) * (x : ℂ))‖
          ≤ ‖L‖ * Real.exp (-(α * x)) ^ (n : ℕ) := by
      intro n
      have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.prop
      have hre : ∀ k,
          (n : ℝ) * (α * x) ≤
            (((n : ℂ) * (x : ℂ)) * s k).re := by
        intro k
        have hcast :
            (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
          norm_cast
        calc
          (n : ℝ) * (α * x)
              ≤ (n : ℝ) * (x * (s k).re) := by
                apply mul_le_mul_of_nonneg_left _ hnpos.le
                nlinarith [mul_le_mul_of_nonneg_left (hstrip k).1 hx0.le]
          _ = (((n : ℂ) * (x : ℂ)) * s k).re := by
                rw [hcast]
                simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
                ring
      have htest := norm_compactExponentialTest_le_exp_neg_of_re s
        ((n : ℂ) * (x : ℂ)) ((n : ℝ) * (α * x)) hre
      calc
        ‖compactFourierBorel L s ((n : ℂ) * (x : ℂ))‖
            ≤ ‖L‖ * ‖compactExponentialTest s ((n : ℂ) * (x : ℂ))‖ :=
          L.le_opNorm _
        _ ≤ ‖L‖ * Real.exp (-((n : ℝ) * (α * x))) := by gcongr
        _ = ‖L‖ * Real.exp (-(α * x)) ^ (n : ℕ) := by
          congr 1
          rw [show -((n : ℝ) * (α * x)) =
              (n : ℕ) * (-(α * x)) by ring, Real.exp_nat_mul]
    have hlam : ∀ n : ℕ+,
        ‖compactCarrierLambertTransform L s ((n : ℂ) * (x : ℂ))‖
          ≤ D * ρ ^ (n : ℕ) := by
      intro n
      have hn1 : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.prop
      have hyR₁ : R₁ ≤ (n : ℝ) * x := by
        have hxR₁ : R₁ ≤ x :=
          le_trans (le_trans (le_max_left R₁ 0) (le_max_left _ _)) hx
        nlinarith
      have hcast :
          (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
        norm_cast
      rw [hcast]
      calc
        ‖compactCarrierLambertTransform L s (((n : ℝ) * x : ℝ) : ℂ)‖
            ≤ C' * Real.exp (-(min σ (α / 2) * ((n : ℝ) * x))) :=
          hray ((n : ℝ) * x) hyR₁
        _ ≤ D * Real.exp (-(min σ (α / 2) * ((n : ℝ) * x))) := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.exp_nonneg _)
        _ = D * ρ ^ (n : ℕ) := by
          congr 1
          rw [hρ, hκdef, show -(min σ (α / 2) * ((n : ℝ) * x)) =
              (n : ℕ) * (-(min σ (α / 2) * x)) by ring,
            Real.exp_nat_mul]
    have hrecover := norm_compactFourierBorel_le_of_sampled_lambert_decay
      L s (x : ℂ) hq (norm_nonneg L) (Real.exp_nonneg _)
      (by rw [Real.exp_lt_one_iff]; nlinarith [mul_pos hα hx0])
      hFB hD hρ0 hρhalf hlam
    simpa [hρ] using hrecover
  let B : ℝ := max (4 * D) (‖L‖ * Real.exp ((‖s‖ + κ) * R))
  have hdecay : ∀ x : ℝ, 0 ≤ x →
      ‖compactFourierBorel L s (x : ℂ)‖
        ≤ B * Real.exp (-(κ * x)) := by
    intro x hx
    by_cases hRx : R ≤ x
    · exact (htail x hRx).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.exp_nonneg _))
    · have hxR : x ≤ R := le_of_not_ge hRx
      have hbasic := norm_compactFourierBorel_le_exp L s (x : ℂ)
      have hnormx : ‖(x : ℂ)‖ = x := by
        rw [Complex.norm_real, Real.norm_of_nonneg hx]
      rw [hnormx] at hbasic
      calc
        ‖compactFourierBorel L s (x : ℂ)‖
            ≤ ‖L‖ * Real.exp (‖s‖ * x) := hbasic
        _ = (‖L‖ * Real.exp ((‖s‖ + κ) * x)) *
              Real.exp (-(κ * x)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ (‖L‖ * Real.exp ((‖s‖ + κ) * R)) *
              Real.exp (-(κ * x)) := by
          gcongr
        _ ≤ B * Real.exp (-(κ * x)) := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.exp_nonneg _)
  have hzero : ∀ z : ℂ, compactFourierBorel L s z = 0 :=
    compactFourierBorel_eq_zero_of_ray_decay L s hβκ
      (fun k => (hstrip k).2) hdecay
  exact ⟨hzero, fun m =>
    map_coordinate_pow_eq_zero_of_fourierBorel_zero L s hzero m⟩

/-- **Positive-strip rate barrier.**  On a nonempty carrier, the lower and
upper strip walls force `α ≤ β`, whereas the oversampling decay supplied above is
at most `α / 2`.  Hence the separation hypothesis of
`compactFourierBorel_eq_zero_of_primeLog_graph_annihilation` has no
nonempty positive-strip instance. -/
theorem not_beta_lt_min_sigma_half_alpha_of_nonempty_positiveStrip
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (s : C(K, ℂ)) {α β σ : ℝ}
    (hα : 0 < α)
    (hstrip : ∀ k, α ≤ (s k).re ∧ (s k).re ≤ β) :
    ¬ β < min σ (α / 2) := by
  intro hβκ
  let k : K := Classical.choice inferInstance
  have hαβ : α ≤ β := (hstrip k).1.trans (hstrip k).2
  have hβhalf : β < α / 2 := hβκ.trans_le (min_le_right _ _)
  linarith

end RHTower
