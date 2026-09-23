/-
Doc 50 §§1–3 + doc 51 §§1–2 (task #151): the lattice collapse and the
collective-push master bound, machine-checked.

* `lattice_collapse` — e^{−iπ(4pm+m²)} = w^m with w = e^{−iπ(1+4p)}: the
  quadratic Gauss lattice of doc 49 §2 is a pure geometric progression,
  because m² ≡ m (mod 2).
* `norm_one_sub_exp` — ‖1 − e^{iθ}‖ = 2|sin(θ/2)|.
* `resonance_denominator` — ‖1 − w‖ = 2|cos(2πp)|: vanishing exactly at the
  quarter-phase coherence points, maximal at p ≡ 0, 1/2.
* `abel_geom_bound` — antitone nonnegative envelope against a unit-circle
  geometric progression: ‖Σ_{m<K} a_m w^m‖ ≤ 2a₀/‖1−w‖.
* `collective_push_le` — the composition: the tower tail's net push is at
  most a₀/|cos 2πp|, for every truncation K.
* `one_wrap_hit` — the rotation orbit lands in any ϑ-wide target within one
  wrap (doc 51 §2(2)).
* `survival_floor` — the walk interface: survival forces the depth above
  every negative excursion (doc 51 §1).

The analytic pushes here are what discharge the `hkill`-side hypotheses of
the finite cascade bookkeeping in `SweepCascade`.
-/
import GaloisForLFunctions.RHTower.GaussLattice
import GaloisForLFunctions.RHTower.CothInfra

noncomputable section

namespace RHTower

open Finset

/-- The lattice ratio w = e^{−iπ(1+4p)} of doc 50 §1. -/
def latticeRatio (p : ℝ) : ℂ :=
  Complex.exp (((-(Real.pi * (1 + 4 * p)) : ℝ) : ℂ) * Complex.I)

theorem norm_latticeRatio (p : ℝ) : ‖latticeRatio p‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- **The lattice collapse (doc 50 §1)**: the quadratic Gauss-lattice phase is
a pure geometric progression, since m² ≡ m (mod 2). -/
theorem lattice_collapse (p : ℝ) (m : ℕ) :
    Complex.exp (((-(Real.pi * (4 * p * m + (m : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) * Complex.I)
      = latticeRatio p ^ m := by
  rw [latticeRatio, ← Complex.exp_nat_mul]
  obtain ⟨k, hk⟩ := pi_msq_phase_alternates (m : ℤ)
  have hk' : ((m : ℂ)) ^ (2 : ℕ) - (m : ℂ) = (k : ℂ) + (k : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hk
  have hx : (((-(Real.pi * (4 * p * m + (m : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) * Complex.I)
      = (m : ℂ) * (((-(Real.pi * (1 + 4 * p)) : ℝ) : ℂ) * Complex.I)
        + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    linear_combination (-(Real.pi : ℂ) * Complex.I) * hk'
  rw [hx, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- ‖1 − e^{iθ}‖ = 2|sin(θ/2)| for real θ. -/
theorem norm_one_sub_exp (θ : ℝ) :
    ‖1 - Complex.exp (↑θ * Complex.I)‖ = 2 * |Real.sin (θ / 2)| := by
  have h1 : (1 : ℂ) - Complex.exp (↑θ * Complex.I)
      = ↑(1 - Real.cos θ) + ↑(-Real.sin θ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [h1, Complex.norm_add_mul_I]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ (2 : ℕ) := by
    have hc2 := Real.cos_two_mul (θ / 2)
    have hs1 := Real.sin_sq_add_cos_sq (θ / 2)
    have hθ : 2 * (θ / 2) = θ := by ring
    rw [hθ] at hc2
    nlinarith [hc2, hs1]
  have hpyth : (1 - Real.cos θ) ^ (2 : ℕ) + (-Real.sin θ) ^ (2 : ℕ)
      = (2 * |Real.sin (θ / 2)|) ^ (2 : ℕ) := by
    have habs : |Real.sin (θ / 2)| ^ (2 : ℕ) = Real.sin (θ / 2) ^ (2 : ℕ) := sq_abs _
    have hs := Real.sin_sq_add_cos_sq θ
    nlinarith [hcos, hs, habs]
  rw [hpyth, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- **The resonance denominator (doc 50 §2)**: ‖1 − w‖ = 2|cos 2πp| — zero
exactly at the quarter-phase points p = 1/4, 3/4 (mod 1), maximal at
p ≡ 0, 1/2. -/
theorem resonance_denominator (p : ℝ) :
    ‖1 - latticeRatio p‖ = 2 * |Real.cos (2 * Real.pi * p)| := by
  rw [latticeRatio, norm_one_sub_exp]
  congr 1
  have harg : -(Real.pi * (1 + 4 * p)) / 2 = -(Real.pi / 2 + 2 * Real.pi * p) := by
    ring
  rw [harg, Real.sin_neg, abs_neg]
  have hshift : Real.sin (Real.pi / 2 + 2 * Real.pi * p)
      = Real.cos (2 * Real.pi * p) := by
    rw [Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  rw [hshift]

theorem latticeRatio_ne_one {p : ℝ} (hp : Real.cos (2 * Real.pi * p) ≠ 0) :
    latticeRatio p ≠ 1 := by
  intro h
  have hden := resonance_denominator p
  rw [h] at hden
  simp only [sub_self, norm_zero] at hden
  have habs : |Real.cos (2 * Real.pi * p)| = 0 := by
    linarith [abs_nonneg (Real.cos (2 * Real.pi * p))]
  exact hp (abs_eq_zero.mp habs)

/-- **The Abel/geometric master bound (doc 50 §3)**: an antitone nonnegative
amplitude envelope against a unit-circle geometric progression is bounded by
2a₀/‖1−w‖, uniformly in the truncation. -/
theorem abel_geom_bound {w : ℂ} (hw : ‖w‖ = 1) (hne : w ≠ 1)
    {a : ℕ → ℝ} (hmono : Antitone a) (hnn : ∀ n, 0 ≤ a n) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, (a m : ℂ) * w ^ m‖ ≤ 2 * a 0 / ‖1 - w‖ := by
  have hden : 0 < ‖1 - w‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hne h.symm
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact div_nonneg (by linarith [hnn 0]) hden.le
  have hparts := Finset.sum_range_by_parts
    (fun m => (a m : ℂ)) (fun m => w ^ m) K
  simp only [smul_eq_mul] at hparts
  have hGbound : ∀ n : ℕ, ‖∑ j ∈ Finset.range n, w ^ j‖ ≤ 2 / ‖1 - w‖ :=
    fun n => norm_geom_sum_le hw hne n
  have hstep : ∀ i : ℕ,
      ‖((a (i + 1) : ℂ) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), w ^ j‖
        ≤ (a i - a (i + 1)) * (2 / ‖1 - w‖) := by
    intro i
    rw [norm_mul]
    have hcast : ((a (i + 1) : ℂ) - (a i : ℂ)) = ((a (i + 1) - a i : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have habs : |a (i + 1) - a i| = a i - a (i + 1) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ i)))
    rw [habs]
    have hd : 0 ≤ a i - a (i + 1) := sub_nonneg.mpr (hmono (Nat.le_succ i))
    exact mul_le_mul_of_nonneg_left (hGbound (i + 1)) hd
  calc ‖∑ m ∈ Finset.range K, (a m : ℂ) * w ^ m‖
      = ‖(a (K - 1) : ℂ) * ∑ i ∈ Finset.range K, w ^ i
          - ∑ i ∈ Finset.range (K - 1),
              (((a (i + 1) : ℂ)) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), w ^ j‖ := by
        rw [hparts]
    _ ≤ ‖(a (K - 1) : ℂ) * ∑ i ∈ Finset.range K, w ^ i‖
          + ‖∑ i ∈ Finset.range (K - 1),
              (((a (i + 1) : ℂ)) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), w ^ j‖ :=
        norm_sub_le _ _
    _ ≤ a (K - 1) * (2 / ‖1 - w‖)
          + ∑ i ∈ Finset.range (K - 1), (a i - a (i + 1)) * (2 / ‖1 - w‖) := by
        gcongr
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn _)]
          exact mul_le_mul_of_nonneg_left (hGbound K) (hnn _)
        · calc ‖∑ i ∈ Finset.range (K - 1),
                (((a (i + 1) : ℂ)) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), w ^ j‖
              ≤ ∑ i ∈ Finset.range (K - 1),
                  ‖(((a (i + 1) : ℂ)) - (a i : ℂ)) * ∑ j ∈ Finset.range (i + 1), w ^ j‖ :=
                norm_sum_le _ _
            _ ≤ ∑ i ∈ Finset.range (K - 1), (a i - a (i + 1)) * (2 / ‖1 - w‖) :=
                Finset.sum_le_sum fun i _ => hstep i
    _ = a (K - 1) * (2 / ‖1 - w‖)
          + (a 0 - a (K - 1)) * (2 / ‖1 - w‖) := by
        rw [← Finset.sum_mul, Finset.sum_range_sub' a (K - 1)]
    _ = 2 * a 0 / ‖1 - w‖ := by
        field_simp
        ring

/-- **The collective-push master bound (doc 50 §3)**: away from the
quarter-phase points, the net push of the whole lattice tail with antitone
nonnegative amplitudes is at most a₀/|cos 2πp| — bounded, not √M. -/
theorem collective_push_le (p : ℝ) (hp : Real.cos (2 * Real.pi * p) ≠ 0)
    {a : ℕ → ℝ} (hmono : Antitone a) (hnn : ∀ n, 0 ≤ a n) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, (a m : ℂ) *
        Complex.exp (((-(Real.pi * (4 * p * m + (m : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) * Complex.I)‖
      ≤ a 0 / |Real.cos (2 * Real.pi * p)| := by
  have hcol : ∀ m ∈ Finset.range K,
      (a m : ℂ) *
          Complex.exp (((-(Real.pi * (4 * p * m + (m : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) * Complex.I)
        = (a m : ℂ) * latticeRatio p ^ m := by
    intro m _
    rw [lattice_collapse]
  rw [Finset.sum_congr rfl hcol]
  have hbound := abel_geom_bound (norm_latticeRatio p) (latticeRatio_ne_one hp)
    hmono hnn K
  rw [resonance_denominator p] at hbound
  calc ‖∑ m ∈ Finset.range K, (a m : ℂ) * latticeRatio p ^ m‖
      ≤ 2 * a 0 / (2 * |Real.cos (2 * Real.pi * p)|) := hbound
    _ = a 0 / |Real.cos (2 * Real.pi * p)| :=
        mul_div_mul_left (a 0) _ two_ne_zero

/-- **One-wrap density (doc 51 §2(2))**: the rotation orbit {kϑ} enters the
window [ψ, ψ+ϑ) within one wrap — the deterministic dip-visiting mechanism. -/
theorem one_wrap_hit {ϑ ψ : ℝ} (hϑ : 0 < ϑ) (hψ : 0 ≤ ψ) :
    ∃ k : ℕ, ψ ≤ (k : ℝ) * ϑ ∧ (k : ℝ) * ϑ < ψ + ϑ := by
  refine ⟨(⌈ψ / ϑ⌉).toNat, ?_, ?_⟩
  · have h0 : (0 : ℤ) ≤ ⌈ψ / ϑ⌉ := Int.ceil_nonneg (div_nonneg hψ hϑ.le)
    have hcast : (((⌈ψ / ϑ⌉).toNat : ℕ) : ℝ) = ((⌈ψ / ϑ⌉ : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
    rw [hcast]
    have h1 : ψ / ϑ ≤ ((⌈ψ / ϑ⌉ : ℤ) : ℝ) := Int.le_ceil _
    calc ψ = ψ / ϑ * ϑ := by field_simp
      _ ≤ ((⌈ψ / ϑ⌉ : ℤ) : ℝ) * ϑ := mul_le_mul_of_nonneg_right h1 hϑ.le
  · have h0 : (0 : ℤ) ≤ ⌈ψ / ϑ⌉ := Int.ceil_nonneg (div_nonneg hψ hϑ.le)
    have hcast : (((⌈ψ / ϑ⌉).toNat : ℕ) : ℝ) = ((⌈ψ / ϑ⌉ : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg h0)
    rw [hcast]
    have h2 : ((⌈ψ / ϑ⌉ : ℤ) : ℝ) < ψ / ϑ + 1 := Int.ceil_lt_add_one _
    have h3 : ((⌈ψ / ϑ⌉ : ℤ) : ℝ) * ϑ < (ψ / ϑ + 1) * ϑ :=
      mul_lt_mul_of_pos_right h2 hϑ
    calc ((⌈ψ / ϑ⌉ : ℤ) : ℝ) * ϑ < (ψ / ϑ + 1) * ϑ := h3
      _ = ψ + ϑ := by field_simp

/-- **Survival floor (doc 51 §1)**: a pair that survives the first `K` pushes
has depth above every negative excursion of the push partial sums. -/
theorem survival_floor {η : ℝ} {S : ℕ → ℝ} {K : ℕ}
    (h : ∀ M ≤ K, 0 < η + S M) :
    ∀ M ≤ K, -S M < η := by
  intro M hM
  have := h M hM
  linarith

/-- **Collective push of the physical spectator-weight tail.**  For an increasing sequence `f`
of positive pole positions, the resonance-lattice tail weighted by the spectator amplitude
`rphi = csch² · coth` at those positions has net push at most `rphi (f 0) / |cos 2πp|`, for every
truncation `K`.  The weight sequence `n ↦ rphi (f n)` is antitone because `rphi` is strictly
decreasing on `(0, ∞)` and `f` is increasing, and nonnegative because `rphi > 0` there; the abstract
`collective_push_le` bound then applies. -/
theorem collective_push_rphi_le (p : ℝ) (hp : Real.cos (2 * Real.pi * p) ≠ 0)
    {f : ℕ → ℝ} (hpos : ∀ n, 0 < f n) (hmono : Monotone f) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, (rphi (f m) : ℂ) *
        Complex.exp (((-(Real.pi * (4 * p * m + (m : ℝ) ^ (2 : ℕ))) : ℝ) : ℂ) * Complex.I)‖
      ≤ rphi (f 0) / |Real.cos (2 * Real.pi * p)| := by
  refine collective_push_le p hp ?_ ?_ K
  · intro m n hmn
    exact rphi_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr (hpos m)) (Set.mem_Ioi.mpr (hpos n))
      (hmono hmn)
  · intro n; exact (rphi_pos_of_pos (hpos n)).le

end RHTower
