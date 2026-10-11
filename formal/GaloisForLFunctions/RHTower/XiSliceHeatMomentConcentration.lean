import GaloisForLFunctions.RHTower.RiemannKernelSharpLogDerivative
import GaloisForLFunctions.RHTower.XiSliceHeatTransferPositivity

/-!
# Concentration of the slice moment measures of `H_λ`

Let `g_λ(u) = Φ(u) e^{λu²}` (`λ ≥ 0`), the kernel of `H_λ`.  The slice moments of `H_λ` at height `t'`
are `M_n(t') = ∫∫ g_λ(u) g_λ(v) (u − v)ⁿ/n! e^{it'(u+v)}`.  For even `n` the weight
`g_λ(u) g_λ(v) (u − v)ⁿ` is nonnegative, and we show that it concentrates on the antidiagonal
`u + v = 0` as `n → ∞`:

  `∫∫ g_λ g_λ (u − v)ⁿ (u + v)² ≤ ε ∫∫ g_λ g_λ (u − v)ⁿ`   for all large even `n`
  (`exists_heatKernel_moment_concentration`).

Mechanism.  On the fibre `u − v = D` write `u = D/2 + τ`, `v = τ − D/2`.  The fibre profile
`k_D(τ) = g_λ(D/2 + τ) g_λ(D/2 − τ)` satisfies, by the sharp tail bounds
`|(log Φ)' + 2πe^{2u}| ≤ C` (`RHTower.riemannKernelReal_le_sharp`, `riemannKernelReal_ge_sharp`),

  `k_D(τ) ≤ k_D(0) exp(−πe^{D}(e^τ − e^{−τ})² + 18|τ| + 2λτ²)`,

so the fibre has width `≍ e^{−D/2}` and its normalised second moment tends to `0` as `D → ∞`
(`heatFibreMoment_le_eps_mul_fibreMass`).  The weight `Dⁿ` pushes the mass to large `|D|`.
-/

open Real MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- The kernel of `H_λ`: `g_λ(u) = Φ(u) e^{λu²}`. -/
def heatKernel (lam u : ℝ) : ℝ := riemannKernelReal u * Real.exp (lam * u ^ 2)

theorem heatKernel_pos (lam u : ℝ) : 0 < heatKernel lam u :=
  mul_pos (riemannKernelReal_pos u) (Real.exp_pos _)

theorem heatKernel_neg (lam u : ℝ) : heatKernel lam (-u) = heatKernel lam u := by
  unfold heatKernel
  rw [neg_sq, show riemannKernelReal (-u) = riemannKernelReal u by
    unfold riemannKernelReal; rw [abs_neg]]

theorem heatKernel_superExp {lam : ℝ} (hlam : 0 ≤ lam) : SuperExpKernel (heatKernel lam) :=
  riemannKernel_superExp.mul_exp_sq hlam

theorem continuous_heatKernel (lam : ℝ) : Continuous (heatKernel lam) := by
  unfold heatKernel
  have := continuous_riemannKernelReal
  fun_prop

/-! ## Elementary exponential inequalities -/

theorem sq_exp_sub_exp_neg_ge (τ : ℝ) : 4 * τ ^ 2 ≤ (Real.exp τ - Real.exp (-τ)) ^ 2 := by
  have hs : Real.exp τ - Real.exp (-τ) = 2 * Real.sinh τ := by rw [Real.sinh_eq]; ring
  rw [hs]
  rcases le_total 0 τ with h | h
  · have := Real.self_le_sinh_iff.mpr h
    nlinarith
  · have h' : -τ ≤ Real.sinh (-τ) := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_neg] at h'
    nlinarith

theorem sq_exp_sub_exp_neg_le {τ : ℝ} (hτ : |τ| ≤ 1) :
    (Real.exp τ - Real.exp (-τ)) ^ 2 ≤ 16 * τ ^ 2 := by
  have h1 := Real.abs_exp_sub_one_le hτ
  have h2 := Real.abs_exp_sub_one_le (x := -τ) (by rwa [abs_neg])
  rw [abs_neg] at h2
  have : |Real.exp τ - Real.exp (-τ)| ≤ 4 * |τ| := by
    calc |Real.exp τ - Real.exp (-τ)| = |(Real.exp τ - 1) - (Real.exp (-τ) - 1)| := by ring_nf
      _ ≤ |Real.exp τ - 1| + |Real.exp (-τ) - 1| := abs_sub _ _
      _ ≤ 4 * |τ| := by linarith
  calc (Real.exp τ - Real.exp (-τ)) ^ 2 = |Real.exp τ - Real.exp (-τ)| ^ 2 := (sq_abs _).symm
    _ ≤ (4 * |τ|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = 16 * τ ^ 2 := by rw [mul_pow, sq_abs]; norm_num

theorem exp_two_mul_add_sub (c τ : ℝ) :
    Real.exp (2 * (c + τ)) - Real.exp (2 * c) - (Real.exp (2 * c) - Real.exp (2 * (c - τ))) =
      Real.exp (2 * c) * (Real.exp τ - Real.exp (-τ)) ^ 2 := by
  have e1 : Real.exp (2 * (c + τ)) = Real.exp (2 * c) * Real.exp τ ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (2 * (c - τ)) = Real.exp (2 * c) * Real.exp (-τ) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have e3 : Real.exp τ * Real.exp (-τ) = 1 := by rw [← Real.exp_add]; simp
  rw [e1, e2, show (Real.exp τ - Real.exp (-τ)) ^ 2 =
    Real.exp τ ^ 2 - 2 * (Real.exp τ * Real.exp (-τ)) + Real.exp (-τ) ^ 2 by ring, e3]
  ring

/-! ## Fibre bounds for the kernel -/

/-- **Fibre upper bound.**  For `τ ≥ 0` and `½ log 3 ≤ c − τ`,
`Φ(c+τ) Φ(c−τ) ≤ Φ(c)² exp(−πe^{2c}(e^τ − e^{−τ})² + (5 + 4π)τ)`. -/
theorem riemannKernelReal_fibre_le {c τ : ℝ} (hτ : 0 ≤ τ) (hc : Real.log 3 / 2 ≤ c - τ) :
    riemannKernelReal (c + τ) * riemannKernelReal (c - τ) ≤
      riemannKernelReal c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
        (Real.exp τ - Real.exp (-τ)) ^ 2)) + (5 + 4 * π) * τ) := by
  have hl3 : 0 ≤ Real.log 3 / 2 := by positivity
  have h1 := riemannKernelReal_le_sharp (a := c) (b := c + τ) (by linarith) (by linarith)
  have h2 := riemannKernelReal_ge_sharp (a := c - τ) (b := c) (by linarith) (by linarith)
  have hΦc := riemannKernelReal_pos c
  have hΦm := riemannKernelReal_pos (c - τ)
  have hΦp := riemannKernelReal_pos (c + τ)
  -- `Φ(c − τ) ≤ Φ(c) e^{π(e^{2c} − e^{2(c−τ)}) + 4πτ}`
  have h2' : riemannKernelReal (c - τ) ≤ riemannKernelReal c *
      Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) + 4 * π * τ) := by
    have hE : Real.exp (-(π * (Real.exp (2 * c) - Real.exp (2 * (c - τ)))) - 4 * π * (c - (c - τ))) *
        Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) + 4 * π * τ) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc riemannKernelReal (c - τ) = riemannKernelReal (c - τ) *
          Real.exp (-(π * (Real.exp (2 * c) - Real.exp (2 * (c - τ)))) - 4 * π * (c - (c - τ))) *
          Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) + 4 * π * τ) := by
          rw [mul_assoc, hE, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  calc riemannKernelReal (c + τ) * riemannKernelReal (c - τ)
      ≤ (riemannKernelReal c * Real.exp (-(π * (Real.exp (2 * (c + τ)) - Real.exp (2 * c))) +
          5 * (c + τ - c))) * (riemannKernelReal c *
          Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) + 4 * π * τ)) :=
        mul_le_mul h1 h2' hΦm.le (by positivity)
    _ = riemannKernelReal c ^ 2 * Real.exp (-(π * (Real.exp (2 * (c + τ)) - Real.exp (2 * c) -
          (Real.exp (2 * c) - Real.exp (2 * (c - τ))))) + (5 + 4 * π) * τ) := by
        rw [mul_mul_mul_comm, ← Real.exp_add, ← sq]; ring_nf
    _ = _ := by rw [exp_two_mul_add_sub]

/-- **Fibre lower bound.**  For `τ ≥ 0` and `½ log 3 ≤ c − τ`,
`Φ(c)² exp(−πe^{2c}(e^τ − e^{−τ})² − (5 + 4π)τ) ≤ Φ(c+τ) Φ(c−τ)`. -/
theorem riemannKernelReal_fibre_ge {c τ : ℝ} (hτ : 0 ≤ τ) (hc : Real.log 3 / 2 ≤ c - τ) :
    riemannKernelReal c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
        (Real.exp τ - Real.exp (-τ)) ^ 2)) - (5 + 4 * π) * τ) ≤
      riemannKernelReal (c + τ) * riemannKernelReal (c - τ) := by
  have hl3 : 0 ≤ Real.log 3 / 2 := by positivity
  have h1 := riemannKernelReal_ge_sharp (a := c) (b := c + τ) (by linarith) (by linarith)
  have h2 := riemannKernelReal_le_sharp (a := c - τ) (b := c) hc (by linarith)
  have hΦc := riemannKernelReal_pos c
  have hΦm := riemannKernelReal_pos (c - τ)
  -- `Φ(c) e^{π(e^{2c} − e^{2(c−τ)}) − 5τ} ≤ Φ(c − τ)`
  have h2' : riemannKernelReal c *
      Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) - 5 * τ) ≤
        riemannKernelReal (c - τ) := by
    have hE : Real.exp (-(π * (Real.exp (2 * c) - Real.exp (2 * (c - τ)))) + 5 * (c - (c - τ))) *
        Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) - 5 * τ) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc riemannKernelReal c * Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) - 5 * τ)
        ≤ riemannKernelReal (c - τ) *
            Real.exp (-(π * (Real.exp (2 * c) - Real.exp (2 * (c - τ)))) + 5 * (c - (c - τ))) *
            Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) - 5 * τ) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = riemannKernelReal (c - τ) := by rw [mul_assoc, hE, mul_one]
  calc riemannKernelReal c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
        (Real.exp τ - Real.exp (-τ)) ^ 2)) - (5 + 4 * π) * τ)
      = (riemannKernelReal c * Real.exp (-(π * (Real.exp (2 * (c + τ)) - Real.exp (2 * c))) -
          4 * π * (c + τ - c))) * (riemannKernelReal c *
          Real.exp (π * (Real.exp (2 * c) - Real.exp (2 * (c - τ))) - 5 * τ)) := by
        rw [← exp_two_mul_add_sub, mul_mul_mul_comm, ← Real.exp_add, ← sq]; ring_nf
    _ ≤ riemannKernelReal (c + τ) * riemannKernelReal (c - τ) :=
        mul_le_mul h1 h2' (by positivity) (riemannKernelReal_pos _).le

/-- The fibre profile `k_D(τ) = g_λ(c + τ) g_λ(c − τ)`, `c = D/2`, is even in `τ`. -/
theorem heatKernel_fibre_symm (lam c τ : ℝ) :
    heatKernel lam (c + -τ) * heatKernel lam (c - -τ) =
      heatKernel lam (c + τ) * heatKernel lam (c - τ) := by
  rw [show c + -τ = c - τ by ring, show c - -τ = c + τ by ring, mul_comm]

theorem heatKernel_fibre_eq (lam c τ : ℝ) :
    heatKernel lam (c + τ) * heatKernel lam (c - τ) =
      riemannKernelReal (c + τ) * riemannKernelReal (c - τ) *
        (Real.exp (lam * c ^ 2) ^ 2 * Real.exp (2 * lam * τ ^ 2)) := by
  unfold heatKernel
  rw [← Real.exp_nat_mul]
  have : Real.exp (lam * (c + τ) ^ 2) * Real.exp (lam * (c - τ) ^ 2) =
      Real.exp (((2 : ℕ) : ℝ) * (lam * c ^ 2)) * Real.exp (2 * lam * τ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
  calc riemannKernelReal (c + τ) * Real.exp (lam * (c + τ) ^ 2) *
        (riemannKernelReal (c - τ) * Real.exp (lam * (c - τ) ^ 2))
      = riemannKernelReal (c + τ) * riemannKernelReal (c - τ) *
          (Real.exp (lam * (c + τ) ^ 2) * Real.exp (lam * (c - τ) ^ 2)) := by ring
    _ = _ := by rw [this]

theorem heatKernel_sq_eq (lam c : ℝ) :
    heatKernel lam c ^ 2 = riemannKernelReal c ^ 2 * Real.exp (lam * c ^ 2) ^ 2 := by
  unfold heatKernel; ring

/-- **Fibre upper bound for `g_λ`.**  For `½ log 3 ≤ c − |τ|`,
`k(τ) ≤ k(0) exp(−πe^{2c}(e^τ − e^{−τ})² + 18|τ| + 2λτ²)`. -/
theorem heatKernel_fibre_le (lam : ℝ) {c τ : ℝ} (hc : Real.log 3 / 2 ≤ c - |τ|) :
    heatKernel lam (c + τ) * heatKernel lam (c - τ) ≤
      heatKernel lam c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
        (Real.exp τ - Real.exp (-τ)) ^ 2)) + 18 * |τ| + 2 * lam * τ ^ 2) := by
  have key : ∀ σ : ℝ, 0 ≤ σ → Real.log 3 / 2 ≤ c - σ →
      heatKernel lam (c + σ) * heatKernel lam (c - σ) ≤
        heatKernel lam c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
          (Real.exp σ - Real.exp (-σ)) ^ 2)) + 18 * σ + 2 * lam * σ ^ 2) := by
    intro σ hσ hcσ
    rw [heatKernel_fibre_eq, heatKernel_sq_eq]
    have hf := riemannKernelReal_fibre_le hσ hcσ
    have h18 : (5 + 4 * π) * σ ≤ 18 * σ := by
      have := Real.pi_lt_d2; nlinarith
    have hE : Real.exp (-(π * (Real.exp (2 * c) * (Real.exp σ - Real.exp (-σ)) ^ 2)) +
        (5 + 4 * π) * σ) ≤ Real.exp (-(π * (Real.exp (2 * c) * (Real.exp σ - Real.exp (-σ)) ^ 2)) +
          18 * σ) := Real.exp_le_exp.mpr (by linarith)
    have hG : 0 ≤ Real.exp (lam * c ^ 2) ^ 2 * Real.exp (2 * lam * σ ^ 2) := by positivity
    calc riemannKernelReal (c + σ) * riemannKernelReal (c - σ) *
          (Real.exp (lam * c ^ 2) ^ 2 * Real.exp (2 * lam * σ ^ 2))
        ≤ riemannKernelReal c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
            (Real.exp σ - Real.exp (-σ)) ^ 2)) + 18 * σ) *
            (Real.exp (lam * c ^ 2) ^ 2 * Real.exp (2 * lam * σ ^ 2)) :=
          mul_le_mul_of_nonneg_right (hf.trans (mul_le_mul_of_nonneg_left hE (by positivity))) hG
      _ = _ := by
          rw [Real.exp_add (-(π * (Real.exp (2 * c) * (Real.exp σ - Real.exp (-σ)) ^ 2)) + 18 * σ)
            (2 * lam * σ ^ 2)]
          ring
  rcases le_total 0 τ with h | h
  · rw [abs_of_nonneg h] at hc ⊢
    exact key τ h hc
  · rw [abs_of_nonpos h] at hc ⊢
    have := key (-τ) (by linarith) hc
    rw [heatKernel_fibre_symm, neg_sq] at this
    rw [show (Real.exp τ - Real.exp (-τ)) ^ 2 = (Real.exp (-τ) - Real.exp (- -τ)) ^ 2 by
      rw [neg_neg]; ring]
    exact this

/-- **Fibre lower bound for `g_λ`.**  For `½ log 3 ≤ c − |τ|` and `λ ≥ 0`,
`k(0) exp(−πe^{2c}(e^τ − e^{−τ})² − 18|τ|) ≤ k(τ)`. -/
theorem heatKernel_fibre_ge {lam : ℝ} (hlam : 0 ≤ lam) {c τ : ℝ}
    (hc : Real.log 3 / 2 ≤ c - |τ|) :
    heatKernel lam c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
        (Real.exp τ - Real.exp (-τ)) ^ 2)) - 18 * |τ|) ≤
      heatKernel lam (c + τ) * heatKernel lam (c - τ) := by
  have key : ∀ σ : ℝ, 0 ≤ σ → Real.log 3 / 2 ≤ c - σ →
      heatKernel lam c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
          (Real.exp σ - Real.exp (-σ)) ^ 2)) - 18 * σ) ≤
        heatKernel lam (c + σ) * heatKernel lam (c - σ) := by
    intro σ hσ hcσ
    rw [heatKernel_fibre_eq, heatKernel_sq_eq]
    have hf := riemannKernelReal_fibre_ge hσ hcσ
    have h18 : (5 + 4 * π) * σ ≤ 18 * σ := by
      have := Real.pi_lt_d2; nlinarith
    have hE : Real.exp (-(π * (Real.exp (2 * c) * (Real.exp σ - Real.exp (-σ)) ^ 2)) - 18 * σ) ≤
        Real.exp (-(π * (Real.exp (2 * c) * (Real.exp σ - Real.exp (-σ)) ^ 2)) -
          (5 + 4 * π) * σ) := Real.exp_le_exp.mpr (by linarith)
    have hG1 : 1 ≤ Real.exp (2 * lam * σ ^ 2) := Real.one_le_exp (by positivity)
    have hP : 0 ≤ riemannKernelReal (c + σ) * riemannKernelReal (c - σ) :=
      mul_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le
    calc riemannKernelReal c ^ 2 * Real.exp (lam * c ^ 2) ^ 2 *
          Real.exp (-(π * (Real.exp (2 * c) * (Real.exp σ - Real.exp (-σ)) ^ 2)) - 18 * σ)
        ≤ riemannKernelReal c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
            (Real.exp σ - Real.exp (-σ)) ^ 2)) - (5 + 4 * π) * σ) *
            Real.exp (lam * c ^ 2) ^ 2 := by
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity))
            (by positivity)
      _ ≤ riemannKernelReal (c + σ) * riemannKernelReal (c - σ) * Real.exp (lam * c ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hf (by positivity)
      _ ≤ riemannKernelReal (c + σ) * riemannKernelReal (c - σ) *
            (Real.exp (lam * c ^ 2) ^ 2 * Real.exp (2 * lam * σ ^ 2)) := by
          rw [← mul_assoc]
          exact le_mul_of_one_le_right (by positivity) hG1
  rcases le_total 0 τ with h | h
  · rw [abs_of_nonneg h] at hc ⊢
    exact key τ h hc
  · rw [abs_of_nonpos h] at hc ⊢
    have := key (-τ) (by linarith) hc
    rw [heatKernel_fibre_symm] at this
    rw [show (Real.exp τ - Real.exp (-τ)) ^ 2 = (Real.exp (-τ) - Real.exp (- -τ)) ^ 2 by
      rw [neg_neg]; ring]
    exact this

/-! ## Boundedness, integrability and tails -/

theorem SuperExpKernel.exists_bound {g : ℝ → ℝ} (hg : SuperExpKernel g) :
    ∃ M : ℝ, 0 < M ∧ ∀ x, g x ≤ M := by
  obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := hg.decay
  obtain ⟨K, hK⟩ := exists_sq_le_exp hB hb hc
  refine ⟨A * Real.exp K + 1, by positivity, fun x => ?_⟩
  have h := kernel_mul_exp_le hA hB hb le_rfl hK x
  simp only [zero_mul, Real.exp_zero, mul_one, zero_div, mul_zero, add_zero, Real.log_one] at h
  have h2 : Real.exp (-(B * b ^ 2 / 4) * x ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ B * b ^ 2 / 4 * x ^ 2 := by positivity
    linarith
  calc g x ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) := hdec x
    _ ≤ A * Real.exp K * Real.exp (-(B * b ^ 2 / 4) * x ^ 2) := h
    _ ≤ A * Real.exp K * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ A * Real.exp K + 1 := by linarith

theorem sq_le_two_mul_exp_abs (x : ℝ) : x ^ 2 ≤ 2 * Real.exp |x| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  rw [sq_abs] at h
  nlinarith [abs_nonneg x]

/-- `τ ↦ g_λ(c + τ) τ²` is integrable. -/
theorem integrable_heatKernel_shift_mul_sq {lam : ℝ} (hlam : 0 ≤ lam) (c : ℝ) :
    Integrable (fun τ : ℝ => heatKernel lam (c + τ) * τ ^ 2) := by
  have hg := heatKernel_superExp hlam
  have hmaj : Integrable (fun x : ℝ => (4 + 4 * c ^ 2) * (heatKernel lam x * Real.exp (1 * |x|))) :=
    (hg.integrable_mul_exp 1).const_mul _
  have h1 : Integrable (fun x : ℝ => heatKernel lam x * (x - c) ^ 2) := by
    refine hmaj.mono' ((continuous_heatKernel lam).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg.nonneg x) (sq_nonneg _)), one_mul]
    have hx := sq_le_two_mul_exp_abs x
    have hE := Real.one_le_exp (abs_nonneg x)
    have hsq : (x - c) ^ 2 ≤ (4 + 4 * c ^ 2) * Real.exp |x| := by
      nlinarith [sq_nonneg (x + c), sq_nonneg c]
    calc heatKernel lam x * (x - c) ^ 2 ≤ heatKernel lam x * ((4 + 4 * c ^ 2) * Real.exp |x|) :=
          mul_le_mul_of_nonneg_left hsq (hg.nonneg x)
      _ = _ := by ring
  have h2 := h1.comp_add_right c
  refine h2.congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [add_comm τ c, add_sub_cancel_left]

/-- The fibre profile and its second moment are integrable. -/
theorem integrable_heatKernel_fibre {lam : ℝ} (hlam : 0 ≤ lam) (c : ℝ) :
    Integrable (fun τ : ℝ => heatKernel lam (c + τ) * heatKernel lam (c - τ)) ∧
      Integrable (fun τ : ℝ => heatKernel lam (c + τ) * heatKernel lam (c - τ) * τ ^ 2) := by
  have hg := heatKernel_superExp hlam
  obtain ⟨M, hM, hbound⟩ := hg.exists_bound
  have hcont : Continuous fun τ : ℝ => heatKernel lam (c - τ) :=
    (continuous_heatKernel lam).comp (by fun_prop)
  have hb : ∀ τ, ‖heatKernel lam (c - τ)‖ ≤ M := fun τ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg.nonneg _)]; exact hbound _
  have hI0 : Integrable (fun τ : ℝ => heatKernel lam (c + τ)) :=
    (hg.integrable_mul_exp 0 |>.congr (Eventually.of_forall fun x => by simp)).comp_add_left c
  constructor
  · have := hI0.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall hb)
    exact this.congr (Eventually.of_forall fun τ => by simp only; ring)
  · have := (integrable_heatKernel_shift_mul_sq hlam c).bdd_mul hcont.aestronglyMeasurable
      (Eventually.of_forall hb)
    exact this.congr (Eventually.of_forall fun τ => by simp only; ring)

/-- Tail of `g_λ` from a point of the tail: `g(c + σ) ≤ g(c) e^{−π(e^{2(c+σ)} − e^{2c}) + 5σ + λ(2cσ+σ²)}`. -/
theorem heatKernel_shift_le (lam : ℝ) {c σ : ℝ} (hc : Real.log 3 / 2 ≤ c) (hσ : 0 ≤ σ) :
    heatKernel lam (c + σ) ≤ heatKernel lam c *
      Real.exp (-(π * (Real.exp (2 * (c + σ)) - Real.exp (2 * c))) + 5 * σ +
        lam * (2 * c * σ + σ ^ 2)) := by
  have h := riemannKernelReal_le_sharp hc (show c ≤ c + σ by linarith)
  unfold heatKernel
  rw [show c + σ - c = σ by ring] at h
  have e : Real.exp (lam * (c + σ) ^ 2) = Real.exp (lam * c ^ 2) * Real.exp (lam * (2 * c * σ + σ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  calc riemannKernelReal (c + σ) * (Real.exp (lam * c ^ 2) * Real.exp (lam * (2 * c * σ + σ ^ 2)))
      ≤ riemannKernelReal c * Real.exp (-(π * (Real.exp (2 * (c + σ)) - Real.exp (2 * c))) + 5 * σ) *
          (Real.exp (lam * c ^ 2) * Real.exp (lam * (2 * c * σ + σ ^ 2))) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by rw [Real.exp_add (-(π * (Real.exp (2 * (c + σ)) - Real.exp (2 * c))) + 5 * σ)]; ring

/-- Lower bound on `g_λ` along the tail: `Φ(½ log 3) e^{−π(e^{2c} − 3) − 4π(c − ½ log 3)} ≤ g_λ(c)`. -/
theorem heatKernel_ge_base {lam : ℝ} (hlam : 0 ≤ lam) {c : ℝ} (hc : Real.log 3 / 2 ≤ c) :
    riemannKernelReal (Real.log 3 / 2) *
        Real.exp (-(π * (Real.exp (2 * c) - 3)) - 4 * π * (c - Real.log 3 / 2)) ≤
      heatKernel lam c := by
  have h := riemannKernelReal_ge_sharp (a := Real.log 3 / 2) (b := c) (by positivity) hc
  have e3 : Real.exp (2 * (Real.log 3 / 2)) = 3 := by
    rw [show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
  rw [e3] at h
  unfold heatKernel
  have h1 : 1 ≤ Real.exp (lam * c ^ 2) := Real.one_le_exp (by positivity)
  calc riemannKernelReal (Real.log 3 / 2) *
        Real.exp (-(π * (Real.exp (2 * c) - 3)) - 4 * π * (c - Real.log 3 / 2))
      ≤ riemannKernelReal c := h
    _ ≤ riemannKernelReal c * Real.exp (lam * c ^ 2) :=
        le_mul_of_one_le_right (riemannKernelReal_pos c).le h1

/-! ## The fibre profile away from its centre -/

/-- `e^{2c} ≥ 2c²` for `c ≥ 0`. -/
private theorem two_mul_sq_le_exp_two_mul {c : ℝ} (hc : 0 ≤ c) : 2 * c ^ 2 ≤ Real.exp (2 * c) := by
  have := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * c)
  nlinarith

/-- `e^{2c} ≥ c⁴/4` for `c ≥ 0`. -/
theorem pow_four_le_exp_two_mul {c : ℝ} (hc : 0 ≤ c) : c ^ 4 / 4 ≤ Real.exp (2 * c) := by
  have h := Real.quadratic_le_exp_of_nonneg hc
  have e : Real.exp (2 * c) = Real.exp c ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h2 : c ^ 2 / 2 ≤ Real.exp c := by nlinarith
  nlinarith [sq_nonneg (c ^ 2 / 2)]

/-- **Near part.**  For `|τ| ≥ δ` and large `c`,
`exp(−πe^{2c}(e^τ − e^{−τ})² + 18|τ| + 2λτ²) ≤ θ e^{−c} e^{−πτ²}`. -/
theorem exists_fibre_near {lam δ θ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 < δ) (hθ : 0 < θ) :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ τ : ℝ, δ ≤ |τ| →
      Real.exp (-(π * (Real.exp (2 * c) * (Real.exp τ - Real.exp (-τ)) ^ 2)) + 18 * |τ| +
        2 * lam * τ ^ 2) ≤ θ * Real.exp (-c) * Real.exp (-(π * τ ^ 2)) := by
  set A : ℝ := 18 / δ + 2 * lam + π + |Real.log θ| / δ ^ 2 with hA
  set B : ℝ := 1 / δ ^ 2 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨1 + A + B, by positivity, fun c hc τ hτ => ?_⟩
  have hc1 : 1 ≤ c := by linarith
  have hE := two_mul_sq_le_exp_two_mul (by linarith : 0 ≤ c)
  have hπ := Real.pi_gt_three
  -- `4πe^{2c} ≥ A + Bc`
  have hQ : A + B * c ≤ 4 * π * Real.exp (2 * c) := by
    have h1 : A + B * c ≤ (A + B) * c := by nlinarith
    have h2 : (A + B) * c ≤ c * c := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h3 : c * c ≤ 4 * π * Real.exp (2 * c) := by nlinarith [Real.exp_pos (2 * c)]
    linarith
  have hτ0 : 0 < |τ| := lt_of_lt_of_le hδ hτ
  have hsq := sq_exp_sub_exp_neg_ge τ
  have hτ2 : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
  have hlin : 18 * |τ| ≤ 18 / δ * τ ^ 2 := by
    rw [hτ2, div_mul_eq_mul_div, le_div_iff₀ hδ]; nlinarith
  have hδτ : δ ^ 2 ≤ τ ^ 2 := by rw [hτ2]; exact pow_le_pow_left₀ hδ.le hτ 2
  rw [show θ * Real.exp (-c) * Real.exp (-(π * τ ^ 2)) =
    Real.exp (Real.log θ + -c + -(π * τ ^ 2)) by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hθ]]
  apply Real.exp_le_exp.mpr
  have hEnn : 0 ≤ Real.exp (2 * c) := (Real.exp_pos _).le
  have h1 : π * (Real.exp (2 * c) * (4 * τ ^ 2)) ≤
      π * (Real.exp (2 * c) * (Real.exp τ - Real.exp (-τ)) ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hEnn) Real.pi_pos.le
  have hcoef : B * c + |Real.log θ| / δ ^ 2 ≤ 4 * π * Real.exp (2 * c) - 18 / δ - 2 * lam - π := by
    rw [hA] at hQ; linarith
  have hcoef0 : 0 ≤ B * c + |Real.log θ| / δ ^ 2 := by positivity
  have h2 : (B * c + |Real.log θ| / δ ^ 2) * δ ^ 2 ≤
      (4 * π * Real.exp (2 * c) - 18 / δ - 2 * lam - π) * τ ^ 2 :=
    mul_le_mul hcoef hδτ (by positivity) (le_trans hcoef0 hcoef)
  have e : (B * c + |Real.log θ| / δ ^ 2) * δ ^ 2 = c + |Real.log θ| := by
    rw [hB]; field_simp
  have hl := neg_abs_le (Real.log θ)
  nlinarith

theorem far_poly {lam K c : ℝ} (hc : 15 + 2 * lam ^ 2 + (1 + 4 * π) + |K| ≤ c) :
    13 + 2 * lam ^ 2 * c ^ 2 + (1 + 4 * π) * c + |K| ≤ π * (c ^ 4 / 4) := by
  have hπ := Real.pi_gt_three
  set P : ℝ := 13 + 2 * lam ^ 2 + (1 + 4 * π) + |K| with hP
  have hP0 : 0 ≤ P := by positivity
  have hcP : P + 2 ≤ c := by rw [hP]; linarith
  have hc1 : 1 ≤ c := by linarith
  have hcsq1 : 1 ≤ c ^ 2 := one_le_pow₀ hc1
  have hcsq : c ≤ c ^ 2 := by nlinarith
  have hsq : (P + 2) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by positivity) hcP 2
  have hc2 : 4 / 3 * P ≤ c ^ 2 := by nlinarith [sq_nonneg P]
  have a2 : (1 + 4 * π) * c ≤ (1 + 4 * π) * c ^ 2 := mul_le_mul_of_nonneg_left hcsq (by positivity)
  have a3 : |K| ≤ |K| * c ^ 2 := le_mul_of_one_le_right (abs_nonneg _) hcsq1
  have hlhs : 13 + 2 * lam ^ 2 * c ^ 2 + (1 + 4 * π) * c + |K| ≤ P * c ^ 2 := by
    rw [hP]; linarith
  have h4 : 4 / 3 * P * c ^ 2 ≤ c ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg c)
  have h5 : 3 * (c ^ 2 * c ^ 2) ≤ π * (c ^ 2 * c ^ 2) :=
    mul_le_mul_of_nonneg_right hπ.le (by positivity)
  have e : c ^ 4 = c ^ 2 * c ^ 2 := by ring
  rw [e]
  linarith

theorem far_exponent_ineq {lam c σ E F K₀ : ℝ} (hF : 3 + 2 * σ ^ 2 ≤ F) (hE0 : 0 ≤ E)
    (hcoef : lam + π + 1 ≤ 2 * π * E) (hE4 : c ^ 4 / 4 ≤ E)
    (hpoly : 13 + 2 * lam ^ 2 * c ^ 2 + (1 + 4 * π) * c + |K₀| ≤ π * (c ^ 4 / 4)) :
    -(π * (E * F - E)) + 5 * σ + lam * (2 * c * σ + σ ^ 2) ≤
      K₀ - c - π * E - 4 * π * c - π * σ ^ 2 := by
  have G1 : π * (E * (3 + 2 * σ ^ 2)) ≤ π * (E * F) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hE0) Real.pi_pos.le
  have G2 : (lam + π + 1) * σ ^ 2 ≤ 2 * π * E * σ ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg σ)
  have F3 : σ * (5 + 2 * lam * c) ≤ σ ^ 2 + (5 + 2 * lam * c) ^ 2 / 4 := by
    nlinarith [sq_nonneg (σ - (5 + 2 * lam * c) / 2)]
  have F4 : (5 + 2 * lam * c) ^ 2 / 4 ≤ 13 + 2 * lam ^ 2 * c ^ 2 := by
    nlinarith [sq_nonneg (5 - 2 * lam * c)]
  have G5 : π * (c ^ 4 / 4) ≤ π * E := mul_le_mul_of_nonneg_left hE4 Real.pi_pos.le
  have hK := neg_abs_le K₀
  linarith

/-- **Far part.**  For `σ ≥ c − ½ log 3` and large `c`,
`M e^{−π(e^{2(c+σ)} − e^{2c}) + 5σ + λ(2cσ+σ²)} ≤ θ e^{−c} L(c) e^{−πσ²}` with
`L(c) = Φ₀ e^{−π(e^{2c} − 3) − 4π(c − ½ log 3)}`. -/
theorem exists_fibre_far {lam M θ Φ₀ : ℝ} (hlam : 0 ≤ lam) (hM : 0 < M) (hθ : 0 < θ)
    (hΦ₀ : 0 < Φ₀) :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ σ, c - Real.log 3 / 2 ≤ σ →
      M * Real.exp (-(π * (Real.exp (2 * (c + σ)) - Real.exp (2 * c))) + 5 * σ +
          lam * (2 * c * σ + σ ^ 2)) ≤
        θ * Real.exp (-c) * (Φ₀ * Real.exp (-(π * (Real.exp (2 * c) - 3)) -
          4 * π * (c - Real.log 3 / 2))) * Real.exp (-(π * σ ^ 2)) := by
  set x₀ : ℝ := Real.log 3 / 2 with hx₀
  have hx₀0 : 0 ≤ x₀ := by positivity
  set K₀ : ℝ := Real.log θ + Real.log Φ₀ - Real.log M + 3 * π + 4 * π * x₀ with hK₀
  set R : ℝ := 15 + 2 * lam ^ 2 + (1 + 4 * π) + |K₀| + x₀ + lam + π + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨R, hR0, fun c hc σ hσ => ?_⟩
  have hπ := Real.pi_gt_three
  have hc2 : 2 + x₀ ≤ c := by
    have : 0 ≤ 15 + 2 * lam ^ 2 + (1 + 4 * π) + |K₀| + lam + π := by positivity
    linarith
  have hσ1 : 1 ≤ σ := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hσE : 3 + 2 * σ ^ 2 ≤ Real.exp (2 * σ) := by
    have := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * σ); nlinarith
  have hEc := Real.exp_pos (2 * c)
  have hsplit : Real.exp (2 * (c + σ)) = Real.exp (2 * c) * Real.exp (2 * σ) := by
    rw [← Real.exp_add]; ring_nf
  have hE4 := pow_four_le_exp_two_mul hc0
  have hlc : lam + π + 1 ≤ c := by
    have : 0 ≤ 15 + 2 * lam ^ 2 + 4 * π + |K₀| + x₀ := by positivity
    linarith
  have hcE : c ≤ Real.exp (2 * c) := by
    have := Real.add_one_le_exp (2 * c); linarith
  have hcoef : lam + π + 1 ≤ 2 * π * Real.exp (2 * c) := by nlinarith
  have hpoly := far_poly (lam := lam) (K := K₀) (c := c) (by
    have : 0 ≤ x₀ + lam + π + 2 := by positivity
    linarith)
  have hineq := far_exponent_ineq (σ := σ) hσE hEc.le hcoef hE4 hpoly
  have key : Real.log M + (-(π * (Real.exp (2 * (c + σ)) - Real.exp (2 * c))) + 5 * σ +
      lam * (2 * c * σ + σ ^ 2)) ≤ Real.log θ + -c + (Real.log Φ₀ + (-(π * (Real.exp (2 * c) - 3)) -
        4 * π * (c - x₀))) + -(π * σ ^ 2) := by
    rw [hsplit]; rw [hK₀] at hineq; linarith
  have eL : M * Real.exp (-(π * (Real.exp (2 * (c + σ)) - Real.exp (2 * c))) + 5 * σ +
      lam * (2 * c * σ + σ ^ 2)) = Real.exp (Real.log M + (-(π * (Real.exp (2 * (c + σ)) -
        Real.exp (2 * c))) + 5 * σ + lam * (2 * c * σ + σ ^ 2))) := by
    rw [Real.exp_add (Real.log M), Real.exp_log hM]
  have eR : θ * Real.exp (-c) * (Φ₀ * Real.exp (-(π * (Real.exp (2 * c) - 3)) -
      4 * π * (c - x₀))) * Real.exp (-(π * σ ^ 2)) = Real.exp (Real.log θ + -c + (Real.log Φ₀ +
        (-(π * (Real.exp (2 * c) - 3)) - 4 * π * (c - x₀))) + -(π * σ ^ 2)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hθ, Real.exp_log hΦ₀]
  rw [eL, eR]
  exact Real.exp_le_exp.mpr key

/-- **Pointwise smallness of the fibre off its centre.**  For `δ > 0`, `θ > 0` and all large `c`,
`g(c+τ) g(c−τ) ≤ θ e^{−c} g(c)² e^{−πτ²}` whenever `|τ| ≥ δ`. -/
theorem exists_heatKernel_fibre_small {lam δ θ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 < δ) (hθ : 0 < θ) :
    ∃ c₁ : ℝ, Real.log 3 / 2 ≤ c₁ ∧ ∀ c, c₁ ≤ c → ∀ τ : ℝ, δ ≤ |τ| →
      heatKernel lam (c + τ) * heatKernel lam (c - τ) ≤
        θ * (Real.exp (-c) * heatKernel lam c ^ 2) * Real.exp (-(π * τ ^ 2)) := by
  obtain ⟨M, hM, hbound⟩ := (heatKernel_superExp hlam).exists_bound
  have hΦ₀ := riemannKernelReal_pos (Real.log 3 / 2)
  obtain ⟨cA, hcA0, hA⟩ := exists_fibre_near hlam hδ hθ
  obtain ⟨cB, hcB0, hB⟩ := exists_fibre_far hlam hM hθ hΦ₀
  have hx₀ : 0 ≤ Real.log 3 / 2 := by positivity
  refine ⟨max (Real.log 3 / 2) (max cA cB), le_max_left _ _, fun c hc τ hτ => ?_⟩
  have hcx : Real.log 3 / 2 ≤ c := le_trans (le_max_left _ _) hc
  have hcA : cA ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hc
  have hcB : cB ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hc
  have hg2 : 0 ≤ heatKernel lam c ^ 2 := sq_nonneg _
  rcases le_or_gt |τ| (c - Real.log 3 / 2) with hnear | hfar
  · have h := heatKernel_fibre_le lam (c := c) (τ := τ) (by linarith)
    calc heatKernel lam (c + τ) * heatKernel lam (c - τ)
        ≤ heatKernel lam c ^ 2 * Real.exp (-(π * (Real.exp (2 * c) *
            (Real.exp τ - Real.exp (-τ)) ^ 2)) + 18 * |τ| + 2 * lam * τ ^ 2) := h
      _ ≤ heatKernel lam c ^ 2 * (θ * Real.exp (-c) * Real.exp (-(π * τ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hA c hcA τ hτ) hg2
      _ = _ := by ring
  · -- reduce to `τ ≥ 0` by symmetry
    have hk : heatKernel lam (c + τ) * heatKernel lam (c - τ) =
        heatKernel lam (c + |τ|) * heatKernel lam (c - |τ|) := by
      rcases le_total 0 τ with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, show c + -τ = c - τ by ring, show c - -τ = c + τ by ring, mul_comm]
    rw [hk, show τ ^ 2 = |τ| ^ 2 from (sq_abs τ).symm]
    have hσ : 0 ≤ |τ| := abs_nonneg τ
    have h1 := heatKernel_shift_le lam hcx hσ
    have h2 : heatKernel lam (c - |τ|) ≤ M := hbound _
    have hL := heatKernel_ge_base hlam hcx
    have hfarB := hB c hcB |τ| hfar.le
    have hgc := heatKernel_pos lam c
    calc heatKernel lam (c + |τ|) * heatKernel lam (c - |τ|)
        ≤ (heatKernel lam c * Real.exp (-(π * (Real.exp (2 * (c + |τ|)) - Real.exp (2 * c))) +
            5 * |τ| + lam * (2 * c * |τ| + |τ| ^ 2))) * M :=
          mul_le_mul h1 h2 (heatKernel_pos _ _).le (by positivity)
      _ = heatKernel lam c * (M * Real.exp (-(π * (Real.exp (2 * (c + |τ|)) -
            Real.exp (2 * c))) + 5 * |τ| + lam * (2 * c * |τ| + |τ| ^ 2))) := by ring
      _ ≤ heatKernel lam c * (θ * Real.exp (-c) * (riemannKernelReal (Real.log 3 / 2) *
            Real.exp (-(π * (Real.exp (2 * c) - 3)) - 4 * π * (c - Real.log 3 / 2))) *
            Real.exp (-(π * |τ| ^ 2))) := mul_le_mul_of_nonneg_left hfarB hgc.le
      _ ≤ heatKernel lam c * (θ * Real.exp (-c) * heatKernel lam c * Real.exp (-(π * |τ| ^ 2))) := by
          gcongr
      _ = _ := by ring

/-! ## Fibre mass and fibre second moment -/

/-- The fibre mass `∫ g_λ(c + τ) g_λ(c − τ) dτ`. -/
def heatFibreMass (lam c : ℝ) : ℝ := ∫ τ : ℝ, heatKernel lam (c + τ) * heatKernel lam (c - τ)

/-- The fibre second moment `∫ g_λ(c + τ) g_λ(c − τ) τ² dτ`. -/
def heatFibreMoment (lam c : ℝ) : ℝ := ∫ τ : ℝ, heatKernel lam (c + τ) * heatKernel lam (c - τ) * τ ^ 2

theorem heatFibreMass_neg (lam c : ℝ) : heatFibreMass lam (-c) = heatFibreMass lam c := by
  unfold heatFibreMass
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [show -c + τ = -(c - τ) by ring, show -c - τ = -(c + τ) by ring, heatKernel_neg,
    heatKernel_neg, mul_comm]

theorem heatFibreMoment_neg (lam c : ℝ) : heatFibreMoment lam (-c) = heatFibreMoment lam c := by
  unfold heatFibreMoment
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [show -c + τ = -(c - τ) by ring, show -c - τ = -(c + τ) by ring, heatKernel_neg,
    heatKernel_neg, mul_comm (heatKernel lam (c - τ))]

theorem heatFibreMass_nonneg (lam c : ℝ) : 0 ≤ heatFibreMass lam c :=
  integral_nonneg fun _ => (mul_pos (heatKernel_pos _ _) (heatKernel_pos _ _)).le

/-- **Fibre mass from below.**  For `c ≥ ½ log 3 + 1`,
`heatFibreMass ≥ 2e^{−c} e^{−(16π+18)} g_λ(c)²`. -/
theorem heatFibreMass_ge {lam : ℝ} (hlam : 0 ≤ lam) {c : ℝ} (hc : Real.log 3 / 2 + 1 ≤ c) :
    2 * Real.exp (-c) * Real.exp (-(16 * π + 18)) * heatKernel lam c ^ 2 ≤ heatFibreMass lam c := by
  have hx₀ : 0 ≤ Real.log 3 / 2 := by positivity
  set η : ℝ := Real.exp (-c) with hη
  have hη0 : 0 < η := Real.exp_pos _
  have hη1 : η ≤ 1 := by rw [hη, Real.exp_le_one_iff]; linarith
  have hEη : Real.exp (2 * c) * η ^ 2 = 1 := by
    rw [hη, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf; simp
  obtain ⟨hI, -⟩ := integrable_heatKernel_fibre hlam c
  have hlow : ∀ τ ∈ Set.Icc (-η) η, heatKernel lam c ^ 2 * Real.exp (-(16 * π + 18)) ≤
      heatKernel lam (c + τ) * heatKernel lam (c - τ) := by
    intro τ hτ
    have habs : |τ| ≤ η := abs_le.mpr ⟨hτ.1, hτ.2⟩
    have h := heatKernel_fibre_ge hlam (c := c) (τ := τ) (by linarith)
    have hsq := sq_exp_sub_exp_neg_le (le_trans habs hη1)
    have hτ2 : τ ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hE0 := Real.exp_pos (2 * c)
    have h1 : π * (Real.exp (2 * c) * (Real.exp τ - Real.exp (-τ)) ^ 2) ≤ 16 * π := by
      have : Real.exp (2 * c) * (Real.exp τ - Real.exp (-τ)) ^ 2 ≤ 16 := by
        calc Real.exp (2 * c) * (Real.exp τ - Real.exp (-τ)) ^ 2 ≤ Real.exp (2 * c) * (16 * τ ^ 2) :=
              mul_le_mul_of_nonneg_left hsq hE0.le
          _ ≤ Real.exp (2 * c) * (16 * η ^ 2) := by gcongr
          _ = 16 := by rw [show Real.exp (2 * c) * (16 * η ^ 2) = 16 * (Real.exp (2 * c) * η ^ 2) by
                ring, hEη, mul_one]
      nlinarith [Real.pi_pos]
    have h2 : 18 * |τ| ≤ 18 := by linarith
    refine le_trans ?_ h
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)
  have hset := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hlow hI.integrableOn
  rw [Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hset
  have hle := setIntegral_le_integral (s := Set.Icc (-η) η) hI
    (Eventually.of_forall fun τ => (mul_pos (heatKernel_pos lam _) (heatKernel_pos lam _)).le)
  unfold heatFibreMass
  calc 2 * η * Real.exp (-(16 * π + 18)) * heatKernel lam c ^ 2
      = (η - -η) * (heatKernel lam c ^ 2 * Real.exp (-(16 * π + 18))) := by ring
    _ ≤ _ := hset.trans hle

theorem integrable_sq_mul_exp_neg_pi_sq :
    Integrable (fun τ : ℝ => τ ^ 2 * Real.exp (-(π * τ ^ 2))) := by
  have hmaj : Integrable (fun τ : ℝ => 2 / π * Real.exp (-(π / 2) * τ ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine hmaj.mono' (by fun_prop) (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := Real.add_one_le_exp (π / 2 * τ ^ 2)
  have hτ : τ ^ 2 ≤ 2 / π * Real.exp (π / 2 * τ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
    nlinarith [sq_nonneg τ, Real.pi_pos]
  calc τ ^ 2 * Real.exp (-(π * τ ^ 2))
      ≤ 2 / π * Real.exp (π / 2 * τ ^ 2) * Real.exp (-(π * τ ^ 2)) :=
        mul_le_mul_of_nonneg_right hτ (Real.exp_pos _).le
    _ = 2 / π * Real.exp (-(π / 2) * τ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- **Fibre concentration.**  For every `ε > 0` and all large `c`,
`heatFibreMoment λ c ≤ ε · heatFibreMass λ c`. -/
theorem exists_fibreMoment_le {lam : ℝ} (hlam : 0 ≤ lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ c₁ : ℝ, Real.log 3 / 2 + 1 ≤ c₁ ∧ ∀ c, c₁ ≤ c → heatFibreMoment lam c ≤ ε * heatFibreMass lam c := by
  set δ : ℝ := min 1 (Real.sqrt (ε / 2)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (Real.sqrt_pos.mpr (by positivity))
  have hδ2 : δ ^ 2 ≤ ε / 2 := by
    calc δ ^ 2 ≤ Real.sqrt (ε / 2) ^ 2 := pow_le_pow_left₀ hδ0.le (min_le_right _ _) 2
      _ = ε / 2 := Real.sq_sqrt (by positivity)
  set G₂ : ℝ := ∫ τ : ℝ, τ ^ 2 * Real.exp (-(π * τ ^ 2)) with hG₂
  have hG₂0 : 0 ≤ G₂ := integral_nonneg fun τ => by positivity
  set C : ℝ := Real.exp (16 * π + 18) with hC
  have hC0 : 0 < C := Real.exp_pos _
  set θ : ℝ := ε / (G₂ * C + 1) with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨c₁, hc₁x, hsmall⟩ := exists_heatKernel_fibre_small hlam hδ0 hθ0
  refine ⟨max c₁ (Real.log 3 / 2 + 1), le_max_right _ _, fun c hc => ?_⟩
  have hcc₁ : c₁ ≤ c := le_trans (le_max_left _ _) hc
  have hcx : Real.log 3 / 2 + 1 ≤ c := le_trans (le_max_right _ _) hc
  obtain ⟨hI, hI2⟩ := integrable_heatKernel_fibre hlam c
  set A : ℝ := Real.exp (-c) * heatKernel lam c ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ τ : ℝ, heatKernel lam (c + τ) * heatKernel lam (c - τ) * τ ^ 2 ≤
      δ ^ 2 * (heatKernel lam (c + τ) * heatKernel lam (c - τ)) +
        θ * A * (τ ^ 2 * Real.exp (-(π * τ ^ 2))) := by
    intro τ
    have hk0 : 0 ≤ heatKernel lam (c + τ) * heatKernel lam (c - τ) :=
      (mul_pos (heatKernel_pos _ _) (heatKernel_pos _ _)).le
    have hrest : 0 ≤ θ * A * (τ ^ 2 * Real.exp (-(π * τ ^ 2))) := by positivity
    rcases lt_or_ge |τ| δ with h | h
    · have hτ2 : τ ^ 2 ≤ δ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h.le 2
      have := mul_le_mul_of_nonneg_left hτ2 hk0
      linarith
    · have hb := hsmall c hcc₁ τ h
      have := mul_le_mul_of_nonneg_right hb (sq_nonneg τ)
      have hδk : 0 ≤ δ ^ 2 * (heatKernel lam (c + τ) * heatKernel lam (c - τ)) := by positivity
      calc heatKernel lam (c + τ) * heatKernel lam (c - τ) * τ ^ 2
          ≤ θ * A * Real.exp (-(π * τ ^ 2)) * τ ^ 2 := this
        _ = θ * A * (τ ^ 2 * Real.exp (-(π * τ ^ 2))) := by ring
        _ ≤ _ := by linarith
  have hmono : heatFibreMoment lam c ≤ δ ^ 2 * heatFibreMass lam c + θ * A * G₂ := by
    unfold heatFibreMoment heatFibreMass
    rw [← integral_const_mul, ← integral_const_mul (θ * A),
      ← integral_add (hI.const_mul _) (integrable_sq_mul_exp_neg_pi_sq.const_mul _)]
    exact integral_mono hI2 ((hI.const_mul _).add (integrable_sq_mul_exp_neg_pi_sq.const_mul _)) hpt
  have hmass := heatFibreMass_ge hlam hcx
  have hAmass : A ≤ C / 2 * heatFibreMass lam c := by
    have e : 2 * Real.exp (-c) * Real.exp (-(16 * π + 18)) * heatKernel lam c ^ 2 =
        2 / C * A := by
      rw [hC, hA, Real.exp_neg (16 * π + 18)]; field_simp
    rw [e] at hmass
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul_of_nonneg_left hmass hC0.le
    rw [show C * (2 / C * A) = 2 * A by field_simp] at this
    linarith
  have hθG : θ * G₂ * C ≤ ε := by
    rw [hθ, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hG₂0 hC0.le]
  have hM0 := heatFibreMass_nonneg lam c
  calc heatFibreMoment lam c ≤ δ ^ 2 * heatFibreMass lam c + θ * A * G₂ := hmono
    _ ≤ ε / 2 * heatFibreMass lam c + θ * (C / 2 * heatFibreMass lam c) * G₂ := by
        gcongr
    _ = ε / 2 * heatFibreMass lam c + θ * G₂ * C / 2 * heatFibreMass lam c := by ring
    _ ≤ ε / 2 * heatFibreMass lam c + ε / 2 * heatFibreMass lam c := by
        gcongr
    _ = ε * heatFibreMass lam c := by ring

/-! ## Fibre decomposition of the plane -/

/-- **Fibre decomposition.**  For integrable `F` on the plane,
`∫∫ F = ∫_D ∫_τ F(D/2 + τ, τ − D/2)`, and the inner integral is integrable in `D`. -/
theorem integral_eq_integral_fibre {F : ℝ × ℝ → ℝ} (hF : Integrable F) :
    Integrable (fun D : ℝ => ∫ τ : ℝ, F (D / 2 + τ, τ - D / 2)) ∧
      ∫ p : ℝ × ℝ, F p = ∫ D : ℝ, ∫ τ : ℝ, F (D / 2 + τ, τ - D / 2) := by
  have hmp : MeasurePreserving (MeasurableEquiv.shearAddRight ℝ) (volume : Measure (ℝ × ℝ))
      volume := by
    rw [Measure.volume_eq_prod]
    exact measurePreserving_prod_add volume volume
  set Fs : ℝ × ℝ → ℝ := fun p => F p.swap with hFs
  have hFsI : Integrable Fs := by
    have := hF.swap
    rw [← Measure.volume_eq_prod] at this
    exact this
  set G : ℝ × ℝ → ℝ := fun z => Fs (MeasurableEquiv.shearAddRight ℝ z) with hG
  have hGI : Integrable G := (hmp.integrable_comp hFsI.aestronglyMeasurable).mpr hFsI
  have h1 : ∫ p : ℝ × ℝ, F p = ∫ p : ℝ × ℝ, Fs p := by
    have := integral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) F
    rw [← Measure.volume_eq_prod] at this
    exact this.symm
  have h2 : ∫ p : ℝ × ℝ, Fs p = ∫ z : ℝ × ℝ, G z := (hmp.integral_comp' Fs).symm
  have hGprod : Integrable G ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hGI
  have h3 : ∫ z : ℝ × ℝ, G z = ∫ D : ℝ, ∫ v : ℝ, G (v, D) := by
    rw [Measure.volume_eq_prod]; exact integral_prod_symm G hGprod
  have hinner : ∀ D : ℝ, ∫ v : ℝ, G (v, D) = ∫ τ : ℝ, F (D / 2 + τ, τ - D / 2) := by
    intro D
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun v : ℝ => G (v, D)) (D / 2)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [hG, hFs]
    show F (Prod.swap (τ - D / 2, τ - D / 2 + D)) = F (D / 2 + τ, τ - D / 2)
    simp only [Prod.swap_prod_mk]
    rw [show τ - D / 2 + D = D / 2 + τ by ring]
  refine ⟨?_, ?_⟩
  · have := hGprod.integral_prod_right
    exact this.congr (Eventually.of_forall hinner)
  · rw [h1, h2, h3]
    exact integral_congr_ae (Eventually.of_forall hinner)

/-- `g_λ(u) g_λ(v) (|u| + |v|)^k` is integrable on the plane. -/
theorem integrable_heatKernel_prod_pow {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) :
    Integrable (fun p : ℝ × ℝ => heatKernel lam p.1 * heatKernel lam p.2 * (|p.1| + |p.2|) ^ k) := by
  have hg := heatKernel_superExp hlam
  have hmaj : Integrable (fun p : ℝ × ℝ => (k.factorial : ℝ) *
      (heatKernel lam p.1 * Real.exp (1 * |p.1|) * (heatKernel lam p.2 * Real.exp (1 * |p.2|)))) := by
    have := (hg.integrable_mul_exp 1).mul_prod (hg.integrable_mul_exp 1)
    rw [← Measure.volume_eq_prod] at this
    exact this.const_mul _
  refine hmaj.mono' (by
    have := continuous_heatKernel lam
    fun_prop) (Eventually.of_forall fun p => ?_)
  have hp0 : 0 ≤ heatKernel lam p.1 * heatKernel lam p.2 :=
    mul_nonneg (heatKernel_pos _ _).le (heatKernel_pos _ _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 (by positivity))]
  have h := Real.pow_div_factorial_le_exp (|p.1| + |p.2|) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hk] at h
  calc heatKernel lam p.1 * heatKernel lam p.2 * (|p.1| + |p.2|) ^ k
      ≤ heatKernel lam p.1 * heatKernel lam p.2 * (Real.exp (|p.1| + |p.2|) * k.factorial) :=
        mul_le_mul_of_nonneg_left h hp0
    _ = _ := by rw [Real.exp_add]; ring_nf

theorem abs_sub_pow_mul_sq_le (u v : ℝ) (l : ℕ) :
    |(u - v) ^ (2 * l) * (u + v) ^ 2| ≤ (|u| + |v|) ^ (2 * l + 2) := by
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  have h1 : |u - v| ≤ |u| + |v| := abs_sub _ _
  have h2 : |u + v| ≤ |u| + |v| := abs_add_le _ _
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 _) (pow_le_pow_left₀ (abs_nonneg _) h2 _)
    (by positivity) (by positivity)

theorem abs_sub_pow_le (u v : ℝ) (l : ℕ) : |(u - v) ^ (2 * l)| ≤ (|u| + |v|) ^ (2 * l) := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) _

theorem integrable_heatKernel_moment {lam : ℝ} (hlam : 0 ≤ lam) (l : ℕ) :
    Integrable (fun p : ℝ × ℝ => heatKernel lam p.1 * heatKernel lam p.2 * (p.1 - p.2) ^ (2 * l)) ∧
      Integrable (fun p : ℝ × ℝ => heatKernel lam p.1 * heatKernel lam p.2 * (p.1 - p.2) ^ (2 * l) *
        (p.1 + p.2) ^ 2) := by
  have hc := continuous_heatKernel lam
  constructor
  · refine (integrable_heatKernel_prod_pow hlam (2 * l)).mono' (by fun_prop)
      (Eventually.of_forall fun p => ?_)
    have hp0 : 0 ≤ heatKernel lam p.1 * heatKernel lam p.2 :=
      mul_nonneg (heatKernel_pos _ _).le (heatKernel_pos _ _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0]
    exact mul_le_mul_of_nonneg_left (abs_sub_pow_le _ _ _) hp0
  · refine (integrable_heatKernel_prod_pow hlam (2 * l + 2)).mono' (by fun_prop)
      (Eventually.of_forall fun p => ?_)
    have hp0 : 0 ≤ heatKernel lam p.1 * heatKernel lam p.2 :=
      mul_nonneg (heatKernel_pos _ _).le (heatKernel_pos _ _).le
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg hp0]
    exact mul_le_mul_of_nonneg_left (abs_sub_pow_mul_sq_le _ _ _) hp0

theorem fibre_moment_integrand (lam D τ : ℝ) (l : ℕ) :
    heatKernel lam (D / 2 + τ) * heatKernel lam (τ - D / 2) * (D / 2 + τ - (τ - D / 2)) ^ (2 * l) =
      D ^ (2 * l) * (heatKernel lam (D / 2 + τ) * heatKernel lam (D / 2 - τ)) := by
  rw [show τ - D / 2 = -(D / 2 - τ) by ring, heatKernel_neg, show D / 2 + τ - -(D / 2 - τ) = D by ring]
  ring

theorem fibre_moment_integrand_sq (lam D τ : ℝ) (l : ℕ) :
    heatKernel lam (D / 2 + τ) * heatKernel lam (τ - D / 2) * (D / 2 + τ - (τ - D / 2)) ^ (2 * l) *
        (D / 2 + τ + (τ - D / 2)) ^ 2 =
      4 * D ^ (2 * l) * (heatKernel lam (D / 2 + τ) * heatKernel lam (D / 2 - τ) * τ ^ 2) := by
  rw [fibre_moment_integrand, show D / 2 + τ + (τ - D / 2) = 2 * τ by ring]
  ring

/-- A uniform bound for the fibre second moment on bounded centres. -/
theorem heatFibreMoment_le_bound {lam : ℝ} (hlam : 0 ≤ lam) {M : ℝ} (hM : ∀ x, heatKernel lam x ≤ M)
    (c : ℝ) : heatFibreMoment lam c ≤ M * (2 * ∫ x : ℝ, heatKernel lam x * x ^ 2) +
      M * (2 * c ^ 2 * ∫ x : ℝ, heatKernel lam x) := by
  have hg := heatKernel_superExp hlam
  have hM0 : 0 ≤ M := le_trans (heatKernel_pos lam 0).le (hM 0)
  have hI0 : Integrable (fun x : ℝ => heatKernel lam x) :=
    (hg.integrable_mul_exp 0).congr (Eventually.of_forall fun x => by simp)
  have hI2 : Integrable (fun x : ℝ => heatKernel lam x * x ^ 2) := by
    have := integrable_heatKernel_shift_mul_sq hlam 0
    simpa using this
  obtain ⟨-, hF⟩ := integrable_heatKernel_fibre hlam c
  have hS := integrable_heatKernel_shift_mul_sq hlam c
  have h1 : heatFibreMoment lam c ≤ ∫ τ : ℝ, M * (heatKernel lam (c + τ) * τ ^ 2) := by
    unfold heatFibreMoment
    refine integral_mono hF (hS.const_mul M) fun τ => ?_
    have hk : 0 ≤ heatKernel lam (c + τ) * τ ^ 2 := mul_nonneg (heatKernel_pos _ _).le (sq_nonneg _)
    calc heatKernel lam (c + τ) * heatKernel lam (c - τ) * τ ^ 2
        = heatKernel lam (c - τ) * (heatKernel lam (c + τ) * τ ^ 2) := by ring
      _ ≤ M * (heatKernel lam (c + τ) * τ ^ 2) := mul_le_mul_of_nonneg_right (hM _) hk
  have h2 : ∫ τ : ℝ, M * (heatKernel lam (c + τ) * τ ^ 2) =
      ∫ x : ℝ, M * (heatKernel lam x * (x - c) ^ 2) := by
    have := integral_add_left_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => M * (heatKernel lam x * (x - c) ^ 2)) c
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    rw [show c + τ - c = τ by ring]
  have hIc : Integrable (fun x : ℝ => M * (heatKernel lam x * (x - c) ^ 2)) := by
    have := (integrable_heatKernel_shift_mul_sq hlam c).comp_sub_right c
    refine (this.const_mul M).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [show c + (x - c) = x by ring]
  have h3 : ∫ x : ℝ, M * (heatKernel lam x * (x - c) ^ 2) ≤
      M * (2 * ∫ x : ℝ, heatKernel lam x * x ^ 2) + M * (2 * c ^ 2 * ∫ x : ℝ, heatKernel lam x) := by
    calc ∫ x : ℝ, M * (heatKernel lam x * (x - c) ^ 2)
        ≤ ∫ x : ℝ, (M * 2 * (heatKernel lam x * x ^ 2) + M * 2 * c ^ 2 * heatKernel lam x) := by
          refine integral_mono hIc ((hI2.const_mul _).add (hI0.const_mul _)) fun x => ?_
          have hx := heatKernel_pos lam x
          have : (x - c) ^ 2 ≤ 2 * x ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (x + c)]
          nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM0 hx.le)]
      _ = _ := by
          rw [integral_add (hI2.const_mul _) (hI0.const_mul _), integral_const_mul,
            integral_const_mul]
          ring
  linarith

/-! ## Concentration of the moment measures -/

/-- **Concentration on the antidiagonal.**  For every `ε > 0` and all large `l`,
`∫∫ g_λ(u) g_λ(v) (u − v)^{2l} (u + v)² ≤ ε ∫∫ g_λ(u) g_λ(v) (u − v)^{2l}`. -/
theorem exists_heatKernel_moment_concentration {lam : ℝ} (hlam : 0 ≤ lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ l₁ : ℕ, ∀ l, l₁ ≤ l →
      ∫ p : ℝ × ℝ, heatKernel lam p.1 * heatKernel lam p.2 * (p.1 - p.2) ^ (2 * l) *
          (p.1 + p.2) ^ 2 ≤
        ε * ∫ p : ℝ × ℝ, heatKernel lam p.1 * heatKernel lam p.2 * (p.1 - p.2) ^ (2 * l) := by
  have hg := heatKernel_superExp hlam
  obtain ⟨M, hM, hbound⟩ := hg.exists_bound
  obtain ⟨c₁, hc₁x, hfib⟩ := exists_fibreMoment_le hlam (ε := ε / 8) (by positivity)
  have hx₀ : 0 ≤ Real.log 3 / 2 := by positivity
  have hc₁0 : 1 ≤ c₁ := by linarith
  set D₁ : ℝ := 2 * c₁ with hD₁
  have hD₁0 : 0 < D₁ := by positivity
  set m₀ : ℝ := ∫ x : ℝ, heatKernel lam x with hm₀
  set m₂ : ℝ := ∫ x : ℝ, heatKernel lam x * x ^ 2 with hm₂
  have hm₀0 : 0 ≤ m₀ := integral_nonneg fun x => (heatKernel_pos _ _).le
  have hm₂0 : 0 ≤ m₂ := integral_nonneg fun x => mul_nonneg (heatKernel_pos _ _).le (sq_nonneg _)
  set B₁ : ℝ := M * (2 * m₂) + M * (2 * c₁ ^ 2 * m₀) with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  -- the mass on `[D₁ + 1, D₁ + 2]`
  set c₂ : ℝ := c₁ + 1 with hc₂
  set L₂ : ℝ := riemannKernelReal (Real.log 3 / 2) *
    Real.exp (-(π * (Real.exp (2 * c₂) - 3)) - 4 * π * (c₂ - Real.log 3 / 2)) with hL₂
  have hL₂0 : 0 < L₂ := mul_pos (riemannKernelReal_pos _) (Real.exp_pos _)
  set m₁ : ℝ := 2 * Real.exp (-c₂) * Real.exp (-(16 * π + 18)) * L₂ ^ 2 with hm₁
  have hm₁0 : 0 < m₁ := by positivity
  have hmass_low : ∀ D ∈ Set.Icc (D₁ + 1) (D₁ + 2), m₁ ≤ heatFibreMass lam (D / 2) := by
    intro D hD
    have hc : Real.log 3 / 2 + 1 ≤ D / 2 := by rw [hD₁] at hD; linarith [hD.1]
    have hc' : D / 2 ≤ c₂ := by rw [hD₁] at hD; rw [hc₂]; linarith [hD.2]
    have h := heatFibreMass_ge hlam hc
    have hb := heatKernel_ge_base hlam (by linarith : Real.log 3 / 2 ≤ D / 2)
    have hbase : L₂ ≤ riemannKernelReal (Real.log 3 / 2) *
        Real.exp (-(π * (Real.exp (2 * (D / 2)) - 3)) - 4 * π * (D / 2 - Real.log 3 / 2)) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (riemannKernelReal_pos _).le
      have : Real.exp (2 * (D / 2)) ≤ Real.exp (2 * c₂) := Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.pi_pos]
    have hgL : L₂ ≤ heatKernel lam (D / 2) := hbase.trans hb
    have hsq : L₂ ^ 2 ≤ heatKernel lam (D / 2) ^ 2 := pow_le_pow_left₀ hL₂0.le hgL 2
    have he : Real.exp (-c₂) ≤ Real.exp (-(D / 2)) := Real.exp_le_exp.mpr (by linarith)
    calc m₁ = 2 * Real.exp (-c₂) * Real.exp (-(16 * π + 18)) * L₂ ^ 2 := rfl
      _ ≤ 2 * Real.exp (-(D / 2)) * Real.exp (-(16 * π + 18)) * heatKernel lam (D / 2) ^ 2 := by
          gcongr
      _ ≤ _ := h
  -- the decay of `(D₁/(D₁+1))^{2l}`
  set q : ℝ := D₁ / (D₁ + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  set η : ℝ := ε * m₁ / (16 * D₁ * (B₁ + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hη0 hq1
  refine ⟨n₀, fun l hl => ?_⟩
  obtain ⟨hI1, hI2⟩ := integrable_heatKernel_moment hlam l
  obtain ⟨hD1, e1⟩ := integral_eq_integral_fibre hI1
  obtain ⟨hD2, e2⟩ := integral_eq_integral_fibre hI2
  have hf1 : (fun D : ℝ => ∫ τ : ℝ, heatKernel lam (D / 2 + τ) * heatKernel lam (τ - D / 2) *
      (D / 2 + τ - (τ - D / 2)) ^ (2 * l)) = fun D => D ^ (2 * l) * heatFibreMass lam (D / 2) := by
    funext D
    simp_rw [fibre_moment_integrand]
    rw [integral_const_mul]; rfl
  have hf2 : (fun D : ℝ => ∫ τ : ℝ, heatKernel lam (D / 2 + τ) * heatKernel lam (τ - D / 2) *
      (D / 2 + τ - (τ - D / 2)) ^ (2 * l) * (D / 2 + τ + (τ - D / 2)) ^ 2) =
      fun D => 4 * D ^ (2 * l) * heatFibreMoment lam (D / 2) := by
    funext D
    simp_rw [fibre_moment_integrand_sq]
    rw [integral_const_mul]; rfl
  simp only at e1 e2 hD1 hD2
  rw [hf1] at e1 hD1
  rw [hf2] at e2 hD2
  rw [e1, e2]
  -- pointwise domination
  set K : ℝ := 4 * D₁ ^ (2 * l) * B₁ with hK
  have hpt : ∀ D : ℝ, 4 * D ^ (2 * l) * heatFibreMoment lam (D / 2) ≤
      ε / 2 * (D ^ (2 * l) * heatFibreMass lam (D / 2)) +
        (Set.Icc (-D₁) D₁).indicator (fun _ => K) D := by
    intro D
    have hpow : 0 ≤ D ^ (2 * l) := by rw [pow_mul]; positivity
    have hmom0 : 0 ≤ heatFibreMoment lam (D / 2) :=
      integral_nonneg fun τ => mul_nonneg (mul_pos (heatKernel_pos _ _) (heatKernel_pos _ _)).le
        (sq_nonneg _)
    have hmass0 := heatFibreMass_nonneg lam (D / 2)
    by_cases hD : D ∈ Set.Icc (-D₁) D₁
    · rw [Set.indicator_of_mem hD]
      have habs : |D| ≤ D₁ := abs_le.mpr ⟨hD.1, hD.2⟩
      have hDp : D ^ (2 * l) ≤ D₁ ^ (2 * l) := by
        rw [← (even_two_mul l).pow_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) habs _
      have hc2 : (D / 2) ^ 2 ≤ c₁ ^ 2 := by
        rw [← sq_abs]; refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        rw [abs_div, abs_two]; rw [hD₁] at habs; linarith
      have hmB : heatFibreMoment lam (D / 2) ≤ B₁ := by
        have := heatFibreMoment_le_bound hlam hbound (D / 2)
        rw [hB₁]
        have : M * (2 * (D / 2) ^ 2 * m₀) ≤ M * (2 * c₁ ^ 2 * m₀) := by gcongr
        linarith
      have : 4 * D ^ (2 * l) * heatFibreMoment lam (D / 2) ≤ 4 * D₁ ^ (2 * l) * B₁ := by gcongr
      have : 0 ≤ ε / 2 * (D ^ (2 * l) * heatFibreMass lam (D / 2)) := by positivity
      linarith
    · rw [Set.indicator_of_notMem hD, add_zero]
      have habs : D₁ ≤ |D| := by
        by_contra h; push Not at h
        exact hD ⟨by linarith [neg_abs_le D], by linarith [le_abs_self D]⟩
      have hc : c₁ ≤ |D / 2| := by rw [abs_div, abs_two]; rw [hD₁] at habs; linarith
      have hmom : heatFibreMoment lam (D / 2) ≤ ε / 8 * heatFibreMass lam (D / 2) := by
        rcases le_total 0 (D / 2) with h | h
        · rw [abs_of_nonneg h] at hc; exact hfib _ hc
        · rw [abs_of_nonpos h] at hc
          have := hfib _ hc
          rwa [heatFibreMoment_neg, heatFibreMass_neg] at this
      calc 4 * D ^ (2 * l) * heatFibreMoment lam (D / 2)
          ≤ 4 * D ^ (2 * l) * (ε / 8 * heatFibreMass lam (D / 2)) := by gcongr
        _ = ε / 2 * (D ^ (2 * l) * heatFibreMass lam (D / 2)) := by ring
  have hIndI : Integrable (fun D : ℝ => (Set.Icc (-D₁) D₁).indicator (fun _ => K) D) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hnum : ∫ D : ℝ, 4 * D ^ (2 * l) * heatFibreMoment lam (D / 2) ≤
      ε / 2 * (∫ D : ℝ, D ^ (2 * l) * heatFibreMass lam (D / 2)) + 2 * D₁ * K := by
    calc ∫ D : ℝ, 4 * D ^ (2 * l) * heatFibreMoment lam (D / 2)
        ≤ ∫ D : ℝ, (ε / 2 * (D ^ (2 * l) * heatFibreMass lam (D / 2)) +
            (Set.Icc (-D₁) D₁).indicator (fun _ => K) D) :=
          integral_mono hD2 ((hD1.const_mul _).add hIndI) hpt
      _ = _ := by
          rw [integral_add (hD1.const_mul _) hIndI, integral_const_mul,
            integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
            smul_eq_mul]
          ring
  have hden : (D₁ + 1) ^ (2 * l) * m₁ ≤ ∫ D : ℝ, D ^ (2 * l) * heatFibreMass lam (D / 2) := by
    have hlow : ∀ D ∈ Set.Icc (D₁ + 1) (D₁ + 2), (D₁ + 1) ^ (2 * l) * m₁ ≤
        D ^ (2 * l) * heatFibreMass lam (D / 2) := by
      intro D hD
      have hD0 : 0 ≤ D₁ + 1 := by positivity
      exact mul_le_mul (pow_le_pow_left₀ hD0 hD.1 _) (hmass_low D hD) hm₁0.le
        (pow_nonneg (by linarith [hD.1]) _)
    have hset := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hlow hD1.integrableOn
    rw [Real.volume_real_Icc_of_le (by linarith), smul_eq_mul,
      show D₁ + 2 - (D₁ + 1) = 1 by ring, one_mul] at hset
    refine hset.trans (setIntegral_le_integral hD1 (Eventually.of_forall fun D => ?_))
    have := heatFibreMass_nonneg lam (D / 2)
    have : 0 ≤ D ^ (2 * l) := by rw [pow_mul]; positivity
    positivity
  -- the bounded part is small
  have hqn : q ^ (2 * l) ≤ q ^ n₀ := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have hDpow : D₁ ^ (2 * l) = q ^ (2 * l) * (D₁ + 1) ^ (2 * l) := by
    rw [hq, div_pow]; field_simp
  have hsmall : 2 * D₁ * K ≤ ε / 2 * ((D₁ + 1) ^ (2 * l) * m₁) := by
    rw [hK, hDpow]
    have hP : 0 ≤ (D₁ + 1) ^ (2 * l) := by positivity
    have h1 : q ^ (2 * l) ≤ η := le_trans hqn hn₀.le
    have h2 : 2 * D₁ * (4 * (η * (D₁ + 1) ^ (2 * l)) * B₁) ≤ ε / 2 * ((D₁ + 1) ^ (2 * l) * m₁) := by
      rw [hη]
      have hB : B₁ ≤ B₁ + 1 := by linarith
      have e : 2 * D₁ * (4 * (ε * m₁ / (16 * D₁ * (B₁ + 1)) * (D₁ + 1) ^ (2 * l)) * B₁) =
          ε / 2 * ((D₁ + 1) ^ (2 * l) * m₁) * (B₁ / (B₁ + 1)) := by
        field_simp; ring
      rw [e]
      have h3 : B₁ / (B₁ + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have h4 : 0 ≤ ε / 2 * ((D₁ + 1) ^ (2 * l) * m₁) := by positivity
      exact mul_le_of_le_one_right h4 h3
    calc 2 * D₁ * (4 * (q ^ (2 * l) * (D₁ + 1) ^ (2 * l)) * B₁)
        ≤ 2 * D₁ * (4 * (η * (D₁ + 1) ^ (2 * l)) * B₁) := by gcongr
      _ ≤ _ := h2
  have h5 := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ ε / 2)
  linarith

end

end RHTower.DeBruijn
