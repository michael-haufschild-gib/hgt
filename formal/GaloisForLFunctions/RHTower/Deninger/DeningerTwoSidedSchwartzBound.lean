import GaloisForLFunctions.RHTower.Deninger.DeningerTwoSidedWeight
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerSeminorm

/-!
# The weighted Schwartz seminorms are bounded by the Meyer seminorms

Every Schwartz seminorm of `w_K h` is dominated by the Meyer seminorms of `h` at exponent `K+1`:
the Leibniz expansion moves the weight onto constants, the two exponentials combine into
`2e^{K|x|}`, and the polynomial factor is absorbed by `|x|^a \le a!\,e^{|x|}`.

* `deningerTwoSidedWeighted_pointwise` : the pointwise Leibniz estimate.
* `deningerTwoSidedWeighted_schwartzSeminorm_bound` : **the seminorm bound.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The two-sided weighted function, as a plain function. -/
theorem deningerTwoSidedMul_eq_add (K : ℝ) (h : DeningerExpSchwartz) :
    (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = (fun t => deningerExpWeightC K t * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t)
        + (fun t => deningerExpWeightC (-K) t * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) := by
  funext t
  rw [deningerTwoSidedMul_apply]
  show _ = deningerExpWeightC K t * _ + deningerExpWeightC (-K) t * _
  rw [deningerExpWeightC, deningerExpWeightC]
  push_cast
  rw [show (-(K : ℂ)) * (t : ℂ) = -((K : ℂ) * (t : ℂ)) from by ring]
  ring

/-- **The pointwise Leibniz estimate for the two-sided weight.** -/
theorem deningerTwoSidedWeighted_pointwise {K : ℝ} (hK : 0 ≤ K) (b : ℕ)
    (h : DeningerExpSchwartz) (x : ℝ) :
    ‖iteratedFDeriv ℝ b (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * K ^ j
          * (2 * Real.exp (K * |x|))
          * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) ((((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) :=
    ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)
  have hsplit : iteratedFDeriv ℝ b
      (((deningerTwoSidedMul K h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
      = iteratedFDeriv ℝ b
          (fun t => deningerExpWeightC K t * (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t) x
        + iteratedFDeriv ℝ b
          (fun t => deningerExpWeightC (-K) t
            * (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t) x := by
    rw [deningerTwoSidedMul_eq_add]
    exact iteratedFDeriv_add_apply
      (((deningerExpWeightC_contDiff K).mul hsm).of_le (by exact_mod_cast le_top)).contDiffAt
      (((deningerExpWeightC_contDiff (-K)).mul hsm).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hpos := deningerWeighted_iteratedFDeriv_bound hsm K b x
  have hneg := deningerWeighted_iteratedFDeriv_bound hsm (-K) b x
  refine le_trans (add_le_add hpos hneg) ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ :=
    norm_nonneg _
  have habs : |(-K)| = K := by rw [abs_neg, abs_of_nonneg hK]
  have habs' : |K| = K := abs_of_nonneg hK
  have hw : Real.exp (K * x) + Real.exp (-(K * x)) ≤ 2 * Real.exp (K * |x|) :=
    deningerTwoSidedWeight_le K x hK
  have hexpand : (b.choose j : ℝ) * (|K| ^ j * Real.exp (K * x))
        * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      + (b.choose j : ℝ) * (|(-K)| ^ j * Real.exp (-K * x))
        * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      = (b.choose j : ℝ) * K ^ j
        * (Real.exp (K * x) + Real.exp (-(K * x)))
        * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ := by
    rw [habs, habs', show -K * x = -(K * x) from by ring]
    ring
  rw [hexpand]
  refine mul_le_mul_of_nonneg_right ?_ hnn
  refine mul_le_mul_of_nonneg_left hw ?_
  positivity

/-- **Every Schwartz seminorm of the weighted function is bounded by Meyer seminorms.** -/
theorem deningerTwoSidedWeighted_schwartzSeminorm_bound (K : ℕ) (a b : ℕ)
    (h : DeningerExpSchwartz) :
    SchwartzMap.seminorm ℂ a b
        ((deningerTwoSidedMul (K : ℝ) h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
      ≤ (2 * (Nat.factorial a : ℝ) * ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * (K : ℝ) ^ j)
        * ∑ i ∈ Finset.range (b + 1), deningerMeyerSeminormFun ((K : ℝ) + 1) i h := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  refine SchwartzMap.seminorm_le_bound ℂ a b _
    (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => deningerMeyerSeminormFun_nonneg _ i h)) fun x => ?_
  have hpt := deningerTwoSidedWeighted_pointwise hK b h x
  have hpow := deningerPow_le_factorial_mul_exp a x
  have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ b
      (((deningerTwoSidedMul (K : ℝ) h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ :=
    norm_nonneg _
  refine le_trans (mul_le_mul hpow hpt hnn (by positivity)) ?_
  set S : ℝ := ∑ i ∈ Finset.range (b + 1), deningerMeyerSeminormFun ((K : ℝ) + 1) i h with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ => deningerMeyerSeminormFun_nonneg _ i h
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (b + 1),
      (Nat.factorial a : ℝ) * Real.exp |x| * ((b.choose j : ℝ) * (K : ℝ) ^ j
          * (2 * Real.exp ((K : ℝ) * |x|))
          * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖)
        ≤ 2 * (Nat.factorial a : ℝ) * ((b.choose j : ℝ) * (K : ℝ) ^ j) * S := by
    intro j hj
    have hmey : Real.exp (((K : ℝ) + 1) * |x|)
        * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
        ≤ deningerMeyerSeminormFun ((K : ℝ) + 1) (b - j) h := by
      have hw := deningerMeyerWeight_le ((K : ℝ) + 1) (b - j) h x
      rwa [deningerMeyerWeight] at hw
    have hsum : deningerMeyerSeminormFun ((K : ℝ) + 1) (b - j) h ≤ S :=
      Finset.single_le_sum (f := fun i => deningerMeyerSeminormFun ((K : ℝ) + 1) i h)
        (fun i _ => deningerMeyerSeminormFun_nonneg _ i h)
        (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.sub_le _ _)))
    have hexp : (Nat.factorial a : ℝ) * Real.exp |x| * ((b.choose j : ℝ) * (K : ℝ) ^ j
          * (2 * Real.exp ((K : ℝ) * |x|))
          * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖)
        = 2 * (Nat.factorial a : ℝ) * ((b.choose j : ℝ) * (K : ℝ) ^ j)
          * (Real.exp (((K : ℝ) + 1) * |x|)
            * ‖iteratedFDeriv ℝ (b - j) (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖) := by
      rw [show ((K : ℝ) + 1) * |x| = (K : ℝ) * |x| + |x| from by ring, Real.exp_add]
      ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_left (le_trans hmey hsum) (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.mul_sum]

end

end RHTower
