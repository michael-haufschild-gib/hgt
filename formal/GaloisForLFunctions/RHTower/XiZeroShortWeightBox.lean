import GaloisForLFunctions.RHTower.XiZeroFoldedHeightCount
import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound

/-!
# The zero weight over one height box

For zeros with `T ≤ |γ| ≤ 2T` the weight `x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|))` is at most
`c · min(1, x^{2u}/T²) · x^{β-1}`.  Feeding the folded layer cake with a density bound
`#{β ≥ σ, T ≤ γ ≤ 2T} ≤ D (1 + log T)^B T^{A(1-σ)}` and a zero-free width `β ≤ 1 - w` inside the box
gives the box bound

`Σ_{ρ ∈ box} weight ≤ 4 M c D x^{1/(2M)} (1 + log T)^B x^{-(1-uA) w} g(x, T)`,

with `g(x, T) = 1` for `T ≤ x^u` and `g(x, T) = (x^u/T)^{2-A/2}` beyond.  The key exponent inequality
is `min(1, x^{2u}/T²) x^{-s} T^{As} ≤ x^{-(1-uA)s} g(x, T)` for `0 ≤ s ≤ 1/2`: below `x^u` it is
monotonicity in `T`, above `x^u` its logarithmic defect is `A(log T - u log x)(1/2 - s) ≥ 0`.
-/

namespace RHTower

noncomputable section

open Complex Finset

/-- The height factor: `1` up to `x^u`, then `(x^u/T)^{c₁}`. -/
def shortWeightHeightFactor (x u c₁ T : ℝ) : ℝ := if T ≤ x ^ u then 1 else (x ^ u / T) ^ c₁

theorem shortWeightHeightFactor_nonneg {x : ℝ} (hx : 0 ≤ x) (u c₁ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ shortWeightHeightFactor x u c₁ T := by
  rw [shortWeightHeightFactor]
  split_ifs
  · exact zero_le_one
  · exact Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg hx _) hT) _

theorem shortWeightHeightFactor_le_one {x : ℝ} (hx : 0 ≤ x) (u : ℝ) {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    {T : ℝ} :
    shortWeightHeightFactor x u c₁ T ≤ 1 := by
  rw [shortWeightHeightFactor]
  split_ifs with h
  · exact le_rfl
  · push Not at h
    have hT : 0 < T := lt_of_le_of_lt (Real.rpow_nonneg hx _) h
    exact Real.rpow_le_one (div_nonneg (Real.rpow_nonneg hx _) hT.le)
      ((div_le_one hT).mpr h.le) hc₁

/-- **The exponent inequality.** -/
theorem min_mul_rpow_le_heightFactor {x T u A s : ℝ} (hx : 1 ≤ x) (hT : 0 < T) (_hu : 0 ≤ u)
    (hA : 0 ≤ A) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    min 1 (x ^ (2 * u) / T ^ 2) * (x ^ (-s) * T ^ (A * s))
      ≤ x ^ (-((1 - u * A) * s)) * shortWeightHeightFactor x u (2 - A / 2) T := by
  have hx0 : 0 < x := by linarith
  have hxs : 0 ≤ x ^ (-s) * T ^ (A * s) := by positivity
  rw [shortWeightHeightFactor]
  split_ifs with hTx
  · -- below `x^u`
    rw [mul_one]
    refine le_trans (mul_le_of_le_one_left hxs (min_le_left _ _)) ?_
    have h1 : T ^ (A * s) ≤ (x ^ u) ^ (A * s) :=
      Real.rpow_le_rpow hT.le hTx (by positivity)
    rw [← Real.rpow_mul hx0.le] at h1
    calc x ^ (-s) * T ^ (A * s) ≤ x ^ (-s) * x ^ (u * (A * s)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0.le _)
      _ = x ^ (-((1 - u * A) * s)) := by
          rw [← Real.rpow_add hx0]
          congr 1
          ring
  · -- above `x^u`
    push Not at hTx
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hxs) ?_
    set ℓ := Real.log x with hℓ
    set τ := Real.log T with hτ
    have hτℓ : u * ℓ < τ := by
      have := Real.log_lt_log (Real.rpow_pos_of_pos hx0 u) hTx
      rwa [Real.log_rpow hx0] at this
    have hq : 0 < x ^ u / T := div_pos (Real.rpow_pos_of_pos hx0 u) hT
    have hlogq : Real.log (x ^ u / T) = u * ℓ - τ := by
      rw [Real.log_div (Real.rpow_pos_of_pos hx0 u).ne' hT.ne', Real.log_rpow hx0]
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hT,
      Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hq, hlogq, ← hℓ, ← hτ,
      show T ^ 2 = Real.exp (2 * τ) by
        rw [hτ, show 2 * Real.log T = Real.log T + Real.log T by ring, Real.exp_add,
          Real.exp_log hT]
        ring,
      div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp]
    have hkey : 0 ≤ A * (τ - u * ℓ) * (1 / 2 - s) :=
      mul_nonneg (mul_nonneg hA (by linarith)) (by linarith)
    nlinarith

theorem min_one_mul_le {c z : ℝ} (hc : 1 ≤ c) : min 1 (c * z) ≤ c * min 1 z := by
  rcases le_total z 1 with h | h
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left h, mul_one]
    exact le_trans (min_le_left _ _) hc

/-- The weight of a zero above height `T` is at most `c · min(1, x^{2u}/T²) · x^{β-1}`. -/
theorem zeroShortWeight_le_of_height {x : ℝ} (hx : 0 ≤ x) {c Y T : ℝ} (hc : 1 ≤ c) (hY : 0 ≤ Y)
    (hT : 0 < T) (q : XiZeroCopy) (hq : T ≤ |(q.1 : ℂ).im|) :
    zeroShortWeight x (c * Y) (q.1 : ℂ)
      ≤ c * min 1 (Y / T ^ 2) * x ^ ((q.1 : ℂ).re - 1) := by
  rw [zeroShortWeight]
  have hN : T ^ 2 ≤ ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ := by
    have h1 : |(q.1 : ℂ).im| ≤ ‖(q.1 : ℂ)‖ := Complex.abs_im_le_norm _
    have h2 : |(q.1 : ℂ).im| ≤ ‖1 - (q.1 : ℂ)‖ := by
      have := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
      rwa [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
    nlinarith
  have hxp : 0 ≤ x ^ ((q.1 : ℂ).re - 1) := Real.rpow_nonneg hx _
  have hmin : min 1 (c * Y / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) ≤ c * min 1 (Y / T ^ 2) := by
    refine le_trans (min_le_min_left _ ?_) (min_one_mul_le hc)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hY (by positivity) hN)
      (by linarith)
  rw [mul_comm (x ^ _)]
  exact mul_le_mul_of_nonneg_right hmin hxp

/-- **The box bound.** -/
theorem sum_zeroShortWeight_box_le {x u A c D w T : ℝ} {B M : ℕ} (hx : 1 ≤ x) (hu : 0 ≤ u)
    (hA : 0 ≤ A) (hδ : 0 ≤ 1 - u * A) (hc : 1 ≤ c) (hD : 0 ≤ D) (hw : 0 ≤ w) (hT : 1 ≤ T)
    (hM : 0 < M)
    (hdens : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ)))
    (hfree : ∀ σ : ℝ, (zeroHeightBox σ T).Nonempty → σ ≤ 1 - w)
    (G : Finset XiZeroCopy) (hG : ∀ q ∈ G, T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) :
    ∑ q ∈ G, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)
      ≤ 4 * M * c * D * x ^ (1 / (2 * (M : ℝ))) * (1 + Real.log T) ^ B
          * x ^ (-((1 - u * A) * w)) * shortWeightHeightFactor x u (2 - A / 2) T := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogT : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  set m₀ := min 1 (x ^ (2 * u) / T ^ 2) with hm₀
  have hm₀0 : 0 ≤ m₀ := le_min zero_le_one (by positivity)
  set g := shortWeightHeightFactor x u (2 - A / 2) T with hg
  have hg0 : 0 ≤ g := shortWeightHeightFactor_nonneg hx0.le u _ hT0.le
  set R := D * x ^ (1 / (2 * (M : ℝ))) * (1 + Real.log T) ^ B * x ^ (-((1 - u * A) * w)) * g
    with hR
  have hR0 : 0 ≤ R := by positivity
  have hstep1 : ∑ q ∈ G, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)
      ≤ c * m₀ * ∑ q ∈ G, x ^ ((q.1 : ℂ).re - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq =>
      zeroShortWeight_le_of_height hx0.le hc (by positivity) hT0 q (hG q hq).1
  have hstep2 := sum_rpow_re_le_zeroHeightBox hx hM G hG
  have hslab : ∀ m ∈ Finset.range M,
      m₀ * (x ^ (slabAbscissa M (m + 1) - 1) * ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ))
        ≤ R := by
    intro m hm
    have hmM : m < M := Finset.mem_range.mp hm
    set σ := slabAbscissa M m with hσ
    have hmR : (m : ℝ) < M := by exact_mod_cast hmM
    have hσ1 : 1 / 2 ≤ σ := by
      rw [hσ, slabAbscissa]
      have : 0 ≤ (m : ℝ) / (2 * M) := by positivity
      linarith
    have hσ2 : σ ≤ 1 := by
      rw [hσ, slabAbscissa]
      have : (m : ℝ) / (2 * M) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith
    have hexp : slabAbscissa M (m + 1) - 1 = 1 / (2 * (M : ℝ)) + -(1 - σ) := by
      rw [hσ, slabAbscissa, slabAbscissa]
      push_cast
      field_simp
      ring
    rw [hexp, Real.rpow_add hx0]
    rcases (zeroHeightBox σ T).eq_empty_or_nonempty with hE | hN
    · rw [hE, Set.ncard_empty, Nat.cast_zero, mul_zero, mul_zero]
      exact hR0
    · have hsw : w ≤ 1 - σ := by linarith [hfree σ hN]
      have hs0 : 0 ≤ 1 - σ := le_trans hw hsw
      have hs12 : 1 - σ ≤ 1 / 2 := by linarith
      have hd := hdens σ hσ1 hσ2
      have hE := min_mul_rpow_le_heightFactor hx hT0 hu hA hs0 hs12
      rw [← hm₀, ← hg] at hE
      have hmono : x ^ (-((1 - u * A) * (1 - σ))) ≤ x ^ (-((1 - u * A) * w)) :=
        Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg (mul_le_mul_of_nonneg_left hsw hδ))
      have hxM : 0 ≤ x ^ (1 / (2 * (M : ℝ))) := Real.rpow_nonneg hx0.le _
      have hxs : 0 ≤ x ^ (-(1 - σ)) := Real.rpow_nonneg hx0.le _
      calc m₀ * (x ^ (1 / (2 * (M : ℝ))) * x ^ (-(1 - σ))
            * ((zeroHeightBox σ T).ncard : ℝ))
          ≤ m₀ * (x ^ (1 / (2 * (M : ℝ))) * x ^ (-(1 - σ))
              * (D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ)))) := by gcongr
        _ = D * x ^ (1 / (2 * (M : ℝ))) * (1 + Real.log T) ^ B
              * (m₀ * (x ^ (-(1 - σ)) * T ^ (A * (1 - σ)))) := by ring
        _ ≤ D * x ^ (1 / (2 * (M : ℝ))) * (1 + Real.log T) ^ B
              * (x ^ (-((1 - u * A) * (1 - σ))) * g) := by gcongr
        _ ≤ D * x ^ (1 / (2 * (M : ℝ))) * (1 + Real.log T) ^ B
              * (x ^ (-((1 - u * A) * w)) * g) := by gcongr
        _ = R := by rw [hR]; ring
  have hc0 : 0 ≤ c * m₀ := mul_nonneg (by linarith) hm₀0
  calc ∑ q ∈ G, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)
      ≤ c * m₀ * ∑ q ∈ G, x ^ ((q.1 : ℂ).re - 1) := hstep1
    _ ≤ c * m₀ * (4 * ∑ m ∈ Finset.range M,
          x ^ (slabAbscissa M (m + 1) - 1) * ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 hc0
    _ = 4 * c * ∑ m ∈ Finset.range M, m₀ *
          (x ^ (slabAbscissa M (m + 1) - 1) * ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ)) := by
        rw [← Finset.mul_sum]
        ring
    _ ≤ 4 * c * ∑ m ∈ Finset.range M, R :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hslab) (by linarith)
    _ = 4 * M * c * D * x ^ (1 / (2 * (M : ℝ))) * (1 + Real.log T) ^ B
          * x ^ (-((1 - u * A) * w)) * g := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hR]
        ring

end

end RHTower
