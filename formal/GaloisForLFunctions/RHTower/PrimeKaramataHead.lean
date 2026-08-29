import GaloisForLFunctions.RHTower.PrimePowerSumBound
import GaloisForLFunctions.HTGeometry.SlowlyVarying

/-!
# The head of the prime Karamata sum

The weight `F(t) = t^{−α}L(t)` of the regular-variation Steinhaus model has a singular endpoint at
`t = 0`.  Potter's bound turns the head `∑_{p ≤ v₀X}(log p)F(p)` into the sub-critical prime power
sum at exponent `β = (1+α)/2`, which is `≪ (v₀X)^{1−β}`; the exponents combine to
`X^{1−α}L(X)·v₀^{1−β}`, so the head is uniformly negligible as `v₀ → 0`.
-/

open Filter Topology HTGeometry

namespace RHTower

noncomputable section

/-- The regular-variation weight. -/
def rvPrimeWeight (α : ℝ) (L : ℝ → ℝ) (t : ℝ) : ℝ := t ^ (-α) * L t

/-- The card's `W_X`. -/
def rvWeightSum (α : ℝ) (L : ℝ → ℝ) (X : ℝ) : ℝ := primeLogSum (rvPrimeWeight α L) 0 X

theorem rvPrimeWeight_nonneg {α : ℝ} {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {t : ℝ} (ht : 0 < t) :
    0 ≤ rvPrimeWeight α L t := by
  have h1 : (0 : ℝ) ≤ t ^ (-α) := Real.rpow_nonneg ht.le _
  have h2 : 0 < L t := hL.pos t ht
  exact mul_nonneg h1 h2.le

/-- **The head estimate.**  For every `ε > 0` there is a threshold `v₀` below which the head of
the prime Karamata sum is at most `ε X^{1−α}L(X)`, eventually in `X`. -/
theorem exists_karamata_head_bound {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {ε : ℝ} (hε : 0 < ε) :
    ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ < 1 ∧ ∀ᶠ X in atTop,
      primeLogSum (rvPrimeWeight α L) 0 (v₀ * X) ≤ ε * (X ^ (1 - α) * L X) := by
  set δ : ℝ := (1 - α) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set β : ℝ := α + δ with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef, hδdef]; linarith
  obtain ⟨K, hK0, hK⟩ := exists_primeLogSum_rpow_le hβ0 hβ1
  obtain ⟨X₀, hX₀1, hpotter⟩ := isSlowlyVarying_potter hL hδ
  have hX₀0 : (0 : ℝ) < X₀ := lt_of_lt_of_le one_pos hX₀1
  have he2 : (0 : ℝ) < Real.exp (2 * δ) := Real.exp_pos _
  -- the threshold
  have hexp : (0 : ℝ) < 1 - β := by linarith
  obtain ⟨v₀, hv₀0, hv₀1, hv₀⟩ : ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ < 1 ∧
      K * Real.exp (2 * δ) * v₀ ^ (1 - β) ≤ ε / 2 := by
    have hlim : Tendsto (fun v : ℝ => K * Real.exp (2 * δ) * v ^ (1 - β)) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
      have hc : ContinuousAt (fun v : ℝ => v ^ (1 - β)) 0 :=
        Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)
      have h0 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      rw [Real.zero_rpow hexp.ne'] at h0
      have := h0.const_mul (K * Real.exp (2 * δ))
      rwa [mul_zero] at this
    have hev := hlim.eventually_le_const (by linarith : (0 : ℝ) < ε / 2)
    obtain ⟨v, ⟨hv1, hv2⟩⟩ := ((hev.and self_mem_nhdsWithin).and
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)).exists
    exact ⟨v, hv1.2, hv2, hv1.1⟩
  refine ⟨v₀, hv₀0, hv₀1, ?_⟩
  -- the fixed initial segment
  set H₀ : ℝ := primeLogSum (rvPrimeWeight α L) 0 X₀ with hH₀
  have hlowL : ∀ X : ℝ, X₀ ≤ X → L X₀ * Real.exp (-(2 * δ)) * (X₀ / X) ^ δ ≤ L X := by
    intro X hX
    have h := (hpotter X₀ X le_rfl hX).2
    have hLX₀ : 0 < L X₀ := hL.pos _ hX₀0
    rw [le_div_iff₀ hLX₀] at h
    linarith [h]
  have hdiv : Tendsto (fun X : ℝ => H₀ / (X ^ (1 - α) * L X)) atTop (𝓝 0) := by
    have hgrow : Tendsto (fun X : ℝ => X ^ (1 - α) * L X) atTop atTop := by
      have hc : (0 : ℝ) < L X₀ * Real.exp (-(2 * δ)) * X₀ ^ δ := by
        have := hL.pos _ hX₀0
        have h2 : (0 : ℝ) < X₀ ^ δ := Real.rpow_pos_of_pos hX₀0 _
        positivity
      have hpow : Tendsto (fun X : ℝ => (L X₀ * Real.exp (-(2 * δ)) * X₀ ^ δ) * X ^ (1 - α - δ))
          atTop atTop := by
        have := (tendsto_rpow_atTop (y := 1 - α - δ) (by rw [hδdef]; linarith))
        exact this.const_mul_atTop hc
      refine tendsto_atTop_mono' atTop ?_ hpow
      filter_upwards [eventually_ge_atTop X₀, eventually_gt_atTop (0 : ℝ)] with X hX hX0
      have hL' := hlowL X hX
      have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
      have hid : (L X₀ * Real.exp (-(2 * δ)) * X₀ ^ δ) * X ^ (1 - α - δ)
          = X ^ (1 - α) * (L X₀ * Real.exp (-(2 * δ)) * (X₀ / X) ^ δ) := by
        rw [Real.div_rpow hX₀0.le hX0.le]
        have hsplit : X ^ (1 - α) = X ^ (1 - α - δ) * X ^ δ := by
          rw [← Real.rpow_add hX0]
          ring_nf
        rw [hsplit]
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_left hL' hXpow.le
    exact hgrow.const_div_atTop H₀
  have hHsmall : ∀ᶠ X in atTop, H₀ ≤ (ε / 2) * (X ^ (1 - α) * L X) := by
    have hev := hdiv.eventually_le_const (by linarith : (0 : ℝ) < ε / 2)
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with X hX hX0
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    rw [div_le_iff₀ (by positivity)] at hX
    linarith
  -- the main body of the head
  filter_upwards [hHsmall, eventually_ge_atTop (X₀ / v₀), eventually_ge_atTop X₀,
    eventually_gt_atTop (0 : ℝ)] with X hHX hXv hXX₀ hX0
  have hvX : X₀ ≤ v₀ * X := by
    rw [div_le_iff₀ hv₀0] at hXv
    rw [mul_comm]
    exact hXv
  have hfl1 : ⌊(0 : ℝ)⌋₊ ≤ ⌊X₀⌋₊ := by simp
  have hfl2 : ⌊X₀⌋₊ ≤ ⌊v₀ * X⌋₊ := Nat.floor_mono hvX
  have hsplit := primeLogSum_add (f := rvPrimeWeight α L) hfl1 hfl2
  -- Potter on the second piece
  have hbody : primeLogSum (rvPrimeWeight α L) X₀ (v₀ * X)
      ≤ (L X * Real.exp (2 * δ) * X ^ δ) * primeLogSum (fun t : ℝ => t ^ (-β)) 0 (v₀ * X) := by
    have hcomp : primeLogSum (rvPrimeWeight α L) X₀ (v₀ * X)
        ≤ (L X * Real.exp (2 * δ) * X ^ δ) * primeLogSum (fun t : ℝ => t ^ (-β)) X₀ (v₀ * X) := by
      rw [primeLogSum, primeLogSum, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hprime, h1, h2⟩ := mem_shell_of_mem_filter hX₀0.le hp
      have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hX₀0 h1.le
      have hpX : (p : ℝ) ≤ X := le_trans h2 (by nlinarith [hv₀1, hX0])
      have hLp := (hpotter p X h1.le hpX).2
      have hLp0 : 0 < L (p : ℝ) := hL.pos _ hp0
      have hLX : 0 < L X := hL.pos _ hX0
      have hee : Real.exp (-(2 * δ)) * Real.exp (2 * δ) = 1 := by
        rw [← Real.exp_add]
        simp
      have hinv : ((p : ℝ) / X) ^ δ * (X / (p : ℝ)) ^ δ = 1 := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          show (p : ℝ) / X * (X / (p : ℝ)) = 1 by field_simp]
        exact Real.one_rpow _
      have hbound : L (p : ℝ) ≤ L X * Real.exp (2 * δ) * (X / p) ^ δ := by
        rw [le_div_iff₀ hLp0] at hLp
        have hnn : (0 : ℝ) ≤ Real.exp (2 * δ) * (X / (p : ℝ)) ^ δ := by positivity
        have hmul := mul_le_mul_of_nonneg_right hLp hnn
        have hlhs : Real.exp (-(2 * δ)) * ((p : ℝ) / X) ^ δ * L (p : ℝ)
            * (Real.exp (2 * δ) * (X / (p : ℝ)) ^ δ) = L (p : ℝ) := by
          calc Real.exp (-(2 * δ)) * ((p : ℝ) / X) ^ δ * L (p : ℝ)
                * (Real.exp (2 * δ) * (X / (p : ℝ)) ^ δ)
              = (Real.exp (-(2 * δ)) * Real.exp (2 * δ))
                * (((p : ℝ) / X) ^ δ * (X / (p : ℝ)) ^ δ) * L (p : ℝ) := by ring
            _ = L (p : ℝ) := by rw [hee, hinv]; ring
        rw [hlhs] at hmul
        linarith [hmul]
      have hweight : rvPrimeWeight α L (p : ℝ)
          ≤ (L X * Real.exp (2 * δ) * X ^ δ) * ((p : ℝ) ^ (-β)) := by
        rw [rvPrimeWeight]
        have hpa : (0 : ℝ) < (p : ℝ) ^ (-α) := Real.rpow_pos_of_pos hp0 _
        have hstep : (p : ℝ) ^ (-α) * L (p : ℝ)
            ≤ (p : ℝ) ^ (-α) * (L X * Real.exp (2 * δ) * (X / p) ^ δ) :=
          mul_le_mul_of_nonneg_left hbound hpa.le
        have hpd : (0 : ℝ) < (p : ℝ) ^ δ := Real.rpow_pos_of_pos hp0 _
        have hsum : (p : ℝ) ^ (-β) = (p : ℝ) ^ (-α) * ((p : ℝ) ^ δ)⁻¹ := by
          rw [hβdef, show -(α + δ) = -α + -δ by ring, Real.rpow_add hp0,
            Real.rpow_neg hp0.le δ]
        have hid : (p : ℝ) ^ (-α) * (L X * Real.exp (2 * δ) * (X / (p : ℝ)) ^ δ)
            = (L X * Real.exp (2 * δ) * X ^ δ) * ((p : ℝ) ^ (-β)) := by
          rw [Real.div_rpow hX0.le hp0.le, hsum]
          field_simp
        linarith [hstep, hid.le, hid.ge]
      have hlogp := log_nonneg_of_prime hprime
      nlinarith [hweight, hlogp]
    have hmono : primeLogSum (fun t : ℝ => t ^ (-β)) X₀ (v₀ * X)
        ≤ primeLogSum (fun t : ℝ => t ^ (-β)) 0 (v₀ * X) := by
      have hadd := primeLogSum_add (f := fun t : ℝ => t ^ (-β)) hfl1 hfl2
      have hnn : 0 ≤ primeLogSum (fun t : ℝ => t ^ (-β)) 0 X₀ := by
        refine primeLogSum_nonneg le_rfl fun p _ h1 _ => ?_
        exact Real.rpow_nonneg (le_of_lt (lt_of_le_of_lt (by norm_num) h1)) _
      linarith [hadd]
    have hcst : (0 : ℝ) ≤ L X * Real.exp (2 * δ) * X ^ δ := by
      have := hL.pos _ hX0
      have h2 : (0 : ℝ) < X ^ δ := Real.rpow_pos_of_pos hX0 _
      positivity
    linarith [hcomp, mul_le_mul_of_nonneg_left hmono hcst]
  have hpow := hK (v₀ * X) (by positivity)
  have hfinal : (L X * Real.exp (2 * δ) * X ^ δ) * (K * (v₀ * X) ^ (1 - β))
      ≤ (ε / 2) * (X ^ (1 - α) * L X) := by
    have hid : (v₀ * X) ^ (1 - β) = v₀ ^ (1 - β) * X ^ (1 - β) :=
      Real.mul_rpow hv₀0.le hX0.le
    have hXid : X ^ δ * X ^ (1 - β) = X ^ (1 - α) := by
      rw [← Real.rpow_add hX0, hβdef]
      congr 1
      ring
    have hLX : 0 < L X := hL.pos _ hX0
    have hstep : (L X * Real.exp (2 * δ) * X ^ δ) * (K * (v₀ * X) ^ (1 - β))
        = (K * Real.exp (2 * δ) * v₀ ^ (1 - β)) * (X ^ (1 - α) * L X) := by
      rw [hid, ← hXid]
      ring
    rw [hstep]
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    exact mul_le_mul_of_nonneg_right hv₀ (by positivity)
  have hcst : (0 : ℝ) ≤ L X * Real.exp (2 * δ) * X ^ δ := by
    have := hL.pos _ hX0
    have h2 : (0 : ℝ) < X ^ δ := Real.rpow_pos_of_pos hX0 _
    positivity
  have hchain : primeLogSum (rvPrimeWeight α L) X₀ (v₀ * X) ≤ (ε / 2) * (X ^ (1 - α) * L X) := by
    have := mul_le_mul_of_nonneg_left hpow hcst
    linarith [hbody, this, hfinal]
  linarith [hsplit, hHX, hchain]

end

end RHTower
