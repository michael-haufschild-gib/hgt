import GaloisForLFunctions.BezoutValuationIncidence.VasyuninFormulaForTheDiscreteBaezDuarteGram

/-!
# Vasyunin reciprocity for all moduli from the pronic covariance of residues

Under the pronic probability measure `w(M) = 1/(M(M+1))` the residue `M mod m` has mean

`Σ_M (M mod m) w(M) = log m`,

since its spectral form `-Σ α_a(ζ_a^M - 1)` pairs with the pronic characters to `Σ_a log(1 - ζ_a)`, and
`Π_a (1 - ζ_a) = m`. Its second moments are the Vasyunin series
`S(m₁, m₂) = Σ_M (M mod m₁)(M mod m₂) w(M)`, equal to `m₁ m₂` times the discrete Báez-Duarte Gram. The
covariance matrix `S(m₁, m₂) - log m₁ log m₂` is positive semidefinite. A head/tail split at `M = m`
bounds its diagonal by `2(m - 1)²/m`. For all `m, m₁, m₂ ≥ 1`, with `L = log`:

* `L(m)² ≤ π V(1, m) + (m - 1) L(m) ≤ 2(m - 1)²/m`;
* `(L m₁ - L m₂)² ≤ π (V(m₂, m₁) + V(m₁, m₂)) + (m₂ - m₁)(L m₂ - L m₁)`
  `≤ 4((m₁ - 1)²/m₁ + (m₂ - 1)²/m₂) - (L m₁ + L m₂)²`.

The reciprocity pair of Vasyunin sums is thus determined up to `O(m₁ + m₂)` by elementary terms, for
every pair of moduli.
-/

open Finset Complex RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The Vasyunin second moment `S(m₁, m₂)`. -/
def vasyuninSecondMoment (m₁ m₂ : ℕ) : ℝ :=
  (((m₁ : ℝ) - 1) * Real.log m₂ + ((m₂ : ℝ) - 1) * Real.log m₁) / 2 -
    Real.pi / 2 * (vasyuninSum m₂ m₁ - vasyuninSum 1 m₁ + vasyuninSum m₁ m₂ - vasyuninSum 1 m₂)

/-- Hecke's relation turns the cotangent–sawtooth sum into Vasyunin sums. -/
theorem cotangentSawtooth_sum_eq_vasyunin {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
      (Real.cot (Real.pi * ((a : ℝ) / m₁)) + Real.cot (Real.pi * ((b : ℝ) / m₂))) *
        sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
      vasyuninSum m₂ m₁ - vasyuninSum 1 m₁ + vasyuninSum m₁ m₂ - vasyuninSum 1 m₂ := by
  simp only [add_mul, sum_add_distrib]
  have e1 : ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
      Real.cot (Real.pi * ((a : ℝ) / m₁)) * sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
      vasyuninSum m₂ m₁ - vasyuninSum 1 m₁ := by
    rw [vasyuninSum, vasyuninSum, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← mul_sum, sum_Ico_sawtooth_add h₂, mul_sub]
    congr 2 <;> ring_nf
  have e2 : ∑ a ∈ Ico 1 m₁, ∑ b ∈ Ico 1 m₂,
      Real.cot (Real.pi * ((b : ℝ) / m₂)) * sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
      vasyuninSum m₁ m₂ - vasyuninSum 1 m₂ := by
    rw [sum_comm, vasyuninSum, vasyuninSum, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [← mul_sum]
    have h := sum_Ico_sawtooth_add h₁ ((b : ℝ) / m₂)
    rw [show ∑ a ∈ Ico 1 m₁, sawtooth ((a : ℝ) / m₁ + (b : ℝ) / m₂) =
        ∑ a ∈ Ico 1 m₁, sawtooth ((b : ℝ) / m₂ + (a : ℝ) / m₁) from
      sum_congr rfl fun a _ => by rw [add_comm], h, mul_sub]
    congr 2 <;> ring_nf
  rw [e1, e2]
  ring

/-- The second moments of residues under the pronic measure. -/
theorem hasSum_natMod_mul_natMod_vasyunin {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    HasSum (fun M : ℕ => ((M % m₁ : ℕ) : ℝ) * ((M % m₂ : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)))
      (vasyuninSecondMoment m₁ m₂) := by
  have h := hasSum_natMod_mul_natMod h₁ h₂
  rwa [cotangentSawtooth_sum_eq_vasyunin h₁ h₂] at h

/-- **The pronic mean of a residue.** `Σ_M (M mod m)/(M(M+1)) = log m`. -/
theorem hasSum_natMod_pronic {m : ℕ} (hm : 0 < m) :
    HasSum (fun M : ℕ => ((M % m : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))) (Real.log m) := by
  have hterm : ∀ M : ℕ, ((((M % m : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)) : ℝ) : ℂ) =
      ∑ a ∈ Ico 1 m, -(rootAt m a / (rootAt m a - 1)) *
        (pronicTerm (rootAt m a) M - pronicTerm 1 M) := by
    intro M
    push_cast
    rw [natMod_eq_spectral hm, neg_div, sum_div, ← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [pronicTerm, one_pow]
    ring
  have hV : HasSum (fun M : ℕ => ((((M % m : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1)) : ℝ) : ℂ))
      (∑ a ∈ Ico 1 m, log (1 - rootAt m a)) := by
    simp only [hterm]
    refine hasSum_sum fun a ha => ?_
    have h := (hasSum_pronicTerm_of_norm_eq_one (norm_rootAt m a)).sub
      (hasSum_pronicTerm_of_norm_eq_one (by simp : ‖(1 : ℂ)‖ = 1))
    have hval : log (1 - rootAt m a) = -(rootAt m a / (rootAt m a - 1)) *
        ((1 + cyclotomicLogKernel (rootAt m a)) - (1 + cyclotomicLogKernel 1)) := by
      have hK1 : cyclotomicLogKernel 1 = 0 := by simp [cyclotomicLogKernel]
      rw [hK1, add_zero, add_sub_cancel_left, neg_mul, rootAt_div_mul_cyclotomicLogKernel ha,
        neg_neg]
    rw [hval]
    exact h.mul_left _
  have hreal := Complex.reCLM.hasSum hV
  simp only [Complex.reCLM_apply, Complex.ofReal_re, re_sum, Complex.log_re] at hreal
  rwa [sum_Ico_log_norm_one_sub_rootAt hm] at hreal

/-- **Positivity of the pronic covariance of residues.** For every real `s`,
`(S(m₁,m₁) - L₁²) + 2s(S(m₁,m₂) - L₁L₂) + s²(S(m₂,m₂) - L₂²) ≥ 0`. -/
theorem vasyunin_covariance_nonneg {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) (s : ℝ) :
    0 ≤ (vasyuninSecondMoment m₁ m₁ - Real.log m₁ ^ 2) +
      2 * s * (vasyuninSecondMoment m₁ m₂ - Real.log m₁ * Real.log m₂) +
        s ^ 2 * (vasyuninSecondMoment m₂ m₂ - Real.log m₂ ^ 2) := by
  set w : ℕ → ℝ := fun M => 1 / ((M : ℝ) * ((M : ℝ) + 1))
  set r₁ : ℕ → ℝ := fun M => ((M % m₁ : ℕ) : ℝ)
  set r₂ : ℕ → ℝ := fun M => ((M % m₂ : ℕ) : ℝ)
  have hw : HasSum w 1 := RHTower.hasSum_pm_reciprocal_weight
  have h11 := hasSum_natMod_mul_natMod_vasyunin h₁ h₁
  have h12 := hasSum_natMod_mul_natMod_vasyunin h₁ h₂
  have h22 := hasSum_natMod_mul_natMod_vasyunin h₂ h₂
  have hm₁ := hasSum_natMod_pronic h₁
  have hm₂ := hasSum_natMod_pronic h₂
  set L₁ := Real.log m₁
  set L₂ := Real.log m₂
  -- the square `w (r₁ - L₁ + s (r₂ - L₂))²` expanded into the moment series
  have hsq := ((((((h11.add (h12.mul_left (2 * s))).add (h22.mul_left (s ^ 2))).sub
    (hm₁.mul_left (2 * L₁ + 2 * s * L₂))).sub (hm₂.mul_left (2 * s * L₁ + 2 * s ^ 2 * L₂))).add
      (hw.mul_left ((L₁ + s * L₂) ^ 2))))
  have hfun : ∀ M : ℕ, r₁ M * r₁ M / ((M : ℝ) * ((M : ℝ) + 1)) +
      2 * s * (r₁ M * r₂ M / ((M : ℝ) * ((M : ℝ) + 1))) +
      s ^ 2 * (r₂ M * r₂ M / ((M : ℝ) * ((M : ℝ) + 1))) -
      (2 * L₁ + 2 * s * L₂) * (r₁ M / ((M : ℝ) * ((M : ℝ) + 1))) -
      (2 * s * L₁ + 2 * s ^ 2 * L₂) * (r₂ M / ((M : ℝ) * ((M : ℝ) + 1))) +
      (L₁ + s * L₂) ^ 2 * w M =
      (r₁ M - L₁ + s * (r₂ M - L₂)) ^ 2 * w M := fun M => by
    simp only [w]
    ring
  have hnn := hsq.nonneg fun M => by
    rw [hfun M]
    exact mul_nonneg (sq_nonneg _) (by simp only [w]; positivity)
  nlinarith [hnn]

/-- The diagonal moment: `S(m, m) = (m - 1) log m + π V(1, m)`. -/
theorem vasyuninSecondMoment_self {m : ℕ} (hm : 0 < m) :
    vasyuninSecondMoment m m = ((m : ℝ) - 1) * Real.log m + Real.pi * vasyuninSum 1 m := by
  have hVmm : vasyuninSum m m = 0 := by
    unfold vasyuninSum
    refine sum_eq_zero fun a _ => ?_
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [show (m : ℝ) * a / m = ((a : ℤ) : ℝ) by field_simp; push_cast; ring,
      show sawtooth ((a : ℤ) : ℝ) = 0 by simp [sawtooth], mul_zero]
  rw [vasyuninSecondMoment, hVmm]
  ring

/-- **The diagonal moment is at most `2(m - 1)²/m`.** -/
theorem vasyuninSecondMoment_self_le {m : ℕ} (hm : 0 < m) :
    vasyuninSecondMoment m m ≤ 2 * ((m : ℝ) - 1) ^ 2 / m := by
  set w : ℕ → ℝ := fun M => 1 / ((M : ℝ) * ((M : ℝ) + 1))
  set t : ℕ → ℝ := fun M => ((M % m : ℕ) : ℝ) * ((M % m : ℕ) : ℝ) / ((M : ℝ) * ((M : ℝ) + 1))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : HasSum w 1 := RHTower.hasSum_pm_reciprocal_weight
  have ht := hasSum_natMod_mul_natMod_vasyunin hm hm
  have hsum : Summable t := ht.summable
  rw [← ht.tsum_eq, ← hsum.sum_add_tsum_nat_add m]
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hmass : ∑ M ∈ range m, w M = 1 - 1 / (m : ℝ) := by
    rw [hn, sum_range_succ_pronic_mass n]
    push_cast
    ring
  -- head: `t 0 = 0`, and `t M = M/(M+1) ≤ (m-1)/m` for `0 < M < m`
  have hhead : ∑ M ∈ range m, t M ≤ ((m : ℝ) - 1) ^ 2 / m := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hm]
    have h0 : t 0 = 0 := by simp [t]
    have hle : ∀ M ∈ Ico 1 m, t M ≤ ((m : ℝ) - 1) / m := fun M hM => by
      obtain ⟨hM1, hM2⟩ := mem_Ico.mp hM
      have hM0' : (0 : ℝ) < M := by exact_mod_cast hM1
      have hMm : (M : ℝ) + 1 ≤ m := by exact_mod_cast hM2
      simp only [t]
      rw [Nat.mod_eq_of_lt hM2, div_le_div_iff₀ (by positivity) hmR]
      nlinarith
    calc t 0 + ∑ M ∈ Ico (0 + 1) m, t M ≤ 0 + ∑ M ∈ Ico 1 m, ((m : ℝ) - 1) / m := by
          rw [h0]
          exact add_le_add le_rfl (sum_le_sum hle)
      _ = ((m : ℝ) - 1) ^ 2 / m := by
          rw [zero_add, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ m),
            Nat.cast_one]
          ring
  -- tail: `M mod m ≤ m - 1` and the tail mass is `1/m`
  have htail : ∑' n, t (n + m) ≤ ((m : ℝ) - 1) ^ 2 * (1 / m) := by
    have hwt : ∑' n, w (n + m) = 1 / m := by
      have h := hw.summable.sum_add_tsum_nat_add m
      rw [hw.tsum_eq, hmass] at h
      linarith
    have hs1 : Summable (fun n => t (n + m)) := (summable_nat_add_iff m).mpr hsum
    have hs2 : Summable (fun n => ((m : ℝ) - 1) ^ 2 * w (n + m)) :=
      ((summable_nat_add_iff m).mpr hw.summable).mul_left _
    have hpt : ∀ n, t (n + m) ≤ ((m : ℝ) - 1) ^ 2 * w (n + m) := fun n => by
      have hlt : ((n + m) % m : ℕ) + 1 ≤ m := Nat.mod_lt _ hm
      have hc : (((n + m) % m : ℕ) : ℝ) ≤ (m : ℝ) - 1 := by
        have : ((((n + m) % m : ℕ) : ℝ)) + 1 ≤ m := by exact_mod_cast hlt
        linarith
      have h0 : (0 : ℝ) ≤ (((n + m) % m : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [t, w]
      rw [div_eq_mul_one_div _ (((n + m : ℕ) : ℝ) * (((n + m : ℕ) : ℝ) + 1))]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    calc ∑' n, t (n + m) ≤ ∑' n, ((m : ℝ) - 1) ^ 2 * w (n + m) := Summable.tsum_le_tsum hpt hs1 hs2
      _ = ((m : ℝ) - 1) ^ 2 * (1 / m) := by rw [tsum_mul_left, hwt]
  have : ((m : ℝ) - 1) ^ 2 * (1 / m) = ((m : ℝ) - 1) ^ 2 / m := by ring
  have h2 : 2 * ((m : ℝ) - 1) ^ 2 / m = ((m : ℝ) - 1) ^ 2 / m + ((m : ℝ) - 1) ^ 2 / m := by ring
  linarith

/-- **Two-sided law for `V(1, m)`, all moduli.** -/
theorem vasyuninSum_one_two_sided {m : ℕ} (hm : 0 < m) :
    Real.log m ^ 2 ≤ Real.pi * vasyuninSum 1 m + ((m : ℝ) - 1) * Real.log m ∧
      Real.pi * vasyuninSum 1 m + ((m : ℝ) - 1) * Real.log m ≤ 2 * ((m : ℝ) - 1) ^ 2 / m := by
  have hpos := vasyunin_covariance_nonneg hm hm 0
  have hup := vasyuninSecondMoment_self_le hm
  rw [vasyuninSecondMoment_self hm] at hpos hup
  constructor <;> nlinarith

/-- **Vasyunin reciprocity for all moduli.** -/
theorem vasyunin_reciprocity_all_moduli {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    (Real.log m₁ - Real.log m₂) ^ 2 ≤
        Real.pi * (vasyuninSum m₂ m₁ + vasyuninSum m₁ m₂) +
          ((m₂ : ℝ) - m₁) * (Real.log m₂ - Real.log m₁) ∧
      Real.pi * (vasyuninSum m₂ m₁ + vasyuninSum m₁ m₂) +
          ((m₂ : ℝ) - m₁) * (Real.log m₂ - Real.log m₁) ≤
        4 * (((m₁ : ℝ) - 1) ^ 2 / m₁ + ((m₂ : ℝ) - 1) ^ 2 / m₂) -
          (Real.log m₁ + Real.log m₂) ^ 2 := by
  have hplus := vasyunin_covariance_nonneg h₁ h₂ 1
  have hminus := vasyunin_covariance_nonneg h₁ h₂ (-1)
  have hup₁ := vasyuninSecondMoment_self_le h₁
  have hup₂ := vasyuninSecondMoment_self_le h₂
  have hd₁ := vasyuninSecondMoment_self h₁
  have hd₂ := vasyuninSecondMoment_self h₂
  have h12 : vasyuninSecondMoment m₁ m₂ =
      (((m₁ : ℝ) - 1) * Real.log m₂ + ((m₂ : ℝ) - 1) * Real.log m₁) / 2 -
        Real.pi / 2 * (vasyuninSum m₂ m₁ + vasyuninSum m₁ m₂) +
          Real.pi / 2 * (vasyuninSum 1 m₁ + vasyuninSum 1 m₂) := by
    rw [vasyuninSecondMoment]
    ring
  rw [h12, hd₁, hd₂] at hplus hminus
  rw [hd₁] at hup₁
  rw [hd₂] at hup₂
  rw [mul_div_assoc] at hup₁ hup₂
  constructor
  · linarith
  · linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
