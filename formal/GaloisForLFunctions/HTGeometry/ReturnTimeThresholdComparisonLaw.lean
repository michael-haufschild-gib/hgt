import GaloisForLFunctions.HTGeometry.FidelityReturnExponent

open Filter Topology Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Times after a cutoff at which a nonnegative return signal is below threshold. -/
def scalarSignalReturnSet (signal : ℝ → ℝ) (t₀ δ : ℝ) : Set ℝ :=
  {t | t₀ ≤ t ∧ signal t < δ}

/-- First post-cutoff return of a scalar signal. -/
def scalarSignalReturnTime (signal : ℝ → ℝ) (t₀ δ : ℝ) : ℝ :=
  sInf (scalarSignalReturnSet signal t₀ δ)

@[simp] theorem scalarSignalReturnSet_spectralReturnDeficit {D : ℕ}
    (E p : Fin D → ℝ) (t₀ δ : ℝ) :
    scalarSignalReturnSet (spectralReturnDeficit E p) t₀ δ =
      fidelityReturnSet E p t₀ δ := rfl

@[simp] theorem scalarSignalReturnTime_spectralReturnDeficit {D : ℕ}
    (E p : Fin D → ℝ) (t₀ δ : ℝ) :
    scalarSignalReturnTime (spectralReturnDeficit E p) t₀ δ =
      fidelityReturnTime E p t₀ δ := rfl

theorem bddBelow_scalarSignalReturnSet (signal : ℝ → ℝ) (t₀ δ : ℝ) :
    BddBelow (scalarSignalReturnSet signal t₀ δ) :=
  ⟨t₀, fun _ ht => ht.1⟩

theorem le_scalarSignalReturnTime {signal : ℝ → ℝ} {t₀ δ : ℝ}
    (hne : (scalarSignalReturnSet signal t₀ δ).Nonempty) :
    t₀ ≤ scalarSignalReturnTime signal t₀ δ :=
  le_csInf hne fun _ ht => ht.1

theorem scalarSignalReturnTime_mono_of_set_subset
    {signal₁ signal₂ : ℝ → ℝ} {t₀ δ₁ δ₂ : ℝ}
    (hne₂ : (scalarSignalReturnSet signal₂ t₀ δ₂).Nonempty)
    (hsub : scalarSignalReturnSet signal₂ t₀ δ₂ ⊆
      scalarSignalReturnSet signal₁ t₀ δ₁) :
    scalarSignalReturnTime signal₁ t₀ δ₁ ≤
      scalarSignalReturnTime signal₂ t₀ δ₂ := by
  apply le_csInf hne₂
  intro t ht
  exact csInf_le (bddBelow_scalarSignalReturnSet signal₁ t₀ δ₁) (hsub ht)

theorem tendsto_pos_const_mul_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun δ : ℝ => c * δ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hbase : Tendsto (fun δ : ℝ => c * δ) (𝓝 0) (𝓝 (c * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa using hbase.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_pos hc hδ

theorem tendsto_log_one_div_const_mul_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun δ : ℝ => Real.log (1 / (c * δ)) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hlim : Tendsto
      (fun δ : ℝ => (-Real.log c) / Real.log (1 / δ) + 1)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using (tendsto_const_div_log_one_div (-Real.log c)).add
      (tendsto_const_nhds (x := (1 : ℝ)) (f := 𝓝[>] (0 : ℝ)))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ hδ1
  have hδ0 : 0 < δ := hδ
  have hlogne : Real.log (1 / δ) ≠ 0 := by
    have : 1 < 1 / δ := by
      rw [lt_div_iff₀ hδ0]
      linarith [hδ1.2]
    exact (Real.log_pos this).ne'
  have hlog : Real.log (1 / (c * δ)) = -Real.log c + Real.log (1 / δ) := by
    rw [one_div, Real.log_inv, Real.log_mul hc.ne' hδ0.ne', one_div,
      Real.log_inv]
    ring
  rw [hlog, add_div, div_self hlogne]

theorem tendsto_log_returnTime_scaled
    {returnTime : ℝ → ℝ} {α c : ℝ} (hc : 0 < c)
    (h : Tendsto
      (fun δ : ℝ => Real.log (returnTime δ) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 α)) :
    Tendsto
      (fun δ : ℝ => Real.log (returnTime (c * δ)) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 α) := by
  have hcomp := h.comp (tendsto_pos_const_mul_nhdsGT hc)
  have hratio := tendsto_log_one_div_const_mul_ratio hc
  have hprod := hcomp.mul hratio
  have halpha : α * 1 = α := mul_one α
  rw [halpha] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Ioo_mem_nhdsGT (show 0 < 1 / (2 * c) by positivity)] with δ hδ hδsmall
  have hcδpos : 0 < c * δ := mul_pos hc hδ
  have hcδne : c * δ ≠ 1 := by
    have : c * δ < 1 / 2 := by
      calc
        c * δ < c * (1 / (2 * c)) := mul_lt_mul_of_pos_left hδsmall.2 hc
        _ = 1 / 2 := by field_simp
    linarith
  have hden : Real.log (1 / (c * δ)) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · positivity
    · intro h
      apply hcδne
      field_simp at h
      rw [← h]
      field_simp [(ne_of_gt hδsmall.1)]
  simp only [Function.comp_apply]
  field_simp

/-- Multiplicatively comparable nonnegative signals have identical logarithmic
first-return exponents. -/
theorem tendsto_log_scalarSignalReturnTime_of_comparable
    (signal reference : ℝ → ℝ) {a b t₀ α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht₀ : 0 < t₀)
    (hcompare : ∀ t, a * reference t ≤ signal t ∧ signal t ≤ b * reference t)
    (hne : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      (scalarSignalReturnSet reference t₀ δ).Nonempty)
    (href : Tendsto
      (fun δ : ℝ => Real.log (scalarSignalReturnTime reference t₀ δ) /
        Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 α)) :
    Tendsto
      (fun δ : ℝ => Real.log (scalarSignalReturnTime signal t₀ δ) /
        Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 α) := by
  have hlow := tendsto_log_returnTime_scaled (returnTime :=
    scalarSignalReturnTime reference t₀) (c := 1 / a) (by positivity) href
  have hhigh := tendsto_log_returnTime_scaled (returnTime :=
    scalarSignalReturnTime reference t₀) (c := 1 / b) (by positivity) href
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ),
      (tendsto_pos_const_mul_nhdsGT (show 0 < 1 / b by positivity)).eventually hne]
      with δ hδ hδ1 hrefB
    have hδ0 : 0 < δ := hδ
    have hlogpos : 0 < Real.log (1 / δ) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hδ0]
      linarith [hδ1.2]
    have hsubUpper : scalarSignalReturnSet reference t₀ (δ / b) ⊆
        scalarSignalReturnSet signal t₀ δ := by
      intro t ht
      refine ⟨ht.1, lt_of_le_of_lt (hcompare t).2 ?_⟩
      have hmul := mul_lt_mul_of_pos_left ht.2 hb
      rw [mul_div_cancel₀ δ hb.ne'] at hmul
      exact hmul
    have hrefB' : (scalarSignalReturnSet reference t₀ (δ / b)).Nonempty := by
      simpa [div_eq_mul_inv, mul_comm] using hrefB
    have hsignalNonempty : (scalarSignalReturnSet signal t₀ δ).Nonempty :=
      Set.Nonempty.mono hsubUpper hrefB'
    have hsubLower : scalarSignalReturnSet signal t₀ δ ⊆
        scalarSignalReturnSet reference t₀ (δ / a) := by
      intro t ht
      refine ⟨ht.1, ?_⟩
      rw [lt_div_iff₀ ha]
      simpa [mul_comm] using lt_of_le_of_lt (hcompare t).1 ht.2
    have htime := scalarSignalReturnTime_mono_of_set_subset
      hsignalNonempty hsubLower
    have hposRef : 0 < scalarSignalReturnTime reference t₀ (δ / a) :=
      lt_of_lt_of_le ht₀ (le_scalarSignalReturnTime
        (hne := Set.Nonempty.mono hsubLower hsignalNonempty))
    have htime' : scalarSignalReturnTime reference t₀ ((1 / a) * δ) ≤
        scalarSignalReturnTime signal t₀ δ := by
      simpa [div_eq_mul_inv, mul_comm] using htime
    have hposRef' : 0 < scalarSignalReturnTime reference t₀ ((1 / a) * δ) := by
      simpa [div_eq_mul_inv, mul_comm] using hposRef
    exact (div_le_div_iff_of_pos_right hlogpos).2
      (Real.log_le_log hposRef' htime')
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ),
      (tendsto_pos_const_mul_nhdsGT (show 0 < 1 / b by positivity)).eventually hne]
      with δ hδ hδ1 hrefB
    have hδ0 : 0 < δ := hδ
    have hlogpos : 0 < Real.log (1 / δ) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hδ0]
      linarith [hδ1.2]
    have hsub : scalarSignalReturnSet reference t₀ (δ / b) ⊆
        scalarSignalReturnSet signal t₀ δ := by
      intro t ht
      refine ⟨ht.1, lt_of_le_of_lt (hcompare t).2 ?_⟩
      have hmul := mul_lt_mul_of_pos_left ht.2 hb
      rw [mul_div_cancel₀ δ hb.ne'] at hmul
      exact hmul
    have hrefB' : (scalarSignalReturnSet reference t₀ (δ / b)).Nonempty := by
      simpa [div_eq_mul_inv, mul_comm] using hrefB
    have htime := scalarSignalReturnTime_mono_of_set_subset hrefB' hsub
    have hsignalNonempty : (scalarSignalReturnSet signal t₀ δ).Nonempty :=
      Set.Nonempty.mono hsub hrefB'
    have hposSig : 0 < scalarSignalReturnTime signal t₀ δ :=
      lt_of_lt_of_le ht₀ (le_scalarSignalReturnTime hsignalNonempty)
    have htime' : scalarSignalReturnTime signal t₀ δ ≤
        scalarSignalReturnTime reference t₀ ((1 / b) * δ) := by
      simpa [div_eq_mul_inv, mul_comm] using htime
    exact (div_le_div_iff_of_pos_right hlogpos).2
      (Real.log_le_log hposSig htime')

/-- A single exact zero after the cutoff uniformly bounds every positive-threshold first return,
so its logarithmic shrinking-target exponent is zero. -/
theorem tendsto_log_scalarSignalReturnTime_zero_of_exact_zero
    (signal : ℝ → ℝ) {t₀ tau : ℝ}
    (ht₀ : 0 < t₀) (ht₀tau : t₀ ≤ tau) (hzero : signal tau = 0) :
    Tendsto
      (fun delta : ℝ => Real.log (scalarSignalReturnTime signal t₀ delta) /
        Real.log (1 / delta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have htau : 0 < tau := lt_of_lt_of_le ht₀ ht₀tau
  have hreturn : ∀ {delta : ℝ}, 0 < delta →
      (scalarSignalReturnSet signal t₀ delta).Nonempty ∧
        scalarSignalReturnTime signal t₀ delta ≤ tau := by
    intro delta hdelta
    have hmem : tau ∈ scalarSignalReturnSet signal t₀ delta :=
      ⟨ht₀tau, by rw [hzero]; exact hdelta⟩
    exact ⟨⟨tau, hmem⟩,
      csInf_le (bddBelow_scalarSignalReturnSet signal t₀ delta) hmem⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_div_log_one_div (Real.log t₀))
    (tendsto_const_div_log_one_div (Real.log tau)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with delta hdelta hdelta1
    have hlogpos : 0 < Real.log (1 / delta) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hdelta]
      linarith [hdelta1.2]
    have hr := hreturn hdelta
    have hlower := le_scalarSignalReturnTime hr.1
    exact (div_le_div_iff_of_pos_right hlogpos).2
      (Real.log_le_log ht₀ hlower)
  · filter_upwards [self_mem_nhdsWithin,
      Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with delta hdelta hdelta1
    have hlogpos : 0 < Real.log (1 / delta) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hdelta]
      linarith [hdelta1.2]
    have hr := hreturn hdelta
    have hlower := le_scalarSignalReturnTime hr.1
    have htimepos : 0 < scalarSignalReturnTime signal t₀ delta :=
      lt_of_lt_of_le ht₀ hlower
    exact (div_le_div_iff_of_pos_right hlogpos).2
      (Real.log_le_log htimepos hr.2)

end

end GaloisForLFunctions.HTGeometry
