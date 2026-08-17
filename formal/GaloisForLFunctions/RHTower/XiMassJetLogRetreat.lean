import GaloisForLFunctions.RHTower.XiMassLogRetreatTail

/-!
# The logarithmic retreat data, extracted

The exterior tail at a logarithmic retreat needs two facts about `H = κ_B u − q log u`, both proved
inside `exists_norm_logRetreatTail_le` but not exposed there:

* the retreat stays inside a fixed inner cone, `((1+κ_B)/2)·u ≤ H`;
* the action costs at most the linear rate, `g_u(H) ≤ m_B·q·log u + 1`, `m_B = 2a² − 1/2`.

Both are needed again for the jet-modified tail, where the profile changes but the geometry does
not, so they are recorded here as a standalone statement.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **The logarithmic retreat data.**  Past an explicit height the retreat `κ_B u − q log u` lies in
a fixed inner cone and costs the action at most `m_B·q·log u + 1`. -/
theorem exists_logRetreat_data {a q : ℝ} (ha : 1 / 2 < a) (hq : 0 < q) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ((1 + xiMassSpacelikeSharpSlope a) / 2 * u
          ≤ xiMassSpacelikeSharpSlope a * u - q * Real.log u)
        ∧ ((xiMassSpacelikeSharpSlope a * u - q * Real.log u) / 2
            - a * Real.sqrt ((xiMassSpacelikeSharpSlope a * u - q * Real.log u) ^ 2 - u ^ 2)
          ≤ (2 * a ^ 2 - 1 / 2) * (q * Real.log u) + 1) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkap : 0 < xiMassSpacelikeSharpSlope a := sharpSlope_pos ha
  have hkone : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hk2 : (0 : ℝ) < xiMassSpacelikeSharpSlope a ^ 2 - 1 := by nlinarith
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℝ, (1 + xiMassSpacelikeSharpSlope a) / 2 = k0 := ⟨_, rfl⟩
  have hk0one : 1 < k0 := by rw [← hk0def]; linarith
  have hgapk : (0 : ℝ) < xiMassSpacelikeSharpSlope a - k0 := by rw [← hk0def]; linarith
  obtain ⟨D, hD⟩ : ∃ D : ℝ, 8 * a ^ 2 * xiMassSpacelikeSharpSlope a * q ^ 2
      / (xiMassSpacelikeSharpSlope a ^ 2 - 1) = D := ⟨_, rfl⟩
  have hDnn : (0 : ℝ) ≤ D := by rw [← hD]; positivity
  have hgrow : Tendsto (fun u : ℝ => u ^ ((3 : ℝ) / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hgrow2 : Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 2)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨u₁, hu₁⟩ :=
    ((((hgrow.eventually_ge_atTop (4 * q / (xiMassSpacelikeSharpSlope a - k0))).and
      (hgrow.eventually_ge_atTop (16 * xiMassSpacelikeSharpSlope a * q
        / (xiMassSpacelikeSharpSlope a ^ 2 - 1)))).and
      (hgrow2.eventually_ge_atTop (16 * D))).and
      (eventually_ge_atTop (2 : ℝ))).exists_forall_of_atTop
  refine ⟨max u₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun u hu => ?_⟩
  have hu2 : (2 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hupos : (0 : ℝ) < u := by linarith
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, _⟩ := hu₁ u (le_trans (le_max_left _ _) hu)
  have hlogpos : 0 < Real.log u := Real.log_pos (by linarith)
  have hlog0 : 0 ≤ Real.log u := hlogpos.le
  have hlog4 : Real.log u ≤ 4 * u ^ ((1 : ℝ) / 4) := log_le_four_mul_rpow hupos
  have hrpos : (0 : ℝ) < q * Real.log u := mul_pos hq hlogpos
  have hsplit34 : u ^ ((1 : ℝ) / 4) * u ^ ((3 : ℝ) / 4) = u := by
    rw [← Real.rpow_add hupos]
    norm_num
  have hpow4 : (0 : ℝ) < u ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hupos _
  have hpow2 : (0 : ℝ) < u ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hupos _
  have hcone : k0 * u ≤ xiMassSpacelikeSharpSlope a * u - q * Real.log u := by
    have h1 : 4 * q ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hgapk] at hA
      linarith
    have h2 : 4 * q * u ^ ((1 : ℝ) / 4)
        ≤ (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (xiMassSpacelikeSharpSlope a - k0) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)
        = (xiMassSpacelikeSharpSlope a - k0) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    nlinarith [mul_le_mul_of_nonneg_left hlog4 hq.le, h2]
  have hx : 2 * xiMassSpacelikeSharpSlope a * (q * Real.log u)
      ≤ (1 / 2) * (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)) := by
    have h1 : 16 * xiMassSpacelikeSharpSlope a * q
        ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) := by
      rw [div_le_iff₀ hk2] at hB
      linarith
    have h2 : 16 * xiMassSpacelikeSharpSlope a * q * u ^ ((1 : ℝ) / 4)
        ≤ (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right h1 hpow4.le
    have h3 : (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u ^ ((3 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)
        = (xiMassSpacelikeSharpSlope a ^ 2 - 1) * u := by
      rw [mul_assoc, mul_comm (u ^ ((3 : ℝ) / 4)), hsplit34]
    rw [h3] at h2
    nlinarith [mul_le_mul_of_nonneg_left hlog4 (by positivity :
      (0 : ℝ) ≤ 2 * xiMassSpacelikeSharpSlope a * q), h2]
  have hcurv : 4 * a ^ 2 * (q * Real.log u)
      * (2 * xiMassSpacelikeSharpSlope a * (q * Real.log u)
        / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1))) ≤ 1 := by
    have hval : 4 * a ^ 2 * (q * Real.log u)
        * (2 * xiMassSpacelikeSharpSlope a * (q * Real.log u)
          / (u * (xiMassSpacelikeSharpSlope a ^ 2 - 1)))
        = D * (Real.log u * Real.log u / u) := by
      rw [← hD]
      field_simp
      ring
    rw [hval]
    have hlogsq : Real.log u * Real.log u / u ≤ 16 * u ^ (-((1 : ℝ) / 2)) := by
      have hsq : Real.log u * Real.log u ≤ 16 * (u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4)) := by
        nlinarith [hlog4, hlog0, hpow4]
      have hid : u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) = u ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hupos]
        norm_num
      rw [hid] at hsq
      rw [div_le_iff₀ hupos]
      have hneg : u ^ (-((1 : ℝ) / 2)) * u = u ^ ((1 : ℝ) / 2) := by
        nth_rewrite 2 [show u = u ^ (1 : ℝ) from (Real.rpow_one u).symm]
        rw [← Real.rpow_add hupos]
        norm_num
      rw [mul_assoc, hneg]
      linarith
    have hDsmall : D * (16 * u ^ (-((1 : ℝ) / 2))) ≤ 1 := by
      have hinv : u ^ (-((1 : ℝ) / 2)) * u ^ ((1 : ℝ) / 2) = 1 := by
        rw [← Real.rpow_add hupos]
        norm_num
      have hstep : D * (16 * u ^ (-((1 : ℝ) / 2))) * u ^ ((1 : ℝ) / 2) = 16 * D := by
        calc D * (16 * u ^ (-((1 : ℝ) / 2))) * u ^ ((1 : ℝ) / 2)
            = 16 * D * (u ^ (-((1 : ℝ) / 2)) * u ^ ((1 : ℝ) / 2)) := by ring
          _ = 16 * D := by rw [hinv]; ring
      have hCle : 16 * D ≤ u ^ ((1 : ℝ) / 2) := hC
      have hfin : D * (16 * u ^ (-((1 : ℝ) / 2))) * u ^ ((1 : ℝ) / 2)
          ≤ 1 * u ^ ((1 : ℝ) / 2) := by
        rw [hstep, one_mul]
        exact hCle
      exact le_of_mul_le_mul_right hfin hpow2
    nlinarith [mul_le_mul_of_nonneg_left hlogsq hDnn, hDsmall]
  refine ⟨by rw [hk0def]; exact hcone, ?_⟩
  have haction := xiMassAction_penetration_le (a := a) (u := u) (r := q * Real.log u)
    ha hupos hrpos hx
  refine haction.trans ?_
  linarith [hcurv]

end

end RHTower
