import GaloisForLFunctions.RHTower.SteinhausCumulantSlope

/-!
# The Legendre transform of a power law

If the cumulant satisfies `Λ_α(λ) ∼ A λ^p` as `λ → 0⁺` for some `p > 1` and `A > 0`, then its
Legendre transform satisfies

`I_α(q) ∼ (p−1) p^{−p/(p−1)} A^{−1/(p−1)} q^{p/(p−1)}`   as `q → 0⁺`.

Both halves are elementary.  The lower half evaluates the tilt `λ = (q/(pA))^{1/(p−1)}`, at which
`A λ^p = λq/p`, so the value is exactly `λq(p−1)/p`.  The upper half is Young's inequality
`λq ≤ Aλ^p + C q^{p/(p−1)}` for small tilts, together with the nondecreasing slope of the cumulant,
which makes every large tilt contribute a negative value.

Specialised at `p = 2` this is the sub-critical regime; at `p = 1/α` it is the super-critical one.
-/

open Filter Topology Set

namespace HTGeometry

noncomputable section

/-- The Legendre constant attached to the power law `A λ^p`. -/
def rvLegConst (p A : ℝ) : ℝ := (p - 1) * p ^ (-(p / (p - 1))) * A ^ (-(1 / (p - 1)))

theorem rvLegConst_pos {p A : ℝ} (hp : 1 < p) (hA : 0 < A) : 0 < rvLegConst p A := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have h1 : (0 : ℝ) < p ^ (-(p / (p - 1))) := Real.rpow_pos_of_pos hp0 _
  have h2 : (0 : ℝ) < A ^ (-(1 / (p - 1))) := Real.rpow_pos_of_pos hA _
  have h3 : (0 : ℝ) < p - 1 := by linarith
  exact mul_pos (mul_pos h3 h1) h2

theorem continuousAt_rvLegConst {p A : ℝ} (hA : 0 < A) :
    ContinuousAt (fun B : ℝ => rvLegConst p B) A := by
  have h : ContinuousAt (fun B : ℝ => B ^ (-(1 / (p - 1)))) A :=
    Real.continuousAt_rpow_const A _ (Or.inl hA.ne')
  exact h.const_mul _

/-- The tilt realizing the Legendre transform of `A λ^p` at `q`. -/
def rvLegTilt (p A q : ℝ) : ℝ := (q / (p * A)) ^ (1 / (p - 1))

theorem rvLegTilt_pos {p A q : ℝ} (hp : 1 < p) (hA : 0 < A) (hq : 0 < q) :
    0 < rvLegTilt p A q := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The optimal tilt tends to zero with `q`. -/
theorem tendsto_rvLegTilt {p A : ℝ} (hp : 1 < p) (hA : 0 < A) :
    Tendsto (fun q : ℝ => rvLegTilt p A q) (𝓝[>] 0) (𝓝[>] 0) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hk : (0 : ℝ) < 1 / (p - 1) := by
    have : (0 : ℝ) < p - 1 := by linarith
    positivity
  have hcont : ContinuousAt (fun x : ℝ => x ^ (1 / (p - 1))) 0 :=
    Real.continuousAt_rpow_const 0 _ (Or.inr hk.le)
  have hdiv : Tendsto (fun q : ℝ => q / (p * A)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun q : ℝ => q / (p * A)) (𝓝 0) (𝓝 (0 / (p * A))) :=
      (continuous_id.div_const _).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h2 := hcont.tendsto.comp hdiv
    rw [show ((0 : ℝ) ^ (1 / (p - 1)) : ℝ) = 0 from Real.zero_rpow hk.ne'] at h2
    simpa [rvLegTilt, Function.comp_def] using h2
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact rvLegTilt_pos hp hA hq


/-- **The Legendre tilt realizes the constant.**  At `λ = (q/(pA))^{1/(p−1)}` the value of the
tilted functional against the exact power law `A λ^p` is `rvLegConst p A · q^{p/(p−1)}`. -/
theorem rvLegTilt_value {p A q : ℝ} (hp : 1 < p) (hA : 0 < A) (hq : 0 < q) :
    rvLegTilt p A q * q - A * rvLegTilt p A q ^ p = rvLegConst p A * q ^ (p / (p - 1)) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hpA : (0 : ℝ) < p * A := by positivity
  have hc0 : (0 : ℝ) < q / (p * A) := by positivity
  set k : ℝ := 1 / (p - 1) with hkdef
  have hk0 : (0 : ℝ) < k := by rw [hkdef]; positivity
  have hkp : k * (p - 1) = 1 := by rw [hkdef]; field_simp
  have hkp1 : k + 1 = p / (p - 1) := by rw [hkdef]; field_simp; ring
  have hlam : rvLegTilt p A q = (q / (p * A)) ^ k := rfl
  have h1 : ((q / (p * A)) ^ k) ^ p = q / (p * A) * (q / (p * A)) ^ k := by
    rw [← Real.rpow_mul hc0.le]
    have hkpp : k * p = 1 + k := by nlinarith [hkp]
    rw [hkpp, Real.rpow_add hc0, Real.rpow_one]
  have hsplit : (q / (p * A)) ^ k = q ^ k / (p ^ k * A ^ k) := by
    rw [Real.div_rpow hq.le hpA.le, Real.mul_rpow hp0.le hA.le]
  have hconst : rvLegConst p A = (p - 1) * (p ^ k * p)⁻¹ * (A ^ k)⁻¹ := by
    rw [rvLegConst, ← hkp1, ← hkdef]
    rw [show -(k + 1) = -(k + 1) from rfl, Real.rpow_neg hp0.le, Real.rpow_neg hA.le,
      Real.rpow_add hp0, Real.rpow_one]
  have hq1 : q ^ (p / (p - 1)) = q ^ k * q := by
    rw [← hkp1, Real.rpow_add hq, Real.rpow_one]
  have hPk : (0 : ℝ) < p ^ k := Real.rpow_pos_of_pos hp0 _
  have hAk : (0 : ℝ) < A ^ k := Real.rpow_pos_of_pos hA _
  rw [hlam, h1, hsplit, hconst, hq1]
  field_simp


/-- **Young's inequality in the shape the Legendre bound consumes.** -/
theorem young_rvLegConst {p A q lam : ℝ} (hp : 1 < p) (hA : 0 < A) (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) : lam * q ≤ A * lam ^ p + rvLegConst p A * q ^ (p / (p - 1)) := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hpA : (0 : ℝ) < p * A := by positivity
  set s : ℝ := (p * A) ^ (1 / p) with hs
  have hs0 : (0 : ℝ) < s := Real.rpow_pos_of_pos hpA _
  have hconj : Real.HolderConjugate p (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hy := Real.young_inequality (s * lam) (q / s) hconj
  have hab : s * lam * (q / s) = lam * q := by field_simp; ring
  rw [hab] at hy
  have h1 : |s * lam| ^ p / p = A * lam ^ p := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ s * lam), Real.mul_rpow hs0.le hlam]
    have hsp : s ^ p = p * A := by
      rw [hs, ← Real.rpow_mul hpA.le]
      rw [show 1 / p * p = 1 by field_simp]
      exact Real.rpow_one _
    rw [hsp]
    field_simp
  have h2 : |q / s| ^ (p / (p - 1)) / (p / (p - 1))
      = rvLegConst p A * q ^ (p / (p - 1)) := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ q / s)]
    rw [Real.div_rpow hq hs0.le]
    have hsq : s ^ (p / (p - 1)) = (p * A) ^ (1 / (p - 1)) := by
      rw [hs, ← Real.rpow_mul hpA.le]
      congr 1
      field_simp
    rw [hsq, Real.mul_rpow hp0.le hA.le, rvLegConst]
    have hsplit : -(p / (p - 1)) = -(1 / (p - 1)) + -1 := by field_simp; ring
    rw [hsplit, Real.rpow_add hp0, Real.rpow_neg hp0.le, Real.rpow_neg hp0.le,
      Real.rpow_neg hA.le, Real.rpow_one]
    have hPk : (0 : ℝ) < p ^ (1 / (p - 1)) := Real.rpow_pos_of_pos hp0 _
    have hAk : (0 : ℝ) < A ^ (1 / (p - 1)) := Real.rpow_pos_of_pos hA _
    field_simp
    ring
  rw [h1, h2] at hy
  exact hy

/-- **The rate from below**, when the cumulant is eventually dominated by `A' λ^p`. -/
theorem eventually_le_rvRate_pow {α p A' : ℝ} (hα : α < 1) (hp : 1 < p) (hA' : 0 < A')
    (h : ∀ᶠ lam in 𝓝[>] (0 : ℝ), rvCumulant α lam ≤ A' * lam ^ p) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), rvLegConst p A' * q ^ (p / (p - 1)) ≤ rvRate α q := by
  have hpull := (tendsto_rvLegTilt hp hA').eventually h
  have hq1ev : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpull, hq1ev, self_mem_nhdsWithin] with q hcum hq1 hq0
  have hq : 0 < q := hq0
  have hlam0 : 0 < rvLegTilt p A' q := rvLegTilt_pos hp hA' hq
  have hle := le_rvRate hα hq1 hlam0.le
  have hval := rvLegTilt_value hp hA' hq
  linarith

/-- **The rate from above**, when the cumulant eventually dominates `A'' λ^p`. -/
theorem eventually_rvRate_le_pow {α p A'' : ℝ} (hα : α < 1) (hp : 1 < p) (hA'' : 0 < A'')
    (h : ∀ᶠ lam in 𝓝[>] (0 : ℝ), A'' * lam ^ p ≤ rvCumulant α lam) :
    ∀ᶠ q in 𝓝[>] (0 : ℝ), rvRate α q ≤ rvLegConst p A'' * q ^ (p / (p - 1)) := by
  obtain ⟨t, ht, htP⟩ := Filter.eventually_iff_exists_mem.1 h
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp ht
  have hu0 : (0 : ℝ) < u := hu
  set δ : ℝ := u / 2 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hlow : ∀ lam : ℝ, 0 < lam → lam ≤ δ → A'' * lam ^ p ≤ rvCumulant α lam := by
    intro lam hlam0 hlamδ
    exact htP lam (hsub ⟨hlam0, by rw [hδdef] at hlamδ; linarith⟩)
  set m : ℝ := rvCumulant α δ / δ with hm
  have hm0 : 0 < m := div_pos (rvCumulant_pos hα hδ0) hδ0
  have hq1ev : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < min 1 m :=
    (eventually_lt_nhds (lt_min (by norm_num) hm0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hq1ev, self_mem_nhdsWithin] with q hqlt hq0
  have hq : 0 < q := hq0
  have hqm : q < m := lt_of_lt_of_le hqlt (min_le_right _ _)
  have hRHS : (0 : ℝ) ≤ rvLegConst p A'' * q ^ (p / (p - 1)) := by
    have := rvLegConst_pos hp hA''
    have : (0 : ℝ) < q ^ (p / (p - 1)) := Real.rpow_pos_of_pos hq _
    positivity
  refine csSup_le (rvLegendreSet_nonempty α q) ?_
  rintro y ⟨lam, hlam, rfl⟩
  rcases eq_or_lt_of_le hlam with hzero | hpos
  · rw [← hzero, rvCumulant_zero]
    simpa using hRHS
  · rcases le_or_gt lam δ with hle | hgt
    · have hb := hlow lam hpos hle
      have hy := young_rvLegConst (p := p) (A := A'') hp hA'' hq.le hlam
      linarith
    · have hslope := rvCumulant_slope_mono hα hδ0 hgt.le
      have hid : lam / δ * rvCumulant α δ = lam * m := by rw [hm]; field_simp
      rw [hid] at hslope
      have hneg : lam * q - lam * m ≤ 0 := by nlinarith [hpos, hqm]
      linarith

end

end HTGeometry
