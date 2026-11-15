import GaloisForLFunctions.TensorPowerProgramme.AnAbelianBaseIsARuler

/-!
# The prime number theorem of the characters gives their independence

In an abelian base the analytic package — for each character `ψ` the series
`F_ψ(s) = Σ_x λ(x) ψ(x) N(x)^{−s}` is, on `Re s > 1`, a function continuous on `Re s ≥ 1` plus
`[ψ = 1]/(s − 1)` — already forces the characters to be linearly independent
(`linearIndependent_of_pnt`). A relation `Σ_j g_j ψ_j = 0`, multiplied by `ψ_i⁻¹`, gives
`Σ_j g_j F_{ψ_j ψ_i⁻¹} = 0` on `Re s > 1`; times `s − 1` as `s ↓ 1` only the trivial character
`ψ_j = ψ_i` survives, with residue `1`, so `g_i = 0`. The pole of the trivial character separates
the characters.

`IsAbelianBase.of_pnt` builds an abelian base from the analytic package alone.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {P C : Type*} [CommGroup C] {N lam : P → ℝ} {ev : C → P → ℂ}

/-- **The prime number theorem of the characters gives their independence.** -/
theorem linearIndependent_of_pnt (one_le_norm : ∀ x, 1 ≤ N x) (lam_nonneg : ∀ x, 0 ≤ lam x)
    (summable_lam : ∀ σ : ℝ, 1 < σ → Summable fun x => lam x * N x ^ (-σ))
    (norm_ev_le : ∀ ψ x, ‖ev ψ x‖ ≤ 1)
    (ev_mul : ∀ ψ ψ' x, ev (ψ * ψ') x = ev ψ x * ev ψ' x)
    (pnt_one : ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      baseLSeries N lam ev 1 s = G s + 1 / (s - 1))
    (pnt_ne : ∀ ψ, ψ ≠ 1 → ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      baseLSeries N lam ev ψ s = G s) :
    LinearIndependent ℂ ev := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  -- the relation, shifted by the inverse of the i-th character
  have hpt : ∀ x, ∑ j ∈ s, g j * ev (j * i⁻¹) x = 0 := by
    intro x
    have h := congrFun hsum x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    calc ∑ j ∈ s, g j * ev (j * i⁻¹) x = (∑ j ∈ s, g j * ev j x) * ev i⁻¹ x := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ev_mul]
          ring
      _ = 0 := by rw [h, zero_mul]
  have hsumm : ∀ (ψ : C) (σ : ℝ), 1 < σ →
      Summable fun x => (lam x : ℂ) * ev ψ x * (N x : ℂ) ^ (-(σ : ℂ)) := by
    intro ψ σ hσ
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
      (summable_lam σ hσ))
    have hN : 0 < N x := by linarith [one_le_norm x]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (lam_nonneg x),
      Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re, Complex.ofReal_re]
    calc lam x * ‖ev ψ x‖ * N x ^ (-σ) ≤ lam x * 1 * N x ^ (-σ) := by
          gcongr
          · exact lam_nonneg x
          · exact norm_ev_le ψ x
      _ = lam x * N x ^ (-σ) := by ring
  -- the shifted series vanish identically on Re s > 1
  have hser : ∀ σ : ℝ, 1 < σ → ∑ j ∈ s, g j * baseLSeries N lam ev (j * i⁻¹) σ = 0 := by
    intro σ hσ
    simp_rw [baseLSeries, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum fun j _ => (hsumm (j * i⁻¹) σ hσ).mul_left (g j)]
    have hz : ∀ x, ∑ j ∈ s, g j * ((lam x : ℂ) * ev (j * i⁻¹) x * (N x : ℂ) ^ (-(σ : ℂ))) = 0 := by
      intro x
      calc ∑ j ∈ s, g j * ((lam x : ℂ) * ev (j * i⁻¹) x * (N x : ℂ) ^ (-(σ : ℂ)))
          = (lam x : ℂ) * (N x : ℂ) ^ (-(σ : ℂ)) * ∑ j ∈ s, g j * ev (j * i⁻¹) x := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = 0 := by rw [hpt x, mul_zero]
    simp only [hz, tsum_zero]
  -- times (σ − 1), each shifted series tends to its residue
  have hterm : ∀ j : C, Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * baseLSeries N lam ev (j * i⁻¹) σ)
      (𝓝[>] 1) (𝓝 (if j * i⁻¹ = 1 then 1 else 0)) := by
    intro j
    have hZ : (0 : ℂ).re ≤ (1 : ℝ) - 1 := by simp
    by_cases hj : j * i⁻¹ = 1
    · obtain ⟨G, hG, hF⟩ := pnt_one
      rw [hj] at *
      have h := tendsto_sub_mul_of_pole hG hF hZ
      simp only [sub_zero, sub_self, Complex.ofReal_zero, if_true] at h
      simpa using h
    · obtain ⟨G, hG, hF⟩ := pnt_ne _ hj
      have hF' : ∀ s : ℂ, 1 < s.re → baseLSeries N lam ev (j * i⁻¹) s = G s + 0 / (s - 1) :=
        fun s hs => by rw [zero_div, add_zero]; exact hF s hs
      have h := tendsto_sub_mul_of_pole hG hF' hZ
      simp only [sub_zero, sub_self, Complex.ofReal_zero, if_true] at h
      rw [if_neg hj]
      exact h
  have hlim := tendsto_finsetSum s fun j _ => (hterm j).const_mul (g j)
  have hval : ∑ j ∈ s, g j * (if j * i⁻¹ = 1 then (1 : ℂ) else 0) = g i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg (fun h => hji (mul_inv_eq_one.mp h)), mul_zero]
    · intro h
      exact absurd hi h
  rw [hval] at hlim
  have hzero : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      ∑ j ∈ s, g j * (((σ - 1 : ℝ) : ℂ) * baseLSeries N lam ev (j * i⁻¹) σ) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have h := hser σ hσ
    calc ∑ j ∈ s, g j * (((σ - 1 : ℝ) : ℂ) * baseLSeries N lam ev (j * i⁻¹) σ)
        = ((σ - 1 : ℝ) : ℂ) * ∑ j ∈ s, g j * baseLSeries N lam ev (j * i⁻¹) σ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by rw [h, mul_zero]
  exact tendsto_nhds_unique (hlim.congr' hzero) tendsto_const_nhds

/-- **An abelian base from the analytic package alone.** -/
theorem IsAbelianBase.of_pnt (one_le_norm : ∀ x, 1 ≤ N x) (lam_nonneg : ∀ x, 0 ≤ lam x)
    (summable_lam : ∀ σ : ℝ, 1 < σ → Summable fun x => lam x * N x ^ (-σ))
    (norm_ev_le : ∀ ψ x, ‖ev ψ x‖ ≤ 1)
    (ev_mul : ∀ ψ ψ' x, ev (ψ * ψ') x = ev ψ x * ev ψ' x)
    (conj_ev : ∀ ψ x, (starRingEnd ℂ) (ev ψ x) = ev ψ⁻¹ x)
    (pnt_one : ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      baseLSeries N lam ev 1 s = G s + 1 / (s - 1))
    (pnt_ne : ∀ ψ, ψ ≠ 1 → ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ ∀ s : ℂ, 1 < s.re →
      baseLSeries N lam ev ψ s = G s) :
    IsAbelianBase N lam ev :=
  ⟨one_le_norm, lam_nonneg, summable_lam, norm_ev_le, ev_mul, conj_ev, pnt_one, pnt_ne,
    linearIndependent_of_pnt one_le_norm lam_nonneg summable_lam norm_ev_le ev_mul pnt_one pnt_ne⟩

end GaloisForLFunctions.TensorPowerProgramme
