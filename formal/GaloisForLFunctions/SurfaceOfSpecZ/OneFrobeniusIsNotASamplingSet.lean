import GaloisForLFunctions.SurfaceOfSpecZ.TwoFrobeniiFromBothSides

/-!
# One Frobenius is not a sampling set

The degrees `pᵃ` of one prime, weighted by `n`, have the series
`Σ_a (pᵃ)^{1−s} = (1 − p^{1−s})⁻¹` (`wSeries_geomWeight`), invariant under `s ↦ s + 2πi/log p`. So
the twisted series at `c = 2πi/log p` equals the untwisted one and its ratio to `Σ w(n) n^{−σ}` is
`1`, not `0` (`not_samplingWeight_geomWeight`): one Frobenius resonates with the heights
`2πm/log p`, which is the aliasing of `TheGeometricDegreesAlias`. Two Frobenii cannot resonate
together and sample (`TwoFrobeniiSuffice`): a monoid of prime degrees samples once its rank is two.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

variable {p : ℕ}

open Classical in
/-- The degrees `pᵃ` weighted by `n`, at `n = j + 1`. -/
def geomWeight (p : ℕ) (j : ℕ) : ℝ := if ∃ a : ℕ, j + 1 = p ^ a then (j : ℝ) + 1 else 0

theorem geomWeight_nonneg (j : ℕ) : 0 ≤ geomWeight p j := by
  unfold geomWeight; split_ifs <;> positivity

theorem geomIndex_add_one (hp : p.Prime) (a : ℕ) : p ^ a - 1 + 1 = p ^ a :=
  Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero))

theorem geomIndex_injective (hp : p.Prime) : Function.Injective fun a : ℕ => p ^ a - 1 := by
  intro a b h
  have h' : p ^ a = p ^ b := by
    have := congrArg (· + 1) h
    simpa only [geomIndex_add_one hp] using this
  exact Nat.pow_right_injective hp.two_le h'

theorem support_geomSeries_subset (s : ℂ) :
    Function.support (fun j : ℕ => (geomWeight p j : ℂ) * ((j : ℂ) + 1) ^ (-s)) ⊆
      Set.range fun a : ℕ => p ^ a - 1 := by
  intro j hj
  have hw : geomWeight p j ≠ 0 := fun h0 => hj (by simp [h0])
  unfold geomWeight at hw
  split_ifs at hw with h
  · obtain ⟨a, ha⟩ := h
    exact ⟨a, show p ^ a - 1 = j by rw [← ha, Nat.add_sub_cancel]⟩
  · exact absurd rfl hw

/-- The term of `pᵃ` is `(p^{1−s})ᵃ`. -/
theorem geomTerm_eq (hp : p.Prime) (a : ℕ) (s : ℂ) :
    ((geomWeight p (p ^ a - 1) : ℝ) : ℂ) * (((p ^ a - 1 : ℕ) : ℂ) + 1) ^ (-s) =
      cexp ((Real.log p : ℂ) * (1 - s)) ^ a := by
  have hpos : (0 : ℝ) < ((p ^ a - 1 : ℕ) : ℝ) + 1 := by positivity
  have hw : ((geomWeight p (p ^ a - 1) : ℝ) : ℂ) =
      cexp ((Real.log (((p ^ a - 1 : ℕ) : ℝ) + 1) : ℝ) : ℂ) := by
    unfold geomWeight
    rw [if_pos ⟨a, geomIndex_add_one hp a⟩, ← Complex.ofReal_exp, Real.exp_log hpos]
  have hlog : Real.log (((p ^ a - 1 : ℕ) : ℝ) + 1) = a * Real.log p := by
    rw [show (((p ^ a - 1 : ℕ) : ℝ) + 1) = (p : ℝ) ^ a by exact_mod_cast geomIndex_add_one hp a,
      Real.log_pow]
  rw [hw, natCast_add_one_cpow_eq, ← Complex.exp_add, ← Complex.exp_nat_mul, hlog]
  congr 1
  push_cast
  ring

/-- **The series of the degrees of one prime.** -/
theorem wSeries_geomWeight (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    wSeries (geomWeight p) s = (1 - cexp ((Real.log p : ℂ) * (1 - s)))⁻¹ := by
  have hX := norm_cexp_log_mul_one_sub_lt hp hs
  rw [← tsum_geometric_of_norm_lt_one hX, wSeries,
    ← (geomIndex_injective hp).tsum_eq (support_geomSeries_subset s)]
  exact tsum_congr fun a => geomTerm_eq hp a s

/-- **One Frobenius is not a sampling set.** -/
theorem not_samplingWeight_geomWeight (hp : p.Prime) : ¬ SamplingWeight (geomWeight p) := by
  intro hw
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  set c : ℂ := ((2 * Real.pi / Real.log p : ℝ) : ℂ) * I with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    refine mul_ne_zero ?_ I_ne_zero
    exact_mod_cast (div_pos Real.two_pi_pos hlp).ne'
  have hre : 0 ≤ c.re := by
    rw [hcdef, Complex.re_ofReal_mul, Complex.I_re, mul_zero]
  have hres : cexp (-(Real.log p : ℂ) * c) = 1 := by
    have hkey : -(Real.log p : ℂ) * c = ((-1 : ℤ) : ℂ) * (2 * Real.pi * I) := by
      have hL : (Real.log p : ℝ) ≠ 0 := hlp.ne'
      have h1 : (Real.log p : ℝ) * (2 * Real.pi / Real.log p) = 2 * Real.pi := by
        field_simp
      have h2 : ((Real.log p : ℝ) : ℂ) * ((2 * Real.pi / Real.log p : ℝ) : ℂ) =
          ((2 * Real.pi : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, h1]
      rw [hcdef]
      push_cast at h2 ⊢
      linear_combination -I * h2
    rw [hkey]
    exact Complex.exp_int_mul_two_pi_mul_I (-1)
  have hlim := hw.tendsto_off c hc hre
  -- the twisted ratio is identically `1`
  have hone : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      wSeries (geomWeight p) ((σ : ℂ) + c) / (wSum (geomWeight p) σ : ℂ) = 1 := by
    filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hV
    have hσ1 : 1 < σ := hσ
    have hs : 1 < ((σ : ℂ) + c).re := by simp; linarith
    rw [ofReal_wSum, wSeries_geomWeight hp hs, wSeries_geomWeight hp (by simpa using hσ1)]
    have hXc : cexp ((Real.log p : ℂ) * (1 - ((σ : ℂ) + c))) =
        cexp ((Real.log p : ℂ) * (1 - (σ : ℂ))) * cexp (-(Real.log p : ℂ) * c) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [hXc, hres, mul_one]
    have hne : (1 - cexp ((Real.log p : ℂ) * (1 - (σ : ℂ))))⁻¹ ≠ 0 := by
      refine inv_ne_zero fun h0 => ?_
      have := norm_cexp_log_mul_one_sub_lt hp (s := (σ : ℂ)) (by simpa using hσ1)
      rw [show cexp ((Real.log p : ℂ) * (1 - (σ : ℂ))) = 1 by linear_combination -h0] at this
      simp at this
    exact div_self hne
  have h1 := tendsto_const_nhds.congr' (hone.mono fun σ h => h.symm)
  exact one_ne_zero (tendsto_nhds_unique h1 hlim)

end GaloisForLFunctions.SurfaceOfSpecZ
