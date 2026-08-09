import GaloisForLFunctions.HTGeometry.PolynomialOnePointRecession

/-!
# The polynomial one-point recession is locally uniform

Reparametrising the vertical translate by `u = w⁻¹` turns `q(z + w)/w^d` into a polynomial in the
two variables `(u, z)`,

`polyRecessionAux q d u z = ∑_{m ≤ d} q_m · (z·u + 1)^m · u^{d−m}`,

whose value at `u = 0` is the constant `q_d`.  Joint continuity therefore upgrades the pointwise
recession `poly_scaled_translate_tendsto` to locally uniform convergence, which is the form the
projective-boundary interface demands.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- The two-variable reparametrisation of a scaled vertical translate. -/
def polyRecessionAux (q : Polynomial ℂ) (d : ℕ) (u z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (d + 1), q.coeff m * (z * u + 1) ^ m * u ^ (d - m)

theorem continuous_polyRecessionAux (q : Polynomial ℂ) (d : ℕ) :
    Continuous fun p : ℂ × ℂ => polyRecessionAux q d p.1 p.2 := by
  refine continuous_finset_sum _ fun m _ => ?_
  fun_prop

theorem polyRecessionAux_zero (q : Polynomial ℂ) (d : ℕ) (z : ℂ) :
    polyRecessionAux q d 0 z = q.coeff d := by
  rw [polyRecessionAux, Finset.sum_eq_single d]
  · simp
  · intro m hm hne
    have hpos : d - m ≠ 0 := by
      simp only [Finset.mem_range] at hm
      omega
    simp [zero_pow hpos]
  · intro h
    simp at h

theorem polyRecessionAux_eq (q : Polynomial ℂ) {d : ℕ} (hd : q.natDegree ≤ d) {w : ℂ}
    (hw : w ≠ 0) (z : ℂ) :
    q.eval (z + w) / w ^ d = polyRecessionAux q d w⁻¹ z := by
  rw [Polynomial.eval_eq_sum_range' (by omega : q.natDegree < d + 1), Finset.sum_div,
    polyRecessionAux]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  have hmd : m ≤ d := by omega
  have hsplit : w ^ d = w ^ m * w ^ (d - m) := by
    rw [← pow_add]
    congr 1
    omega
  have hz : z * w⁻¹ + 1 = (z + w) / w := by
    field_simp
  rw [hz, div_pow, hsplit, inv_pow]
  field_simp

/-! ## Locally uniform convergence in a continuous parameter -/

theorem tendstoLocallyUniformly_of_continuous_param {ι : Type*} {l : Filter ι}
    (G : ℂ × ℂ → ℂ) (hG : Continuous G) {u : ι → ℂ} (hu : Tendsto u l (𝓝 0)) :
    TendstoLocallyUniformly (fun i z => G (u i, z)) (fun z => G (0, z)) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcont : Continuous (Function.uncurry fun (w : ℂ) (z : K) => G (w, (z : ℂ))) := by
    refine hG.comp ?_
    exact (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hbase : TendstoUniformly (fun (w : ℂ) (z : K) => G (w, (z : ℂ)))
      (fun z : K => G (0, (z : ℂ))) (𝓝 0) :=
    Continuous.tendstoUniformly _ hcont 0
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  intro v hv
  exact hu.eventually (hbase v hv)

/-! ## The recession is locally uniform -/

theorem tendsto_inv_I_mul_ofReal_atTop :
    Tendsto (fun T : ℝ => (Complex.I * (T : ℂ))⁻¹) atTop (𝓝 0) := by
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [eventually_gt_atTop (max 1 ε⁻¹)] with T hT
  have hT1 : (1 : ℝ) < T := lt_of_le_of_lt (le_max_left _ _) hT
  have hTpos : (0 : ℝ) < T := lt_trans zero_lt_one hT1
  have hnorm : ‖(Complex.I * (T : ℂ))⁻¹‖ = T⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hTpos]
  rw [hnorm]
  have hinv : ε⁻¹ < T := lt_of_le_of_lt (le_max_right _ _) hT
  rw [inv_lt_comm₀ hTpos hε]
  exact hinv

/-- **The one-point recession of a polynomial is locally uniform.**  For `deg q ≤ d`,
`q(z + iT)/(iT)^d → q_d` locally uniformly in `z` as `T → ∞`. -/
theorem poly_scaled_translate_tendstoLocallyUniformly (q : Polynomial ℂ) {d : ℕ}
    (hd : q.natDegree ≤ d) :
    TendstoLocallyUniformly
      (fun (T : ℝ) (z : ℂ) => q.eval (z + Complex.I * (T : ℂ)) / (Complex.I * (T : ℂ)) ^ d)
      (fun _ : ℂ => q.coeff d) atTop := by
  have hparam := tendstoLocallyUniformly_of_continuous_param
    (fun p : ℂ × ℂ => polyRecessionAux q d p.1 p.2) (continuous_polyRecessionAux q d)
    tendsto_inv_I_mul_ofReal_atTop
  have hlim : (fun z : ℂ => polyRecessionAux q d 0 z) = fun _ : ℂ => q.coeff d := by
    funext z
    exact polyRecessionAux_zero q d z
  rw [hlim] at hparam
  refine hparam.congr ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT z
  have hTne : (T : ℂ) ≠ 0 := by
    simpa using ne_of_gt hT
  have hw : Complex.I * (T : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hTne
  exact (polyRecessionAux_eq q hd hw z).symm

end

end GaloisForLFunctions.HTGeometry
