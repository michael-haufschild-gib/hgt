import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheProperPowerMassOnADilatedGcdOctave

/-!
# Proper prime powers at a finite cofactor ratio

For X/M tending to a finite λ the floor multiplicities survive at
leading order. Transposition leaves finitely many Chebyshev intervals.
Their square-root masses give a continuous piecewise affine function
of √λ, including the one-sided transitions at integer ratios.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private abbrev body (x : ℝ) := Chebyshev.psi x-Chebyshev.theta x
private def edge (M X j : ℕ) : ℝ := max (M:ℝ) (min (2*(M:ℝ)) ((X:ℝ)/j))
/-- Relative upper endpoint selected by the j-th cofactor. -/
def properHorizonClip (t : ℝ) (j : ℕ) := max 1 (min 2 (t/j))

/-- The finite-horizon proper-power coefficient at dilation λ. -/
def properHorizonProfile (t : ℝ) :=
  ∑ j ∈ Ioc 0 ⌊t⌋₊, (Real.sqrt (properHorizonClip t j)-1)

theorem proper_horizon_profile_with_cap {t : ℝ} {K : ℕ} (hk : ⌊t⌋₊ ≤ K) :
    properHorizonProfile t = ∑ j ∈ Ioc 0 K, (Real.sqrt (properHorizonClip t j)-1) := by
  apply sum_subset_zero_on_sdiff (Ioc_subset_Ioc_right hk)
  · intro j hj
    obtain ⟨hK,hout⟩ := mem_sdiff.mp hj
    have jp := (mem_Ioc.mp hK).1
    have high : ⌊t⌋₊<j := lt_of_not_ge fun h => hout (mem_Ioc.mpr ⟨jp,h⟩)
    have htj : t<(j:ℝ) := (Nat.floor_lt' jp.ne').mp high
    have hc : properHorizonClip t j=1 := max_eq_left ((min_le_right _ _).trans
      ((div_le_one (Nat.cast_pos.mpr jp)).mpr htj.le))
    rw [hc,Real.sqrt_one,sub_self]
  · intro _ _; rfl

private theorem floor_prefix (x : ℝ) : properOctavePrefix ⌊x⌋₊=body x := by
  rw [proper_octave_prefix_eq]
  simp only [body,Chebyshev.psi,Chebyshev.theta,Nat.floor_natCast]

private theorem price_transposed {M X K : ℕ} (hm : 0<M) (hK : X≤K*M) :
    properGcdOctavePrice M X = ∑ j ∈ Ioc 0 K, (body (edge M X j)-body M) := by
  have row (d : ℕ) (hd : d∈Ioc M (2*M)) :
      ((X/d:ℕ):ℝ)*properOctaveWeight d =
      ∑ j ∈ Ioc 0 K, if j*d≤X then properOctaveWeight d else 0 := by
    have hMd := (mem_Ioc.mp hd).1
    have hp := hm.trans hMd
    have hcap : X/d≤K := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr
      (hK.trans_lt (by rw [Nat.succ_mul]; have := Nat.mul_le_mul_left K hMd.le; omega)))
    have hset : (Ioc 0 K).filter (fun j => j*d≤X) = Ioc 0 (X/d) := by
      ext j; simp only [mem_filter,mem_Ioc,←Nat.le_div_iff_mul_le hp]; omega
    rw [←sum_filter,hset,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
  rw [proper_gcd_as_floor_sum _ _ hm,sum_congr rfl row,sum_comm]
  apply sum_congr rfl
  intro j hj
  have jp := (mem_Ioc.mp hj).1
  have ej : (M:ℝ) ≤ edge M X j := le_max_left _ _
  have e0 := (Nat.cast_nonneg M).trans ej
  have hMe := (Nat.le_floor_iff e0).mpr ej
  have sets : (Ioc M (2*M)).filter (fun d => j*d≤X) = Ioc M ⌊edge M X j⌋₊ := by
    ext d
    simp only [mem_filter,mem_Ioc,Nat.le_floor_iff e0,edge,le_max_iff,le_min_iff,
      le_div_iff₀ (Nat.cast_pos.mpr jp : 0<(j:ℝ))]
    have hm' : (d:ℝ)≤M ↔ d≤M := Nat.cast_le
    have h2 : (d:ℝ)≤2*M ↔ d≤2*M := by exact_mod_cast Iff.rfl
    have hmul : (d:ℝ)*j≤X ↔ j*d≤X := by rw [mul_comm]; exact_mod_cast Iff.rfl
    rw [hm',h2,hmul]; omega
  have hset : Icc 1 ⌊edge M X j⌋₊ \ Icc 1 M = Ioc M ⌊edge M X j⌋₊ := by
    ext d; simp only [mem_sdiff,mem_Icc,mem_Ioc]; omega
  rw [←sum_filter,sets,←hset,sum_sdiff_eq_sub (Icc_subset_Icc_right hMe),←floor_prefix,←proper_octave_prefix_eq]

private theorem edge_factor {M : ℕ} (hm : 0<M) (X j : ℕ) :
    edge M X j = (M:ℝ)*properHorizonClip ((X:ℝ)/M) j := by
  rw [edge,properHorizonClip,mul_max_of_nonneg _ _ (Nat.cast_nonneg M),mul_min_of_nonneg _ _ (Nat.cast_nonneg M),mul_one]
  congr 2
  · ring
  · rw [←mul_div_assoc,mul_div_cancel₀ _ (Nat.cast_pos.mpr hm : 0<(M:ℝ)).ne']

/-- At every finite nonnegative cofactor ratio, independently moving
integer endpoints converge to the same explicit proper-power profile. -/
theorem proper_gcd_finite_ratio {ι : Type*} {l : Filter ι} {M X : ι → ℕ} {t : ℝ}
    (ht : 0≤t) (hm : Tendsto M l atTop) (hr : Tendsto (fun i => (X i:ℝ)/(M i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => properGcdOctavePrice (M i) (X i)/Real.sqrt (M i)) l (𝓝 (properHorizonProfile t)) := by
  let K := ⌊t⌋₊+1
  have tk : t < (K:ℝ) := by simpa only [K,Nat.cast_succ] using Nat.lt_floor_add_one t
  rw [proper_horizon_profile_with_cap (Nat.le_succ ⌊t⌋₊)]
  have mr := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hm
  have base := proper_chebyshev_square_root_density.comp mr
  have row (j : ℕ) (_ : j∈Ioc 0 K) :
      Tendsto (fun i => (body (edge (M i) (X i) j)-body (M i))/Real.sqrt (M i))
        l (𝓝 (Real.sqrt (properHorizonClip t j)-1)) := by
    have c : Continuous (fun x => properHorizonClip x j) := by unfold properHorizonClip; fun_prop
    have hclip := c.continuousAt.tendsto.comp hr
    have hedge : Tendsto (fun i => edge (M i) (X i) j) l atTop :=
      tendsto_atTop_mono (fun i => le_max_left _ _) mr
    have hf := (proper_chebyshev_square_root_density.comp hedge).mul hclip.sqrt
    rw [one_mul] at hf
    apply (hf.sub base).congr'
    filter_upwards [hm.eventually_ge_atTop 1] with i hp
    have mrp := (Nat.cast_pos (α:=ℝ)).mpr hp
    have cr : 0<properHorizonClip ((X i:ℝ)/(M i)) j := zero_lt_one.trans_le (le_max_left _ _)
    change body _ /Real.sqrt _ * Real.sqrt (properHorizonClip _ j) - body _/Real.sqrt _ = _
    rw [edge_factor hp,Real.sqrt_mul mrp.le]
    field_simp [(Real.sqrt_pos.mpr mrp).ne',(Real.sqrt_pos.mpr cr).ne']
    <;> ring
  have hsum := tendsto_finsetSum (Ioc 0 K) row
  apply hsum.congr'
  filter_upwards [hm.eventually_ge_atTop 1,hr.eventually_lt_const tk] with i hp hcap
  have cap : X i ≤ K*M i := by
    exact_mod_cast ((div_lt_iff₀ (Nat.cast_pos.mpr hp : 0<(M i:ℝ))).mp hcap).le
  rw [price_transposed hp cap,sum_div]

#print axioms proper_gcd_finite_ratio
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
