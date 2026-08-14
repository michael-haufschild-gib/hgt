import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# Unit-block estimates for exponentially localized kernels

A kernel dominated by `C e^{-μ|x-y|}` acts on the unit-block decomposition of the ray as a discrete
exponential envelope.  On the block `I_m = (m, m+1)` the kernel is at most `C e^{μ} e^{-μ|n-m|}`
whenever the argument lies in `I_n`, and Cauchy--Schwarz on a block of unit measure replaces the
profile by its block `L²` norm.  Hence

`∫_0^∞ K(x,y) Φ(y) dy ≤ C e^{μ} ∑_m e^{-μ|n-m|} ‖Φ‖_{L²(I_m)}`   for `x ∈ I_n`,

which is the block form of the Gamma cutoff-commutator estimate.  Everything is stated in `ℝ≥0∞`,
so no integrability hypothesis appears.
-/

open MeasureTheory Set ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The unit block of the ray. -/
def rayBlock (m : ℕ) : Set ℝ := Ioo (m : ℝ) ((m : ℝ) + 1)

theorem measurableSet_rayBlock (m : ℕ) : MeasurableSet (rayBlock m) := measurableSet_Ioo

theorem volume_rayBlock (m : ℕ) : volume (rayBlock m) = 1 := by
  rw [rayBlock, Real.volume_Ioo]
  simp

/-- The block `L²` norm of a nonnegative profile. -/
noncomputable def blockNorm (Φ : ℝ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  (∫⁻ y in rayBlock m, Φ y ^ 2) ^ ((1 : ℝ) / 2)

/-- On a unit block, the mass is at most the block `L²` norm. -/
theorem lintegral_rayBlock_le_blockNorm {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) (m : ℕ) :
    (∫⁻ y in rayBlock m, Φ y) ≤ blockNorm Φ m := by
  have hconj : Real.HolderConjugate 2 2 := by
    constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (rayBlock m)) hconj
    (f := fun _ => (1 : ℝ≥0∞)) (g := Φ) measurable_const.aemeasurable hΦ.aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow] at h
  have hone : (∫⁻ _ : ℝ in rayBlock m, (1 : ℝ≥0∞)) = 1 := by
    rw [lintegral_const, Measure.restrict_apply_univ, volume_rayBlock, one_mul]
  rw [hone, ENNReal.one_rpow, one_mul] at h
  refine le_trans h (le_of_eq ?_)
  rw [blockNorm]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [← ENNReal.rpow_natCast (Φ y) 2]
  norm_num

/-- The ray is the disjoint union of its unit blocks, up to a null set. -/
theorem lintegral_Ioi_eq_tsum_rayBlock (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in Ioi (0:ℝ), g y) = ∑' m : ℕ, ∫⁻ y in rayBlock m, g y := by
  have hdisj : Pairwise (Function.onFun Disjoint rayBlock) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    have h1 : (i : ℝ) < x := hxi.1
    have h2 : x < (i : ℝ) + 1 := hxi.2
    have h3 : (j : ℝ) < x := hxj.1
    have h4 : x < (j : ℝ) + 1 := hxj.2
    have hij' : i ≠ j := hij
    rcases lt_or_gt_of_ne hij' with h | h
    · have : (i : ℝ) + 1 ≤ (j : ℝ) := by
        have : i + 1 ≤ j := h
        exact_mod_cast this
      linarith
    · have : (j : ℝ) + 1 ≤ (i : ℝ) := by
        have : j + 1 ≤ i := h
        exact_mod_cast this
      linarith
  have hunion : (∫⁻ y in ⋃ m : ℕ, rayBlock m, g y) = ∑' m : ℕ, ∫⁻ y in rayBlock m, g y :=
    lintegral_iUnion measurableSet_rayBlock hdisj g
  have hsub : (⋃ m : ℕ, rayBlock m) ⊆ Ioi (0:ℝ) := by
    intro x hx
    obtain ⟨s, ⟨m, rfl⟩, hxm⟩ := hx
    have h1 : (m : ℝ) < x := hxm.1
    have hm : (0:ℝ) ≤ (m : ℝ) := by positivity
    exact lt_of_le_of_lt hm h1
  have hdiff : Ioi (0:ℝ) \ (⋃ m : ℕ, rayBlock m) ⊆ (fun k : ℕ => (k : ℝ)) '' univ := by
    intro x hx
    obtain ⟨hx0, hxn⟩ := hx
    have hx0' : (0:ℝ) < x := hx0
    refine ⟨⌊x⌋₊, mem_univ _, ?_⟩
    by_contra hne
    refine hxn ?_
    refine Set.mem_iUnion.mpr ⟨⌊x⌋₊, ?_⟩
    refine ⟨lt_of_le_of_ne (Nat.floor_le hx0'.le) ?_, Nat.lt_floor_add_one x⟩
    intro h
    exact hne h
  have hnull : volume (Ioi (0:ℝ) \ (⋃ m : ℕ, rayBlock m)) = 0 := by
    refine measure_mono_null hdiff ?_
    exact Set.Countable.measure_zero (Set.countable_univ.image _) _
  have hae : Ioi (0:ℝ) =ᵐ[volume] ⋃ m : ℕ, rayBlock m := by
    rw [ae_eq_set]
    refine ⟨hnull, ?_⟩
    rw [Set.sdiff_eq_empty.mpr hsub]
    simp
  rw [setLIntegral_congr hae, hunion]

/-- The exponential kernel is almost constant across a pair of unit blocks. -/
theorem exp_kernel_block_le {μ : ℝ} (hμ : 0 ≤ μ) {n m : ℕ} {x y : ℝ}
    (hx : x ∈ rayBlock n) (hy : y ∈ rayBlock m) :
    Real.exp (-μ * |x - y|) ≤ Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|) := by
  have hx1 : (n : ℝ) < x := hx.1
  have hx2 : x < (n : ℝ) + 1 := hx.2
  have hy1 : (m : ℝ) < y := hy.1
  have hy2 : y < (m : ℝ) + 1 := hy.2
  have hdist : |(n : ℝ) - m| - 2 ≤ |x - y| := by
    have h1 : |(n : ℝ) - m| ≤ |x - y| + 2 := by
      have hstep : |(n : ℝ) - m| ≤ |(n : ℝ) - x| + |x - y| + |y - (m : ℝ)| := by
        have h := abs_sub_le (n : ℝ) x y
        have h' := abs_sub_le (n : ℝ) y (m : ℝ)
        calc |(n : ℝ) - m| ≤ |(n : ℝ) - y| + |y - (m : ℝ)| := h'
          _ ≤ |(n : ℝ) - x| + |x - y| + |y - (m : ℝ)| := by linarith [h]
      have hnx : |(n : ℝ) - x| ≤ 1 := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hym : |y - (m : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hstrict : |(n : ℝ) - x| + |y - (m : ℝ)| ≤ 2 := by linarith
      have hxy : (0:ℝ) ≤ |x - y| := abs_nonneg _
      linarith
    linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hdist, hμ]

/-- **The block form of an exponentially localized kernel bound.** -/
theorem lintegral_Ioi_kernel_le_blockEnvelope {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ)
    {K : ℝ → ℝ → ℝ≥0∞} {C μ : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ)
    (hK : ∀ x y, K x y ≤ ENNReal.ofReal (C * Real.exp (-μ * |x - y|)))
    {n : ℕ} {x : ℝ} (hx : x ∈ rayBlock n) :
    (∫⁻ y in Ioi (0:ℝ), K x y * Φ y)
      ≤ ∑' m : ℕ, ENNReal.ofReal (C * Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|))
          * blockNorm Φ m := by
  rw [lintegral_Ioi_eq_tsum_rayBlock]
  refine ENNReal.tsum_le_tsum fun m => ?_
  have hblock : ∀ y ∈ rayBlock m, K x y * Φ y
      ≤ ENNReal.ofReal (C * Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|)) * Φ y := by
    intro y hy
    gcongr
    refine le_trans (hK x y) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hker := exp_kernel_block_le hμ hx hy
    calc C * Real.exp (-μ * |x - y|)
        ≤ C * (Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|)) :=
          mul_le_mul_of_nonneg_left hker hC
      _ = C * Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|) := by ring
  calc (∫⁻ y in rayBlock m, K x y * Φ y)
      ≤ ∫⁻ y in rayBlock m,
          ENNReal.ofReal (C * Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|)) * Φ y :=
        setLIntegral_mono' (measurableSet_rayBlock m) hblock
    _ = ENNReal.ofReal (C * Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|))
          * ∫⁻ y in rayBlock m, Φ y := by
        rw [lintegral_const_mul _ hΦ]
    _ ≤ ENNReal.ofReal (C * Real.exp (2 * μ) * Real.exp (-μ * |(n : ℝ) - m|))
          * blockNorm Φ m := by
        gcongr
        exact lintegral_rayBlock_le_blockNorm hΦ m

end GaloisForLFunctions.HTGeometry
