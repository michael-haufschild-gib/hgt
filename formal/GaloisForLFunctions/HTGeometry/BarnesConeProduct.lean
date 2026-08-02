import GaloisForLFunctions.HTGeometry.ConePeriodSummability
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# The Barnes cone product is entire

The reciprocal Barnes multiple gamma is a Weierstrass product of genus `N` over the period cone:
one elementary factor for every nonzero exponent vector, evaluated at `-z` divided by the cone
value of that vector.

Convergence is exactly the pairing of the two bricks already built.  On a compact set the argument
of every factor is eventually inside the half-disc, where the genus estimate bounds the deviation
of the factor from one by a constant times the inverse `(N+1)`-st power of the cone value; and those
inverse powers are summable over the cone.  Only finitely many exponent vectors are excluded,
because the cone value grows at least linearly in the total degree.

Hence the product converges locally uniformly on the whole plane and its limit is entire.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## The factors -/

/-- One factor of the Barnes cone product: the genus-`N` elementary factor at `-z/w_n`, the zero
exponent vector contributing trivially. -/
def barnesConeFactor (ω : ι → ℂ) (n : ι → ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 1 else weierstrassFactor (Fintype.card ι) (-(z / conePeriod ω n))

/-- The Barnes cone product, the reciprocal multiple gamma up to its linear factor and
normalization. -/
def barnesConeProduct (ω : ι → ℂ) (z : ℂ) : ℂ := ∏' n : ι → ℕ, barnesConeFactor ω n z

theorem differentiable_barnesConeFactor (ω : ι → ℂ) (n : ι → ℕ) :
    Differentiable ℂ (barnesConeFactor ω n) := by
  unfold barnesConeFactor
  split_ifs with h
  · exact differentiable_const 1
  · exact (differentiable_weierstrassFactor (Fintype.card ι)).comp
      ((differentiable_id.div_const (conePeriod ω n)).neg)

theorem barnesConeFactor_sub_one_zero (ω : ι → ℂ) (z : ℂ) :
    barnesConeFactor ω 0 z - 1 = 0 := by
  rw [barnesConeFactor, if_pos rfl, sub_self]

/-! ## Only finitely many small cone values -/

theorem finite_conePeriod_lt (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (R : ℝ) :
    {n : ι → ℕ | ¬ (2 * R ≤ ‖conePeriod ω n‖)}.Finite := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_im ω hω
  set M : ℕ := ⌈2 * R / δ⌉₊ with hM
  refine Set.Finite.subset (Set.Finite.pi fun _ : ι => Set.finite_Iic M) ?_
  intro n hn
  rw [Set.mem_setOf_eq, not_le] at hn
  have hcone : δ * ∑ i, (n i : ℝ) ≤ ‖conePeriod ω n‖ :=
    mul_sum_le_norm_conePeriod ω hδ n
  have hsum : δ * ∑ i, (n i : ℝ) < 2 * R := lt_of_le_of_lt hcone hn
  have hsumle : ∑ i, (n i : ℝ) ≤ 2 * R / δ := by
    rw [le_div_iff₀ hδpos]
    nlinarith
  have hMle : (2 : ℝ) * R / δ ≤ (M : ℝ) := Nat.le_ceil _
  refine Set.mem_univ_pi.mpr fun i => ?_
  rw [Set.mem_Iic]
  have hi : (n i : ℝ) ≤ ∑ k, (n k : ℝ) :=
    Finset.single_le_sum (f := fun k => (n k : ℝ)) (fun k _ => Nat.cast_nonneg _)
      (Finset.mem_univ i)
  have : (n i : ℝ) ≤ (M : ℝ) := le_trans hi (le_trans hsumle hMle)
  exact_mod_cast this

/-! ## Local uniform convergence -/

theorem hasProdLocallyUniformlyOn_barnesConeFactor (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    HasProdLocallyUniformlyOn (barnesConeFactor ω) (barnesConeProduct ω) Set.univ := by
  classical
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨C, hC⟩ := hK.bddAbove_image (continuous_norm (E := ℂ)).continuousOn
  set R : ℝ := max C 0 with hR
  have hRnn : (0 : ℝ) ≤ R := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz =>
    (hC (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
  set N : ℕ := Fintype.card ι with hN
  set A : ℝ := Real.exp (weierstrassLogBound N) * R ^ (N + 1) with hA
  have hAnn : (0 : ℝ) ≤ A := by positivity
  set u : (ι → ℕ) → ℝ := fun n =>
    A * (if n = 0 then 0 else (‖conePeriod ω n‖ ^ (N + 1))⁻¹) with hu
  have husum : Summable u := (summable_conePeriod_inv_pow ω hω).mul_left A
  have hbound : ∀ᶠ n : ι → ℕ in cofinite,
      ∀ z ∈ K, ‖barnesConeFactor ω n z - 1‖ ≤ u n := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (finite_conePeriod_lt ω hω R) ?_
    intro n hn
    rw [Set.mem_setOf_eq]
    intro hcone
    apply hn
    rw [Set.mem_setOf_eq]
    intro z hz
    by_cases h0 : n = 0
    · rw [h0, barnesConeFactor_sub_one_zero, norm_zero, hu]
      simp
    · have hz2 : 2 * ‖z‖ ≤ ‖conePeriod ω n‖ := by
        have := hKR z hz
        linarith
      have hmaj := norm_weierstrassFactor_conePeriod_sub_one_le ω z n hz2
      rw [barnesConeFactor, if_neg h0, hu, if_neg h0, hA]
      refine hmaj.trans ?_
      have hpow : ‖z‖ ^ (N + 1) ≤ R ^ (N + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (hKR z hz) _
      have hinv : (0 : ℝ) ≤ (‖conePeriod ω n‖ ^ (N + 1))⁻¹ := by positivity
      have hexp : (0 : ℝ) ≤ Real.exp (weierstrassLogBound N) := (Real.exp_pos _).le
      calc Real.exp (weierstrassLogBound N) * ‖z‖ ^ (N + 1) *
            (‖conePeriod ω n‖ ^ (N + 1))⁻¹
          ≤ Real.exp (weierstrassLogBound N) * R ^ (N + 1) *
            (‖conePeriod ω n‖ ^ (N + 1))⁻¹ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow hexp) hinv
        _ = Real.exp (weierstrassLogBound N) * R ^ (N + 1) *
            (‖conePeriod ω n‖ ^ (N + 1))⁻¹ := rfl
  have hcont : ∀ n : ι → ℕ, ContinuousOn (fun z => barnesConeFactor ω n z - 1) K :=
    fun n => ((differentiable_barnesConeFactor ω n).continuous.sub continuous_const).continuousOn
  have hprod := Summable.hasProdUniformlyOn_one_add hK husum hbound hcont
  have heq : (fun (n : ι → ℕ) (z : ℂ) => 1 + (barnesConeFactor ω n z - 1)) =
      barnesConeFactor ω := by
    funext n z
    ring
  have heq2 : (fun z : ℂ => ∏' n : ι → ℕ, (1 + (barnesConeFactor ω n z - 1))) =
      barnesConeProduct ω := by
    funext z
    rw [barnesConeProduct]
    exact tprod_congr fun n => by ring
  rwa [heq, heq2] at hprod

/-- **The Barnes cone product is entire.** -/
theorem differentiable_barnesConeProduct (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    Differentiable ℂ (barnesConeProduct ω) := by
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (hasProdLocallyUniformlyOn_barnesConeFactor ω hω)
  have hd : ∀ᶠ S : Finset (ι → ℕ) in atTop,
      DifferentiableOn ℂ (fun z => ∏ n ∈ S, barnesConeFactor ω n z) Set.univ := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun n _ =>
      (differentiable_barnesConeFactor ω n).differentiableOn
  intro z
  simpa only [differentiableWithinAt_univ] using
    ht.differentiableOn hd isOpen_univ z (Set.mem_univ z)

end

end GaloisForLFunctions
