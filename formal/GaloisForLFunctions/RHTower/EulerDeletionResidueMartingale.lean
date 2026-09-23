import GaloisForLFunctions.RHTower.EulerDeletionCoefficientPrefixEnergy
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-!
# Bounded innovations in the physical residue filtration

The probability mass of cell `j` is `1/((j+1)*(j+2))`, exactly the weight
in the discrete Báez--Duarte Gram formula. At stage `n`, the history records
`j mod lcm(1,...,n)`. The literal Möbius residue source splits into its
orthogonal innovations and accumulated conditional means.

The cumulative innovation energy is at most two at every cutoff, and
nonprime signed innovations vanish. The norm of the complete physical
source differs from the norm of its predictable part by at most `sqrt 2`.
This bounds the innovation component; no growth bound for the predictable
part or Riemann hypothesis is asserted.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped BigOperators
namespace RHTower.DeletionResidueMartingale

/-- Original discrete physical cell mass, indexed from zero. -/
def cellWeight (j : ℕ) : ℝ := 1 / (((j : ℝ)+1)*((j : ℝ)+2))

private theorem sum_cellWeight (N : ℕ) :
    (∑ j ∈ range N, cellWeight j) = 1-1/((N : ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,ih]
    unfold cellWeight
    push_cast
    field_simp
    ring

/-- The complete physical cell masses sum to one. -/
theorem hasSum_cellWeight : HasSum cellWeight 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => by unfold cellWeight; positivity) 1).mpr
  simp_rw [sum_cellWeight]
  simpa using tendsto_const_nhds.sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The physical cell weights as a probability mass function. -/
def cellPMF : PMF ℕ := ⟨fun j => ENNReal.ofReal (cellWeight j), by
  have ht : (∑' j, ENNReal.ofReal (cellWeight j)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => by unfold cellWeight; positivity) hasSum_cellWeight.summable,
      hasSum_cellWeight.tsum_eq, ENNReal.ofReal_one]
  exact ht ▸ ENNReal.summable.hasSum⟩

/-- The original physical cell probability measure. -/
abbrev cellMeasure : Measure ℕ := cellPMF.toMeasure

instance : IsProbabilityMeasure cellMeasure := by unfold cellMeasure; infer_instance

/-- Every singleton retains its original physical mass. -/
theorem cellMeasure_singleton (j : ℕ) : cellMeasure.real {j} = cellWeight j := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ENNReal.toReal_ofReal (by unfold cellWeight; positivity)

/-- Exact mass of the entire physical tail. -/
theorem cellMeasure_tail (L : ℕ) : cellMeasure.real {j | L ≤ j} = 1/((L : ℝ)+1) := by
  have h := measureReal_add_measureReal_compl (μ := cellMeasure)
    (s := (range L : Set ℕ)) (Finset.measurableSet _)
  have he : ((range L : Set ℕ)ᶜ) = {j | L ≤ j} := by ext j; simp
  have hh : cellMeasure.real (range L : Set ℕ) = 1-1/((L : ℝ)+1) := by
    rw [measureReal_def, PMF.toMeasure_apply_finset]
    change (∑ j ∈ range L, ENNReal.ofReal (cellWeight j)).toReal = _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by unfold cellWeight; positivity),
      ENNReal.toReal_ofReal (by apply sum_nonneg; intro j hj; unfold cellWeight; positivity),
      sum_cellWeight]
  rw [he,hh,probReal_univ] at h
  linarith

/-- The residue numerator on physical cell `j+1`. -/
def residue (n j : ℕ) : ℝ := (((j+1)%n : ℕ) : ℝ)/(n : ℝ)

/-- All residue numerators lie in the unit interval. -/
theorem residue_bounds (n j : ℕ) : 0 ≤ residue n j ∧ residue n j ≤ 1 := by
  constructor
  · unfold residue; positivity
  · by_cases hn : n = 0
    · subst n; simp [residue]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    rw [residue, div_le_one hn0]
    exact_mod_cast (Nat.mod_lt (j+1) (Nat.pos_of_ne_zero hn)).le

private theorem memLp_bounded {f : ℕ → ℝ} {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    MemLp f 2 cellMeasure :=
  MemLp.of_bound (measurable_from_top.aestronglyMeasurable) C
    (Eventually.of_forall fun j => by simpa only [Real.norm_eq_abs] using hf j)

/-- A residue numerator in the actual physical L2 space. -/
def residueVec (n : ℕ) : Lp ℝ 2 cellMeasure :=
  (memLp_bounded (fun j => by
    rw [abs_of_nonneg (residue_bounds n j).1]
    exact (residue_bounds n j).2)).toLp (residue n)

/-- A residue predictor determined by the cell modulo `L`. -/
def predictorVec (n L : ℕ) : Lp ℝ 2 cellMeasure :=
  (memLp_bounded (fun j => by
    rw [abs_of_nonneg (residue_bounds n (j%L)).1]
    exact (residue_bounds n (j%L)).2)).toLp (fun j => residue n (j%L))

private theorem residueVec_ae (n : ℕ) : residueVec n =ᵐ[cellMeasure] residue n :=
  MemLp.coeFn_toLp _

private theorem predictorVec_ae (n L : ℕ) :
    predictorVec n L =ᵐ[cellMeasure] (fun j => residue n (j%L)) :=
  MemLp.coeFn_toLp _

private theorem norm_sq_integral (v : Lp ℝ 2 cellMeasure) :
    ‖v‖^(2 : ℕ) = ∫ j, v j^(2 : ℕ) ∂cellMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

/-- The predictor agrees before `L`; its squared error costs at most the exact tail mass. -/
theorem residue_prediction_error (n L : ℕ) :
    ‖residueVec n - predictorVec n L‖^(2 : ℕ) ≤ 1/((L : ℝ)+1) := by
  have hmeas : MeasurableSet {j : ℕ | L ≤ j} := (Set.to_countable _).measurableSet
  have hsq : Integrable (fun j => (residueVec n-predictorVec n L) j^(2 : ℕ)) cellMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp
        (Lp.memLp (residueVec n-predictorVec n L))
  calc
    _ = ∫ j, (residueVec n-predictorVec n L) j^(2 : ℕ) ∂cellMeasure := norm_sq_integral _
    _ ≤ ∫ j, ({j : ℕ | L ≤ j} : Set ℕ).indicator (fun _ => (1 : ℝ)) j ∂cellMeasure := by
      apply integral_mono_ae hsq ((integrable_const _).indicator hmeas)
      filter_upwards [Lp.coeFn_sub (residueVec n) (predictorVec n L),
        residueVec_ae n,predictorVec_ae n L] with j hj hr hp
      rw [hj,Pi.sub_apply,hr,hp]
      by_cases h : L ≤ j
      · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_pos h]
        have h1 := residue_bounds n j
        have h2 := residue_bounds n (j%L)
        nlinarith [sq_nonneg (residue n j + residue n (j%L) - 1)]
      · simp only [Set.indicator_apply,Set.mem_setOf_eq,if_neg h,Nat.mod_eq_of_lt (by omega : j < L)]
        simp
    _ = 1/((L : ℝ)+1) := by rw [integral_indicator_const _ hmeas,smul_eq_mul,mul_one,cellMeasure_tail]

/-- The least common multiple of the first `n` positive integers. -/
def clock (n : ℕ) : ℕ := (range n).lcm (fun i => i+1)

/-- Every residue clock is positive, including the empty clock. -/
theorem clock_pos (n : ℕ) : 0 < clock n := by
  apply Nat.pos_of_ne_zero
  rw [clock,Finset.lcm_ne_zero_iff]
  intro i hi
  omega

/-- Every positive integer already processed divides the residue clock. -/
theorem dvd_clock {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : m ∣ clock n := by
  have h := Finset.dvd_lcm (f := fun i : ℕ => i+1) (mem_range.mpr (show m-1 < n by omega))
  simpa only [Nat.sub_add_cancel hm,clock] using h

/-- Later residue clocks refine earlier clocks by divisibility. -/
theorem clock_dvd {m n : ℕ} (hmn : m ≤ n) : clock m ∣ clock n := by
  apply Finset.lcm_dvd
  intro i hi
  exact dvd_clock (by omega) (by have := mem_range.mp hi; omega)

/-- Two consecutive coprime factors give a quadratic lower bound for the clock. -/
theorem consecutive_le_clock (n : ℕ) : (n+1)*(n+2) ≤ clock (n+2) := by
  have hc : Nat.Coprime (n+1) (n+2) := by
    rw [show n+2 = (n+1)+1 by omega]
    simp
  exact Nat.le_of_dvd (clock_pos _) (hc.mul_dvd_of_dvd_of_dvd
    (dvd_clock (by omega) (by omega)) (dvd_clock (by omega) le_rfl))

/-- The sigma-algebra generated by the cell modulo `L`. -/
abbrev residueSigma (L : ℕ) : MeasurableSpace ℕ :=
  MeasurableSpace.comap (fun j : ℕ => j%L) ⊤

/-- Divisibility of moduli gives refinement of their residue sigma-algebras. -/
theorem residueSigma_mono {L K : ℕ} (h : L ∣ K) : residueSigma L ≤ residueSigma K := by
  apply MeasurableSpace.comap_le_comap_of_eq_comp (fun j : ℕ => j%L) measurable_from_top
  funext j
  exact (Nat.mod_mod_of_dvd j h).symm

/-- The closed subspace of physical observables determined by earlier residues. -/
def historySpace (n : ℕ) : Submodule ℝ (Lp ℝ 2 cellMeasure) :=
  lpMeas ℝ ℝ (residueSigma (clock n)) 2 cellMeasure

instance (n : ℕ) : (historySpace n).HasOrthogonalProjection := by
  haveI : Fact (residueSigma (clock n) ≤ (inferInstance : MeasurableSpace ℕ)) := ⟨le_top⟩
  unfold historySpace
  infer_instance

/-- The physical history spaces increase with the arithmetic cutoff. -/
theorem historySpace_mono {m n : ℕ} (h : m ≤ n) : historySpace m ≤ historySpace n := by
  intro f hf
  rw [historySpace,mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  exact hf.mono (residueSigma_mono (clock_dvd h))

/-- The residue predictor belongs to the specified physical history space. -/
theorem predictorVec_mem (n m : ℕ) : predictorVec n (clock m) ∈ historySpace m := by
  rw [historySpace,mem_lpMeas_iff_aestronglyMeasurable]
  have h : Measurable[residueSigma (clock m)] (fun j => residue n (j%clock m)) :=
    (measurable_from_top (f := residue n)).comp
      (comap_measurable (m := (⊤ : MeasurableSpace ℕ)) (fun j : ℕ => j%clock m))
  exact h.aestronglyMeasurable.congr (predictorVec_ae _ _).symm


/-- A residue whose modulus divides the clock is already determined by that history. -/
theorem residueVec_mem_of_dvd {n L : ℕ} (hd : n ∣ clock L) :
    residueVec n ∈ historySpace L := by
  have he : residueVec n = predictorVec n (clock L) := by
    apply Lp.ext
    filter_upwards [residueVec_ae n,predictorVec_ae n (clock L)] with j hj hp
    rw [hj,hp,residue,residue]
    congr 2
    calc
      (j+1)%n = (j%n+1)%n := (Nat.mod_add_mod _ _ _).symm
      _ = ((j%clock L)%n+1)%n := by rw [Nat.mod_mod_of_dvd _ hd]
      _ = (j%clock L+1)%n := Nat.mod_add_mod _ _ _
  rw [he]
  exact predictorVec_mem _ _

/-- Each processed residue is adapted to its own stage. -/
theorem residueVec_mem (n : ℕ) : residueVec (n+1) ∈ historySpace (n+1) :=
  residueVec_mem_of_dvd (dvd_clock (by omega) le_rfl)

/-- The next residue minus its orthogonal projection onto the previous history. -/
def innovation (n : ℕ) : Lp ℝ 2 cellMeasure :=
  residueVec (n+1) - (historySpace n).starProjection (residueVec (n+1))

/-- Each innovation belongs to the next history space. -/
theorem innovation_mem (n : ℕ) : innovation n ∈ historySpace (n+1) := by
  exact Submodule.sub_mem _ (residueVec_mem n)
    (historySpace_mono (by omega) (Submodule.starProjection_apply_mem _ _))

/-- Distinct chronological residue innovations are orthogonal. -/
theorem innovation_orthogonal {i j : ℕ} (h : i < j) :
    inner ℝ (innovation j) (innovation i) = 0 :=
  Submodule.starProjection_inner_eq_zero _ _
    (historySpace_mono (by omega) (innovation_mem i))

/-- Projection minimality bounds the actual innovation by the physical tail mass. -/
theorem innovation_sq_le (n : ℕ) : ‖innovation n‖^(2 : ℕ) ≤ 1/((clock n : ℝ)+1) := by
  have h : ‖innovation n‖ ≤ ‖residueVec (n+1)-predictorVec (n+1) (clock n)‖ := by
    rw [innovation,Submodule.starProjection_minimal]
    change _ ≤ ‖residueVec (n+1) -
      (⟨predictorVec (n+1) (clock n),predictorVec_mem _ _⟩ : historySpace n)‖
    exact ciInf_le ⟨0,Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h |>.trans
    (residue_prediction_error _ _)

/-- The modulus-one residue produces no innovation. -/
theorem innovation_zero : innovation 0 = 0 := by
  have hr : residueVec 1 = 0 := by
    apply Lp.ext
    filter_upwards [residueVec_ae 1,Lp.coeFn_zero ℝ 2 cellMeasure] with j hj hz
    rw [hj,hz]
    simp only [residue,Nat.mod_one,Nat.cast_zero,Nat.cast_one,zero_div,Pi.zero_apply]
  simp [innovation,hr]

/-- A modulus already dividing the clock produces no innovation. -/
theorem innovation_vanishes_of_dvd (n : ℕ) (hd : n+1 ∣ clock n) : innovation n = 0 := by
  rw [innovation,(Submodule.starProjection_eq_self_iff).mpr (residueVec_mem_of_dvd hd),sub_self]

/-- The literal Möbius coefficient times the residue innovation. -/
def signedInnovation (n : ℕ) : Lp ℝ 2 cellMeasure :=
  ((ArithmeticFunction.moebius (n+1) : ℤ) : ℝ) • innovation n

private theorem abs_moebius_real_le_one (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

/-- The actual Möbius innovation obeys the same tail-mass budget. -/
theorem signedInnovation_sq_le (n : ℕ) :
    ‖signedInnovation n‖^(2 : ℕ) ≤ 1/((clock n : ℝ)+1) := by
  have hn : ‖signedInnovation n‖ ≤ ‖innovation n‖ := by
    rw [signedInnovation,norm_smul,Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_moebius_real_le_one _)
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn).trans (innovation_sq_le _)

/-- The cumulative literal signed innovations. -/
def martingalePart (N : ℕ) : Lp ℝ 2 cellMeasure := ∑ i ∈ range N,signedInnovation i

/-- Exact Pythagoras for the complete cumulative innovation. -/
theorem martingalePart_sq (N : ℕ) :
    ‖martingalePart N‖^(2 : ℕ) = ∑ i ∈ range N,‖signedInnovation i‖^(2 : ℕ) := by
  induction N with
  | zero => simp [martingalePart]
  | succ N ih =>
    have ho : inner ℝ (signedInnovation N) (martingalePart N) = 0 := by
      rw [martingalePart,inner_sum]
      apply sum_eq_zero
      intro i hi
      simp only [signedInnovation,real_inner_smul_left,real_inner_smul_right,
        innovation_orthogonal (mem_range.mp hi),mul_zero]
    rw [martingalePart,sum_range_succ]
    change ‖martingalePart N+signedInnovation N‖^(2 : ℕ) = _
    rw [add_comm]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (signedInnovation N) (martingalePart N) ho
    rw [← pow_two,← pow_two,← pow_two,ih] at hp
    rw [sum_range_succ,add_comm (∑ i ∈ range N,‖signedInnovation i‖^(2 : ℕ))]
    exact hp

private theorem sum_consecutive_reciprocal (N : ℕ) :
    (∑ i ∈ range N,1/(((i : ℝ)+1)*((i : ℝ)+2))) = 1-1/((N : ℝ)+1) :=
  sum_cellWeight N

/-- Unconditional cutoff-independent energy bound for the literal innovations. -/
theorem martingalePart_sq_le_two (N : ℕ) : ‖martingalePart N‖^(2 : ℕ) ≤ 2 := by
  rw [martingalePart_sq]
  have ht : ∀ K, (∑ i ∈ range K,‖signedInnovation (i+2)‖^(2 : ℕ)) ≤ 1-1/((K : ℝ)+1) := by
    intro K
    rw [← sum_consecutive_reciprocal]
    apply sum_le_sum
    intro i hi
    apply (signedInnovation_sq_le (i+2)).trans
    apply one_div_le_one_div_of_le (by positivity)
    have hc : ((i : ℝ)+1)*((i : ℝ)+2) ≤ (clock (i+2) : ℝ) := by
      exact_mod_cast consecutive_le_clock i
    linarith
  have h0 : signedInnovation 0 = 0 := by simp [signedInnovation,innovation_zero]
  have h1 : ‖signedInnovation 1‖^(2 : ℕ) ≤ 1 := by
    apply (signedInnovation_sq_le 1).trans
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) (clock 1)]
  rcases N with _ | N
  · simp
  rcases N with _ | K
  · simp [h0]
  · rw [show K+1+1 = 2+K by omega,sum_range_add]
    have hK := ht K
    simp only [sum_range_succ,sum_range_zero,zero_add,h0,norm_zero]
    simp only [Nat.add_comm 2]
    have hx : 0 ≤ 1/((K : ℝ)+1) := by positivity
    linarith


/-- The complete real residue source with the original coefficients. -/
def sourceVec (a : ℕ → ℝ) (N : ℕ) : Lp ℝ 2 cellMeasure :=
  ∑ i ∈ range N,a (i+1) • residueVec (i+1)

private theorem sourceVec_ae (a : ℕ → ℝ) (N : ℕ) :
    sourceVec a N =ᵐ[cellMeasure] (fun j => DeletionCoefficientTransfer.cell a N (j+1)) := by
  induction N with
  | zero =>
    filter_upwards [Lp.coeFn_zero ℝ 2 cellMeasure] with j hj
    simpa only [sourceVec,DeletionCoefficientTransfer.cell,sum_range_zero,Pi.zero_apply] using hj
  | succ N ih =>
    have hs : sourceVec a (N+1) = sourceVec a N + a (N+1) • residueVec (N+1) := by
      simp only [sourceVec,sum_range_succ]
    rw [hs]
    filter_upwards [Lp.coeFn_add (sourceVec a N) (a (N+1) • residueVec (N+1)),
      ih,Lp.coeFn_smul (a (N+1)) (residueVec (N+1)),residueVec_ae (N+1)] with j hj hi hm hr
    rw [hj,Pi.add_apply,hi,hm,Pi.smul_apply,hr]
    simp only [DeletionCoefficientTransfer.cell,sum_range_succ,residue,smul_eq_mul,
      Nat.cast_add,Nat.cast_one,mul_div_assoc]

/-- The discrete probability-space norm equals the complete physical carrier energy. -/
theorem sourceVec_energy (a : ℕ → ℝ) (N : ℕ) :
    ‖sourceVec a N‖^(2 : ℕ) = ‖DeletionCoefficientTransfer.source a N‖^(2 : ℕ) := by
  have hi : Integrable (fun j => (sourceVec a N) j^(2 : ℕ)) cellMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp
        (Lp.memLp (sourceVec a N))
  rw [norm_sq_integral,integral_countable hi]
  calc
    _ = ∑' j,DeletionCoefficientTransfer.cell a N (j+1)^(2 : ℕ)/
        (((j : ℝ)+1)*((j : ℝ)+2)) := by
      apply tsum_congr
      intro j
      have hj : sourceVec a N j = DeletionCoefficientTransfer.cell a N (j+1) := by
        exact (ae_iff_of_countable.mp (sourceVec_ae a N)) j (by
          rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
          change ENNReal.ofReal (cellWeight j) ≠ 0
          exact ne_of_gt (ENNReal.ofReal_pos.mpr (by unfold cellWeight; positivity)))
      rw [cellMeasure_singleton,hj,smul_eq_mul,cellWeight]
      ring
    _ = _ := (DeletionCoefficientTransfer.hasSum_source_energy a N).tsum_eq

/-- Accumulated conditional means of the literal Möbius increments. -/
def predictableDrift (N : ℕ) : Lp ℝ 2 cellMeasure :=
  ∑ i ∈ range N, ((ArithmeticFunction.moebius (i+1) : ℤ) : ℝ) •
    (historySpace i).starProjection (residueVec (i+1))

/-- Exact complete-source decomposition, retaining every conditional mean. -/
theorem source_eq_martingale_add_drift (N : ℕ) :
    sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N =
      martingalePart N + predictableDrift N := by
  rw [sourceVec,martingalePart,predictableDrift,← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  simp only [signedInnovation,innovation,smul_sub]
  abel

/-- All possible unbounded source growth remains in the predictable drift. -/
theorem source_drift_norm_gap (N : ℕ) :
    |‖DeletionCoefficientTransfer.source (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ -
      ‖predictableDrift N‖|^(2 : ℕ) ≤ 2 := by
  have he : ‖DeletionCoefficientTransfer.source
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ =
      ‖sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ := by
    nlinarith [sourceVec_energy (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N,
      norm_nonneg (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N),
      norm_nonneg (DeletionCoefficientTransfer.source
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)]
  rw [he,source_eq_martingale_add_drift]
  have h : |‖martingalePart N+predictableDrift N‖-‖predictableDrift N‖| ≤ ‖martingalePart N‖ := by
    simpa only [add_sub_cancel_right] using
      abs_norm_sub_norm_le (martingalePart N+predictableDrift N) (predictableDrift N)
  exact ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h).trans (martingalePart_sq_le_two N)


/-- Only primes can contribute nonzero signed innovations; composites remain predictable. -/
theorem signedInnovation_eq_zero_of_not_prime (n : ℕ) (hn : ¬ (n+1).Prime) :
    signedInnovation n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [signedInnovation,innovation_zero]
  by_cases hm : ArithmeticFunction.moebius (n+1) = 0
  · simp [signedInnovation,hm]
  have hs : Squarefree (n+1) := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hm
  have hd : n+1 ∣ clock n := by
    rw [← Nat.prod_primeFactors_of_squarefree hs,
      Nat.prod_primeFactors_dvd_iff (clock_pos n).ne']
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hpd := (Nat.mem_primeFactors.mp hp).2.1
    have hpn : p ≤ n+1 := Nat.le_of_dvd (by omega) hpd
    have hpne : p ≠ n+1 := fun he => hn (he ▸ hpp)
    have hc := dvd_clock hpp.one_lt.le (show p ≤ n by omega)
    exact Nat.mem_primeFactors.mpr ⟨hpp,hc,(clock_pos n).ne'⟩
  simp [signedInnovation,innovation_vanishes_of_dvd n hd]

end RHTower.DeletionResidueMartingale
