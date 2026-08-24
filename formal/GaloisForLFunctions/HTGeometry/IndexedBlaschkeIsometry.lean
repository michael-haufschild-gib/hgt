import GaloisForLFunctions.HTGeometry.ScheffeCounting
import GaloisForLFunctions.HTGeometry.IndexedBlaschkeMultiplier
import GaloisForLFunctions.HTGeometry.GeneralizedSchurKernelRankProfile
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne
import GaloisForLFunctions.HTGeometry.StrongConvergenceDense

/-!
# Indexed Blaschke products are Hardy isometries

Finite phase-normalized Blaschke prefixes act isometrically on `H²(D)`.  The Blaschke condition
makes their complementary products converge to `1` in `H²`; exact prefix--tail factorization and
density of analytic polynomials then give strong convergence of the prefix multipliers.  Hence the
full indexed product is an isometric Hardy multiplier, for an arbitrary divisor index type.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem tendsto_tsum_compl_atTop_zero
    {ι : Type*} {f : ι → ℝ} (hf : Summable f) (hf0 : ∀ i, 0 ≤ f i) :
    Tendsto (fun s : Finset ι => ∑' i : ↑((↑s : Set ι)ᶜ), f i) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ := exists_finset_tsum_compl_lt hf.hasSum hε
  filter_upwards [eventually_ge_atTop F] with s hFs
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ => hf0 _)]
  have hsplitF := hf.sum_add_tsum_compl (s := F)
  have hsplits := hf.sum_add_tsum_compl (s := s)
  have hhead : ∑ i ∈ F, f i ≤ ∑ i ∈ s, f i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hFs (fun i _ _ => hf0 i)
  linarith

/-- One phase-normalized Blaschke factor as a contractive disk multiplier. -/
def normalizedBlaschkeMultiplier (a : ℂ) (ha : ‖a‖ < 1) : DiskMultiplier where
  fn := normalizedBlaschkeFactor a
  diff := differentiableOn_normalizedBlaschkeFactor ha
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => norm_normalizedBlaschkeFactor_le_one ha <| by
    exact (mem_ball_zero_iff.mp hz).le

private def normalizedBlaschkePhase (a : ℂ) : ℂ :=
  if a = 0 then 1 else -((‖a‖ : ℂ) / a)

private theorem norm_normalizedBlaschkePhase (a : ℂ) :
    ‖normalizedBlaschkePhase a‖ = 1 := by
  by_cases ha0 : a = 0
  · simp [normalizedBlaschkePhase, ha0]
  · rw [normalizedBlaschkePhase, if_neg ha0, norm_neg, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a),
      div_self (norm_ne_zero_iff.mpr ha0)]

private theorem normalizedBlaschkeFactor_eq_phase_mul (a z : ℂ) :
    normalizedBlaschkeFactor a z =
      normalizedBlaschkePhase a * blaschkeFactor a z := by
  by_cases ha0 : a = 0
  · simp [normalizedBlaschkeFactor, normalizedBlaschkePhase, ha0, blaschkeFactor]
  · simp [normalizedBlaschkeFactor, normalizedBlaschkePhase, ha0]

/-- Multiplication by one phase-normalized Blaschke factor preserves the Hardy norm. -/
theorem norm_hardyMul_normalizedBlaschkeMultiplier
    (a : ℂ) (ha : ‖a‖ < 1) (x : HardyDisk) :
    ‖hardyMul (normalizedBlaschkeMultiplier a ha) x‖ = ‖x‖ := by
  have heq : hardyMul (normalizedBlaschkeMultiplier a ha) x =
      normalizedBlaschkePhase a • hardyMul (singleBlaschke ha).toMultiplier x := by
    refine hardyDisk_ext fun z hz => ?_
    rw [hardyFun_hardyMul _ _ hz, hardyFun_smul _ _ hz,
      hardyFun_hardyMul _ _ hz]
    simp only [normalizedBlaschkeMultiplier, FiniteBlaschke.toMultiplier,
      singleBlaschke_fn]
    rw [normalizedBlaschkeFactor_eq_phase_mul]
    ring
  rw [heq, norm_smul, norm_normalizedBlaschkePhase, one_mul, norm_hardyMul_blaschke]

/-- Finite phase-normalized prefix of an indexed Blaschke product. -/
def indexedBlaschkePrefixMultiplier
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1) (s : Finset ι) :
    DiskMultiplier where
  fn := fun z => ∏ i ∈ s, normalizedBlaschkeFactor (a i) z
  diff := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i t hit iht =>
        simp only [Finset.prod_insert hit]
        exact (differentiableOn_normalizedBlaschkeFactor (haDisk i)).mul iht
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ =>
      norm_normalizedBlaschkeFactor_le_one (haDisk i) <| (mem_ball_zero_iff.mp hz).le

/-- Every finite phase-normalized indexed prefix acts isometrically on `H²(D)`. -/
theorem norm_hardyMul_indexedBlaschkePrefixMultiplier
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (s : Finset ι) (x : HardyDisk) :
    ‖hardyMul (indexedBlaschkePrefixMultiplier a haDisk s) x‖ = ‖x‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have heq : hardyMul (indexedBlaschkePrefixMultiplier a haDisk ∅) x = x := by
        calc
          hardyMul (indexedBlaschkePrefixMultiplier a haDisk ∅) x =
              hardyMul DiskMultiplier.one x := by
            apply hardyMul_congr
            intro z _
            simp [indexedBlaschkePrefixMultiplier, DiskMultiplier.one]
          _ = x := hardyMul_one x
      rw [heq]
  | @insert i s his ih =>
      have heq : hardyMul (indexedBlaschkePrefixMultiplier a haDisk (insert i s)) x =
          hardyMul (normalizedBlaschkeMultiplier (a i) (haDisk i))
            (hardyMul (indexedBlaschkePrefixMultiplier a haDisk s) x) := by
        refine hardyDisk_ext fun z hz => ?_
        rw [hardyFun_hardyMul _ _ hz, hardyFun_hardyMul _ _ hz,
          hardyFun_hardyMul _ _ hz]
        simp only [indexedBlaschkePrefixMultiplier, normalizedBlaschkeMultiplier,
          Finset.prod_insert his]
        ring
      rw [heq, norm_hardyMul_normalizedBlaschkeMultiplier, ih]

private def indexedBlaschkeTailMultiplier
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) (s : Finset ι) : DiskMultiplier :=
  indexedBlaschkeMultiplier
    (fun i : ↑((↑s : Set ι)ᶜ) => a i)
    (fun i => haDisk i)
    (hsum.subtype fun i => i ∈ (↑s : Set ι)ᶜ)

private theorem indexedBlaschkeProduct_split
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) (s : Finset ι)
    {z : ℂ} (hz : ‖z‖ < 1) :
    indexedBlaschkeProduct a z =
      (∏ i ∈ s, normalizedBlaschkeFactor (a i) z) *
        indexedBlaschkeProduct (fun i : ↑((↑s : Set ι)ᶜ) => a i) z := by
  classical
  let f : ι → ℂ := fun i => normalizedBlaschkeFactor (a i) z
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hfull : HasProd f (indexedBlaschkeProduct a z) :=
    (indexedBlaschkeProduct_hasProdLocallyUniformlyOn a haDisk hsum).hasProd hzmem
  have hfin : HasProd (fun i : ↑(↑s : Set ι) => f i)
      (∏ i ∈ s, normalizedBlaschkeFactor (a i) z) := by
    have h := hasProd_fintype (fun i : ↑(↑s : Set ι) => f i)
    have hval : (∏ i : ↑(↑s : Set ι), f i) = ∏ i ∈ s, f i :=
      Finset.prod_coe_sort s f
    rw [hval] at h
    exact h
  have htail : HasProd
      (f ∘ fun i : ↑((↑s : Set ι)ᶜ) => (i : ι))
      (indexedBlaschkeProduct (fun i : ↑((↑s : Set ι)ᶜ) => a i) z) := by
    have h := (indexedBlaschkeProduct_hasProdLocallyUniformlyOn
      (fun i : ↑((↑s : Set ι)ᶜ) => a i)
      (fun i => haDisk i)
      (hsum.subtype fun i => i ∈ (↑s : Set ι)ᶜ)).hasProd hzmem
    exact h
  exact hfull.unique (HasProd.mul_compl hfin htail)

private theorem hardyMul_indexedBlaschke_eq_prefix_tail
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) (s : Finset ι) (x : HardyDisk) :
    hardyMul (indexedBlaschkeMultiplier a haDisk hsum) x =
      hardyMul (indexedBlaschkePrefixMultiplier a haDisk s)
        (hardyMul (indexedBlaschkeTailMultiplier a haDisk hsum s) x) := by
  refine hardyDisk_ext fun z hz => ?_
  rw [hardyFun_hardyMul _ _ hz, hardyFun_hardyMul _ _ hz,
    hardyFun_hardyMul _ _ hz]
  change indexedBlaschkeProduct a z * hardyFun x z =
    (∏ i ∈ s, normalizedBlaschkeFactor (a i) z) *
      (indexedBlaschkeProduct (fun i : ↑((↑s : Set ι)ᶜ) => a i) z * hardyFun x z)
  rw [indexedBlaschkeProduct_split a haDisk hsum s hz]
  ring

private theorem normalizedBlaschkeFactor_zero (a : ℂ) :
    normalizedBlaschkeFactor a 0 = (‖a‖ : ℂ) := by
  by_cases ha0 : a = 0
  · simp [normalizedBlaschkeFactor, ha0]
  · rw [normalizedBlaschkeFactor, if_neg ha0, blaschkeFactor]
    field_simp [ha0]
    ring

private theorem norm_hardyOne : ‖hardyOne‖ = 1 := by
  simp [hardyOne]

private theorem inner_hardyOne (x : HardyDisk) :
    inner ℂ hardyOne x = hardyFun x 0 := by
  let h0 : ‖(0 : ℂ)‖ < 1 := by norm_num
  have hk : hardyKernel h0 = hardyOne := by
    apply lp.ext
    funext n
    change (starRingEnd ℂ 0) ^ n = ((Pi.single 0 (1 : ℂ) : ℕ → ℂ) n)
    by_cases hn : n = 0
    · subst n
      simp
    · simp [hn]
  rw [← hk, inner_hardyKernel]

private def blaschkeTailMass
    {ι : Type*} (a : ι → ℂ) (s : Finset ι) : ℝ :=
  tsum (fun i : ↑((↑s : Set ι)ᶜ) => 1 - ‖a (i : ι)‖)

private theorem tendsto_blaschkeTailMass
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) :
    Tendsto (blaschkeTailMass a) atTop (nhds 0) := by
  change Tendsto (fun s : Finset ι =>
    tsum (fun i : ↑((↑s : Set ι)ᶜ) => 1 - ‖a (i : ι)‖)) atTop (nhds 0)
  exact tendsto_tsum_compl_atTop_zero hsum fun i =>
    sub_nonneg.mpr (haDisk i).le

private theorem tail_hardyOne_sub_norm_sq_le
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) (s : Finset ι) :
    ‖hardyOf (indexedBlaschkeTailMultiplier a haDisk hsum s) - hardyOne‖ ^ 2 ≤
      2 * (Real.exp (blaschkeTailMass a s) - 1) := by
  let J := ↑((↑s : Set ι)ᶜ)
  let b : J → ℂ := fun i => a i
  let T := indexedBlaschkeTailMultiplier a haDisk hsum s
  let q : HardyDisk := hardyOf T
  have hdev (i : J) : ‖normalizedBlaschkeFactor (b i) 0 - 1‖ = 1 - ‖b i‖ := by
    rw [normalizedBlaschkeFactor_zero]
    rw [show (‖b i‖ : ℂ) - 1 = ((‖b i‖ - 1 : ℝ) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr (haDisk i).le)]
    ring
  have hsumJ : Summable (fun i : J => 1 - ‖b i‖) :=
    hsum.subtype fun i => i ∈ (↑s : Set ι)ᶜ
  have hsumDev : Summable (fun i : J => ‖normalizedBlaschkeFactor (b i) 0 - 1‖) :=
    hsumJ.congr fun i => (hdev i).symm
  have hzeroMem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have hprod : HasProd (fun i : J => normalizedBlaschkeFactor (b i) 0)
      (indexedBlaschkeProduct b 0) :=
    (indexedBlaschkeProduct_hasProdLocallyUniformlyOn b
      (fun i => haDisk i) hsumJ).hasProd hzeroMem
  have hprod' : HasProd
      (fun i : J => 1 + (normalizedBlaschkeFactor (b i) 0 - 1))
      (indexedBlaschkeProduct b 0) := by
    convert hprod using 1
    ext i
    ring
  have hprodClose : ‖indexedBlaschkeProduct b 0 - 1‖ ≤
      Real.exp (blaschkeTailMass a s) - 1 := by
    apply norm_tprod_one_add_sub_one_le hprod' hsumDev
    rw [tsum_congr hdev]
    simp only [blaschkeTailMass, J, b]
    exact le_rfl
  have hqnorm : ‖q‖ ≤ 1 := by
    calc
      ‖q‖ = ‖hardyMul T hardyOne‖ := rfl
      _ ≤ ‖hardyMul T‖ * ‖hardyOne‖ := (hardyMul T).le_opNorm hardyOne
      _ ≤ 1 * 1 := mul_le_mul (norm_hardyMul_le T) (le_of_eq norm_hardyOne)
        (norm_nonneg _) zero_le_one
      _ = 1 := by ring
  have hinner : inner ℂ hardyOne q = indexedBlaschkeProduct b 0 := by
    rw [inner_hardyOne, hardyFun_hardyOf]
    rfl
    norm_num
  have hre : 1 - (indexedBlaschkeProduct b 0).re ≤
      ‖indexedBlaschkeProduct b 0 - 1‖ := by
    calc
      1 - (indexedBlaschkeProduct b 0).re =
          -(indexedBlaschkeProduct b 0 - 1).re := by simp
      _ ≤ |(indexedBlaschkeProduct b 0 - 1).re| := neg_le_abs _
      _ ≤ ‖indexedBlaschkeProduct b 0 - 1‖ := Complex.abs_re_le_norm _
  have hqnormsq : ‖q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q]
  calc
    ‖hardyOf T - hardyOne‖ ^ 2 = ‖hardyOne - q‖ ^ 2 := by
      rw [norm_sub_rev]
    _ = ‖hardyOne‖ ^ 2 - 2 * RCLike.re (inner ℂ hardyOne q) + ‖q‖ ^ 2 :=
      norm_sub_sq hardyOne q
    _ ≤ 2 * (1 - (indexedBlaschkeProduct b 0).re) := by
      rw [norm_hardyOne, hinner]
      change 1 ^ 2 - 2 * (indexedBlaschkeProduct b 0).re + ‖q‖ ^ 2 ≤
        2 * (1 - (indexedBlaschkeProduct b 0).re)
      nlinarith
    _ ≤ 2 * ‖indexedBlaschkeProduct b 0 - 1‖ :=
      mul_le_mul_of_nonneg_left hre (by norm_num)
    _ ≤ 2 * (Real.exp (blaschkeTailMass a s) - 1) :=
      mul_le_mul_of_nonneg_left hprodClose (by norm_num)

private theorem tendsto_tail_hardyOne
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) :
    Tendsto
      (fun s : Finset ι => hardyOf (indexedBlaschkeTailMultiplier a haDisk hsum s))
      atTop (nhds hardyOne) := by
  have hmass := tendsto_blaschkeTailMass a haDisk hsum
  have hexp : Tendsto (fun s : Finset ι => Real.exp (blaschkeTailMass a s))
      atTop (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp hmass
    change Tendsto (fun s : Finset ι => Real.exp (blaschkeTailMass a s))
      atTop (nhds (Real.exp 0)) at h
    simpa using h
  have hbound : Tendsto
      (fun s : Finset ι => 2 * (Real.exp (blaschkeTailMass a s) - 1))
      atTop (nhds 0) := by
    have hone : Tendsto (fun _ : Finset ι => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_self, mul_zero] using (hexp.sub hone).const_mul 2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev := Metric.tendsto_nhds.mp hbound (ε ^ 2) (sq_pos_of_pos hε)
  filter_upwards [hev] with s hs
  rw [dist_eq_norm]
  have hb := tail_hardyOne_sub_norm_sq_le a haDisk hsum s
  have hmass0 : 0 ≤ blaschkeTailMass a s := by
    unfold blaschkeTailMass
    exact tsum_nonneg fun i => sub_nonneg.mpr (haDisk i).le
  have hbound0 : 0 ≤ 2 * (Real.exp (blaschkeTailMass a s) - 1) := by
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp hmass0))
  have hs' : 2 * (Real.exp (blaschkeTailMass a s) - 1) < ε ^ 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbound0] at hs
    exact hs
  nlinarith [norm_nonneg
    (hardyOf (indexedBlaschkeTailMultiplier a haDisk hsum s) - hardyOne)]

private theorem tendsto_prefix_hardyOne
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) :
    Tendsto
      (fun s : Finset ι => hardyOf (indexedBlaschkePrefixMultiplier a haDisk s))
      atTop (nhds (hardyOf (indexedBlaschkeMultiplier a haDisk hsum))) := by
  have htail := tendsto_tail_hardyOne a haDisk hsum
  rw [Metric.tendsto_nhds] at htail ⊢
  intro ε hε
  filter_upwards [htail ε hε] with s hs
  rw [dist_eq_norm] at hs ⊢
  have hfactor := hardyMul_indexedBlaschke_eq_prefix_tail a haDisk hsum s hardyOne
  have heq :
      hardyOf (indexedBlaschkeMultiplier a haDisk hsum) -
          hardyOf (indexedBlaschkePrefixMultiplier a haDisk s) =
        hardyMul (indexedBlaschkePrefixMultiplier a haDisk s)
          (hardyOf (indexedBlaschkeTailMultiplier a haDisk hsum s) - hardyOne) := by
    rw [map_sub]
    exact congrArg (fun y => y - hardyOf (indexedBlaschkePrefixMultiplier a haDisk s))
      hfactor
  calc
    ‖hardyOf (indexedBlaschkePrefixMultiplier a haDisk s) -
        hardyOf (indexedBlaschkeMultiplier a haDisk hsum)‖ =
        ‖hardyOf (indexedBlaschkeMultiplier a haDisk hsum) -
          hardyOf (indexedBlaschkePrefixMultiplier a haDisk s)‖ := norm_sub_rev _ _
    _ = ‖hardyMul (indexedBlaschkePrefixMultiplier a haDisk s)
          (hardyOf (indexedBlaschkeTailMultiplier a haDisk hsum s) - hardyOne)‖ := by
      rw [heq]
    _ = ‖hardyOf (indexedBlaschkeTailMultiplier a haDisk hsum s) - hardyOne‖ :=
      norm_hardyMul_indexedBlaschkePrefixMultiplier a haDisk s _
    _ < ε := hs

private theorem hardyMul_comm_shift_pow
    (φ : DiskMultiplier) (n : ℕ) (x : HardyDisk) :
    hardyMul φ (((hardyMul diskShift) ^ n) x) =
      ((hardyMul diskShift) ^ n) (hardyMul φ x) := by
  refine hardyDisk_ext fun z hz => ?_
  rw [hardyFun_hardyMul _ _ hz, hardyFun_shift_pow n x hz,
    hardyFun_shift_pow n (hardyMul φ x) hz, hardyFun_hardyMul _ _ hz]
  ring

private theorem dense_polyMultiples_hardyOne :
    Dense (((polyMultiples hardyOne : Submodule ℂ HardyDisk) : Set HardyDisk)) := by
  have hc := cyclicSubspace_hardyOne
  rw [cyclicSubspace] at hc
  have hcoe := congrArg (fun W : Submodule ℂ HardyDisk => (W : Set HardyDisk)) hc
  rw [Submodule.topologicalClosure_coe, Submodule.top_coe] at hcoe
  exact dense_iff_closure_eq.mpr hcoe

/-- Finite indexed Blaschke prefixes converge strongly to the full multiplier. -/
theorem tendsto_hardyMul_indexedBlaschkePrefix
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) (x : HardyDisk) :
    Tendsto
      (fun s : Finset ι => hardyMul (indexedBlaschkePrefixMultiplier a haDisk s) x)
      atTop (nhds (hardyMul (indexedBlaschkeMultiplier a haDisk hsum) x)) := by
  let T : Finset ι → HardyDisk →L[ℂ] HardyDisk := fun s =>
    hardyMul (indexedBlaschkePrefixMultiplier a haDisk s)
  let S : HardyDisk →L[ℂ] HardyDisk := hardyMul (indexedBlaschkeMultiplier a haDisk hsum)
  have hbase : Tendsto (fun s : Finset ι => T s hardyOne) atTop (nhds (S hardyOne)) :=
    tendsto_prefix_hardyOne a haDisk hsum
  have hconv : ∀ v ∈ (polyMultiples hardyOne : Submodule ℂ HardyDisk),
      Tendsto (fun s : Finset ι => T s v) atTop (nhds (S v)) := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro y ⟨n, rfl⟩
      have hmap := (((hardyMul diskShift) ^ n).continuous.tendsto _).comp hbase
      have hScomm : S (((hardyMul diskShift) ^ n) hardyOne) =
          ((hardyMul diskShift) ^ n) (S hardyOne) := by
        dsimp [S]
        exact hardyMul_comm_shift_pow _ n hardyOne
      rw [hScomm]
      convert hmap using 1
      funext s
      dsimp [T]
      exact hardyMul_comm_shift_pow _ n hardyOne
    · simpa only [map_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : Finset ι => (0 : HardyDisk)) atTop (nhds 0))
    · intro v w _ _ hv hw
      simpa only [map_add] using hv.add hw
    · intro c v _ hv
      simpa only [map_smul] using hv.const_smul c
  apply tendsto_of_dense_of_uniform_bound (C := 1) zero_le_one
    (Eventually.of_forall fun s => ?_) (norm_hardyMul_le _) dense_polyMultiples_hardyOne
    hconv x
  exact norm_hardyMul_le _

/-- An indexed Blaschke product satisfying the Blaschke condition acts isometrically on `H²(D)`. -/
theorem indexedBlaschkeMultiplier_isometry
    {ι : Type*} (a : ι → ℂ) (haDisk : ∀ i, ‖a i‖ < 1)
    (hsum : Summable (fun i => 1 - ‖a i‖)) :
    HardyMultiplierIsometry (indexedBlaschkeMultiplier a haDisk hsum) := by
  intro x
  have hconv := tendsto_hardyMul_indexedBlaschkePrefix a haDisk hsum x
  have hnorm : Tendsto
      (fun s : Finset ι => ‖hardyMul (indexedBlaschkePrefixMultiplier a haDisk s) x‖)
      atTop (nhds ‖hardyMul (indexedBlaschkeMultiplier a haDisk hsum) x‖) :=
    (continuous_norm.tendsto _).comp hconv
  have heq : (fun s : Finset ι =>
      ‖hardyMul (indexedBlaschkePrefixMultiplier a haDisk s) x‖) =
      fun _ => ‖x‖ := by
    funext s
    exact norm_hardyMul_indexedBlaschkePrefixMultiplier a haDisk s x
  rw [heq] at hnorm
  exact tendsto_nhds_unique hnorm tendsto_const_nhds

end

end GaloisForLFunctions.HTGeometry
