import GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherCompleteMinimalSingularRealization
import GaloisForLFunctions.RHTower.Sieve.VinogradovBertrandReservoir

/-!
# Markushevich-basis singular realization of the physical MSC columns

Dyadic squarefree blocks carry explicit finite regular-simplex biorthogonal bases.  Their source
and overlap representatives have summable block energy throughout `1 / 2 < Re rho`, although the
exact coefficient-product invariant is not summable when `Re rho ≤ 1`.  The orthogonal block sum
therefore realizes both physical MSC columns with a normalized complete system whose explicit
biorthogonal dual is also complete, while every finite Bessel bound still fails in the critical
strip.  Thus even Markushevich-basis rigidity has no RH force without quantitative stability.
-/

open Complex Filter Set Topology
open scoped BigOperators Topology InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource.MarkushevichSingular

open Classical
open RHTower
open RHTower.HedenmalmThetaSource.CompleteMinimalSingular

def block (j : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter Squarefree

theorem block_nonempty (j : ℕ) : (block j).Nonempty := by
  let p := RHTower.Sieve.vinogradovBertrandNext (2 ^ j - 1)
  have hpow : 0 < 2 ^ j := pow_pos (by omega) _
  have hpownz : 2 ^ j ≠ 0 := ne_of_gt hpow
  have hpred : (2 ^ j - 1) + 1 = 2 ^ j := Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr hpownz)
  have hp : Nat.Prime p := RHTower.Sieve.vinogradovBertrandNext_prime _
  have hpgt : 2 ^ j < p := by
    dsimp [p, RHTower.Sieve.vinogradovBertrandNext]
    simpa [hpred] using (Classical.choose_spec
      (Nat.exists_prime_lt_and_le_two_mul ((2 ^ j - 1) + 1)
        (Nat.succ_ne_zero (2 ^ j - 1)))).2.1
  have hple : p ≤ 2 ^ (j + 1) := by
    calc
      p ≤ 2 * ((2 ^ j - 1) + 1) := RHTower.Sieve.vinogradovBertrandNext_le _
      _ = 2 ^ (j + 1) := by rw [hpred, pow_succ]; omega
  refine ⟨p, ?_⟩
  simp [block, hp.squarefree, hpgt, hple]

noncomputable instance blockSubtypeNonempty (j : ℕ) : Nonempty ↥(block j) :=
  ⟨⟨(block_nonempty j).choose, (block_nonempty j).choose_spec⟩⟩

theorem mem_block_log_pred {n : ℕ} (hn1 : n ≠ 1) (hn : Squarefree n) :
    n ∈ block (Nat.log 2 (n - 1)) := by
  have hn0 : n ≠ 0 := fun h => not_squarefree_zero (h ▸ hn)
  have hn2 : 2 ≤ n := by omega
  have hpred0 : n - 1 ≠ 0 := by omega
  have hlog := (Nat.log_eq_iff (m := Nat.log 2 (n - 1))
    (n := n - 1) (Or.inr ⟨by omega, hpred0⟩)).mp rfl
  rw [block, Finset.mem_filter, Finset.mem_Ioc]
  exact ⟨⟨by omega, by omega⟩, hn⟩

theorem log_pred_eq_of_mem_block {j n : ℕ} (hn : n ∈ block j) :
    Nat.log 2 (n - 1) = j := by
  rw [block, Finset.mem_filter, Finset.mem_Ioc] at hn
  have hpred0 : n - 1 ≠ 0 := by omega
  apply (Nat.log_eq_iff (m := j) (n := n - 1)
    (Or.inr ⟨by omega, hpred0⟩)).2
  omega

def budget (rho : ℂ) (sigma : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ ((j : ℝ) * (1 / 2 - rho.re)) /
    RHTower.squarefreeMobiusTotal sigma

theorem budget_pos (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) :
    0 < budget rho sigma j := by
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (RHTower.squarefreeMobiusTotal_pos hsigma)

theorem productWeight_le_block
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re)
    {j n : ℕ} (hn : n ∈ block j) :
    productWeight rho sigma n ≤
      (2 : ℝ) ^ (-(j : ℝ) * rho.re) /
        RHTower.squarefreeMobiusTotal sigma := by
  rw [block, Finset.mem_filter, Finset.mem_Ioc] at hn
  rw [productWeight_eq rho hsigma, RHTower.squarefreeMobiusMass,
    if_pos hn.2]
  apply div_le_div_of_nonneg_right _
    (RHTower.squarefreeMobiusTotal_pos hsigma).le
  have hbase : ((2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.1.le
  have hx0 : 0 < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hy0 : 0 < (n : ℝ) := lt_of_lt_of_le hx0 hbase
  have hpos := Real.rpow_le_rpow hx0.le hbase hrho.le
  have hpow : (n : ℝ) ^ (-rho.re) ≤ ((2 ^ j : ℕ) : ℝ) ^ (-rho.re) := by
    rw [Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx0 _) hpos
  calc
    (n : ℝ) ^ (-rho.re) ≤ ((2 ^ j : ℕ) : ℝ) ^ (-rho.re) := hpow
    _ = (((2 : ℝ) ^ (j : ℕ)) : ℝ) ^ (-rho.re) := by norm_num
    _ = ((2 : ℝ) ^ (j : ℝ)) ^ (-rho.re) := by rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ ((j : ℝ) * (-rho.re)) := by
      rw [Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    _ = (2 : ℝ) ^ (-(j : ℝ) * rho.re) := by congr 1; ring

theorem block_energy_le_budget_sq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 0 < rho.re)
    (j : ℕ) :
    ∑ n ∈ block j, productWeight rho sigma n ^ 2 ≤
      budget rho sigma j ^ 2 := by
  have hterm : ∀ n ∈ block j,
      productWeight rho sigma n ^ 2 ≤
        ((2 : ℝ) ^ (-(j : ℝ) * rho.re) /
          RHTower.squarefreeMobiusTotal sigma) ^ 2 := by
    intro n hn
    have hp := productWeight_le_block rho hsigma hrho hn
    have hp0 : 0 ≤ productWeight rho sigma n :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hb0 : 0 ≤ (2 : ℝ) ^ (-(j : ℝ) * rho.re) /
        RHTower.squarefreeMobiusTotal sigma :=
      (div_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (RHTower.squarefreeMobiusTotal_pos hsigma)).le
    nlinarith
  calc
    _ ≤ ∑ _n ∈ block j,
        ((2 : ℝ) ^ (-(j : ℝ) * rho.re) /
          RHTower.squarefreeMobiusTotal sigma) ^ 2 := by
      exact Finset.sum_le_sum hterm
    _ = (block j).card *
        ((2 : ℝ) ^ (-(j : ℝ) * rho.re) /
          RHTower.squarefreeMobiusTotal sigma) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 ^ j : ℝ) *
        ((2 : ℝ) ^ (-(j : ℝ) * rho.re) /
          RHTower.squarefreeMobiusTotal sigma) ^ 2 := by
      gcongr
      exact_mod_cast (calc
        (block j).card ≤ (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).card := by
          exact Finset.card_filter_le _ _
        _ = 2 ^ (j + 1) - 2 ^ j := by simp
        _ = 2 ^ j := by rw [pow_succ]; omega)
    _ = budget rho sigma j ^ 2 := by
      rw [budget]
      rw [show ((2 : ℝ) ^ j) = (2 : ℝ) ^ (j : ℝ) by
        exact (Real.rpow_natCast 2 j).symm]
      have hZ : RHTower.squarefreeMobiusTotal sigma ≠ 0 :=
        (RHTower.squarefreeMobiusTotal_pos hsigma).ne'
      field_simp [hZ]
      simp only [pow_two]
      rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ)),
        ← Real.rpow_add (by norm_num : 0 < (2 : ℝ)),
        ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      congr 1
      ring

theorem summable_budget
    (rho : ℂ) (sigma : ℝ) (hrho : 1 / 2 < rho.re) :
    Summable (budget rho sigma) := by
  let q : ℝ := (2 : ℝ) ^ (1 / 2 - rho.re)
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo := summable_geometric_of_lt_one hq0 hq1
  have heq : budget rho sigma = fun j : ℕ => q ^ j /
      RHTower.squarefreeMobiusTotal sigma := by
    funext j
    rw [budget]
    congr 1
    change (2 : ℝ) ^ ((j : ℝ) * (1 / 2 - rho.re)) =
      ((2 : ℝ) ^ (1 / 2 - rho.re)) ^ j
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    congr 1
    ring
  rw [heq]
  exact hgeo.div_const _

namespace Block

abbrev E (j : ℕ) :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.E ↥(block j)

def phase (rho : ℂ) (sigma : ℝ) (j : ℕ) (n : ↥(block j)) : ℂ :=
  sourceWeight rho sigma n / ‖sourceWeight rho sigma n‖

theorem norm_phase
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) (n : ↥(block j)) :
    ‖phase rho sigma j n‖ = 1 := by
  have hn : Squarefree (n : ℕ) := (Finset.mem_filter.mp n.property).2
  have hne := sourceWeight_ne_zero_of_squarefree rho hsigma hn
  simp [phase, hne]

def primal (rho : ℂ) (sigma : ℝ) (j : ℕ) (n : ↥(block j)) : E j :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.phasePrimal
    ↥(block j) (phase rho sigma j) n

def dual (rho : ℂ) (sigma : ℝ) (j : ℕ) (n : ↥(block j)) : E j :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.phaseDual
    ↥(block j) (phase rho sigma j) n

theorem norm_primal
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) (n : ↥(block j)) :
    ‖primal rho sigma j n‖ = 1 :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.norm_phasePrimal
    ↥(block j) (phase rho sigma j) (norm_phase rho hsigma j) n

theorem inner_primal_dual
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ)
    (n m : ↥(block j)) :
    inner ℂ (primal rho sigma j n) (dual rho sigma j m) =
      if n = m then 1 else 0 :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.inner_phasePrimal_phaseDual
      ↥(block j) (phase rho sigma j)
      (norm_phase rho hsigma j) n m

theorem isCompleteSystem_primal
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (primal rho sigma j) :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.isCompleteSystem_phasePrimal
      ↥(block j) (phase rho sigma j)
      (norm_phase rho hsigma j)

theorem isCompleteSystem_dual
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (dual rho sigma j) :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.isCompleteSystem_phaseDual
      ↥(block j) (phase rho sigma j)
      (norm_phase rho hsigma j)

def radius (rho : ℂ) (sigma : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (budget rho sigma j)

theorem radius_pos
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) :
    0 < radius rho sigma j :=
  Real.sqrt_pos.2 (budget_pos rho hsigma j)

theorem radius_sq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) :
    radius rho sigma j ^ 2 = budget rho sigma j := by
  exact Real.sq_sqrt (budget_pos rho hsigma j).le

def modeNorm (rho : ℂ) (sigma : ℝ) (j : ℕ) (n : ↥(block j)) : ℝ :=
  radius rho sigma j / ‖sourceWeight rho sigma n‖

theorem modeNorm_pos
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) (n : ↥(block j)) :
    0 < modeNorm rho sigma j n := by
  have hn : Squarefree (n : ℕ) := (Finset.mem_filter.mp n.property).2
  exact div_pos (radius_pos rho hsigma j)
    (norm_pos_iff.mpr (sourceWeight_ne_zero_of_squarefree rho hsigma hn))

def source (rho : ℂ) (sigma : ℝ) (j : ℕ) : E j :=
  ((GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.scale
      ↥(block j) : ℂ) * (radius rho sigma j : ℂ)) •
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.mean ↥(block j)

theorem inner_primal_source
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) (n : ↥(block j)) :
    inner ℂ (primal rho sigma j n) (source rho sigma j) =
      star (sourceWeight rho sigma n) * modeNorm rho sigma j n := by
  let ι := ↥(block j)
  let z := phase rho sigma j n
  have hn : Squarefree (n : ℕ) := (Finset.mem_filter.mp n.property).2
  have hA : sourceWeight rho sigma n ≠ 0 :=
    sourceWeight_ne_zero_of_squarefree rho hsigma hn
  have hs : GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.scale ι ≠ 0 :=
    (GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.scale_pos ι).ne'
  rw [primal, source,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.phasePrimal,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.primal,
    inner_smul_left, inner_smul_left, inner_smul_right, inner_add_left,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.inner_mean_mean,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.inner_centered_mean]
  simp only [mul_one, add_zero, map_inv₀,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.star_ofReal_local]
  have hsC : ((GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.scale ι : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hs
  rw [inv_mul_cancel_left₀ hsC]
  rw [phase, modeNorm]
  have hnormA : ‖sourceWeight rho sigma n‖ ≠ 0 := norm_ne_zero_iff.mpr hA
  rw [map_div₀]
  rw [GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.star_ofReal_local]
  push_cast
  field_simp [hnormA]
  simpa [RCLike.star_def] using
    (mul_comm ((starRingEnd ℂ) (sourceWeight rho sigma n)) (radius rho sigma j : ℂ))

def overlapData (rho : ℂ) (sigma : ℝ) (j : ℕ) (n : ↥(block j)) : ℂ :=
  phase rho sigma j n * star (overlapWeight sigma n) /
    modeNorm rho sigma j n

def overlap (rho : ℂ) (sigma : ℝ) (j : ℕ) : E j :=
  GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.solution
    ↥(block j) (overlapData rho sigma j)

theorem inner_primal_overlap
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) (n : ↥(block j)) :
    inner ℂ (primal rho sigma j n) (overlap rho sigma j) =
      star (overlapWeight sigma n) / modeNorm rho sigma j n := by
  rw [primal, overlap,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.phasePrimal,
    inner_smul_left,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.inner_primal_solution,
    overlapData]
  have hz := norm_phase rho hsigma j n
  have hzprod : (starRingEnd ℂ) (phase rho sigma j n) * phase rho sigma j n = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
    norm_num
  calc
    (starRingEnd ℂ) (phase rho sigma j n) *
          ((phase rho sigma j n * star (overlapWeight sigma n)) /
            (modeNorm rho sigma j n : ℂ)) =
        ((starRingEnd ℂ) (phase rho sigma j n) * phase rho sigma j n) *
          star (overlapWeight sigma n) / (modeNorm rho sigma j n : ℂ) := by ring
    _ = _ := by rw [hzprod, one_mul]

theorem norm_overlapData_sq
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) (n : ↥(block j)) :
    ‖overlapData rho sigma j n‖ ^ 2 =
      productWeight rho sigma n ^ 2 / budget rho sigma j := by
  have hn : Squarefree (n : ℕ) := (Finset.mem_filter.mp n.property).2
  have hApos : 0 < ‖sourceWeight rho sigma n‖ :=
    norm_pos_iff.mpr (sourceWeight_ne_zero_of_squarefree rho hsigma hn)
  have hrpos := radius_pos rho hsigma j
  have htpos := modeNorm_pos rho hsigma j n
  rw [overlapData, norm_div, norm_mul, norm_phase rho hsigma,
    one_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos htpos, modeNorm, productWeight]
  rw [← radius_sq rho hsigma j]
  field_simp [hrpos.ne', hApos.ne']

theorem sum_norm_overlapData_sq_le_budget
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hrho : 0 < rho.re) (j : ℕ) :
    ∑ n : ↥(block j), ‖overlapData rho sigma j n‖ ^ 2 ≤
      budget rho sigma j := by
  simp_rw [norm_overlapData_sq rho hsigma]
  rw [← Finset.sum_div]
  have henergy := block_energy_le_budget_sq rho hsigma hrho j
  have hreindex :
      ∑ n : ↥(block j), productWeight rho sigma n ^ 2 =
        ∑ n ∈ block j, productWeight rho sigma n ^ 2 := by
    simpa only [Finset.univ_eq_attach] using
      Finset.sum_attach (block j) (fun n => productWeight rho sigma n ^ 2)
  rw [hreindex]
  have hQ := budget_pos rho hsigma j
  calc
    (∑ n ∈ block j, productWeight rho sigma n ^ 2) /
          budget rho sigma j ≤
        budget rho sigma j ^ 2 / budget rho sigma j :=
      div_le_div_of_nonneg_right henergy hQ.le
    _ = budget rho sigma j := by field_simp [hQ.ne']

theorem norm_source_sq_le
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (j : ℕ) :
    ‖source rho sigma j‖ ^ 2 ≤ 2 * budget rho sigma j := by
  rw [source, norm_smul,
    GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.norm_mean,
    mul_one, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.scale_pos _),
    abs_of_pos (radius_pos rho hsigma j), mul_pow, radius_sq rho hsigma]
  exact mul_le_mul_of_nonneg_right
    (GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.scale_sq_le_two _)
    (budget_pos rho hsigma j).le

theorem norm_overlap_sq_le
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hrho : 0 < rho.re) (j : ℕ) :
    ‖overlap rho sigma j‖ ^ 2 ≤ 20 * budget rho sigma j := by
  exact (GaloisForLFunctions.HTGeometry.FiniteMarkushevichSimplexBlock.norm_solution_sq_le
    ↥(block j) (overlapData rho sigma j)).trans
      (mul_le_mul_of_nonneg_left
        (sum_norm_overlapData_sq_le_budget rho hsigma hrho j) (by norm_num))

end Block

abbrev BlockH := lp Block.E 2
abbrev ResidualIndex := {n : ℕ // n = 1 ∨ ¬ Squarefree n}
abbrev ResidualH := lp (fun _ : ResidualIndex => ℂ) 2
abbrev H := WithLp 2 (BlockH × ResidualH)

theorem blockSourceFamily_memℓp
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) :
    Memℓp (Block.source rho sigma) 2 := by
  refine memℓp_gen ?_
  have hsum := (summable_budget rho sigma hrho).mul_left 2
  refine Summable.of_nonneg_of_le
    (fun j => Real.rpow_nonneg (norm_nonneg _) _) (fun j => ?_) hsum
  rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  exact Block.norm_source_sq_le rho hsigma j

theorem blockOverlapFamily_memℓp
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) :
    Memℓp (Block.overlap rho sigma) 2 := by
  refine memℓp_gen ?_
  have hsum := (summable_budget rho sigma hrho).mul_left 20
  refine Summable.of_nonneg_of_le
    (fun j => Real.rpow_nonneg (norm_nonneg _) _) (fun j => ?_) hsum
  rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  exact Block.norm_overlap_sq_le rho hsigma (by linarith) j

def blockSourceVector
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) : BlockH :=
  ⟨Block.source rho sigma, blockSourceFamily_memℓp rho hsigma hrho⟩

def blockOverlapVector
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) : BlockH :=
  ⟨Block.overlap rho sigma, blockOverlapFamily_memℓp rho hsigma hrho⟩

@[simp] theorem blockSourceVector_apply
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) (j : ℕ) :
    blockSourceVector rho hsigma hrho j = Block.source rho sigma j := rfl

@[simp] theorem blockOverlapVector_apply
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) (j : ℕ) :
    blockOverlapVector rho hsigma hrho j = Block.overlap rho sigma j := rfl

def headIndex : ResidualIndex := ⟨1, Or.inl rfl⟩

def residualSource (rho : ℂ) (sigma : ℝ) : ResidualH :=
  lp.single 2 headIndex (star (sourceWeight rho sigma 1))

def residualOverlap (sigma : ℝ) : ResidualH :=
  lp.single 2 headIndex (star (overlapWeight sigma 1))

def sourceVector
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) : H :=
  WithLp.toLp 2 (blockSourceVector rho hsigma hrho, residualSource rho sigma)

def overlapVector
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) : H :=
  WithLp.toLp 2 (blockOverlapVector rho hsigma hrho, residualOverlap sigma)

def normalizedMode (rho : ℂ) (sigma : ℝ) (n : ℕ) : H := by
  classical
  by_cases h1 : n = 1
  · exact WithLp.toLp 2 (0,
      lp.single (E := fun _ : ResidualIndex => ℂ) 2 headIndex 1)
  by_cases hn : Squarefree n
  · let j := Nat.log 2 (n - 1)
    let i : ↥(block j) := ⟨n, mem_block_log_pred h1 hn⟩
    exact WithLp.toLp 2 (lp.single 2 j (Block.primal rho sigma j i), 0)
  · exact WithLp.toLp 2 (0, lp.single 2
      (⟨n, Or.inr hn⟩ : ResidualIndex) 1)

def normalizedDual (rho : ℂ) (sigma : ℝ) (n : ℕ) : H := by
  classical
  by_cases h1 : n = 1
  · exact WithLp.toLp 2 (0,
      lp.single (E := fun _ : ResidualIndex => ℂ) 2 headIndex 1)
  by_cases hn : Squarefree n
  · let j := Nat.log 2 (n - 1)
    let i : ↥(block j) := ⟨n, mem_block_log_pred h1 hn⟩
    exact WithLp.toLp 2 (lp.single 2 j (Block.dual rho sigma j i), 0)
  · exact WithLp.toLp 2 (0, lp.single 2
      (⟨n, Or.inr hn⟩ : ResidualIndex) 1)

def modeNorm (rho : ℂ) (sigma : ℝ) (n : ℕ) : ℝ := by
  classical
  by_cases h1 : n = 1
  · exact 1
  by_cases hn : Squarefree n
  · let j := Nat.log 2 (n - 1)
    let i : ↥(block j) := ⟨n, mem_block_log_pred h1 hn⟩
    exact Block.modeNorm rho sigma j i
  · exact 1

@[simp] theorem normalizedMode_one (rho : ℂ) (sigma : ℝ) :
    normalizedMode rho sigma 1 =
      WithLp.toLp 2 (0, lp.single 2 headIndex 1) := by
  rw [normalizedMode]
  simp

theorem normalizedMode_of_squarefree
    (rho : ℂ) (sigma : ℝ) {n : ℕ} (h1 : n ≠ 1) (hn : Squarefree n) :
    normalizedMode rho sigma n =
      WithLp.toLp 2
        (lp.single 2 (Nat.log 2 (n - 1))
          (Block.primal rho sigma (Nat.log 2 (n - 1))
            ⟨n, mem_block_log_pred h1 hn⟩), 0) := by
  rw [normalizedMode]
  simp [h1, hn]

theorem normalizedMode_of_not_squarefree
    (rho : ℂ) (sigma : ℝ) {n : ℕ} (h1 : n ≠ 1) (hn : ¬ Squarefree n) :
    normalizedMode rho sigma n =
      WithLp.toLp 2 (0, lp.single 2 (⟨n, Or.inr hn⟩ : ResidualIndex) 1) := by
  rw [normalizedMode]
  simp [h1, hn]

theorem normalizedMode_of_mem_block
    (rho : ℂ) (sigma : ℝ) {j n : ℕ} (hmem : n ∈ block j) :
    normalizedMode rho sigma n =
      WithLp.toLp 2
        (lp.single 2 j (Block.primal rho sigma j ⟨n, hmem⟩), 0) := by
  have hn : Squarefree n := (Finset.mem_filter.mp hmem).2
  have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem).1).1
  have hjpos : 0 < 2 ^ j := pow_pos (by omega) _
  have h1 : n ≠ 1 := by omega
  rw [normalizedMode_of_squarefree rho sigma h1 hn]
  have hlog := log_pred_eq_of_mem_block hmem
  cases hlog
  rfl

@[simp] theorem normalizedDual_one (rho : ℂ) (sigma : ℝ) :
    normalizedDual rho sigma 1 =
      WithLp.toLp 2 (0, lp.single 2 headIndex 1) := by
  rw [normalizedDual]
  simp

theorem normalizedDual_of_squarefree
    (rho : ℂ) (sigma : ℝ) {n : ℕ} (h1 : n ≠ 1) (hn : Squarefree n) :
    normalizedDual rho sigma n =
      WithLp.toLp 2
        (lp.single 2 (Nat.log 2 (n - 1))
          (Block.dual rho sigma (Nat.log 2 (n - 1))
            ⟨n, mem_block_log_pred h1 hn⟩), 0) := by
  rw [normalizedDual]
  simp [h1, hn]

theorem normalizedDual_of_not_squarefree
    (rho : ℂ) (sigma : ℝ) {n : ℕ} (h1 : n ≠ 1) (hn : ¬ Squarefree n) :
    normalizedDual rho sigma n =
      WithLp.toLp 2 (0, lp.single 2 (⟨n, Or.inr hn⟩ : ResidualIndex) 1) := by
  rw [normalizedDual]
  simp [h1, hn]

theorem normalizedDual_of_mem_block
    (rho : ℂ) (sigma : ℝ) {j n : ℕ} (hmem : n ∈ block j) :
    normalizedDual rho sigma n =
      WithLp.toLp 2
        (lp.single 2 j (Block.dual rho sigma j ⟨n, hmem⟩), 0) := by
  have hn : Squarefree n := (Finset.mem_filter.mp hmem).2
  have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem).1).1
  have hjpos : 0 < 2 ^ j := pow_pos (by omega) _
  have h1 : n ≠ 1 := by omega
  rw [normalizedDual_of_squarefree rho sigma h1 hn]
  have hlog := log_pred_eq_of_mem_block hmem
  cases hlog
  rfl

@[simp] theorem modeNorm_one (rho : ℂ) (sigma : ℝ) :
    modeNorm rho sigma 1 = 1 := by
  rw [modeNorm]
  simp

theorem modeNorm_of_squarefree
    (rho : ℂ) (sigma : ℝ) {n : ℕ} (h1 : n ≠ 1) (hn : Squarefree n) :
    modeNorm rho sigma n = Block.modeNorm rho sigma (Nat.log 2 (n - 1))
      ⟨n, mem_block_log_pred h1 hn⟩ := by
  rw [modeNorm]
  simp [h1, hn]

theorem modeNorm_of_not_squarefree
    (rho : ℂ) (sigma : ℝ) {n : ℕ} (hn : ¬ Squarefree n) :
    modeNorm rho sigma n = 1 := by
  rw [modeNorm]
  simp [hn]

theorem modeNorm_pos
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 < modeNorm rho sigma n := by
  classical
  rw [modeNorm]
  split_ifs with h1 hn
  · norm_num
  · exact Block.modeNorm_pos rho hsigma _ _
  · norm_num

theorem norm_withLp_left (x : BlockH) :
    ‖(WithLp.toLp 2 (x, 0) : H)‖ = ‖x‖ :=
  WithLp.norm_toLp_fst 2 BlockH ResidualH x

theorem norm_withLp_right (x : ResidualH) :
    ‖(WithLp.toLp 2 (0, x) : H)‖ = ‖x‖ :=
  WithLp.norm_toLp_snd 2 BlockH ResidualH x

theorem norm_normalizedMode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖normalizedMode rho sigma n‖ = 1 := by
  classical
  by_cases h1 : n = 1
  · subst n
    rw [normalizedMode_one]
    rw [norm_withLp_right, lp.norm_single (by norm_num), norm_one]
  · by_cases hn : Squarefree n
    · rw [normalizedMode_of_squarefree rho sigma h1 hn]
      rw [norm_withLp_left, lp.norm_single (by norm_num), Block.norm_primal rho hsigma]
    · rw [normalizedMode_of_not_squarefree rho sigma h1 hn]
      rw [norm_withLp_right, lp.norm_single (by norm_num), norm_one]

def mode (rho : ℂ) (sigma : ℝ) (n : ℕ) : H :=
  (modeNorm rho sigma n : ℂ) • normalizedMode rho sigma n

theorem norm_mode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    ‖mode rho sigma n‖ = modeNorm rho sigma n := by
  rw [mode, norm_smul, norm_normalizedMode rho hsigma, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (modeNorm_pos rho hsigma n)]

theorem mode_ne_zero
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    mode rho sigma n ≠ 0 := by
  rw [← norm_pos_iff, norm_mode rho hsigma]
  exact modeNorm_pos rho hsigma n

theorem normalized_mode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode (mode rho sigma) n =
      normalizedMode rho sigma n := by
  have ht : (modeNorm rho sigma n : ℂ) ≠ 0 := by
    exact_mod_cast (modeNorm_pos rho hsigma n).ne'
  rw [RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode,
    norm_mode rho hsigma, mode]
  calc
    (modeNorm rho sigma n : ℂ)⁻¹ •
        ((modeNorm rho sigma n : ℂ) • normalizedMode rho sigma n) =
        ((modeNorm rho sigma n : ℂ)⁻¹ * (modeNorm rho sigma n : ℂ)) •
          normalizedMode rho sigma n := by rw [smul_smul]
    _ = normalizedMode rho sigma n := by rw [inv_mul_cancel₀ ht, one_smul]

theorem inner_normalizedMode_source
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hrho : 1 / 2 < rho.re) (n : ℕ) :
    inner ℂ (normalizedMode rho sigma n) (sourceVector rho hsigma hrho) =
      star (sourceWeight rho sigma n) * modeNorm rho sigma n := by
  classical
  by_cases h1 : n = 1
  · subst n
    simp [normalizedMode_one, modeNorm_one, sourceVector, residualSource,
      WithLp.prod_inner_apply, lp.inner_single_left, headIndex]
  · by_cases hn : Squarefree n
    · let j := Nat.log 2 (n - 1)
      let i : ↥(block j) := ⟨n, mem_block_log_pred h1 hn⟩
      rw [normalizedMode_of_squarefree rho sigma h1 hn,
        modeNorm_of_squarefree rho sigma h1 hn]
      rw [WithLp.prod_inner_apply]
      change inner ℂ (lp.single (E := Block.E) 2 j (Block.primal rho sigma j i))
          (blockSourceVector rho hsigma hrho) + inner ℂ (0 : ResidualH)
            (residualSource rho sigma) =
        star (sourceWeight rho sigma n) * Block.modeNorm rho sigma j i
      rw [inner_zero_left, add_zero, lp.inner_single_left, blockSourceVector_apply]
      exact Block.inner_primal_source rho hsigma j i
    · rw [normalizedMode_of_not_squarefree rho sigma h1 hn,
        modeNorm_of_not_squarefree rho sigma hn,
        sourceWeight_eq_zero_of_not_squarefree rho sigma hn]
      rw [WithLp.prod_inner_apply]
      simp [sourceVector, residualSource, lp.inner_single_left, lp.single_apply,
        headIndex, h1]

theorem inner_normalizedMode_overlap
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hrho : 1 / 2 < rho.re) (n : ℕ) :
    inner ℂ (normalizedMode rho sigma n) (overlapVector rho hsigma hrho) =
      star (overlapWeight sigma n) / modeNorm rho sigma n := by
  classical
  by_cases h1 : n = 1
  · subst n
    simp [normalizedMode_one, modeNorm_one, overlapVector, residualOverlap,
      WithLp.prod_inner_apply, lp.inner_single_left, headIndex]
  · by_cases hn : Squarefree n
    · let j := Nat.log 2 (n - 1)
      let i : ↥(block j) := ⟨n, mem_block_log_pred h1 hn⟩
      rw [normalizedMode_of_squarefree rho sigma h1 hn,
        modeNorm_of_squarefree rho sigma h1 hn]
      rw [WithLp.prod_inner_apply]
      change inner ℂ (lp.single (E := Block.E) 2 j (Block.primal rho sigma j i))
          (blockOverlapVector rho hsigma hrho) + inner ℂ (0 : ResidualH)
            (residualOverlap sigma) =
        star (overlapWeight sigma n) / Block.modeNorm rho sigma j i
      rw [inner_zero_left, add_zero, lp.inner_single_left, blockOverlapVector_apply]
      exact Block.inner_primal_overlap rho hsigma j i
    · rw [normalizedMode_of_not_squarefree rho sigma h1 hn,
        modeNorm_of_not_squarefree rho sigma hn,
        overlapWeight_eq_zero_of_not_squarefree sigma hn]
      rw [WithLp.prod_inner_apply]
      simp [overlapVector, residualOverlap, lp.inner_single_left, lp.single_apply,
        headIndex, h1]

theorem isMSCPhysicalOverlapHilbertRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) :
    RHTower.HedenmalmThetaSource.IsMSCPhysicalOverlapHilbertRealization
      rho sigma (mode rho sigma) (sourceVector rho hsigma hrho)
        (overlapVector rho hsigma hrho) := by
  refine ⟨mode_ne_zero rho hsigma, ?_, ?_⟩
  · intro n
    rw [normalized_mode rho hsigma, inner_normalizedMode_source rho hsigma hrho,
      norm_mode rho hsigma]
    rfl
  · intro n
    rw [normalized_mode rho hsigma, inner_normalizedMode_overlap rho hsigma hrho,
      norm_mode rho hsigma]
    rfl

theorem withLp_ext {x y : H} (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  apply (WithLp.equiv 2 (BlockH × ResidualH)).injective
  exact Prod.ext hfst hsnd

theorem isCompleteSystem_normalizedMode
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (normalizedMode rho sigma) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  apply withLp_ext
  · apply lp.ext
    funext j
    have hc := Block.isCompleteSystem_primal rho hsigma j
    rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero] at hc
    apply hc
    intro i
    have hi := hx (i : ℕ)
    rw [normalizedMode_of_mem_block rho sigma i.property, WithLp.prod_inner_apply] at hi
    simp only [inner_zero_left, add_zero] at hi
    rw [lp.inner_single_left] at hi
    exact hi
  · apply lp.ext
    funext q
    rcases q.property with hq | hq
    · have hqeq : q = headIndex := Subtype.ext hq
      subst q
      have h := hx 1
      rw [normalizedMode_one, WithLp.prod_inner_apply] at h
      simp only [inner_zero_left, zero_add] at h
      rw [lp.inner_single_left] at h
      simpa using h
    · have hq1 : (q : ℕ) ≠ 1 := by
        intro heq
        apply hq
        simp [heq]
      have h := hx (q : ℕ)
      rw [normalizedMode_of_not_squarefree rho sigma hq1 hq, WithLp.prod_inner_apply] at h
      simp only [inner_zero_left, zero_add] at h
      rw [lp.inner_single_left] at h
      simpa using h

theorem isCompleteSystem_normalizedDual
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ (normalizedDual rho sigma) := by
  rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero]
  intro x hx
  apply withLp_ext
  · apply lp.ext
    funext j
    have hc := Block.isCompleteSystem_dual rho hsigma j
    rw [GaloisForLFunctions.HTGeometry.isCompleteSystem_iff_forall_inner_eq_zero] at hc
    apply hc
    intro i
    have hi := hx (i : ℕ)
    rw [normalizedDual_of_mem_block rho sigma i.property, WithLp.prod_inner_apply] at hi
    simp only [inner_zero_left, add_zero] at hi
    rw [lp.inner_single_left] at hi
    exact hi
  · apply lp.ext
    funext q
    rcases q.property with hq | hq
    · have hqeq : q = headIndex := Subtype.ext hq
      subst q
      have h := hx 1
      rw [normalizedDual_one, WithLp.prod_inner_apply] at h
      simp only [inner_zero_left, zero_add] at h
      rw [lp.inner_single_left] at h
      simpa using h
    · have hq1 : (q : ℕ) ≠ 1 := by
        intro heq
        apply hq
        simp [heq]
      have h := hx (q : ℕ)
      rw [normalizedDual_of_not_squarefree rho sigma hq1 hq, WithLp.prod_inner_apply] at h
      simp only [inner_zero_left, zero_add] at h
      rw [lp.inner_single_left] at h
      simpa using h

theorem inner_normalizedMode_normalizedDual_self
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    inner ℂ (normalizedMode rho sigma n) (normalizedDual rho sigma n) = 1 := by
  classical
  by_cases h1 : n = 1
  · subst n
    rw [normalizedMode_one, normalizedDual_one, WithLp.prod_inner_apply]
    simp
  · by_cases hn : Squarefree n
    · rw [normalizedMode_of_squarefree rho sigma h1 hn,
        normalizedDual_of_squarefree rho sigma h1 hn, WithLp.prod_inner_apply]
      simp only [inner_zero_left, add_zero, lp.inner_single_left, lp.single_apply]
      rw [Pi.single_eq_same, Block.inner_primal_dual rho hsigma]
      simp
    · rw [normalizedMode_of_not_squarefree rho sigma h1 hn,
        normalizedDual_of_not_squarefree rho sigma h1 hn, WithLp.prod_inner_apply]
      simp

theorem inner_normalizedMode_normalizedDual_ne
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) {n m : ℕ} (hnm : n ≠ m) :
    inner ℂ (normalizedMode rho sigma n) (normalizedDual rho sigma m) = 0 := by
  classical
  by_cases hn1 : n = 1
  · subst n
    have hm1 : m ≠ 1 := Ne.symm hnm
    by_cases hm : Squarefree m
    · rw [normalizedMode_one, normalizedDual_of_squarefree rho sigma hm1 hm,
        WithLp.prod_inner_apply]
      simp
    · rw [normalizedMode_one, normalizedDual_of_not_squarefree rho sigma hm1 hm,
        WithLp.prod_inner_apply]
      simp [lp.inner_single_left, lp.single_apply, headIndex, hm1]
  · by_cases hn : Squarefree n
    · by_cases hm1 : m = 1
      · subst m
        rw [normalizedMode_of_squarefree rho sigma hn1 hn, normalizedDual_one,
          WithLp.prod_inner_apply]
        simp
      · by_cases hm : Squarefree m
        · let jn := Nat.log 2 (n - 1)
          let jm := Nat.log 2 (m - 1)
          by_cases hj : jn = jm
          · have hnn : n ∈ block jn := by
              simpa [jn] using mem_block_log_pred hn1 hn
            have hmm : m ∈ block jn := by
              rw [hj]
              simpa [jm] using mem_block_log_pred hm1 hm
            rw [normalizedMode_of_mem_block rho sigma hnn,
              normalizedDual_of_mem_block rho sigma hmm, WithLp.prod_inner_apply]
            simp only [inner_zero_left, add_zero, lp.inner_single_left, lp.single_apply]
            rw [Pi.single_eq_same, Block.inner_primal_dual rho hsigma]
            simp [Subtype.ext_iff, hnm]
          · have hj' : jm ≠ jn := Ne.symm hj
            rw [normalizedMode_of_squarefree rho sigma hn1 hn,
              normalizedDual_of_squarefree rho sigma hm1 hm, WithLp.prod_inner_apply]
            simp only [inner_zero_left, add_zero, lp.inner_single_left, lp.single_apply]
            simp [jn, jm, hj']
        · rw [normalizedMode_of_squarefree rho sigma hn1 hn,
            normalizedDual_of_not_squarefree rho sigma hm1 hm,
            WithLp.prod_inner_apply]
          simp
    · by_cases hm1 : m = 1
      · subst m
        rw [normalizedMode_of_not_squarefree rho sigma hn1 hn, normalizedDual_one,
          WithLp.prod_inner_apply]
        simp [lp.inner_single_left, lp.single_apply, headIndex, hn1]
      · by_cases hm : Squarefree m
        · rw [normalizedMode_of_not_squarefree rho sigma hn1 hn,
            normalizedDual_of_squarefree rho sigma hm1 hm,
            WithLp.prod_inner_apply]
          simp
        · rw [normalizedMode_of_not_squarefree rho sigma hn1 hn,
            normalizedDual_of_not_squarefree rho sigma hm1 hm,
            WithLp.prod_inner_apply]
          have hsub : (⟨n, Or.inr hn⟩ : ResidualIndex) ≠ ⟨m, Or.inr hm⟩ := by
            intro h
            exact hnm (congrArg Subtype.val h)
          simp [lp.inner_single_left, lp.single_apply, hsub]

theorem isDualSystem_normalizedMode_normalizedDual
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) :
    GaloisForLFunctions.HTGeometry.IsDualSystem ℂ
      (normalizedMode rho sigma) (normalizedDual rho sigma) := by
  apply GaloisForLFunctions.HTGeometry.IsDualSystem.symm
  constructor
  · exact inner_normalizedMode_normalizedDual_self rho hsigma
  · intro i j hij
    exact inner_normalizedMode_normalizedDual_ne rho hsigma hij

def IsMSCPhysicalOverlapMarkushevichHilbertRealization
    (rho : ℂ) (sigma : ℝ) (modes : ℕ → H) (source overlap : H)
    (dual : ℕ → H) : Prop :=
  RHTower.HedenmalmThetaSource.IsMSCPhysicalOverlapHilbertRealization
      rho sigma modes source overlap ∧
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ
      (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes) ∧
    GaloisForLFunctions.HTGeometry.IsCompleteSystem ℂ dual ∧
    GaloisForLFunctions.HTGeometry.IsDualSystem ℂ
      (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes) dual

theorem isMSCPhysicalOverlapMarkushevichHilbertRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) :
    IsMSCPhysicalOverlapMarkushevichHilbertRealization rho sigma
      (mode rho sigma) (sourceVector rho hsigma hrho) (overlapVector rho hsigma hrho)
        (normalizedDual rho sigma) := by
  refine ⟨isMSCPhysicalOverlapHilbertRealization rho hsigma hrho, ?_,
    isCompleteSystem_normalizedDual rho hsigma, ?_⟩
  · rw [show RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode
        (mode rho sigma) = normalizedMode rho sigma by
      funext n
      exact normalized_mode rho hsigma n]
    exact isCompleteSystem_normalizedMode rho hsigma
  · rw [show RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode
        (mode rho sigma) = normalizedMode rho sigma by
      funext n
      exact normalized_mode rho hsigma n]
    exact isDualSystem_normalizedMode_normalizedDual rho hsigma

theorem exists_mscPhysicalOverlapMarkushevichHilbertRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma) (hrho : 1 / 2 < rho.re) :
    ∃ (modes : ℕ → H) (source overlap : H) (dual : ℕ → H),
      IsMSCPhysicalOverlapMarkushevichHilbertRealization
        rho sigma modes source overlap dual := by
  exact ⟨mode rho sigma, sourceVector rho hsigma hrho, overlapVector rho hsigma hrho,
    normalizedDual rho sigma,
    isMSCPhysicalOverlapMarkushevichHilbertRealization rho hsigma hrho⟩

theorem exists_mscPhysicalOverlapMarkushevichNonBesselRealization
    (rho : ℂ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hrho : 1 / 2 < rho.re) (hrho1 : rho.re ≤ 1) :
    ∃ (modes : ℕ → H) (source overlap : H) (dual : ℕ → H),
      IsMSCPhysicalOverlapMarkushevichHilbertRealization
          rho sigma modes source overlap dual ∧
        ∀ B : ℝ, ∃ packet : Finset ℕ, ∃ x : H,
          B * ‖x‖ ^ 2 <
            ∑ n ∈ packet,
              ‖inner ℂ
                (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes n) x‖ ^ 2 := by
  refine ⟨mode rho sigma, sourceVector rho hsigma hrho, overlapVector rho hsigma hrho,
    normalizedDual rho sigma,
    isMSCPhysicalOverlapMarkushevichHilbertRealization rho hsigma hrho, ?_⟩
  intro B
  exact RHTower.HedenmalmThetaSource.exists_besselViolation_of_re_le_one
    rho hsigma hrho1 (mode rho sigma) (sourceVector rho hsigma hrho)
      (overlapVector rho hsigma hrho)
        (isMSCPhysicalOverlapHilbertRealization rho hsigma hrho) B

/-- Strict-right route kill. The physical four-unit MSC regular germ coexists with an explicit
positive Markushevich-basis realization of both literal arithmetic columns. The normalized modes
and their explicit biorthogonal dual are both complete, yet every finite Bessel bound fails. Thus
source-side M-basis rigidity alone cannot imply the MSC stability premise needed for RH. -/
theorem strictRightXiZero_mscMarkushevichSingularRouteKill
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : RHTower.xi rho = 0) {sigma : ℝ} (hsigma : 1 < sigma) :
    (∃ k : ℕ, analyticOrderAt RHTower.xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        (∀ tau : ℝ, 1 < tau →
          AnalyticAt ℂ (RHTower.mscPhysicalRegularGerm rho g tau)
              (RHTower.mscPhysicalZeroCoordinate rho tau) ∧
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v /
                GaloisForLFunctions.squarefreeBoundaryOverlap
                  (tau : ℂ) ((tau - 1 : ℝ) : ℂ) v) =ᶠ[
              𝓝[≠] (RHTower.mscPhysicalZeroCoordinate rho tau)]
                fun v => 2 * ((k + 1 : ℕ) : ℂ) /
                  (v - RHTower.mscPhysicalZeroCoordinate rho tau) +
                    RHTower.mscPhysicalRegularGerm rho g tau v) ∧
          Tendsto
            (fun tau : ℝ =>
              Complex.normSq
                (RHTower.mscPhysicalRegularGerm rho g tau
                  (RHTower.mscPhysicalZeroCoordinate rho tau)))
            (nhdsWithin 1 (Set.Ioi 1)) (nhds 4)) ∧
      ∃ (modes : ℕ → H) (source overlap : H) (dual : ℕ → H),
        IsMSCPhysicalOverlapMarkushevichHilbertRealization
            rho sigma modes source overlap dual ∧
          ∀ B : ℝ, ∃ packet : Finset ℕ, ∃ x : H,
            B * ‖x‖ ^ 2 <
              ∑ n ∈ packet,
                ‖inner ℂ
                  (RHTower.HedenmalmThetaSource.mscSignGaugeNormalizedMode modes n) x‖ ^ 2 := by
  have hM := isMSCPhysicalOverlapMarkushevichHilbertRealization rho hsigma hhalf
  have hwall :=
    RHTower.HedenmalmThetaSource.strictRightXiZero_mscBesselHilbertStabilityWall
      hhalf hone hzero hsigma (mode rho sigma) (sourceVector rho hsigma hhalf)
        (overlapVector rho hsigma hhalf)
  rcases hwall with ⟨hregular, _, hviolation⟩
  exact ⟨hregular, mode rho sigma, sourceVector rho hsigma hhalf,
    overlapVector rho hsigma hhalf, normalizedDual rho sigma, hM, hviolation hM.1⟩

end RHTower.HedenmalmThetaSource.MarkushevichSingular
