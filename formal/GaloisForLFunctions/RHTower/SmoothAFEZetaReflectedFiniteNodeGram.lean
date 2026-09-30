import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Field.Pi
import GaloisForLFunctions.RHTower.SteinhausFiniteNodePowerMinor
import GaloisForLFunctions.RHTower.SteinhausTerminalColoredMinors

/-!
# Literal reflected-AFE finite-node Gram lower bound

At fixed distinct right-strip nodes, a common height shift factors out of the
normalized terminal power minor as unit-modulus column phases. The chi envelope
supplies one inverse square-root conductor factor per node; the ordinary cutoff
stays uniformly positive on an inner interval. Ordered fixed sample intervals
supply linearly many prime–cofactor features each. Summing their squared minors
cancels the conductor scale and gives a height-uniform positive determinant for
the literal arithmetic mean covariance matrix.
-/

open Filter Matrix Set Topology
namespace GaloisForLFunctions.RHTower
noncomputable section

/-- Fixed disjoint normalized intervals carrying a common positive power-minor floor. -/
theorem exists_ordered_power_minor_intervals {J : ℕ} {β : Fin J → ℂ}
    (hβ : Function.Injective β) :
    ∃ a b : Fin J → ℝ, ∃ c : ℝ, 0 < c ∧
      (∀ j, 0 < a j ∧ a j < b j ∧ b j < 1) ∧
      (∀ i j, i < j → b i < a j) ∧
      ∀ u : Fin J → ℝ, (∀ j, u j ∈ Ioc (a j) (b j)) →
        c ≤ ‖(finiteNodePowerEvaluationMatrix β (fun j => (Real.log (u j) : ℂ))).det‖ := by
  classical
  obtain ⟨p, hp, hpI, hpdet⟩ :=
    exists_realComplexInterval_powerEvaluation_det_isUnit hβ (a := -1) (b := 0)
      (by norm_num)
  have hre : Function.Injective (fun j => (p j).re) := by
    intro i j hij
    apply hp
    apply Complex.ext hij
    rw [(hpI i).1, (hpI j).1]
  let e := Tuple.sort (fun j => (p j).re)
  let x : Fin J → ℝ := fun j => (p (e j)).re
  have hxmono : StrictMono x :=
    (Tuple.monotone_sort (fun j => (p j).re)).strictMono_of_injective
      (hre.comp e.injective)
  have hxneg : ∀ j, x j < 0 := fun j => (hpI (e j)).2.2
  have hpcast : ∀ j, ((x j : ℝ) : ℂ) = p (e j) := by
    intro j
    apply Complex.ext
    · rfl
    · simpa using (hpI (e j)).1.symm
  have hxdet : IsUnit (finiteNodePowerEvaluationMatrix β (fun j => (x j : ℂ))).det := by
    have hmat : finiteNodePowerEvaluationMatrix β (fun j => (x j : ℂ)) =
        (finiteNodePowerEvaluationMatrix β p).submatrix e id := by
      ext i j
      simp [finiteNodePowerEvaluationMatrix, hpcast]
    rw [hmat, Matrix.det_permute]
    exact ((Equiv.Perm.sign e).isUnit.map (Int.castRingHom ℂ)).mul hpdet
  obtain ⟨ε, c, hε, hc, hclose⟩ :=
    exists_powerEvaluation_det_norm_lower_neighborhood β (fun j => (x j : ℂ)) hxdet
  obtain ⟨η, hη, hxη⟩ := Pi.exists_forall_pos_add_lt hxneg
  let gap : Fin J × Fin J → ℝ := fun ij =>
    if ij.1 < ij.2 then (x ij.2 - x ij.1) / 3 else 1
  have hgap : ∀ ij, (0 : ℝ) < gap ij := by
    intro ij
    dsimp only [gap]
    split_ifs with h
    · exact div_pos (sub_pos.mpr (hxmono h)) (by norm_num)
    · norm_num
  obtain ⟨γ, hγ, hγgap⟩ := Pi.exists_forall_pos_add_lt hgap
  let δ : ℝ := min (ε / 2) (min (η / 2) (γ / 2))
  have hδ : 0 < δ := lt_min (half_pos hε) (lt_min (half_pos hη) (half_pos hγ))
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδη : δ ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδγ : δ ≤ γ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨fun j => Real.exp (x j - δ), fun j => Real.exp (x j + δ), c, hc, ?_, ?_, ?_⟩
  · intro j
    refine ⟨Real.exp_pos _, Real.exp_lt_exp.mpr (by linarith),
      Real.exp_lt_one_iff.mpr ?_⟩
    have := hxη j
    linarith
  · intro i j hij
    apply Real.exp_lt_exp.mpr
    have hg := hγgap (i,j)
    simp only [gap, hij, if_pos, zero_add] at hg
    linarith
  · intro u hu
    apply hclose
    intro j
    have hu0 : 0 < u j := (Real.exp_pos _).trans (hu j).1
    have hlo : x j - δ < Real.log (u j) := by
      have := Real.strictMonoOn_log (show Real.exp (x j - δ) ∈ Ioi (0 : ℝ) from Real.exp_pos _)
        hu0 (hu j).1
      simpa only [Real.log_exp] using this
    have hhi : Real.log (u j) ≤ x j + δ := by
      exact (Real.log_le_iff_le_exp hu0).mpr (hu j).2
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
    rw [Real.norm_eq_abs]
    apply abs_lt.mpr
    constructor <;> linarith
end
end GaloisForLFunctions.RHTower

open Complex Finset Matrix
open GaloisForLFunctions.RHTower
namespace RHTower
noncomputable section

private theorem terminal_cpow_factor {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (β : ℂ) (τ : ℝ) :
    ((x * y : ℝ) : ℂ) ^ (β + (τ : ℂ) * I) =
      (x : ℂ) ^ (β + (τ : ℂ) * I) *
        (y : ℂ) ^ ((τ : ℂ) * I) * exp (β * (Real.log y : ℂ)) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le hy.le,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') β,
    ← Complex.ofReal_log hy.le, mul_comm (↑(Real.log y)) β]
  ring

/-- Exact separation of the common moving height from the fixed node shape. -/
theorem reflectedPrimalPositiveCoefficient_factor
    (d b τ r : ℝ) {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    smoothAFEZetaRightReflectedPrimalPositiveCoefficient d (τ + b) r N n =
      (zetaChi (rightDisplacedLinePt d (τ + b)) *
        (N : ℂ) ^ (rightDisplacedLinePt d (τ + b) - 1)) *
      (((n : ℝ) / N : ℝ) : ℂ) ^ ((τ : ℂ) * I) *
      smoothAFECutoff (r * ((n : ℝ) / N)) *
      exp ((rightDisplacedLinePt d b - 1) *
        (Real.log ((n : ℝ) / N) : ℂ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hexp : rightDisplacedLinePt d (τ + b) - 1 =
      (rightDisplacedLinePt d b - 1) + (τ : ℂ) * I := by
    simp only [rightDisplacedLinePt, Complex.ofReal_add]
    ring
  have hpow := terminal_cpow_factor hNR (div_pos hnR hNR)
    (rightDisplacedLinePt d b - 1) τ
  rw [mul_div_cancel₀ _ hNR.ne', ← hexp] at hpow
  simp only [Complex.ofReal_natCast] at hpow
  unfold smoothAFEZetaRightReflectedPrimalPositiveCoefficient
    smoothAFEZetaRightReflectedPrimalCoefficient
  have hidxC : (↑(n - 1) + 1 : ℂ) = n := by exact_mod_cast hindex
  have hidxR : (↑(n - 1) + 1 : ℝ) = n := by exact_mod_cast hindex
  rw [hidxC, hidxR, hpow]
  have hcut : (n : ℝ) / ((N : ℝ) / r) = r * ((n : ℝ) / N) := by
    simp only [div_div_eq_mul_div]; ring
  rw [hcut]
  ring

/-- The terminal coefficient minor retains precisely the fixed node power determinant.
The common height contributes only column phases of modulus one. -/
theorem norm_reflectedPrimalFiniteNode_minor_eq
    {J : ℕ} (d b : Fin J → ℝ) (τ r : ℝ) {N : ℕ} (hN : 0 < N)
    (n : Fin J → ℕ) (hn : ∀ j, 0 < n j) :
    ‖(Matrix.of fun i j =>
      smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient
        d (fun i => τ + b i) r N i (n j)).det‖ =
      (∏ i, ‖zetaChi (rightDisplacedLinePt (d i) (τ + b i))‖ *
        (N : ℝ) ^ (d i - 1 / 2)) *
      (∏ j, ‖smoothAFECutoff (r * ((n j : ℝ) / N))‖) *
      ‖(finiteNodePowerEvaluationMatrix (fun i => rightDisplacedLinePt (d i) (b i) - 1)
        (fun j => (Real.log ((n j : ℝ) / N) : ℂ))).det‖ := by
  let A : Fin J → ℂ := fun i =>
    zetaChi (rightDisplacedLinePt (d i) (τ + b i)) *
      (N : ℂ) ^ (rightDisplacedLinePt (d i) (τ + b i) - 1)
  let B : Fin J → ℂ := fun j =>
    (((n j : ℝ) / N : ℝ) : ℂ) ^ ((τ : ℂ) * I) *
      smoothAFECutoff (r * ((n j : ℝ) / N))
  let P : Matrix (Fin J) (Fin J) ℂ := finiteNodePowerEvaluationMatrix
    (fun i => rightDisplacedLinePt (d i) (b i) - 1)
    (fun j => (Real.log ((n j : ℝ) / N) : ℂ))
  have hmat : (Matrix.of fun i j =>
      smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient
        d (fun i => τ + b i) r N i (n j)) =
      Matrix.of (fun i j => A i * (B j * P.transpose i j)) := by
    ext i j
    dsimp [smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient, A, B,
      P, finiteNodePowerEvaluationMatrix]
    rw [reflectedPrimalPositiveCoefficient_factor _ _ _ _ hN (hn j)]
    ring
  have hdet : (Matrix.of fun i j => A i * (B j * P.transpose i j)).det =
      (∏ i, A i) * ((∏ j, B j) * P.det) := by
    calc
      _ = (∏ i, A i) * (Matrix.of fun i j => B j * P.transpose i j).det :=
        Matrix.det_mul_column A _
      _ = (∏ i, A i) * ((∏ j, B j) * P.transpose.det) :=
        congrArg (fun z => (∏ i, A i) * z) (Matrix.det_mul_row B P.transpose)
      _ = _ := by rw [Matrix.det_transpose]
  rw [hmat, hdet, norm_mul, norm_mul, norm_prod, norm_prod]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : ∀ i, ‖A i‖ = ‖zetaChi (rightDisplacedLinePt (d i) (τ + b i))‖ *
      (N : ℝ) ^ (d i - 1 / 2) := by
    intro i
    dsimp only [A]
    rw [norm_mul]
    have hpow := Complex.norm_cpow_eq_rpow_re_of_pos hNR
      (rightDisplacedLinePt (d i) (τ + b i) - 1)
    have hre : (rightDisplacedLinePt (d i) (τ + b i) - 1).re = d i - 1 / 2 := by
      simp only [Complex.sub_re, rightDisplacedLinePt_re, Complex.one_re]; ring
    rw [hre] at hpow
    simpa using congrArg (fun x => ‖zetaChi (rightDisplacedLinePt (d i) (τ + b i))‖ * x) hpow
  have hB : ∀ j, ‖B j‖ = ‖smoothAFECutoff (r * ((n j : ℝ) / N))‖ := by
    intro j
    dsimp only [B]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos (by exact_mod_cast hn j) hNR)]
    simp
  simp_rw [hA, hB]
  exact (mul_assoc _ _ _).symm

/-- The common-height literal minor has the natural `N^(-J/2)` floor on fixed
normalized terminal intervals. All analytic constants are supplied by the literal chi and cutoff. -/
theorem exists_reflectedPrimalFiniteNode_minor_floor
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j))) :
    ∃ r c : ℝ, ∃ a z : Fin J → ℝ, 0 < r ∧ 0 < c ∧
      (∀ j, 0 < a j ∧ a j < z j ∧ z j < 1) ∧
      (∀ i j, i < j → z i < a j) ∧
      ∀ {N : ℕ}, 0 < N → ∀ τ : ℝ,
        (∀ i, τ + b i ∈ Set.Icc (N : ℝ) (2 * N : ℝ)) →
        ∀ n : Fin J → ℕ,
          (∀ j, (n j : ℝ) / N ∈ Set.Ioc (a j) (z j)) →
          c * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ J ≤
            ‖(Matrix.of fun i j =>
              smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient
                d (fun i => τ + b i) r N i (n j)).det‖ := by
  have hβ : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j) - 1) := by
    intro i j h
    exact hinj (sub_left_injective h)
  obtain ⟨a, z, c₀, hc₀, haz, hsep, hshape⟩ := exists_ordered_power_minor_intervals hβ
  obtain ⟨r, hr, hcut⟩ := exists_smoothAFECutoff_inner_norm_lower
  choose k hk hchi using fun j => exists_norm_zetaChi_rightDisplaced_ge_nat_window (hd j) (hdhalf j)
  let K : ℝ := ∏ j, k j
  have hK : 0 < K := Finset.prod_pos fun j _ => hk j
  refine ⟨r, K * (1 / 2 : ℝ) ^ J * c₀, a, z, hr, by positivity, haz, hsep, ?_⟩
  intro N hN τ hτ n hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnp : ∀ j, 0 < n j := by
    intro j
    have hu : 0 < (n j : ℝ) / N := (haz j).1.trans (hn j).1
    have : (0 : ℝ) < n j := (div_pos_iff.mp hu).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge hNR.le h.2))
    exact_mod_cast this
  rw [norm_reflectedPrimalFiniteNode_minor_eq d b τ r hN n hnp]
  have hrows : K * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ J ≤
      ∏ i, ‖zetaChi (rightDisplacedLinePt (d i) (τ + b i))‖ *
        (N : ℝ) ^ (d i - 1 / 2) := by
    calc
      K * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ J =
          ∏ i, k i * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        simp [K, Finset.prod_mul_distrib]
      _ ≤ _ := Finset.prod_le_prod (fun i _ => mul_nonneg (hk i).le (Real.rpow_nonneg hNR.le _)) (fun i _ => by
        have h := mul_le_mul_of_nonneg_right (hchi i hN (τ + b i) (hτ i))
          (Real.rpow_nonneg hNR.le (d i - 1 / 2))
        have heq : k i * (N : ℝ) ^ (-d i) * (N : ℝ) ^ (d i - 1 / 2) =
            k i * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hNR]
          congr 2
          ring
        rwa [heq] at h)
  have hcuts : (1 / 2 : ℝ) ^ J ≤ ∏ j, ‖smoothAFECutoff (r * ((n j : ℝ) / N))‖ := by
    calc
      (1 / 2 : ℝ) ^ J = ∏ _j : Fin J, (1 / 2 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => by
        apply hcut (mul_pos hr ((haz j).1.trans (hn j).1))
        have hu : (n j : ℝ) / N ≤ 1 := (hn j).2.trans (haz j).2.2.le
        simpa using mul_le_mul_of_nonneg_left hu hr.le)
  have hprod := mul_le_mul hrows hcuts (by positivity) (Finset.prod_nonneg fun i _ => by positivity)
  have hfull := mul_le_mul hprod (hshape _ hn) hc₀.le (by positivity)
  calc
    (K * (1 / 2 : ℝ) ^ J * c₀) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ J =
        ((K * ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ J) * (1 / 2 : ℝ) ^ J) * c₀ := by ring
    _ ≤ _ := hfull

/-- The literal reflected-primal arithmetic Gram determinant is uniformly positive
for every fixed distinct finite node family in the strict right strip. -/
theorem exists_eventually_reflectedPrimalFiniteNode_gram_det_lower
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j))) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ τ : ℝ, (∀ j, τ + b j ∈ Set.Icc (N : ℝ) (2 * N : ℝ)) →
        c ≤ (steinhausFiniteNodeArithmeticGram (terminalPrimePowerWindow N)
          (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient
            d (fun j => τ + b j) r N) N).det.re := by
  obtain ⟨r, c, a, z, hr, hc, haz, hsep, hminor⟩ :=
    exists_reflectedPrimalFiniteNode_minor_floor d b hd hdhalf hinj
  obtain ⟨C, hC, hcount⟩ :=
    exists_eventually_prod_terminal_normalizedProductFeatureBlock_card_ge_pow
      (fun j => (haz j).1.le) (fun j => (haz j).2.1) (fun j => (haz j).2.2.le)
  refine ⟨r, C * c ^ 2, hr, by positivity, ?_⟩
  filter_upwards [hcount, Filter.eventually_ge_atTop 1] with N hcount hN
  intro τ hτ
  have hNp : 0 < N := hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  let v : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ))
  have hv : 0 < v := Real.rpow_pos_of_pos hNR _
  have hunit : (N : ℝ) * v ^ 2 = 1 := by
    dsimp only [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNR.le]
    norm_num
    rw [Real.rpow_neg_one]
    exact mul_inv_cancel₀ hNR.ne'
  have hscale : (N : ℝ) ^ J * (v ^ J) ^ 2 = 1 := by
    calc
      (N : ℝ) ^ J * (v ^ J) ^ 2 = ((N : ℝ) * v ^ 2) ^ J := by
        rw [mul_pow]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm J 2]
      _ = 1 := by rw [hunit, one_pow]
  have hbound := prod_normalizedProductBlock_card_mul_sq_le_arithmeticGram_det_re
    (terminalPrimePowerWindow N) a z N (fun i j hij => (hsep i j hij).le)
    (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient d (fun j => τ + b j) r N)
    (c := c * v ^ J) (by positivity) (by
      intro q
      apply hminor hNp τ hτ (fun j => (q j).1.1.1 * (q j).1.1.2)
      intro j
      have hq := mem_steinhausFiniteNodeNormalizedProductBlock.mp (q j).2
      exact ⟨(lt_div_iff₀ hNR).mpr hq.1, (div_le_iff₀ hNR).mpr hq.2⟩)
  calc
    C * c ^ 2 = C * c ^ 2 * ((N : ℝ) ^ J * (v ^ J) ^ 2) := by rw [hscale, mul_one]
    _ = (C * (N : ℝ) ^ J) * (c * v ^ J) ^ 2 := by ring
    _ ≤ ((∏ j, (steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) (a j) (z j) N).card : ℕ) : ℝ) *
          (c * v ^ J) ^ 2 := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ ≤ _ := hbound

/-- Uniform literal covariance-volume floor on an interval of moving heights of length `N/2`.
The node offsets and the normalized cutoff are fixed before the height tends to infinity. -/
theorem exists_eventually_reflectedPrimalFiniteNode_gram_det_lower_height_window
    {J : ℕ} (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j))) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ τ ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
        c ≤ (steinhausFiniteNodeArithmeticGram (terminalPrimePowerWindow N)
          (smoothAFEZetaRightReflectedPrimalFiniteNodeCoefficient
            d (fun j => τ + b j) r N) N).det.re := by
  obtain ⟨r, c, hr, hc, hgram⟩ :=
    exists_eventually_reflectedPrimalFiniteNode_gram_det_lower d b hd hdhalf hinj
  have hoffset : ∀ᶠ N : ℕ in Filter.atTop, ∀ j, 4 * |b j| ≤ (N : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : ℕ => (N : ℝ))
      Filter.atTop Filter.atTop).eventually (Filter.eventually_ge_atTop (4 * |b j|))
  refine ⟨r, c, hr, hc, ?_⟩
  filter_upwards [hgram, hoffset] with N hN hbN
  intro τ hτ
  apply hN τ
  intro j
  have hlo := neg_abs_le (b j)
  have hhi := le_abs_self (b j)
  have hb := hbN j
  constructor <;> linarith [hτ.1, hτ.2]

end
end RHTower
