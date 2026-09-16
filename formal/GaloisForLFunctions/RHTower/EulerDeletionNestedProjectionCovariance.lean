import GaloisForLFunctions.RHTower.EulerDeletionWeightedResidueProjection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumOverResidueClass

/-!
# Nested-history covariance of the Euler-deletion drift

The chronological residue histories are nested.  Consequently, each cross-time covariance of
conditional residue predictors reduces exactly to an earlier predictor paired with the raw later
residue.  The resulting triangular covariance is the literal multi-prime quantity that must be
controlled; no periodic averaging, absolute value, or one-prime replacement occurs here.
-/

noncomputable section
set_option autoImplicit false

open Finset MeasureTheory Filter Topology
open scoped BigOperators Interval

namespace RHTower.DeletionResidueMartingale

/-- The literal physical cell mass is exactly a beta-geometric mixture weight.  This preserves
the original nonuniform measure and is the starting point for a source-faithful fibre analysis. -/
theorem cellWeight_eq_beta_interval_integral (j : ℕ) :
    cellWeight j = ∫ x in (0 : ℝ)..1, (1 - x) * x ^ j := by
  rw [show (fun x : ℝ => (1 - x) * x ^ j) = fun x => x ^ j - x ^ (j + 1) by
    funext x
    ring]
  rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_pow j)
    (intervalIntegral.intervalIntegrable_pow (j + 1)), integral_pow, integral_pow]
  unfold cellWeight
  push_cast
  field_simp
  ring

/-- Every finite physical arithmetic-progression mass is one beta-geometric integral with the
literal finite progression kernel.  No period completion or averaging is introduced. -/
theorem cellWeight_clock_progression_prefix_eq_beta (L r K : ℕ) :
    (∑ k ∈ range K, cellWeight (r + k * clock L)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
        ∑ k ∈ range K, x ^ (k * clock L) := by
  calc
    (∑ k ∈ range K, cellWeight (r + k * clock L)) =
        ∑ k ∈ range K, ∫ x in (0 : ℝ)..1, (1 - x) * x ^ (r + k * clock L) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact cellWeight_eq_beta_interval_integral (r + k * clock L)
    _ = ∫ x in (0 : ℝ)..1, ∑ k ∈ range K,
          (1 - x) * x ^ (r + k * clock L) := by
      rw [intervalIntegral.integral_finsetSum]
      intro k hk
      exact ((continuous_const.sub continuous_id).mul
        (continuous_id.pow (r + k * clock L))).intervalIntegrable _ _
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (∑ k ∈ range K, (1 - x) * x ^ (r + k * clock L)) =
        (1 - x) * x ^ r * ∑ k ∈ range K, x ^ (k * clock L)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_add]
      ring

/-- The finite physical numerator of a residue fibre is an exact beta-geometric integral.  The
finite prefix and every signed residue value remain inside the kernel, so this introduces neither
a completed period nor an averaged surrogate. -/
theorem finite_fibre_residue_numerator_eq_beta (n L r K : ℕ) :
    (∑ k ∈ range K,
      cellWeight (r + k * clock L) * residue n (r + k * clock L)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
        ∑ k ∈ range K, x ^ (k * clock L) * residue n (r + k * clock L) := by
  calc
    (∑ k ∈ range K,
        cellWeight (r + k * clock L) * residue n (r + k * clock L)) =
        ∑ k ∈ range K,
          (∫ x in (0 : ℝ)..1, (1 - x) * x ^ (r + k * clock L)) *
            residue n (r + k * clock L) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← cellWeight_eq_beta_interval_integral]
    _ = ∑ k ∈ range K, ∫ x in (0 : ℝ)..1,
          ((1 - x) * x ^ (r + k * clock L)) * residue n (r + k * clock L) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_mul_const]
    _ = ∫ x in (0 : ℝ)..1, ∑ k ∈ range K,
          ((1 - x) * x ^ (r + k * clock L)) * residue n (r + k * clock L) := by
      rw [intervalIntegral.integral_finsetSum]
      intro k hk
      exact (((continuous_const.sub continuous_id).mul
        (continuous_id.pow (r + k * clock L))).mul continuous_const).intervalIntegrable _ _
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (∑ k ∈ range K,
        ((1 - x) * x ^ (r + k * clock L)) * residue n (r + k * clock L)) =
        (1 - x) * x ^ r * ∑ k ∈ range K,
          x ^ (k * clock L) * residue n (r + k * clock L)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_add]
      ring

/-- A residue numerator is unchanged by any physical shift divisible by its modulus.  Applied to
`q = n * clock L`, this identifies the exact period of the signed numerator kernel along a
chronological fibre; it does not replace a finite fibre prefix by a period average. -/
theorem residue_add_eq_of_dvd {n j q : ℕ} (hq : n ∣ q) :
    residue n (j + q) = residue n j := by
  rcases hq with ⟨t, rfl⟩
  unfold residue
  congr 1
  rw [show j + n * t + 1 = (j + 1) + n * t by omega]
  simp

/-- Along an actual clock progression, the residue numerator has its literal modulus period.
The equality is pointwise in the progression index and keeps every finite prefix intact. -/
theorem residue_clock_progression_periodic (n L r k : ℕ) :
    residue n (r + (k + n) * clock L) = residue n (r + k * clock L) := by
  rw [show r + (k + n) * clock L = (r + k * clock L) + n * clock L by
    rw [Nat.add_mul]
    exact Nat.add_assoc _ _ _ |>.symm]
  exact residue_add_eq_of_dvd (dvd_mul_right n (clock L))

/-- Inside the physical beta interval, every literal residue kernel along a clock progression is
summable.  This is only geometric damping from `x < 1`; no Möbius sign is removed or bounded. -/
theorem summable_residue_clock_kernel (n L r : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun k : ℕ => x ^ (k * clock L) * residue n (r + k * clock L)) := by
  have hclock : 0 < clock L := clock_pos L
  have hxclock0 : 0 ≤ x ^ clock L := pow_nonneg hx0 _
  have hxclock1 : x ^ clock L < 1 :=
    pow_lt_one₀ hx0 hx1 hclock.ne'
  have hgeom : Summable (fun k : ℕ => (x ^ clock L) ^ k) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg hxclock0]
    exact hxclock1
  apply Summable.of_norm_bounded hgeom
  intro k
  have hxpow : 0 ≤ x ^ (k * clock L) := pow_nonneg hx0 _
  have hres := residue_bounds n (r + k * clock L)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxpow hres.1)]
  calc
    x ^ (k * clock L) * residue n (r + k * clock L) ≤ x ^ (k * clock L) :=
      mul_le_of_le_one_right hxpow hres.2
    _ = (x ^ clock L) ^ k := by rw [← pow_mul, Nat.mul_comm]

/-- Exact periodic resolvent of the literal infinite residue kernel for an interior beta point.
It is a reindexing of the original `tsum` by residue classes, not a replacement of a finite
physical prefix by a completed or averaged column. -/
theorem residue_clock_kernel_tsum_eq_periodic_geometric (n L r : ℕ) [NeZero n] {x : ℝ}
    (hn : 0 < n) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑' k : ℕ, x ^ (k * clock L) * residue n (r + k * clock L)) =
      ∑ s : ZMod n, (x ^ (s.val * clock L) * residue n (r + s.val * clock L)) *
        (1 - x ^ (n * clock L))⁻¹ := by
  have hsum := summable_residue_clock_kernel n L r hx0 hx1
  calc
    (∑' k : ℕ, x ^ (k * clock L) * residue n (r + k * clock L)) =
        ∑ s : ZMod n, ∑' k : ℕ,
          x ^ ((s.val + n * k) * clock L) * residue n
            (r + (s.val + n * k) * clock L) :=
      Nat.sumByResidueClasses hsum n
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [show (fun k : ℕ =>
          x ^ ((s.val + n * k) * clock L) * residue n
            (r + (s.val + n * k) * clock L)) =
          fun k => (x ^ (s.val * clock L) * residue n (r + s.val * clock L)) *
            (x ^ (n * clock L)) ^ k by
          funext k
          have harg : r + (s.val + n * k) * clock L =
              (r + s.val * clock L) + n * (k * clock L) := by
            rw [Nat.add_mul]
            ac_rfl
          have hexp : (s.val + n * k) * clock L =
              s.val * clock L + k * (n * clock L) := by
            rw [Nat.add_mul]
            ac_rfl
          have hpow : x ^ (k * (n * clock L)) = (x ^ (n * clock L)) ^ k := by
            calc
              x ^ (k * (n * clock L)) = x ^ ((n * clock L) * k) := by
                congr 1
                ac_rfl
              _ = (x ^ (n * clock L)) ^ k := pow_mul x (n * clock L) k
          rw [harg, residue_add_eq_of_dvd (dvd_mul_right n (k * clock L)), hexp, pow_add, hpow]
          ring]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (pow_nonneg hx0 _)
        (pow_lt_one₀ hx0 hx1 (Nat.mul_ne_zero hn.ne' (clock_pos L).ne'))]

/-- An aligned finite physical prefix has an exact quotient--remainder block reindexing.  This is
only a bijective enumeration of its actual cells; the two finite factors are not period averages. -/
theorem sum_fin_block_decomposition (n K : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin (K * n), f k) =
      ∑ qs : Fin K × Fin n, f (qs.2 + n * qs.1) := by
  exact (Fintype.sum_equiv (finProdFinEquiv) _ _ (by
    intro qs
    rfl)).symm

/-- The signed residue kernel of an aligned finite physical prefix factors exactly into its
literal modulus block and its finite geometric block.  This is a finite equality of the original
cells, not a completed column or a period average. -/
theorem finite_residue_kernel_block_factorization (n L r K : ℕ) (x : ℝ) :
    (∑ k : Fin (K * n), x ^ (k * clock L) * residue n (r + k * clock L)) =
      (∑ s : Fin n, x ^ (s * clock L) * residue n (r + s * clock L)) *
        ∑ q : Fin K, x ^ (q * n * clock L) := by
  calc
    (∑ k : Fin (K * n), x ^ (k * clock L) * residue n (r + k * clock L)) =
        ∑ qs : Fin K × Fin n,
          x ^ ((qs.2 + n * qs.1) * clock L) *
            residue n (r + (qs.2 + n * qs.1) * clock L) :=
      sum_fin_block_decomposition n K
        (fun k => x ^ (k * clock L) * residue n (r + k * clock L))
    _ = ∑ q : Fin K, ∑ s : Fin n,
          x ^ ((s + n * q) * clock L) * residue n (r + (s + n * q) * clock L) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ s : Fin n, ∑ q : Fin K,
          x ^ ((s + n * q) * clock L) * residue n (r + (s + n * q) * clock L) := by
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have harg : r + (s + n * q) * clock L =
          (r + s * clock L) + n * (q * clock L) := by
        calc
          r + (s + n * q) * clock L = r + (s * clock L + (n * q) * clock L) := by
            rw [Nat.add_mul]
          _ = (r + s * clock L) + (n * q) * clock L := (Nat.add_assoc _ _ _).symm
          _ = (r + s * clock L) + n * (q * clock L) := by rw [Nat.mul_assoc]
      have hexp : (s + n * q) * clock L = s * clock L + q * n * clock L := by
        rw [Nat.add_mul, Nat.mul_comm n q]
      rw [harg, residue_add_eq_of_dvd (dvd_mul_right n (q * clock L)), hexp, pow_add]
      ring

/-- An aligned finite physical fibre numerator is a beta integral whose kernel factors into the
literal signed modulus block and a finite geometric block.  No limiting completion is taken. -/
theorem finite_fibre_residue_aligned_block_eq_beta (n L r K : ℕ) :
    (∑ k ∈ range (K * n),
      cellWeight (r + k * clock L) * residue n (r + k * clock L)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
        ((∑ s : Fin n, x ^ (s * clock L) * residue n (r + s * clock L)) *
          ∑ q : Fin K, x ^ (q * n * clock L)) := by
  calc
    (∑ k ∈ range (K * n),
        cellWeight (r + k * clock L) * residue n (r + k * clock L)) =
        ∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
          ∑ k ∈ range (K * n), x ^ (k * clock L) * residue n (r + k * clock L) :=
      finite_fibre_residue_numerator_eq_beta n L r (K * n)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (1 - x) * x ^ r *
          ∑ k ∈ range (K * n), x ^ (k * clock L) * residue n (r + k * clock L) =
        (1 - x) * x ^ r *
          ((∑ s : Fin n, x ^ (s * clock L) * residue n (r + s * clock L)) *
            ∑ q : Fin K, x ^ (q * n * clock L))
      congr 1
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => x ^ (k * clock L) * residue n (r + k * clock L)) (K * n)]
      exact finite_residue_kernel_block_factorization n L r K x

/-- Every literal physical fibre mass is summable under the original cell law. -/
theorem summable_fibre_weight_progression (L r : ℕ) :
    Summable (fun k : ℕ => cellWeight (r + k * clock L)) := by
  change Summable (cellWeight ∘ fun k : ℕ => r + k * clock L)
  exact hasSum_cellWeight.summable.comp_injective (i := fun k : ℕ => r + k * clock L)
    (fun a b hab => Nat.mul_right_cancel (clock_pos L) (Nat.add_left_cancel hab))

/-- Every literal residue numerator along a physical chronological fibre is summable under the
original cell law.  This supplies the convergence needed to pass finite aligned-prefix identities
to the actual infinite fibre, without bounding or separating the later Möbius tail. -/
theorem summable_fibre_residue_progression (n L r : ℕ) :
    Summable (fun k : ℕ =>
      cellWeight (r + k * clock L) * residue n (r + k * clock L)) := by
  have hweight := summable_fibre_weight_progression L r
  apply Summable.of_norm_bounded hweight
  intro k
  have hw : 0 ≤ cellWeight (r + k * clock L) := by unfold cellWeight; positivity
  have hres := residue_bounds n (r + k * clock L)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hres.1)]
  exact mul_le_of_le_one_right hw hres.2

/-- One literal fibre-residue term as a beta kernel on the physical interval. -/
def fibreResidueBetaKernel (n L r k : ℕ) (x : ℝ) : ℝ :=
  (1 - x) * x ^ (r + k * clock L) * residue n (r + k * clock L)

/-- Each physical beta kernel is integrable on the original interval. -/
theorem fibreResidueBetaKernel_integrable (n L r k : ℕ) :
    Integrable (fibreResidueBetaKernel n L r k)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  change IntegrableOn (fibreResidueBetaKernel n L r k) (Set.Ioc (0 : ℝ) 1) volume
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
  exact (((continuous_const.sub continuous_id).mul
    (continuous_id.pow (r + k * clock L))).mul continuous_const).intervalIntegrable _ _

/-- The norm mass of a beta kernel is exactly the original nonuniform cell-residue mass. -/
theorem fibreResidueBetaKernel_norm_integral_eq_physical (n L r k : ℕ) :
    (∫ x, ‖fibreResidueBetaKernel n L r k x‖ ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      cellWeight (r + k * clock L) * residue n (r + k * clock L) := by
  calc
    (∫ x, ‖fibreResidueBetaKernel n L r k x‖ ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) =
        ∫ x in (0 : ℝ)..1, ‖fibreResidueBetaKernel n L r k x‖ :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = ∫ x in (0 : ℝ)..1, fibreResidueBetaKernel n L r k x := by
      apply intervalIntegral.integral_congr
      intro x hx
      change ‖fibreResidueBetaKernel n L r k x‖ = fibreResidueBetaKernel n L r k x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      change 0 ≤ (1 - x) * x ^ (r + k * clock L) * residue n (r + k * clock L)
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
      exact mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hx'.2) (pow_nonneg hx'.1 _))
        (residue_bounds n (r + k * clock L)).1
    _ = _ := by
      unfold fibreResidueBetaKernel
      rw [intervalIntegral.integral_mul_const, ← cellWeight_eq_beta_interval_integral]

/-- The beta-kernel family has summable norm integrals because these are exactly its physical
cell-residue masses. -/
theorem summable_fibreResidueBetaKernel_norm_integral (n L r : ℕ) :
    Summable (fun k : ℕ =>
      ∫ x, ‖fibreResidueBetaKernel n L r k x‖ ∂volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  exact (summable_fibre_residue_progression n L r).congr
    (fun k => (fibreResidueBetaKernel_norm_integral_eq_physical n L r k).symm)

/-- The infinite literal residue progression is its beta integral.  The `tsum` remains inside
the integrand and keeps every physical residue value; this is a dominated interchange under the
original cell law, not a period completion. -/
theorem fibre_residue_progression_eq_beta_tsum (n L r : ℕ) :
    (∑' k : ℕ, cellWeight (r + k * clock L) * residue n (r + k * clock L)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
        ∑' k : ℕ, x ^ (k * clock L) * residue n (r + k * clock L) := by
  calc
    (∑' k : ℕ, cellWeight (r + k * clock L) * residue n (r + k * clock L)) =
        ∑' k : ℕ, ∫ x, fibreResidueBetaKernel n L r k x ∂
          volume.restrict (Set.Ioc (0 : ℝ) 1) := by
      apply tsum_congr
      intro k
      rw [← fibreResidueBetaKernel_norm_integral_eq_physical n L r k]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))]
        with x hx
      change ‖fibreResidueBetaKernel n L r k x‖ = fibreResidueBetaKernel n L r k x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      change 0 ≤ (1 - x) * x ^ (r + k * clock L) * residue n (r + k * clock L)
      exact mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg hx.1.le _))
        (residue_bounds n (r + k * clock L)).1
    _ = ∫ x, ∑' k : ℕ, fibreResidueBetaKernel n L r k x ∂
          volume.restrict (Set.Ioc (0 : ℝ) 1) :=
      MeasureTheory.integral_tsum_of_summable_integral_norm
        (fibreResidueBetaKernel_integrable n L r)
        (summable_fibreResidueBetaKernel_norm_integral n L r)
    _ = ∫ x in (0 : ℝ)..1, ∑' k : ℕ, fibreResidueBetaKernel n L r k x :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      change (∑' k : ℕ, fibreResidueBetaKernel n L r k x) =
        (1 - x) * x ^ r * ∑' k : ℕ, x ^ (k * clock L) * residue n (r + k * clock L)
      rw [show (fun k : ℕ => fibreResidueBetaKernel n L r k x) =
          fun k => ((1 - x) * x ^ r) *
            (x ^ (k * clock L) * residue n (r + k * clock L)) by
          funext k
          unfold fibreResidueBetaKernel
          rw [pow_add]
          ring]
      rw [tsum_mul_left]

/-- A physical history fibre is exactly its chronological arithmetic progression. -/
def historyFibreProgressionEquiv (L r : ℕ) (hr : r < clock L) :
    ℕ ≃ historyFibre L r where
  toFun k := ⟨r + k * clock L, by
    simp [historyFibre, Nat.mod_eq_of_lt hr]⟩
  invFun j := j.1 / clock L
  left_inv k := by
    change (r + k * clock L) / clock L = k
    rw [Nat.mul_comm, Nat.add_mul_div_left _ _ (clock_pos L), Nat.div_eq_of_lt hr, zero_add]
  right_inv j := by
    apply Subtype.ext
    change r + (j.1 / clock L) * clock L = j.1
    have hj : j.1 % clock L = r := j.2
    calc
      r + (j.1 / clock L) * clock L = j.1 % clock L + clock L * (j.1 / clock L) := by
        rw [hj]
        ac_rfl
      _ = j.1 := Nat.mod_add_div j.1 (clock L)

/-- The literal numerator over a physical history fibre is its chronological progression sum. -/
theorem tsum_historyFibre_eq_progression (n L r : ℕ) (hr : r < clock L) :
    (∑' j : historyFibre L r, cellWeight j * residue n j) =
      ∑' k : ℕ, cellWeight (r + k * clock L) * residue n (r + k * clock L) := by
  exact (historyFibreProgressionEquiv L r hr).tsum_eq
    (fun j => cellWeight j * residue n j) |>.symm

/-- The quotient's original indicator numerator equals the same physical progression sum. -/
theorem weightedResidue_numerator_eq_progression (n L r : ℕ) (hr : r < clock L) :
    (∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (residue n) j)) =
      ∑' k : ℕ, cellWeight (r + k * clock L) * residue n (r + k * clock L) := by
  calc
    (∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (residue n) j)) =
        ∑' j : ℕ, (historyFibre L r).indicator (fun j => cellWeight j * residue n j) j := by
      apply tsum_congr
      intro j
      by_cases hj : j ∈ historyFibre L r <;> simp [hj]
    _ = ∑' j : historyFibre L r, cellWeight j * residue n j := by
      exact (_root_.tsum_subtype (historyFibre L r)
        (fun j => cellWeight j * residue n j)).symm
    _ = _ := tsum_historyFibre_eq_progression n L r hr

/-- Exact beta form of the original chronological residue quotient.  Its denominator remains the
physical fibre mass, and the numerator retains the full pointwise residue `tsum`. -/
theorem weightedResidueQuotient_eq_beta_tsum (n L r : ℕ) (hr : r < clock L) :
    weightedResidueQuotient n L r =
      (∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
        ∑' k : ℕ, x ^ (k * clock L) * residue n (r + k * clock L)) /
        cellMeasure.real (historyFibre L r) := by
  unfold weightedResidueQuotient
  rw [weightedResidue_numerator_eq_progression n L r hr,
    fibre_residue_progression_eq_beta_tsum]

/-- Orthogonal increment from one chronological history space to the next. -/
def historyLayer (i : ℕ) : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure :=
  (historySpace (i + 1)).starProjection - (historySpace i).starProjection

/-- A clock step does not refine the physical residue history when its new modulus was already
encoded by the preceding clock. -/
theorem clock_succ_eq_of_dvd (i : ℕ) (hi : i + 1 ∣ clock i) :
    clock (i + 1) = clock i := by
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro k hk
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) with hki | hki
    · subst k
      exact hi
    · exact dvd_clock (by omega) (by omega)
  · exact clock_dvd (by omega)

/-- A chronological layer is zero exactly whenever its successive clocks agree. -/
theorem historyLayer_eq_zero_of_clock_succ_eq (i : ℕ)
    (hi : clock (i + 1) = clock i) : historyLayer i = 0 := by
  ext v
  simp [historyLayer, historySpace, hi]

/-- A chronological layer is zero if the next modulus already divides its lower clock. -/
theorem historyLayer_eq_zero_of_dvd_clock (i : ℕ) (hi : i + 1 ∣ clock i) :
    historyLayer i = 0 :=
  historyLayer_eq_zero_of_clock_succ_eq i (clock_succ_eq_of_dvd i hi)

/-- A stage with two coprime nontrivial factors creates no new chronological residue layer:
each factor was already present in its preceding clock. -/
theorem historyLayer_eq_zero_of_coprime_product_predecessor (a b : ℕ)
    (ha : 1 < a) (hb : 1 < b) (hab : a.Coprime b) :
    historyLayer (a * b - 1) = 0 := by
  apply historyLayer_eq_zero_of_dvd_clock
  have habpos : 1 ≤ a * b := by nlinarith
  rw [Nat.sub_add_cancel habpos]
  apply hab.mul_dvd_of_dvd_of_dvd
  · have hbound : a + 1 ≤ a * b := by
      calc
        a + 1 ≤ a + a := by omega
        _ = a * 2 := (Nat.mul_two _).symm
        _ ≤ a * b := Nat.mul_le_mul_left _ (by omega)
    exact dvd_clock (by omega) (Nat.le_sub_of_add_le hbound)
  · have hbound : b + 1 ≤ a * b := by
      calc
        b + 1 ≤ b + b := by omega
        _ = 2 * b := (Nat.two_mul _).symm
        _ ≤ a * b := Nat.mul_le_mul_right _ (by omega)
    exact dvd_clock (by omega) (Nat.le_sub_of_add_le hbound)

/-- Under the physical cell law, almost-everywhere equal real observables agree at every cell
because every singleton has positive mass. -/
theorem cell_point_eq_of_ae {f g : ℕ → ℝ} (h : f =ᵐ[cellMeasure] g) (j : ℕ) : f j = g j := by
  apply (ae_iff_of_countable.mp h) j
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change ENNReal.ofReal (cellWeight j) ≠ 0
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by unfold cellWeight; positivity))

/-- The canonical `Lp` representative of one physical residue is its literal residue at every
cell, since the physical measure has full support. -/
theorem residueVec_apply_eq_residue (n j : ℕ) : residueVec n j = residue n j := by
  apply cell_point_eq_of_ae
  exact MemLp.coeFn_toLp _

/-- The finite residue source has its literal physical-cell numerator at every cell. -/
theorem sourceVec_apply_eq_cell (a : ℕ → ℝ) (N j : ℕ) :
    sourceVec a N j = DeletionCoefficientTransfer.cell a N (j + 1) := by
  apply cell_point_eq_of_ae
  induction N with
  | zero =>
    filter_upwards [Lp.coeFn_zero ℝ 2 cellMeasure] with x hx
    simpa only [sourceVec, DeletionCoefficientTransfer.cell, sum_range_zero, Pi.zero_apply]
      using hx
  | succ N ih =>
    have hs : sourceVec a (N + 1) = sourceVec a N + a (N + 1) • residueVec (N + 1) := by
      simp only [sourceVec, sum_range_succ]
    rw [hs]
    filter_upwards [Lp.coeFn_add (sourceVec a N) (a (N + 1) • residueVec (N + 1)), ih,
      Lp.coeFn_smul (a (N + 1)) (residueVec (N + 1))] with x hx hi hm
    rw [hx, Pi.add_apply, hi, hm, Pi.smul_apply, residueVec_apply_eq_residue]
    simp only [DeletionCoefficientTransfer.cell, sum_range_succ, residue, smul_eq_mul,
      Nat.cast_add, Nat.cast_one, mul_div_assoc]

/-- The full finite Möbius source, with its reciprocal and floor components retained as one
paired physical observable.  Neither displayed component is introduced as a separate `L²` vector. -/
def pairedMoebiusSource (N j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) *
      (∑ i ∈ Finset.range N,
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) / ((i : ℝ) + 1)) -
    ∑ i ∈ Finset.range N,
      ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) * (((j + 1) / (i + 1) : ℕ) : ℝ)

/-- Exact all-cell floor normal form of the original finite source.  The two summands remain
paired because their separate physical representatives are not available to the layer map. -/
theorem sourceVec_moebius_apply_eq_pairedMoebiusSource (N j : ℕ) :
    sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N j =
      pairedMoebiusSource N j := by
  rw [sourceVec_apply_eq_cell]
  unfold DeletionCoefficientTransfer.cell pairedMoebiusSource
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hdivmod := Nat.div_add_mod (j + 1) (i + 1)
  have hcast :
      (((i + 1) * ((j + 1) / (i + 1)) + (j + 1) % (i + 1) : ℕ) : ℝ) =
        ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast hdivmod
  push_cast at hcast
  have hsplit : (((j + 1) % (i + 1) : ℕ) : ℝ) / ((i : ℝ) + 1) =
      ((j : ℝ) + 1) / ((i : ℝ) + 1) - ((j + 1) / (i + 1) : ℕ) := by
    field_simp [hpos.ne']
    linarith
  rw [mul_div_assoc, hsplit]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- The complete paired source has the exact joint clock period.  This is a pointwise equality
of the original finite signed source, not a replacement of a fibre prefix by a period average. -/
theorem pairedMoebiusSource_add_clock (N j : ℕ) :
    pairedMoebiusSource N (j + clock N) = pairedMoebiusSource N j := by
  rw [← sourceVec_moebius_apply_eq_pairedMoebiusSource,
    ← sourceVec_moebius_apply_eq_pairedMoebiusSource,
    sourceVec_apply_eq_cell, sourceVec_apply_eq_cell]
  unfold DeletionCoefficientTransfer.cell
  apply Finset.sum_congr rfl
  intro i hi
  have hdiv : i + 1 ∣ clock N := dvd_clock (by omega) (by
    exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hi))
  rw [mul_div_assoc, mul_div_assoc]
  have hres := residue_add_eq_of_dvd (n := i + 1) (j := j) hdiv
  unfold residue at hres
  simpa only [Nat.cast_add, Nat.cast_one] using
    congrArg (fun x : ℝ => ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) * x) hres

/-- The paired floor form represents the finite `L²` source pointwise on the full physical
space. -/
theorem sourceVec_moebius_ae_eq_pairedMoebiusSource (N : ℕ) :
    (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N : ℕ → ℝ) =ᵐ[cellMeasure]
      pairedMoebiusSource N :=
  Filter.Eventually.of_forall (sourceVec_moebius_apply_eq_pairedMoebiusSource N)

private theorem integrable_pairedMoebiusSource (N : ℕ) :
    Integrable (pairedMoebiusSource N) cellMeasure := by
  have hsource : Integrable
      (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N : ℕ → ℝ) cellMeasure :=
    (Lp.memLp (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)).integrable
      (by norm_num)
  exact hsource.congr (sourceVec_moebius_ae_eq_pairedMoebiusSource N)

private theorem historyFibre_measurable_paired (L r : ℕ) :
    MeasurableSet[residueSigma (clock L)] (historyFibre L r) := by
  change MeasurableSet[MeasurableSpace.comap (fun j : ℕ => j % clock L) ⊤] _
  exact MeasurableSpace.measurableSet_comap.mpr
    ⟨{r}, (Set.to_countable _).measurableSet, rfl⟩

private theorem historyFibre_measurable_top_paired (L r : ℕ) :
    MeasurableSet (historyFibre L r) :=
  (Set.to_countable _).measurableSet

/-- Literal paired physical fibre numerator of the finite Möbius source. -/
def pairedMoebiusQuotient (N L r : ℕ) : ℝ :=
  (∑' j : ℕ, cellWeight j * ((historyFibre L r).indicator (pairedMoebiusSource N) j)) /
    cellMeasure.real (historyFibre L r)

private theorem integral_historyProjection_source_on_fibre_eq_pairedMoebiusSource
    (N L r : ℕ) :
    ∫ j in historyFibre L r,
      ((historySpace L).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)) j ∂cellMeasure =
      ∑' j : ℕ, cellWeight j *
        ((historyFibre L r).indicator (pairedMoebiusSource N) j) := by
  have hproj := integral_condExpL2_eq (E' := ℝ) (𝕜 := ℝ)
    (m := residueSigma (clock L)) (m0 := (inferInstance : MeasurableSpace ℕ))
    (μ := cellMeasure)
    (show residueSigma (clock L) ≤ (inferInstance : MeasurableSpace ℕ) from le_top)
    (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
    (historyFibre_measurable_paired L r) (measure_ne_top _ _)
  have hsource := sourceVec_moebius_ae_eq_pairedMoebiusSource N
  have hweight :
      ∫ j in historyFibre L r, pairedMoebiusSource N j ∂cellMeasure =
        ∑' j : ℕ, cellWeight j *
          ((historyFibre L r).indicator (pairedMoebiusSource N) j) := by
    rw [← integral_indicator (historyFibre_measurable_top_paired L r)]
    have h := PMF.integral_eq_tsum cellPMF
      ((historyFibre L r).indicator (pairedMoebiusSource N))
      ((integrable_pairedMoebiusSource N).indicator (historyFibre_measurable_top_paired L r))
    change (∫ j, (historyFibre L r).indicator (pairedMoebiusSource N) j ∂cellPMF.toMeasure) = _
    rw [h]
    apply tsum_congr
    intro j
    change (ENNReal.ofReal (cellWeight j)).toReal *
      (historyFibre L r).indicator (pairedMoebiusSource N) j = _
    rw [ENNReal.toReal_ofReal (by unfold cellWeight; positivity)]
  calc
    _ = ∫ j in historyFibre L r,
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N) j ∂cellMeasure := by
      simpa only [historySpace, condExpL2, Submodule.starProjection_apply] using hproj
    _ = ∫ j in historyFibre L r, pairedMoebiusSource N j ∂cellMeasure := by
      exact setIntegral_congr_ae (historyFibre_measurable_top_paired L r)
        (hsource.mono fun _ h _ => h)
    _ = _ := hweight

private theorem historyProjection_factors_through_clock_paired
    (L : ℕ) (v : Lp ℝ 2 cellMeasure) :
    ∃ h : ℕ → ℝ, StronglyMeasurable h ∧
      ∀ j : ℕ, ((historySpace L).starProjection v) j = h (j % clock L) := by
  let g : ℕ → ℝ := ((historySpace L).starProjection v : ℕ → ℝ)
  have hmem : (historySpace L).starProjection v ∈ historySpace L :=
    Submodule.starProjection_apply_mem _ _
  change ((historySpace L).starProjection v : Lp ℝ 2 cellMeasure) ∈
    lpMeas ℝ ℝ (residueSigma (clock L)) 2 cellMeasure at hmem
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hmem
  let g₀ : ℕ → ℝ := hmem.mk g
  have hg₀ : StronglyMeasurable[residueSigma (clock L)] g₀ := hmem.stronglyMeasurable_mk
  obtain ⟨h, hh, hfac⟩ := hg₀.exists_eq_measurable_comp
    (f := fun j : ℕ => j % clock L)
  refine ⟨h, hh, ?_⟩
  have hae : g =ᵐ[cellMeasure] g₀ := hmem.ae_eq_mk
  have hpoint : ∀ j : ℕ, g j = g₀ j := by
    intro j
    apply (ae_iff_of_countable.mp hae) j
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    change ENNReal.ofReal (cellWeight j) ≠ 0
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by unfold cellWeight; positivity))
  intro j
  change g j = _
  rw [hpoint j, hfac]
  rfl

/-- Chronological projection of the complete source is the literal paired floor numerator over
its actual physical fibre mass. -/
theorem historyProjection_source_apply_eq_pairedMoebiusQuotient (N L j : ℕ) :
    ((historySpace L).starProjection
      (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)) j =
      pairedMoebiusQuotient N L (j % clock L) := by
  obtain ⟨h, hh, hpoint⟩ := historyProjection_factors_through_clock_paired L
    (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
  have hmean (r : ℕ) :
      ∫ x in historyFibre L r,
        ((historySpace L).starProjection
          (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)) x ∂cellMeasure =
        cellMeasure.real (historyFibre L r) * h r := by
    rw [show (∫ x in historyFibre L r,
        ((historySpace L).starProjection
          (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)) x ∂cellMeasure) =
        ∫ x in historyFibre L r, h r ∂cellMeasure by
          apply setIntegral_congr_fun (historyFibre_measurable_top_paired L r)
          intro x hx
          rw [hpoint x]
          congr]
    simpa only [smul_eq_mul] using
      (setIntegral_const (μ := cellMeasure) (s := historyFibre L r) (h r))
  have hr : j % clock L < clock L := Nat.mod_lt _ (clock_pos L)
  have hmass : cellMeasure.real (historyFibre L (j % clock L)) ≠ 0 :=
    ne_of_gt (historyFibre_mass_pos L _ hr)
  have hvalue := hmean (j % clock L)
  rw [integral_historyProjection_source_on_fibre_eq_pairedMoebiusSource] at hvalue
  rw [hpoint j]
  apply (eq_div_iff hmass).mpr
  rw [mul_comm]
  exact hvalue.symm

/-- Exact physical-cell coordinate of a chronological layer.  It is the difference of adjacent
weighted residue quotients, retaining their original nonuniform fibre masses. -/
theorem historyLayer_apply_residueVec_eq_weighted_residue_quotient (l n j : ℕ) :
    (historyLayer l (residueVec n)) j =
      weightedResidueQuotient n (l + 1) (j % clock (l + 1)) -
        weightedResidueQuotient n l (j % clock l) := by
  apply cell_point_eq_of_ae
  change (((historySpace (l + 1)).starProjection (residueVec n) -
    (historySpace l).starProjection (residueVec n)) : Lp ℝ 2 cellMeasure) =ᵐ[cellMeasure] _
  filter_upwards [Lp.coeFn_sub ((historySpace (l + 1)).starProjection (residueVec n))
    ((historySpace l).starProjection (residueVec n))] with x hx
  rw [hx, Pi.sub_apply, historyProjection_apply_eq_weightedResidueQuotient,
    historyProjection_apply_eq_weightedResidueQuotient]

/-- Scalar weighted-residue coordinate of one chronological layer. -/
theorem smul_historyLayer_apply_residueVec_eq_weighted_residue_quotient
    (c : ℝ) (l n j : ℕ) :
    (c • historyLayer l (residueVec n)) j =
      c * (weightedResidueQuotient n (l + 1) (j % clock (l + 1)) -
        weightedResidueQuotient n l (j % clock l)) := by
  apply cell_point_eq_of_ae
  filter_upwards [Lp.coeFn_smul c (historyLayer l (residueVec n))] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul,
    historyLayer_apply_residueVec_eq_weighted_residue_quotient]

/-- A history layer kills every vector already measurable at its lower clock. -/
theorem historyLayer_apply_eq_zero_of_mem (i : ℕ) (v : Lp ℝ 2 cellMeasure)
    (hv : v ∈ historySpace i) :
    historyLayer i v = 0 := by
  change (historySpace (i + 1)).starProjection v -
    (historySpace i).starProjection v = 0
  have hvnext : v ∈ historySpace (i + 1) := historySpace_mono (by omega) hv
  rw [Submodule.starProjection_eq_self_iff.mpr hvnext,
    Submodule.starProjection_eq_self_iff.mpr hv, sub_self]

/-- A history layer passes unchanged through any later chronological projection. -/
theorem historyLayer_apply_starProjection_eq (i n : ℕ) (hin : i + 1 ≤ n)
    (v : Lp ℝ 2 cellMeasure) :
    historyLayer i ((historySpace n).starProjection v) = historyLayer i v := by
  change (historySpace (i + 1)).starProjection ((historySpace n).starProjection v) -
      (historySpace i).starProjection ((historySpace n).starProjection v) =
    (historySpace (i + 1)).starProjection v - (historySpace i).starProjection v
  have hnext : (historySpace (i + 1)).starProjection
      ((historySpace n).starProjection v) =
      (historySpace (i + 1)).starProjection v := by
    exact congrArg (fun f : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure => f v)
      (Submodule.starProjection_comp_starProjection_of_le (historySpace_mono hin))
  have hnow : (historySpace i).starProjection ((historySpace n).starProjection v) =
      (historySpace i).starProjection v := by
    exact congrArg (fun f : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure => f v)
      (Submodule.starProjection_comp_starProjection_of_le
        (historySpace_mono (Nat.le_trans (by omega) hin)))
  rw [hnext, hnow]

/-- A chronological layer extracts exactly its own signed innovation and annihilates every
other innovation. -/
theorem historyLayer_signedInnovation (l i : ℕ) :
    historyLayer l (signedInnovation i) = if i = l then signedInnovation i else 0 := by
  unfold signedInnovation
  rw [map_smul]
  by_cases hil : i = l
  · subst i
    have hinnovation : historyLayer l (innovation l) = innovation l := by
      rw [innovation, map_sub,
        historyLayer_apply_eq_zero_of_mem l
          ((historySpace l).starProjection (residueVec (l + 1)))
          (Submodule.starProjection_apply_mem _ _)]
      unfold historyLayer
      simp only [sub_apply]
      rw [Submodule.starProjection_eq_self_iff.mpr (residueVec_mem l)]
      abel
    simp [hinnovation]
  · rw [if_neg hil]
    rcases lt_or_gt_of_ne hil with hil | hli
    · rw [historyLayer_apply_eq_zero_of_mem l (innovation i)
        (historySpace_mono (by omega) (innovation_mem i)), smul_zero]
    · unfold innovation
      rw [map_sub, historyLayer_apply_starProjection_eq l i (by omega), sub_self, smul_zero]

/-- The layer component of the accumulated innovation is precisely the innovation inserted at
that layer, when the finite source has reached it. -/
theorem historyLayer_martingalePart (l N : ℕ) :
    historyLayer l (martingalePart N) = if l < N then signedInnovation l else 0 := by
  unfold martingalePart
  rw [map_sum]
  simp_rw [historyLayer_signedInnovation]
  by_cases hlN : l < N
  · rw [if_pos hlN]
    calc
      (∑ i ∈ range N, if i = l then signedInnovation i else 0) =
          if l = l then signedInnovation l else 0 := by
        apply Finset.sum_eq_single l
        · intro i hi hil
          simp [hil]
        · simp [Finset.mem_range, hlN]
      _ = signedInnovation l := by simp
  · rw [if_neg hlN]
    apply Finset.sum_eq_zero
    intro i hi
    have hil : i ≠ l := by
      intro hil
      subst i
      exact hlN (Finset.mem_range.mp hi)
    simp [hil]

/-- Before any analytic estimate, the complete signed predictable tail is the layer of the
original physical Möbius source after removing only its single local innovation.  This keeps
all later Möbius signs together before the chronological projection. -/
theorem historyLayer_predictableDrift_eq_historyLayer_source_sub_innovation (l N : ℕ) :
    historyLayer l (predictableDrift N) =
      historyLayer l (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N) -
        if l < N then signedInnovation l else 0 := by
  have h := congrArg (historyLayer l) (source_eq_martingale_add_drift N)
  rw [map_add, historyLayer_martingalePart] at h
  rw [h]
  abel

/-- Exact paired-source coordinate of one chronological drift layer.  The full finite Möbius
source enters each fibre quotient before projection; the sole unpaired term is its one local
innovation. -/
theorem historyLayer_predictableDrift_apply_eq_pairedMoebiusQuotient_sub_innovation
    (l N j : ℕ) :
    (historyLayer l (predictableDrift N)) j =
      pairedMoebiusQuotient N (l + 1) (j % clock (l + 1)) -
        pairedMoebiusQuotient N l (j % clock l) -
          if l < N then signedInnovation l j else 0 := by
  have hbridge := congrArg (fun v : Lp ℝ 2 cellMeasure => v j)
    (historyLayer_predictableDrift_eq_historyLayer_source_sub_innovation l N)
  by_cases hlN : l < N
  · rw [if_pos hlN]
    simp only [if_pos hlN] at hbridge
    rw [hbridge]
    let upper : Lp ℝ 2 cellMeasure :=
      (historySpace (l + 1)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
    let lower : Lp ℝ 2 cellMeasure :=
      (historySpace l).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
    change (upper - lower - signedInnovation l) j = _
    apply cell_point_eq_of_ae
    change ((upper - lower - signedInnovation l : Lp ℝ 2 cellMeasure) : ℕ → ℝ) =ᵐ[cellMeasure]
      (fun x => pairedMoebiusQuotient N (l + 1) (x % clock (l + 1)) -
        pairedMoebiusQuotient N l (x % clock l) - signedInnovation l x)
    have hfirst := Lp.coeFn_sub upper lower
    have hsecond := Lp.coeFn_sub (upper - lower) (signedInnovation l)
    filter_upwards [hfirst, hsecond] with x hx hy
    have hupper : upper x = pairedMoebiusQuotient N (l + 1) (x % clock (l + 1)) := by
      dsimp only [upper]
      exact historyProjection_source_apply_eq_pairedMoebiusQuotient N (l + 1) x
    have hlower : lower x = pairedMoebiusQuotient N l (x % clock l) := by
      dsimp only [lower]
      exact historyProjection_source_apply_eq_pairedMoebiusQuotient N l x
    rw [hy, Pi.sub_apply, hx, Pi.sub_apply, hupper, hlower]
  · rw [if_neg hlN]
    simp only [if_neg hlN] at hbridge
    have hbridge' :
        (historyLayer l (predictableDrift N)) j =
          (historyLayer l
            (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)) j := by
      simpa using hbridge
    rw [hbridge']
    simp only [sub_zero]
    let upper : Lp ℝ 2 cellMeasure :=
      (historySpace (l + 1)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
    let lower : Lp ℝ 2 cellMeasure :=
      (historySpace l).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
    change (upper - lower) j = _
    apply cell_point_eq_of_ae
    change ((upper - lower : Lp ℝ 2 cellMeasure) : ℕ → ℝ) =ᵐ[cellMeasure]
      (fun x => pairedMoebiusQuotient N (l + 1) (x % clock (l + 1)) -
        pairedMoebiusQuotient N l (x % clock l))
    have hfirst := Lp.coeFn_sub upper lower
    filter_upwards [hfirst] with x hx
    have hupper : upper x = pairedMoebiusQuotient N (l + 1) (x % clock (l + 1)) := by
      dsimp only [upper]
      exact historyProjection_source_apply_eq_pairedMoebiusQuotient N (l + 1) x
    have hlower : lower x = pairedMoebiusQuotient N l (x % clock l) := by
      dsimp only [lower]
      exact historyProjection_source_apply_eq_pairedMoebiusQuotient N l x
    rw [hx, Pi.sub_apply, hupper, hlower]

/-- Every history layer of the final drift is a reverse complete Möbius tail.  Earlier predictors
are annihilated and every later predictor reduces to its raw residue on that layer.  This retains
all simultaneous prime insertions in the tail. -/
theorem historyLayer_predictableDrift_eq_reverse_tail (l N : ℕ) :
    historyLayer l (predictableDrift N) =
      ∑ i ∈ range N, if l < i then
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
          historyLayer l (residueVec (i + 1)) else 0 := by
  unfold predictableDrift
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  by_cases hli : l < i
  · rw [if_pos hli, historyLayer_apply_starProjection_eq l i
      (Nat.succ_le_iff.mpr hli)]
  · rw [if_neg hli]
    have hil : i ≤ l := Nat.le_of_not_gt hli
    rw [historyLayer_apply_eq_zero_of_mem l
      ((historySpace i).starProjection (residueVec (i + 1)))
      (historySpace_mono hil (Submodule.starProjection_apply_mem _ _)), smul_zero]

/-- Exact physical-cell coordinate of a complete reverse tail.  The Möbius signs remain inside
one simultaneous sum of adjacent weighted-residue quotient differences. -/
theorem historyLayer_predictableDrift_apply_eq_reverse_tail_quotient_difference (l N j : ℕ) :
    (historyLayer l (predictableDrift N)) j =
      ∑ i ∈ range N, if l < i then
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          (weightedResidueQuotient (i + 1) (l + 1) (j % clock (l + 1)) -
            weightedResidueQuotient (i + 1) l (j % clock l)) else 0 := by
  rw [historyLayer_predictableDrift_eq_reverse_tail]
  apply cell_point_eq_of_ae
  filter_upwards [Lp.coeFn_fun_finsetSum (range N) (fun i =>
    if l < i then ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
      historyLayer l (residueVec (i + 1)) else 0)] with x hx
  rw [hx]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hli : l < i
  · simp only [if_pos hli]
    exact smul_historyLayer_apply_residueVec_eq_weighted_residue_quotient _ _ _ _
  · simp [if_neg hli]

/-- On one actual upper-clock fibre, a complete reverse tail has a single finite residue-class
coordinate.  The lower quotient is evaluated at the compatible lower-clock class. -/
theorem historyLayer_predictableDrift_apply_on_historyFibre (l N r j : ℕ)
    (hj : j ∈ historyFibre (l + 1) r) :
    (historyLayer l (predictableDrift N)) j =
      ∑ i ∈ range N, if l < i then
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          (weightedResidueQuotient (i + 1) (l + 1) r -
            weightedResidueQuotient (i + 1) l (r % clock l)) else 0 := by
  rw [historyLayer_predictableDrift_apply_eq_reverse_tail_quotient_difference]
  change j % clock (l + 1) = r at hj
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hli : l < i
  · simp only [if_pos hli]
    have hmod : j % clock l = r % clock l := by
      calc
        j % clock l = (j % clock (l + 1)) % clock l := by
          rw [Nat.mod_mod_of_dvd _ (clock_dvd (by omega))]
        _ = r % clock l := by rw [hj]
    rw [hj, hmod]
  · simp [if_neg hli]

/-- Exact beta-kernel coordinate of the complete signed reverse tail on one physical fibre.
Every later Möbius coefficient remains in the same finite sum, while each quotient is its literal
beta integral divided by its original fibre mass. -/
theorem historyLayer_predictableDrift_apply_on_historyFibre_eq_beta_tail (l N r j : ℕ)
    (hj : j ∈ historyFibre (l + 1) r) :
    (historyLayer l (predictableDrift N)) j =
      ∑ i ∈ range N, if l < i then
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          ((∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
            ∑' k : ℕ, x ^ (k * clock (l + 1)) * residue (i + 1)
              (r + k * clock (l + 1))) /
              cellMeasure.real (historyFibre (l + 1) r) -
            (∫ x in (0 : ℝ)..1, (1 - x) * x ^ (r % clock l) *
              ∑' k : ℕ, x ^ (k * clock l) * residue (i + 1)
                (r % clock l + k * clock l)) /
              cellMeasure.real (historyFibre l (r % clock l))) else 0 := by
  have hr : r < clock (l + 1) := by
    change j % clock (l + 1) = r at hj
    rw [← hj]
    exact Nat.mod_lt _ (clock_pos _)
  rw [historyLayer_predictableDrift_apply_on_historyFibre l N r j hj]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hli : l < i
  · simp only [if_pos hli]
    rw [weightedResidueQuotient_eq_beta_tsum (i + 1) (l + 1) r hr,
      weightedResidueQuotient_eq_beta_tsum (i + 1) l (r % clock l)
        (Nat.mod_lt _ (clock_pos l))]
  · simp [hli]

/-- A chronological layer is measurable at its upper residue clock. -/
theorem historyLayer_mem_historySpace_succ (l : ℕ) (v : Lp ℝ 2 cellMeasure) :
    historyLayer l v ∈ historySpace (l + 1) := by
  change (historySpace (l + 1)).starProjection v -
    (historySpace l).starProjection v ∈ historySpace (l + 1)
  apply Submodule.sub_mem
  · exact Submodule.starProjection_apply_mem _ _
  · exact historySpace_mono (by omega) (Submodule.starProjection_apply_mem _ _)

/-- Physical coarea of one complete reverse-tail layer. -/
theorem historyLayer_predictableDrift_norm_sq_eq_fibre_coarea (l N : ℕ) :
    ‖historyLayer l (predictableDrift N)‖ ^ 2 =
      ∑ r ∈ range (clock (l + 1)),
        (∫ j in historyFibre (l + 1) r, historyLayer l (predictableDrift N) j ∂cellMeasure) ^ 2 /
          cellMeasure.real (historyFibre (l + 1) r) :=
  historySpace_norm_sq_eq_fibre_coarea (l + 1) (historyLayer l (predictableDrift N))
    (historyLayer_mem_historySpace_succ l (predictableDrift N))

/-- Exact finite physical fibre energy of one complete reverse tail.  Each displayed square
contains all simultaneous later Möbius signs. -/
theorem historyLayer_predictableDrift_norm_sq_eq_reverse_tail_fibre_energy (l N : ℕ) :
    ‖historyLayer l (predictableDrift N)‖ ^ 2 =
      ∑ r ∈ range (clock (l + 1)),
        cellMeasure.real (historyFibre (l + 1) r) *
          (∑ i ∈ range N, if l < i then
            ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
              (weightedResidueQuotient (i + 1) (l + 1) r -
                weightedResidueQuotient (i + 1) l (r % clock l)) else 0) ^ 2 := by
  rw [historyLayer_predictableDrift_norm_sq_eq_fibre_coarea]
  apply Finset.sum_congr rfl
  intro r hr
  have hmass : cellMeasure.real (historyFibre (l + 1) r) ≠ 0 :=
    ne_of_gt (historyFibre_mass_pos (l + 1) r (mem_range.mp hr))
  have hmeas : MeasurableSet (historyFibre (l + 1) r) :=
    (Set.to_countable _).measurableSet
  have hmean :
      ∫ j in historyFibre (l + 1) r, historyLayer l (predictableDrift N) j ∂cellMeasure =
        cellMeasure.real (historyFibre (l + 1) r) *
          ∑ i ∈ range N, if l < i then
            ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
              (weightedResidueQuotient (i + 1) (l + 1) r -
                weightedResidueQuotient (i + 1) l (r % clock l)) else 0 := by
    rw [show (∫ j in historyFibre (l + 1) r, historyLayer l (predictableDrift N) j ∂cellMeasure) =
        ∫ _j in historyFibre (l + 1) r, ∑ i ∈ range N, if l < i then
          ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
            (weightedResidueQuotient (i + 1) (l + 1) r -
              weightedResidueQuotient (i + 1) l (r % clock l)) else 0 ∂cellMeasure by
        apply setIntegral_congr_fun hmeas
        intro j hj
        exact historyLayer_predictableDrift_apply_on_historyFibre l N r j hj]
    simpa only [smul_eq_mul] using
      (setIntegral_const (μ := cellMeasure) (s := historyFibre (l + 1) r)
        (∑ i ∈ range N, if l < i then
          ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
            (weightedResidueQuotient (i + 1) (l + 1) r -
              weightedResidueQuotient (i + 1) l (r % clock l)) else 0))
  rw [hmean]
  field_simp [hmass]

/-- One chronological projection step is Pythagorean: the newly exposed history layer carries
exactly the difference of the two nested projections. -/
theorem history_projection_succ_norm_sq_eq_add_layer (i : ℕ)
    (v : Lp ℝ 2 cellMeasure) :
    ‖(historySpace (i + 1)).starProjection v‖ ^ 2 =
      ‖(historySpace i).starProjection v‖ ^ 2 + ‖historyLayer i v‖ ^ 2 := by
  have hcomp : (historySpace i).starProjection
      ((historySpace (i + 1)).starProjection v) =
      (historySpace i).starProjection v := by
    exact congrArg (fun f : Lp ℝ 2 cellMeasure →L[ℝ] Lp ℝ 2 cellMeasure => f v)
      (Submodule.starProjection_comp_starProjection_of_le (historySpace_mono (by omega)))
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection
    ((historySpace (i + 1)).starProjection v) (historySpace i)
  rw [Submodule.starProjection_orthogonal_val, hcomp] at hpyth
  change ‖(historySpace (i + 1)).starProjection v‖ ^ 2 =
    ‖(historySpace i).starProjection v‖ ^ 2 +
      ‖(historySpace (i + 1)).starProjection v - (historySpace i).starProjection v‖ ^ 2
  exact hpyth

/-- Projection onto a terminal chronological history decomposes into its base history and every
intermediate orthogonal layer. -/
theorem history_projection_norm_sq_eq_layer_sum (N : ℕ)
    (v : Lp ℝ 2 cellMeasure) :
    ‖(historySpace N).starProjection v‖ ^ 2 =
      ‖(historySpace 0).starProjection v‖ ^ 2 +
        ∑ i ∈ range N, ‖historyLayer i v‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    calc
      ‖(historySpace (N + 1)).starProjection v‖ ^ 2 =
          ‖(historySpace N).starProjection v‖ ^ 2 + ‖historyLayer N v‖ ^ 2 :=
        history_projection_succ_norm_sq_eq_add_layer N v
      _ = _ := by rw [ih, Finset.sum_range_succ]; ring

/-- Exact layer energy of the complete predictable drift. -/
theorem predictableDrift_norm_sq_eq_historyLayer_sum (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ i ∈ range N, ‖historyLayer i (predictableDrift N)‖ ^ 2 := by
  calc
    ‖predictableDrift N‖ ^ 2 =
        ‖(historySpace N).starProjection (predictableDrift N)‖ ^ 2 := by
      rw [Submodule.starProjection_eq_self_iff.mpr (predictableDrift_mem_historySpace N)]
    _ = _ := history_projection_norm_sq_eq_layer_sum N (predictableDrift N)

/-- Full EDQ layer decomposition.  The covariance energy is exactly the base-history mass plus
the positive sum of squared reverse tails, each retaining all later signed Möbius insertions. -/
theorem predictableDrift_norm_sq_eq_reverse_tail_layer_energy (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ l ∈ range N, ‖∑ i ∈ range N, if l < i then
          ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
            historyLayer l (residueVec (i + 1)) else 0‖ ^ 2 := by
  calc
    ‖predictableDrift N‖ ^ 2 =
        ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
          ∑ l ∈ range N, ‖historyLayer l (predictableDrift N)‖ ^ 2 :=
      predictableDrift_norm_sq_eq_historyLayer_sum N
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      rw [historyLayer_predictableDrift_eq_reverse_tail]

/-- Fully physical EDQ energy identity.  Bounding this finite double sum cofinally by a
polylogarithm is exactly the remaining analytic theorem; every square retains its complete
signed multi-prime tail. -/
theorem predictableDrift_norm_sq_eq_reverse_tail_quotient_fibre_energy (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ l ∈ range N, ∑ r ∈ range (clock (l + 1)),
          cellMeasure.real (historyFibre (l + 1) r) *
            (∑ i ∈ range N, if l < i then
              ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
                (weightedResidueQuotient (i + 1) (l + 1) r -
                  weightedResidueQuotient (i + 1) l (r % clock l)) else 0) ^ 2 := by
  calc
    ‖predictableDrift N‖ ^ 2 =
        ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
          ∑ l ∈ range N, ‖historyLayer l (predictableDrift N)‖ ^ 2 :=
      predictableDrift_norm_sq_eq_historyLayer_sum N
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      exact historyLayer_predictableDrift_norm_sq_eq_reverse_tail_fibre_energy l N

/-- For nested chronological histories, the cross covariance of two projected residues is the
pairing of the earlier projection with the raw later residue. -/
theorem nested_projected_residue_inner_eq_raw (i j : ℕ) (hij : i ≤ j) :
    inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
      ((historySpace j).starProjection (residueVec (j + 1))) =
      inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
        (residueVec (j + 1)) := by
  have hmem : (historySpace i).starProjection (residueVec (i + 1)) ∈ historySpace j :=
    historySpace_mono hij (Submodule.starProjection_apply_mem _ _)
  calc
    inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
        ((historySpace j).starProjection (residueVec (j + 1))) =
        inner ℝ ((historySpace j).starProjection
          ((historySpace i).starProjection (residueVec (i + 1))))
          (residueVec (j + 1)) :=
      (Submodule.inner_starProjection_left_eq_right (historySpace j)
        ((historySpace i).starProjection (residueVec (i + 1)))
        (residueVec (j + 1))).symm
    _ = _ := by rw [Submodule.starProjection_eq_self_iff.mpr hmem]

/-- Inserting the next chronological residue adds precisely its signed predictor to the drift. -/
theorem predictableDrift_succ (N : ℕ) :
    predictableDrift (N + 1) = predictableDrift N +
      ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) •
        (historySpace N).starProjection (residueVec (N + 1)) := by
  unfold predictableDrift
  rw [Finset.sum_range_succ]

/-- At every non-prime stage the Möbius-weighted predictor is exactly the raw residue.  This
retains every squarefree composite insertion; a vanishing Möbius coefficient covers the remaining
composites. -/
theorem signed_predictor_eq_raw_of_not_prime (n : ℕ) (hn : ¬ (n + 1).Prime) :
    ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) •
      (historySpace n).starProjection (residueVec (n + 1)) =
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) • residueVec (n + 1) := by
  have hzero := signedInnovation_eq_zero_of_not_prime n hn
  rw [signedInnovation, innovation, smul_sub, sub_eq_zero] at hzero
  exact hzero.symm

/-- A non-prime chronological insertion therefore changes the drift by its literal Möbius
residue, with no conditional approximation. -/
theorem predictableDrift_succ_eq_raw_of_not_prime (N : ℕ) (hN : ¬ (N + 1).Prime) :
    predictableDrift (N + 1) = predictableDrift N +
      ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) • residueVec (N + 1) := by
  rw [predictableDrift_succ, signed_predictor_eq_raw_of_not_prime N hN]

/-- The cross covariance of the accumulated drift and the next predictor is an exact triangular
sum over all earlier histories, with the later residue left unprojected. -/
theorem predictableDrift_cross_eq_earlier_raw_residue_sum (N : ℕ) :
    inner ℝ (predictableDrift N)
      ((historySpace N).starProjection (residueVec (N + 1))) =
      ∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
        inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
          (residueVec (N + 1)) := by
  unfold predictableDrift
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_left, nested_projected_residue_inner_eq_raw i N
    (Nat.le_of_lt (mem_range.mp hi))]
  simp

/-- Exact chronological drift-energy increment.  Its middle term is the complete signed
triangular multi-prime covariance, now expressed using raw later residues. -/
theorem predictableDrift_energy_succ_eq_nested_residue_covariance (N : ℕ) :
    ‖predictableDrift (N + 1)‖ ^ 2 = ‖predictableDrift N‖ ^ 2 +
      2 * ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) *
        (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          inner ℝ ((historySpace i).starProjection (residueVec (i + 1)))
            (residueVec (N + 1))) +
      ((ArithmeticFunction.moebius (N + 1) : ℤ) : ℝ) ^ 2 *
        ‖(historySpace N).starProjection (residueVec (N + 1))‖ ^ 2 := by
  rw [predictableDrift_succ, norm_add_sq (𝕜 := ℝ), inner_smul_right,
    predictableDrift_cross_eq_earlier_raw_residue_sum, norm_smul, Real.norm_eq_abs]
  simp only [RCLike.re_to_real]
  rw [mul_pow, sq_abs]
  ring

end RHTower.DeletionResidueMartingale
