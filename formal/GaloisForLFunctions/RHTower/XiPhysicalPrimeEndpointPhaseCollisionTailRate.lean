import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointUltravioletTail

/-!
# Quantitative phase-collision tail rate for physical prime endpoints

Finite atomic Wiener convergence is made effective for inverse-square ultraviolet tails.  A
nontrivial unit phase has tail at most `2 / (|1-w| (N+1)^2)`.  Expanding a finite exponential
pencil therefore exposes an explicit ordered-pair collision budget.  Specialization to physical
prime-log endpoints gives finite-frequency error bounds for both differentiated moments and raw
FCRJ amplitudes.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem summable_shift_invSq_real (N : ℕ) :
    Summable fun k : ℕ => ((((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹) := by
  have h := GaloisForLFunctions.HTGeometry.summable_shift_rpow
    (q := -1) (by norm_num) N
  have h' : Summable fun k : ℕ => ((N : ℝ) + 1 + (k : ℝ)) ^ (-2 : ℝ) := by
    convert h using 1
    norm_num
  refine h'.congr fun k => ?_
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg (by positivity)]
  congr 1
  exact Real.rpow_natCast _ 2

private theorem summable_unitPhase_invSqTail
    {w : ℂ} (hw : ‖w‖ = 1) (N : ℕ) :
    Summable fun k : ℕ =>
      w ^ (N + 1 + k) / ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded (summable_shift_invSq_real N) fun k => ?_
  rw [norm_div, norm_pow, hw, one_pow]
  have hden : 0 ≤ (((N + 1 + k : ℕ) : ℝ) ^ 2) := sq_nonneg _
  rw [norm_real, Real.norm_of_nonneg hden, one_div]
  push_cast
  rfl

/-- A nonconstant unit phase has an explicit inverse-square tail bound. -/
theorem norm_tsum_unitPhase_invSqTail_le
    {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N : ℕ) :
    ‖∑' k : ℕ,
        w ^ (N + 1 + k) / ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤
      2 / (‖1 - w‖ * ((N + 1 : ℕ) : ℝ) ^ 2) := by
  let u : ℕ → ℝ := fun k => (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹
  let f : ℕ → ℂ := fun k => w ^ (N + 1 + k) * (u k : ℂ)
  have hu : Summable u := summable_shift_invSq_real N
  have hushu : Summable fun k : ℕ => u (k + 1) :=
    hu.comp_injective Nat.succ_injective
  have hv : Summable fun k : ℕ => u k - u (k + 1) := hu.sub hushu
  have hvnonneg (k : ℕ) : 0 ≤ u k - u (k + 1) := by
    dsimp only [u]
    have hx : 0 < (N : ℝ) + 1 + (k : ℝ) := by positivity
    have hxp : (N : ℝ) + 1 + ((k + 1 : ℕ) : ℝ) =
        ((N : ℝ) + 1 + (k : ℝ)) + 1 := by push_cast; ring
    rw [hxp, sub_nonneg]
    apply (inv_le_inv₀ (sq_pos_of_pos (by linarith)) (sq_pos_of_pos hx)).2
    nlinarith
  have htsumv : (∑' k : ℕ, (u k - u (k + 1))) = u 0 := by
    rw [hu.tsum_sub hushu, hu.tsum_eq_zero_add]
    ring
  have hf : Summable f := by
    have h := summable_unitPhase_invSqTail hw N
    refine h.congr fun k => ?_
    simp only [f, u, div_eq_mul_inv]
    congr 2
    push_cast
    norm_num
  have hvar : Summable fun k : ℕ =>
      w ^ (N + 2 + k) * ((u k - u (k + 1) : ℝ) : ℂ) := by
    refine Summable.of_norm_bounded hv fun k => ?_
    rw [norm_mul, norm_pow, hw, one_pow, norm_real,
      Real.norm_of_nonneg (hvnonneg k)]
    simp
  have hfsucc : Summable fun k : ℕ => f (k + 1) :=
    hf.comp_injective Nat.succ_injective
  have hwf : Summable fun k : ℕ => w * f k := hf.mul_left w
  have hdiff : (∑' k : ℕ, w * f k) - (∑' k : ℕ, f (k + 1)) =
      ∑' k : ℕ, w ^ (N + 2 + k) * ((u k - u (k + 1) : ℝ) : ℂ) := by
    rw [← hwf.tsum_sub hfsucc]
    apply tsum_congr
    intro k
    simp only [f]
    push_cast
    have hE1 : N + 2 + k = (N + 1 + k) + 1 := by omega
    have hE2 : N + 1 + (k + 1) = N + 2 + k := by omega
    rw [hE2, hE1, pow_succ']
    ring
  have hid : (1 - w) * (∑' k : ℕ, f k) =
      w ^ (N + 1) * (u 0 : ℂ) -
        ∑' k : ℕ, w ^ (N + 2 + k) * ((u k - u (k + 1) : ℝ) : ℂ) := by
    rw [sub_mul, one_mul, ← tsum_mul_left, hf.tsum_eq_zero_add]
    rw [show f 0 = w ^ (N + 1) * (u 0 : ℂ) by simp [f]]
    rw [← hdiff]
    ring
  have hnormvar : ‖∑' k : ℕ,
      w ^ (N + 2 + k) * ((u k - u (k + 1) : ℝ) : ℂ)‖ ≤ u 0 := by
    refine (norm_tsum_le_tsum_norm hvar.norm).trans ?_
    rw [show (∑' k : ℕ,
        ‖w ^ (N + 2 + k) * ((u k - u (k + 1) : ℝ) : ℂ)‖) =
        ∑' k : ℕ, (u k - u (k + 1)) by
          apply tsum_congr
          intro k
          rw [norm_mul, norm_pow, hw, one_pow, norm_real,
            Real.norm_of_nonneg (hvnonneg k)]
          simp]
    rw [htsumv]
  have hmul : ‖1 - w‖ * ‖∑' k : ℕ, f k‖ ≤ 2 * u 0 := by
    rw [← norm_mul, hid]
    refine (norm_sub_le _ _).trans ?_
    have hhead : ‖w ^ (N + 1) * (u 0 : ℂ)‖ = u 0 := by
      rw [norm_mul, norm_pow, hw, one_pow, norm_real,
        Real.norm_of_nonneg (by dsimp only [u]; positivity)]
      simp
    rw [hhead]
    linarith
  have hnorm1 : 0 < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1.symm)
  have hbound : ‖∑' k : ℕ, f k‖ ≤ 2 * u 0 / ‖1 - w‖ := by
    exact (le_div_iff₀ hnorm1).2 (by simpa [mul_comm] using hmul)
  have htarget : (2 * u 0 / ‖1 - w‖) =
      2 / (‖1 - w‖ * ((N + 1 : ℕ) : ℝ) ^ 2) := by
    dsimp only [u]
    push_cast
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    field_simp
    ring
  rw [← htarget]
  have htf : (∑' k : ℕ,
      w ^ (N + 1 + k) / ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) =
      ∑' k : ℕ, f k := by
    apply tsum_congr
    intro k
    simp only [f, u, div_eq_mul_inv]
    congr 2
    push_cast
    norm_num
  rw [htf]
  exact hbound

/-- Inverse-square ultraviolet tail of a finite exponential pencil. -/
def finiteExponentialPencilInvSqTail {ι : Type*}
    (s : Finset ι) (c z : ι → ℂ) (N : ℕ) : ℂ :=
  ∑' k : ℕ,
    star (finiteExponentialPencil s c z (N + 1 + k)) *
      finiteExponentialPencil s c z (N + 1 + k) /
        ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)

/-- The complex pencil tail is the real norm-square tail embedded in `ℂ`. -/
theorem finiteExponentialPencilInvSqTail_eq_ofReal_norm_sq
    {ι : Type*} (s : Finset ι) (c z : ι → ℂ) (N : ℕ) :
    finiteExponentialPencilInvSqTail s c z N =
      ((∑' k : ℕ,
        ‖finiteExponentialPencil s c z (N + 1 + k)‖ ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [finiteExponentialPencilInvSqTail]
  calc
    _ = ∑' k : ℕ,
        ((‖finiteExponentialPencil s c z (N + 1 + k)‖ ^ 2 /
          ((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro k
      have hsq :
          star (finiteExponentialPencil s c z (N + 1 + k)) *
              finiteExponentialPencil s c z (N + 1 + k) =
            ((‖finiteExponentialPencil s c z (N + 1 + k)‖ ^ 2 : ℝ) : ℂ) := by
        change (starRingEnd ℂ) (finiteExponentialPencil s c z (N + 1 + k)) *
            finiteExponentialPencil s c z (N + 1 + k) = _
        calc
          _ = (‖finiteExponentialPencil s c z (N + 1 + k)‖ : ℂ) ^ 2 :=
            Complex.conj_mul' _
          _ = _ := by push_cast; rfl
      rw [hsq]
      push_cast
      rfl
    _ = _ := by rw [Complex.ofReal_tsum]

private theorem finiteExponentialPencilInvSqTail_expand
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (N : ℕ) :
    finiteExponentialPencilInvSqTail s c z N =
      ∑ i ∈ s, ∑ j ∈ s, star (c i) * c j *
        ∑' k : ℕ, (star (z i) * z j) ^ (N + 1 + k) /
          ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hphase (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ‖star (z i) * z j‖ = 1 := by
    rw [norm_mul, norm_star, hz i hi, hz j hj, one_mul]
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Summable fun k : ℕ => star (c i) * c j *
        ((star (z i) * z j) ^ (N + 1 + k) /
          ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) :=
    (summable_unitPhase_invSqTail (hphase i hi j hj) N).mul_left _
  rw [finiteExponentialPencilInvSqTail]
  calc
    (∑' k : ℕ, star (finiteExponentialPencil s c z (N + 1 + k)) *
        finiteExponentialPencil s c z (N + 1 + k) /
          ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) =
      ∑' k : ℕ, ∑ i ∈ s, ∑ j ∈ s, star (c i) * c j *
        ((star (z i) * z j) ^ (N + 1 + k) /
          ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) := by
      apply tsum_congr
      intro k
      simp only [finiteExponentialPencil]
      change (starRingEnd ℂ) (∑ i ∈ s, c i * z i ^ (N + 1 + k)) *
          (∑ j ∈ s, c j * z j ^ (N + 1 + k)) /
            ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) = _
      rw [map_sum]
      simp_rw [map_mul, map_pow, starRingEnd_apply]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_pow]
      ring_nf
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑' k : ℕ, star (c i) * c j *
        ((star (z i) * z j) ^ (N + 1 + k) /
          ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) := by
      rw [Summable.tsum_finsetSum (fun i hi =>
        summable_sum fun j hj => hpair i hi j hj)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Summable.tsum_finsetSum (fun j hj => hpair i hi j hj)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [tsum_mul_left]

private theorem abs_mul_invSqTail_sub_one_le (N : ℕ) (hN : 1 ≤ N) :
    |(N : ℝ) * (∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹) - 1| ≤
      1 / ((N : ℝ) + 1) := by
  have htail :
      (∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹) =
        ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ ((-1 : ℝ) - 1) := by
    apply tsum_congr
    intro k
    rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
      show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (by positivity)]
    exact congrArg Inv.inv (Real.rpow_natCast _ 2).symm
  have hlo := GaloisForLFunctions.HTGeometry.tsum_shift_rpow_ge
    (q := (-1 : ℝ)) (by norm_num) N
  have hup := GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le
    (q := (-1 : ℝ)) (by norm_num) hN
  rw [← htail, Real.rpow_neg_one] at hlo hup
  norm_num at hlo hup
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hupper : (N : ℝ) * (∑' k : ℕ,
      (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹) ≤ 1 := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 1 := by field_simp
  have hlower : (N : ℝ) / ((N : ℝ) + 1) ≤
      (N : ℝ) * (∑' k : ℕ,
        (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹) := by
    calc
      _ = (N : ℝ) * (((N : ℝ) + 1)⁻¹) := by rw [div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  have hid : 1 - (N : ℝ) / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) := by
    field_simp
    ring
  rw [← hid]
  linarith

/-- Ordered pairwise collision cost for a finite exponential pencil. -/
def finiteExponentialPencilCollisionBudget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c z : ι → ℂ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    if i = j then 0 else
      2 * ‖c i‖ * ‖c j‖ / ‖1 - star (z i) * z j‖

private theorem norm_diagonal_invSqTail_error_le (c : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ‖(N : ℂ) * (star c * c *
        ∑' k : ℕ, (1 : ℂ) ^ (N + 1 + k) /
          ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) -
      ((‖c‖ ^ 2 : ℝ) : ℂ)‖ ≤ ‖c‖ ^ 2 / ((N : ℝ) + 1) := by
  let T : ℝ := ∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹
  have htail :
      (∑' k : ℕ, (1 : ℂ) ^ (N + 1 + k) /
        ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) = (T : ℂ) := by
    calc
      _ = ∑' k : ℕ, (((((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹ : ℝ) : ℂ) := by
        apply tsum_congr
        intro k
        simp only [one_pow, one_div]
        push_cast
        rfl
      _ = (T : ℂ) := by rw [Complex.ofReal_tsum]
  have hcc : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    change (starRingEnd ℂ) c * c = _
    calc
      _ = (‖c‖ : ℂ) ^ 2 := Complex.conj_mul' c
      _ = ((‖c‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  have herr := abs_mul_invSqTail_sub_one_le N hN
  change |(N : ℝ) * T - 1| ≤ 1 / ((N : ℝ) + 1) at herr
  rw [htail, hcc]
  have heq :
      (N : ℂ) * (((‖c‖ ^ 2 : ℝ) : ℂ) * (T : ℂ)) -
          ((‖c‖ ^ 2 : ℝ) : ℂ) =
        ((‖c‖ ^ 2 * ((N : ℝ) * T - 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖c‖)]
  simpa [div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_left herr (sq_nonneg ‖c‖))

/-- Effective inverse-square Wiener law for a finite pencil of distinct unit modes. -/
theorem norm_natCast_mul_finiteExponentialPencilInvSqTail_sub_energy_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : Set.InjOn z (s : Set ι))
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(N : ℂ) * finiteExponentialPencilInvSqTail s c z N -
        ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (∑ i ∈ s, ‖c i‖ ^ 2) / ((N : ℝ) + 1) +
        (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
          finiteExponentialPencilCollisionBudget s c z := by
  have hphase (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      star (z i) * z j = 1 ↔ i = j := by
    have hui : z i * star (z i) = 1 := by
      simpa [hz i hi] using Complex.mul_conj' (z i)
    have hsi : star (z i) * z i = 1 := by
      simpa [hz i hi] using Complex.conj_mul' (z i)
    constructor
    · intro h
      exact (hinj hj hi (calc
        z j = 1 * z j := (one_mul _).symm
        _ = (z i * star (z i)) * z j := by rw [hui]
        _ = z i * (star (z i) * z j) := by rw [mul_assoc]
        _ = z i := by rw [h, mul_one])).symm
    · intro h
      subst j
      exact hsi
  let Q : ι → ι → ℂ := fun i j =>
    star (c i) * c j *
      ∑' k : ℕ, (star (z i) * z j) ^ (N + 1 + k) /
        ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)
  let E : ι → ι → ℂ := fun i j =>
    if i = j then ((‖c i‖ ^ 2 : ℝ) : ℂ) else 0
  have henergyPair :
      (∑ i ∈ s, ∑ j ∈ s, E i j) =
        ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = ∑ i ∈ s, ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · simp [E]
        · intro j hj hji
          simp [E, Ne.symm hji]
        · intro hi'
          exact (hi' hi).elim
      _ = _ := by push_cast; rfl
  have herror :
      (N : ℂ) * finiteExponentialPencilInvSqTail s c z N -
          ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ s, ∑ j ∈ s, ((N : ℂ) * Q i j - E i j) := by
    rw [finiteExponentialPencilInvSqTail_expand s c z hz N, ← henergyPair]
    change (N : ℂ) * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
        ∑ i ∈ s, ∑ j ∈ s, E i j = _
    calc
      _ = (∑ i ∈ s, ∑ j ∈ s, (N : ℂ) * Q i j) -
          ∑ i ∈ s, ∑ j ∈ s, E i j := by simp_rw [Finset.mul_sum]
      _ = ∑ i ∈ s,
          ((∑ j ∈ s, (N : ℂ) * Q i j) - ∑ j ∈ s, E i j) := by
            rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_sub_distrib]
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ‖(N : ℂ) * Q i j - E i j‖ ≤
        if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else
          (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
            (2 * ‖c i‖ * ‖c j‖ / ‖1 - star (z i) * z j‖) := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have hself := (hphase i hi i hi).2 rfl
      simp only [Q, E, if_pos, hself]
      exact norm_diagonal_invSqTail_error_le (c i) N hN
    · rw [if_neg hij]
      have hw : ‖star (z i) * z j‖ = 1 := by
        rw [norm_mul, norm_star, hz i hi, hz j hj, one_mul]
      have hw1 : star (z i) * z j ≠ 1 :=
        fun h => hij ((hphase i hi j hj).1 h)
      have htail := norm_tsum_unitPhase_invSqTail_le hw hw1 N
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hden : 0 < ‖1 - star (z i) * z j‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hw1.symm)
      simp only [Q, E, if_neg hij, sub_zero]
      calc
        ‖(N : ℂ) * (star (c i) * c j *
            ∑' k : ℕ, (star (z i) * z j) ^ (N + 1 + k) /
              ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))‖ =
            (N : ℝ) * (‖c i‖ * ‖c j‖) *
              ‖∑' k : ℕ, (star (z i) * z j) ^ (N + 1 + k) /
                ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖ := by
          simp only [norm_mul, Complex.norm_natCast, norm_star]
          ring
        _ ≤ (N : ℝ) * (‖c i‖ * ‖c j‖) *
            (2 / (‖1 - star (z i) * z j‖ * ((N + 1 : ℕ) : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left htail
            (mul_nonneg hN0 (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
            (2 * ‖c i‖ * ‖c j‖ / ‖1 - star (z i) * z j‖) := by
          push_cast
          field_simp
  have hdiag :
      (∑ i ∈ s, ∑ j ∈ s,
        if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else 0) =
          (∑ i ∈ s, ‖c i‖ ^ 2) / ((N : ℝ) + 1) := by
    calc
      _ = ∑ i ∈ s, ‖c i‖ ^ 2 / ((N : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          simp [Ne.symm hji]
        · intro hi'
          exact (hi' hi).elim
      _ = _ := by rw [← Finset.sum_div]
  have hoff :
      (∑ i ∈ s, ∑ j ∈ s,
        if i = j then 0 else
          (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
            (2 * ‖c i‖ * ‖c j‖ / ‖1 - star (z i) * z j‖)) =
        (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
          finiteExponentialPencilCollisionBudget s c z := by
    rw [finiteExponentialPencilCollisionBudget]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  rw [herror]
  calc
    ‖∑ i ∈ s, ∑ j ∈ s, ((N : ℂ) * Q i j - E i j)‖ ≤
        ∑ i ∈ s, ‖∑ j ∈ s, ((N : ℂ) * Q i j - E i j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖(N : ℂ) * Q i j - E i j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        (if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else
          (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
            (2 * ‖c i‖ * ‖c j‖ / ‖1 - star (z i) * z j‖)) := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = (∑ i ∈ s, ∑ j ∈ s,
          if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else 0) +
        ∑ i ∈ s, ∑ j ∈ s,
          if i = j then 0 else
            (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
              (2 * ‖c i‖ * ‖c j‖ / ‖1 - star (z i) * z j‖) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ = _ := by rw [hdiag, hoff]

/-- Pairwise endpoint collision cost for a physical prime-log aperture packet. -/
def xiPhysicalPrimeLogEndpointCollisionBudget
    (P : Finset Nat.Primes) (A m k : ℝ) : ℝ :=
  finiteExponentialPencilCollisionBudget
    (xiPhysicalPrimeLogEndpointNodeSet P A m k)
    (xiPhysicalPrimeLogEndpointCircleJump P A m k)
    (fun x : AddCircle A => fourier 1 x)

private theorem fourier_one_injective_for_collision
    {A : ℝ} (hA : 0 < A) :
    Function.Injective (fun x : AddCircle A => fourier 1 x) := by
  intro x y hxy
  change fourier 1 x = fourier 1 y at hxy
  rw [fourier_one, fourier_one] at hxy
  apply AddCircle.injective_toCircle hA.ne'
  exact Subtype.ext hxy

/-- Explicit finite-frequency ultraviolet-tail error for physical endpoint moments. -/
theorem abs_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail_sub_jumpCharge_le
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ)
    (N : ℕ) (hN : 1 ≤ N) :
    |(N : ℝ) * ∑' r : ℕ,
        ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
          ((N + 1 + r : ℕ) : ℝ) ^ 2 -
      ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2| ≤
      (∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2) /
          ((N : ℝ) + 1) +
      (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
        xiPhysicalPrimeLogEndpointCollisionBudget P A m k := by
  have h := norm_natCast_mul_finiteExponentialPencilInvSqTail_sub_energy_le
    (xiPhysicalPrimeLogEndpointNodeSet P A m k)
    (xiPhysicalPrimeLogEndpointCircleJump P A m k)
    (fun x : AddCircle A => fourier 1 x)
    (by intro x hx; simp)
    (fourier_one_injective_for_collision hA).injOn N hN
  rw [finiteExponentialPencilInvSqTail_eq_ofReal_norm_sq] at h
  have hcastN : (N : ℂ) = ((N : ℝ) : ℂ) := by norm_num
  rw [hcastN] at h
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, norm_real,
    Real.norm_eq_abs] at h
  simpa only [xiPhysicalPrimeLogEndpointCircleMoment,
    finiteExponentialPencil, xiPhysicalPrimeLogEndpointCollisionBudget,
    norm_real, Real.norm_eq_abs] using h

private theorem normSq_xiPhysicalApertureCharacterRate_nat_for_collision
    {A : ℝ} (hA : 0 < A) (n : ℕ) :
    Complex.normSq (xiPhysicalApertureCharacterRate A (n : ℤ)) =
      4 * Real.pi ^ 2 * (n : ℝ) ^ 2 / A ^ 2 := by
  rw [xiPhysicalApertureCharacterRate, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_I]
  field_simp [hA.ne']
  norm_cast
  ring

private theorem normSq_xiPhysicalPrimeLogCharacterAmplitude_eq_endpointMoment_for_collision
    {P : Finset Nat.Primes} {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    {n : ℕ} (hn : n ≠ 0) :
    Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A (n : ℤ) m k) =
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        (‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 / (n : ℝ) ^ 2) := by
  rw [xiPhysicalPrimeLogEndpointCircleMoment_eq_rate_mul_amplitude hA hn hactive,
    Complex.sq_norm, Complex.normSq_mul,
    normSq_xiPhysicalApertureCharacterRate_nat_for_collision hA]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hA.ne', hnR, hpi]

/-- Explicit finite-frequency ultraviolet-tail error for raw physical FCRJ amplitudes. -/
theorem abs_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail_sub_jumpCharge_le
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (N : ℕ) (hN : 1 ≤ N) :
    |(N : ℝ) * ∑' r : ℕ,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k) -
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
          ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2| ≤
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        ((∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
            ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2) /
              ((N : ℝ) + 1) +
          (N : ℝ) / ((N : ℝ) + 1) ^ 2 *
            xiPhysicalPrimeLogEndpointCollisionBudget P A m k) := by
  have hmoment :=
    abs_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail_sub_jumpCharge_le
      P hA m k N hN
  have htsum :
      (∑' r : ℕ, Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k)) =
        (A ^ 2 / (4 * Real.pi ^ 2)) * ∑' r : ℕ,
          ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
            ((N + 1 + r : ℕ) : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    exact
      normSq_xiPhysicalPrimeLogCharacterAmplitude_eq_endpointMoment_for_collision
        hA hactive (by omega)
  have hcoef : 0 ≤ A ^ 2 / (4 * Real.pi ^ 2) := by positivity
  rw [htsum]
  have heq :
      (N : ℝ) * ((A ^ 2 / (4 * Real.pi ^ 2)) *
          ∑' r : ℕ,
            ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
              ((N + 1 + r : ℕ) : ℝ) ^ 2) -
        (A ^ 2 / (4 * Real.pi ^ 2)) *
          ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
            ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2 =
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        ((N : ℝ) * ∑' r : ℕ,
            ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
              ((N + 1 + r : ℕ) : ℝ) ^ 2 -
          ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
            ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2) := by
    ring
  rw [heq, abs_mul, abs_of_nonneg hcoef]
  exact mul_le_mul_of_nonneg_left hmoment hcoef

private theorem tsum_shift_invSq_le_inv (N : ℕ) (hN : 1 ≤ N) :
    (∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹) ≤ 1 / (N : ℝ) := by
  have htail :
      (∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹) =
        ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ ((-1 : ℝ) - 1) := by
    apply tsum_congr
    intro k
    rw [show ((-1 : ℝ) - 1) = -2 by norm_num,
      show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (by positivity)]
    exact congrArg Inv.inv (Real.rpow_natCast _ 2).symm
  rw [htail]
  have h := GaloisForLFunctions.HTGeometry.tsum_shift_rpow_le
    (q := (-1 : ℝ)) (by norm_num) hN
  simpa [Real.rpow_neg_one] using h

/-- A unit-phase inverse-square tail is bounded simultaneously by absolute mass and oscillatory
separation.  The minimum resolves the transition at chord scale `1/N`. -/
theorem norm_tsum_unitPhase_invSqTail_le_min
    {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑' k : ℕ,
        w ^ (N + 1 + k) / ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤
      min (1 / (N : ℝ))
        (2 / (‖1 - w‖ * ((N + 1 : ℕ) : ℝ) ^ 2)) := by
  apply le_min
  · refine (norm_tsum_le_tsum_norm
      (summable_unitPhase_invSqTail hw N).norm).trans ?_
    rw [show (∑' k : ℕ,
        ‖w ^ (N + 1 + k) /
          ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖) =
        ∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ)) ^ 2)⁻¹ by
          apply tsum_congr
          intro k
          rw [norm_div, norm_pow, hw, one_pow]
          have hden : 0 ≤ (((N + 1 + k : ℕ) : ℝ) ^ 2) := sq_nonneg _
          rw [norm_real, Real.norm_of_nonneg hden, one_div]
          push_cast
          rfl]
    exact tsum_shift_invSq_le_inv N hN
  · exact norm_tsum_unitPhase_invSqTail_le hw hw1 N

/-- Frequency-resolved ordered collision cost.  Each pair is capped by its full coefficient mass
when its chord is smaller than the `1/N` resolution scale. -/
def finiteExponentialPencilResolvedCollisionBudget {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c z : ι → ℂ) (N : ℕ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    if i = j then 0 else
      min (‖c i‖ * ‖c j‖)
        ((N : ℝ) * (‖c i‖ * ‖c j‖) *
          (2 / (‖1 - star (z i) * z j‖ * ((N + 1 : ℕ) : ℝ) ^ 2)))

/-- Effective inverse-square Wiener law with pairwise saturation at the frequency-resolution
scale.  Unlike a raw inverse-chord budget, the right side never charges more than full pair mass. -/
theorem norm_natCast_mul_finiteExponentialPencilInvSqTail_sub_energy_le_resolved
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : Set.InjOn z (s : Set ι))
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(N : ℂ) * finiteExponentialPencilInvSqTail s c z N -
        ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ)‖ ≤
      (∑ i ∈ s, ‖c i‖ ^ 2) / ((N : ℝ) + 1) +
        finiteExponentialPencilResolvedCollisionBudget s c z N := by
  have hphase (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      star (z i) * z j = 1 ↔ i = j := by
    have hui : z i * star (z i) = 1 := by
      simpa [hz i hi] using Complex.mul_conj' (z i)
    have hsi : star (z i) * z i = 1 := by
      simpa [hz i hi] using Complex.conj_mul' (z i)
    constructor
    · intro h
      exact (hinj hj hi (calc
        z j = 1 * z j := (one_mul _).symm
        _ = (z i * star (z i)) * z j := by rw [hui]
        _ = z i * (star (z i) * z j) := by rw [mul_assoc]
        _ = z i := by rw [h, mul_one])).symm
    · intro h
      subst j
      exact hsi
  let Q : ι → ι → ℂ := fun i j =>
    star (c i) * c j *
      ∑' k : ℕ, (star (z i) * z j) ^ (N + 1 + k) /
        ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)
  let E : ι → ι → ℂ := fun i j =>
    if i = j then ((‖c i‖ ^ 2 : ℝ) : ℂ) else 0
  have henergyPair :
      (∑ i ∈ s, ∑ j ∈ s, E i j) =
        ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = ∑ i ∈ s, ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · simp [E]
        · intro j hj hji
          simp [E, Ne.symm hji]
        · intro hi'
          exact (hi' hi).elim
      _ = _ := by push_cast; rfl
  have herror :
      (N : ℂ) * finiteExponentialPencilInvSqTail s c z N -
          ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ s, ∑ j ∈ s, ((N : ℂ) * Q i j - E i j) := by
    rw [finiteExponentialPencilInvSqTail_expand s c z hz N, ← henergyPair]
    change (N : ℂ) * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
        ∑ i ∈ s, ∑ j ∈ s, E i j = _
    calc
      _ = (∑ i ∈ s, ∑ j ∈ s, (N : ℂ) * Q i j) -
          ∑ i ∈ s, ∑ j ∈ s, E i j := by simp_rw [Finset.mul_sum]
      _ = ∑ i ∈ s,
          ((∑ j ∈ s, (N : ℂ) * Q i j) - ∑ j ∈ s, E i j) := by
            rw [Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_sub_distrib]
  have hpair (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ‖(N : ℂ) * Q i j - E i j‖ ≤
        if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else
          min (‖c i‖ * ‖c j‖)
            ((N : ℝ) * (‖c i‖ * ‖c j‖) *
              (2 / (‖1 - star (z i) * z j‖ * ((N + 1 : ℕ) : ℝ) ^ 2))) := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have hself := (hphase i hi i hi).2 rfl
      simp only [Q, E, if_pos, hself]
      exact norm_diagonal_invSqTail_error_le (c i) N hN
    · rw [if_neg hij]
      have hw : ‖star (z i) * z j‖ = 1 := by
        rw [norm_mul, norm_star, hz i hi, hz j hj, one_mul]
      have hw1 : star (z i) * z j ≠ 1 :=
        fun h => hij ((hphase i hi j hj).1 h)
      have htail := norm_tsum_unitPhase_invSqTail_le_min hw hw1 N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
      have hfac : 0 ≤ (N : ℝ) * (‖c i‖ * ‖c j‖) := by positivity
      simp only [Q, E, if_neg hij, sub_zero]
      calc
        ‖(N : ℂ) * (star (c i) * c j *
            ∑' k : ℕ, (star (z i) * z j) ^ (N + 1 + k) /
              ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))‖ =
            (N : ℝ) * (‖c i‖ * ‖c j‖) *
              ‖∑' k : ℕ, (star (z i) * z j) ^ (N + 1 + k) /
                ((((N + 1 + k : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖ := by
          simp only [norm_mul, Complex.norm_natCast, norm_star]
          ring
        _ ≤ (N : ℝ) * (‖c i‖ * ‖c j‖) *
            min (1 / (N : ℝ))
              (2 / (‖1 - star (z i) * z j‖ * ((N + 1 : ℕ) : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left htail hfac
        _ = min (‖c i‖ * ‖c j‖)
            ((N : ℝ) * (‖c i‖ * ‖c j‖) *
              (2 / (‖1 - star (z i) * z j‖ * ((N + 1 : ℕ) : ℝ) ^ 2))) := by
          rw [mul_min_of_nonneg _ _ hfac]
          congr 1
          field_simp
  have hdiag :
      (∑ i ∈ s, ∑ j ∈ s,
        if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else 0) =
          (∑ i ∈ s, ‖c i‖ ^ 2) / ((N : ℝ) + 1) := by
    calc
      _ = ∑ i ∈ s, ‖c i‖ ^ 2 / ((N : ℝ) + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · simp
        · intro j hj hji
          simp [Ne.symm hji]
        · intro hi'
          exact (hi' hi).elim
      _ = _ := by rw [← Finset.sum_div]
  rw [herror]
  calc
    ‖∑ i ∈ s, ∑ j ∈ s, ((N : ℂ) * Q i j - E i j)‖ ≤
        ∑ i ∈ s, ‖∑ j ∈ s, ((N : ℂ) * Q i j - E i j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖(N : ℂ) * Q i j - E i j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        (if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else
          min (‖c i‖ * ‖c j‖)
            ((N : ℝ) * (‖c i‖ * ‖c j‖) *
              (2 / (‖1 - star (z i) * z j‖ * ((N + 1 : ℕ) : ℝ) ^ 2)))) := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = (∑ i ∈ s, ∑ j ∈ s,
          if i = j then ‖c i‖ ^ 2 / ((N : ℝ) + 1) else 0) +
        finiteExponentialPencilResolvedCollisionBudget s c z N := by
      rw [finiteExponentialPencilResolvedCollisionBudget,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ = _ := by rw [hdiag]

/-- Frequency-resolved endpoint collision cost for a physical prime-log aperture packet. -/
def xiPhysicalPrimeLogEndpointResolvedCollisionBudget
    (P : Finset Nat.Primes) (A m k : ℝ) (N : ℕ) : ℝ :=
  finiteExponentialPencilResolvedCollisionBudget
    (xiPhysicalPrimeLogEndpointNodeSet P A m k)
    (xiPhysicalPrimeLogEndpointCircleJump P A m k)
    (fun x : AddCircle A => fourier 1 x) N

/-- Physical endpoint-moment tail error with collision costs saturated at frequency resolution. -/
theorem abs_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail_sub_jumpCharge_le_resolved
    (P : Finset Nat.Primes) {A : ℝ} (hA : 0 < A) (m k : ℝ)
    (N : ℕ) (hN : 1 ≤ N) :
    |(N : ℝ) * ∑' r : ℕ,
        ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
          ((N + 1 + r : ℕ) : ℝ) ^ 2 -
      ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2| ≤
      (∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
        ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2) /
          ((N : ℝ) + 1) +
      xiPhysicalPrimeLogEndpointResolvedCollisionBudget P A m k N := by
  have h := norm_natCast_mul_finiteExponentialPencilInvSqTail_sub_energy_le_resolved
    (xiPhysicalPrimeLogEndpointNodeSet P A m k)
    (xiPhysicalPrimeLogEndpointCircleJump P A m k)
    (fun x : AddCircle A => fourier 1 x)
    (by intro x hx; simp)
    (fourier_one_injective_for_collision hA).injOn N hN
  rw [finiteExponentialPencilInvSqTail_eq_ofReal_norm_sq] at h
  have hcastN : (N : ℂ) = ((N : ℝ) : ℂ) := by norm_num
  rw [hcastN] at h
  rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, norm_real,
    Real.norm_eq_abs] at h
  simpa only [xiPhysicalPrimeLogEndpointCircleMoment,
    finiteExponentialPencil, xiPhysicalPrimeLogEndpointResolvedCollisionBudget,
    norm_real, Real.norm_eq_abs] using h

/-- Raw physical FCRJ tail error with collision costs saturated at frequency resolution. -/
theorem abs_xiPhysicalPrimeLogCharacterAmplitude_ultravioletTail_sub_jumpCharge_le_resolved
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (N : ℕ) (hN : 1 ≤ N) :
    |(N : ℝ) * ∑' r : ℕ,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k) -
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
          ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2| ≤
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        ((∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
            ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2) /
              ((N : ℝ) + 1) +
          xiPhysicalPrimeLogEndpointResolvedCollisionBudget P A m k N) := by
  have hmoment :=
    abs_xiPhysicalPrimeLogEndpointCircleMoment_ultravioletTail_sub_jumpCharge_le_resolved
      P hA m k N hN
  have htsum :
      (∑' r : ℕ, Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k)) =
        (A ^ 2 / (4 * Real.pi ^ 2)) * ∑' r : ℕ,
          ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
            ((N + 1 + r : ℕ) : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    exact
      normSq_xiPhysicalPrimeLogCharacterAmplitude_eq_endpointMoment_for_collision
        hA hactive (by omega)
  have hcoef : 0 ≤ A ^ 2 / (4 * Real.pi ^ 2) := by positivity
  rw [htsum]
  have heq :
      (N : ℝ) * ((A ^ 2 / (4 * Real.pi ^ 2)) *
          ∑' r : ℕ,
            ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
              ((N + 1 + r : ℕ) : ℝ) ^ 2) -
        (A ^ 2 / (4 * Real.pi ^ 2)) *
          ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
            ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2 =
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        ((N : ℝ) * ∑' r : ℕ,
            ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
              ((N + 1 + r : ℕ) : ℝ) ^ 2 -
          ∑ x ∈ xiPhysicalPrimeLogEndpointNodeSet P A m k,
            ‖xiPhysicalPrimeLogEndpointCircleJump P A m k x‖ ^ 2) := by
    ring
  rw [heq, abs_mul, abs_of_nonneg hcoef]
  exact mul_le_mul_of_nonneg_left hmoment hcoef

end

end RHTower
