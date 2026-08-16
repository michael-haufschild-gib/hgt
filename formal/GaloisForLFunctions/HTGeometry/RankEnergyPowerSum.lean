import Mathlib.Analysis.MeanInequalitiesPow
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-!
# The sharp rank--energy law

A nonnegative spectral packet supported on at most `R` levels satisfies

`∑ aᵢ^k ≤ R^{1-k/p} (∑ aᵢ^p)^{k/p}`,   `0 < k ≤ p`,

which is Jensen for `x ↦ x^{p/k}` against uniform weights.  For a Hermitian matrix the `k`-th
trace power is the `k`-th power sum of the eigenvalues, so the same bound controls it by the rank
and the Schatten energy.  Equality is attained by a flat packet, so the bound is sharp and the
cutoff below the Schatten order is forced quantitatively rather than chosen.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **Rank--energy power-sum bound.**  Jensen for `x ↦ x^{p/k}` against uniform weights. -/
theorem sum_rpow_le_card_rpow_mul_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) {k p : ℝ} (hk : 0 < k) (hkp : k ≤ p) (hs : s.Nonempty) :
    ∑ i ∈ s, a i ^ k ≤ (s.card : ℝ) ^ (1 - k / p) * (∑ i ∈ s, a i ^ p) ^ (k / p) := by
  have hp : 0 < p := lt_of_lt_of_le hk hkp
  have hR : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  set S : ℝ := ∑ i ∈ s, a i ^ k with hS
  set T : ℝ := ∑ i ∈ s, a i ^ p with hT
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) k
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) p
  have hm : (1 : ℝ) ≤ p / k := (one_le_div hk).mpr hkp
  have hjensen := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => 1 / (s.card : ℝ))
    (fun i => a i ^ k) (fun i _ => by positivity)
    (by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp)
    (fun i hi => Real.rpow_nonneg (ha i hi) k) hm
  have hleft : (∑ i ∈ s, (1 / (s.card : ℝ)) * a i ^ k) = (1 / (s.card : ℝ)) * S := by
    rw [hS, Finset.mul_sum]
  have hright : (∑ i ∈ s, (1 / (s.card : ℝ)) * (a i ^ k) ^ (p / k))
      = (1 / (s.card : ℝ)) * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    rw [← Real.rpow_mul (ha i hi)]
    congr 1
    field_simp
  rw [hleft, hright] at hjensen
  -- raise to the reciprocal power
  have hpow := Real.rpow_le_rpow (by positivity) hjensen (le_of_lt (by positivity : (0:ℝ) < k / p))
  have hcollapse : (((1 / (s.card : ℝ)) * S) ^ (p / k)) ^ (k / p)
      = (1 / (s.card : ℝ)) * S := by
    rw [← Real.rpow_mul (by positivity)]
    rw [show p / k * (k / p) = 1 from by field_simp]
    exact Real.rpow_one _
  rw [hcollapse] at hpow
  -- unwind the normalisation
  have hsplit : ((1 / (s.card : ℝ)) * T) ^ (k / p)
      = (s.card : ℝ) ^ (-(k / p)) * T ^ (k / p) := by
    rw [Real.mul_rpow (by positivity) hTnn]
    congr 1
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt hR)]
    congr 1
    ring
  rw [hsplit] at hpow
  have hfinal : S ≤ (s.card : ℝ) * ((s.card : ℝ) ^ (-(k / p)) * T ^ (k / p)) := by
    have := mul_le_mul_of_nonneg_left hpow (le_of_lt hR)
    calc S = (s.card : ℝ) * ((1 / (s.card : ℝ)) * S) := by field_simp
      _ ≤ (s.card : ℝ) * ((s.card : ℝ) ^ (-(k / p)) * T ^ (k / p)) := this
  calc S ≤ (s.card : ℝ) * ((s.card : ℝ) ^ (-(k / p)) * T ^ (k / p)) := hfinal
    _ = (s.card : ℝ) ^ (1 - k / p) * T ^ (k / p) := by
        rw [← mul_assoc]
        congr 1
        rw [show (1 : ℝ) - k / p = 1 + -(k / p) from by ring, Real.rpow_add hR, Real.rpow_one]

/-- **The rank--energy law for a Hermitian matrix.**  The `k`-th power sum of the eigenvalues is
bounded by the rank to the power `1-k/p` times the `k/p` power of the `p`-th energy. -/
theorem abs_sum_eigenvalues_pow_le_rank_energy {n : ℕ} (hn : 0 < n)
    {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) {k p : ℝ} (hk : 0 < k) (hkp : k ≤ p) :
    |∑ i, |hB.eigenvalues i| ^ k|
      ≤ (n : ℝ) ^ (1 - k / p) * (∑ i, |hB.eigenvalues i| ^ p) ^ (k / p) := by
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hn
  have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by
    simp
  have hnn : (0 : ℝ) ≤ ∑ i, |hB.eigenvalues i| ^ k :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) k
  rw [abs_of_nonneg hnn, ← hcard]
  exact sum_rpow_le_card_rpow_mul_sum_rpow _ _ (fun i _ => abs_nonneg _) hk hkp hs

/-! ## The trace power of a Hermitian matrix -/

/-- A Hermitian power is the conjugate of the diagonal power. -/
theorem isHermitian_pow_eq_conj_diagonal {d : Type*} [Fintype d] [DecidableEq d]
    {H : Matrix d d ℂ} (hH : H.IsHermitian) (k : ℕ) :
    H ^ k = (hH.eigenvectorUnitary : Matrix d d ℂ) *
        Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) ^ k *
        star (hH.eigenvectorUnitary : Matrix d d ℂ) := by
  have hmem := hH.eigenvectorUnitary.2
  have hVs : star (hH.eigenvectorUnitary : Matrix d d ℂ) *
      (hH.eigenvectorUnitary : Matrix d d ℂ) = 1 := (Unitary.mem_iff.mp hmem).1
  have hsV : (hH.eigenvectorUnitary : Matrix d d ℂ) *
      star (hH.eigenvectorUnitary : Matrix d d ℂ) = 1 := (Unitary.mem_iff.mp hmem).2
  induction k with
  | zero => simpa using hsV.symm
  | succ k ih =>
      rw [pow_succ, ih, isHermitian_eq_conj_diagonal hH]
      rw [show ((hH.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) ^ k *
            star (hH.eigenvectorUnitary : Matrix d d ℂ)) *
          ((hH.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) *
            star (hH.eigenvectorUnitary : Matrix d d ℂ))
          = (hH.eigenvectorUnitary : Matrix d d ℂ) *
            Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) ^ k *
            (star (hH.eigenvectorUnitary : Matrix d d ℂ) *
              (hH.eigenvectorUnitary : Matrix d d ℂ)) *
            Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) *
            star (hH.eigenvectorUnitary : Matrix d d ℂ) from by
        simp [Matrix.mul_assoc]]
      rw [hVs, Matrix.mul_one, pow_succ]

/-- **The trace power of a Hermitian matrix is the eigenvalue power sum.** -/
theorem trace_pow_eq_sum_eigenvalues_pow {d : Type*} [Fintype d] [DecidableEq d]
    {H : Matrix d d ℂ} (hH : H.IsHermitian) (k : ℕ) :
    (H ^ k).trace = ∑ i, ((hH.eigenvalues i : ℂ)) ^ k := by
  have hmem := hH.eigenvectorUnitary.2
  have hVs : star (hH.eigenvectorUnitary : Matrix d d ℂ) *
      (hH.eigenvectorUnitary : Matrix d d ℂ) = 1 := (Unitary.mem_iff.mp hmem).1
  rw [isHermitian_pow_eq_conj_diagonal hH k, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hVs,
    Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]

/-- **(RE), the sharp rank--energy law for a Hermitian matrix.** -/
theorem norm_trace_pow_le_rank_energy {n : ℕ} (hn : 0 < n)
    {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) {k : ℕ} (hk : 0 < k) {p : ℝ}
    (hkp : (k : ℝ) ≤ p) :
    ‖(B ^ k).trace‖
      ≤ (n : ℝ) ^ (1 - (k : ℝ) / p) * (∑ i, |hB.eigenvalues i| ^ p) ^ ((k : ℝ) / p) := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbound : ‖(B ^ k).trace‖ ≤ ∑ i, |hB.eigenvalues i| ^ (k : ℝ) := by
    rw [trace_pow_eq_sum_eigenvalues_pow hB k]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.rpow_natCast]
  refine le_trans hbound ?_
  have := abs_sum_eigenvalues_pow_le_rank_energy hn hB hkr hkp
  rwa [abs_of_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)] at this

end GaloisForLFunctions.HTGeometry
