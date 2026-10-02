import GaloisForLFunctions.RHTower.Sieve.KuzminLandauInterval
import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality
import Mathlib.Analysis.SpecialFunctions.Sqrt
import GaloisForLFunctions.RHTower.Sieve.SeparatedRowSum
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The degree-two stationary root-phase matrix

The exact degree-two chi stationary phase contains exp(4*pi*i*sqrt(p*q)).
On the complete integer block [N,2N], Kuzmin-Landau bounds every off-diagonal
Gram entry by 7N/|p-q|, including every sample and the lattice band condition.
Harmonic row summation and finite Schur duality give squared operator bound
16N*(1+log(N+1)). Arbitrary complex coefficients and zero-extended prime
restrictions are admitted. This controls the leading stationary matrix;
it does not estimate the complete physical stationary remainder.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace
noncomputable section
namespace RHTower

/-- Complete integer-block row correlations of the degree-two stationary
root-phase matrix, with the literal phase and every sample retained. -/
theorem norm_sum_root_phase_row_correlation_le {N : ℕ} (hN : 1 ≤ N)
    {p q : ℝ} (hp : p ∈ Icc (N : ℝ) (2 * N))
    (hq : q ∈ Icc (N : ℝ) (2 * N)) (hpq : p < q) :
    ‖∑ j ∈ Finset.range (N + 1),
      Complex.exp (((4 * Real.pi * (Real.sqrt p - Real.sqrt q) *
        Real.sqrt ((N : ℝ) + j) : ℝ) : ℂ) * I)‖ ≤ 7 * (N : ℝ) / (q - p) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp0 : 0 < p := hN0.trans_le hp.1
  have hq0 : 0 < q := hN0.trans_le hq.1
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hdN : q - p ≤ N := by linarith only [hp.1, hq.2]
  have hsN := Real.sqrt_pos.mpr hN0
  have hroot : Real.sqrt p < Real.sqrt q := Real.sqrt_lt_sqrt hp0.le hpq
  have hdiff : (Real.sqrt q - Real.sqrt p) * (Real.sqrt p + Real.sqrt q) = q - p := by
    nlinarith only [Real.sq_sqrt hp0.le, Real.sq_sqrt hq0.le]
  let δ : ℝ := (q - p) / (4 * N)
  let g : ℝ → ℝ := fun x => 2 * (Real.sqrt p - Real.sqrt q) * Real.sqrt x
  let g' : ℝ → ℝ := fun x => (Real.sqrt p - Real.sqrt q) / Real.sqrt x
  have hδ : 0 < δ := div_pos hd (by positivity)
  have hδhi : δ ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * N)).mpr
    linarith only [hdN]
  have hxN (x : ℝ) (hx : x ∈ Icc (N : ℝ) ((N : ℝ) + N)) : x ∈ Icc (N : ℝ) (2 * N) :=
    ⟨hx.1, by linarith only [hx.2]⟩
  have hderiv (x : ℝ) (hx : x ∈ Icc (N : ℝ) ((N : ℝ) + N)) : HasDerivAt g (g' x) x := by
    have hx0 : 0 < x := hN0.trans_le hx.1
    have hb := (Real.hasDerivAt_sqrt hx0.ne').const_mul (2 * (Real.sqrt p - Real.sqrt q))
    have he : 2 * (Real.sqrt p - Real.sqrt q) * (1 / (2 * Real.sqrt x)) = g' x := by
      dsimp only [g']; ring
    exact he ▸ hb
  have hmono : MonotoneOn g' (Icc (N : ℝ) ((N : ℝ) + N)) := by
    intro x hx y hy hxy
    have hx0 := Real.sqrt_pos.mpr (hN0.trans_le hx.1)
    have hh := div_le_div_of_nonneg_left (sub_nonneg.mpr hroot.le) hx0 (Real.sqrt_le_sqrt hxy)
    dsimp only [g']
    rw [show Real.sqrt p - Real.sqrt q = -(Real.sqrt q - Real.sqrt p) by ring, neg_div, neg_div]
    exact neg_le_neg hh
  have hbounds (x : ℝ) (hx : x ∈ Icc (N : ℝ) ((N : ℝ) + N)) :
      -(1 / 2 : ℝ) ≤ g' x ∧ g' x ≤ -δ := by
    have hx0 : 0 < x := hN0.trans_le hx.1
    let D : ℝ := (Real.sqrt p + Real.sqrt q) * Real.sqrt x
    have hD0 : 0 < D := mul_pos (add_pos (Real.sqrt_pos.mpr hp0) (Real.sqrt_pos.mpr hq0))
      (Real.sqrt_pos.mpr hx0)
    have hDlo : 2 * (N : ℝ) ≤ D := by
      calc
        _ = (Real.sqrt (N : ℝ) + Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) := by
          nlinarith only [Real.sq_sqrt hN0.le]
        _ ≤ _ := mul_le_mul (add_le_add (Real.sqrt_le_sqrt hp.1) (Real.sqrt_le_sqrt hq.1))
          (Real.sqrt_le_sqrt hx.1) (Real.sqrt_nonneg _) (by positivity)
    have hDhi : D ≤ 4 * (N : ℝ) := by
      calc
        _ ≤ (Real.sqrt (2 * (N : ℝ)) + Real.sqrt (2 * (N : ℝ))) * Real.sqrt (2 * (N : ℝ)) :=
          mul_le_mul (add_le_add (Real.sqrt_le_sqrt hp.2) (Real.sqrt_le_sqrt hq.2))
            (Real.sqrt_le_sqrt (hxN x hx).2) (Real.sqrt_nonneg _) (by positivity)
        _ = _ := by nlinarith only [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * N)]
    have hlo : δ ≤ (q - p) / D := div_le_div_of_nonneg_left hd.le hD0 hDhi
    have hhi : (q - p) / D ≤ 1 / 2 := by
      calc
        _ ≤ (q - p) / (2 * N) := div_le_div_of_nonneg_left hd.le (by positivity) hDlo
        _ ≤ _ := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mpr (by linarith only [hdN])
    have heq : g' x = -((q - p) / D) := by
      dsimp only [g', D]
      field_simp
      nlinarith only [hdiff]
    rw [heq]
    constructor <;> linarith only [hlo, hhi]
  have hk := Sieve.kuzminLandau_interval g g' (N : ℝ) N (-1) hδ hderiv hmono
    (fun x hx => by norm_num only [Int.cast_neg, Int.cast_one]; linarith only [(hbounds x hx).1, hδhi])
    (fun x hx => by norm_num only [Int.cast_neg, Int.cast_one]; linarith only [(hbounds x hx).2])
  have hphase (j : ℕ) :
      Complex.exp (((2 * Real.pi * g ((N : ℝ) + j) : ℝ) : ℂ) * I) =
      Complex.exp (((4 * Real.pi * (Real.sqrt p - Real.sqrt q) * Real.sqrt ((N : ℝ) + j) : ℝ) : ℂ) * I) := by
    congr 3
    dsimp only [g]
    ring
  simp_rw [hphase] at hk
  apply hk.trans
  have hid : 3 / (2 * δ) = 6 * (N : ℝ) / (q - p) := by dsimp only [δ]; field_simp; ring
  rw [hid]
  apply (le_div_iff₀ hd).mpr
  have hcancel : (6 * (N : ℝ) / (q - p) + 1) * (q - p) = 6 * N + (q - p) := by field_simp
  rw [hcancel]
  linarith only [hdN]


/-- The full degree-two stationary matrix row on the integer block [N,2N]. -/
def chiDegreeTwoRootRow (N : ℕ) (p : ℝ) : EuclideanSpace ℂ (Fin (N + 1)) :=
  WithLp.toLp 2 (fun j : Fin (N + 1) => Complex.exp
    (((4 * Real.pi * Real.sqrt p * Real.sqrt ((N : ℝ) + j) : ℝ) : ℂ) * I))

theorem norm_chiDegreeTwoRootRow_sq (N : ℕ) (p : ℝ) :
    ‖chiDegreeTwoRootRow N p‖ ^ 2 = ((N + 1 : ℕ) : ℝ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hterm (j : Fin (N + 1)) : ‖(chiDegreeTwoRootRow N p) j‖ ^ 2 = 1 := by
    rw [show (chiDegreeTwoRootRow N p) j = Complex.exp
      (((4 * Real.pi * Real.sqrt p * Real.sqrt ((N : ℝ) + j) : ℝ) : ℂ) * I) from rfl,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  simp_rw [hterm]
  simp

theorem inner_chiDegreeTwoRootRow (N : ℕ) (p q : ℝ) :
    ⟪chiDegreeTwoRootRow N p, chiDegreeTwoRootRow N q⟫_ℂ =
      ∑ j ∈ Finset.range (N + 1), Complex.exp
        (((4 * Real.pi * (Real.sqrt q - Real.sqrt p) * Real.sqrt ((N : ℝ) + j) : ℝ) : ℂ) * I) := by
  rw [PiLp.inner_apply]
  simp only [chiDegreeTwoRootRow, RCLike.inner_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => Complex.exp
    (((4 * Real.pi * (Real.sqrt q - Real.sqrt p) * Real.sqrt ((N : ℝ) + j) : ℝ) : ℂ) * I)) (N + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem norm_inner_chiDegreeTwoRootRow_le {N : ℕ} (hN : 1 ≤ N)
    {p q : ℝ} (hp : p ∈ Icc (N : ℝ) (2 * N))
    (hq : q ∈ Icc (N : ℝ) (2 * N)) (hpq : p ≠ q) :
    ‖⟪chiDegreeTwoRootRow N p, chiDegreeTwoRootRow N q⟫_ℂ‖ ≤ 7 * (N : ℝ) / |q - p| := by
  rcases lt_or_gt_of_ne hpq with h | h
  · rw [Sieve.norm_inner_symm, inner_chiDegreeTwoRootRow, abs_of_pos (sub_pos.mpr h)]
    exact norm_sum_root_phase_row_correlation_le hN hp hq h
  · rw [inner_chiDegreeTwoRootRow, abs_of_neg (sub_neg.mpr h), neg_sub]
    exact norm_sum_root_phase_row_correlation_le hN hq hp h

/-- The complete Gram row has harmonic rather than cardinality growth. -/
theorem sum_norm_inner_chiDegreeTwoRootRow_le {N : ℕ} (hN : 1 ≤ N)
    {r : ℕ} (hr : r < N + 1) :
    ∑ s ∈ Finset.range (N + 1),
      ‖⟪chiDegreeTwoRootRow N ((N : ℝ) + r), chiDegreeTwoRootRow N ((N : ℝ) + s)⟫_ℂ‖ ≤
        16 * (N : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmem (j : ℕ) (hj : j < N + 1) : (N : ℝ) + j ∈ Icc (N : ℝ) (2 * N) := by
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast (by omega : j ≤ N)
    constructor <;> linarith only [hjN, Nat.cast_nonneg (α := ℝ) j]
  let lam : ℕ → ℝ := fun j => (N : ℝ) + j
  have hgap (j : ℕ) : lam j + 1 ≤ lam (j + 1) := by dsimp only [lam]; push_cast; linarith
  have hinv := Sieve.sum_inv_abs_dist_le (by norm_num : (0 : ℝ) < 1) hgap hr
  have hH : (∑ j ∈ Finset.range (N + 1), 1 / ((j : ℝ) + 1)) ≤
      1 + Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [← Sieve.sum_Icc_one_div_eq_sum_range]
    exact Sieve.sum_Icc_one_div_le_one_add_log (N + 1)
  have hoff : ∑ s ∈ (Finset.range (N + 1)).erase r,
      ‖⟪chiDegreeTwoRootRow N (lam r), chiDegreeTwoRootRow N (lam s)⟫_ℂ‖ ≤
      (7 * N) * ∑ s ∈ (Finset.range (N + 1)).erase r, 1 / |lam s - lam r| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hsmem : s < N + 1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hs)
    have hne : lam r ≠ lam s := by
      intro heq
      have he : (s : ℝ) = r := by dsimp only [lam] at heq; linarith only [heq]
      exact (Finset.mem_erase.mp hs).1 (by exact_mod_cast he)
    have hb := norm_inner_chiDegreeTwoRootRow_le hN (hmem r hr) (hmem s hsmem) hne
    calc
      _ ≤ 7 * (N : ℝ) / |lam s - lam r| := hb
      _ = _ := by ring
  have hoff' : ∑ s ∈ (Finset.range (N + 1)).erase r,
      ‖⟪chiDegreeTwoRootRow N (lam r), chiDegreeTwoRootRow N (lam s)⟫_ℂ‖ ≤
      14 * N * (1 + Real.log ((N + 1 : ℕ) : ℝ)) := by
    apply hoff.trans
    have hi := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 7 * N)
    have hh := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 14 * N)
    norm_num only [div_one] at hi
    linarith only [hi, hh]
  have hdiag : ‖⟪chiDegreeTwoRootRow N (lam r), chiDegreeTwoRootRow N (lam r)⟫_ℂ‖ =
      ((N + 1 : ℕ) : ℝ) := by
    simp [inner_self_eq_norm_sq_to_K, norm_chiDegreeTwoRootRow_sq]
  change (∑ s ∈ Finset.range (N + 1), ‖⟪chiDegreeTwoRootRow N (lam r), chiDegreeTwoRootRow N (lam s)⟫_ℂ‖) ≤ _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hr), hdiag]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  norm_num only [Nat.cast_add, Nat.cast_one] at hoff' hlog ⊢
  nlinarith only [hoff', hN1, mul_nonneg hN0.le hlog]

/-- Signed degree-two stationary coefficients pay their quadratic energy.
This is the full integer matrix; zero coefficients permit arbitrary prime
restrictions without applying lattice cancellation to an incomplete sample set. -/
theorem norm_sum_smul_chiDegreeTwoRootRow_sq_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℂ) :
    ‖∑ p ∈ Finset.range (N + 1), c p • chiDegreeTwoRootRow N ((N : ℝ) + p)‖ ^ 2 ≤
      (16 * (N : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ))) *
        ∑ p ∈ Finset.range (N + 1), ‖c p‖ ^ 2 := by
  exact Sieve.norm_sum_smul_sq_le_of_schur (Finset.range (N + 1))
    (fun p => chiDegreeTwoRootRow N ((N : ℝ) + p))
    (fun r hr => sum_norm_inner_chiDegreeTwoRootRow_le hN (Finset.mem_range.mp hr)) c

end RHTower
