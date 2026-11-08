import GaloisForLFunctions.SurfaceOfSpecZ.TheTorsionEnergyAgainstTheJets
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant

/-!
# The archimedean Frobenius has infinite rank; its compensation changes sign at the plastic ratio

**Cauchy blocks.** For orders `m < n` the archimedean Frobenius kernel is
`archKernel m n = m n²/(n² − m²)`, a Cauchy kernel in `(m², n²)` up to diagonal scalings. Hence every
square block on rows `m_1, …, m_r` and columns `n_1, …, n_r` with every `m_i` below every `n_j` is
nonsingular (`det_archBlock_ne_zero_of_lt`): its determinant is
`Π m_i · Π n_j² · Π_{i<j}(m_j² − m_i²)(n_i² − n_j²) / Π_{i,j}(n_j² − m_i²)` up to sign.

**Infinite rank on coprime orders.** Taking rows and columns among distinct primes, the archimedean
Frobenius restricted to pairwise coprime orders agrees with no kernel `Σ_{k<r} u_k(m) v_k(n)` of finite
rank (`not_finiteRank_on_coprime`). The jets of the trivial zeros therefore need an
infinite-dimensional archimedean fibre: no metric on a line bundle over a variety of finite dimension,
no finite collection of channels, and no finite-genus fibre carries them. This extends the rank-two
exclusion of metrics on `ℙ¹_ℤ` to every finite rank.

**The plastic ratio.** For `m < n` the archimedean compensation (pole plane minus cusp and jets) is

  `√(mn)·C_∞(m, n) = (n³ − n m² − m³)/(n² − m²)`   (`sqrt_mul_archCompensation_eq_cubic`),

so `C_∞(m, n) < 0` iff `n³ < n m² + m³`, i.e. iff `n/m` is below the plastic number `ρ` (`ρ³ = ρ + 1`),
and `C_∞(m, n) > 0` iff `n/m > ρ` (`archCompensation_neg_iff`, `archCompensation_pos_iff`). Since `ρ` is
irrational, `C_∞` never vanishes off the diagonal (`archCompensation_ne_zero`). The hyperbolic distance
`log ρ` at which the compensation changes sign is the aperture at which Weil's archimedean Lévy weight
turns negative.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

/-- For `m < n` the archimedean Frobenius kernel is the Cauchy entry `m n²/(n² − m²)`. -/
theorem archKernel_of_lt {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    archKernel m n = (m : ℝ) * n ^ 2 * ((n : ℝ) ^ 2 - m ^ 2)⁻¹ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hn' : (0 : ℝ) < n := hm'.trans hmn'
  have hd : (n : ℝ) ^ 2 - m ^ 2 ≠ 0 := by nlinarith
  rw [archKernel, min_eq_left hmn'.le, max_eq_right hmn'.le]
  field_simp

/-- **Every ordered square block of the archimedean Frobenius is nonsingular.** -/
theorem det_archBlock_ne_zero_of_lt {r : ℕ} {m n : Fin r → ℕ} (hm : ∀ i, 0 < m i)
    (hmi : Function.Injective m) (hni : Function.Injective n) (hlt : ∀ i j, m i < n j) :
    (Matrix.of fun i j => archKernel (m i) (n j)).det ≠ 0 := by
  set x : Fin r → ℝ := fun i => -((m i : ℝ) ^ 2)
  set y : Fin r → ℝ := fun j => (n j : ℝ) ^ 2
  have hpos : ∀ i j, 0 < x i + y j := by
    intro i j
    have h1 : (m i : ℝ) < n j := by exact_mod_cast hlt i j
    have h0 : (0 : ℝ) < m i := by exact_mod_cast hm i
    simp only [x, y]; nlinarith
  have hfac : (Matrix.of fun i j => archKernel (m i) (n j)) =
      Matrix.diagonal (fun i => (m i : ℝ)) * HTGeometry.cauchyMatrix x y *
        Matrix.diagonal (fun j => (n j : ℝ) ^ 2) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply,
      archKernel_of_lt (hm i) (hlt i j), HTGeometry.cauchyMatrix_apply]
    simp only [x, y]
    ring
  have hcd := HTGeometry.det_cauchyMatrix x y fun i j => (hpos i j).ne'
  have hprod : ∏ i, ∏ j ∈ Finset.Ioi i, ((x i - x j) * (y i - y j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
    refine mul_ne_zero ?_ ?_
    · simp only [x]
      intro h
      have : (m i : ℝ) ^ 2 = (m j : ℝ) ^ 2 := by linarith
      have h' : (m i : ℝ) = m j := by
        have := (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp this; exact this
      exact hij (hmi (by exact_mod_cast h'))
    · simp only [y]
      intro h
      have : (n i : ℝ) ^ 2 = (n j : ℝ) ^ 2 := by linarith
      have h' : (n i : ℝ) = n j := (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp this
      exact hij (hni (by exact_mod_cast h'))
  have hc : (HTGeometry.cauchyMatrix x y).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcd
    exact hprod hcd.symm
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  refine mul_ne_zero (mul_ne_zero ?_ hc) ?_
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (hm i).ne'
  · refine Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero 2 ?_
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (hlt j j)).ne'

/-- **No finite-rank kernel carries the jets on coprime orders.** For every `r`, no kernel
`Σ_{k<r'} u_k(m)v_k(n)` with `r' < r` agrees with the archimedean Frobenius on all pairs of distinct
primes. -/
theorem not_finiteRank_on_coprime {r' : ℕ} (u v : Fin r' → ℕ → ℝ) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → archKernel p q = ∑ k, u k p * v k q := by
  intro h
  set r := r' + 1
  set P : ℕ → ℕ := Nat.nth Nat.Prime
  have hPmono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hPprime : ∀ k, (P k).Prime := fun k => Nat.prime_nth_prime k
  set m : Fin r → ℕ := fun i => P i
  set n : Fin r → ℕ := fun j => P (r + j)
  have hlt : ∀ i j, m i < n j := fun i j => hPmono (by have := i.isLt; omega)
  have hdet := det_archBlock_ne_zero_of_lt (fun i => (hPprime _).pos)
    (fun i j hij => Fin.ext (hPmono.injective hij)) (fun i j hij => by
      have := hPmono.injective hij; exact Fin.ext (by omega)) hlt
  have hfac : (Matrix.of fun i j => archKernel (m i) (n j)) =
      (Matrix.of fun (i : Fin r) (k : Fin r') => u k (m i)) *
        (Matrix.of fun (k : Fin r') (j : Fin r) => v k (n j)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, h _ _ (hPprime _) (hPprime _) (hlt i j).ne]
    simp
  have hrank : (Matrix.of fun i j => archKernel (m i) (n j)).rank = r :=
    by rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)),
      Fintype.card_fin]
  have hle : (Matrix.of fun i j => archKernel (m i) (n j)).rank ≤ r' := by
    rw [hfac]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_width _).trans (by simp))
  omega

/-! ## The sign of the archimedean compensation -/

/-- **The compensation is the plastic cubic over the hyperbolic difference.** For `m < n`,
`√(mn)·C_∞(m, n) = (n³ − n m² − m³)/(n² − m²)`. -/
theorem sqrt_mul_archCompensation_eq_cubic {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    Real.sqrt ((m : ℝ) * n) * archCompensation m n =
      ((n : ℝ) ^ 3 - n * m ^ 2 - m ^ 3) / ((n : ℝ) ^ 2 - m ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hd : (n : ℝ) ^ 2 - m ^ 2 ≠ 0 := by nlinarith
  rw [sqrt_mul_archCompensation hm (hm.trans hmn), min_eq_left hmn'.le, max_eq_right hmn'.le]
  have hn : (n : ℝ) ≠ 0 := (hm'.trans hmn').ne'
  field_simp
  ring

theorem archCompensation_sign_eq {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    0 < archCompensation m n ↔ (m : ℝ) ^ 3 + n * m ^ 2 < n ^ 3 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hsq : 0 < Real.sqrt ((m : ℝ) * n) := Real.sqrt_pos.mpr (by positivity)
  have hd : 0 < (n : ℝ) ^ 2 - m ^ 2 := by nlinarith
  have h := sqrt_mul_archCompensation_eq_cubic hm hmn
  constructor
  · intro hC
    have : 0 < ((n : ℝ) ^ 3 - n * m ^ 2 - m ^ 3) / ((n : ℝ) ^ 2 - m ^ 2) := by
      rw [← h]; exact mul_pos hsq hC
    have := (div_pos_iff_of_pos_right hd).mp this
    linarith
  · intro hc
    have : 0 < ((n : ℝ) ^ 3 - n * m ^ 2 - m ^ 3) / ((n : ℝ) ^ 2 - m ^ 2) :=
      div_pos (by linarith) hd
    rw [← h] at this
    exact pos_of_mul_pos_right this hsq.le

/-- The plastic cubic `x³ − x − 1` has no rational root; for integers, `n³ ≠ n m² + m³` when `0 < m`. -/
theorem cube_ne_plastic {m n : ℕ} (hm : 0 < m) : (n : ℤ) ^ 3 ≠ n * m ^ 2 + m ^ 3 := by
  intro h
  -- Divide by `g = gcd(m, n)`: with `m = g a`, `n = g b` and `a, b` coprime, `b³ = b a² + a³`.
  obtain ⟨g, a, b, hg, hab, rfl, rfl⟩ : ∃ g a b : ℕ, 0 < g ∧ Nat.Coprime a b ∧ m = g * a ∧ n = g * b := by
    refine ⟨Nat.gcd m n, m / Nat.gcd m n, n / Nat.gcd m n, Nat.gcd_pos_of_pos_left _ hm,
      Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ hm), ?_, ?_⟩
    · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)).symm
    · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)).symm
  have hg' : (g : ℤ) ^ 3 ≠ 0 := pow_ne_zero 3 (by exact_mod_cast hg.ne')
  have h' : (b : ℤ) ^ 3 = b * a ^ 2 + a ^ 3 := by
    have : (g : ℤ) ^ 3 * (b ^ 3) = (g : ℤ) ^ 3 * (b * a ^ 2 + a ^ 3) := by
      push_cast at h; linear_combination h
    exact mul_left_cancel₀ hg' this
  -- `a ∣ b³` and `b ∣ a³` with `a, b` coprime force `a = b = 1`, and `1 ≠ 2`.
  have ha : (a : ℤ) ∣ (b : ℤ) ^ 3 := ⟨b * a + a ^ 2, by rw [h']; ring⟩
  have hb : (b : ℤ) ∣ (a : ℤ) ^ 3 := ⟨b ^ 2 - a ^ 2, by linear_combination (-1 : ℤ) * h'⟩
  have ha1 : a = 1 := by
    have : a ∣ b ^ 3 := by exact_mod_cast ha
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3 hab) this
  have hb1 : b = 1 := by
    have : b ∣ a ^ 3 := by exact_mod_cast hb
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3 hab.symm) this
  subst ha1; subst hb1
  norm_num at h'

/-- **The compensation never vanishes off the diagonal.** -/
theorem archCompensation_ne_zero {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    archCompensation m n ≠ 0 := by
  intro h0
  have h := sqrt_mul_archCompensation_eq_cubic hm hmn
  rw [h0, mul_zero] at h
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : (n : ℝ) ^ 2 - m ^ 2 ≠ 0 := by nlinarith
  have hnum : (n : ℝ) ^ 3 - n * m ^ 2 - m ^ 3 = 0 := by
    rcases div_eq_zero_iff.mp h.symm with h1 | h1
    · exact h1
    · exact absurd h1 hd
  have : (n : ℤ) ^ 3 = n * m ^ 2 + m ^ 3 := by
    have : (n : ℝ) ^ 3 = n * m ^ 2 + m ^ 3 := by linarith
    exact_mod_cast this
  exact cube_ne_plastic hm this

/-- **Below the plastic ratio the compensation is negative.** For `m < n`, `C_∞(m, n) < 0` iff
`n³ < n m² + m³`. -/
theorem archCompensation_neg_iff {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    archCompensation m n < 0 ↔ (n : ℝ) ^ 3 < n * m ^ 2 + m ^ 3 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hc | hc
    · have := (archCompensation_sign_eq hm hmn).mpr (by linarith)
      linarith
    · have : (n : ℤ) ^ 3 = n * m ^ 2 + m ^ 3 := by exact_mod_cast hc.symm
      exact cube_ne_plastic hm this
  · intro h
    rcases lt_or_gt_of_ne (archCompensation_ne_zero hm hmn) with h1 | h1
    · exact h1
    · have := (archCompensation_sign_eq hm hmn).mp h1
      linarith

/-- **Above the plastic ratio the compensation is positive.** -/
theorem archCompensation_pos_iff {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    0 < archCompensation m n ↔ n * (m : ℝ) ^ 2 + m ^ 3 < n ^ 3 := by
  rw [archCompensation_sign_eq hm hmn, add_comm]

end GaloisForLFunctions.SurfaceOfSpecZ
