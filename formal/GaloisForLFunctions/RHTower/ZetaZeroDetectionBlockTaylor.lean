import GaloisForLFunctions.RHTower.ZetaZeroDetectionThirdOrder
import GaloisForLFunctions.RHTower.Sieve.DirichletAbscissaTaylorSelection

/-!
# From a detected zero to a dyadic block at a fixed abscissa

The detection polynomial `D_N M_y - 1 = Σ_{k ∈ P} e_k k^{-s}` has support in `[1, Ny]`.  Split the
support into the dyadic blocks `B_j = {k : ⌊log₂ k⌋ = j}`, `j < J = ⌊log₂(Ny)⌋ + 1`.  A value of
modulus `1/2` at `s = σ₀ + δ + iγ` gives a block of modulus at least `1/(2J)`.  With
`Λ = log(Ny)` and `δΛ ≤ 1`, the Taylor transfer
(`RHTower.Sieve.exists_abscissaTaylorPoly_large`) of order `J + 8` then gives a companion polynomial
of that block, weighted by `(log k/Λ)^i`, with modulus at least `1/(12J)` on the line `σ₀`.

The Taylor tail is controlled by the crude bounds `|e_k| ≤ Ny + 1` and `#P ≤ Ny < 2^J`, together with
`7!·8^{J+1} ≤ (J+8)!`.
-/

namespace RHTower

noncomputable section

open Complex Finset RHTower.Sieve

/-- The support of the detection polynomial. -/
def detSupport (N y : ℕ) : Finset ℕ := prodSupport (Finset.Icc 1 N) (Finset.Icc 1 y)

/-- The `j`-th dyadic block of the detection support. -/
def detDyadicBlock (N y j : ℕ) : Finset ℕ :=
  (detSupport N y).filter (fun k => Nat.log 2 k = j)

/-- The detection coefficients, as complex numbers. -/
def detCoeffC (N y : ℕ) (k : ℕ) : ℂ := ((detCoeff N y k : ℝ) : ℂ)

/-- The number of dyadic blocks. -/
def detBlockCount (N y : ℕ) : ℕ := Nat.log 2 (N * y) + 1

theorem mem_detSupport_le {N y k : ℕ} (hk : k ∈ detSupport N y) : 1 ≤ k ∧ k ≤ N * y := by
  unfold detSupport prodSupport at hk
  rw [Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    Nat.mul_le_mul hp.1.2 hp.2.2⟩

theorem card_detSupport_le (N y : ℕ) : (detSupport N y).card ≤ N * y := by
  unfold detSupport prodSupport
  refine le_trans Finset.card_image_le ?_
  simp

theorem mem_detDyadicBlock_bounds {N y j k : ℕ} (hk : k ∈ detDyadicBlock N y j) :
    2 ^ j ≤ k ∧ k < 2 ^ (j + 1) := by
  unfold detDyadicBlock at hk
  rw [Finset.mem_filter] at hk
  have hk1 := (mem_detSupport_le hk.1).1
  rw [← hk.2]
  exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) k⟩

theorem abs_detCoeff_le (N y k : ℕ) : |detCoeff N y k| ≤ N * y + 1 := by
  unfold detCoeff dpolyConv
  have hsum : |∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 y)).filter (fun p => p.1 * p.2 = k),
      (1 : ℝ) * moebiusCoeff p.2| ≤ N * y := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 y)).filter (fun p => p.1 * p.2 = k),
          |(1 : ℝ) * moebiusCoeff p.2|
        ≤ ∑ _p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 y)).filter (fun p => p.1 * p.2 = k),
          (1 : ℝ) := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [one_mul]
          exact abs_moebiusCoeff_le_one _
      _ = (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 y)).filter (fun p => p.1 * p.2 = k)).card := by
          simp
      _ ≤ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 y)).card := by
          exact_mod_cast Finset.card_filter_le _ _
      _ = N * y := by simp
  have hind : |(if k = 1 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  calc |_ - (if k = 1 then (1 : ℝ) else 0)|
      ≤ |∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 y)).filter (fun p => p.1 * p.2 = k),
          (1 : ℝ) * moebiusCoeff p.2| + |(if k = 1 then (1 : ℝ) else 0)| := abs_sub _ _
    _ ≤ N * y + 1 := add_le_add hsum hind

/-- The detection polynomial is the sum of its dyadic blocks. -/
theorem detPolyC_eq_sum_blocks (N y : ℕ) (σ γ : ℝ) :
    detPolyC N y ((σ : ℂ) + (γ : ℂ) * I)
      = ∑ j ∈ range (detBlockCount N y),
          abscissaDirichletValue (detDyadicBlock N y j) (detCoeffC N y) σ γ := by
  unfold detPolyC abscissaDirichletValue detDyadicBlock
  rw [dpolyC_apply]
  change ∑ n ∈ detSupport N y, ((detCoeff N y n : ℝ) : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + (γ : ℂ) * I)) = _
  have hmaps : ∀ k ∈ detSupport N y, Nat.log 2 k ∈ range (detBlockCount N y) := by
    intro k hk
    rw [mem_range, detBlockCount, Nat.lt_succ_iff]
    exact Nat.log_mono_right (mem_detSupport_le hk).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rfl

/-- Pigeonhole over a finite sum: some summand carries a `1/J` share of the modulus. -/
theorem exists_range_norm_ge_div {J : ℕ} (hJ : 1 ≤ J) (f : ℕ → ℂ) {V : ℝ}
    (hV : V ≤ ‖∑ j ∈ range J, f j‖) : ∃ j < J, V / J ≤ ‖f j‖ := by
  by_contra hcon
  push Not at hcon
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hlt : ∑ j ∈ range J, ‖f j‖ < ∑ _j ∈ range J, V / J :=
    Finset.sum_lt_sum_of_nonempty (by simp; omega) fun j hj => hcon j (mem_range.mp hj)
  have hsum : ∑ _j ∈ range J, V / J = V := by
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    field_simp
  linarith [norm_sum_le (range J) f]

/-- The crude block mass: `Σ_{k ∈ B_j} |e_k| k^{-σ₀} ≤ 2·4^J` for `σ₀ ≥ 0`. -/
theorem sum_norm_detCoeffC_block_le {N y j : ℕ} {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) :
    ∑ k ∈ detDyadicBlock N y j, ‖detCoeffC N y k‖ * (k : ℝ) ^ (-σ₀)
      ≤ 2 * 4 ^ (detBlockCount N y) := by
  have hNy : N * y < 2 ^ (detBlockCount N y) := by
    unfold detBlockCount
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hNyR : ((N * y : ℕ) : ℝ) < 2 ^ (detBlockCount N y) := by exact_mod_cast hNy
  have hterm : ∀ k ∈ detDyadicBlock N y j,
      ‖detCoeffC N y k‖ * (k : ℝ) ^ (-σ₀) ≤ (N * y : ℕ) + 1 := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_detSupport_le (Finset.mem_filter.mp hk).1).1
    have hpow : (k : ℝ) ^ (-σ₀) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk1) (by linarith)
    rw [detCoeffC, Complex.norm_real, Real.norm_eq_abs]
    have hb := abs_detCoeff_le N y k
    push_cast
    calc |detCoeff N y k| * (k : ℝ) ^ (-σ₀) ≤ ((N : ℝ) * y + 1) * 1 :=
          mul_le_mul hb hpow (Real.rpow_nonneg (Nat.cast_nonneg k) _) (by positivity)
      _ = (N : ℝ) * y + 1 := mul_one _
  have hcard : ((detDyadicBlock N y j).card : ℝ) ≤ (N * y : ℕ) := by
    have h := le_trans (Finset.card_filter_le (detSupport N y) (fun k => Nat.log 2 k = j))
      (card_detSupport_le N y)
    exact_mod_cast h
  calc ∑ k ∈ detDyadicBlock N y j, ‖detCoeffC N y k‖ * (k : ℝ) ^ (-σ₀)
      ≤ ∑ _k ∈ detDyadicBlock N y j, (((N * y : ℕ) : ℝ) + 1) := Finset.sum_le_sum hterm
    _ = (detDyadicBlock N y j).card * (((N * y : ℕ) : ℝ) + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N * y : ℕ) : ℝ) * (((N * y : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 2 ^ (detBlockCount N y) * (2 * 2 ^ (detBlockCount N y)) := by
        have h1 : ((N * y : ℕ) : ℝ) + 1 ≤ 2 * 2 ^ (detBlockCount N y) := by
          have : (1 : ℝ) ≤ 2 ^ (detBlockCount N y) := one_le_pow₀ (by norm_num)
          linarith
        exact mul_le_mul hNyR.le h1 (by positivity) (by positivity)
    _ = 2 * 4 ^ (detBlockCount N y) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        ring_nf

/-- `2·(2·4^J) / (J+8)! ≤ 1/(4J)` for every `J ≥ 1`. -/
theorem taylor_tail_factorial_bound {J : ℕ} (hJ : 1 ≤ J) :
    2 / ((J + 8).factorial : ℝ) * (2 * 4 ^ J) ≤ 1 / (2 * J) / 2 := by
  have hfac : (7 : ℕ).factorial * (7 + 1) ^ (J + 1) ≤ (7 + (J + 1)).factorial :=
    Nat.factorial_mul_pow_le_factorial
  have hfacR : (5040 : ℝ) * 8 ^ (J + 1) ≤ ((J + 8).factorial : ℝ) := by
    have h := hfac
    rw [show 7 + (J + 1) = J + 8 by ring] at h
    have h' : ((7 : ℕ).factorial * (7 + 1) ^ (J + 1) : ℕ) ≤ ((J + 8).factorial : ℕ) := h
    have hcast : (((7 : ℕ).factorial * (7 + 1) ^ (J + 1) : ℕ) : ℝ) = 5040 * 8 ^ (J + 1) := by
      push_cast
      norm_num [Nat.factorial]
    rw [← hcast]
    exact_mod_cast h'
  have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ2 : (J : ℝ) ≤ 2 ^ J := by
    have := Nat.lt_pow_self (n := J) (a := 2) (by norm_num)
    exact_mod_cast this.le
  have hpos : (0 : ℝ) < ((J + 8).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have h8 : (8 : ℝ) ^ (J + 1) = 8 * (2 ^ J * 4 ^ J) := by
    rw [pow_succ, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
    ring
  have h4 : (0 : ℝ) < 4 ^ J := by positivity
  have key : (2 : ℝ) * (2 * 4 ^ J) * (4 * J) ≤ 5040 * 8 ^ (J + 1) := by
    rw [h8]
    nlinarith
  have hJ0 : (0 : ℝ) < J := by linarith
  calc (2 : ℝ) * (2 * 4 ^ J) = ((2 : ℝ) * (2 * 4 ^ J) * (4 * J)) / (4 * J) := by field_simp
    _ ≤ ((5040 : ℝ) * 8 ^ (J + 1)) / (4 * J) := by gcongr
    _ ≤ ((J + 8).factorial : ℝ) / (4 * J) := by gcongr
    _ = 1 / (2 * J) / 2 * ((J + 8).factorial : ℝ) := by field_simp; ring

/-- **From a detected zero to a dyadic block on a fixed line.**  If
`1/2 ≤ |D_N M_y - 1|` at `σ₀ + δ + iγ` with `σ₀ ≥ 0`, `δ ≥ 0` and `δ log(Ny) ≤ 1`, then some dyadic
block `j < J` and some Taylor order `i < J + 8` give a companion polynomial of modulus at least
`1/(12J)` at `σ₀ + iγ`, where `J = ⌊log₂(Ny)⌋ + 1`. -/
theorem exists_detBlock_taylor_large {N y : ℕ} (hNy : 2 ≤ N * y) {σ₀ δ γ : ℝ}
    (hσ₀ : 0 ≤ σ₀) (hδ0 : 0 ≤ δ) (hδΛ : δ * Real.log (N * y : ℕ) ≤ 1)
    (hdet : 1 / 2 ≤ ‖detPolyC N y (((σ₀ + δ : ℝ) : ℂ) + (γ : ℂ) * I)‖) :
    ∃ j < detBlockCount N y, ∃ i < detBlockCount N y + 8,
      1 / (12 * detBlockCount N y) ≤
        ‖abscissaTaylorPoly (detDyadicBlock N y j) (detCoeffC N y)
          (Real.log (N * y : ℕ)) i σ₀ γ‖ := by
  set J := detBlockCount N y with hJdef
  have hJ : 1 ≤ J := by rw [hJdef, detBlockCount]; omega
  rw [detPolyC_eq_sum_blocks] at hdet
  obtain ⟨j, hj, hblock⟩ := exists_range_norm_ge_div hJ _ hdet
  have hΛ0 : 0 < Real.log (N * y : ℕ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N * y))
  have hS : ∀ k ∈ detDyadicBlock N y j, 1 ≤ k := fun k hk =>
    (mem_detSupport_le (Finset.mem_filter.mp hk).1).1
  have hΛ : ∀ k ∈ detDyadicBlock N y j, Real.log k ≤ Real.log (N * y : ℕ) := by
    intro k hk
    have hk := mem_detSupport_le (Finset.mem_filter.mp hk).1
    exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk.2)
  have htail : 2 / ((J + 8).factorial : ℝ) *
      ∑ k ∈ detDyadicBlock N y j, ‖detCoeffC N y k‖ * (k : ℝ) ^ (-σ₀) ≤ 1 / 2 / J / 2 := by
    have h1 := sum_norm_detCoeffC_block_le (N := N) (y := y) (j := j) hσ₀
    have h2 := taylor_tail_factorial_bound hJ
    have hpos : (0 : ℝ) ≤ 2 / ((J + 8).factorial : ℝ) := by positivity
    calc _ ≤ 2 / ((J + 8).factorial : ℝ) * (2 * 4 ^ J) := mul_le_mul_of_nonneg_left h1 hpos
      _ ≤ 1 / (2 * J) / 2 := h2
      _ = 1 / 2 / J / 2 := by ring
  obtain ⟨i, hi, hlarge⟩ := exists_abscissaTaylorPoly_large hS (detCoeffC N y) hδ0 hΛ0 hΛ hδΛ
    (by omega : 1 ≤ J + 8) hblock htail
  refine ⟨j, hj, i, hi, le_trans (le_of_eq ?_) hlarge⟩
  field_simp
  ring

end

end RHTower
