import GaloisForLFunctions.RHTower.Deninger.DeningerGammaAllPrimeStokesPairBridge
import GaloisForLFunctions.RHTower.STCOrderedCurvatureRank

/-!
# Geometry of the all-prime Gamma-to-Stokes pair calibration

The equal-depth Gamma exterior and the analytic Stokes scalar are related on every ordered prime
pair by the positive, grade-independent calibration `K_pq,e = B_p B_q (H_q - H_p)/2`.  This
module records its intrinsic pair structure:

* after removing the critical amplitudes, `K_pq,e/(B_p B_q) = (e+1) log(q/p)/4`;
* for `p<q<r<s`, `K_pq K_rs < K_pr K_qs`, so no one-prime weights `a_p a_q` reproduce it;
* the normalized calibration has infimum zero over arbitrarily large prime pairs (a PNT input);
* the raw modular exterior on any finite packet of cells has rank at most two, its
  reflection-odd part rank at most four, also after one-cell diagonal rescalings;
* consequently, at every nonzero grade, no global scalar times one-prime rescalings of the
  reflection-odd exterior at any common local grade reproduces the ordered analytic Stokes
  scalar on all prime pairs, because the latter has unbounded packet rank.
-/

open Filter Topology Matrix

namespace RHTower

noncomputable section

/-- The normalized pair calibration is a pure logarithmic height gap. -/
theorem sourcePairCalibration_div_amplitudes (p q : Nat.Primes) (e : ℕ) :
    sourcePairCalibration p q e /
        (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e)) =
      ((e : ℝ) + 1) * (Real.log (q : ℝ) - Real.log (p : ℝ)) / 4 := by
  have hp := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell p e)
  have hq := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell q e)
  unfold sourcePairCalibration xiGammaEulerBoundaryHalfHeight
  field_simp
  ring

private theorem calibration_eq (p q : Nat.Primes) (e : ℕ) :
    sourcePairCalibration p q e =
      xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e) *
        (((e : ℝ) + 1) / 4) * (Real.log (q : ℝ) - Real.log (p : ℝ)) := by
  unfold sourcePairCalibration xiGammaEulerBoundaryHalfHeight
  ring

private theorem gap_cross_strict {x y z w : ℝ} (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    (y - x) * (w - z) < (z - x) * (w - y) := by
  have hprod : 0 < (z - y) * (w - x) :=
    mul_pos (sub_pos.mpr hyz) (sub_pos.mpr (hxy.trans (hyz.trans hzw)))
  nlinarith

/-- **Strict pair inequality.** For four increasing primes at one depth,
`K_pq K_rs < K_pr K_qs`. -/
theorem sourcePairCalibration_cross_lt (p q r s : Nat.Primes) (e : ℕ)
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) (hrs : (r : ℕ) < s) :
    sourcePairCalibration p q e * sourcePairCalibration r s e <
      sourcePairCalibration p r e * sourcePairCalibration q s e := by
  rw [calibration_eq, calibration_eq, calibration_eq, calibration_eq]
  have hlog : ∀ a b : Nat.Primes, (a : ℕ) < b → Real.log (a : ℝ) < Real.log (b : ℝ) :=
    fun a b hab => Real.log_lt_log (by exact_mod_cast a.property.pos) (by exact_mod_cast hab)
  have hcross := gap_cross_strict (hlog p q hpq) (hlog q r hqr) (hlog r s hrs)
  set Bp := xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e)
  set Bq := xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e)
  set Br := xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell r e)
  set Bs := xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell s e)
  have hpos : 0 < Bp * Bq * Br * Bs * (((e : ℝ) + 1) / 4) ^ 2 := by
    have := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell p e)
    have := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell q e)
    have := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell r e)
    have := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell s e)
    positivity
  have key := mul_lt_mul_of_pos_left hcross hpos
  nlinarith [key]

/-- **The calibration is intrinsically pairwise.** No one-prime weights `a` satisfy
`K_pq,e = a_p a_q` on all increasing prime pairs. -/
theorem no_rank_one_sourcePairCalibration (e : ℕ) :
    ¬∃ a : Nat.Primes → ℝ, ∀ p q : Nat.Primes, (p : ℕ) < q →
      sourcePairCalibration p q e = a p * a q := by
  rintro ⟨a, ha⟩
  let P3 : Nat.Primes := ⟨3, Nat.prime_three⟩
  let P5 : Nat.Primes := ⟨5, by norm_num⟩
  let P7 : Nat.Primes := ⟨7, by norm_num⟩
  let P11 : Nat.Primes := ⟨11, by norm_num⟩
  have h := sourcePairCalibration_cross_lt P3 P5 P7 P11 e (by decide) (by decide) (by decide)
  rw [ha P3 P5 (by decide), ha P7 P11 (by decide), ha P3 P7 (by decide),
    ha P5 P11 (by decide)] at h
  have heq : a P3 * a P5 * (a P7 * a P11) = a P3 * a P7 * (a P5 * a P11) := by ring
  rw [heq] at h
  exact lt_irrefl _ h

/-- **Vanishing normalized calibration.** At every depth, arbitrarily large prime pairs have
normalized calibration below any `ε > 0`; it is positive on every increasing pair. -/
theorem exists_sourcePairCalibration_normalized_lt (e : ℕ) {ε : ℝ} (hε : 0 < ε) (N : ℝ) :
    ∃ p q : Nat.Primes, N < (p : ℕ) ∧ (p : ℕ) < q ∧
      0 < sourcePairCalibration p q e /
          (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e)) ∧
      sourcePairCalibration p q e /
          (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e)) < ε := by
  have he : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  obtain ⟨p, q, hp, hq, hNp, hpq, hqp⟩ :=
    exists_prime_pair_ratio_lt (ε := 4 * ε / ((e : ℝ) + 1)) (by positivity) N
  refine ⟨⟨p, hp⟩, ⟨q, hq⟩, hNp, hpq, ?_, ?_⟩
  · exact div_pos (sourcePairCalibration_pos _ _ e hpq)
      (mul_pos (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 _)
        (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 _))
  · rw [sourcePairCalibration_div_amplitudes]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlog : Real.log (q : ℝ) - Real.log p < 4 * ε / ((e : ℝ) + 1) := by
      have h1 : Real.log (q : ℝ) < Real.log ((1 + 4 * ε / ((e : ℝ) + 1)) * p) :=
        Real.log_lt_log (by exact_mod_cast hq.pos) hqp
      rw [Real.log_mul (by positivity) hp0.ne'] at h1
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 4 * ε / ((e : ℝ) + 1) by
        positivity)
      linarith
    show ((e : ℝ) + 1) * (Real.log (q : ℝ) - Real.log p) / 4 < ε
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have := mul_lt_mul_of_pos_left hlog he
    rw [mul_div_cancel₀ _ he.ne'] at this
    linarith

/-- The divided-difference factor `1/(H_q - H_p)` is unbounded over arbitrarily large pairs. -/
theorem exists_halfHeight_gap_inv_gt (e : ℕ) (M N : ℝ) :
    ∃ p q : Nat.Primes, N < (p : ℕ) ∧ (p : ℕ) < q ∧
      M < (xiGammaEulerBoundaryHalfHeight q e - xiGammaEulerBoundaryHalfHeight p e)⁻¹ := by
  obtain ⟨p, q, hNp, hpq, hpos, hlt⟩ :=
    exists_sourcePairCalibration_normalized_lt e (ε := 1 / (2 * (max M 1)))
      (by positivity) N
  refine ⟨p, q, hNp, hpq, ?_⟩
  have hK := sourcePairCalibration_div_amplitudes p q e
  have hgap : xiGammaEulerBoundaryHalfHeight q e - xiGammaEulerBoundaryHalfHeight p e =
      2 * (sourcePairCalibration p q e /
        (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e))) := by
    rw [hK]
    unfold xiGammaEulerBoundaryHalfHeight
    ring
  rw [hgap]
  have hM : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right M 1)
  have h2 : 2 * (sourcePairCalibration p q e /
      (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e))) < 1 / max M 1 := by
    have := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 2)
    rw [show 2 * (1 / (2 * max M 1)) = 1 / max M 1 by field_simp] at this
    exact this
  have hpos2 : 0 < 2 * (sourcePairCalibration p q e /
      (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e))) := by positivity
  have := one_div_lt_one_div_of_lt hpos2 h2
  rw [one_div_one_div, one_div] at this
  exact lt_of_le_of_lt (le_max_left M 1) this

/-! ### Packet ranks of the literal exterior -/

/-- The modular exterior on a finite packet of prime/depth cells. -/
def modularExteriorPacket {n : ℕ} (c : Fin n → Nat.Primes × ℕ) (a : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => xiGammaEulerPrimitiveModularExterior a (c i) (c j)

/-- The reflection-odd exterior on a finite packet of prime/depth cells. -/
def reflectionOddExteriorPacket {n : ℕ} (c : Fin n → Nat.Primes × ℕ) (a : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => xiGammaEulerPrimitiveReflectionOddExterior a (c i) (c j)

/-- **Wedge of two sections.** The raw modular exterior has packet rank at most two. -/
theorem rank_modularExteriorPacket_le {n : ℕ} (c : Fin n → Nat.Primes × ℕ) (a : ℝ) :
    (modularExteriorPacket c a).rank ≤ 2 := by
  let m : Fin n → ℝ := fun i => xiGammaEulerPrimitiveModularCurrent a (c i)
  let H : Fin n → ℝ := fun i => xiGammaEulerBoundaryHalfHeight (c i).1 (c i).2
  let U : Matrix (Fin n) (Fin 2) ℝ := Matrix.of fun i t => ![m i * H i, m i] t
  let V : Matrix (Fin 2) (Fin n) ℝ := Matrix.of fun t j => ![m j, -(m j * H j)] t
  have hfac : modularExteriorPacket c a = U * V := by
    ext i j
    simp only [modularExteriorPacket, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two, U, V,
      Matrix.cons_val_zero, Matrix.cons_val_one, xiGammaEulerPrimitiveModularExterior, m, H]
    simp
    ring
  rw [hfac]
  calc (U * V).rank ≤ U.rank := Matrix.rank_mul_le_left U V
    _ ≤ Fintype.card (Fin 2) := Matrix.rank_le_card_width U
    _ = 2 := Fintype.card_fin 2

/-- The reflection-odd exterior, a difference of two wedges, has packet rank at most four. -/
theorem rank_reflectionOddExteriorPacket_le {n : ℕ} (c : Fin n → Nat.Primes × ℕ) (a : ℝ) :
    (reflectionOddExteriorPacket c a).rank ≤ 4 := by
  let m : Fin n → ℝ := fun i => xiGammaEulerPrimitiveModularCurrent a (c i)
  let m' : Fin n → ℝ := fun i => xiGammaEulerPrimitiveModularCurrent (-a) (c i)
  let H : Fin n → ℝ := fun i => xiGammaEulerBoundaryHalfHeight (c i).1 (c i).2
  let U : Matrix (Fin n) (Fin 4) ℝ := Matrix.of fun i t =>
    ![m i * H i, m i, m' i * H i, m' i] t
  let V : Matrix (Fin 4) (Fin n) ℝ := Matrix.of fun t j =>
    ![m j / 2, -(m j * H j) / 2, -(m' j) / 2, m' j * H j / 2] t
  have hfac : reflectionOddExteriorPacket c a = U * V := by
    ext i j
    simp only [reflectionOddExteriorPacket, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four,
      U, V, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      xiGammaEulerPrimitiveReflectionOddExterior, xiGammaEulerPrimitiveModularExterior, m, m', H]
    simp
    ring
  rw [hfac]
  calc (U * V).rank ≤ U.rank := Matrix.rank_mul_le_left U V
    _ ≤ Fintype.card (Fin 4) := Matrix.rank_le_card_width U
    _ = 4 := Fintype.card_fin 4

/-- One-cell diagonal rescaling (and a global scalar) preserve the rank bound four. -/
theorem rank_rescaled_reflectionOddExteriorPacket_le {n : ℕ} (c : Fin n → Nat.Primes × ℕ)
    (a lam : ℝ) (d d' : Fin n → ℝ) :
    (lam • (diagonal d * reflectionOddExteriorPacket c a * diagonal d')).rank ≤ 4 := by
  calc (lam • (diagonal d * reflectionOddExteriorPacket c a * diagonal d')).rank
      ≤ (diagonal d * reflectionOddExteriorPacket c a * diagonal d').rank := by
        rw [Matrix.smul_eq_diagonal_mul]
        exact Matrix.rank_mul_le_right _ _
    _ ≤ (diagonal d * reflectionOddExteriorPacket c a).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (reflectionOddExteriorPacket c a).rank := Matrix.rank_mul_le_right _ _
    _ ≤ 4 := rank_reflectionOddExteriorPacket_le c a

/-- **No scalar-times-rescaling identification.** At every nonzero grade `g` and depth `e`,
no global scalar `λ`, common local grade `α` and one-prime weights `d` satisfy
`c_pq(g) = λ d_p d_q S_α((p,e),(q,e))` on all increasing prime pairs. -/
theorem no_scalar_rescaled_reflectionOdd_stokes_identification {g : ℝ} (hg : g ≠ 0) (e : ℕ) :
    ¬∃ (lam α : ℝ) (d : ℕ → ℝ), ∀ p q : Nat.Primes, (p : ℕ) < q →
      routeRCrossPrimeStokesOddCurvature p q g =
        lam * d p * d q * xiGammaEulerPrimitiveReflectionOddExterior α (p, e) (q, e) := by
  rintro ⟨lam, α, d, hid⟩
  obtain ⟨p, hmono, hprime, -, hrank⟩ :=
    exists_prime_packet_orderedStokesMatrix_rank hg (n := 6) ⟨3, rfl⟩ 0
  let c : Fin 6 → Nat.Primes × ℕ := fun i => (⟨p i, hprime i⟩, e)
  let D : Fin 6 → ℝ := fun i => d (p i)
  have hdiag : ∀ i, xiGammaEulerPrimitiveReflectionOddExterior α (c i) (c i) = 0 := by
    intro i
    have := xiGammaEulerPrimitiveReflectionOddExterior_swap α (c i) (c i)
    linarith
  have hfac : orderedStokesMatrix p g =
      lam • (diagonal D * reflectionOddExteriorPacket c α * diagonal D) := by
    ext i j
    simp only [orderedStokesMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_mul, Matrix.mul_diagonal, reflectionOddExteriorPacket, D]
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [if_pos hij, hid ⟨p i, hprime i⟩ ⟨p j, hprime j⟩ (hmono hij)]
      ring
    · subst hij
      simp [hdiag]
    · rw [if_neg (not_lt.mpr hij.le), if_pos hij, hid ⟨p j, hprime j⟩ ⟨p i, hprime i⟩
        (hmono hij), xiGammaEulerPrimitiveReflectionOddExterior_swap α (c j) (c i)]
      simp only [c]
      ring
  have hle := rank_rescaled_reflectionOddExteriorPacket_le c α lam D D
  rw [← hfac, hrank] at hle
  omega

end

end RHTower
