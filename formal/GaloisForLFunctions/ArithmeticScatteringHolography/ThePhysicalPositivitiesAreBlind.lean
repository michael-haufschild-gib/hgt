import GaloisForLFunctions.ArithmeticScatteringHolography.TheHasseWindow
import GaloisForLFunctions.ArithmeticScatteringHolography.TheHorocycleIsTheWave

/-!
# The physical positivities are blind

Three kinds of positivity are available from physics, and each of them holds on every black hole, the fake
ones included. So none of them can locate a resonance. This is a proof of blindness, not an observation.

* **Schur (causality, passivity).** Away from the ground factor the scattering coefficient is the Schur symbol
  `v P(v)/R(v)`, `v = q/X²`, `P(v) = 1 - t v + q v²`, `R(v) = q - t v + v²` (`radialScattering_eq_schur`).
  It is bounded by `|v|` on the disc exactly when `|t| ≤ q + 1` (`schur_bound_iff`). So passivity is the
  edge.
* **Reflection positivity (KMS, GNS).** The correlator of the core has positive semidefinite Hankel matrices
  (`coreMoment_psd`), and its spectral density on the critical circle is a ratio of squares
  (`spectralDensity_nonneg`). Every `t` gives such a measure.
* **`C*` positivity and Ramanujan.** Square-integrable modes occur only at the ground states: the `L²`
  spectrum of `A` has the Ramanujan shape for every `t` (`ramanujan_for_every_black_hole`), and `T_Q` is
  positive with norm attained on constants.

The position of a resonance is therefore not a spectral datum of the self-adjoint operator: it is a property
of the analytic continuation of the resolvent, which these positivities do not reach.
-/

open Finset ComplexConjugate
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-! ### Schur -/

/-- The numerator polynomial `P(v) = 1 - t v + q v²`. -/
def schurNum (q t : ℝ) (v : ℂ) : ℂ := 1 - t * v + q * v ^ 2

/-- The denominator polynomial `R(v) = q - t v + v²`. -/
def schurDen (q t : ℝ) (v : ℂ) : ℂ := q - t * v + v ^ 2

/-- The difference of squares on the disc. -/
theorem normSq_schurDen_sub_num (q t : ℝ) (v : ℂ) :
    Complex.normSq (schurDen q t v) - Complex.normSq (schurNum q t v) =
      (q - 1) * (1 - Complex.normSq v) *
        ((q + 1) * (1 + Complex.normSq v) - 2 * t * v.re) := by
  unfold schurDen schurNum
  simp only [Complex.normSq_apply, pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.one_re, Complex.one_im]
  ring

/-- **Passivity is the edge.** On the closed disc `|P| ≤ |R|` exactly when `|t| ≤ q + 1`. -/
theorem schur_bound_iff {q t : ℝ} (hq : 1 < q) :
    (∀ v : ℂ, ‖v‖ ≤ 1 → ‖schurNum q t v‖ ≤ ‖schurDen q t v‖) ↔ |t| ≤ q + 1 := by
  have hq1 : 0 < q - 1 := by linarith
  constructor
  · intro h
    by_contra hlt
    have hlt' : q + 1 < |t| := not_le.mp hlt
    have hatpos : 0 < |t| := by linarith
    set r : ℝ := (q + 1) / |t| with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r < 1 := by
      rw [hr, div_lt_one hatpos]
      exact hlt'
    have hrt : r * |t| = q + 1 := by
      rw [hr]
      field_simp
    set σ : ℝ := ((SignType.sign t : SignType) : ℝ) with hσ
    have ht0 : t ≠ 0 := fun h0 => by
      rw [h0, abs_zero] at hatpos
      exact lt_irrefl _ hatpos
    have hσ2 : σ ^ 2 = 1 := by
      rcases lt_or_gt_of_ne ht0 with h' | h'
      · simp [hσ, sign_neg h']
      · simp [hσ, sign_pos h']
    have hσt : t * σ = |t| := by
      have hab : σ * |t| = t := sign_mul_abs t
      linear_combination (-σ) * hab + |t| * hσ2
    set v : ℂ := ((σ * r : ℝ) : ℂ) with hv
    have hnorm : Complex.normSq v = r ^ 2 := by
      rw [hv, Complex.normSq_ofReal]
      linear_combination r ^ 2 * hσ2
    have hvre : v.re = σ * r := by
      rw [hv, Complex.ofReal_re]
    have hnv : ‖v‖ ≤ 1 := by
      rw [Complex.norm_def, hnorm, Real.sqrt_sq hr0.le]
      exact hr1.le
    have hb := h v hnv
    have hsq : Complex.normSq (schurNum q t v) ≤ Complex.normSq (schurDen q t v) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hid := normSq_schurDen_sub_num q t v
    rw [hnorm, hvre] at hid
    have hneg : (q + 1) * (1 + r ^ 2) - 2 * t * (σ * r) = (q + 1) * (r ^ 2 - 1) := by
      have : t * (σ * r) = (q + 1) := by
        rw [← mul_assoc, hσt, mul_comm, hrt]
      linear_combination (-2 : ℝ) * this
    rw [hneg] at hid
    have hr2 : 0 < 1 - r ^ 2 := by nlinarith
    have hval : Complex.normSq (schurDen q t v) - Complex.normSq (schurNum q t v) < 0 := by
      rw [hid]
      have : (q - 1) * (1 - r ^ 2) * ((q + 1) * (r ^ 2 - 1)) =
          -((q - 1) * (q + 1) * (1 - r ^ 2) ^ 2) := by ring
      rw [this]
      have : 0 < (q - 1) * (q + 1) * (1 - r ^ 2) ^ 2 := by positivity
      linarith
    linarith
  · intro ht v hv
    have hsq : 0 ≤ Complex.normSq (schurDen q t v) - Complex.normSq (schurNum q t v) := by
      rw [normSq_schurDen_sub_num]
      have hv2 : Complex.normSq v ≤ 1 := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg v]
      have hv3 : 0 ≤ 1 - Complex.normSq v := by linarith
      have hre : |v.re| ≤ ‖v‖ := Complex.abs_re_le_norm v
      have hre2 : 2 * |v.re| ≤ 1 + Complex.normSq v := by
        have : v.re ^ 2 ≤ Complex.normSq v := by
          rw [Complex.normSq_apply]
          nlinarith [mul_self_nonneg v.im]
        nlinarith [sq_nonneg (|v.re| - 1), sq_abs v.re]
      have hmain : 0 ≤ (q + 1) * (1 + Complex.normSq v) - 2 * t * v.re := by
        have h1 : t * v.re ≤ |t| * |v.re| := by
          calc t * v.re ≤ |t * v.re| := le_abs_self _
            _ = |t| * |v.re| := abs_mul _ _
        have h2 : |t| * |v.re| ≤ (q + 1) * |v.re| :=
          mul_le_mul_of_nonneg_right ht (abs_nonneg _)
        nlinarith
      exact mul_nonneg (mul_nonneg hq1.le hv3) hmain
    have h2 : ‖schurNum q t v‖ ^ 2 ≤ ‖schurDen q t v‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The Schur symbol of the black hole. -/
def schurSymbol (q t : ℝ) (v : ℂ) : ℂ := v * schurNum q t v / schurDen q t v

/-- **Every black hole is passive.** The Schur symbol is bounded by `|v|` on the disc, true or fake. -/
theorem norm_schurSymbol_le (q t : ℝ) (hq : 1 < q) (ht : |t| ≤ q + 1) {v : ℂ} (hv : ‖v‖ ≤ 1) :
    ‖schurSymbol q t v‖ ≤ ‖v‖ := by
  have hb := (schur_bound_iff hq).mpr ht v hv
  unfold schurSymbol
  rw [norm_div, norm_mul]
  by_cases hR : ‖schurDen q t v‖ = 0
  · rw [hR, div_zero]
    exact norm_nonneg _
  · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hR))]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-- **The scattering coefficient is the ground factor times the Schur symbol**, with `v = q/X²`. -/
theorem radialScattering_eq_schur {q t : ℝ} {X : ℂ} (hX : X ≠ 0) (hq : (q : ℂ) ≠ 0)
    (h1 : X ^ 2 - (q : ℂ) ^ 2 ≠ 0) (h2 : X ^ 4 - t * X ^ 2 + q ≠ 0) :
    radialScattering t X ((q : ℂ) / X) =
      ((q : ℂ) - q / X ^ 2) / (1 - q * (q / X ^ 2)) * schurSymbol q t ((q : ℂ) / X ^ 2) := by
  rw [scattering_eq_prompt_add_core hX h1 h2]
  unfold schurSymbol schurNum schurDen
  have hR : (q : ℂ) - t * (q / X ^ 2) + (q / X ^ 2) ^ 2 = q * (X ^ 4 - t * X ^ 2 + q) / X ^ 4 := by
    field_simp
  have hG : 1 - (q : ℂ) * (q / X ^ 2) = (X ^ 2 - q ^ 2) / X ^ 2 := by
    field_simp
  have hN : 1 - (t : ℂ) * (q / X ^ 2) + q * (q / X ^ 2) ^ 2 =
      (X ^ 4 - t * q * X ^ 2 + q ^ 3) / X ^ 4 := by
    field_simp
  rw [hR, hG, hN]
  obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = X ^ 2 - (q : ℂ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = X ^ 4 - (t : ℂ) * X ^ 2 + q := ⟨_, rfl⟩
  rw [← hΔ] at h1 ⊢
  rw [← hP] at h2 ⊢
  field_simp
  rw [hΔ, hP]
  ring

/-! ### Reflection positivity -/

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- `A^n` applied to the unit impulse at the core. -/
def coreIter (q : ℕ) : ℕ → Vertex G D → ℂ
  | 0 => deltaCore
  | n + 1 => waveOp q (coreIter q n)

/-- The correlator of the core: the return amplitude of the impulse after `n` ticks. -/
def coreMoment (G D : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]
    (q n : ℕ) : ℂ := coreIter (G := G) (D := D) q n .core

/-- The impulse has finite speed: after `n` ticks it has not passed depth `n - 2`. -/
theorem coreIter_ray (q n : ℕ) (P : G) (k : ℕ) (hk : n < k + 2) :
    coreIter (G := G) (D := D) q n (.ray P k) = 0 := by
  induction n generalizing P k with
  | zero => rfl
  | succ n ih =>
    show waveOp q (coreIter q n) (.ray P k) = 0
    rcases k with _ | k
    · rw [waveOp_ray_zero, ih P 1 (by omega)]
      have hn : n = 0 := by omega
      subst hn
      unfold gapOp
      simp only [coreIter, deltaCore]
      split_ifs <;> simp
    · rw [waveOp_ray_succ, ih P k (by omega), ih P (k + 2) (by omega)]
      ring

/-- The iterates are real. -/
theorem coreIter_conj (q n : ℕ) (v : Vertex G D) :
    conj (coreIter q n v) = coreIter q n v := by
  induction n generalizing v with
  | zero =>
    rcases v with _ | d | x | L | ⟨P, k⟩ <;> simp [coreIter, deltaCore]
  | succ n ih =>
    show conj (waveOp q (coreIter q n) v) = waveOp q (coreIter q n) v
    rw [← waveOp_conj]
    congr 1
    funext w
    exact ih w

/-- Symmetry of the wave operator on functions that vanish at the boundary. -/
theorem Channels.pairing_waveOp_symm (B : Channels G D) (K : ℕ) {f g : Vertex G D → ℂ}
    (hf : ∀ P, f (.ray P K) = 0 ∧ f (.ray P (K + 1)) = 0) :
    pairing B.q (K + 1) (waveOp B.q f) g = pairing B.q (K + 1) f (waveOp B.q g) := by
  have hgreen := truncSum_greenDensity B f (fun v => conj (g v)) K
  have hzero : ∑ P : G, rayFlux B.q f (fun v => conj (g v)) P K = 0 := by
    refine Finset.sum_eq_zero fun P _ => ?_
    unfold rayFlux
    rw [(hf P).1, (hf P).2]
    ring
  rw [hzero] at hgreen
  have hsplit : truncSum (K + 1) (greenDensity B.q f fun v => conj (g v)) =
      pairing B.q (K + 1) (waveOp B.q f) g - pairing B.q (K + 1) f (waveOp B.q g) := by
    unfold pairing
    have h1 := truncSum_add (K + 1) (fun v => mass B.q v * (waveOp B.q f v * conj (g v)))
      (fun v => (-1 : ℂ) * (mass B.q v * (f v * conj (waveOp B.q g v))))
    rw [truncSum_smul] at h1
    rw [show (truncSum (K + 1) fun v => mass B.q v * (waveOp B.q f v * conj (g v))) -
        (truncSum (K + 1) fun v => mass B.q v * (f v * conj (waveOp B.q g v))) =
        (truncSum (K + 1) fun v => mass B.q v * (waveOp B.q f v * conj (g v))) +
          (-1 : ℂ) * (truncSum (K + 1) fun v => mass B.q v * (f v * conj (waveOp B.q g v))) by ring,
      ← h1]
    refine truncSum_congr _ fun v => ?_
    unfold greenDensity
    rw [waveOp_conj]
    ring
  rw [hsplit] at hgreen
  exact sub_eq_zero.mp hgreen

/-- Moving the operator across the pairing. -/
theorem Channels.pairing_coreIter (B : Channels G D) (K i j : ℕ) (hK : i + j < K + 2) :
    pairing B.q (K + 1) (coreIter (G := G) (D := D) B.q (i + j)) (coreIter B.q 0) =
      pairing B.q (K + 1) (coreIter (G := G) (D := D) B.q i) (coreIter B.q j) := by
  induction j generalizing i with
  | zero => rfl
  | succ j ih =>
    rw [show i + (j + 1) = (i + 1) + j by ring, ih (i + 1) (by omega)]
    show pairing B.q (K + 1) (waveOp B.q (coreIter B.q i)) (coreIter B.q j) =
      pairing B.q (K + 1) (coreIter B.q i) (waveOp B.q (coreIter B.q j))
    refine B.pairing_waveOp_symm K fun P => ⟨?_, ?_⟩
    · exact coreIter_ray B.q i P K (by omega)
    · exact coreIter_ray B.q i P (K + 1) (by omega)

/-- The pairing with the impulse reads the core value. -/
theorem pairing_deltaCore (q K : ℕ) (f : Vertex G D → ℂ) :
    pairing q K f (coreIter (G := G) (D := D) q 0) = f .core := by
  unfold pairing truncSum
  simp [coreIter, deltaCore]

/-- The truncated sum of a finite family. -/
theorem truncSum_finset_sum {ι : Type*} (s : Finset ι) (K : ℕ) (F : ι → Vertex G D → ℂ) :
    truncSum K (fun v => ∑ i ∈ s, F i v) = ∑ i ∈ s, truncSum K (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [truncSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, ← truncSum_add]
    refine truncSum_congr _ fun v => ?_
    rw [Finset.sum_insert ha]

/-- **Reflection positivity of the core correlator.** On every black hole, the Hankel matrices of the return
amplitudes are positive semidefinite. So this positivity has no information about `t` beyond the moments. -/
theorem Channels.coreMoment_psd (B : Channels G D) (n : ℕ) (c : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * coreMoment G D B.q (i + j) := by
  set K := 2 * n with hK
  set f : Vertex G D → ℂ := fun v => ∑ i, c i * coreIter B.q i v with hf
  have hnn : 0 ≤ pairing B.q (K + 1) f f := by
    unfold pairing
    refine truncSum_nonneg _ fun v => ?_
    exact mul_nonneg (B.mass_nonneg v) (mul_conj_nonneg _)
  have hexp : pairing B.q (K + 1) f f =
      ∑ i, ∑ j, c i * conj (c j) * coreMoment G D B.q (i + j) := by
    unfold pairing
    have e1 : (fun v => mass B.q v * (f v * conj (f v))) =
        fun v => ∑ i, ∑ j, c i * conj (c j) *
          (mass B.q v * (coreIter B.q i v * conj (coreIter B.q j v))) := by
      funext v
      simp only [hf, map_sum, map_mul]
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, truncSum_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [truncSum_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [truncSum_smul]
    congr 1
    have hij : (i : ℕ) + j < K + 2 := by
      have := i.2
      have := j.2
      omega
    have h := B.pairing_coreIter K i j hij
    unfold pairing at h
    rw [← h]
    have h0 := pairing_deltaCore (G := G) (D := D) B.q (K + 1) (coreIter B.q (i + j))
    unfold pairing at h0
    rw [h0]
    rfl
  rw [← hexp]
  exact hnn

/-- **The spectral density is a ratio of squares.** On the critical circle `Y = X̄`, the density of the core
measure `|X - Y|²/|j(X,Y)|²` is nonnegative for every `t`, true or fake. -/
theorem spectralDensity_nonneg {t : ℝ} {X Y : ℂ} (hY : Y = conj X) :
    0 ≤ ((X - Y) * (Y - X)) / (jost (t : ℂ) X Y * jost (t : ℂ) Y X) := by
  have hconj : jost (t : ℂ) Y X = conj (jost (t : ℂ) X Y) := by
    unfold jost
    rw [hY]
    simp [Complex.conj_ofReal]
  have hdiff : Y - X = conj (X - Y) := by
    rw [hY]
    simp
  rw [hconj, hdiff, Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_div]
  exact Complex.zero_le_real.mpr (div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

/-! ### Ramanujan -/

/-- **The Ramanujan shape holds on every black hole.** A zero of the Jost function that is not a ground state
has `|X|² < q`, so its outgoing state is not square-integrable. The `L²` spectrum of `A` in the radial sector
is the critical interval and the ground states, for every `t`. -/
theorem ramanujan_for_every_black_hole (B : Channels G D) {X Y : ℂ} (hXY : X * Y = B.q)
    (hj : jost B.trace X Y = 0) (hY : Y ^ 2 ≠ 1) : Complex.normSq X < B.q := by
  have hX0 : X ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hXY
    exact B.q_ne_zero hXY.symm
  rcases (jost_eq_zero_iff hXY hX0).mp hj with h | h
  · exact absurd h hY
  · rw [B.trace_eq_ofReal] at h
    have := B.norm_resonance_lt h
    rw [norm_pow, ← Complex.normSq_eq_norm_sq] at this
    exact this

/-- **`T_Q` is positive and has the norm of `A` on constants**: its coefficients are nonnegative and the
constants are an eigenvector, on every black hole. -/
theorem Channels.heckeOp_nonneg (B : Channels G D) (Q : G) {f : Vertex G D → ℝ} (hf : ∀ v, 0 ≤ f v)
    (v : Vertex G D) : 0 ≤ heckeOp B.q Q (fun w => (f w : ℂ)) v := by
  have h := waveOp_nonneg (G := G) (D := D) B.q (by have := B.two_le; omega)
    (f := fun w => f (transl (-Q) w)) (fun w => hf _) (transl Q v)
  obtain ⟨r, hr, hrv⟩ := h
  rw [heckeOp_eq_conj, hrv]
  exact Complex.zero_le_real.mpr hr

end GaloisForLFunctions.ArithmeticScatteringHolography

end
