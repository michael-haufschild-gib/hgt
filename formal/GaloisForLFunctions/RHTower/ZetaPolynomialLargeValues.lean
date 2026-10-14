import GaloisForLFunctions.RHTower.ZetaLineResonatorLargeValues

/-!
# Large values of `Re(ζ(½+it) P(½+it))` for a nonzero Dirichlet polynomial `P`

Let `P(s) = Σ_{j∈J} p(j) j^{−s}` with real coefficients, `J ⊆ ℕ_{≥1}` finite. On the critical line
`P(½+it) = Σ_j p(j) j^{−½} e^{−it log j}` (`polyLine`).

* **Twisted resonance** (`resonance_le`). Let `W_P` be the prime product resonator of
  `ZetaResonator` and `Q(t) = Σ_{a∈A} c(a) a^{it}` (`resQ`), with every prime of `P` coprime to `A`
  and `J`. If `Re(ζ P) ≤ B` on `[T, 2T]`, `B ≥ 0`, then
  `T ∏(2 + p^{−½}) Re 𝒫 − err ≤ B (2^{|P|} T ‖c‖² + err')`, with the resonance form
  `𝒫 = Σ_{j,a,b} p(j) c(a) c̄(b) [jb ∣ a] √(b/a)` (`twistForm`). The expansion
  `ζ P |Q|² = Σ p(j) j^{−½} c(a) c̄(b) ζ (a/(jb))^{it}` reduces it to the twisted moments
  `norm_twistInt_zeta_sub_le` and `norm_twistInt_one_sub_le`.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower.ZetaPolyResonator

open RHTower.WeilBoundaryDilation RHTower.ZetaLineTwist RHTower.ZetaResonator

local notation "eχ" => _root_.GaloisForLFunctions.expChar

/-! ## The objects -/

/-- `P(½+it) = Σ_{j∈J} p(j) j^{−½} e^{−it log j}`. -/
def polyLine (J : Finset ℕ) (p : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ J, ((p j * (Real.sqrt j)⁻¹ : ℝ) : ℂ) * eχ (-Real.log j) t

/-- The resonator `Q(t) = Σ_{a∈A} c(a) a^{it}`. -/
def resQ (A : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ := ∑ a ∈ A, c a * eχ (Real.log a) t

/-- The resonance form `𝒫 = Σ_{j,a,b} p(j) c(a) c̄(b) [jb ∣ a] √b/√a`. -/
def twistForm (J : Finset ℕ) (p : ℕ → ℝ) (A : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ j ∈ J, ∑ a ∈ A, ∑ b ∈ A, (p j : ℂ) * c a * conj (c b) *
    (if j * b ∣ a then ((Real.sqrt b / Real.sqrt a : ℝ) : ℂ) else 0)

/-- `‖c‖² = Σ_{a∈A} ‖c(a)‖²`. -/
def massForm (A : Finset ℕ) (c : ℕ → ℂ) : ℝ := ∑ a ∈ A, ‖c a‖ ^ 2

/-- The error weight of the twisted first moments. -/
def errZeta (J : Finset ℕ) (p : ℕ → ℝ) (A : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ j ∈ J, ∑ a ∈ A, ∑ b ∈ A, |p j| * (Real.sqrt j)⁻¹ * ‖c a‖ * ‖c b‖ *
    (Real.sqrt (((j * b : ℕ) : ℝ) * a) * (a : ℝ) ^ 2)

/-- The error weight of the twisted mass. -/
def errOne (A : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ A, ‖c a‖ * ‖c b‖ * (2 * (a : ℝ) * b)

/-! ## Characters -/

theorem expChar_mul (ξ η t : ℝ) : eχ ξ t * eχ η t = eχ (ξ + η) t := by
  unfold _root_.GaloisForLFunctions.expChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_expChar (ξ t : ℝ) : conj (eχ ξ t) = eχ (-ξ) t := by
  unfold _root_.GaloisForLFunctions.expChar
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem log_natMul {j b : ℕ} (hj : 1 ≤ j) (hb : 1 ≤ b) :
    Real.log ((j * b : ℕ) : ℝ) = Real.log j + Real.log b := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Nat.cast_mul, Real.log_mul hj0.ne' hb0.ne']

theorem resQ_mul_conj (A : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    resQ A c t * conj (resQ A c t) =
      ∑ a ∈ A, ∑ b ∈ A, c a * conj (c b) * eχ (Real.log a - Real.log b) t := by
  unfold resQ
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, conj_expChar, sub_eq_add_neg, ← expChar_mul]
  ring

/-- The pointwise expansion of `ζ P W |Q|²`. -/
theorem zeta_poly_resW_normSq_eq (J : Finset ℕ) (p : ℕ → ℝ) (A : Finset ℕ) (c : ℕ → ℂ)
    (P : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j) (hA : ∀ a ∈ A, 1 ≤ a) (f : ℝ → ℂ) (t : ℝ) :
    f t * polyLine J p t * (resW P t : ℂ) * (resQ A c t * conj (resQ A c t)) =
      ∑ j ∈ J, ∑ a ∈ A, ∑ b ∈ A,
        ((p j * (Real.sqrt j)⁻¹ : ℝ) : ℂ) * c a * conj (c b) *
          (f t * (resW P t : ℂ) * eχ (Real.log a - Real.log ((j * b : ℕ) : ℝ)) t) := by
  unfold polyLine
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, resQ_mul_conj]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [log_natMul (hJ j hj) (hA b hb)]
  have e : eχ (Real.log a - (Real.log j + Real.log b)) t =
      eχ (-Real.log j) t * eχ (Real.log a - Real.log b) t := by
    rw [expChar_mul]
    congr 1
    ring
  rw [e]
  ring

theorem resW_resQ_normSq_eq (A : Finset ℕ) (c : ℕ → ℂ) (P : Finset ℕ) (t : ℝ) :
    (resW P t : ℂ) * (resQ A c t * conj (resQ A c t)) =
      ∑ a ∈ A, ∑ b ∈ A, c a * conj (c b) *
        ((fun _ : ℝ => (1 : ℂ)) t * (resW P t : ℂ) * eχ (Real.log a - Real.log b) t) := by
  rw [resQ_mul_conj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ## The integrals as twisted moments -/

theorem continuous_twistIntegrand {f : ℝ → ℂ} (hf : Continuous f) (P : Finset ℕ) (ξ : ℝ) :
    Continuous fun t => f t * (resW P t : ℂ) * eχ ξ t :=
  (hf.mul (Complex.continuous_ofReal.comp (continuous_resW P))).mul (continuous_expChar' ξ)

theorem integral_poly_eq_sum {f : ℝ → ℂ} (hf : Continuous f) (T : ℝ) (J : Finset ℕ)
    (p : ℕ → ℝ) (A : Finset ℕ) (c : ℕ → ℂ) (P : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j)
    (hA : ∀ a ∈ A, 1 ≤ a) :
    ∫ t in T..(2 * T), f t * polyLine J p t * (resW P t : ℂ) * (resQ A c t * conj (resQ A c t)) =
      ∑ j ∈ J, ∑ a ∈ A, ∑ b ∈ A,
        ((p j * (Real.sqrt j)⁻¹ : ℝ) : ℂ) * c a * conj (c b) * twistInt f T P a (j * b) := by
  rw [intervalIntegral.integral_congr fun t _ => zeta_poly_resW_normSq_eq J p A c P hJ hA f t]
  have hc : ∀ (k : ℂ) (ξ : ℝ), Continuous fun t => k * (f t * (resW P t : ℂ) * eχ ξ t) :=
    fun k ξ => continuous_const.mul (continuous_twistIntegrand hf P ξ)
  rw [intervalIntegral.integral_finsetSum fun j _ => (continuous_finsetSum _ fun a _ =>
    continuous_finsetSum _ fun b _ => hc _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun a _ => (continuous_finsetSum _ fun b _ =>
    hc _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [intervalIntegral.integral_finsetSum fun b _ => (hc _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem integral_mass_eq_sum (T : ℝ) (A : Finset ℕ) (c : ℕ → ℂ) (P : Finset ℕ) :
    ∫ t in T..(2 * T), (resW P t : ℂ) * (resQ A c t * conj (resQ A c t)) =
      ∑ a ∈ A, ∑ b ∈ A, c a * conj (c b) * twistInt (fun _ => 1) T P a b := by
  rw [intervalIntegral.integral_congr fun t _ => resW_resQ_normSq_eq A c P t]
  have hc : ∀ (k : ℂ) (ξ : ℝ), Continuous
      fun t => k * ((fun _ : ℝ => (1 : ℂ)) t * (resW P t : ℂ) * eχ ξ t) :=
    fun k ξ => continuous_const.mul (continuous_twistIntegrand continuous_const P ξ)
  rw [intervalIntegral.integral_finsetSum fun a _ => (continuous_finsetSum _ fun b _ =>
    hc _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [intervalIntegral.integral_finsetSum fun b _ => (hc _ _).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [intervalIntegral.integral_const_mul]
  rfl

/-! ## Main terms -/

theorem sum_zetaMain_eq (T : ℝ) (J : Finset ℕ) (p : ℕ → ℝ) (A : Finset ℕ) (c : ℕ → ℂ)
    (P : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j) :
    ∑ j ∈ J, ∑ a ∈ A, ∑ b ∈ A,
        ((p j * (Real.sqrt j)⁻¹ : ℝ) : ℂ) * c a * conj (c b) * zetaMain T P a (j * b) =
      ((T * resGain P : ℝ) : ℂ) * twistForm J p A c := by
  unfold twistForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold zetaMain
  have hj0 : (0 : ℝ) < Real.sqrt j := Real.sqrt_pos.mpr (by exact_mod_cast hJ j hj)
  have hj0' : ((Real.sqrt j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hj0.ne'
  split_ifs with h
  · have hs : Real.sqrt ((j * b : ℕ) : ℝ) = Real.sqrt j * Real.sqrt b := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    rw [hs]
    push_cast
    field_simp
  · simp

theorem sum_oneMain_eq (T : ℝ) (A : Finset ℕ) (c : ℕ → ℂ) (P : Finset ℕ) :
    ∑ a ∈ A, ∑ b ∈ A, c a * conj (c b) * oneMain T P a b =
      (((2 : ℝ) ^ P.card * T * massForm A c : ℝ) : ℂ) := by
  unfold oneMain massForm
  have h : ∀ a ∈ A, ∑ b ∈ A, c a * conj (c b) *
      (if a = b then (((2 : ℝ) ^ P.card * T : ℝ) : ℂ) else 0) =
      (((2 : ℝ) ^ P.card * T * ‖c a‖ ^ 2 : ℝ) : ℂ) := by
    intro a ha
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq A a, if_pos ha, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, ← Complex.ofReal_sum, Finset.mul_sum]

/-! ## Error terms -/

theorem coprime_mul_of_coprime {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {j b : ℕ}
    (hj : ∀ q ∈ P, ¬ q ∣ j) (hb : ∀ q ∈ P, ¬ q ∣ b) : ∀ q ∈ P, ¬ q ∣ j * b := by
  intro q hq h
  rcases (hP q hq).dvd_mul.mp h with h | h
  · exact hj q hq h
  · exact hb q hq h

theorem norm_coef (p : ℝ) (j : ℕ) (x y : ℂ) :
    ‖((p * (Real.sqrt j)⁻¹ : ℝ) : ℂ) * x * conj y‖ = |p| * (Real.sqrt j)⁻¹ * ‖x‖ * ‖y‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]

/-- **The twisted first moment of `ζ P` against `W |Q|²`.** -/
theorem norm_integral_zeta_poly_sub_le {T : ℝ} (hT : 4 ≤ T) {P J A : Finset ℕ} {p : ℕ → ℝ}
    {c : ℕ → ℂ} (hP : ∀ q ∈ P, q.Prime) (hJ : ∀ j ∈ J, 1 ≤ j) (hA : ∀ a ∈ A, 1 ≤ a)
    (hcopJ : ∀ q ∈ P, ∀ j ∈ J, ¬ q ∣ j) (hcopA : ∀ q ∈ P, ∀ a ∈ A, ¬ q ∣ a) :
    ‖(∫ t in T..(2 * T), riemannZeta (linePt t) * polyLine J p t * (resW P t : ℂ) *
        (resQ A c t * conj (resQ A c t))) - ((T * resGain P : ℝ) : ℂ) * twistForm J p A c‖ ≤
      4 ^ P.card * primeProd P ^ 3 * (35 * Real.sqrt T) * errZeta J p A c := by
  rw [integral_poly_eq_sum continuous_zeta_linePt T J p A c P hJ hA,
    ← sum_zetaMain_eq T J p A c P hJ]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  unfold errZeta
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  rw [norm_mul, norm_coef]
  have hjb : 1 ≤ j * b := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := hJ j hj; omega) (by have := hA b hb; omega))
  have h := norm_twistInt_zeta_sub_le hT hP (hA a ha) hjb fun q hq =>
    ⟨hcopA q hq a ha, coprime_mul_of_coprime hP (fun q hq => hcopJ q hq j hj)
      (fun q hq => hcopA q hq b hb) q hq⟩
  have h0 : 0 ≤ |p j| * (Real.sqrt j)⁻¹ * ‖c a‖ * ‖c b‖ := by positivity
  calc |p j| * (Real.sqrt j)⁻¹ * ‖c a‖ * ‖c b‖ *
        ‖twistInt (fun t => riemannZeta (linePt t)) T P a (j * b) - zetaMain T P a (j * b)‖
      ≤ |p j| * (Real.sqrt j)⁻¹ * ‖c a‖ * ‖c b‖ *
          (4 ^ P.card * primeProd P ^ 3 *
            (35 * Real.sqrt (((j * b : ℕ) : ℝ) * a) * (a : ℝ) ^ 2 * Real.sqrt T)) :=
        mul_le_mul_of_nonneg_left h h0
    _ = _ := by ring

/-- **The twisted mass of `W |Q|²`.** -/
theorem norm_integral_mass_sub_le {T : ℝ} {P A : Finset ℕ} {c : ℕ → ℂ} (hP : ∀ q ∈ P, q.Prime)
    (hA : ∀ a ∈ A, 1 ≤ a) (hcopA : ∀ q ∈ P, ∀ a ∈ A, ¬ q ∣ a) :
    ‖(∫ t in T..(2 * T), (resW P t : ℂ) * (resQ A c t * conj (resQ A c t))) -
        (((2 : ℝ) ^ P.card * T * massForm A c : ℝ) : ℂ)‖ ≤
      4 ^ P.card * primeProd P ^ 2 * errOne A c := by
  rw [integral_mass_eq_sum T A c P, ← sum_oneMain_eq T A c P]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  unfold errOne
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have h := norm_twistInt_one_sub_le (T := T) hP (hA a ha) (hA b hb) fun q hq =>
    ⟨hcopA q hq a ha, hcopA q hq b hb⟩
  have h0 : 0 ≤ ‖c a‖ * ‖c b‖ := by positivity
  calc ‖c a‖ * ‖c b‖ * ‖twistInt (fun _ => 1) T P a b - oneMain T P a b‖
      ≤ ‖c a‖ * ‖c b‖ * (4 ^ P.card * primeProd P ^ 2 * (2 * (a : ℝ) * b)) :=
        mul_le_mul_of_nonneg_left h h0
    _ = _ := by ring

/-! ## Resonance -/

theorem integrand_eq_mul_ofReal (z w : ℂ) (W : ℝ) (t : ℝ) (A : Finset ℕ) (c : ℕ → ℂ) :
    z * w * (W : ℂ) * (resQ A c t * conj (resQ A c t)) =
      z * w * ((W * Complex.normSq (resQ A c t) : ℝ) : ℂ) := by
  rw [Complex.mul_conj]
  push_cast
  ring

/-- **The twisted resonance inequality.** If `Re(ζ P) ≤ B` on `[T, 2T]`, `B ≥ 0`, then
`T ∏(2 + p^{−½}) Re 𝒫 − err ≤ B (2^{|P|} T ‖c‖² + err')`. -/
theorem resonance_le {T B : ℝ} (hT : 4 ≤ T) (hB : 0 ≤ B) {P J A : Finset ℕ} {p : ℕ → ℝ}
    {c : ℕ → ℂ} (hP : ∀ q ∈ P, q.Prime) (hJ : ∀ j ∈ J, 1 ≤ j) (hA : ∀ a ∈ A, 1 ≤ a)
    (hcopJ : ∀ q ∈ P, ∀ j ∈ J, ¬ q ∣ j) (hcopA : ∀ q ∈ P, ∀ a ∈ A, ¬ q ∣ a)
    (hre : ∀ t ∈ Icc T (2 * T), (riemannZeta (linePt t) * polyLine J p t).re ≤ B) :
    T * resGain P * (twistForm J p A c).re -
        4 ^ P.card * primeProd P ^ 3 * (35 * Real.sqrt T) * errZeta J p A c ≤
      B * ((2 : ℝ) ^ P.card * T * massForm A c + 4 ^ P.card * primeProd P ^ 2 * errOne A c) := by
  have hI := norm_integral_zeta_poly_sub_le (p := p) (c := c) hT hP hJ hA hcopJ hcopA
  have hM := norm_integral_mass_sub_le (T := T) (c := c) hP hA hcopA
  set w : ℝ → ℝ := fun t => resW P t * Complex.normSq (resQ A c t) with hw
  have hw0 : ∀ t, 0 ≤ w t := fun t => mul_nonneg (resW_nonneg P t) (Complex.normSq_nonneg _)
  have hQc : Continuous fun t => resQ A c t := by
    unfold resQ
    exact continuous_finsetSum _ fun a _ => continuous_const.mul (continuous_expChar' _)
  have hwc : Continuous w := (continuous_resW P).mul (Complex.continuous_normSq.comp hQc)
  have hPc : Continuous fun t => polyLine J p t := by
    unfold polyLine
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_expChar' _)
  have hzc : Continuous fun t => riemannZeta (linePt t) * polyLine J p t :=
    continuous_zeta_linePt.mul hPc
  have eI : (∫ t in T..(2 * T), riemannZeta (linePt t) * polyLine J p t * (resW P t : ℂ) *
      (resQ A c t * conj (resQ A c t))) =
      ∫ t in T..(2 * T), riemannZeta (linePt t) * polyLine J p t * ((w t : ℝ) : ℂ) :=
    intervalIntegral.integral_congr fun t _ =>
      integrand_eq_mul_ofReal _ _ _ t A c
  have eM : (∫ t in T..(2 * T), (resW P t : ℂ) * (resQ A c t * conj (resQ A c t))) =
      (((∫ t in T..(2 * T), w t) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hw, Complex.mul_conj]
    push_cast
    ring
  rw [eI] at hI
  rw [eM, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hM
  have hreI : (∫ t in T..(2 * T), riemannZeta (linePt t) * polyLine J p t * ((w t : ℝ) : ℂ)).re =
      ∫ t in T..(2 * T), (riemannZeta (linePt t) * polyLine J p t).re * w t := by
    rw [← Complex.reCLM_apply, ← (Complex.reCLM).intervalIntegral_comp_comm
      ((show Continuous fun t => riemannZeta (linePt t) * polyLine J p t * ((w t : ℝ) : ℂ) from
        hzc.mul (Complex.continuous_ofReal.comp hwc)).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  have hup : ∫ t in T..(2 * T), (riemannZeta (linePt t) * polyLine J p t).re * w t ≤
      ∫ t in T..(2 * T), B * w t := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((Complex.continuous_re.comp hzc).mul hwc |>.intervalIntegrable _ _)
      ((continuous_const.mul hwc).intervalIntegrable _ _) fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hre t ht) (hw0 t)
  rw [intervalIntegral.integral_const_mul] at hup
  have hlow : T * resGain P * (twistForm J p A c).re -
      4 ^ P.card * primeProd P ^ 3 * (35 * Real.sqrt T) * errZeta J p A c ≤
      (∫ t in T..(2 * T), riemannZeta (linePt t) * polyLine J p t * ((w t : ℝ) : ℂ)).re := by
    have h1 := (Complex.abs_re_le_norm _).trans hI
    rw [Complex.sub_re, Complex.re_ofReal_mul] at h1
    linarith [(abs_le.mp h1).1]
  have hmass := (abs_le.mp hM).2
  calc T * resGain P * (twistForm J p A c).re -
        4 ^ P.card * primeProd P ^ 3 * (35 * Real.sqrt T) * errZeta J p A c
      ≤ B * ∫ t in T..(2 * T), w t := by linarith
    _ ≤ B * ((2 : ℝ) ^ P.card * T * massForm A c + 4 ^ P.card * primeProd P ^ 2 * errOne A c) := by
        apply mul_le_mul_of_nonneg_left _ hB; linarith

/-! ## Rotation by a fresh prime -/

/-- `A ∪ qA`. -/
def extendSet (A : Finset ℕ) (q : ℕ) : Finset ℕ := A ∪ A.image (· * q)

/-- `c'(n) = i c(n/q)` if `q ∣ n`, else `c(n)`. -/
def extendCoef (c : ℕ → ℂ) (q : ℕ) (n : ℕ) : ℂ := if q ∣ n then I * c (n / q) else c n

theorem disjoint_extend {A : Finset ℕ} {q : ℕ} (hqA : ∀ a ∈ A, ¬ q ∣ a) :
    Disjoint A (A.image (· * q)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hb
  exact hqA _ ha (Dvd.intro_left b rfl)

theorem extendCoef_of_mem {c : ℕ → ℂ} {q a : ℕ} (hqa : ¬ q ∣ a) : extendCoef c q a = c a := by
  simp [extendCoef, hqa]

theorem extendCoef_mul {c : ℕ → ℂ} {q a : ℕ} (hq : 0 < q) : extendCoef c q (a * q) = I * c a := by
  simp [extendCoef, Nat.mul_div_cancel _ hq]

theorem twistForm_extend {J A : Finset ℕ} {p : ℕ → ℝ} {c : ℕ → ℂ} {q : ℕ} (hq : q.Prime)
    (hqA : ∀ a ∈ A, ¬ q ∣ a) (hqJ : ∀ j ∈ J, ¬ q ∣ j) :
    twistForm J p (extendSet A q) (extendCoef c q) =
      (2 + I * (((Real.sqrt q)⁻¹ : ℝ) : ℂ)) * twistForm J p A c := by
  have hq0 : 0 < q := hq.pos
  have hinj : ∀ x ∈ A, ∀ y ∈ A, x * q = y * q → x = y := fun x _ y _ h =>
    Nat.eq_of_mul_eq_mul_right hq0 h
  have hsq : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hq0)
  unfold twistForm extendSet
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.sum_union (disjoint_extend hqA), Finset.sum_image hinj]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hqa := hqA a ha
  have hqb := hqA b hb
  have hcop : Nat.Coprime (j * b) q := by
    refine Nat.Coprime.mul_left ?_ ?_
    · exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr (hqJ j hj)))
    · exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqb))
  have d1 : j * b ∣ a * q ↔ j * b ∣ a := ⟨fun h => hcop.dvd_of_dvd_mul_right h,
    fun h => h.mul_right q⟩
  have d2 : ¬ j * (b * q) ∣ a := fun h => hqa (dvd_trans (Dvd.intro_left (j * b) (by ring)) h)
  have d3 : j * (b * q) ∣ a * q ↔ j * b ∣ a := by
    rw [show j * (b * q) = j * b * q by ring]
    exact Nat.mul_dvd_mul_iff_right hq0
  rw [extendCoef_of_mem hqa, extendCoef_of_mem hqb, extendCoef_mul hq0, extendCoef_mul hq0,
    if_neg d2, if_congr d1 rfl rfl, if_congr d3 rfl rfl]
  have e1 : Real.sqrt ((b * q : ℕ) : ℝ) / Real.sqrt ((a * q : ℕ) : ℝ) =
      Real.sqrt b / Real.sqrt a := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_mul (Nat.cast_nonneg _), mul_div_mul_right _ _ hsq.ne']
  have e2 : Real.sqrt b / Real.sqrt ((a * q : ℕ) : ℝ) =
      (Real.sqrt q)⁻¹ * (Real.sqrt b / Real.sqrt a) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    field_simp
  rw [e1, e2]
  split_ifs
  · rw [map_mul, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp

theorem massForm_extend {A : Finset ℕ} {c : ℕ → ℂ} {q : ℕ} (hq : q.Prime)
    (hqA : ∀ a ∈ A, ¬ q ∣ a) :
    massForm (extendSet A q) (extendCoef c q) = 2 * massForm A c := by
  have hinj : ∀ x ∈ A, ∀ y ∈ A, x * q = y * q → x = y := fun x _ y _ h =>
    Nat.eq_of_mul_eq_mul_right hq.pos h
  unfold massForm extendSet
  rw [Finset.sum_union (disjoint_extend hqA), Finset.sum_image hinj, two_mul]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [extendCoef_of_mem (hqA a ha)]
  · exact Finset.sum_congr rfl fun a _ => by
      rw [extendCoef_mul hq.pos, norm_mul, Complex.norm_I, one_mul]

/-! ## Iterated rotation -/

/-- The rotation factor `2 + i/√q` of a fresh prime. -/
def rotFactor (q : ℕ) : ℂ := 2 + I * (((Real.sqrt q)⁻¹ : ℝ) : ℂ)

theorem exists_rotated (J A₀ : Finset ℕ) (p : ℕ → ℝ) (c₀ : ℕ → ℂ) (Y₀ : ℕ)
    (hA₀ : ∀ a ∈ A₀, 1 ≤ a ∧ a ≤ Y₀) (hJ : ∀ j ∈ J, 1 ≤ j ∧ j ≤ Y₀) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ Y₀ < q) :
    ∃ (A : Finset ℕ) (c : ℕ → ℂ), (∀ a ∈ A, 1 ≤ a) ∧
      (∀ q, q.Prime → Y₀ < q → q ∉ S → ∀ a ∈ A, ¬ q ∣ a) ∧
      twistForm J p A c = (∏ q ∈ S, rotFactor q) * twistForm J p A₀ c₀ ∧
      massForm A c = 2 ^ S.card * massForm A₀ c₀ := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨A₀, c₀, fun a ha => (hA₀ a ha).1, fun q hq hqY _ a ha h => ?_, by simp, by simp⟩
    have := Nat.le_of_dvd (by have := (hA₀ a ha).1; omega) h
    have := (hA₀ a ha).2
    omega
  | insert q S hqS ih =>
    obtain ⟨A, c, hA1, hAcop, htw, hms⟩ := ih fun r hr => hS r (Finset.mem_insert_of_mem hr)
    obtain ⟨hq, hqY⟩ := hS q (Finset.mem_insert_self q S)
    have hqA : ∀ a ∈ A, ¬ q ∣ a := hAcop q hq hqY hqS
    have hqJ : ∀ j ∈ J, ¬ q ∣ j := fun j hj h => by
      have := Nat.le_of_dvd (by have := (hJ j hj).1; omega) h
      have := (hJ j hj).2
      omega
    refine ⟨extendSet A q, extendCoef c q, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_union.mp ha with h | h
      · exact hA1 a h
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := hA1 b hb; omega)
          hq.ne_zero)
    · intro r hr hrY hrS a ha hra
      have hrS' : r ∉ S := fun h => hrS (Finset.mem_insert_of_mem h)
      have hrq : r ≠ q := fun h => hrS (h ▸ Finset.mem_insert_self q S)
      rcases Finset.mem_union.mp ha with h | h
      · exact hAcop r hr hrY hrS' a h hra
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        rcases hr.dvd_mul.mp hra with h1 | h1
        · exact hAcop r hr hrY hrS' b hb h1
        · exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h1)
    · rw [twistForm_extend hq hqA hqJ, htw, Finset.prod_insert hqS, rotFactor]
      ring
    · rw [massForm_extend hq hqA, hms, Finset.card_insert_of_notMem hqS, pow_succ]
      ring

/-! ## The rotation angle -/

theorem rotFactor_re (q : ℕ) : (rotFactor q).re = 2 := by simp [rotFactor]

theorem rotFactor_im (q : ℕ) : (rotFactor q).im = (Real.sqrt q)⁻¹ := by
  have h2 : (2 : ℂ).im = 0 := by norm_num
  rw [rotFactor, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, h2]
  ring

theorem arg_rotFactor_lt (q : ℕ) : (rotFactor q).arg < Real.pi / 2 :=
  Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [rotFactor_re]; norm_num))

theorem norm_rotFactor_le {q : ℕ} (hq : 1 ≤ q) : ‖rotFactor q‖ ≤ 3 := by
  have h1 : (Real.sqrt q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hq))
  have h0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  unfold rotFactor
  calc ‖(2 : ℂ) + I * (((Real.sqrt q)⁻¹ : ℝ) : ℂ)‖ ≤ ‖(2 : ℂ)‖ + ‖I * (((Real.sqrt q)⁻¹ : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ = 2 + (Real.sqrt q)⁻¹ := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg h0]; simp
    _ ≤ 3 := by linarith

theorem inv_three_mul_le_arg_rotFactor {q : ℕ} (hq : 1 ≤ q) :
    (Real.sqrt q)⁻¹ / 3 ≤ (rotFactor q).arg := by
  have hz : rotFactor q ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [rotFactor_re] at this; simp at this
  have hn : 0 < ‖rotFactor q‖ := norm_pos_iff.mpr hz
  have harg0 : 0 ≤ (rotFactor q).arg :=
    Complex.arg_nonneg_iff.mpr (by rw [rotFactor_im]; exact inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hs := Complex.sin_arg (rotFactor q)
  rw [rotFactor_im] at hs
  have h0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h1 : (Real.sqrt q)⁻¹ / 3 ≤ (Real.sqrt q)⁻¹ / ‖rotFactor q‖ :=
    div_le_div_of_nonneg_left h0 hn (norm_rotFactor_le hq)
  rw [← hs] at h1
  exact h1.trans (Real.sin_le harg0)

/-- The primes `q ≤ Y` with `Y₀ < q`. -/
def rotSet (Y₀ Y : ℕ) : Finset ℕ := (Finset.range (Y + 1)).filter fun q => q.Prime ∧ Y₀ < q

/-- The cumulative rotation angle up to `Y`. -/
def rotAngle (Y₀ Y : ℕ) : ℝ := ∑ q ∈ rotSet Y₀ Y, (rotFactor q).arg

theorem rotAngle_zero (Y₀ : ℕ) : rotAngle Y₀ 0 = 0 := by
  simp [rotAngle, rotSet, Finset.sum_filter, Nat.not_prime_zero]

theorem rotAngle_succ (Y₀ Y : ℕ) :
    rotAngle Y₀ (Y + 1) = rotAngle Y₀ Y +
      if (Y + 1).Prime ∧ Y₀ < Y + 1 then (rotFactor (Y + 1)).arg else 0 := by
  unfold rotAngle rotSet
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp), add_comm]
  · simp

theorem one_div_le_arg_rotFactor {q : ℕ} (hq : 1 ≤ q) : 1 / (3 * (q : ℝ)) ≤ (rotFactor q).arg := by
  refine le_trans ?_ (inv_three_mul_le_arg_rotFactor hq)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs : Real.sqrt q ≤ q := by rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, inv_mul_eq_div,
    le_div_iff₀ hs0]
  nlinarith

theorem exists_lt_rotAngle (Y₀ : ℕ) (M : ℝ) : ∃ Y, M < rotAngle Y₀ Y := by
  by_contra hcon
  push Not at hcon
  apply not_summable_one_div_on_primes
  refine summable_of_sum_range_le (c := (Y₀ + 1 : ℝ) + 3 * M) (fun n => ?_) (fun n => ?_)
  · simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> positivity
  · have hb : ∀ i ∈ Finset.range n, ({p | Nat.Prime p}.indicator fun n => 1 / (n : ℝ)) i ≤
        (if i ≤ Y₀ then 1 else 0) + (if i ∈ rotSet Y₀ n then 1 / (i : ℝ) else 0) := by
      intro i hi
      simp only [Set.indicator, Set.mem_setOf_eq]
      by_cases hp : i.Prime
      · rw [if_pos hp]
        by_cases hY : i ≤ Y₀
        · rw [if_pos hY]
          have h1 : 1 / (i : ℝ) ≤ 1 := by
            rw [div_le_one (by exact_mod_cast hp.pos)]; exact_mod_cast hp.one_lt.le
          have h2 : 0 ≤ (if i ∈ rotSet Y₀ n then 1 / (i : ℝ) else 0) := by
            split_ifs <;> positivity
          linarith
        · have hmem : i ∈ rotSet Y₀ n := by
            unfold rotSet
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨by have := Finset.mem_range.mp hi; omega, hp, by omega⟩
          rw [if_neg hY, if_pos hmem, zero_add]
      · rw [if_neg hp]
        have h1 : 0 ≤ (if i ≤ Y₀ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
        have h2 : 0 ≤ (if i ∈ rotSet Y₀ n then 1 / (i : ℝ) else 0) := by
          split_ifs <;> positivity
        linarith
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_add_distrib]
    have hA : ∑ i ∈ Finset.range n, (if i ≤ Y₀ then (1 : ℝ) else 0) ≤ Y₀ + 1 := by
      rw [Finset.sum_boole]
      have hsub : (Finset.range n).filter (fun i => i ≤ Y₀) ⊆ Finset.range (Y₀ + 1) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        exact Finset.mem_range.mpr (by omega)
      have := Finset.card_le_card hsub
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hB : ∑ i ∈ Finset.range n, (if i ∈ rotSet Y₀ n then 1 / (i : ℝ) else 0) ≤ 3 * M := by
      rw [← Finset.sum_filter]
      have hsub : (Finset.range n).filter (fun i => i ∈ rotSet Y₀ n) ⊆ rotSet Y₀ n :=
        fun i hi => (Finset.mem_filter.mp hi).2
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
      have h3 : ∑ q ∈ rotSet Y₀ n, 1 / (q : ℝ) ≤ ∑ q ∈ rotSet Y₀ n, 3 * (rotFactor q).arg := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq1 : 1 ≤ q := by
          unfold rotSet at hq; rw [Finset.mem_filter] at hq; exact hq.2.1.one_lt.le
        have := one_div_le_arg_rotFactor hq1
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
        rw [div_le_iff₀ (by positivity)] at this
        rw [div_le_iff₀ hq0]
        nlinarith
      rw [← Finset.mul_sum] at h3
      have := hcon n
      unfold rotAngle at this
      linarith
    linarith

/-! ## A sign-reversing block of primes -/

theorem rotFactor_ne_zero (q : ℕ) : rotFactor q ≠ 0 := fun h => by
  have := congrArg Complex.re h; rw [rotFactor_re] at this; simp at this

theorem prod_rotFactor_eq (S : Finset ℕ) :
    ∏ q ∈ S, rotFactor q = ((∏ q ∈ S, ‖rotFactor q‖ : ℝ) : ℂ) *
      Complex.exp (((∑ q ∈ S, (rotFactor q).arg : ℝ) : ℂ) * I) := by
  have h : ∏ q ∈ S, rotFactor q =
      ∏ q ∈ S, (((‖rotFactor q‖ : ℝ) : ℂ) * Complex.exp (((rotFactor q).arg : ℂ) * I)) :=
    Finset.prod_congr rfl fun q _ => (Complex.norm_mul_exp_arg_mul_I _).symm
  rw [h, Finset.prod_mul_distrib, ← Complex.exp_sum, Complex.ofReal_prod, Complex.ofReal_sum,
    Finset.sum_mul]

/-- **Some block of fresh primes reverses the sign of the real part.** The cumulative angle
`Σ arg(2 + i/√q)` diverges in steps below `π/2`, so its first passage over `π/2` lands in
`(π/2, π)`. -/
theorem exists_rotSet_re_neg (Y₀ : ℕ) : ∃ Y, (∏ q ∈ rotSet Y₀ Y, rotFactor q).re < 0 := by
  classical
  have hex := exists_lt_rotAngle Y₀ (Real.pi / 2)
  have hspec : Real.pi / 2 < rotAngle Y₀ (Nat.find hex) := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h; rw [h, rotAngle_zero] at hspec; linarith [Real.pi_pos]
  obtain ⟨Y, hY⟩ : ∃ Y, Nat.find hex = Y + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hmin : rotAngle Y₀ Y ≤ Real.pi / 2 := by
    have := Nat.find_min hex (show Y < Nat.find hex by omega)
    push Not at this
    exact this
  have hite : (if (Y + 1).Prime ∧ Y₀ < Y + 1 then (rotFactor (Y + 1)).arg else 0) <
      Real.pi / 2 := by
    split_ifs
    · exact arg_rotFactor_lt _
    · linarith [Real.pi_pos]
  have hstep := rotAngle_succ Y₀ Y
  rw [hY] at hspec
  refine ⟨Y + 1, ?_⟩
  rw [prod_rotFactor_eq, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hpos : 0 < ∏ q ∈ rotSet Y₀ (Y + 1), ‖rotFactor q‖ :=
    Finset.prod_pos fun q _ => norm_pos_iff.mpr (rotFactor_ne_zero q)
  have hcos : Real.cos (rotAngle Y₀ (Y + 1)) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hspec (by linarith [Real.pi_pos])
  unfold rotAngle at hcos
  exact mul_neg_of_pos_of_neg hpos hcos

/-! ## The seed -/

theorem twistForm_singleton_one (J : Finset ℕ) (p : ℕ → ℝ) (h1 : 1 ∈ J) :
    twistForm J p {1} (fun _ => 1) = (p 1 : ℂ) := by
  unfold twistForm
  simp only [Finset.sum_singleton, mul_one, map_one, Nat.cast_one, Real.sqrt_one, div_one]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro j hj hj1
    rw [if_neg (fun h => hj1 (Nat.dvd_one.mp h))]
    simp
  · intro h; exact absurd h1 h

theorem twistForm_pair_one (J : Finset ℕ) (p : ℕ → ℝ) {j₀ : ℕ}
    (hj₀J : j₀ ∈ J) (hj₀ : 2 ≤ j₀) (hmin : ∀ j ∈ J, p j ≠ 0 → j₀ ≤ j) :
    twistForm J p {1, j₀} (fun _ => 1) = ((p j₀ / Real.sqrt j₀ : ℝ) : ℂ) := by
  have h1j : (1 : ℕ) ≠ j₀ := by omega
  unfold twistForm
  simp only [Finset.sum_pair h1j, mul_one, map_one]
  rw [Finset.sum_eq_single j₀]
  · have e1 : ¬ j₀ ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
    have e2 : ¬ j₀ * j₀ ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; nlinarith
    have e3 : j₀ ∣ j₀ := dvd_rfl
    have e4 : ¬ j₀ * j₀ ∣ j₀ := fun h => by have := Nat.le_of_dvd (by omega) h; nlinarith
    rw [if_neg e1, if_neg e2, if_pos e3, if_neg e4]
    simp
    ring
  · intro j hj hjj
    by_cases hpj : p j = 0
    · simp [hpj]
    · have hge := hmin j hj hpj
      have hgt : j₀ < j := lt_of_le_of_ne hge (Ne.symm hjj)
      have f1 : ¬ j ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
      have f2 : ¬ j * j₀ ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; nlinarith
      have f3 : ¬ j ∣ j₀ := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      have f4 : ¬ j * j₀ ∣ j₀ := fun h => by have := Nat.le_of_dvd (by omega) h; nlinarith
      rw [if_neg f1, if_neg f2, if_neg f3, if_neg f4]
      simp
  · intro h; exact absurd hj₀J h

theorem exists_seed {J : Finset ℕ} {p : ℕ → ℝ} (hJ : ∀ j ∈ J, 1 ≤ j) (hp : ∃ j ∈ J, p j ≠ 0) :
    ∃ (A₀ : Finset ℕ) (ω : ℝ), ω ≠ 0 ∧ (∀ a ∈ A₀, 1 ≤ a ∧ a ≤ J.sup id) ∧
      twistForm J p A₀ (fun _ => 1) = (ω : ℂ) ∧ 0 < massForm A₀ (fun _ => 1) := by
  classical
  by_cases h1 : 1 ∈ J ∧ p 1 ≠ 0
  · refine ⟨{1}, p 1, h1.2, fun a ha => ?_, twistForm_singleton_one J p h1.1, by
      simp [massForm]⟩
    rw [Finset.mem_singleton.mp ha]
    exact ⟨le_rfl, Finset.le_sup (f := id) h1.1⟩
  · have hne : (J.filter fun j => p j ≠ 0).Nonempty := by
      obtain ⟨j, hj, hpj⟩ := hp
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hpj⟩⟩
    set j₀ := (J.filter fun j => p j ≠ 0).min' hne with hj₀def
    have hj₀mem := Finset.min'_mem _ hne
    rw [← hj₀def, Finset.mem_filter] at hj₀mem
    have hmin : ∀ j ∈ J, p j ≠ 0 → j₀ ≤ j := fun j hj hpj =>
      Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj, hpj⟩)
    have hj₀1 : 1 ≤ j₀ := hJ j₀ hj₀mem.1
    have hj₀2 : 2 ≤ j₀ := by
      by_contra hc
      have : j₀ = 1 := by omega
      exact h1 ⟨this ▸ hj₀mem.1, this ▸ hj₀mem.2⟩
    refine ⟨{1, j₀}, p j₀ / Real.sqrt j₀, ?_, fun a ha => ?_,
      twistForm_pair_one J p hj₀mem.1 hj₀2 hmin, ?_⟩
    · exact div_ne_zero hj₀mem.2 (Real.sqrt_pos.mpr (by exact_mod_cast hj₀1)).ne'
    · have hsup : j₀ ≤ J.sup id := Finset.le_sup (f := id) hj₀mem.1
      rcases Finset.mem_insert.mp ha with h | h
      · rw [h]; exact ⟨le_rfl, by omega⟩
      · rw [Finset.mem_singleton.mp h]; exact ⟨hj₀1, hsup⟩
    · unfold massForm
      rw [Finset.sum_pair (by omega)]
      simp

/-! ## A resonator of positive resonance -/

theorem exists_positive_resonator {J : Finset ℕ} {p : ℕ → ℝ} (hJ : ∀ j ∈ J, 1 ≤ j)
    (hp : ∃ j ∈ J, p j ≠ 0) :
    ∃ (A : Finset ℕ) (c : ℕ → ℂ), (∀ a ∈ A, 1 ≤ a) ∧ 0 < (twistForm J p A c).re ∧
      0 < massForm A c := by
  obtain ⟨A₀, ω, hω, hA₀, htw₀, hm₀⟩ := exists_seed hJ hp
  have hJ' : ∀ j ∈ J, 1 ≤ j ∧ j ≤ J.sup id := fun j hj => ⟨hJ j hj, Finset.le_sup (f := id) hj⟩
  rcases lt_or_gt_of_ne hω with hneg | hpos
  · obtain ⟨Y, hY⟩ := exists_rotSet_re_neg (J.sup id)
    have hS : ∀ q ∈ rotSet (J.sup id) Y, q.Prime ∧ J.sup id < q := fun q hq => by
      unfold rotSet at hq; rw [Finset.mem_filter] at hq; exact hq.2
    obtain ⟨A, c, hA1, -, htw, hms⟩ := exists_rotated J A₀ p (fun _ => 1) (J.sup id) hA₀ hJ' _ hS
    refine ⟨A, c, hA1, ?_, ?_⟩
    · rw [htw, htw₀, Complex.re_mul_ofReal]
      exact mul_pos_of_neg_of_neg hY hneg
    · rw [hms]; positivity
  · exact ⟨A₀, fun _ => 1, fun a ha => (hA₀ a ha).1, by rw [htw₀, Complex.ofReal_re]; exact hpos,
      hm₀⟩

/-! ## Large values -/

theorem rotSet_subset_primesLE (Y y : ℕ) : rotSet Y y ⊆ Nat.primesLE y := by
  intro q hq
  unfold rotSet at hq
  rw [Finset.mem_filter, Finset.mem_range] at hq
  exact mem_primesLE.mpr ⟨by omega, hq.2.1⟩

theorem primeProd_le_of_subset {P P' : Finset ℕ} (h : P ⊆ P') (hP' : ∀ p ∈ P', p.Prime) :
    primeProd P ≤ primeProd P' := by
  unfold primeProd
  rw [← Nat.cast_prod, ← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd (Finset.prod_pos fun p hp => (hP' p hp).pos)
    (Finset.prod_dvd_prod_of_subset _ _ _ h)

theorem sum_primesLE_le (Y y : ℕ) :
    ∑ q ∈ Nat.primesLE y, 1 / Real.sqrt q ≤ ∑ q ∈ rotSet Y y, 1 / Real.sqrt q + (Y + 1) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Nat.primesLE y) (fun q => Y < q)]
  have h1 : (Nat.primesLE y).filter (fun q => Y < q) ⊆ rotSet Y y := by
    intro q hq
    rw [Finset.mem_filter, mem_primesLE] at hq
    unfold rotSet
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hq.1.2, hq.2⟩
  have h2 : ∑ q ∈ (Nat.primesLE y).filter (fun q => ¬ Y < q), 1 / Real.sqrt q ≤ Y + 1 := by
    have hsub : (Nat.primesLE y).filter (fun q => ¬ Y < q) ⊆ Finset.range (Y + 1) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      exact Finset.mem_range.mpr (by omega)
    calc ∑ q ∈ (Nat.primesLE y).filter (fun q => ¬ Y < q), 1 / Real.sqrt q
        ≤ ∑ q ∈ (Nat.primesLE y).filter (fun q => ¬ Y < q), (1 : ℝ) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [Finset.mem_filter, mem_primesLE] at hq
          have hq1 : (1 : ℝ) ≤ Real.sqrt q := by
            rw [show (1 : ℝ) = Real.sqrt 1 by simp]
            exact Real.sqrt_le_sqrt (by exact_mod_cast hq.1.2.one_lt.le)
          rw [div_le_one (by linarith)]; exact hq1
      _ = ((Nat.primesLE y).filter (fun q => ¬ Y < q)).card := by simp
      _ ≤ (Finset.range (Y + 1)).card := by exact_mod_cast Finset.card_le_card hsub
      _ = Y + 1 := by simp
  have h3 : ∑ q ∈ (Nat.primesLE y).filter (fun q => Y < q), 1 / Real.sqrt q ≤
      ∑ q ∈ rotSet Y y, 1 / Real.sqrt q :=
    Finset.sum_le_sum_of_subset_of_nonneg h1 fun q _ _ => by positivity
  linarith

theorem cube_div_le_sum_primesLE {N : ℕ} (hN : 5 ≤ N) :
    (N : ℝ) ^ 3 / 16 ≤ ∑ p ∈ Nat.primesLE (N ^ 8), 1 / Real.sqrt p := by
  have hN5 : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hy2 : 2 ≤ N ^ 8 := by
    have : 2 ≤ 5 ^ 8 := by norm_num
    exact this.trans (Nat.pow_le_pow_left hN 8)
  have hyR : ((N ^ 8 : ℕ) : ℝ) = (N : ℝ) ^ 8 := by push_cast; ring
  refine le_trans ?_ (theta_div_le_sum hy2)
  have hth := half_le_theta hN
  have hsq : Real.sqrt (((N ^ 8 : ℕ) : ℝ)) = (N : ℝ) ^ 4 := by
    rw [hyR, show (N : ℝ) ^ 8 = ((N : ℝ) ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog : Real.log (((N ^ 8 : ℕ) : ℝ)) ≤ 8 * N := by
    rw [hyR, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    push_cast; linarith
  have hy2R : (2 : ℝ) ≤ ((N ^ 8 : ℕ) : ℝ) := by exact_mod_cast hy2
  have hlog0 : 0 < Real.log (((N ^ 8 : ℕ) : ℝ)) := Real.log_pos (by linarith)
  rw [hsq, le_div_iff₀ (by positivity)]
  have h4 : (N : ℝ) ^ 3 / 16 * ((N : ℝ) ^ 4 * Real.log (((N ^ 8 : ℕ) : ℝ))) ≤
      (N : ℝ) ^ 3 / 16 * ((N : ℝ) ^ 4 * (8 * N)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
  have h5 : (N : ℝ) ^ 3 / 16 * ((N : ℝ) ^ 4 * (8 * N)) = (N : ℝ) ^ 8 / 2 := by ring
  linarith

/-- The two error terms at `T = e^{20y}` for the resonator primes in `(Y, y]`. -/
theorem errors_le_rotSet (Y : ℕ) {y : ℕ} (hy : 1 ≤ y) :
    4 ^ (rotSet Y y).card * primeProd (rotSet Y y) ^ 3 * (35 * Real.sqrt (Real.exp (20 * y))) ≤
        35 * Real.exp (20 * y) ∧
      4 ^ (rotSet Y y).card * primeProd (rotSet Y y) ^ 2 * 2 ≤ Real.exp (20 * y) := by
  obtain ⟨hEA, hEB⟩ := errors_le hy
  have hsub := rotSet_subset_primesLE Y y
  have hcard : (4 : ℝ) ^ (rotSet Y y).card ≤ 4 ^ (Nat.primesLE y).card :=
    pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hsub)
  have hQ := primeProd_le_of_subset hsub (primes_of_primesLE _)
  have hP : ∀ q ∈ rotSet Y y, q.Prime := fun q hq => (mem_primesLE.mp (hsub hq)).2
  have hQ1 := one_le_primeProd hP
  constructor
  · refine le_trans ?_ hEA
    have : (4 : ℝ) ^ (rotSet Y y).card * primeProd (rotSet Y y) ^ 3 ≤
        4 ^ (Nat.primesLE y).card * primeProd (Nat.primesLE y) ^ 3 :=
      mul_le_mul hcard (pow_le_pow_left₀ (by linarith) hQ 3) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  · refine le_trans ?_ hEB
    have : (4 : ℝ) ^ (rotSet Y y).card * primeProd (rotSet Y y) ^ 2 ≤
        4 ^ (Nat.primesLE y).card * primeProd (Nat.primesLE y) ^ 2 :=
      mul_le_mul hcard (pow_le_pow_left₀ (by linarith) hQ 2) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right this (by norm_num)

/-- The gain of the resonator primes in `(Y, N⁸]`. -/
theorem exp_le_gain_rotSet (Y : ℕ) {N : ℕ} (hN : 5 ≤ N) :
    Real.exp ((N : ℝ) ^ 3 / 64 - (Y + 1) / 4) ≤
      ∏ q ∈ rotSet Y (N ^ 8), (1 + 1 / (2 * Real.sqrt q)) := by
  have hP : ∀ q ∈ rotSet Y (N ^ 8), q.Prime := fun q hq =>
    (mem_primesLE.mp (rotSet_subset_primesLE Y _ hq)).2
  refine le_trans (Real.exp_le_exp.mpr ?_) (exp_sum_le_prod hP)
  have hS := cube_div_le_sum_primesLE hN
  have hS' := sum_primesLE_le Y (N ^ 8)
  have e : ∑ q ∈ rotSet Y (N ^ 8), 1 / (4 * Real.sqrt q) =
      (∑ q ∈ rotSet Y (N ^ 8), 1 / Real.sqrt q) / 4 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun q _ => by ring
  rw [e]
  linarith

/-- Arithmetic of the resonance inequality. -/
theorem gain_le_of_resonance {T c₂ G δ B m κ₁ κ₂ E₁ E₂ : ℝ} (hT0 : 0 < T) (hc₂ : 1 ≤ c₂)
    (hB0 : 0 ≤ B) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hE₁ : E₁ ≤ 35 * T)
    (hE₂ : E₂ * 2 ≤ T) (hres : T * (c₂ * G) * δ - E₁ * κ₁ ≤ B * (c₂ * T * m + E₂ * κ₂)) :
    G * δ ≤ B * (m + κ₂) + 35 * κ₁ := by
  have h1 : E₁ * κ₁ ≤ 35 * T * κ₁ := mul_le_mul_of_nonneg_right hE₁ hκ₁
  have h2 : B * (E₂ * κ₂) ≤ B * (T * κ₂) := by
    apply mul_le_mul_of_nonneg_left _ hB0
    apply mul_le_mul_of_nonneg_right _ hκ₂
    linarith
  have h3 : T * (c₂ * (G * δ)) ≤ T * (c₂ * (B * m) + B * κ₂ + 35 * κ₁) := by
    have e1 : T * (c₂ * G) * δ = T * (c₂ * (G * δ)) := by ring
    have e2 : B * (c₂ * T * m + E₂ * κ₂) = T * (c₂ * (B * m)) + B * (E₂ * κ₂) := by ring
    have e3 : T * (c₂ * (B * m) + B * κ₂ + 35 * κ₁) =
        T * (c₂ * (B * m)) + B * (T * κ₂) + 35 * T * κ₁ := by ring
    rw [e1, e2] at hres
    rw [e3]
    linarith
  have h4 : c₂ * (G * δ) ≤ c₂ * (B * m) + B * κ₂ + 35 * κ₁ := le_of_mul_le_mul_left h3 hT0
  have hBk : 0 ≤ B * κ₂ := mul_nonneg hB0 hκ₂
  have h5 : B * κ₂ + 35 * κ₁ ≤ c₂ * (B * κ₂ + 35 * κ₁) :=
    le_mul_of_one_le_left (by positivity) hc₂
  have h6 : c₂ * (G * δ) ≤ c₂ * (B * (m + κ₂) + 35 * κ₁) := by
    have e : c₂ * (B * (m + κ₂) + 35 * κ₁) = c₂ * (B * m) + c₂ * (B * κ₂ + 35 * κ₁) := by ring
    rw [e]; linarith
  exact le_of_mul_le_mul_left h6 (by linarith)

/-- Arithmetic of the final contradiction: `e^{N³/64 − c} δ ≤ D N⁸` fails for large `N`. -/
theorem not_exp_le_of_large {N δ D c : ℝ} (hN1 : 1 ≤ N) (hδ : 0 < δ)
    (hN : (64 : ℝ) ^ 4 * 24 * (D / δ * Real.exp c) < N) :
    ¬ Real.exp (N ^ 3 / 64 - c) * δ ≤ D * N ^ 8 := by
  intro h
  have hpow := Real.pow_div_factorial_le_exp (N ^ 3 / 64) (by positivity) 4
  have hfact : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfact] at hpow
  have hEc : 0 < Real.exp c := Real.exp_pos c
  have hsplit : Real.exp (N ^ 3 / 64 - c) = Real.exp (N ^ 3 / 64) / Real.exp c := by
    rw [Real.exp_sub]
  rw [hsplit] at h
  have h1 : (N ^ 3 / 64) ^ 4 / 24 / Real.exp c * δ ≤ D * N ^ 8 := by
    refine le_trans ?_ h
    apply mul_le_mul_of_nonneg_right _ hδ.le
    exact div_le_div_of_nonneg_right hpow hEc.le
  have hN8 : 0 < N ^ 8 := by positivity
  have h2 : N ^ 4 * N ^ 8 * δ ≤ (64 : ℝ) ^ 4 * 24 * Real.exp c * D * N ^ 8 := by
    have e : (N ^ 3 / 64) ^ 4 / 24 / Real.exp c * δ =
        N ^ 4 * N ^ 8 * δ / ((64 : ℝ) ^ 4 * 24 * Real.exp c) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at h1
    linarith
  have h3 : N ^ 4 * δ ≤ (64 : ℝ) ^ 4 * 24 * Real.exp c * D := by
    have e1 : N ^ 4 * N ^ 8 * δ = (N ^ 4 * δ) * N ^ 8 := by ring
    have e2 : (64 : ℝ) ^ 4 * 24 * Real.exp c * D * N ^ 8 =
        ((64 : ℝ) ^ 4 * 24 * Real.exp c * D) * N ^ 8 := by ring
    rw [e1, e2] at h2
    exact le_of_mul_le_mul_right h2 hN8
  have h4 : N ^ 4 ≤ (64 : ℝ) ^ 4 * 24 * (D / δ * Real.exp c) := by
    rw [show (64 : ℝ) ^ 4 * 24 * (D / δ * Real.exp c) =
      (64 : ℝ) ^ 4 * 24 * Real.exp c * D / δ by ring, le_div_iff₀ hδ]
    exact h3
  have hN4 : N ≤ N ^ 4 := le_self_pow₀ hN1 (by norm_num)
  linarith

/-- The resonance window bound from a failure of large values. -/
theorem re_le_on_window {J : Finset ℕ} {p : ℕ → ℝ} {K T₀ T : ℝ} {N : ℕ} (hN1 : (1 : ℝ) ≤ N)
    (hT : T = Real.exp (20 * ((N ^ 8 : ℕ) : ℝ))) (hNT : T₀ ≤ N)
    (hcon : ∀ t, T₀ ≤ t → (riemannZeta (linePt t) * polyLine J p t).re ≤ K * (Real.log t + 1)) :
    ∀ t ∈ Icc T (2 * T), (riemannZeta (linePt t) * polyLine J p t).re ≤
      |K| * (20 * (N : ℝ) ^ 8 + 2) := by
  intro t ht
  have hyR : ((N ^ 8 : ℕ) : ℝ) = (N : ℝ) ^ 8 := by push_cast; ring
  have hTlow : 1 + 20 * (N : ℝ) ^ 8 ≤ T := by
    rw [hT, hyR]; linarith [Real.add_one_le_exp (20 * (N : ℝ) ^ 8)]
  have hNy : (N : ℝ) ≤ (N : ℝ) ^ 8 := le_self_pow₀ hN1 (by norm_num)
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have hTt : T₀ ≤ t := by linarith [ht.1]
  have h := hcon t hTt
  have ht0 : 0 < t := by linarith [ht.1]
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
  have hlog : Real.log t ≤ 20 * (N : ℝ) ^ 8 + 1 := by
    have h1 := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num) hT0.ne', hT, Real.log_exp, hyR] at h1
    have := Real.log_two_lt_d9
    linarith
  have hK : K * (Real.log t + 1) ≤ |K| * (Real.log t + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
  have hK2 : |K| * (Real.log t + 1) ≤ |K| * (20 * (N : ℝ) ^ 8 + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
  linarith

/-- **Large values of `Re(ζ P)` on the critical line.** For a real Dirichlet polynomial
`P = Σ_{j∈J} p(j) j^{−s}` with some `p(j) ≠ 0`, and every `K`, `T₀`, there is `t ≥ T₀` with
`Re(ζ(½+it) P(½+it)) > K (log t + 1)`. -/
theorem exists_lt_re_zeta_mul_polyLine {J : Finset ℕ} {p : ℕ → ℝ} (hJ : ∀ j ∈ J, 1 ≤ j)
    (hp : ∃ j ∈ J, p j ≠ 0) (K T₀ : ℝ) :
    ∃ t : ℝ, T₀ ≤ t ∧ K * (Real.log t + 1) < (riemannZeta (linePt t) * polyLine J p t).re := by
  by_contra hcon
  push Not at hcon
  obtain ⟨A, c, hA1, hδ, hm⟩ := exists_positive_resonator hJ hp
  have hκ₁0 : 0 ≤ errZeta J p A c := by unfold errZeta; positivity
  have hκ₂0 : 0 ≤ errOne A c := by unfold errOne; positivity
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = max (J.sup id) (A.sup id) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ,
      D = |K| * 22 * (massForm A c + errOne A c) + 35 * errZeta J p A c := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 5 T₀)
    ((64 : ℝ) ^ 4 * 24 * (D / (twistForm J p A c).re * Real.exp (((Y : ℝ) + 1) / 4))))
  have hN5 : (5 : ℝ) ≤ N :=
    le_of_lt (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hN)
  have hNT : T₀ ≤ N := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hN)
  have hNC := lt_of_le_of_lt (le_max_right _ _) hN
  have hN5' : 5 ≤ N := by exact_mod_cast hN5
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hy1 : 1 ≤ N ^ 8 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨T, hT⟩ : ∃ T, T = Real.exp (20 * ((N ^ 8 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hT4 : 4 ≤ T := by
    have hyR : ((N ^ 8 : ℕ) : ℝ) = (N : ℝ) ^ 8 := by push_cast; ring
    have h1 : 1 + 20 * (N : ℝ) ^ 8 ≤ T := by
      rw [hT, hyR]; linarith [Real.add_one_le_exp (20 * (N : ℝ) ^ 8)]
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hN1
    linarith
  have hT0 : 0 < T := by linarith
  have hPprime : ∀ q ∈ rotSet Y (N ^ 8), q.Prime := fun q hq => by
    unfold rotSet at hq; rw [Finset.mem_filter] at hq; exact hq.2.1
  have hPY : ∀ q ∈ rotSet Y (N ^ 8), Y < q := fun q hq => by
    unfold rotSet at hq; rw [Finset.mem_filter] at hq; exact hq.2.2
  have hcopJ : ∀ q ∈ rotSet Y (N ^ 8), ∀ j ∈ J, ¬ q ∣ j := fun q hq j hj h => by
    have h1 := Nat.le_of_dvd (by have := hJ j hj; omega) h
    have h2 : j ≤ Y := by rw [hYdef]; exact le_max_of_le_left (Finset.le_sup (f := id) hj)
    have := hPY q hq; omega
  have hcopA : ∀ q ∈ rotSet Y (N ^ 8), ∀ a ∈ A, ¬ q ∣ a := fun q hq a ha h => by
    have h1 := Nat.le_of_dvd (by have := hA1 a ha; omega) h
    have h2 : a ≤ Y := by rw [hYdef]; exact le_max_of_le_right (Finset.le_sup (f := id) ha)
    have := hPY q hq; omega
  have hB0 : 0 ≤ |K| * (20 * (N : ℝ) ^ 8 + 2) := by positivity
  have hres := resonance_le (c := c) hT4 hB0 hPprime hJ hA1 hcopJ hcopA
    (re_le_on_window hN1 hT hNT hcon)
  obtain ⟨hE₁, hE₂⟩ := errors_le_rotSet Y hy1
  rw [← hT] at hE₁ hE₂
  rw [resGain_eq] at hres
  have hkey := gain_le_of_resonance hT0 (one_le_pow₀ (by norm_num)) hB0 hκ₁0 hκ₂0
    hE₁ hE₂ hres
  have hgain := exp_le_gain_rotSet Y hN5'
  have hlow : Real.exp ((N : ℝ) ^ 3 / 64 - ((Y : ℝ) + 1) / 4) * (twistForm J p A c).re ≤
      D * (N : ℝ) ^ 8 := by
    refine le_trans (mul_le_mul_of_nonneg_right hgain hδ.le) (hkey.trans ?_)
    have hN8 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hN1
    have hB : |K| * (20 * (N : ℝ) ^ 8 + 2) ≤ |K| * 22 * (N : ℝ) ^ 8 := by
      have := abs_nonneg K
      nlinarith
    have hmk : 0 ≤ massForm A c + errOne A c := by linarith
    have h1 := mul_le_mul_of_nonneg_right hB hmk
    have h2 : 35 * errZeta J p A c ≤ 35 * errZeta J p A c * (N : ℝ) ^ 8 :=
      le_mul_of_one_le_right (by positivity) hN8
    rw [hD]
    nlinarith
  exact not_exp_le_of_large hN1 hδ hNC hlow

end RHTower.ZetaPolyResonator
