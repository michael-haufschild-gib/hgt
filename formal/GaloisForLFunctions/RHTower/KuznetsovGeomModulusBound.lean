import GaloisForLFunctions.RHTower.KuznetsovKloostermanPhaseEnvelope

/-!
# One modulus of the geometric side of the large sieve

For a modulus `c` and coefficients `b` on `(N, 2N]` let

`Φ(c) = Σ_{m,n} b̄_m b_n S(m, n; c) Ψ_1(4π√(mn)/c)`  (`modulusForm`).

With `B(θ) = B_b(θ, c)` (`kloostermanPhaseForm`) and `b'_m = b_m/√m`:

* DI (5.6): `Φ(c) = ∫ 𝒢_K(w) tanh w (B(cosh w) − B(−cosh w))/i dw` (`modulusForm_eq_sin`);
* DI (5.7): `Φ(c) = (c/4π) ∫ R_K(w) (B'(cosh w) + B'(−cosh w)) dw` (`modulusForm_eq_cos`).

With the envelope of `B` this gives, for `c ≤ N` and `K ≥ 1` (`exists_norm_modulusForm_le`),

`|Φ(c)| ≤ (π/2) β Σ|b|² + 8√π e γ K e^{−K²/2} Σ|b|²`,
`|Φ(c)| ≤ (c/2π)(β (π+√π) K² + γ (10π+4√π) e K² e^{−K²/2}) Σ|b'|²`,

with `β = C√c N^{1/2+δ}`, `γ = C₀(1 + N/c)(N + c)`; and for `c > N`,
`|Φ(c)| ≤ 2γ(π/4 + 2πe) Σ|b|²`.  Always `|Φ(c)| ≤ 16π³e N² Σ|b|²` (`norm_modulusForm_le_trivial`).
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.KuznetsovSeparation

open RHTower.Sieve DeckPointPair KuznetsovGauss

noncomputable section

/-- `Φ(c) = Σ_{m,n} b̄_m b_n S(m, n; c) Ψ_1(4π√(mn)/c)`. -/
def modulusForm (c : ℕ) [NeZero c] (N : ℕ) (K : ℝ) (b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Ioc N (N + N), ∑ n ∈ Finset.Ioc N (N + N),
    conj (b m) * b n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
      gaussKernel 1 K (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c)

theorem two_sin_eq (y : ℝ) :
    ((2 * Real.sin y : ℝ) : ℂ) = (cexp ((y : ℂ) * I) - cexp (((-y : ℝ) : ℂ) * I)) / I := by
  rw [Complex.ofReal_mul, Complex.ofReal_sin, Complex.sin, Complex.div_I]
  push_cast
  ring_nf

theorem two_cos_eq (y : ℝ) :
    ((2 * Real.cos y : ℝ) : ℂ) = cexp ((y : ℂ) * I) + cexp (((-y : ℝ) : ℂ) * I) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

theorem integrable_gaussPrim_tanh_mul_bounded {K : ℝ} (hK : 0 < K) {f : ℝ → ℂ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ w, ‖f w‖ ≤ M) :
    Integrable fun w => ((gaussPrim K w * Real.tanh w : ℝ) : ℂ) * f w := by
  refine ((integrable_abs_gaussPrim_tanh hK).mul_const M).mono'
    (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun w => ?_)
  · have := continuous_tanh; unfold gaussPrim; fun_prop
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM w) (abs_nonneg _)

/-- **DI (5.6).** -/
theorem modulusForm_eq_sin (c : ℕ) [NeZero c] (N : ℕ) {K : ℝ} (hK : 0 < K) (b : ℕ → ℂ) :
    modulusForm c N K b = ∫ w, ((gaussPrim K w * Real.tanh w : ℝ) : ℂ) *
      ((kloostermanPhaseForm c N b (1 * Real.cosh w) -
        kloostermanPhaseForm c N b (-1 * Real.cosh w)) / I) := by
  set S := Finset.Ioc N (N + N)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  set E : ℕ → ℕ → ℝ → ℝ → ℂ := fun m n s w =>
    cexp (((2 * Real.pi * (2 * (s * Real.cosh w) / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * I)
  have hE : ∀ m n s w, ‖E m n s w‖ = 1 := fun m n s w => Complex.norm_exp_ofReal_mul_I _
  have hEc : ∀ m n s, Continuous (E m n s) := fun m n s => by simp only [E]; fun_prop
  have hterm : ∀ m ∈ S, ∀ n ∈ S, gaussKernel 1 K (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c) =
      ∫ w, ((gaussPrim K w * Real.tanh w : ℝ) : ℂ) * ((E m n 1 w - E m n (-1) w) / I) := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by
      have := (Finset.mem_Ioc.1 hm).1; exact_mod_cast (Nat.zero_le N).trans_lt this
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.1 hn).1; exact_mod_cast (Nat.zero_le N).trans_lt this
    have hX : 0 < 4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c := by
      have := Real.sqrt_pos.2 (mul_pos hm0 hn0); positivity
    rw [gaussKernel_one hK hX, Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [← Complex.ofReal_mul, show (2 : ℝ) * (gaussPrim K w * Real.tanh w * Real.sin
        (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c * Real.cosh w)) = (gaussPrim K w * Real.tanh w) *
          (2 * Real.sin (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c * Real.cosh w)) by ring,
      Complex.ofReal_mul, two_sin_eq]
    have e1 : E m n 1 w = cexp (((4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c * Real.cosh w : ℝ) : ℂ) * I) := by
      simp only [E]; congr 3; ring
    have e2 : E m n (-1) w =
        cexp (((-(4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c * Real.cosh w) : ℝ) : ℂ) * I) := by
      simp only [E]; congr 3; ring
    rw [e1, e2]
  have hint : ∀ m n, Integrable fun w =>
      ((gaussPrim K w * Real.tanh w : ℝ) : ℂ) * ((E m n 1 w - E m n (-1) w) / I) := fun m n => by
    refine integrable_gaussPrim_tanh_mul_bounded hK (by fun_prop) (M := 2) fun w => ?_
    rw [norm_div, Complex.norm_I, div_one]
    refine (norm_sub_le _ _).trans ?_
    rw [hE, hE]; norm_num
  rw [modulusForm]
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => by rw [hterm m hm n hn],
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => (integral_const_mul _ _).symm,
    Finset.sum_congr rfl fun m _ => (integral_finsetSum S fun n _ => (hint m n).const_mul _).symm,
    ← integral_finsetSum S fun m _ => integrable_finsetSum S fun n _ => (hint m n).const_mul _]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [kloostermanPhaseForm]
  rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [E]
  ring

/-- `b'_m = b_m/√m`. -/
def sqrtNormalize (b : ℕ → ℂ) (m : ℕ) : ℂ := b m / (Real.sqrt m : ℂ)

theorem integrable_cosWeight_mul_bounded {K : ℝ} (hK : 0 < K) {f : ℝ → ℂ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ w, ‖f w‖ ≤ M) :
    Integrable fun w => ((cosWeight K w : ℝ) : ℂ) * f w := by
  refine ((integrable_cosWeight hK).norm.mul_const M).mono'
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (integrable_cosWeight hK).aestronglyMeasurable).mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (hM w) (norm_nonneg _)

/-- **DI (5.7).** -/
theorem modulusForm_eq_cos (c : ℕ) [NeZero c] (N : ℕ) {K : ℝ} (hK : 0 < K) (b : ℕ → ℂ) :
    modulusForm c N K b = ((c / (4 * Real.pi) : ℝ) : ℂ) * ∫ w, ((cosWeight K w : ℝ) : ℂ) *
      (kloostermanPhaseForm c N (sqrtNormalize b) (1 * Real.cosh w) +
        kloostermanPhaseForm c N (sqrtNormalize b) (-1 * Real.cosh w)) := by
  set S := Finset.Ioc N (N + N)
  have hc0 : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  set E : ℕ → ℕ → ℝ → ℝ → ℂ := fun m n s w =>
    cexp (((2 * Real.pi * (2 * (s * Real.cosh w) / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * I)
  have hE : ∀ m n s w, ‖E m n s w‖ = 1 := fun m n s w => Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ m n, Integrable fun w =>
      ((cosWeight K w : ℝ) : ℂ) * (E m n 1 w + E m n (-1) w) := fun m n => by
    refine integrable_cosWeight_mul_bounded hK (by simp only [E]; fun_prop) (M := 2) fun w => ?_
    refine (norm_add_le _ _).trans ?_
    rw [hE, hE]; norm_num
  have hterm : ∀ m ∈ S, ∀ n ∈ S, conj (b m) * b n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
      gaussKernel 1 K (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c) =
      ((c / (4 * Real.pi) : ℝ) : ℂ) * ∫ w, conj (sqrtNormalize b m) * sqrtNormalize b n *
        kloostermanSum c (m : ZMod c) (n : ZMod c) *
          (((cosWeight K w : ℝ) : ℂ) * (E m n 1 w + E m n (-1) w)) := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by
      have := (Finset.mem_Ioc.1 hm).1; exact_mod_cast (Nat.zero_le N).trans_lt this
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.1 hn).1; exact_mod_cast (Nat.zero_le N).trans_lt this
    set X := 4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c
    have hsm := Real.sqrt_pos.2 hm0
    have hsn := Real.sqrt_pos.2 hn0
    have hX : 0 < X := by
      have := Real.sqrt_pos.2 (mul_pos hm0 hn0); simp only [X]; positivity
    have hK1 := mul_integral_gaussPrim_tanh_sin hK hX
    have hPsi : gaussKernel 1 K X = ((X⁻¹ : ℝ) : ℂ) *
        ∫ w, ((cosWeight K w : ℝ) : ℂ) * (E m n 1 w + E m n (-1) w) := by
      rw [gaussKernel_one hK hX]
      have h2 : (2 * ∫ w : ℝ, gaussPrim K w * Real.tanh w * Real.sin (X * Real.cosh w)) =
          X⁻¹ * ∫ w : ℝ, 2 * (cosWeight K w * Real.cos (X * Real.cosh w)) := by
        rw [integral_const_mul, ← hK1]; field_simp
      rw [h2, Complex.ofReal_mul, ← integral_complex_ofReal]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only
      rw [show (((2 * (cosWeight K w * Real.cos (X * Real.cosh w))) : ℝ) : ℂ) =
          ((cosWeight K w : ℝ) : ℂ) * ((2 * Real.cos (X * Real.cosh w) : ℝ) : ℂ) by push_cast; ring,
        two_cos_eq]
      have e1 : E m n 1 w = cexp (((X * Real.cosh w : ℝ) : ℂ) * I) := by
        simp only [E, X]; congr 3; ring
      have e2 : E m n (-1) w = cexp (((-(X * Real.cosh w) : ℝ) : ℂ) * I) := by
        simp only [E, X]; congr 3; ring
      rw [e1, e2]
    rw [hPsi, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [sqrtNormalize, X]
    have hmn : Real.sqrt ((m : ℝ) * n) = Real.sqrt m * Real.sqrt n :=
      Real.sqrt_mul hm0.le n
    rw [hmn, map_div₀, Complex.conj_ofReal]
    have : ((Real.sqrt m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsm.ne'
    have : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsn.ne'
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
  rw [modulusForm, Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => hterm m hm n hn]
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun m _ => (integral_finsetSum S fun n _ => (hint m n).const_mul _).symm,
    ← integral_finsetSum S fun m _ => integrable_finsetSum S fun n _ => (hint m n).const_mul _]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [kloostermanPhaseForm]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [E]
  ring

/-! ## Bounds for one modulus -/

theorem norm_modulusForm_le_sin (c : ℕ) [NeZero c] (N : ℕ) {K : ℝ} (hK : 0 < K) (b : ℕ → ℂ)
    {g : ℝ → ℝ} (hg : Integrable g)
    (hgb : ∀ w, |gaussPrim K w * Real.tanh w| * (‖kloostermanPhaseForm c N b (1 * Real.cosh w)‖ +
      ‖kloostermanPhaseForm c N b (-1 * Real.cosh w)‖) ≤ g w) :
    ‖modulusForm c N K b‖ ≤ ∫ w, g w := by
  rw [modulusForm_eq_sin c N hK b]
  refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun w => ?_)
  refine le_trans ?_ (hgb w)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, Complex.norm_I, div_one]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)

theorem norm_modulusForm_le_cos (c : ℕ) [NeZero c] (N : ℕ) {K : ℝ} (hK : 0 < K) (b : ℕ → ℂ)
    {g : ℝ → ℝ} (hg : Integrable g)
    (hgb : ∀ w, |cosWeight K w| * (‖kloostermanPhaseForm c N (sqrtNormalize b) (1 * Real.cosh w)‖ +
      ‖kloostermanPhaseForm c N (sqrtNormalize b) (-1 * Real.cosh w)‖) ≤ g w) :
    ‖modulusForm c N K b‖ ≤ c / (4 * Real.pi) * ∫ w, g w := by
  rw [modulusForm_eq_cos c N hK b, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hg
    (Eventually.of_forall fun w => ?_)) (by positivity)
  refine le_trans ?_ (hgb w)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)

/-- **The three bounds for one modulus.** -/
theorem exists_norm_modulusForm_le {δ : ℝ} (hδ : 0 < δ) : ∃ C C₀ : ℝ, 0 ≤ C ∧ 0 ≤ C₀ ∧
    ∀ (c : ℕ) [NeZero c] (N : ℕ), 1 ≤ N → ∀ (K : ℝ), 1 ≤ K → ∀ (b : ℕ → ℂ),
      (c ≤ N → ‖modulusForm c N K b‖ ≤
        (Real.pi / 2 * (C * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ)) +
          8 * Real.sqrt Real.pi * Real.exp 1 * (C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c)) *
            (K * Real.exp (-K ^ 2 / 2))) * ∑ n ∈ Finset.Ioc N (N + N), ‖b n‖ ^ 2) ∧
      (c ≤ N → ‖modulusForm c N K b‖ ≤ c / (2 * Real.pi) *
        ((C * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ)) * ((Real.pi + Real.sqrt Real.pi) * K ^ 2) +
          (C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c)) *
            ((10 * Real.pi + 4 * Real.sqrt Real.pi) * Real.exp 1 * K ^ 2 * Real.exp (-K ^ 2 / 2))) *
          ∑ n ∈ Finset.Ioc N (N + N), ‖sqrtNormalize b n‖ ^ 2) ∧
      (N < c → ‖modulusForm c N K b‖ ≤
        2 * (C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c)) * (Real.pi / 4 + 2 * Real.pi * Real.exp 1) *
          ∑ n ∈ Finset.Ioc N (N + N), ‖b n‖ ^ 2) := by
  obtain ⟨C, C₀, hC, hC₀, henv⟩ := exists_envelope_le hδ
  refine ⟨C, C₀, hC, hC₀, fun c _ N hN K hK b => ?_⟩
  have hK0 : 0 < K := by linarith
  have hc0 : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  set γ := C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c)
  have hγ : 0 ≤ γ := by positivity
  set β := C * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ)
  have hβ : 0 ≤ β := by positivity
  refine ⟨fun hcN => ?_, fun hcN => ?_, fun hcN => ?_⟩
  · set A := ∑ n ∈ Finset.Ioc N (N + N), ‖b n‖ ^ 2
    have hA : 0 ≤ A := Finset.sum_nonneg fun n _ => by positivity
    have hpt : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ w,
        ‖kloostermanPhaseForm c N b (s * Real.cosh w)‖ ≤ β * A + γ * A * tailFactor K w := by
      intro s hs w
      have := henv c N hN b K w s hs
      rw [if_pos hcN, if_pos hcN] at this
      exact this
    set g : ℝ → ℝ := fun w => 2 * β * A * |gaussPrim K w * Real.tanh w| +
      2 * γ * A * (|gaussPrim K w| * tailFactor K w)
    have hg : Integrable g :=
      ((integrable_abs_gaussPrim_tanh hK0).const_mul _).add
        ((integrable_abs_gaussPrim_mul_tailFactor hK).const_mul _)
    refine (norm_modulusForm_le_sin c N hK0 b hg fun w => ?_).trans ?_
    · have h1 := hpt 1 (Or.inl rfl) w
      have h2 := hpt (-1) (Or.inr rfl) w
      have ht : |gaussPrim K w * Real.tanh w| ≤ |gaussPrim K w| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_tanh_le_one w)
      have htF := tailFactor_nonneg K w
      have hgt := abs_nonneg (gaussPrim K w * Real.tanh w)
      calc |gaussPrim K w * Real.tanh w| * (‖kloostermanPhaseForm c N b (1 * Real.cosh w)‖ +
            ‖kloostermanPhaseForm c N b (-1 * Real.cosh w)‖)
          ≤ |gaussPrim K w * Real.tanh w| * (2 * (β * A + γ * A * tailFactor K w)) := by
            gcongr; linarith
        _ = 2 * β * A * |gaussPrim K w * Real.tanh w| +
              2 * γ * A * (|gaussPrim K w * Real.tanh w| * tailFactor K w) := by ring
        _ ≤ g w := by
            simp only [g]
            have : |gaussPrim K w * Real.tanh w| * tailFactor K w ≤ |gaussPrim K w| * tailFactor K w :=
              mul_le_mul_of_nonneg_right ht htF
            have : 0 ≤ 2 * γ * A := by positivity
            nlinarith
    · rw [integral_add ((integrable_abs_gaussPrim_tanh hK0).const_mul _)
        ((integrable_abs_gaussPrim_mul_tailFactor hK).const_mul _), integral_const_mul,
        integral_const_mul]
      have h1 := integral_abs_gaussPrim_tanh_le hK0
      have h2 := integral_abs_gaussPrim_mul_tailFactor_le hK
      have e1 : 0 ≤ 2 * β * A := by positivity
      have e2 : 0 ≤ 2 * γ * A := by positivity
      calc 2 * β * A * (∫ w, |gaussPrim K w * Real.tanh w|) +
            2 * γ * A * ∫ w, |gaussPrim K w| * tailFactor K w
          ≤ 2 * β * A * (Real.pi / 4) +
            2 * γ * A * (4 * Real.sqrt Real.pi * Real.exp 1 * K * Real.exp (-K ^ 2 / 2)) := by gcongr
        _ = _ := by ring
  · set A := ∑ n ∈ Finset.Ioc N (N + N), ‖sqrtNormalize b n‖ ^ 2
    have hA : 0 ≤ A := Finset.sum_nonneg fun n _ => by positivity
    have hpt : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ w,
        ‖kloostermanPhaseForm c N (sqrtNormalize b) (s * Real.cosh w)‖ ≤
          β * A + γ * A * tailFactor K w := by
      intro s hs w
      have := henv c N hN (sqrtNormalize b) K w s hs
      rw [if_pos hcN, if_pos hcN] at this
      exact this
    obtain ⟨hRt, hRtle⟩ := integral_abs_cosWeight_mul_tailFactor_le hK
    set g : ℝ → ℝ := fun w => 2 * β * A * |cosWeight K w| + 2 * γ * A * (|cosWeight K w| * tailFactor K w)
    have hg : Integrable g :=
      ((integrable_cosWeight hK0).abs.const_mul _).add (hRt.const_mul _)
    refine (norm_modulusForm_le_cos c N hK0 b hg fun w => ?_).trans ?_
    · have h1 := hpt 1 (Or.inl rfl) w
      have h2 := hpt (-1) (Or.inr rfl) w
      have hR := abs_nonneg (cosWeight K w)
      calc |cosWeight K w| * (‖kloostermanPhaseForm c N (sqrtNormalize b) (1 * Real.cosh w)‖ +
            ‖kloostermanPhaseForm c N (sqrtNormalize b) (-1 * Real.cosh w)‖)
          ≤ |cosWeight K w| * (2 * (β * A + γ * A * tailFactor K w)) := by gcongr; linarith
        _ = g w := by simp only [g]; ring
    · rw [integral_add ((integrable_cosWeight hK0).abs.const_mul _) (hRt.const_mul _),
        integral_const_mul, integral_const_mul]
      have h1 := integral_abs_cosWeight_le hK
      have e1 : 0 ≤ 2 * β * A := by positivity
      have e2 : 0 ≤ 2 * γ * A := by positivity
      calc c / (4 * Real.pi) * (2 * β * A * (∫ w, |cosWeight K w|) +
            2 * γ * A * ∫ w, |cosWeight K w| * tailFactor K w)
          ≤ c / (4 * Real.pi) * (2 * β * A * ((Real.pi + Real.sqrt Real.pi) * K ^ 2) +
            2 * γ * A * ((10 * Real.pi + 4 * Real.sqrt Real.pi) * Real.exp 1 * K ^ 2 *
              Real.exp (-K ^ 2 / 2))) := by gcongr
        _ = _ := by field_simp; ring
  · set A := ∑ n ∈ Finset.Ioc N (N + N), ‖b n‖ ^ 2
    have hA : 0 ≤ A := Finset.sum_nonneg fun n _ => by positivity
    have hcN' : ¬ c ≤ N := by omega
    have hpt : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ w,
        ‖kloostermanPhaseForm c N b (s * Real.cosh w)‖ ≤ γ * A * (1 + Real.cosh w) := by
      intro s hs w
      have := henv c N hN b K w s hs
      rw [if_neg hcN', if_neg hcN', zero_mul, zero_add] at this
      exact this
    obtain ⟨hint, hle⟩ := integral_abs_gaussPrim_tanh_mul_one_add_cosh_le hK
    set g : ℝ → ℝ := fun w => 2 * γ * A * (|gaussPrim K w * Real.tanh w| * (1 + Real.cosh w))
    refine (norm_modulusForm_le_sin c N hK0 b (g := g) (hint.const_mul (2 * γ * A)) fun w => ?_).trans ?_
    · have h1 := hpt 1 (Or.inl rfl) w
      have h2 := hpt (-1) (Or.inr rfl) w
      have hgt := abs_nonneg (gaussPrim K w * Real.tanh w)
      calc |gaussPrim K w * Real.tanh w| * (‖kloostermanPhaseForm c N b (1 * Real.cosh w)‖ +
            ‖kloostermanPhaseForm c N b (-1 * Real.cosh w)‖)
          ≤ |gaussPrim K w * Real.tanh w| * (2 * (γ * A * (1 + Real.cosh w))) := by gcongr; linarith
        _ = _ := by ring
    · rw [integral_const_mul]
      have e2 : 0 ≤ 2 * γ * A := by positivity
      calc 2 * γ * A * ∫ w, |gaussPrim K w * Real.tanh w| * (1 + Real.cosh w)
          ≤ 2 * γ * A * (Real.pi / 4 + 2 * Real.pi * Real.exp 1) := by gcongr
        _ = _ := by ring

/-- **The trivial bound**: `|Φ(c)| ≤ 16π³e N² Σ|b|²` for `K ≥ 1`. -/
theorem norm_modulusForm_le_trivial (c : ℕ) [NeZero c] (N : ℕ) {K : ℝ} (hK : 1 ≤ K) (b : ℕ → ℂ) :
    ‖modulusForm c N K b‖ ≤
      16 * Real.pi ^ 3 * Real.exp 1 * (N : ℝ) ^ 2 * ∑ n ∈ Finset.Ioc N (N + N), ‖b n‖ ^ 2 := by
  set S := Finset.Ioc N (N + N)
  have hK0 : 0 < K := by linarith
  have hc0 : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hM := gaussSinhMass_le hK
  have hM0 : 0 ≤ gaussSinhMass K := integral_nonneg fun w => abs_nonneg _
  have hterm : ∀ m ∈ S, ∀ n ∈ S, ‖conj (b m) * b n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
      gaussKernel 1 K (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c)‖ ≤
      ‖b m‖ * ‖b n‖ * (16 * Real.pi ^ 3 * Real.exp 1 * N) := by
    intro m hm n hn
    rw [Finset.mem_Ioc] at hm hn
    have hS : ‖kloostermanSum c (m : ZMod c) (n : ZMod c)‖ ≤ c :=
      (norm_kloostermanSum_le_totient c _ _).trans (by exact_mod_cast Nat.totient_le c)
    have hsq : Real.sqrt ((m : ℝ) * n) ≤ 2 * N := by
      rw [Real.sqrt_le_left (by positivity)]
      have h1 : (m : ℝ) ≤ 2 * N := by have : (m : ℝ) ≤ N + N := by exact_mod_cast hm.2
                                      linarith
      have h2 : (n : ℝ) ≤ 2 * N := by have : (n : ℝ) ≤ N + N := by exact_mod_cast hn.2
                                      linarith
      have := Nat.cast_nonneg (α := ℝ) m
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    have hX : 0 ≤ 4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c := by positivity
    have hG := norm_gaussKernel_le le_rfl hK0 hX
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
    have hG' : ‖gaussKernel 1 K (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c)‖ ≤
        Real.pi * (4 * Real.pi * (2 * N) / c) * (2 * Real.pi * Real.exp 1) := by
      refine hG.trans ?_
      gcongr
    calc ‖b m‖ * ‖b n‖ * ‖kloostermanSum c (m : ZMod c) (n : ZMod c)‖ *
          ‖gaussKernel 1 K (4 * Real.pi * Real.sqrt ((m : ℝ) * n) / c)‖
        ≤ ‖b m‖ * ‖b n‖ * c * (Real.pi * (4 * Real.pi * (2 * N) / c) * (2 * Real.pi * Real.exp 1)) := by
          gcongr
      _ = _ := by field_simp; ring
  have hsumsq : (∑ m ∈ S, ‖b m‖) ^ 2 ≤ N * ∑ n ∈ S, ‖b n‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun m => ‖b m‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    have hcard : (S.card : ℝ) = N := by
      simp only [S, Nat.card_Ioc]; rw [Nat.add_sub_cancel]
    rw [hcard] at h
    exact h
  calc ‖modulusForm c N K b‖ ≤ ∑ m ∈ S, ∑ n ∈ S, ‖b m‖ * ‖b n‖ * (16 * Real.pi ^ 3 * Real.exp 1 * N) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n hn => hterm m hm n hn))
    _ = 16 * Real.pi ^ 3 * Real.exp 1 * N * (∑ m ∈ S, ‖b m‖) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ ≤ 16 * Real.pi ^ 3 * Real.exp 1 * N * (N * ∑ n ∈ S, ‖b n‖ ^ 2) := by gcongr
    _ = _ := by ring

end

end GaloisForLFunctions.RHTower.KuznetsovSeparation
