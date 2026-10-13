import GaloisForLFunctions.RHTower.FinitePoissonDecayWitness

/-!
# No finite Poisson superposition is blind at all large integers

For points `z_i = p_i + i q_i ∈ ℍ` and the `s = ½` Poisson vectors `φ_{z_i}(x) = (q_i/((x−p_i)² + q_i²))^{1/2}`,
the derivative of `h = Σ a_i φ_{z_i}` has the Fourier moments

`∫ h'(x) sin(cx) dx = −2c Σ a_i √q_i K₀(c q_i) cos(c p_i)`,
`∫ h'(x) cos(cx) dx = 2c Σ a_i √q_i K₀(c q_i) sin(c p_i)`

(`integral_poissonVectorDeriv_mul_sin`, `integral_poissonVectorDeriv_mul_cos`).

**Theorem** (`eq_zero_of_finitePoisson_blind`). Suppose no two of the points differ by an integer
translation, i.e. their heights differ or their real parts are incongruent mod `1`. If both moments
vanish at every frequency `2π(n+1)` with `n ≥ n₀`, then every weight `a_i` is zero.

Proof:
- The lowest height `q₁` dominates: `K₀(c q)/K₀(c q₁) ≤ e^{−c(q − q₁)}` (`kMoment_le_exp_mul`). So the
  exponential sum `Σ_{q_i = q₁} a_i e^{2πi n p_i}` tends to `0`.
- A finite exponential sum with frequencies distinct mod `1` tends to `0` along the integers only if all
  its coefficients vanish (`eq_zero_of_natExpSum_tendsto_zero`). Proof: `F(n+1) − e^{2πiθ_L} F(n)`
  removes one frequency.
- Induct.

Together with `exists_finitePoisson_decayWitness` this is a sharp dichotomy for the decay-class (N1)
problem in the line model. Every finite level is realized by finitely many points of `ℍ`. No exact
witness is a finite superposition: it must spread over infinitely many points, like the arc measure of
the log-edge witness.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Exponential sums along the integers -/

/-- `e(x) = exp(2πix)`. -/
def twoPiExp (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

theorem norm_twoPiExp (x : ℝ) : ‖twoPiExp x‖ = 1 := by
  rw [twoPiExp, Complex.norm_exp]
  simp [Complex.mul_re]

theorem twoPiExp_add (x y : ℝ) : twoPiExp (x + y) = twoPiExp x * twoPiExp y := by
  rw [twoPiExp, twoPiExp, twoPiExp, ← Complex.exp_add]; push_cast; ring_nf

theorem twoPiExp_ne_of_not_int {x y : ℝ} (h : ∀ k : ℤ, x - y ≠ k) : twoPiExp x ≠ twoPiExp y := by
  intro hxy
  rw [twoPiExp, twoPiExp, Complex.exp_eq_exp_iff_exists_int] at hxy
  obtain ⟨k, hk⟩ := hxy
  apply h k
  have h2 : (2 * Real.pi * Complex.I) * ((x : ℂ) - y - k) = 0 := by rw [mul_sub, mul_sub, hk]; ring
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h3 := (mul_eq_zero.mp h2).resolve_left hne
  have h4 : ((x - y - k : ℝ) : ℂ) = 0 := by push_cast; exact h3
  have := Complex.ofReal_eq_zero.mp h4
  linarith

/-- **Exponential sums along the integers.** If `Σ_{i ∈ s} b_i e^{2πi n θ_i} → 0` as `n → ∞` and the
`θ_i` are pairwise incongruent mod `1`, then every `b_i` vanishes. -/
theorem eq_zero_of_natExpSum_tendsto_zero {ι : Type*} [DecidableEq ι] (θ : ι → ℝ) :
    ∀ (s : Finset ι) (b : ι → ℂ), (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ k : ℤ, θ i - θ j ≠ k) →
      Tendsto (fun n : ℕ => ∑ i ∈ s, b i * twoPiExp (n * θ i)) atTop (𝓝 0) → ∀ i ∈ s, b i = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro b _ _ i hi; simp at hi
  | @insert L s hL ih =>
    intro b hdist h0
    have hdist' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ k : ℤ, θ i - θ j ≠ k := fun i hi j hj =>
      hdist i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    set F : ℕ → ℂ := fun n => ∑ i ∈ insert L s, b i * twoPiExp (n * θ i) with hF
    -- remove the frequency `θ_L`
    have hstep : Tendsto (fun n : ℕ => ∑ i ∈ s, (b i * (twoPiExp (θ i) - twoPiExp (θ L))) *
        twoPiExp (n * θ i)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => F (n + 1) - twoPiExp (θ L) * F n) atTop
          (𝓝 (0 - twoPiExp (θ L) * 0)) :=
        ((h0.comp (tendsto_add_atTop_nat 1)).sub (h0.const_mul _))
      rw [mul_zero, sub_zero] at h1
      refine h1.congr fun n => ?_
      have hsplit : F (n + 1) - twoPiExp (θ L) * F n =
          (b L * twoPiExp (θ L) * twoPiExp (n * θ L) +
            ∑ i ∈ s, b i * twoPiExp (θ i) * twoPiExp (n * θ i)) -
          twoPiExp (θ L) * (b L * twoPiExp (n * θ L) + ∑ i ∈ s, b i * twoPiExp (n * θ i)) := by
        have e1 : ∀ i, b i * twoPiExp (((n + 1 : ℕ) : ℝ) * θ i) =
            b i * twoPiExp (θ i) * twoPiExp (n * θ i) := fun i => by
          rw [show ((n + 1 : ℕ) : ℝ) * θ i = θ i + n * θ i by push_cast; ring, twoPiExp_add]; ring
        simp only [hF]
        rw [Finset.sum_insert hL, Finset.sum_insert hL]
        simp_rw [e1]
      rw [hsplit, mul_add, Finset.mul_sum]
      calc b L * twoPiExp (θ L) * twoPiExp (n * θ L) +
            ∑ i ∈ s, b i * twoPiExp (θ i) * twoPiExp (n * θ i) -
          (twoPiExp (θ L) * (b L * twoPiExp (n * θ L)) +
            ∑ i ∈ s, twoPiExp (θ L) * (b i * twoPiExp (n * θ i)))
          = ∑ i ∈ s, b i * twoPiExp (θ i) * twoPiExp (n * θ i) -
              ∑ i ∈ s, twoPiExp (θ L) * (b i * twoPiExp (n * θ i)) := by ring
        _ = ∑ i ∈ s, (b i * twoPiExp (θ i) * twoPiExp (n * θ i) -
              twoPiExp (θ L) * (b i * twoPiExp (n * θ i))) := (Finset.sum_sub_distrib _ _).symm
        _ = _ := Finset.sum_congr rfl fun i _ => by ring
    have hs := ih (fun i => b i * (twoPiExp (θ i) - twoPiExp (θ L))) hdist' hstep
    have hbs : ∀ i ∈ s, b i = 0 := by
      intro i hi
      have h := hs i hi
      have hne : twoPiExp (θ i) - twoPiExp (θ L) ≠ 0 := sub_ne_zero.mpr (twoPiExp_ne_of_not_int
        (hdist i (Finset.mem_insert_of_mem hi) L (Finset.mem_insert_self L s)
          (by rintro rfl; exact hL hi)))
      exact (mul_eq_zero.mp h).resolve_right hne
    have hFL : ∀ n : ℕ, F n = b L * twoPiExp (n * θ L) := fun n => by
      simp only [hF]
      rw [Finset.sum_insert hL, Finset.sum_eq_zero fun i hi => by rw [hbs i hi, zero_mul], add_zero]
    have hbL : b L = 0 := by
      have hn : Tendsto (fun n : ℕ => ‖F n‖) atTop (𝓝 0) := by
        have := h0.norm; rwa [norm_zero] at this
      have hconst : ∀ n : ℕ, ‖F n‖ = ‖b L‖ := fun n => by rw [hFL, norm_mul, norm_twoPiExp, mul_one]
      simp_rw [hconst] at hn
      exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hn)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hbL
    · exact hbs i hi'

/-! ### Poisson vectors at arbitrary points -/

/-- The derivative `−√q (x − p)((x − p)² + q²)^{−3/2}` of `φ_{p+iq}`. -/
def poissonVectorDeriv (z : ℝ × ℝ) (x : ℝ) : ℝ :=
  -(Real.sqrt z.2 * ((x - z.1) * ((x - z.1) ^ 2 + z.2 ^ 2) ^ (-(3 / 2) : ℝ)))

theorem hasDerivAt_poissonVector {z : ℝ × ℝ} (hq : 0 < z.2) (x : ℝ) :
    HasDerivAt (poissonVector z) (poissonVectorDeriv z x) x := by
  have hA : 0 < (x - z.1) ^ 2 + z.2 ^ 2 := by positivity
  have hfun : poissonVector z = fun x => Real.sqrt z.2 * ((x - z.1) ^ 2 + z.2 ^ 2) ^ (-(1 / 2) : ℝ) := by
    funext x
    have hA' : 0 < (x - z.1) ^ 2 + z.2 ^ 2 := by positivity
    unfold poissonVector
    rw [Real.div_rpow hq.le hA'.le, Real.rpow_neg hA'.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  rw [hfun]
  have hd : HasDerivAt (fun x : ℝ => (x - z.1) ^ 2 + z.2 ^ 2) (2 * (x - z.1)) x := by
    have := ((hasDerivAt_id x).sub_const z.1).pow 2
    simpa using this.add_const (z.2 ^ 2)
  have h := (hd.rpow_const (p := -(1 / 2)) (Or.inl hA.ne')).const_mul (Real.sqrt z.2)
  refine h.congr_deriv ?_
  unfold poissonVectorDeriv
  rw [show (-(1 / 2) : ℝ) - 1 = -(3 / 2) by norm_num]
  ring

theorem integral_poissonVectorDeriv_mul_sin {z : ℝ × ℝ} (hq : 0 < z.2) {c : ℝ} (hc : 0 < c) :
    ∫ x, poissonVectorDeriv z x * Real.sin (c * x) =
      -(2 * c * Real.sqrt z.2 * kMoment 0 (c * z.2) * Real.cos (c * z.1)) := by
  have e : (fun x => poissonVectorDeriv z x * Real.sin (c * x)) = fun x =>
      -(Real.sqrt z.2 * ((x - z.1) * ((x - z.1) ^ 2 + z.2 ^ 2) ^ (-(3 / 2) : ℝ) *
        Real.sin (c * x))) := by
    funext x; simp only [poissonVectorDeriv]; ring
  rw [e, integral_neg, integral_const_mul, integral_shift_mul_rpow_sin hq hc]
  ring

theorem integral_poissonVectorDeriv_mul_cos {z : ℝ × ℝ} (hq : 0 < z.2) {c : ℝ} (hc : 0 < c) :
    ∫ x, poissonVectorDeriv z x * Real.cos (c * x) =
      2 * c * Real.sqrt z.2 * kMoment 0 (c * z.2) * Real.sin (c * z.1) := by
  have e : (fun x => poissonVectorDeriv z x * Real.cos (c * x)) = fun x =>
      -(Real.sqrt z.2 * ((x - z.1) * ((x - z.1) ^ 2 + z.2 ^ 2) ^ (-(3 / 2) : ℝ) *
        Real.cos (c * x))) := by
    funext x; simp only [poissonVectorDeriv]; ring
  rw [e, integral_neg, integral_const_mul, integral_shift_mul_rpow_cos hq hc]
  ring

theorem integrable_poissonVectorDeriv_mul_trig {z : ℝ × ℝ} (hq : 0 < z.2) {g : ℝ → ℝ}
    (hg : Continuous g) (hg1 : ∀ x, |g x| ≤ 1) :
    Integrable fun x => poissonVectorDeriv z x * g x := by
  have h := ((integrable_mul_rpow_mul_trig hq (g := fun w => g (w + z.1)) (by fun_prop)
    fun w => hg1 _).comp_sub_right z.1).const_mul (-Real.sqrt z.2)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [poissonVectorDeriv, sub_add_cancel]
  ring

/-! ### The rigidity theorem -/

/-- **Rigidity of the Whittaker moments of finitely many points.** -/
theorem eq_zero_of_whittakerSum_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (z : ι → ℝ × ℝ) (hq : ∀ i, 0 < (z i).2)
    (hdist : ∀ i j, i ≠ j → (z i).2 = (z j).2 → ∀ k : ℤ, (z i).1 - (z j).1 ≠ k) (n₀ : ℕ)
    (hsum : ∀ n, n₀ ≤ n → ∑ i, (a i : ℂ) * (Real.sqrt (z i).2 *
      kMoment 0 (2 * Real.pi * n * (z i).2) : ℝ) * twoPiExp (n * (z i).1) = 0) :
    ∀ i, a i = 0 := by
  by_contra hne
  push Not at hne
  set S : Finset ι := Finset.univ.filter fun i => a i ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne; exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i₁, hi₁S, hmin⟩ := S.exists_min_image (fun i => (z i).2) hSne
  set q₁ := (z i₁).2 with hq₁
  set T : Finset ι := S.filter fun i => (z i).2 = q₁ with hT
  have hi₁T : i₁ ∈ T := Finset.mem_filter.mpr ⟨hi₁S, rfl⟩
  -- the bottom exponential sum tends to zero
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ T, (a i : ℂ) * twoPiExp (n * (z i).1)) atTop (𝓝 0) := by
    set R : ℕ → ℂ := fun n => ∑ i ∈ S \ T, (a i : ℂ) * ((Real.sqrt (z i).2 / Real.sqrt q₁ *
      (kMoment 0 (2 * Real.pi * n * (z i).2) / kMoment 0 (2 * Real.pi * n * q₁))) : ℝ) *
        twoPiExp (n * (z i).1) with hR
    have hRlim : Tendsto R atTop (𝓝 0) := by
      have hterm : ∀ i ∈ S \ T, Tendsto (fun n : ℕ => (a i : ℂ) * ((Real.sqrt (z i).2 /
          Real.sqrt q₁ * (kMoment 0 (2 * Real.pi * n * (z i).2) /
            kMoment 0 (2 * Real.pi * n * q₁))) : ℝ) * twoPiExp (n * (z i).1)) atTop (𝓝 0) := by
        intro i hi
        have hiS : i ∈ S := (Finset.mem_sdiff.mp hi).1
        have hiT : i ∉ T := (Finset.mem_sdiff.mp hi).2
        have hgt : q₁ < (z i).2 := by
          rcases lt_or_eq_of_le (hmin i hiS) with h | h
          · exact h
          · exact absurd (by simp [hT, hiS, h.symm]) hiT
        refine squeeze_zero_norm' (a := fun n : ℕ => |a i| * (Real.sqrt (z i).2 / Real.sqrt q₁) *
          Real.exp (-(2 * Real.pi * (z i).2 - 2 * Real.pi * q₁) * n)) ?_ ?_
        · filter_upwards [eventually_gt_atTop 0] with n hn
          rw [norm_mul, norm_mul, norm_twoPiExp, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
          · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
            have hq1 : 0 < q₁ := hq i₁
            have hr₁ : 0 < 2 * Real.pi * n * q₁ := by positivity
            have hle : 2 * Real.pi * n * q₁ ≤ 2 * Real.pi * n * (z i).2 := by
              have := Real.pi_pos; nlinarith
            have hK := kMoment_le_exp_mul 0 hr₁ hle
            have hK0 : 0 < kMoment 0 (2 * Real.pi * n * q₁) := kMoment_zero_pos_of_pos hr₁
            have hK1 := kMoment_nonneg 0 (2 * Real.pi * n * (z i).2)
            rw [abs_of_nonneg (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
              (div_nonneg hK1 hK0.le))]
            have hratio : kMoment 0 (2 * Real.pi * n * (z i).2) / kMoment 0 (2 * Real.pi * n * q₁) ≤
                Real.exp (-(2 * Real.pi * (z i).2 - 2 * Real.pi * q₁) * n) := by
              rw [div_le_iff₀ hK0]
              calc kMoment 0 (2 * Real.pi * n * (z i).2)
                  ≤ Real.exp (-(2 * Real.pi * n * (z i).2 - 2 * Real.pi * n * q₁)) *
                      kMoment 0 (2 * Real.pi * n * q₁) := hK
                _ = Real.exp (-(2 * Real.pi * (z i).2 - 2 * Real.pi * q₁) * n) *
                      kMoment 0 (2 * Real.pi * n * q₁) := by congr 2; ring
            have hr0 : 0 ≤ Real.sqrt (z i).2 / Real.sqrt q₁ :=
              div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
            calc |a i| * (Real.sqrt (z i).2 / Real.sqrt q₁ *
                  (kMoment 0 (2 * Real.pi * n * (z i).2) / kMoment 0 (2 * Real.pi * n * q₁)))
                ≤ |a i| * (Real.sqrt (z i).2 / Real.sqrt q₁ *
                    Real.exp (-(2 * Real.pi * (z i).2 - 2 * Real.pi * q₁) * n)) := by gcongr
              _ = _ := by ring
        · have hc : 0 < 2 * Real.pi * (z i).2 - 2 * Real.pi * q₁ := by
            have := Real.pi_pos; nlinarith
          have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
            (tendsto_natCast_atTop_atTop.const_mul_atTop hc)).const_mul
              (|a i| * (Real.sqrt (z i).2 / Real.sqrt q₁))
          rw [mul_zero] at h
          refine h.congr fun n => ?_
          simp only [Function.comp_apply]
          congr 2; ring
      have := tendsto_finsetSum (S \ T) hterm
      simpa [hR] using this
    refine (hRlim.neg).congr' ?_ |>.trans (by rw [neg_zero])
    filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
    have hn₀ : n₀ ≤ n := le_of_max_le_left hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (le_of_max_le_right hn))
    have hq1 : 0 < q₁ := hq i₁
    have hK0 : 0 < kMoment 0 (2 * Real.pi * n * q₁) := kMoment_zero_pos_of_pos (by positivity)
    have hs1 : 0 < Real.sqrt q₁ := Real.sqrt_pos.mpr hq1
    have hfull := hsum n hn₀
    -- restrict to `S` and split `S = T ∪ (S \ T)`
    have hS0 : ∑ i, (a i : ℂ) * (Real.sqrt (z i).2 * kMoment 0 (2 * Real.pi * n * (z i).2) : ℝ) *
        twoPiExp (n * (z i).1) = ∑ i ∈ S, (a i : ℂ) * (Real.sqrt (z i).2 *
          kMoment 0 (2 * Real.pi * n * (z i).2) : ℝ) * twoPiExp (n * (z i).1) := by
      rw [hS, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by split_ifs with h <;> simp_all
    rw [hS0, ← Finset.sum_sdiff (show T ⊆ S from Finset.filter_subset _ _)] at hfull
    have hTsum : ∑ i ∈ T, (a i : ℂ) * (Real.sqrt (z i).2 * kMoment 0 (2 * Real.pi * n * (z i).2) : ℝ) *
        twoPiExp (n * (z i).1) = ((Real.sqrt q₁ * kMoment 0 (2 * Real.pi * n * q₁) : ℝ) : ℂ) *
          ∑ i ∈ T, (a i : ℂ) * twoPiExp (n * (z i).1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : (z i).2 = q₁ := (Finset.mem_filter.mp hi).2
      rw [this]; ring
    have hRsum : ∑ i ∈ S \ T, (a i : ℂ) * (Real.sqrt (z i).2 *
        kMoment 0 (2 * Real.pi * n * (z i).2) : ℝ) * twoPiExp (n * (z i).1) =
        ((Real.sqrt q₁ * kMoment 0 (2 * Real.pi * n * q₁) : ℝ) : ℂ) * R n := by
      rw [hR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : ((Real.sqrt q₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs1.ne'
      have h2 : ((kMoment 0 (2 * Real.pi * n * q₁) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
      push_cast
      field_simp
    rw [hTsum, hRsum] at hfull
    have hc : ((Real.sqrt q₁ * kMoment 0 (2 * Real.pi * n * q₁) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos hs1 hK0).ne'
    have := mul_left_cancel₀ hc (by linear_combination hfull :
      ((Real.sqrt q₁ * kMoment 0 (2 * Real.pi * n * q₁) : ℝ) : ℂ) * R n =
        ((Real.sqrt q₁ * kMoment 0 (2 * Real.pi * n * q₁) : ℝ) : ℂ) *
          -∑ i ∈ T, (a i : ℂ) * twoPiExp (n * (z i).1))
    rw [this, neg_neg]
  have hTdist : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ k : ℤ, (z i).1 - (z j).1 ≠ k := by
    intro i hi j hj hij k
    have h1 : (z i).2 = q₁ := (Finset.mem_filter.mp hi).2
    have h2 : (z j).2 = q₁ := (Finset.mem_filter.mp hj).2
    exact hdist i j hij (h1.trans h2.symm) k
  have h0 := eq_zero_of_natExpSum_tendsto_zero (fun i => (z i).1) T (fun i => (a i : ℂ)) hTdist
    hlim i₁ hi₁T
  have : a i₁ ≠ 0 := (Finset.mem_filter.mp hi₁S).2
  exact this (by exact_mod_cast h0)

/-- **No finite Poisson superposition is blind at all large integers.** If
`h = Σ a_i φ_{z_i}` (points pairwise not related by an integer translation) has
`∫ h'(x) sin(2π(n+1)x) dx = ∫ h'(x) cos(2π(n+1)x) dx = 0` for all `n ≥ n₀`, then all `a_i = 0`. -/
theorem eq_zero_of_finitePoisson_blind {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ)
    (z : ι → ℝ × ℝ) (hq : ∀ i, 0 < (z i).2)
    (hdist : ∀ i j, i ≠ j → (z i).2 = (z j).2 → ∀ k : ℤ, (z i).1 - (z j).1 ≠ k) (n₀ : ℕ)
    (hblind : ∀ n, n₀ ≤ n →
      ∫ x, (∑ i, a i * poissonVectorDeriv (z i) x) * Real.sin (arcFreq n * x) = 0 ∧
      ∫ x, (∑ i, a i * poissonVectorDeriv (z i) x) * Real.cos (arcFreq n * x) = 0) :
    ∀ i, a i = 0 := by
  -- work with frequencies `2π m`, `m = n + 1 ≥ n₀ + 1`
  refine eq_zero_of_whittakerSum_eq_zero a z hq hdist (n₀ + 1) fun m hm => ?_
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : n₀ ≤ n := by omega
  obtain ⟨hs, hc⟩ := hblind n hn
  have hpos := arcFreq_pos n
  set c := arcFreq n with hcdef
  have hint : ∀ (g : ℝ → ℝ), Continuous g → (∀ x, |g x| ≤ 1) → ∀ i,
      Integrable fun x => a i * poissonVectorDeriv (z i) x * g x := fun g hg hg1 i => by
    simpa [mul_assoc] using (integrable_poissonVectorDeriv_mul_trig (hq i) hg hg1).const_mul (a i)
  have hmom : ∀ (g : ℝ → ℝ), Continuous g → (∀ x, |g x| ≤ 1) →
      ∫ x, (∑ i, a i * poissonVectorDeriv (z i) x) * g x =
        ∑ i, a i * ∫ x, poissonVectorDeriv (z i) x * g x := fun g hg hg1 => by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ fun i _ => hint g hg hg1 i]
    exact Finset.sum_congr rfl fun i _ => by simp_rw [mul_assoc]; rw [integral_const_mul]
  rw [hmom _ (by fun_prop) (fun x => Real.abs_sin_le_one _)] at hs
  rw [hmom _ (by fun_prop) (fun x => Real.abs_cos_le_one _)] at hc
  simp_rw [integral_poissonVectorDeriv_mul_sin (hq _) hpos] at hs
  simp_rw [integral_poissonVectorDeriv_mul_cos (hq _) hpos] at hc
  have hA : ∑ i, a i * (Real.sqrt (z i).2 * kMoment 0 (c * (z i).2)) * Real.cos (c * (z i).1) = 0 := by
    have h2 : -(2 * c) ≠ 0 := by have := hpos; intro h; linarith
    have : -(2 * c) * ∑ i, a i * (Real.sqrt (z i).2 * kMoment 0 (c * (z i).2)) *
        Real.cos (c * (z i).1) = 0 := by
      rw [← hs, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    exact (mul_eq_zero.mp this).resolve_left h2
  have hB : ∑ i, a i * (Real.sqrt (z i).2 * kMoment 0 (c * (z i).2)) * Real.sin (c * (z i).1) = 0 := by
    have h2 : 2 * c ≠ 0 := by positivity
    have : 2 * c * ∑ i, a i * (Real.sqrt (z i).2 * kMoment 0 (c * (z i).2)) *
        Real.sin (c * (z i).1) = 0 := by
      rw [← hc, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    exact (mul_eq_zero.mp this).resolve_left h2
  have hfreq : ∀ x : ℝ, 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x = c * x := by
    intro x; rw [hcdef]; unfold arcFreq; push_cast; ring
  have hterm : ∀ i, (a i : ℂ) * ((Real.sqrt (z i).2 *
      kMoment 0 (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * (z i).2) : ℝ) : ℂ) *
        twoPiExp (((n + 1 : ℕ) : ℝ) * (z i).1) =
      ((a i * (Real.sqrt (z i).2 * kMoment 0 (c * (z i).2)) * Real.cos (c * (z i).1) : ℝ) : ℂ) +
      ((a i * (Real.sqrt (z i).2 * kMoment 0 (c * (z i).2)) * Real.sin (c * (z i).1) : ℝ) : ℂ) *
        Complex.I := by
    intro i
    have hph : 2 * Real.pi * Complex.I * ((((n + 1 : ℕ) : ℝ) * (z i).1 : ℝ) : ℂ) =
        ((c * (z i).1 : ℝ) : ℂ) * Complex.I := by
      rw [← hfreq]; push_cast; ring
    rw [hfreq, twoPiExp, hph, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Complex.ofReal_sum, ← Complex.ofReal_sum, hA, hB]
  simp

end

end RHTower
