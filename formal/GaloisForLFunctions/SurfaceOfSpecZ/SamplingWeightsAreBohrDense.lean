import GaloisForLFunctions.SurfaceOfSpecZ.BohrDenseSetsSampleEveryAttainedTop

/-!
# Sampling weights are Bohr-dense

The support of every sampling weight is Bohr-dense at `+∞`
(`isBohrDenseAtTop_of_samplingWeight`): the log-degrees `{log n : w(n) ≠ 0}` approximate every
finite family of phases beyond every bound. So the sampling theorems for attained tops (the primes,
a residue class, density-one sets of primes, two Frobenii) are instances of
`BohrDenseSetsSampleEveryAttainedTop`, and Bohr density is the common criterion.

**Proof.** If the support avoided, beyond `U`, the Bohr neighbourhood
`{u : |e^{iλu} − e^{iλv}| < η, λ ∈ S}`, the nonnegative trigonometric polynomial
`Q(t) = Π_{λ∈S} cos(λ(t − v)/2)^{2K}` would be `≤ (1 − η²/4)^K` on the support beyond `U`, so its
`w`-mean `Σ w(n) Q(log n) n^{−σ} / Σ w(n) n^{−σ}` is at most `(1 − η²/4)^K` in the limit `σ ↓ 1`. But
the twisted means of a sampling weight kill every nonzero frequency
(`tendsto_phaseForm_mean`), so the limit is the constant term of `Q`, which has nonnegative
coefficients and is at least `(C(2K, K)/4^K)^{|S|} ≥ (2K + 1)^{−|S|}` (`exists_phaseForm_prod`).
For `K` large this exceeds `(1 − η²/4)^K`.
-/

open Complex Filter Topology
open scoped ComplexConjugate Classical

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### Phase forms -/

/-- A phase form `Σ_i r_i e^{i f_i (t − v)}`. -/
def phaseForm {ι : Type} [Fintype ι] (r f : ι → ℝ) (v t : ℝ) : ℂ :=
  ∑ i, (r i : ℂ) * cexp (((f i * (t - v) : ℝ) : ℂ) * I)

/-- Its constant term `Σ_{f_i = 0} r_i`. -/
def phaseConst {ι : Type} [Fintype ι] (r f : ι → ℝ) : ℝ :=
  ∑ i, if f i = 0 then r i else 0

theorem phaseForm_mul {ι κ : Type} [Fintype ι] [Fintype κ] (r f : ι → ℝ) (s g : κ → ℝ)
    (v t : ℝ) :
    phaseForm r f v t * phaseForm s g v t =
      phaseForm (fun p : ι × κ => r p.1 * s p.2) (fun p => f p.1 + g p.2) v t := by
  unfold phaseForm
  rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [show (((f i + g k) * (t - v) : ℝ) : ℂ) * I =
      (((f i * (t - v) : ℝ) : ℂ) * I) + (((g k * (t - v) : ℝ) : ℂ) * I) by push_cast; ring,
    Complex.exp_add]
  push_cast; ring

theorem phaseConst_mul_le {ι κ : Type} [Fintype ι] [Fintype κ] {r f : ι → ℝ} {s g : κ → ℝ}
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ k, 0 ≤ s k) :
    phaseConst r f * phaseConst s g ≤
      phaseConst (fun p : ι × κ => r p.1 * s p.2) (fun p => f p.1 + g p.2) := by
  unfold phaseConst
  rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
  by_cases hf : f i = 0
  · by_cases hg : g k = 0
    · simp [hf, hg]
    · simp only [hf, hg, if_true, if_false, mul_zero]
      split_ifs <;> positivity
  · simp only [hf, if_false, zero_mul]
    split_ifs
    · exact mul_nonneg (hr i) (hs k)
    · exact le_refl _

/-! ### The binomial block -/

/-- `cos(θ/2)^{2K} = 4^{−K} Σ_j C(2K, j) e^{i(j − K)θ}`, `θ = λ(t − v)`. -/
theorem cos_pow_eq_phaseForm (K : ℕ) (lam v t : ℝ) :
    ((Real.cos (lam * (t - v) / 2) ^ (2 * K) : ℝ) : ℂ) =
      phaseForm (ι := Fin (2 * K + 1)) (fun j => (Nat.choose (2 * K) j : ℝ) / 4 ^ K)
        (fun j => ((j : ℝ) - K) * lam) v t := by
  set θ : ℝ := lam * (t - v) with hθ
  set a : ℂ := cexp (((θ / 2 : ℝ) : ℂ) * I)
  set b : ℂ := cexp (-(((θ / 2 : ℝ) : ℂ) * I))
  have hcos : ((Real.cos (θ / 2) : ℝ) : ℂ) = (a + b) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
    simp only [a, b]; ring_nf
  have hab : ∀ m : ℕ, m ≤ 2 * K → a ^ m * b ^ (2 * K - m) =
      cexp (((((m : ℝ) - K) * lam * (t - v)) : ℝ) * I) := by
    intro m hm
    simp only [a, b, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub hm]
    push_cast
    rw [hθ]; push_cast; ring
  rw [Complex.ofReal_pow, hcos, div_pow, add_pow]
  unfold phaseForm
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ 2 * K := Nat.lt_succ_iff.mp j.2
  rw [hab j hj]
  have h4 : ((2 : ℂ)) ^ (2 * K) = (4 : ℂ) ^ K := by rw [pow_mul]; norm_num
  rw [h4]
  push_cast
  ring_nf

/-- The product `Q_S(t) = Π_{λ∈S} cos(λ(t − v)/2)^{2K}` is a phase form with nonnegative
coefficients and constant term at least `(2K + 1)^{−|S|}`. -/
theorem exists_phaseForm_prod (K : ℕ) (v : ℝ) (S : Finset ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (r f : ι → ℝ), (∀ i, 0 ≤ r i) ∧
      (1 / (2 * (K : ℝ) + 1)) ^ S.card ≤ phaseConst r f ∧
      ∀ t, ((∏ lam ∈ S, Real.cos (lam * (t - v) / 2) ^ (2 * K) : ℝ) : ℂ) = phaseForm r f v t := by
  refine Finset.induction_on S ?_ ?_
  · refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ => zero_le_one, ?_, fun t => ?_⟩
    · simp [phaseConst]
    · simp [phaseForm]
  · intro lam S hlam ih
    obtain ⟨ι, hι, r, f, hr, hc, hQ⟩ := ih
    set r₀ : Fin (2 * K + 1) → ℝ := fun j => (Nat.choose (2 * K) j : ℝ) / 4 ^ K
    set f₀ : Fin (2 * K + 1) → ℝ := fun j => ((j : ℝ) - K) * lam
    have hr₀ : ∀ j, 0 ≤ r₀ j := fun j => by positivity
    have hc₀ : 1 / (2 * (K : ℝ) + 1) ≤ phaseConst r₀ f₀ := by
      unfold phaseConst
      have hK : (⟨K, by omega⟩ : Fin (2 * K + 1)) ∈ Finset.univ := Finset.mem_univ _
      have hle := Finset.single_le_sum (f := fun j : Fin (2 * K + 1) =>
        if f₀ j = 0 then r₀ j else 0) (fun j _ => by split_ifs <;> positivity) hK
      have hf0 : f₀ ⟨K, by omega⟩ = 0 := by simp [f₀]
      simp only [hf0, if_true] at hle
      refine le_trans ?_ hle
      simp only [r₀]
      have hcb := Nat.four_pow_le_two_mul_add_one_mul_central_binom K
      have hcb' : (4 : ℝ) ^ K ≤ (2 * K + 1) * (Nat.choose (2 * K) K : ℝ) := by
        exact_mod_cast hcb
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      simp only [Nat.centralBinom_eq_two_mul_choose] at hcb'
      linarith
    refine ⟨Fin (2 * K + 1) × ι, inferInstance, fun p => r₀ p.1 * r p.2, fun p => f₀ p.1 + f p.2,
      fun p => mul_nonneg (hr₀ p.1) (hr p.2), ?_, fun t => ?_⟩
    · rw [Finset.card_insert_of_notMem hlam, pow_succ']
      refine le_trans ?_ (phaseConst_mul_le hr₀ hr)
      exact mul_le_mul hc₀ hc (by positivity) (by
        unfold phaseConst; exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity)
    · rw [Finset.prod_insert hlam, Complex.ofReal_mul, hQ t, cos_pow_eq_phaseForm, phaseForm_mul]

/-! ### Twisted means of a sampling weight -/

/-- **The `w`-means of a phase form tend to its constant term.** -/
theorem tendsto_phaseForm_mean {w : ℕ → ℝ} (hw : SamplingWeight w) {ι : Type} [Fintype ι]
    (r f : ι → ℝ) (v : ℝ) :
    Tendsto (fun σ : ℝ => (∑' j : ℕ, (w j : ℂ) * phaseForm r f v (Real.log (j + 1)) *
        ((((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)) / (wSum w σ : ℂ)) (𝓝[>] 1)
      (𝓝 (phaseConst r f : ℂ)) := by
  -- rewrite as a finite combination of twisted series
  have hkey : ∀ σ : ℝ, 1 < σ → (∑' j : ℕ, (w j : ℂ) * phaseForm r f v (Real.log (j + 1)) *
      ((((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)) =
        ∑ i, (r i : ℂ) * cexp (((-(f i * v) : ℝ) : ℂ) * I) *
          wSeries w ((σ : ℂ) + (-(f i : ℂ) * I)) := by
    intro σ hσ
    have hterm : ∀ i, Summable fun j : ℕ => (w j : ℂ) * ((r i : ℂ) *
        cexp (((f i * (Real.log (j + 1) - v) : ℝ) : ℂ) * I)) * ((((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
      intro i
      refine Summable.of_norm_bounded ((hw.summable hσ).mul_left |r i|) fun j => ?_
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hw.nonneg j), abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ (-σ))]
      nlinarith [abs_nonneg (r i), hw.nonneg j, (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ (-σ))]
    have e1 : (fun j : ℕ => (w j : ℂ) * phaseForm r f v (Real.log (j + 1)) *
        ((((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ)) = fun j => ∑ i, (w j : ℂ) * ((r i : ℂ) *
          cexp (((f i * (Real.log (j + 1) - v) : ℝ) : ℂ) * I)) * ((((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
      funext j; unfold phaseForm; rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1, Summable.tsum_finsetSum fun i _ => hterm i]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold wSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    have htw := cpow_twist j σ (f i)
    rw [show (σ : ℂ) + (-(f i : ℂ) * I) = (σ : ℂ) - (f i : ℂ) * I by ring, htw]
    rw [show (((f i * (Real.log (j + 1) - v) : ℝ) : ℂ) * I) =
        (((-(f i * v) : ℝ) : ℂ) * I) + ((f i : ℂ) * (Real.log (j + 1) : ℝ) * I) by push_cast; ring,
      Complex.exp_add]
    push_cast; ring
  -- each twisted ratio tends to the indicator of `f_i = 0`
  have hlim : Tendsto (fun σ : ℝ => ∑ i, (r i : ℂ) * cexp (((-(f i * v) : ℝ) : ℂ) * I) *
      (wSeries w ((σ : ℂ) + (-(f i : ℂ) * I)) / (wSum w σ : ℂ))) (𝓝[>] 1)
        (𝓝 (∑ i, (r i : ℂ) * cexp (((-(f i * v) : ℝ) : ℂ) * I) * (if f i = 0 then 1 else 0))) := by
    refine tendsto_finset_sum _ fun i _ => (Tendsto.const_mul _ ?_)
    by_cases hf : f i = 0
    · rw [if_pos hf]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hw.eventually_pos] with σ hσ
      rw [hf, Complex.ofReal_zero, neg_zero, zero_mul, add_zero, ← ofReal_wSum,
        div_self (by exact_mod_cast hσ.ne')]
    · rw [if_neg hf]
      refine hw.tendsto_off _ ?_ (by simp)
      intro h
      have := congrArg Complex.im h
      simp at this
      exact hf this
  have hconst : (∑ i, (r i : ℂ) * cexp (((-(f i * v) : ℝ) : ℂ) * I) * (if f i = 0 then 1 else 0)) =
      (phaseConst r f : ℂ) := by
    unfold phaseConst
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hf : f i = 0
    · simp [hf]
    · simp [hf]
  rw [← hconst]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [hkey σ hσ, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The theorem -/

/-- The supports of `w` as log-degrees. -/
def logSupport (w : ℕ → ℝ) : Set ℝ := {u | ∃ j : ℕ, w j ≠ 0 ∧ u = Real.log (j + 1)}

theorem norm_bohrExp_sub (lam u v : ℝ) :
    ‖bohrExp lam u - bohrExp lam v‖ = 2 * |Real.sin (lam * (u - v) / 2)| := by
  rw [bohrExp_apply, bohrExp_apply]
  have e : cexp (((lam * u : ℝ) : ℂ) * I) - cexp (((lam * v : ℝ) : ℂ) * I) =
      cexp (((lam * v : ℝ) : ℂ) * I) * (cexp (((lam * (u - v) : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  set θ := lam * (u - v)
  have h := Complex.norm_exp_I_mul_ofReal_sub_one θ
  rw [mul_comm] at h
  rw [h]

/-- **Sampling weights are Bohr-dense.** -/
theorem isBohrDenseAtTop_of_samplingWeight {w : ℕ → ℝ} (hw : SamplingWeight w) :
    IsBohrDenseAtTop (logSupport w) := by
  intro S v η U hη
  by_contra hno
  push Not at hno
  -- some `K` with `(1 − η²/4)^K < (2K + 1)^{−|S|}`
  set θ₀ : ℝ := 1 - min (η ^ 2 / 4) (1 / 2) with hθ₀
  have hθ₀0 : 0 < θ₀ := by have := min_le_right (η ^ 2 / 4) (1 / 2); linarith
  have hθ₀1 : θ₀ < 1 := by
    have : 0 < min (η ^ 2 / 4) (1 / 2) := lt_min (by positivity) (by norm_num)
    linarith
  have hlimK : Tendsto (fun K : ℕ => ((2 * (K : ℝ) + 1) ^ S.card) * θ₀ ^ K) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one S.card
      (by rw [abs_of_pos hθ₀0]; exact hθ₀1)
    have h2 : Tendsto (fun K : ℕ => (3 : ℝ) ^ S.card * ((K : ℝ) ^ S.card * θ₀ ^ K)) atTop (𝓝 0) := by
      simpa using h1.const_mul ((3 : ℝ) ^ S.card)
    refine squeeze_zero' (Eventually.of_forall fun K => by positivity) ?_ h2
    filter_upwards [eventually_ge_atTop 1] with K hK
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have : (2 * (K : ℝ) + 1) ^ S.card ≤ (3 : ℝ) ^ S.card * (K : ℝ) ^ S.card := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
    nlinarith [pow_pos hθ₀0 K]
  obtain ⟨K, hK⟩ := (hlimK.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  have hKlt : θ₀ ^ K < (1 / (2 * (K : ℝ) + 1)) ^ S.card := by
    rw [one_div_pow, lt_div_iff₀ (by positivity)]; linarith
  -- the polynomial `Q`
  obtain ⟨ι, hι, r, f, hr, hc, hQ⟩ := exists_phaseForm_prod K v S
  set Q : ℝ → ℝ := fun t => ∏ lam ∈ S, Real.cos (lam * (t - v) / 2) ^ (2 * K) with hQdef
  have hQ0 : ∀ t, 0 ≤ Q t := fun t => Finset.prod_nonneg fun lam _ => by
    rw [pow_mul]; positivity
  have hQ1 : ∀ t, Q t ≤ 1 := fun t => Finset.prod_le_one (fun lam _ => by rw [pow_mul]; positivity)
    fun lam _ => by
      rw [pow_mul]
      exact pow_le_one₀ (by positivity) (by nlinarith [Real.cos_sq_le_one (lam * (t - v) / 2)])
  have hQsmall : ∀ u ∈ logSupport w, U ≤ u → Q u ≤ θ₀ ^ K := by
    intro u hu hUu
    obtain ⟨lam, hlam, hfar⟩ := hno u hu hUu
    rw [norm_bohrExp_sub] at hfar
    have hsin : η ^ 2 / 4 ≤ Real.sin (lam * (u - v) / 2) ^ 2 := by
      have h := mul_self_le_mul_self hη.le (hfar.trans (le_refl _))
      rw [← sq_abs (Real.sin _)]; nlinarith [abs_nonneg (Real.sin (lam * (u - v) / 2))]
    have hcos : Real.cos (lam * (u - v) / 2) ^ 2 ≤ θ₀ := by
      have := Real.sin_sq_add_cos_sq (lam * (u - v) / 2)
      have := min_le_left (η ^ 2 / 4) (1 / 2)
      rw [hθ₀]; linarith
    calc Q u = Real.cos (lam * (u - v) / 2) ^ (2 * K) *
          ∏ mu ∈ S.erase lam, Real.cos (mu * (u - v) / 2) ^ (2 * K) := by
            rw [hQdef, ← Finset.mul_prod_erase S _ hlam]
      _ ≤ θ₀ ^ K * 1 := by
          refine mul_le_mul ?_ (Finset.prod_le_one (fun mu _ => by rw [pow_mul]; positivity)
            fun mu _ => by
              rw [pow_mul]
              exact pow_le_one₀ (by positivity) (by nlinarith [Real.cos_sq_le_one (mu * (u - v) / 2)]))
            (Finset.prod_nonneg fun mu _ => by rw [pow_mul]; positivity) hθ₀0.le.trans' ?_
          · rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hcos K
          · positivity
      _ = θ₀ ^ K := mul_one _
  -- the finite part below `U`
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ j : ℕ, N₀ ≤ j → U ≤ Real.log (j + 1) := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (Real.exp U)
    refine ⟨N₀, fun j hj => ?_⟩
    rw [← Real.log_exp U]
    exact Real.log_le_log (Real.exp_pos _) (by
      have : (N₀ : ℝ) ≤ j := by exact_mod_cast hj
      linarith)
  set C₀ : ℝ := ∑ j ∈ Finset.range N₀, w j with hC₀
  -- the `w`-mean of `Q`
  set Nσ : ℝ → ℝ := fun σ => ∑' j : ℕ, w j * Q (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) with hNσ
  have hcomplex : ∀ σ : ℝ, 1 < σ → ((Nσ σ : ℝ) : ℂ) = ∑' j : ℕ, (w j : ℂ) *
      phaseForm r f v (Real.log (j + 1)) * ((((j : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    intro σ hσ
    rw [hNσ]; simp only []
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun j => ?_
    rw [← hQ, Complex.ofReal_mul, Complex.ofReal_mul]
  have hmean := tendsto_phaseForm_mean hw r f v
  have hreal : Tendsto (fun σ : ℝ => Nσ σ / wSum w σ) (𝓝[>] 1) (𝓝 (phaseConst r f)) := by
    have h := (Complex.continuous_re.tendsto _).comp hmean
    simp only [Complex.ofReal_re] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Function.comp_def]
    rw [← hcomplex σ hσ, ← Complex.ofReal_div, Complex.ofReal_re]
  -- the upper bound `Nσ ≤ C₀ + θ₀^K wSum`
  have hupper : ∀ σ : ℝ, 1 < σ → Nσ σ ≤ C₀ + θ₀ ^ K * wSum w σ := by
    intro σ hσ
    have hs := hw.summable hσ
    have hsN : Summable fun j : ℕ => w j * Q (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) :=
      Summable.of_nonneg_of_le (fun j => mul_nonneg (mul_nonneg (hw.nonneg j) (hQ0 _))
        (by positivity)) (fun j => by
          have := hQ1 (Real.log (j + 1))
          have h0 : 0 ≤ w j * ((j : ℝ) + 1) ^ (-σ) := mul_nonneg (hw.nonneg j) (by positivity)
          nlinarith [hQ0 (Real.log (j + 1))]) hs
    have hbound : ∀ j : ℕ, w j * Q (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) ≤
        (if j < N₀ then w j else 0) + θ₀ ^ K * (w j * ((j : ℝ) + 1) ^ (-σ)) := by
      intro j
      have hp : 0 ≤ ((j : ℝ) + 1) ^ (-σ) := by positivity
      have hp1 : ((j : ℝ) + 1) ^ (-σ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) j])
          (by linarith)
      have hθK : 0 ≤ θ₀ ^ K := by positivity
      have hwj := hw.nonneg j
      split_ifs with hj
      · have h1 := hQ1 (Real.log (j + 1))
        have h2 : w j * Q (Real.log (j + 1)) ≤ w j := by nlinarith [hQ0 (Real.log (j + 1))]
        have h3 : w j * Q (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) ≤ w j * 1 :=
          mul_le_mul h2 hp1 hp hwj
        nlinarith
      · by_cases hw0 : w j = 0
        · rw [hw0]; simp
        · have hmem : Real.log (j + 1) ∈ logSupport w := ⟨j, hw0, rfl⟩
          have h1 := hQsmall _ hmem (hN₀ j (not_lt.mp hj))
          have : w j * Q (Real.log (j + 1)) * ((j : ℝ) + 1) ^ (-σ) ≤
              w j * θ₀ ^ K * ((j : ℝ) + 1) ^ (-σ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hwj) hp
          linarith [show w j * θ₀ ^ K * ((j : ℝ) + 1) ^ (-σ) =
            θ₀ ^ K * (w j * ((j : ℝ) + 1) ^ (-σ)) by ring]
    have hsumF : Summable fun j : ℕ => (if j < N₀ then w j else 0) :=
      summable_of_ne_finset_zero (s := Finset.range N₀) fun j hj => by
        rw [Finset.mem_range] at hj; simp [hj]
    calc Nσ σ ≤ ∑' j : ℕ, ((if j < N₀ then w j else 0) +
          θ₀ ^ K * (w j * ((j : ℝ) + 1) ^ (-σ))) :=
        Summable.tsum_le_tsum hbound hsN (hsumF.add (hs.mul_left _))
      _ = C₀ + θ₀ ^ K * wSum w σ := by
        rw [hsumF.tsum_add (hs.mul_left _), tsum_mul_left, wSum, hC₀,
          tsum_eq_sum (s := Finset.range N₀) (fun j hj => by
            rw [Finset.mem_range] at hj; simp [hj])]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj; simp [hj]
  -- the limit of `C₀/wSum + θ₀^K` is `θ₀^K`
  have hlimR : Tendsto (fun σ : ℝ => C₀ / wSum w σ + θ₀ ^ K) (𝓝[>] 1) (𝓝 (0 + θ₀ ^ K)) :=
    (hw.tendsto_atTop.const_div_atTop' C₀ |>.add tendsto_const_nhds)
  have hle : phaseConst r f ≤ 0 + θ₀ ^ K := by
    refine le_of_tendsto_of_tendsto hreal hlimR ?_
    filter_upwards [self_mem_nhdsWithin, hw.eventually_pos] with σ hσ hpos
    rw [div_le_iff₀ hpos]
    have := hupper σ hσ
    have e : (C₀ / wSum w σ + θ₀ ^ K) * wSum w σ = C₀ + θ₀ ^ K * wSum w σ := by
      field_simp
    rw [e]; exact this
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
