import GaloisForLFunctions.ArithmeticInnerFunctionTheory.InverseScatteringWithPrimeData

/-!
# The forward map from primes to reflectors

How do the reflectors depend on the primes past the first echo? The Weil sequence is affine in each prime weight, and the margins and Schur parameters are
minima of quadratic forms over the interior of the window. So the envelope theorem computes the tangent of the forward map exactly, at every stage.

* **First variation of the margin** (`hasDerivAt_levinsonErr`). Along `κ + tη`, `∂E_n = T^η(v_n)`, with `v_n = (1, a^{(n)})` the Levinson vector.
* **First variation of the Schur parameter** (`hasDerivAt_schurParam`, `hasDerivAt_reflCoeff`). With `w_± = (1, a ± Ja, ±1)`, `∂β_n = (T^η(w₊) − T^η(w₋))/4`, and `∂γ_n = (∂β_n − γ_n∂E_n)/E_n`.
* **The margin is concave** (`levinsonErr_le_add`). `E_n(κ + η) ≤ E_n(κ) + T^η(v_n)`, whenever both windows are positive: the admissible prime weights are cut out by a concave function.
* **The prime response** (`hasDerivAt_levinsonErr_weight`, `toeplitzForm_primeEcho`). A prime power `n₀` moves the margin of stage `n` by

  `∂E_n/∂λ(n₀) = −(2/√n₀) A_n(log n₀)`,

  with `A_n` the autocorrelation of the predictor test `X_n = Σ_k v_{n,k} φ(· + kh)`. So past the first echo a prime is read through the autocorrelation of the whole predictor at its own logarithm: reflectors depend on primes
  through the predictor, and this is the nonlinearity of the forward map.
-/

open Finset Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GrowingWindowsOfSpecZ ArithmeticCastelnuovoSeveri

noncomputable section

/-! ### Affine lines of sequences -/

/-- The line `κ + tη`. -/
def tiltSeq (κ η : ℤ → ℝ) (t : ℝ) (d : ℤ) : ℝ := κ d + t * η d

variable {κ η : ℤ → ℝ}

theorem tiltSeq_isEven (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) (t : ℝ) : IsEvenSeq (tiltSeq κ η t) :=
  fun d => by simp only [tiltSeq, hκ d, hη d]

theorem tiltSeq_zero (κ η : ℤ → ℝ) : tiltSeq κ η 0 = κ := by
  funext d
  simp [tiltSeq]

theorem toeplitzForm_tiltSeq (κ η : ℤ → ℝ) (t : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    toeplitzForm (tiltSeq κ η t) n x = toeplitzForm κ n x + t * toeplitzForm η n x := by
  simp only [toeplitzForm, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [tiltSeq]
  ring

/-- Continuity of the Levinson evolution along a line, while the margins do not vanish. -/
theorem continuousAt_levinson (κ η : ℤ → ℝ) :
    ∀ n : ℕ, (∀ k < n, levinsonErr κ k ≠ 0) →
      ContinuousAt (fun t => levinsonErr (tiltSeq κ η t) n) 0 ∧
        ∀ k : Fin n, ContinuousAt (fun t => levinsonPred (tiltSeq κ η t) n k) 0
  | 0, _ => by
    refine ⟨?_, fun k => k.elim0⟩
    simp only [levinsonErr_zero, tiltSeq]
    fun_prop
  | n + 1, h => by
    obtain ⟨hE, hP⟩ := continuousAt_levinson κ η n fun k hk => h k (by omega)
    have hne : levinsonErr (tiltSeq κ η 0) n ≠ 0 := by
      rw [tiltSeq_zero]
      exact h n (by omega)
    have hd : ∀ d : ℤ, ContinuousAt (fun t => tiltSeq κ η t d) 0 := fun d => by
      simp only [tiltSeq]
      fun_prop
    have hβ : ContinuousAt (fun t => schurParam (tiltSeq κ η t) n) 0 := by
      simp only [schurParam, schurCoupling]
      refine (hd _).add (tendsto_finset_sum _ fun k _ => (hd _).mul (hP _))
    have hγ : ContinuousAt (fun t => reflCoeff (tiltSeq κ η t) n) 0 := hβ.div hE hne
    refine ⟨?_, fun k => ?_⟩
    · simp only [levinsonErr_succ]
      exact hE.sub ((hβ.pow 2).div hE hne)
    · simp only [levinsonPred_succ]
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp only [Fin.snoc_last]
        exact hγ.neg
      · simp only [Fin.snoc_castSucc]
        exact (hP k).sub (hγ.mul (hP _))

/-- **The envelope sandwich.** -/
theorem hasDerivAt_of_sandwich {m b : ℝ → ℝ} (hb : ContinuousAt b 0)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), t * b t ≤ m t - m 0 ∧ m t - m 0 ≤ t * b 0) : HasDerivAt m (b 0) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), |b t - b 0| < c :=
    (Metric.continuousAt_iff'.mp hb c hc).mono fun t ht => by rwa [Real.dist_eq] at ht
  filter_upwards [h, h1] with t ht ht1
  simp only [zero_add, smul_eq_mul, Real.norm_eq_abs]
  have e : t * b t - t * b 0 = t * (b t - b 0) := by ring
  have h2 : |t * (b t - b 0)| ≤ c * |t| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ht1.le (abs_nonneg _)
  have h3 := abs_le.mp h2
  rw [abs_le]
  constructor <;> nlinarith [ht.1, ht.2, abs_nonneg t]

/-- The margin minimizes the form over vectors with first coordinate `1`. -/
theorem levinsonErr_le_toeplitzForm (hκ : IsEvenSeq κ) {n : ℕ} (h : ToeplitzPosDef κ (n + 1))
    (x : Fin n → ℝ) : levinsonErr κ n ≤ toeplitzForm κ (n + 1) (Fin.cons 1 x) := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk.le).ne'
  have ha := levinson_isPredictor hκ hne
  have hpd : ToeplitzPosDef κ n := ((posDef_succ_iff hκ ha).mp h).1
  rw [toeplitzForm_cons hκ ha, predErr_levinson hκ hne, one_pow, mul_one]
  have hT : 0 ≤ toeplitzForm κ n fun k => x k - 1 * levinsonPred κ n k := by
    by_cases h0 : (fun k => x k - 1 * levinsonPred κ n k) = 0
    · rw [h0]
      simp [toeplitzForm]
    · exact (hpd _ h0).le
  linarith

/-- **The margin is concave.** -/
theorem levinsonErr_le_add (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) {n : ℕ} (t : ℝ)
    (h : ToeplitzPosDef κ (n + 1)) (ht : ToeplitzPosDef (tiltSeq κ η t) (n + 1)) :
    levinsonErr (tiltSeq κ η t) n ≤ levinsonErr κ n + t * toeplitzForm η (n + 1) (levinsonVec κ n) := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk.le).ne'
  have h1 := levinsonErr_le_toeplitzForm (tiltSeq_isEven hκ hη t) ht (levinsonPred κ n)
  rw [toeplitzForm_tiltSeq, toeplitzForm_levinsonVec hκ hne] at h1
  exact h1

/-- Nearby windows stay positive definite. -/
theorem eventually_posDef (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) {n : ℕ} (h : ToeplitzPosDef κ (n + 1)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ToeplitzPosDef (tiltSeq κ η t) (n + 1) := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hk : ∀ k ∈ Finset.range (n + 1), ∀ᶠ t in 𝓝 (0 : ℝ), 0 < levinsonErr (tiltSeq κ η t) k := by
    intro k hk'
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')
    have hc := (continuousAt_levinson κ η k fun j hj => (hlow j (by omega)).ne').1
    have h0 : 0 < levinsonErr (tiltSeq κ η 0) k := by
      rw [tiltSeq_zero]
      exact hlow k hkn
    exact hc.eventually (lt_mem_nhds h0)
  filter_upwards [(Finset.eventually_all _).mpr hk] with t ht
  refine (toeplitzForm_posDef_iff (tiltSeq_isEven hκ hη t) n).mpr fun k hk' => ?_
  exact ht k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk'))

/-- Continuity of a Toeplitz form along a continuous vector. -/
theorem continuousAt_toeplitzForm (η : ℤ → ℝ) {n : ℕ} {v : ℝ → Fin n → ℝ}
    (hv : ∀ i, ContinuousAt (fun t => v t i) 0) :
    ContinuousAt (fun t => toeplitzForm η n (v t)) 0 := by
  simp only [toeplitzForm]
  exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
    ((continuousAt_const.mul (hv i)).mul (hv j))

/-- **The first variation of the margin.** -/
theorem hasDerivAt_levinsonErr (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) {n : ℕ}
    (h : ToeplitzPosDef κ (n + 1)) :
    HasDerivAt (fun t => levinsonErr (tiltSeq κ η t) n)
      (toeplitzForm η (n + 1) (levinsonVec κ n)) 0 := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk.le).ne'
  have hP := (continuousAt_levinson κ η n hne).2
  have hvec : ∀ i, ContinuousAt (fun t => levinsonVec (tiltSeq κ η t) n i) 0 := fun i => by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [levinsonVec, Fin.cons_zero]
      exact continuousAt_const
    · simp only [levinsonVec, Fin.cons_succ]
      exact hP k
  have hb := continuousAt_toeplitzForm η hvec
  have hsand := hasDerivAt_of_sandwich (m := fun t => levinsonErr (tiltSeq κ η t) n)
    (b := fun t => toeplitzForm η (n + 1) (levinsonVec (tiltSeq κ η t) n)) hb ?_
  · simpa only [tiltSeq_zero] using hsand
  · filter_upwards [eventually_posDef hκ hη h] with t ht
    simp only [tiltSeq_zero]
    have hlowt := (toeplitzForm_posDef_iff (tiltSeq_isEven hκ hη t) n).mp ht
    have hnet : ∀ k < n, levinsonErr (tiltSeq κ η t) k ≠ 0 := fun k hk => (hlowt k hk.le).ne'
    constructor
    · -- the minimum at `0` tested on the minimizer at `t`
      have h1 := levinsonErr_le_toeplitzForm hκ h (levinsonPred (tiltSeq κ η t) n)
      have h2 := toeplitzForm_levinsonVec (tiltSeq_isEven hκ hη t) hnet
      rw [toeplitzForm_tiltSeq] at h2
      change _ * toeplitzForm η (n + 1) (Fin.cons 1 (levinsonPred (tiltSeq κ η t) n)) ≤ _
      linarith
    · have h3 := levinsonErr_le_add hκ hη t h ht
      linarith

/-! ### The Schur parameter -/

/-- The minimizer with collars `(1, ε)`: `w_ε = (1, a + εJa, ε)`. -/
def collarVec (κ : ℤ → ℝ) (n : ℕ) (ε : ℝ) : Fin (n + 2) → ℝ :=
  Fin.cons 1 (Fin.snoc (fun k => levinsonPred κ n k + ε * levinsonPred κ n (Fin.rev k)) ε)

/-- The value of the form on the minimizer. -/
theorem toeplitzForm_collarVec (hκ : IsEvenSeq κ) {n : ℕ} (h : ToeplitzPosDef κ (n + 1)) (ε : ℝ) :
    toeplitzForm κ (n + 2) (collarVec κ n ε) =
      levinsonErr κ n + 2 * schurParam κ n * ε + levinsonErr κ n * ε ^ 2 := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk.le).ne'
  have ha := levinson_isPredictor hκ hne
  have hE := predErr_levinson hκ hne
  have hE0 : predErr κ n (levinsonPred κ n) ≠ 0 := by
    rw [hE]
    exact (hlow n le_rfl).ne'
  rw [collarVec, toeplitzForm_two_collar hκ ha hE0, hE]
  have hz : toeplitzForm κ n (fun k => levinsonPred κ n k + ε * levinsonPred κ n (Fin.rev k) -
      1 * levinsonPred κ n k - ε * levinsonPred κ n (Fin.rev k)) = 0 := by
    have : (fun k => levinsonPred κ n k + ε * levinsonPred κ n (Fin.rev k) -
        1 * levinsonPred κ n k - ε * levinsonPred κ n (Fin.rev k)) = fun _ => 0 := by
      funext k
      ring
    rw [this]
    simp [toeplitzForm]
  rw [hz, schurParam]
  ring

/-- The collar form is a minimum over the interior. -/
theorem collar_le (hκ : IsEvenSeq κ) {n : ℕ} (h : ToeplitzPosDef κ (n + 1)) (ε : ℝ) (x : Fin n → ℝ) :
    levinsonErr κ n + 2 * schurParam κ n * ε + levinsonErr κ n * ε ^ 2 ≤
      toeplitzForm κ (n + 2) (Fin.cons 1 (Fin.snoc x ε)) := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk.le).ne'
  have ha := levinson_isPredictor hκ hne
  have hE := predErr_levinson hκ hne
  have hE0 : predErr κ n (levinsonPred κ n) ≠ 0 := by
    rw [hE]
    exact (hlow n le_rfl).ne'
  have hpd : ToeplitzPosDef κ n := ((posDef_succ_iff hκ ha).mp h).1
  have hint : ∀ z : Fin n → ℝ, 0 ≤ toeplitzForm κ n z := fun z => by
    by_cases h0 : z = 0
    · rw [h0]
      simp [toeplitzForm]
    · exact (hpd z h0).le
  have hl := (twoCollar_isLeast hκ ha hE0 hint 1 ε).2 ⟨x, rfl⟩
  rw [hE] at hl
  simp only [schurParam] at *
  linarith

/-- The collar value along the line. -/
def collarValue (κ : ℤ → ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  levinsonErr κ n + 2 * schurParam κ n * ε + levinsonErr κ n * ε ^ 2

/-- **The first variation of the collar value.** -/
theorem hasDerivAt_collarValue (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) {n : ℕ}
    (h : ToeplitzPosDef κ (n + 1)) (ε : ℝ) :
    HasDerivAt (fun t => collarValue (tiltSeq κ η t) n ε)
      (toeplitzForm η (n + 2) (collarVec κ n ε)) 0 := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hne : ∀ k < n, levinsonErr κ k ≠ 0 := fun k hk => (hlow k hk.le).ne'
  have hP := (continuousAt_levinson κ η n hne).2
  have hvec : ∀ i, ContinuousAt (fun t => collarVec (tiltSeq κ η t) n ε i) 0 := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [collarVec, Fin.cons_zero]
      exact continuousAt_const
    · refine Fin.lastCases ?_ (fun k => ?_) i
      · simp only [collarVec, Fin.cons_succ, Fin.snoc_last]
        exact continuousAt_const
      · simp only [collarVec, Fin.cons_succ, Fin.snoc_castSucc]
        exact (hP k).add (continuousAt_const.mul (hP _))
  have hb := continuousAt_toeplitzForm η hvec
  have hsand := hasDerivAt_of_sandwich (m := fun t => collarValue (tiltSeq κ η t) n ε)
    (b := fun t => toeplitzForm η (n + 2) (collarVec (tiltSeq κ η t) n ε)) hb ?_
  · simpa only [tiltSeq_zero] using hsand
  · filter_upwards [eventually_posDef hκ hη h] with t ht
    simp only [tiltSeq_zero]
    have h1 : collarValue κ n ε ≤ toeplitzForm κ (n + 2) (collarVec (tiltSeq κ η t) n ε) :=
      collar_le hκ h ε _
    have h2 : toeplitzForm (tiltSeq κ η t) (n + 2) (collarVec (tiltSeq κ η t) n ε) =
        collarValue (tiltSeq κ η t) n ε := toeplitzForm_collarVec (tiltSeq_isEven hκ hη t) ht ε
    have h3 : collarValue (tiltSeq κ η t) n ε ≤ toeplitzForm (tiltSeq κ η t) (n + 2) (collarVec κ n ε) :=
      collar_le (tiltSeq_isEven hκ hη t) ht ε _
    have h4 : toeplitzForm κ (n + 2) (collarVec κ n ε) = collarValue κ n ε :=
      toeplitzForm_collarVec hκ h ε
    rw [toeplitzForm_tiltSeq] at h2 h3
    constructor <;> linarith

/-- **The first variation of the Schur parameter.** `∂β_n = (T^η(w₊) − T^η(w₋))/4`. -/
theorem hasDerivAt_schurParam (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) {n : ℕ}
    (h : ToeplitzPosDef κ (n + 1)) :
    HasDerivAt (fun t => schurParam (tiltSeq κ η t) n)
      ((toeplitzForm η (n + 2) (collarVec κ n 1) - toeplitzForm η (n + 2) (collarVec κ n (-1))) / 4) 0 := by
  have h1 := hasDerivAt_collarValue hκ hη h 1
  have h2 := hasDerivAt_collarValue hκ hη h (-1)
  refine ((h1.fun_sub h2).div_const 4).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only [collarValue]
  ring

/-- **The first variation of a reflector.** `∂γ_n = (∂β_n − γ_n∂E_n)/E_n`. -/
theorem hasDerivAt_reflCoeff (hκ : IsEvenSeq κ) (hη : IsEvenSeq η) {n : ℕ}
    (h : ToeplitzPosDef κ (n + 1)) :
    HasDerivAt (fun t => reflCoeff (tiltSeq κ η t) n)
      (((toeplitzForm η (n + 2) (collarVec κ n 1) - toeplitzForm η (n + 2) (collarVec κ n (-1))) / 4 -
        reflCoeff κ n * toeplitzForm η (n + 1) (levinsonVec κ n)) / levinsonErr κ n) 0 := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hE0 := (hlow n le_rfl).ne'
  have hb := hasDerivAt_schurParam hκ hη h
  have hE := hasDerivAt_levinsonErr hκ hη h
  have hdiv := hb.fun_div hE (by rw [tiltSeq_zero]; exact hE0)
  simp only [tiltSeq_zero] at hdiv
  refine hdiv.congr_deriv ?_
  rw [reflCoeff]
  field_simp

/-! ### The prime response -/

variable {φ : ℝ → ℝ} {h r : ℝ}

/-- The echo of the prime power `n₀` at step `h`: the direction of the weight `λ(n₀)` in the sequence. -/
def primeEcho (φ : ℝ → ℝ) (h : ℝ) (n₀ : ℕ) (d : ℤ) : ℝ :=
  -(1 / Real.sqrt n₀) * (latticeLag φ h d (Real.log n₀) + latticeLag φ h d (-Real.log n₀))

/-- The Weil sequence is affine in each prime weight. -/
theorem weilSeqW_update (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (lam : ℕ → ℝ) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (t : ℝ) :
    weilSeqW (Function.update lam n₀ (lam n₀ + t)) φ h = tiltSeq (weilSeqW lam φ h) (primeEcho φ h n₀) t := by
  funext d
  have hk := weilSeqW_single_kick (h := h) (d := d) hφ (lam := Function.update lam n₀ (lam n₀ + t)) (lam' := lam) hn₀
    (fun m hm => by rw [Function.update_of_ne hm])
  rw [Function.update_self] at hk
  simp only [tiltSeq, primeEcho]
  have e : -((lam n₀ + t - lam n₀) / Real.sqrt n₀) = t * -(1 / Real.sqrt n₀) := by ring
  rw [e] at hk
  linarith

theorem primeEcho_isEven (φ : ℝ → ℝ) (h : ℝ) (n₀ : ℕ) (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hn₀ : 2 ≤ n₀) :
    IsEvenSeq (primeEcho φ h n₀) := by
  intro d
  have hk := fun d' => weilSeqW_single_kick (h := h) (d := d') hφ (lam := Function.update 0 n₀ 1) (lam' := 0) hn₀
    (fun m hm => by rw [Function.update_of_ne hm])
  have h1 := hk (-d)
  have h2 := hk d
  rw [weilSeqW_isEven (Function.update 0 n₀ 1) φ h d, weilSeqW_isEven 0 φ h d] at h1
  simp only [Function.update_self, Pi.zero_apply, sub_zero] at h1 h2
  simp only [primeEcho]
  have e : ∀ a b : ℝ, -(1 / Real.sqrt n₀) * (a + b) = -(1 / Real.sqrt n₀) * (a + b) := fun _ _ => rfl
  linarith

/-- **The prime response of a margin.** -/
theorem hasDerivAt_levinsonErr_weight (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (lam : ℕ → ℝ) {n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) {n : ℕ} (hpd : ToeplitzPosDef (weilSeqW lam φ h) (n + 1)) :
    HasDerivAt (fun t => levinsonErr (weilSeqW (Function.update lam n₀ (lam n₀ + t)) φ h) n)
      (toeplitzForm (primeEcho φ h n₀) (n + 1) (levinsonVec (weilSeqW lam φ h) n)) 0 := by
  simp only [weilSeqW_update hφ lam hn₀]
  exact hasDerivAt_levinsonErr (weilSeqW_isEven lam φ h) (primeEcho_isEven φ h n₀ hφ hn₀) hpd

/-- **The prime response of a reflector.** -/
theorem hasDerivAt_reflCoeff_weight (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (lam : ℕ → ℝ) {n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) {n : ℕ} (hpd : ToeplitzPosDef (weilSeqW lam φ h) (n + 1)) :
    HasDerivAt (fun t => reflCoeff (weilSeqW (Function.update lam n₀ (lam n₀ + t)) φ h) n)
      (((toeplitzForm (primeEcho φ h n₀) (n + 2) (collarVec (weilSeqW lam φ h) n 1) -
          toeplitzForm (primeEcho φ h n₀) (n + 2) (collarVec (weilSeqW lam φ h) n (-1))) / 4 -
        reflCoeff (weilSeqW lam φ h) n *
          toeplitzForm (primeEcho φ h n₀) (n + 1) (levinsonVec (weilSeqW lam φ h) n)) /
        levinsonErr (weilSeqW lam φ h) n) 0 := by
  simp only [weilSeqW_update hφ lam hn₀]
  exact hasDerivAt_reflCoeff (weilSeqW_isEven lam φ h) (primeEcho_isEven φ h n₀ hφ hn₀) hpd

/-- The autocorrelation of a test. -/
def autocorr (X : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u, X u * X (u - y)

/-- The lag in terms of two lattice sites. -/
theorem latticeLag_sub (φ : ℝ → ℝ) (h : ℝ) (i j : ℤ) (y : ℝ) :
    latticeLag φ h (i - j) y = ∫ u, φ (u + j * h) * φ (u + i * h - y) := by
  rw [latticeLag, ← integral_add_right_eq_self (fun u => φ u * φ (u - y + ((i - j : ℤ) : ℝ) * h)) ((j : ℝ) * h)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  congr 2
  push_cast
  ring

/-- **The Toeplitz form of a lag is the autocorrelation of the lattice test.** -/
theorem sum_latticeLag_eq_autocorr (hφ : φ ∈ realTests) (h : ℝ) {n : ℕ} (x : Fin n → ℝ) (y : ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, latticeLag φ h ((i : ℤ) - j) y * x i * x j =
      autocorr (latticeTest φ h x) y := by
  have hc : Continuous φ := ContDiff.continuous hφ.1
  have hcs : HasCompactSupport φ := hφ.2
  have hint : ∀ i j : Fin n, Integrable fun u : ℝ => φ (u + ((j : ℕ) : ℤ) * h) *
      φ (u + ((i : ℕ) : ℤ) * h - y) := fun i j => by
    have h1 : Continuous fun u : ℝ => φ (u + ((j : ℕ) : ℤ) * h) * φ (u + ((i : ℕ) : ℤ) * h - y) := by
      fun_prop
    refine h1.integrable_of_hasCompactSupport ?_
    have h2 : HasCompactSupport fun u : ℝ => φ (u + ((j : ℕ) : ℤ) * h) :=
      hcs.comp_homeomorph (Homeomorph.addRight (((j : ℕ) : ℤ) * h : ℝ))
    exact h2.mul_right
  simp only [autocorr, latticeTest_apply]
  have e : ∀ u : ℝ, (∑ k : Fin n, x k * φ (u + (k : ℕ) * h)) *
      ∑ k : Fin n, x k * φ (u - y + (k : ℕ) * h) = ∑ i : Fin n, ∑ j : Fin n,
        x i * x j * (φ (u + ((j : ℕ) : ℤ) * h) * φ (u + ((i : ℕ) : ℤ) * h - y)) := fun u => by
    rw [mul_comm, Finset.sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have e2 : u - y + ((i : ℕ) : ℝ) * h = u + (((i : ℕ) : ℤ) : ℝ) * h - y := by
      push_cast
      ring
    have e3 : u + ((j : ℕ) : ℝ) * h = u + (((j : ℕ) : ℤ) : ℝ) * h := by
      push_cast
      ring
    rw [e2, e3]
    ring
  simp only [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, latticeLag_sub]
  have e4 : (((i : ℕ) : ℤ) : ℝ) = ((i : ℕ) : ℤ) := rfl
  push_cast
  ring

/-- Autocorrelations are even. -/
theorem autocorr_neg (X : ℝ → ℝ) (y : ℝ) : autocorr X (-y) = autocorr X y := by
  rw [autocorr, autocorr, ← integral_add_right_eq_self (fun u => X u * X (u - y)) y]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [sub_neg_eq_add, add_sub_cancel_right]
  ring

/-- **The prime echo on a vector is the autocorrelation of its lattice test at `log n₀`.** -/
theorem toeplitzForm_primeEcho (hφ : φ ∈ realTests) (h : ℝ) (n₀ : ℕ) {n : ℕ} (x : Fin n → ℝ) :
    toeplitzForm (primeEcho φ h n₀) n x =
      -(2 / Real.sqrt n₀) * autocorr (latticeTest φ h x) (Real.log n₀) := by
  have e : toeplitzForm (primeEcho φ h n₀) n x = -(1 / Real.sqrt n₀) *
      (∑ i : Fin n, ∑ j : Fin n, latticeLag φ h ((i : ℤ) - j) (Real.log n₀) * x i * x j +
        ∑ i : Fin n, ∑ j : Fin n, latticeLag φ h ((i : ℤ) - j) (-Real.log n₀) * x i * x j) := by
    simp only [toeplitzForm, primeEcho, mul_add, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  rw [e, sum_latticeLag_eq_autocorr hφ, sum_latticeLag_eq_autocorr hφ, autocorr_neg]
  ring

/-- **The prime response in closed form.** `∂E_n/∂λ(n₀) = −(2/√n₀) A_n(log n₀)`, with `A_n` the autocorrelation of the predictor test. -/
theorem hasDerivAt_levinsonErr_autocorr (hφ₀ : φ ∈ realTests) (hφ : ∀ y, y ∉ Icc (-r) 0 → φ y = 0)
    (lam : ℕ → ℝ) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {n : ℕ} (hpd : ToeplitzPosDef (weilSeqW lam φ h) (n + 1)) :
    HasDerivAt (fun t => levinsonErr (weilSeqW (Function.update lam n₀ (lam n₀ + t)) φ h) n)
      (-(2 / Real.sqrt n₀) *
        autocorr (latticeTest φ h (levinsonVec (weilSeqW lam φ h) n)) (Real.log n₀)) 0 := by
  have h1 := hasDerivAt_levinsonErr_weight hφ lam hn₀ hpd
  rwa [toeplitzForm_primeEcho hφ₀] at h1

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
