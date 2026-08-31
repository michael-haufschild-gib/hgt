import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBounded

/-!
# Matomäki--Teräväinen Lemma 3.4

This is the literal one-line form of Heath--Brown's sparse mean-value estimate used in the paper.
Sparse coefficients are arbitrary complex numbers of modulus at most one, dense coefficients are
arbitrary real numbers, both reciprocal weights are retained, and the finite coefficient maximum
is constructed internally.  No sign, nonemptiness, height-two, or analytic premise remains.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- Sparse Dirichlet factor on the one-line. -/
def heathBrownSparseOneLineFactor
    (A : Finset PNat) (eps : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ A, eps (m : ℕ) * ((((1 / ((m : ℕ) : ℝ)) : ℝ)) : ℂ) *
    heathBrownDirichletPhase m t

/-- Dense real-coefficient Dirichlet factor on the one-line. -/
def heathBrownDenseOneLineFactor
    (B : Finset PNat) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ B, (((a (n : ℕ) / ((n : ℕ) : ℝ) : ℝ)) : ℂ) *
    heathBrownDirichletPhase n t

theorem continuous_heathBrownSparseOneLineFactor (A : Finset PNat) (eps : ℕ → ℂ) :
    Continuous (heathBrownSparseOneLineFactor A eps) := by
  unfold heathBrownSparseOneLineFactor
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  unfold heathBrownDirichletPhase
  fun_prop

theorem continuous_heathBrownDenseOneLineFactor (B : Finset PNat) (a : ℕ → ℝ) :
    Continuous (heathBrownDenseOneLineFactor B a) := by
  unfold heathBrownDenseOneLineFactor
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  unfold heathBrownDirichletPhase
  fun_prop

/-- Canonical totalized maximum of the absolute dense coefficients. -/
def heathBrownDenseCoefficientMax (B : Finset PNat) (a : ℕ → ℝ) : ℝ :=
  if hB : B.Nonempty then B.sup' hB fun n => |a (n : ℕ)| else 0

theorem heathBrownDenseCoefficientMax_nonneg (B : Finset PNat) (a : ℕ → ℝ) :
    0 ≤ heathBrownDenseCoefficientMax B a := by
  classical
  rw [heathBrownDenseCoefficientMax]
  split
  next hB =>
    obtain ⟨n, hn⟩ := hB
    exact (abs_nonneg (a (n : ℕ))).trans
      (Finset.le_sup' (s := B) (f := fun m : PNat => |a (m : ℕ)|) hn)
  next => exact le_rfl

theorem abs_le_heathBrownDenseCoefficientMax
    (B : Finset PNat) (a : ℕ → ℝ) {n : PNat} (hn : n ∈ B) :
    |a (n : ℕ)| ≤ heathBrownDenseCoefficientMax B a := by
  classical
  have hB : B.Nonempty := ⟨n, hn⟩
  rw [heathBrownDenseCoefficientMax, dif_pos hB]
  exact Finset.le_sup' (s := B) (f := fun m : PNat => |a (m : ℕ)|) hn

/-- Total projection of a real number to `[0,1]`. -/
def heathBrownUnitIntervalClip (x : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨min 1 (max 0 x),
    le_min (by norm_num) (le_max_left 0 x),
    min_le_left 1 (max 0 x)⟩

@[simp] theorem coe_heathBrownUnitIntervalClip_of_mem
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (heathBrownUnitIntervalClip x : ℝ) = x := by
  change min 1 (max 0 x) = x
  rw [max_eq_right hx0, min_eq_right hx1]

/-- Explicit constant for the nonnegative-coefficient one-line estimate. -/
def heathBrownLemma34PositiveCoefficient (eta : ℝ) : ℝ :=
  (25 * Real.pi / 4) *
    (4 * (95 * Real.pi / 2) +
      (2 : ℝ) ^ (eta + 1) * heathBrownTheoremFourCoefficient eta)

/-- Explicit constant in the signed real-coefficient Lemma 3.4. -/
def heathBrownLemma34Coefficient (eta : ℝ) : ℝ :=
  4 * heathBrownLemma34PositiveCoefficient eta

private theorem heathBrownLemma34_scalar
    {K M N T R eta : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hT : 0 < T) (hR : 0 ≤ R) :
    (K / (M * N)) ^ 2 * ((25 * Real.pi / 4) *
      (95 * Real.pi / 2 * (2 * N) ^ 2 * R ^ 2 +
        heathBrownTheoremFourCoefficient eta * ((2 * N * T) ^ eta) *
          (2 * N * R * T + 2 * N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)))) ≤
      heathBrownLemma34PositiveCoefficient eta * K ^ 2 *
        ((R / M) ^ 2 + ((N * T) ^ eta) *
          (R * T / (M ^ 2 * N) +
            R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) / (M ^ 2 * N))) := by
  let d : ℝ := (R / M) ^ 2
  let o : ℝ := ((N * T) ^ eta) *
    (R * T / (M ^ 2 * N) +
      R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) / (M ^ 2 * N))
  let u : ℝ := 4 * (95 * Real.pi / 2)
  let v : ℝ := (2 : ℝ) ^ (eta + 1) * heathBrownTheoremFourCoefficient eta
  have hC : 0 ≤ heathBrownTheoremFourCoefficient eta := by
    dsimp [heathBrownTheoremFourCoefficient,
      heathBrownTheoremFourUniversalCoefficient, heathBrownMeanSquareCoefficient]
    positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have ho : 0 ≤ o := by dsimp only [o]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have huv : u * d + v * o ≤ (u + v) * (d + o) := by
    nlinarith [mul_nonneg hu ho, mul_nonneg hv hd]
  have hrpow : (2 * N * T) ^ eta = (2 : ℝ) ^ eta * (N * T) ^ eta := by
    rw [show 2 * N * T = (2 : ℝ) * (N * T) by ring,
      Real.mul_rpow (by norm_num) (mul_nonneg hN.le hT.le)]
  have heq :
      (K / (M * N)) ^ 2 * ((25 * Real.pi / 4) *
        (95 * Real.pi / 2 * (2 * N) ^ 2 * R ^ 2 +
          heathBrownTheoremFourCoefficient eta * ((2 * N * T) ^ eta) *
            (2 * N * R * T + 2 * N * R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ)))) =
        (25 * Real.pi / 4) * K ^ 2 * (u * d + v * o) := by
    rw [hrpow]
    dsimp only [u, v, d, o]
    rw [show (2 : ℝ) ^ (eta + 1) = (2 : ℝ) ^ eta * 2 by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]]
    field_simp [ne_of_gt hM, ne_of_gt hN]
    ring
  rw [heq]
  dsimp only [heathBrownLemma34PositiveCoefficient]
  calc
    (25 * Real.pi / 4) * K ^ 2 * (u * d + v * o) ≤
        (25 * Real.pi / 4) * K ^ 2 * ((u + v) * (d + o)) :=
      mul_le_mul_of_nonneg_left huv (mul_nonneg (by positivity) (sq_nonneg K))
    _ = (25 * Real.pi / 4) * (u + v) * K ^ 2 * (d + o) := by ring

private theorem integral_heathBrown_oneLine_nonnegative_le
    (A B : Finset PNat) (eps : ℕ → ℂ) (a : ℕ → ℝ)
    {M : ℝ} (hM : 1 ≤ M)
    (hAM : ∀ m ∈ A, M ≤ ((m : ℕ) : ℝ))
    (heps : ∀ m ∈ A, ‖eps (m : ℕ)‖ ≤ 1)
    (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    (hAT : ∀ m ∈ A, ((m : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hN : 2 ≤ N)
    (hBN : ∀ n ∈ B, N < (n : ℕ))
    (hB2N : ∀ n ∈ B, (n : ℕ) ≤ 2 * N)
    {K : ℝ} (hK : 0 < K)
    (ha0 : ∀ n ∈ B, 0 ≤ a (n : ℕ))
    (haK : ∀ n ∈ B, a (n : ℕ) ≤ K)
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseOneLineFactor A eps t *
          heathBrownDenseOneLineFactor B a t‖ ^ 2) ≤
      heathBrownLemma34PositiveCoefficient eta * K ^ 2 *
        (((A.card : ℝ) / M) ^ 2 + (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((A.card : ℝ) * (T : ℝ) / (M ^ 2 * (N : ℝ)) +
            (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              (M ^ 2 * (N : ℝ)))) := by
  let c : ℕ → ℂ := fun m => eps m * (((M / (m : ℝ) : ℝ)) : ℂ)
  let q : ℕ → Set.Icc (0 : ℝ) 1 := fun n =>
    heathBrownUnitIntervalClip ((a n / K) * ((N : ℝ) / (n : ℝ)))
  have hc : ∀ m ∈ A, ‖c (m : ℕ)‖ ≤ 1 := by
    intro m hm
    have hmpos : (0 : ℝ) < (m : ℕ) := by positivity
    have hratio0 : 0 ≤ M / ((m : ℕ) : ℝ) := div_nonneg (by linarith) hmpos.le
    have hratio1 : M / ((m : ℕ) : ℝ) ≤ 1 := (div_le_one hmpos).mpr (hAM m hm)
    dsimp only [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hratio0]
    exact (mul_le_mul_of_nonneg_right (heps m hm) hratio0).trans (by simpa using hratio1)
  have hq : ∀ n ∈ B, (q (n : ℕ) : ℝ) =
      (a (n : ℕ) / K) * ((N : ℝ) / ((n : ℕ) : ℝ)) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
    have hfirst0 : 0 ≤ a (n : ℕ) / K := div_nonneg (ha0 n hn) hK.le
    have hfirst1 : a (n : ℕ) / K ≤ 1 := (div_le_one hK).mpr (haK n hn)
    have hsecond0 : 0 ≤ (N : ℝ) / ((n : ℕ) : ℝ) := by positivity
    have hsecond1 : (N : ℝ) / ((n : ℕ) : ℝ) ≤ 1 := by
      apply (div_le_one hnpos).mpr
      exact_mod_cast (hBN n hn).le
    apply coe_heathBrownUnitIntervalClip_of_mem
    · exact mul_nonneg hfirst0 hsecond0
    · exact (mul_le_mul_of_nonneg_right hfirst1 hsecond0).trans (by simpa using hsecond1)
  have hsparse : ∀ t : ℝ, heathBrownBoundedSparseFactor A c t =
      ((M : ℂ)) * heathBrownSparseOneLineFactor A eps t := by
    intro t
    rw [heathBrownBoundedSparseFactor, heathBrownSparseOneLineFactor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    dsimp only [c]
    push_cast
    rw [div_eq_mul_inv, one_div]
    ring
  have hdense : ∀ t : ℝ, heathBrownDenseFactor B q t =
      ((((N : ℝ) / K : ℝ)) : ℂ) * heathBrownDenseOneLineFactor B a t := by
    intro t
    rw [heathBrownDenseFactor, heathBrownDenseOneLineFactor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hq n hn]
    push_cast
    ring
  have hpoint : ∀ t : ℝ,
      ‖heathBrownSparseOneLineFactor A eps t *
          heathBrownDenseOneLineFactor B a t‖ ^ 2 =
        (K / (M * (N : ℝ))) ^ 2 *
          ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2 := by
    intro t
    have hnormM : ‖((M : ℝ) : ℂ)‖ = M := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < M)]
    have hnormNK : ‖((((N : ℝ) / K : ℝ)) : ℂ)‖ = (N : ℝ) / K := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos (by positivity) hK)]
    rw [hsparse t, hdense t]
    simp only [norm_mul, hnormM, hnormNK]
    field_simp [ne_of_gt (by linarith : 0 < M), ne_of_gt hK,
      ne_of_gt (show (0 : ℝ) < N by positivity)]
  have hint :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseOneLineFactor A eps t *
            heathBrownDenseOneLineFactor B a t‖ ^ 2) =
        (K / (M * (N : ℝ))) ^ 2 *
          ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
            ‖heathBrownBoundedSparseFactor A c t * heathBrownDenseFactor B q t‖ ^ 2 := by
    simp_rw [hpoint]
    exact MeasureTheory.integral_const_mul _ _
  have hgen := integral_Icc_normSq_heathBrownBounded_factors_le_theoremFour
    A B c q T hT hAT hc (N := 2 * N) (by omega) hB2N heta
  have hscalar := heathBrownLemma34_scalar (K := K) (M := M) (N := (N : ℝ))
    (T := (T : ℝ)) (R := (A.card : ℝ)) (eta := eta) (by linarith) (by positivity)
    T.property (by positivity)
  rw [hint]
  exact (mul_le_mul_of_nonneg_left hgen (sq_nonneg _)).trans
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscalar)

private theorem max_pos_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith)]
    simp
  · rw [max_eq_right hx, max_eq_left (by linarith)]
    simp

/-- Matomäki--Teräväinen Lemma 3.4, exact one-line form with an explicit constant.  Every
hypothesis is one of the published support, height, dyadic-range, or coefficient conditions. -/
theorem integral_Icc_normSq_heathBrown_oneLine_le_lemma34
    (A B : Finset PNat) (eps : ℕ → ℂ) (a : ℕ → ℝ)
    {M : ℝ} (hM : 1 ≤ M)
    (hAM : ∀ m ∈ A, M ≤ ((m : ℕ) : ℝ))
    (heps : ∀ m ∈ A, ‖eps (m : ℕ)‖ ≤ 1)
    (T : Set.Ioi (0 : ℝ)) (hMT : M ≤ (T : ℝ))
    (hAT : ∀ m ∈ A, ((m : ℕ) : ℝ) ≤ (T : ℝ))
    {N : ℕ} (hN : 2 ≤ N)
    (hBN : ∀ n ∈ B, N < (n : ℕ))
    (hB2N : ∀ n ∈ B, (n : ℕ) ≤ 2 * N)
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseOneLineFactor A eps t *
          heathBrownDenseOneLineFactor B a t‖ ^ 2) ≤
      heathBrownLemma34Coefficient eta *
        (heathBrownDenseCoefficientMax B a) ^ 2 *
        (((A.card : ℝ) / M) ^ 2 + (((N : ℝ) * (T : ℝ)) ^ eta) *
          ((A.card : ℝ) * (T : ℝ) / (M ^ 2 * (N : ℝ)) +
            (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
              (M ^ 2 * (N : ℝ)))) := by
  let K : ℝ := heathBrownDenseCoefficientMax B a
  have hK0 : 0 ≤ K := heathBrownDenseCoefficientMax_nonneg B a
  by_cases hKzero : K = 0
  · have ha : ∀ n ∈ B, a (n : ℕ) = 0 := by
      intro n hn
      have habs := abs_le_heathBrownDenseCoefficientMax B a hn
      rw [show heathBrownDenseCoefficientMax B a = K by rfl, hKzero] at habs
      exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
    have hdense : ∀ t : ℝ, heathBrownDenseOneLineFactor B a t = 0 := by
      intro t
      rw [heathBrownDenseOneLineFactor]
      apply Finset.sum_eq_zero
      intro n hn
      rw [ha n hn]
      simp
    simp only [hdense, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      integral_zero, K, hKzero]
    simp
  · have hK : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hKzero)
    let ap : ℕ → ℝ := fun n => max (a n) 0
    let am : ℕ → ℝ := fun n => max (-a n) 0
    have hap0 : ∀ n ∈ B, 0 ≤ ap (n : ℕ) := fun n hn => by
      dsimp only [ap]
      exact le_max_right _ _
    have ham0 : ∀ n ∈ B, 0 ≤ am (n : ℕ) := fun n hn => by
      dsimp only [am]
      exact le_max_right _ _
    have hapK : ∀ n ∈ B, ap (n : ℕ) ≤ K := by
      intro n hn
      have habs := abs_le_heathBrownDenseCoefficientMax B a hn
      change |a (n : ℕ)| ≤ K at habs
      dsimp only [ap]
      rw [max_le_iff]
      exact ⟨(le_abs_self _).trans habs, hK.le⟩
    have hamK : ∀ n ∈ B, am (n : ℕ) ≤ K := by
      intro n hn
      have habs := abs_le_heathBrownDenseCoefficientMax B a hn
      change |a (n : ℕ)| ≤ K at habs
      dsimp only [am]
      rw [max_le_iff]
      exact ⟨(neg_le_abs _).trans habs, hK.le⟩
    have hTone : 1 ≤ (T : ℝ) := hM.trans hMT
    let R : ℝ := heathBrownLemma34PositiveCoefficient eta * K ^ 2 *
      (((A.card : ℝ) / M) ^ 2 + (((N : ℝ) * (T : ℝ)) ^ eta) *
        ((A.card : ℝ) * (T : ℝ) / (M ^ 2 * (N : ℝ)) +
          (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
            (M ^ 2 * (N : ℝ))))
    have hp := integral_heathBrown_oneLine_nonnegative_le A B eps ap hM hAM heps T hTone
      hAT hN hBN hB2N hK hap0 hapK heta
    have hm := integral_heathBrown_oneLine_nonnegative_le A B eps am hM hAM heps T hTone
      hAT hN hBN hB2N hK ham0 hamK heta
    have hpR :
        (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
            ‖heathBrownSparseOneLineFactor A eps t *
              heathBrownDenseOneLineFactor B ap t‖ ^ 2) ≤ R := by
      simpa only [R] using hp
    have hmR :
        (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
            ‖heathBrownSparseOneLineFactor A eps t *
              heathBrownDenseOneLineFactor B am t‖ ^ 2) ≤ R := by
      simpa only [R] using hm
    have hdense : ∀ t : ℝ, heathBrownDenseOneLineFactor B a t =
        heathBrownDenseOneLineFactor B ap t - heathBrownDenseOneLineFactor B am t := by
      intro t
      rw [heathBrownDenseOneLineFactor, heathBrownDenseOneLineFactor,
        heathBrownDenseOneLineFactor, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      have haid : ap (n : ℕ) - am (n : ℕ) = a (n : ℕ) := by
        dsimp only [ap, am]
        exact max_pos_sub_max_neg _
      rw [← haid]
      push_cast
      ring
    let fp : ℝ → ℝ := fun t =>
      ‖heathBrownSparseOneLineFactor A eps t *
        heathBrownDenseOneLineFactor B ap t‖ ^ 2
    let fm : ℝ → ℝ := fun t =>
      ‖heathBrownSparseOneLineFactor A eps t *
        heathBrownDenseOneLineFactor B am t‖ ^ 2
    let f : ℝ → ℝ := fun t =>
      ‖heathBrownSparseOneLineFactor A eps t *
        heathBrownDenseOneLineFactor B a t‖ ^ 2
    have hfp : Continuous fp :=
      ((continuous_heathBrownSparseOneLineFactor A eps).mul
        (continuous_heathBrownDenseOneLineFactor B ap)).norm.pow 2
    have hfm : Continuous fm :=
      ((continuous_heathBrownSparseOneLineFactor A eps).mul
        (continuous_heathBrownDenseOneLineFactor B am)).norm.pow 2
    have hf : Continuous f :=
      ((continuous_heathBrownSparseOneLineFactor A eps).mul
        (continuous_heathBrownDenseOneLineFactor B a)).norm.pow 2
    have hpoint : ∀ t : ℝ, f t ≤ 2 * fp t + 2 * fm t := by
      intro t
      have htri :
          ‖heathBrownSparseOneLineFactor A eps t *
              heathBrownDenseOneLineFactor B a t‖ ≤
            ‖heathBrownSparseOneLineFactor A eps t *
              heathBrownDenseOneLineFactor B ap t‖ +
            ‖heathBrownSparseOneLineFactor A eps t *
              heathBrownDenseOneLineFactor B am t‖ := by
        rw [hdense t, mul_sub]
        exact norm_sub_le _ _
      have hx0 : 0 ≤ ‖heathBrownSparseOneLineFactor A eps t *
          heathBrownDenseOneLineFactor B ap t‖ := norm_nonneg _
      have hy0 : 0 ≤ ‖heathBrownSparseOneLineFactor A eps t *
          heathBrownDenseOneLineFactor B am t‖ := norm_nonneg _
      have hz0 : 0 ≤ ‖heathBrownSparseOneLineFactor A eps t *
          heathBrownDenseOneLineFactor B a t‖ := norm_nonneg _
      dsimp only [f, fp, fm]
      nlinarith [sq_nonneg
        (‖heathBrownSparseOneLineFactor A eps t *
            heathBrownDenseOneLineFactor B ap t‖ -
          ‖heathBrownSparseOneLineFactor A eps t *
            heathBrownDenseOneLineFactor B am t‖)]
    have hint :
        (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), f t) ≤
          ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), (2 * fp t + 2 * fm t) :=
      MeasureTheory.integral_mono hf.integrableOn_Icc
        ((continuous_const.mul hfp).add (continuous_const.mul hfm)).integrableOn_Icc hpoint
    have hsum :
        (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), (2 * fp t + 2 * fm t)) =
          2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fp t) +
            2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fm t) := by
      have hadd :
          (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), (2 * fp t + 2 * fm t)) =
            (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), 2 * fp t) +
              ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), 2 * fm t := by
        exact MeasureTheory.integral_add
          ((continuous_const.mul hfp).integrableOn_Icc)
          ((continuous_const.mul hfm).integrableOn_Icc)
      have hp2 : (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), 2 * fp t) =
          2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fp t) := by
        exact MeasureTheory.integral_const_mul _ _
      have hm2 : (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), 2 * fm t) =
          2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fm t) := by
        exact MeasureTheory.integral_const_mul _ _
      rw [hadd, hp2, hm2]
    have hfour :
        2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fp t) +
            2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fm t) ≤ 4 * R := by
      linarith
    change (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), f t) ≤ _
    calc
      _ ≤ ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), (2 * fp t + 2 * fm t) := hint
      _ = 2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fp t) +
          2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), fm t) := hsum
      _ ≤ 4 * R := hfour
      _ = heathBrownLemma34Coefficient eta *
          (heathBrownDenseCoefficientMax B a) ^ 2 *
          (((A.card : ℝ) / M) ^ 2 + (((N : ℝ) * (T : ℝ)) ^ eta) *
            ((A.card : ℝ) * (T : ℝ) / (M ^ 2 * (N : ℝ)) +
              (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
                (M ^ 2 * (N : ℝ)))) := by
        dsimp only [R, K, heathBrownLemma34Coefficient]
        ring

end

end RHTower.Sieve
