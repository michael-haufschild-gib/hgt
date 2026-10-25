import GaloisForLFunctions.MultiplicativePositivityGeometry.GrowthToForcing

/-!
# The barrier of a certificate is the barrier of its fibre

A positive certificate is a nonnegative almost-periodic cosine polynomial
`P(t) = Σ_{i ∈ I} c_i cos(λ_i t)` with finitely many real frequencies. It may couple several
heights, several harmonics and several incommensurable channels. Its `ω`-fibre is the part made of
the modes whose frequency is an integer multiple of `ω`.

* **Bohr projection** (`fibre_projection_nonneg`). The fibre part of a nonnegative certificate is
  nonnegative. Average `P` along `t + k·2π/ω`: resonant modes are periodic in `k`, every other mode
  has bounded sums `|Σ_k cos| ≤ 1/|sin(πλ/ω)|`.
* **Exact barrier** (`fibre_purchase_le_fejer`). The fibre part is the cosine polynomial
  `Σ_{m ≤ K} b_m cos(mωt)` of the fibre degree `K`, with `b_m` the total weight on `± mω`
  (`fibrePart_eq_cosinePolynomial`). The exact Fejér barrier applies:
  `b₁ ≤ 2cos(π/(K+2)) b₀`. For frequencies in `[0, ∞)` this reads
  `c(ω) ≤ 2cos(π/(K+2)) c(0)` (`multiFrequency_purchase_le_fibre_fejer`), which sharpens the
  universal cap `c(ω) ≤ 2c(0)` to the barrier of the fibre. Every spectrum containing
  `0, ω, …, Kω` attains it (`fibre_barrier_attained`).
* **Independent channels.** For `ℚ`-independent frequencies `γ_j` and spectrum
  `⟨k, γ⟩ = Σ_j k_j γ_j`, `k ∈ ℤ^r`, the `γ_j`-fibre consists of the multiples of `e_j`
  (`independent_fibre`). So no channel raises the barrier of another
  (`independentChannel_purchase_le_fejer`). For two channels the two fibre barriers are attained at
  once, by the product of the two extremal profiles (`twoChannel_joint_barrier_attained`): the joint
  barrier is the product of the one-channel barriers.
* **Rank-two interior law** (`twoZero_exclusion_iff`, `twoChannel_width_cap`). Two zeros at the
  same distance from the line and incommensurable heights are excluded exactly when
  `√A + √(Gη) < √(B₁ + B₂)`. The joint purchase is at most `ρ_K + ρ_L < 4`, so with growth `L·W`,
  `W ≥ B₁ + B₂`, the certified width is below `(1 − (ρ_K + ρ_L)^{−1/2})²/L < 1/(4L)`.

Rank in the height variable therefore adds nothing per channel: a multi-channel certificate is
the direct sum of one-channel problems, one for each rational fibre.
-/

open Finset Real

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open MultiplicativePositivityGeometry

/-! ### Bohr projection onto a fibre -/

/-- A frequency resonates with `ω` when it is an integer multiple of `ω`. -/
def Resonant (ω u : ℝ) : Prop := ∃ n : ℤ, u = n * ω

/-- Sums of `cos(u (t + j h))` along a progression are bounded off resonance. -/
theorem abs_sum_cos_shift_le {u h : ℝ} (hs : Real.sin (u * h / 2) ≠ 0) (t : ℝ) (N : ℕ) :
    |∑ j ∈ range N, Real.cos (u * (t + j * h))| ≤ 1 / |Real.sin (u * h / 2)| := by
  have h1 := two_sin_mul_sum_cos (u * t) (u * h / 2) N
  have hterm : ∀ j ∈ range N, Real.cos (u * t + 2 * (j : ℝ) * (u * h / 2)) =
      Real.cos (u * (t + j * h)) := fun j _ => by congr 1; ring
  rw [Finset.sum_congr rfl hterm] at h1
  have hpos : 0 < |Real.sin (u * h / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos]
  have hb : |2 * Real.sin (u * h / 2) * ∑ j ∈ range N, Real.cos (u * (t + j * h))| ≤ 2 := by
    rw [h1]
    calc |Real.sin (u * t + (2 * N - 1) * (u * h / 2)) - Real.sin (u * t - u * h / 2)|
        ≤ |Real.sin (u * t + (2 * N - 1) * (u * h / 2))| + |Real.sin (u * t - u * h / 2)| :=
          abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  rw [abs_mul, abs_mul, abs_two] at hb
  linarith

/-- With step `2π/ω`, a non-resonant frequency is off every resonance of the progression. -/
theorem sin_half_step_ne_zero {ω u : ℝ} (hω : 0 < ω) (hr : ¬ Resonant ω u) :
    Real.sin (u * (2 * π / ω) / 2) ≠ 0 := by
  intro h0
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h0
  have e : u * (2 * π / ω) / 2 = (u / ω) * π := by field_simp
  rw [e] at hn
  have hnu : (n : ℝ) = u / ω := mul_right_cancel₀ Real.pi_ne_zero hn
  rw [eq_div_iff hω.ne'] at hnu
  exact hr ⟨n, hnu.symm⟩

/-- **Bohr projection.** The `ω`-fibre part of a nonnegative certificate is nonnegative. -/
theorem fibre_projection_nonneg {ι : Type*} (I : Finset ι) (c lam : ι → ℝ) {ω : ℝ} (hω : 0 < ω)
    (hP : ∀ t, 0 ≤ ∑ i ∈ I, c i * Real.cos (lam i * t)) (t : ℝ) :
    0 ≤ ∑ i ∈ I, if Resonant ω (lam i) then c i * Real.cos (lam i * t) else 0 := by
  set h := 2 * π / ω with hh
  set Q := ∑ i ∈ I, if Resonant ω (lam i) then c i * Real.cos (lam i * t) else 0
  set C := ∑ i ∈ I, if Resonant ω (lam i) then 0 else |c i| / |Real.sin (lam i * h / 2)|
  -- Averaging along the progression: `0 ≤ N Q + C` for every `N`.
  have key : ∀ N : ℕ, 0 ≤ N * Q + C := by
    intro N
    have hsum : 0 ≤ ∑ j ∈ range N, ∑ i ∈ I, c i * Real.cos (lam i * (t + j * h)) :=
      Finset.sum_nonneg fun j _ => hP _
    rw [Finset.sum_comm] at hsum
    have hmode : ∀ i ∈ I, ∑ j ∈ range N, c i * Real.cos (lam i * (t + j * h)) ≤
        N * (if Resonant ω (lam i) then c i * Real.cos (lam i * t) else 0) +
          (if Resonant ω (lam i) then 0 else |c i| / |Real.sin (lam i * h / 2)|) := by
      intro i _
      by_cases hr : Resonant ω (lam i)
      · obtain ⟨n, hn⟩ := hr
        have hper : ∀ j ∈ range N, c i * Real.cos (lam i * (t + j * h)) =
            c i * Real.cos (lam i * t) := by
          intro j _
          have e : lam i * (t + j * h) = lam i * t + ((n * j : ℤ) : ℝ) * (2 * π) := by
            rw [hn, hh]; push_cast; field_simp
          rw [e, Real.cos_add_int_mul_two_pi]
        rw [if_pos ⟨n, hn⟩, if_pos ⟨n, hn⟩, Finset.sum_congr rfl hper, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, add_zero]
      · rw [if_neg hr, if_neg hr, mul_zero, zero_add, ← Finset.mul_sum]
        have hs := sin_half_step_ne_zero hω hr
        calc c i * ∑ j ∈ range N, Real.cos (lam i * (t + j * h))
            ≤ |c i * ∑ j ∈ range N, Real.cos (lam i * (t + j * h))| := le_abs_self _
          _ = |c i| * |∑ j ∈ range N, Real.cos (lam i * (t + j * h))| := abs_mul _ _
          _ ≤ |c i| * (1 / |Real.sin (lam i * h / 2)|) :=
              mul_le_mul_of_nonneg_left (abs_sum_cos_shift_le hs t N) (abs_nonneg _)
          _ = |c i| / |Real.sin (lam i * h / 2)| := by ring
    have := hsum.trans (Finset.sum_le_sum hmode)
    rwa [Finset.sum_add_distrib, ← Finset.mul_sum] at this
  by_contra hneg
  push Not at hneg
  have hQ : 0 < -Q := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (C / -Q)
  rw [div_lt_iff₀ hQ] at hN
  nlinarith [key N]

/-! ### The fibre as a cosine polynomial -/

/-- Total weight of the modes at the frequencies `± mω`. -/
def fibreCoeff {ι : Type*} (I : Finset ι) (c lam : ι → ℝ) (ω : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ I, if |lam i| = m * ω then c i else 0

/-- `cos(|n| x) = cos(n x)` for integers `n`. -/
theorem cos_natAbs_mul (n : ℤ) (x : ℝ) : Real.cos ((n.natAbs : ℝ) * x) = Real.cos (n * x) := by
  rw [Nat.cast_natAbs, Int.cast_abs]
  rcases abs_choice (n : ℝ) with h | h <;> rw [h]
  rw [neg_mul, Real.cos_neg]

/-- The fibre part is the cosine polynomial of the fibre coefficients, evaluated at `ωt`. -/
theorem fibrePart_eq_cosinePolynomial {ι : Type*} (I : Finset ι) (c lam : ι → ℝ) {ω : ℝ}
    (hω : 0 < ω) {K : ℕ} (hK : ∀ i ∈ I, ∀ m : ℕ, |lam i| = m * ω → m ≤ K) (t : ℝ) :
    (∑ i ∈ I, if Resonant ω (lam i) then c i * Real.cos (lam i * t) else 0) =
      HTGeometry.cosinePolynomial (fibreCoeff I c lam ω) K (ω * t) := by
  unfold HTGeometry.cosinePolynomial fibreCoeff
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hr : Resonant ω (lam i)
  · obtain ⟨n, hn⟩ := hr
    have habs : |lam i| = (n.natAbs : ℝ) * ω := by
      rw [hn, abs_mul, abs_of_pos hω, Nat.cast_natAbs, Int.cast_abs]
    rw [if_pos ⟨n, hn⟩, Finset.sum_eq_single_of_mem n.natAbs
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hK i hi _ habs)))]
    · rw [if_pos habs, cos_natAbs_mul, hn]
      ring_nf
    · intro m _ hm
      rw [if_neg, zero_mul]
      intro h
      apply hm
      exact_mod_cast mul_right_cancel₀ hω.ne' (h.symm.trans habs)
  · rw [if_neg hr]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    rw [if_neg, zero_mul]
    intro h
    apply hr
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ m * ω)).mp h with h' | h'
    · exact ⟨m, by rw [h']; push_cast; ring⟩
    · exact ⟨-m, by rw [h']; push_cast; ring⟩

/-- **The barrier of a certificate is the barrier of its fibre.** If every frequency of a
nonnegative certificate that is a multiple `± mω` has `m ≤ K`, its total weight on `± ω` is at
most `2cos(π/(K+2))` times its weight at `0`. -/
theorem fibre_purchase_le_fejer {ι : Type*} (I : Finset ι) (c lam : ι → ℝ) {ω : ℝ} (hω : 0 < ω)
    {K : ℕ} (hK1 : 1 ≤ K) (hK : ∀ i ∈ I, ∀ m : ℕ, |lam i| = m * ω → m ≤ K)
    (hP : ∀ t, 0 ≤ ∑ i ∈ I, c i * Real.cos (lam i * t)) :
    fibreCoeff I c lam ω 1 ≤ 2 * Real.cos (π / (K + 2 : ℕ)) * fibreCoeff I c lam ω 0 := by
  refine cosinePolynomial_first_le_fejer hK1 fun θ => ?_
  have := fibre_projection_nonneg I c lam hω hP (θ / ω)
  rwa [fibrePart_eq_cosinePolynomial I c lam hω hK, mul_div_cancel₀ _ hω.ne'] at this

/-! ### Multi-frequency certificates -/

/-- For frequencies in `[0, ∞)` the fibre weight at `mω` is the coefficient at `mω`. -/
theorem fibreCoeff_of_nonneg {S : Finset ℝ} {a : ℝ → ℝ} (hS : ∀ u ∈ S, 0 ≤ u) (ω : ℝ) (m : ℕ) :
    fibreCoeff S a id ω m = if (m : ℝ) * ω ∈ S then a (m * ω) else 0 := by
  unfold fibreCoeff
  rw [← Finset.sum_ite_eq S ((m : ℝ) * ω) a]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [id, abs_of_nonneg (hS u hu)]
  exact if_congr eq_comm rfl rfl

/-- **Exact multi-frequency barrier.** A nonnegative certificate with frequencies in `[0, ∞)`
whose multiples of `γ` stop at `Kγ` has `a(γ) ≤ 2cos(π/(K+2)) a(0)`. -/
theorem multiFrequency_purchase_le_fibre_fejer {S : Finset ℝ} {a : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hS : ∀ u ∈ S, 0 ≤ u) (h0 : 0 ∈ S) (hγS : γ ∈ S) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : ∀ m : ℕ, (m : ℝ) * γ ∈ S → m ≤ K)
    (hP : ∀ t, 0 ≤ ∑ u ∈ S, a u * Real.cos (u * t)) :
    a γ ≤ 2 * Real.cos (π / (K + 2 : ℕ)) * a 0 := by
  have h := fibre_purchase_le_fejer S a id hγ hK1
    (fun u hu m hm => hK m (by rw [id, abs_of_nonneg (hS u hu)] at hm; rwa [← hm])) hP
  rw [fibreCoeff_of_nonneg hS, fibreCoeff_of_nonneg hS] at h
  simpa [hγS, h0] using h

/-- **The fibre barrier is attained.** If a spectrum contains `0, ω, …, Kω`, the Fejér extremal
in the variable `ωt` is a nonnegative certificate on it with `a(ω) = 2cos(π/(K+2)) a(0)`. -/
theorem fibre_barrier_attained {S : Finset ℝ} {ω : ℝ} (hω : 0 < ω) {K : ℕ} (hK1 : 1 ≤ K)
    (hsub : ∀ m ≤ K, (m : ℝ) * ω ∈ S) :
    ∃ a : ℝ → ℝ, (∀ t, 0 ≤ ∑ u ∈ S, a u * Real.cos (u * t)) ∧ 0 < a 0 ∧
      a ω = 2 * Real.cos (π / (K + 2 : ℕ)) * a 0 := by
  obtain ⟨hP, h0, h1⟩ := fejer_barrier_attained hK1
  set b := fejerExtremalCoeff K
  refine ⟨fun u => ∑ m ∈ range (K + 1), if u = m * ω then b m else 0, fun t => ?_, ?_, ?_⟩
  · have e : ∑ u ∈ S, (∑ m ∈ range (K + 1), if u = m * ω then b m else 0) * Real.cos (u * t) =
        HTGeometry.cosinePolynomial b K (ω * t) := by
      unfold HTGeometry.cosinePolynomial
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.sum_ite_eq' S ((m : ℝ) * ω) (fun u => b m * Real.cos (u * t)),
        if_pos (hsub m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))), mul_assoc]
    rw [e]
    exact hP _
  · beta_reduce
    rw [Finset.sum_eq_single_of_mem 0 (by simp)]
    · simpa using h0
    · intro m _ hm
      rw [if_neg]
      intro h
      exact hm (by exact_mod_cast (mul_eq_zero.mp h.symm).resolve_right hω.ne')
  · have hone : ∀ m ∈ range (K + 1), m ≠ 1 → (if ω = m * ω then b m else 0) = 0 := by
      intro m _ hm
      rw [if_neg]
      intro h
      exact hm (by exact_mod_cast (mul_eq_right₀ hω.ne').mp h.symm)
    have hzero : ∀ m ∈ range (K + 1), m ≠ 0 → (if (0 : ℝ) = m * ω then b m else 0) = 0 := by
      intro m _ hm
      rw [if_neg]
      intro h
      exact hm (by exact_mod_cast (mul_eq_zero.mp h.symm).resolve_right hω.ne')
    beta_reduce
    rw [Finset.sum_eq_single_of_mem 1 (by simp; omega) hone,
      Finset.sum_eq_single_of_mem 0 (by simp) hzero]
    simpa using h1

/-! ### Independent channels -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The frequency `⟨k, γ⟩ = Σ_j k_j γ_j` of an exponent vector `k ∈ ℤ^ι`. -/
def channelFreq (γ : ι → ℝ) (k : ι → ℤ) : ℝ := ∑ i, (k i : ℝ) * γ i

omit [DecidableEq ι] in
/-- `ℚ`-independent frequencies admit no integer relation. -/
theorem eq_zero_of_channelFreq_eq_zero {γ : ι → ℝ} (hγ : LinearIndependent ℚ γ) {z : ι → ℤ}
    (h : channelFreq γ z = 0) : z = 0 := by
  funext i
  have := Fintype.linearIndependent_iff.mp hγ (fun i => (z i : ℚ)) (by
    simpa [channelFreq, Rat.smul_def] using h)
  exact_mod_cast this i

theorem channelFreq_smul_single (γ : ι → ℝ) (j : ι) (m : ℤ) :
    channelFreq γ (m • Pi.single j 1) = m * γ j := by
  unfold channelFreq
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- **The fibre of an independent channel.** If `|⟨k, γ⟩| = m |γ_j|`, then `k = ± m e_j`. -/
theorem independent_fibre {γ : ι → ℝ} (hγ : LinearIndependent ℚ γ) {j : ι} {k : ι → ℤ} {m : ℕ}
    (h : |channelFreq γ k| = m * |γ j|) :
    k = (m : ℤ) • Pi.single j 1 ∨ k = -((m : ℤ) • Pi.single j 1) := by
  have hrel : ∀ s : ℤ, channelFreq γ k = s * γ j → k = s • Pi.single j 1 := by
    intro s hs
    have h0 : channelFreq γ (k - s • Pi.single j 1) = 0 := by
      have hsub : channelFreq γ (k - s • Pi.single j 1) =
          channelFreq γ k - channelFreq γ (s • Pi.single j 1) := by
        unfold channelFreq
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.sub_apply]
        push_cast
        ring
      rw [hsub, channelFreq_smul_single, hs, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_channelFreq_eq_zero hγ h0)
  have hm : |channelFreq γ k| = |(m : ℝ) * γ j| := by
    rw [h, abs_mul, Nat.abs_cast]
  rcases abs_eq_abs.mp hm with h1 | h1
  · left
    exact hrel m (by rw [h1]; push_cast; ring)
  · right
    rw [hrel (-m) (by rw [h1]; push_cast; ring), neg_smul]

omit [Fintype ι] in
/-- The frequency vectors `± e_j` are distinct. -/
theorem single_ne_neg_single (j : ι) : (Pi.single j 1 : ι → ℤ) ≠ -Pi.single j 1 := by
  intro h
  have := congrFun h j
  simp at this

/-- In an independent channel the fibre weight at `± γ_j` is `c(e_j) + c(−e_j)`, and the fibre
weight at `0` is `c(0)`. -/
theorem independent_fibreCoeff {γ : ι → ℝ} (hγ : LinearIndependent ℚ γ) {j : ι}
    (B : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ) (hB0 : 0 ∈ B) (hB1 : Pi.single j 1 ∈ B)
    (hB1' : -Pi.single j 1 ∈ B) :
    fibreCoeff B c (channelFreq γ) |γ j| 1 = c (Pi.single j 1) + c (-Pi.single j 1) ∧
      fibreCoeff B c (channelFreq γ) |γ j| 0 = c 0 := by
  have hγj : γ j ≠ 0 := hγ.ne_zero j
  constructor
  · unfold fibreCoeff
    have e : ∀ k ∈ B, (if |channelFreq γ k| = ((1 : ℕ) : ℝ) * |γ j| then c k else 0) =
        (if k = Pi.single j 1 then c k else 0) + (if k = -Pi.single j 1 then c k else 0) := by
      intro k _
      by_cases h : |channelFreq γ k| = ((1 : ℕ) : ℝ) * |γ j|
      · rw [if_pos h]
        rcases independent_fibre hγ h with h' | h' <;> simp only [Nat.cast_one, one_smul] at h'
        · rw [if_pos h', if_neg (h' ▸ single_ne_neg_single j)]; ring
        · rw [if_neg (h' ▸ (single_ne_neg_single j).symm), if_pos h']; ring
      · rw [if_neg h]
        have h1 : k ≠ Pi.single j 1 := by
          rintro rfl
          apply h
          rw [show (Pi.single j 1 : ι → ℤ) = (1 : ℤ) • Pi.single j 1 by simp,
            channelFreq_smul_single]
          simp
        have h2 : k ≠ -Pi.single j 1 := by
          rintro rfl
          apply h
          rw [show -(Pi.single j 1 : ι → ℤ) = (-1 : ℤ) • Pi.single j 1 by simp,
            channelFreq_smul_single]
          simp
        rw [if_neg h1, if_neg h2]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq' B _ c,
      Finset.sum_ite_eq' B _ c, if_pos hB1, if_pos hB1']
  · unfold fibreCoeff
    have h0 : (∑ k ∈ B, if k = 0 then c k else 0) = c 0 := by
      rw [Finset.sum_ite_eq' B 0 c, if_pos hB0]
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
    rw [Nat.cast_zero, zero_mul, abs_eq_zero]
    exact ⟨eq_zero_of_channelFreq_eq_zero hγ, fun h => by simp [h, channelFreq]⟩

/-- **A channel never raises the barrier of another.** For `ℚ`-independent frequencies, a
nonnegative certificate on the spectrum `⟨k, γ⟩`, `k ∈ B`, whose `j`-th axis stops at `K`, has
`c(e_j) + c(−e_j) ≤ 2cos(π/(K+2)) c(0)`, whatever the other channels carry. -/
theorem independentChannel_purchase_le_fejer {γ : ι → ℝ} (hγ : LinearIndependent ℚ γ) (j : ι)
    (B : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ) (hB0 : 0 ∈ B) (hB1 : Pi.single j 1 ∈ B)
    (hB1' : -Pi.single j 1 ∈ B) {K : ℕ} (hK1 : 1 ≤ K)
    (hK : ∀ m : ℕ, ((m : ℤ) • Pi.single j 1 ∈ B ∨ -((m : ℤ) • Pi.single j 1) ∈ B) → m ≤ K)
    (hP : ∀ t, 0 ≤ ∑ k ∈ B, c k * Real.cos (channelFreq γ k * t)) :
    c (Pi.single j 1) + c (-Pi.single j 1) ≤ 2 * Real.cos (π / (K + 2 : ℕ)) * c 0 := by
  obtain ⟨e1, e0⟩ := independent_fibreCoeff hγ B c hB0 hB1 hB1'
  rw [← e1, ← e0]
  refine fibre_purchase_le_fejer B c (channelFreq γ) (abs_pos.mpr (hγ.ne_zero j)) hK1
    (fun k hk m hm => hK m ?_) hP
  rcases independent_fibre hγ hm with h | h
  · exact Or.inl (h ▸ hk)
  · exact Or.inr (h ▸ hk)

/-! ### Two channels: the joint barrier is the product -/

/-- Modes of the product of two cosine polynomials: `((m, n), s)` carries the frequency
`m γ₁ + s n γ₂`, `s = ± 1`. -/
def productModes (K L : ℕ) : Finset ((ℕ × ℕ) × ℤ) := (range (K + 1) ×ˢ range (L + 1)) ×ˢ {1, -1}

def productFreq (γ₁ γ₂ : ℝ) (i : (ℕ × ℕ) × ℤ) : ℝ := i.1.1 * γ₁ + i.2 * (i.1.2 * γ₂)

def productCoeff (b b' : ℕ → ℝ) (i : (ℕ × ℕ) × ℤ) : ℝ := b i.1.1 * b' i.1.2 / 2

/-- The product certificate is `Q₁(γ₁t) Q₂(γ₂t)`. -/
theorem productCertificate_eq (b b' : ℕ → ℝ) (K L : ℕ) (γ₁ γ₂ t : ℝ) :
    ∑ i ∈ productModes K L, productCoeff b b' i * Real.cos (productFreq γ₁ γ₂ i * t) =
      HTGeometry.cosinePolynomial b K (γ₁ * t) * HTGeometry.cosinePolynomial b' L (γ₂ * t) := by
  unfold productModes productCoeff productFreq HTGeometry.cosinePolynomial
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_pair (by norm_num : (1 : ℤ) ≠ -1)]
  have e1 : ((m : ℝ) * γ₁ + ((1 : ℤ) : ℝ) * (n * γ₂)) * t = m * (γ₁ * t) + n * (γ₂ * t) := by
    push_cast; ring
  have e2 : ((m : ℝ) * γ₁ + ((-1 : ℤ) : ℝ) * (n * γ₂)) * t = m * (γ₁ * t) - n * (γ₂ * t) := by
    push_cast; ring
  rw [e1, e2, Real.cos_add, Real.cos_sub]
  ring

/-- With integrally independent `γ₁, γ₂ > 0`, the `γ₁`-fibre of the product modes at `p` is
`((p, 0), ± 1)`. -/
theorem productFreq_fibre {γ₁ γ₂ : ℝ} (h₁ : 0 < γ₁)
    (hind : ∀ m n : ℤ, m * γ₁ + n * γ₂ = 0 → m = 0 ∧ n = 0) {i : (ℕ × ℕ) × ℤ}
    (hi : i.2 = 1 ∨ i.2 = -1) {p : ℕ} :
    |productFreq γ₁ γ₂ i| = p * γ₁ ↔ i.1.1 = p ∧ i.1.2 = 0 := by
  obtain ⟨⟨m, n⟩, s⟩ := i
  simp only at hi ⊢
  unfold productFreq
  simp only
  constructor
  · intro h
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ p * γ₁)).mp h with h' | h'
    · obtain ⟨hm, hn⟩ := hind (m - p) (s * n) (by push_cast; linarith)
      have hs : s ≠ 0 := by rcases hi with rfl | rfl <;> norm_num
      exact ⟨by omega, by
        have := (mul_eq_zero.mp hn).resolve_left hs; omega⟩
    · obtain ⟨hm, hn⟩ := hind (m + p) (s * n) (by push_cast; linarith)
      have hs : s ≠ 0 := by rcases hi with rfl | rfl <;> norm_num
      exact ⟨by omega, by
        have := (mul_eq_zero.mp hn).resolve_left hs; omega⟩
  · rintro ⟨rfl, rfl⟩
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    exact abs_of_nonneg (by positivity)

/-- The same for the `γ₂`-fibre: it is `((0, p), ± 1)`. -/
theorem productFreq_fibre' {γ₁ γ₂ : ℝ} (h₂ : 0 < γ₂)
    (hind : ∀ m n : ℤ, m * γ₁ + n * γ₂ = 0 → m = 0 ∧ n = 0) {i : (ℕ × ℕ) × ℤ}
    (hi : i.2 = 1 ∨ i.2 = -1) {p : ℕ} :
    |productFreq γ₁ γ₂ i| = p * γ₂ ↔ i.1.1 = 0 ∧ i.1.2 = p := by
  obtain ⟨⟨m, n⟩, s⟩ := i
  simp only at hi ⊢
  unfold productFreq
  simp only
  have hs2 : s * s = 1 := by rcases hi with rfl | rfl <;> norm_num
  constructor
  · intro h
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ p * γ₂)).mp h with h' | h'
    · obtain ⟨hm, hn⟩ := hind m (s * n - p) (by push_cast; linarith)
      refine ⟨by omega, ?_⟩
      have : s * n = p := by omega
      rcases hi with rfl | rfl <;> omega
    · obtain ⟨hm, hn⟩ := hind m (s * n + p) (by push_cast; linarith)
      refine ⟨by omega, ?_⟩
      have : s * n = -p := by omega
      rcases hi with rfl | rfl <;> omega
  · rintro ⟨rfl, rfl⟩
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rcases hi with rfl | rfl
    · simp only [Int.cast_one, one_mul]; exact abs_of_nonneg (by positivity)
    · simp only [Int.cast_neg, Int.cast_one, neg_one_mul, abs_neg]
      exact abs_of_nonneg (by positivity)

/-- Fibre weights of the product certificate: `b_p b'_0` along `γ₁`, `b_0 b'_p` along `γ₂`. -/
theorem productCoeff_fibreCoeff {γ₁ γ₂ : ℝ} (h₁ : 0 < γ₁) (h₂ : 0 < γ₂)
    (hind : ∀ m n : ℤ, m * γ₁ + n * γ₂ = 0 → m = 0 ∧ n = 0) (b b' : ℕ → ℝ) {K L p : ℕ}
    (hpK : p ≤ K) (hpL : p ≤ L) :
    fibreCoeff (productModes K L) (productCoeff b b') (productFreq γ₁ γ₂) γ₁ p = b p * b' 0 ∧
      fibreCoeff (productModes K L) (productCoeff b b') (productFreq γ₁ γ₂) γ₂ p = b 0 * b' p := by
  have hmem : ∀ i ∈ productModes K L, i.2 = 1 ∨ i.2 = -1 := by
    intro i hi
    simp only [productModes, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hi
    exact hi.2
  constructor
  · unfold fibreCoeff
    rw [Finset.sum_congr rfl fun i hi =>
      if_congr (productFreq_fibre h₁ hind (hmem i hi)) rfl rfl]
    unfold productModes
    rw [Finset.sum_product, Finset.sum_product,
      Finset.sum_eq_single_of_mem p (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
      · rw [Finset.sum_pair (by norm_num : (1 : ℤ) ≠ -1)]
        simp [productCoeff]
      · intro n _ hn
        exact Finset.sum_eq_zero fun s _ => if_neg fun h => hn h.2
    · intro m _ hm
      exact Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun s _ => if_neg fun h => hm h.1
  · unfold fibreCoeff
    rw [Finset.sum_congr rfl fun i hi =>
      if_congr (productFreq_fibre' h₂ hind (hmem i hi)) rfl rfl]
    unfold productModes
    rw [Finset.sum_product, Finset.sum_product,
      Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem p (Finset.mem_range.mpr (by omega))]
      · rw [Finset.sum_pair (by norm_num : (1 : ℤ) ≠ -1)]
        simp [productCoeff]
      · intro n _ hn
        exact Finset.sum_eq_zero fun s _ => if_neg fun h => hn h.2
    · intro m _ hm
      exact Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun s _ => if_neg fun h => hm h.1

/-- **The joint barrier of two independent channels is the product of their barriers.** The
product of the two Fejér extremals is a nonnegative certificate on the two-channel spectrum whose
`γ₁`-fibre and `γ₂`-fibre both meet their barriers, with the same pole weight. -/
theorem twoChannel_joint_barrier_attained {γ₁ γ₂ : ℝ} (h₁ : 0 < γ₁) (h₂ : 0 < γ₂)
    (hind : ∀ m n : ℤ, m * γ₁ + n * γ₂ = 0 → m = 0 ∧ n = 0) {K L : ℕ} (hK : 1 ≤ K) (hL : 1 ≤ L) :
    let I := productModes K L
    let c := productCoeff (fejerExtremalCoeff K) (fejerExtremalCoeff L)
    let lam := productFreq γ₁ γ₂
    (∀ t, 0 ≤ ∑ i ∈ I, c i * Real.cos (lam i * t)) ∧ 0 < fibreCoeff I c lam γ₁ 0 ∧
      fibreCoeff I c lam γ₂ 0 = fibreCoeff I c lam γ₁ 0 ∧
      fibreCoeff I c lam γ₁ 1 = 2 * Real.cos (π / (K + 2 : ℕ)) * fibreCoeff I c lam γ₁ 0 ∧
      fibreCoeff I c lam γ₂ 1 = 2 * Real.cos (π / (L + 2 : ℕ)) * fibreCoeff I c lam γ₂ 0 := by
  intro I c lam
  obtain ⟨hPK, h0K, h1K⟩ := fejer_barrier_attained hK
  obtain ⟨hPL, h0L, h1L⟩ := fejer_barrier_attained hL
  obtain ⟨a0, a0'⟩ := productCoeff_fibreCoeff h₁ h₂ hind (fejerExtremalCoeff K)
    (fejerExtremalCoeff L) (Nat.zero_le K) (Nat.zero_le L)
  obtain ⟨a1, -⟩ := productCoeff_fibreCoeff h₁ h₂ hind (fejerExtremalCoeff K)
    (fejerExtremalCoeff L) hK hL
  obtain ⟨-, a1'⟩ := productCoeff_fibreCoeff h₁ h₂ hind (fejerExtremalCoeff K)
    (fejerExtremalCoeff L) hK hL
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_⟩
  · rw [productCertificate_eq]
    exact mul_nonneg (hPK _) (hPL _)
  · rw [a0]; exact mul_pos h0K h0L
  · rw [a0, a0']
  · rw [a1, a0, h1K]; ring
  · rw [a1', a0', h1L]; ring

/-! ### The rank-two interior law -/

/-- **Two-zero exclusion.** Two zeros at the same distance `η` from the line, with zero weights
`B₁, B₂`, are excluded by pole weight `A` and growth `G` iff `√A + √(Gη) < √(B₁ + B₂)`. -/
theorem twoZero_exclusion_iff {A B₁ B₂ G η : ℝ} (hA : 0 < A) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hG : 0 < G) (hη : 0 < η) :
    (∃ δ > 0, A / δ + G < B₁ / (δ + η) + B₂ / (δ + η)) ↔
      Real.sqrt A + Real.sqrt (G * η) < Real.sqrt (B₁ + B₂) := by
  rw [← exclusion_iff hA (add_nonneg hB₁ hB₂) hG hη]
  simp only [add_div]

/-- **Width cap from a purchase ratio.** If the zero weight is at most `ρ ≥ 1` times the pole
weight and the growth is `L·W` with `W ≥ B`, a zero at distance `η` can only be excluded when
`η < (1 − ρ^{−1/2})²/L`. -/
theorem width_cap_of_purchase_le {A B W L η ρ : ℝ} (hA : 0 < A) (hB : 0 < B) (hρ1 : 1 ≤ ρ)
    (hBρ : B ≤ ρ * A) (hW : B ≤ W) (hL : 0 < L) (hη : 0 < η)
    (hexcl : ∃ δ > 0, A / δ + L * W < B / (δ + η)) :
    η < (1 - 1 / Real.sqrt ρ) ^ 2 / L := by
  have h := (exclusion_iff hA hB.le (mul_pos hL (hB.trans_le hW)) hη).mp hexcl
  have hu0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hv0 : 0 ≤ Real.sqrt (L * η) := Real.sqrt_nonneg _
  have hr0 : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr (by linarith)
  have hvu : Real.sqrt (L * η) * Real.sqrt B ≤ Real.sqrt (L * W * η) := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ L * η by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith [mul_pos hL hη])
  have hur : Real.sqrt B ≤ Real.sqrt ρ * Real.sqrt A := by
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ ρ by linarith)]
    exact Real.sqrt_le_sqrt hBρ
  have h0 : Real.sqrt A + Real.sqrt (L * η) * Real.sqrt B < Real.sqrt B := by linarith
  have h1 := mul_lt_mul_of_pos_right h0 hr0
  have hkey : Real.sqrt B * (1 + Real.sqrt (L * η) * Real.sqrt ρ) <
      Real.sqrt B * Real.sqrt ρ := by nlinarith
  have hkey' := lt_of_mul_lt_mul_left hkey hu0.le
  have hv : Real.sqrt (L * η) < 1 - 1 / Real.sqrt ρ := by
    rw [show 1 - 1 / Real.sqrt ρ = (Real.sqrt ρ - 1) / Real.sqrt ρ by field_simp,
      lt_div_iff₀ hr0]
    linarith
  have hsq := mul_self_lt_mul_self hv0 hv
  rw [Real.mul_self_sqrt (by positivity)] at hsq
  rw [lt_div_iff₀ hL, mul_comm]
  nlinarith

/-- **Rank-two width cap.** Two independent channels of degrees `K, L` purchase at most
`ρ_K + ρ_L` units of zero weight per unit of pole, so two zeros at the same distance are excluded
only within `(1 − (ρ_K + ρ_L)^{−1/2})²/L'`, which is below `1/(4L')`. -/
theorem twoChannel_width_cap {A B₁ B₂ W L' η : ℝ} {K L : ℕ} (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hA : 0 < A) (hB : 0 < B₁ + B₂) (hB₁ : B₁ ≤ 2 * Real.cos (π / (K + 2 : ℕ)) * A)
    (hB₂ : B₂ ≤ 2 * Real.cos (π / (L + 2 : ℕ)) * A) (hW : B₁ + B₂ ≤ W) (hL' : 0 < L')
    (hη : 0 < η) (hexcl : ∃ δ > 0, A / δ + L' * W < B₁ / (δ + η) + B₂ / (δ + η)) :
    η < (1 - 1 / Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ)) + 2 * Real.cos (π / (L + 2 : ℕ)))) ^ 2
        / L' ∧
      (1 - 1 / Real.sqrt (2 * Real.cos (π / (K + 2 : ℕ)) + 2 * Real.cos (π / (L + 2 : ℕ)))) ^ 2
        / L' < 1 / (4 * L') := by
  obtain ⟨hρK1, hρK2⟩ := fejer_ratio_mem hK
  obtain ⟨hρL1, hρL2⟩ := fejer_ratio_mem hL
  set ρ := 2 * Real.cos (π / (K + 2 : ℕ)) + 2 * Real.cos (π / (L + 2 : ℕ))
  refine ⟨width_cap_of_purchase_le hA hB (by linarith) (by linarith) hW hL' hη ?_, ?_⟩
  · obtain ⟨δ, hδ, h⟩ := hexcl
    exact ⟨δ, hδ, by rwa [← add_div] at h⟩
  · have hr1 : 1 ≤ Real.sqrt ρ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    have hr2 : Real.sqrt ρ < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact (Real.sqrt_lt_sqrt_iff (by linarith)).mpr (by linarith)
    have hr0 : 0 < Real.sqrt ρ := by linarith
    have hx0 : 0 ≤ 1 - 1 / Real.sqrt ρ := by
      rw [sub_nonneg, div_le_one hr0]; exact hr1
    have hx : 1 - 1 / Real.sqrt ρ < 1 / 2 := by
      rw [show 1 - 1 / Real.sqrt ρ = (Real.sqrt ρ - 1) / Real.sqrt ρ by field_simp,
        div_lt_iff₀ hr0]
      linarith
    rw [div_lt_div_iff₀ hL' (by positivity)]
    nlinarith [mul_self_lt_mul_self hx0 hx]

end GaloisForLFunctions.ArithmeticPositiveDuality

