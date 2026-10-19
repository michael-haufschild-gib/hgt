import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPronicRayDecomposition

/-!
# Physical Fermi ray weights and terminal control

Exact weight comparisons and geometric tail identities transfer the existing
mixed-boundary sine inequality to the complete normalized Fermi ray. These are
ingredients for physical trace conditioning; no asymptotic optimality is asserted here.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open RHTower GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

private theorem real_weight_bounds (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a / ((a + 1) * b^2) ≤ a^2 / (a * b * (a * b + 1)) ∧
      a^2 / (a * b * (a * b + 1)) ≤ 1 / b^2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  constructor
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hp : 0 ≤ a^2 * b * (b - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg a) hb0.le) (by linarith)
    nlinarith only [hp]
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_nonneg ha0.le hb0.le]

private theorem real_weight_formula (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2 / (a * b * (a * b + 1)) = 1 / (b * (b + 1 / a)) := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have hab : a * b + 1 ≠ 0 := by positivity
  have hs : b + 1 / a ≠ 0 := by positivity
  field_simp

/-- The physical ray weight lies between explicit multiples of the homogeneous weight. -/
theorem fermiDyadicPronicWeight_bounds (k b : ℕ) (hb : 0 < b) :
    (2 : ℝ)^k / (((2 : ℝ)^k + 1) * (b : ℝ)^2) ≤ fermiDyadicPronicWeight k b ∧
      fermiDyadicPronicWeight k b ≤ 1 / (b : ℝ)^2 := by
  have ha : (1 : ℝ) ≤ 2^k := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  unfold fermiDyadicPronicWeight
  rw [cast_pronicSeq_eq]
  push_cast
  exact real_weight_bounds _ _ ha hb'

/-- Exact physical weight in normalized dyadic ray coordinates. -/
theorem fermiDyadicPronicWeight_formula (k b : ℕ) (hb : 0 < b) :
    fermiDyadicPronicWeight k b = 1 / ((b : ℝ) * ((b : ℝ) + 1 / (2 : ℝ)^k)) := by
  unfold fermiDyadicPronicWeight
  rw [cast_pronicSeq_eq]
  push_cast
  exact real_weight_formula _ _ (by positivity) (by exact_mod_cast hb)

/-- The homogeneous weight loses at most a dyadic relative error. -/
theorem fermiDyadicPronicWeight_lower_error (k b : ℕ) (hb : 0 < b) :
    (1 - 1 / (2 : ℝ)^k) / (b : ℝ)^2 ≤ fermiDyadicPronicWeight k b := by
  have ha : (0 : ℝ) < 2^k := by positivity
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  refine le_trans ?_ (fermiDyadicPronicWeight_bounds k b hb).1
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have he : (1 - 1 / (2 : ℝ)^k) * (((2 : ℝ)^k + 1) * (b : ℝ)^2) =
      (2 : ℝ)^k * (b : ℝ)^2 - (b : ℝ)^2 / (2 : ℝ)^k := by
    field_simp
    ring
  rw [he]
  nlinarith only [div_nonneg (sq_nonneg (b : ℝ)) ha.le]

/-- Physical ray weights increase with the dyadic level. -/
theorem fermiDyadicPronicWeight_mono (k l b : ℕ) (hkl : k ≤ l) (hb : 0 < b) :
    fermiDyadicPronicWeight k b ≤ fermiDyadicPronicWeight l b := by
  have ha : (0 : ℝ) < 2^k := by positivity
  have hA : (0 : ℝ) < 2^l := by positivity
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hpow : (2 : ℝ)^k ≤ 2^l := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    rw [pow_add]
    have hd : (1 : ℝ) ≤ 2^d := by
      clear hkl hA
      induction d with
      | zero => norm_num
      | succ d ih => rw [pow_succ]; nlinarith
    nlinarith
  rw [fermiDyadicPronicWeight_formula k b hb, fermiDyadicPronicWeight_formula l b hb]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hi : 1 / (2 : ℝ)^l ≤ 1 / (2 : ℝ)^k :=
    (div_le_div_iff₀ hA ha).mpr (by simpa using hpow)
  nlinarith

/-- A free terminal value costs an explicit square penalty in the sharp finite-chain inequality. -/
theorem fermiNormalizedDyadicSieve_terminal_mass_bound (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b)
    (a n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
    M * lam * (∑ k ∈ Finset.range n, (fermiNormalizedDyadicSieve N c b (a + k))^2) ≤
      (M + 1) * (∑ k ∈ Finset.range n, (fermiNormalizedDyadicJump N c b (a + k))^2) +
        M * (M + 1) * lam * n * (fermiNormalizedDyadicSieve N c b (a + n))^2 := by
  dsimp only
  let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
  let x := fun k => fermiNormalizedDyadicSieve N c b (a + k)
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    linarith [Real.cos_le_one (Real.pi / (((2 * n : ℕ) : ℝ) + 1))]
  have hs := fermiNormalizedDyadicSieve_terminal_sine_bound N c hb a n
  have hyoung : M * (∑ k ∈ Finset.range n, (x k)^2) ≤
      (M + 1) * (∑ k ∈ Finset.range n, (x k - x n)^2) +
        M * (M + 1) * n * (x n)^2 := by
    have hpoint : ∀ k : ℕ, M * (x k)^2 ≤
        (M + 1) * (x k - x n)^2 + M * (M + 1) * (x n)^2 := by
      intro k
      nlinarith only [sq_nonneg (x k - (M + 1) * x n)]
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => hpoint k)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hsum
  have h1 := mul_le_mul_of_nonneg_left hyoung hlam
  have h2 := mul_le_mul_of_nonneg_left hs (show 0 ≤ M + 1 by linarith)
  change lam * (M * ∑ k ∈ Finset.range n, (x k)^2) ≤ _ at h1
  change lam * (∑ k ∈ Finset.range n, (x k - x n)^2) ≤ _ at hs
  dsimp only [x, lam] at h1
  nlinarith only [h1, h2]

private theorem sieve_depth_tail (N : ℕ) (c : ℕ → ℝ) (b j : ℕ) :
    sieveSeq N c (2^(Nat.log 2 N + 1 + j) * b) =
      sieveSeq N c (2^(Nat.log 2 N + 1) * b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show Nat.log 2 N + 1 + (j + 1) = Nat.log 2 N + 2 + j by omega,
      pow_add, Nat.mul_assoc, sieveSeq_dyadic_depth_saturation,
      ← Nat.mul_assoc, ← pow_add]
    exact ih

private theorem normalized_tail (N : ℕ) (c : ℕ → ℝ) (b j : ℕ) :
    fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + j) =
      fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1) / (2 : ℝ)^j := by
  unfold fermiNormalizedDyadicSieve
  rw [sieve_depth_tail, div_div, pow_add (2 : ℝ) (Nat.log 2 N + 1) j]

/-- Beyond the admission depth, normalized sieve values decay exactly by powers of two. -/
theorem fermiNormalizedDyadicSieve_depth_tail (N : ℕ) (c : ℕ → ℝ) (b a j : ℕ) :
    fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + a + j) =
      fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + a) / (2 : ℝ)^j := by
  rw [show Nat.log 2 N + 1 + a + j = Nat.log 2 N + 1 + (a + j) by omega,
    normalized_tail, normalized_tail, pow_add (2 : ℝ) a j, div_div]

private theorem square_half_power (x : ℝ) (j : ℕ) :
    (x / (2 : ℝ)^j)^2 = x^2 * (1 / 4 : ℝ)^j := by
  rw [div_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul, div_pow]
  norm_num
  ring

/-- Exact square mass of every geometric tail beyond the admission depth. -/
theorem fermiNormalizedDyadicSieve_tail_hasSum (N : ℕ) (c : ℕ → ℝ) (b a : ℕ) :
    HasSum (fun j : ℕ => (fermiNormalizedDyadicSieve N c b
      (Nat.log 2 N + 1 + a + j))^2)
      ((4 / 3 : ℝ) * (fermiNormalizedDyadicSieve N c b
        (Nat.log 2 N + 1 + a))^2) := by
  have hg := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hh := hg.mul_left ((fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 1 + a))^2)
  have heq : (fun j : ℕ => (fermiNormalizedDyadicSieve N c b
      (Nat.log 2 N + 1 + a + j))^2) =
      fun j : ℕ => (fermiNormalizedDyadicSieve N c b
        (Nat.log 2 N + 1 + a))^2 * (1 / 4 : ℝ)^j := by
    funext j
    rw [fermiNormalizedDyadicSieve_depth_tail, square_half_power]
  rw [heq]
  simpa only [show (1 - 1 / 4 : ℝ)⁻¹ = 4 / 3 by norm_num, mul_comm] using hh

/-- The first unadmitted tail has square mass determined by the observed terminal jump. -/
theorem fermiNormalizedDyadicSieve_observed_tail_hasSum (N : ℕ) (c : ℕ → ℝ) {b : ℕ}
    (hb : 0 < b) :
    HasSum (fun j : ℕ => (fermiNormalizedDyadicSieve N c b
      (Nat.log 2 N + 2 + j))^2)
      ((4 / 3 : ℝ) * (fermiNormalizedDyadicJump N c b (Nat.log 2 N + 1))^2) := by
  have h := fermiNormalizedDyadicSieve_tail_hasSum N c b 1
  have ht := fermiNormalizedDyadicJump_depth_boundary N c hb
  dsimp only at ht
  simpa only [show Nat.log 2 N + 1 + 1 = Nat.log 2 N + 2 by omega, ← ht] using h

/-- The complete ray, including its geometric tail, is controlled by finitely many observed jumps. -/
theorem fermiNormalizedDyadicSieve_complete_ray_sine_bound (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b)
    (a n : ℕ) (hn : a + n = Nat.log 2 N + 2) (hn0 : 0 < n)
    (M : ℝ) (hM : 0 ≤ M) :
    let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
    M * lam * (∑' k : ℕ, (fermiNormalizedDyadicSieve N c b (a + k))^2) ≤
      ((M + 1) + M * (M + 1) * lam * n + (4 / 3 : ℝ) * M * lam) *
        (∑ k ∈ Finset.range n, (fermiNormalizedDyadicJump N c b (a + k))^2) := by
  dsimp only
  let lam := 2 - 2 * Real.cos (Real.pi / (((2 * n : ℕ) : ℝ) + 1))
  have hlam : 0 ≤ lam := by
    dsimp [lam]
    linarith [Real.cos_le_one (Real.pi / (((2 * n : ℕ) : ℝ) + 1))]
  have htail : HasSum (fun j : ℕ => (fermiNormalizedDyadicSieve N c b (a + (j + n)))^2)
      ((4 / 3 : ℝ) * (fermiNormalizedDyadicJump N c b (Nat.log 2 N + 1))^2) := by
    have heq : (fun j : ℕ => (fermiNormalizedDyadicSieve N c b (a + (j + n)))^2) =
        fun j : ℕ => (fermiNormalizedDyadicSieve N c b (Nat.log 2 N + 2 + j))^2 := by
      funext j
      congr 2
      omega
    rw [heq]
    exact fermiNormalizedDyadicSieve_observed_tail_hasSum N c hb
  have hf : Summable (fun j : ℕ => (fermiNormalizedDyadicSieve N c b (a + j))^2) :=
    (summable_nat_add_iff n).mp htail.summable
  have hsplit := Summable.sum_add_tsum_nat_add n hf
  rw [htail.tsum_eq] at hsplit
  have hbd : (fermiNormalizedDyadicJump N c b (Nat.log 2 N + 1))^2 ≤
      ∑ k ∈ Finset.range n, (fermiNormalizedDyadicJump N c b (a + k))^2 := by
    have hh := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range n) =>
        sq_nonneg (fermiNormalizedDyadicJump N c b (a + k)))
      (show n - 1 ∈ Finset.range n by simp only [Finset.mem_range]; omega)
    rw [show a + (n - 1) = Nat.log 2 N + 1 by omega] at hh
    exact hh
  have hmass := fermiNormalizedDyadicSieve_terminal_mass_bound N c hb a n M hM
  dsimp only at hmass
  have hterm : fermiNormalizedDyadicSieve N c b (a + n) =
      fermiNormalizedDyadicJump N c b (Nat.log 2 N + 1) := by
    rw [hn]
    simpa only [Nat.add_assoc] using
      (fermiNormalizedDyadicJump_depth_boundary N c hb).symm
  rw [hterm] at hmass
  have hcoef : 0 ≤ M * (M + 1) * lam * n + (4 / 3 : ℝ) * M * lam := by positivity
  have hbound := mul_le_mul_of_nonneg_left hbd hcoef
  dsimp only [lam] at hbound
  rw [← hsplit]
  nlinarith only [hmass, hbound]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
