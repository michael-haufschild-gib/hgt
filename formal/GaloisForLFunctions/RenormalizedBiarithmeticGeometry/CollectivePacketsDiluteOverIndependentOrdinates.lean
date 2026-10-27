import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import GaloisForLFunctions.MultiplicativePositivityGeometry.ExactFejerBarrier

/-!
# Collective packets dilute over independent ordinates

A *positive packet* on a family of ordinates `ω_j` is a nonnegative almost-periodic polynomial
`P(t) = a_0 + Σ_j a_j cos(ω_j t) ≥ 0`: the constant `a_0` is the pole share it pays, the `a_j` are
what it buys at the ordinates. Coupling many ordinates in one packet is the collective
amortization proposed for clouds of off-line companions. Whether it amortizes depends only on the
arithmetic of the cloud.

* **Kronecker dilution** (`sum_abs_le_of_packet_nonneg`). If the ordinates are linearly independent
  over `ℚ`, then `Σ_j |a_j| ≤ a_0`: the whole cloud buys at most the pole share, so each of `K`
  ordinates gets `a_0/K` on average. The bound is sharp (`packet_nonneg_of_sum_abs_le`). Proof:
  Kronecker's theorem puts every `cos(ω_j t)` near `−sign(a_j)` at one time `t`.
* **Peak-to-mean** (`packet_peak_le_two_mul`): an independent packet never exceeds twice its pole
  share at `t = 0`.
* **Harmonic concentration** (`exists_harmonic_packet`). On the harmonic ordinates
  `γ, 2γ, …, Mγ` the Fejér packet `|Σ_{j ≤ M} e^{ijγt}|²` has pole share `M + 1` and buys
  `M(M + 1)`: `M` times the pole share.

* **The height law** (`sum_le_height_mul_of_packet_nonneg`). For a cloud made of harmonic
  progressions `g_i, …, M g_i` along independent generators, the total purchase is at most `M`
  times the pole share, whatever the number of generators: the packet is nonnegative on the
  diagonal of the torus (Kronecker), and the quadrature over `M + 1` equally spaced diagonal nodes
  kills every harmonic of order `≤ M`.

* **Generated clouds** (`sum_le_height_mul_of_generated_packet`). More generally, if the ordinates
  are nonnegative integer combinations `Σ_i n_{ji} g_i` of independent generators with heights
  `1 ≤ Σ_i n_{ji} ≤ M`, the total purchase is at most `M` times the pole share.

So collective amortization exists only through arithmetic relations among the ordinates, and its
size is the maximal height of the cloud over a basis of independent generators. A cloud
of companions with independent ordinates is worse than a single ordinate (MPG
`multiFrequency_purchase_le_two`); only commensurable clouds can be amortized.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

/-- `|cos x − cos y|` is bounded by the distance of the unit characters. -/
theorem abs_cos_sub_cos_le (x y : ℝ) :
    |Real.cos x - Real.cos y| ≤
      ‖Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I)‖ := by
  have h := Complex.abs_re_le_norm
    (Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I))
  rwa [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at h

/-- **Kronecker dilution.** A nonnegative packet on `ℚ`-independent ordinates buys in total at
most its pole share: `Σ_j |a_j| ≤ a_0`. -/
theorem sum_abs_le_of_packet_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ι → ℝ}
    (hind : LinearIndependent ℚ ω) (a₀ : ℝ) (a : ι → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos (ω j * t)) : ∑ j, |a j| ≤ a₀ := by
  set S := ∑ j, |a j|
  -- Target phases: `cos θ_j = −sign(a_j)`.
  set θ : ι → ℝ := fun j => if 0 ≤ a j then Real.pi else 0
  have hθ : ∀ j, a j * Real.cos (θ j) = -|a j| := fun j => by
    simp only [θ]
    split_ifs with h
    · rw [Real.cos_pi, abs_of_nonneg h]; ring
    · rw [Real.cos_zero, abs_of_neg (not_le.mp h)]; ring
  -- For every `ε > 0`, `0 ≤ a₀ − (1 − ε) S`.
  have hε : ∀ ε : ℝ, 0 < ε → (1 - ε) * S ≤ a₀ := by
    intro ε hεpos
    obtain ⟨t, ht⟩ := kronecker_approx hind θ hεpos
    have hj : ∀ j, a j * Real.cos (ω j * t) ≤ -|a j| + |a j| * ε := by
      intro j
      have hcos : |Real.cos (ω j * t) - Real.cos (θ j)| ≤ ε := by
        refine (abs_cos_sub_cos_le _ _).trans ?_
        have := (ht j).le
        simpa [expChar] using this
      have h1 : a j * Real.cos (ω j * t) - a j * Real.cos (θ j) ≤ |a j| * ε := by
        rw [← mul_sub]
        calc a j * (Real.cos (ω j * t) - Real.cos (θ j))
            ≤ |a j * (Real.cos (ω j * t) - Real.cos (θ j))| := le_abs_self _
          _ = |a j| * |Real.cos (ω j * t) - Real.cos (θ j)| := abs_mul _ _
          _ ≤ |a j| * ε := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      linarith [hθ j]
    have hsum : ∑ j, a j * Real.cos (ω j * t) ≤ ∑ j, (-|a j| + |a j| * ε) :=
      sum_le_sum fun j _ => hj j
    rw [sum_add_distrib, sum_neg_distrib, ← sum_mul] at hsum
    have := hP t
    linarith
  have hS0 : 0 ≤ S := sum_nonneg fun j _ => abs_nonneg (a j)
  by_contra hlt
  rw [not_le] at hlt
  rcases hS0.lt_or_eq with hSpos | hSzero
  · have h := hε ((S - a₀) / (2 * S)) (div_pos (by linarith) (by positivity))
    have heq : (1 - (S - a₀) / (2 * S)) * S = (S + a₀) / 2 := by field_simp; ring
    rw [heq] at h
    linarith
  · have h := hε 1 one_pos
    rw [← hSzero] at hlt
    linarith

/-- The bound is attained: any packet with `Σ_j |a_j| ≤ a_0` is nonnegative. -/
theorem packet_nonneg_of_sum_abs_le {ι : Type*} [Fintype ι] (ω : ι → ℝ) (a₀ : ℝ) (a : ι → ℝ)
    (h : ∑ j, |a j| ≤ a₀) (t : ℝ) : 0 ≤ a₀ + ∑ j, a j * Real.cos (ω j * t) := by
  have hj : ∀ j, -|a j| ≤ a j * Real.cos (ω j * t) := fun j => by
    have h1 : |a j * Real.cos (ω j * t)| ≤ |a j| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    linarith [neg_abs_le (a j * Real.cos (ω j * t))]
  have := sum_le_sum fun j (_ : j ∈ univ) => hj j
  rw [sum_neg_distrib] at this
  linarith

/-- **Peak-to-mean.** A nonnegative packet on independent ordinates is at most twice its pole share
at `t = 0`. -/
theorem packet_peak_le_two_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : ι → ℝ}
    (hind : LinearIndependent ℚ ω) (a₀ : ℝ) (a : ι → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos (ω j * t)) :
    a₀ + ∑ j, a j ≤ 2 * a₀ := by
  have h := sum_abs_le_of_packet_nonneg hind a₀ a hP
  have := sum_le_sum fun j (_ : j ∈ univ) => le_abs_self (a j)
  linarith

/-- **Harmonic concentration.** On the harmonic ordinates `γ, …, Mγ` the Fejér packet has pole
share `M + 1`, is nonnegative, and buys `M(M + 1)` in total. -/
theorem exists_harmonic_packet (M : ℕ) :
    ∃ a : ℕ → ℝ, a 0 = M + 1 ∧
      (∀ θ : ℝ, 0 ≤ ∑ k ∈ range (M + 1), a k * Real.cos (k * θ)) ∧
      ∑ k ∈ range (M + 1), a k = (M + 1) ^ 2 := by
  set a := ArithmeticCastelnuovoSeveri.fejerAutoCoeff M (fun _ => 1)
  refine ⟨a, ?_, fun θ => ?_, ?_⟩
  · simp only [a]
    rw [MultiplicativePositivityGeometry.fejerAutoCoeff_zero_eq]
    simp
  · exact ArithmeticCastelnuovoSeveri.cosinePolynomial_fejerAutoCoeff_nonneg M _ θ
  · have h := ArithmeticCastelnuovoSeveri.cosinePolynomial_fejerAutoCoeff M (fun _ => 1) 0
    simp [HTGeometry.cosinePolynomial] at h
    linarith

/-- **Dilution versus concentration.** Over independent ordinates the total purchase is at most the
pole share; over `M` harmonic ordinates it can be `M` times the pole share. -/
theorem harmonic_purchase_eq (M : ℕ) :
    ∃ a : ℕ → ℝ, (∀ θ : ℝ, 0 ≤ ∑ k ∈ range (M + 1), a k * Real.cos (k * θ)) ∧
      ∑ k ∈ (range (M + 1)).erase 0, a k = M * a 0 := by
  obtain ⟨a, h0, hnn, hsum⟩ := exists_harmonic_packet M
  refine ⟨a, hnn, ?_⟩
  have := sum_erase_add (range (M + 1)) a (mem_range.mpr (Nat.succ_pos M))
  rw [h0]
  rw [hsum, h0] at this
  linarith

/-! ### Mixed clouds: the height law -/

/-- Powers of points of the closed unit disc: `‖u^k − v^k‖ ≤ k ‖u − v‖`. -/
theorem norm_pow_sub_pow_le {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : ℕ) :
    ‖u ^ k - v ^ k‖ ≤ k * ‖u - v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : u ^ (k + 1) - v ^ (k + 1) = u ^ k * (u - v) + (u ^ k - v ^ k) * v := by ring
    rw [h]
    calc ‖u ^ k * (u - v) + (u ^ k - v ^ k) * v‖
        ≤ ‖u ^ k‖ * ‖u - v‖ + ‖u ^ k - v ^ k‖ * ‖v‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ‖u - v‖ + (k * ‖u - v‖) * 1 := by
          gcongr
          · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu
      _ = ((k + 1 : ℕ) : ℝ) * ‖u - v‖ := by push_cast; ring

/-- A packet on harmonic progressions along independent generators is nonnegative on the diagonal
of the torus: `a₀ + Σ_{i,k} a_{ik} cos((k+1)θ) ≥ 0` for every `θ`. -/
theorem diagonal_nonneg_of_packet_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ι → ℝ}
    (hind : LinearIndependent ℚ g) (M : ℕ) (a₀ : ℝ) (a : ι → ℕ → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * g i * t))
    (θ : ℝ) : 0 ≤ a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ) := by
  set S : ℝ := ∑ i, ∑ k ∈ range M, |a i k|
  -- For every `ε`, the diagonal value is at least `−M ε S`.
  have hε : ∀ ε : ℝ, 0 < ε →
      -(M * ε * S) ≤ a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ) := by
    intro ε hεpos
    obtain ⟨t, ht⟩ := kronecker_approx hind (fun _ => θ) hεpos
    have hterm : ∀ i, ∀ k ∈ range M, a i k * Real.cos ((k + 1) * g i * t) ≤
        a i k * Real.cos ((k + 1) * θ) + |a i k| * (M * ε) := by
      intro i k hk
      have hkM : ((k : ℝ) + 1) ≤ M := by
        have := mem_range.mp hk; exact_mod_cast this
      have hcos : |Real.cos ((k + 1) * g i * t) - Real.cos ((k + 1) * θ)| ≤ M * ε := by
        refine (abs_cos_sub_cos_le _ _).trans ?_
        have e1 : Complex.exp ((((k + 1) * g i * t : ℝ)) * Complex.I) =
            (expChar (g i) t) ^ (k + 1) := by
          rw [expChar, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
        have e2 : Complex.exp ((((k + 1) * θ : ℝ)) * Complex.I) =
            (Complex.exp ((θ : ℝ) * Complex.I)) ^ (k + 1) := by
          rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
        rw [e1, e2]
        refine (norm_pow_sub_pow_le (by rw [norm_expChar]) (by
          rw [Complex.norm_exp_ofReal_mul_I]) (k + 1)).trans ?_
        push_cast
        exact mul_le_mul hkM (ht i).le (norm_nonneg _) (by positivity)
      have h1 : a i k * Real.cos ((k + 1) * g i * t) - a i k * Real.cos ((k + 1) * θ) ≤
          |a i k| * (M * ε) := by
        rw [← mul_sub]
        calc a i k * (Real.cos ((k + 1) * g i * t) - Real.cos ((k + 1) * θ))
            ≤ |a i k * (Real.cos ((k + 1) * g i * t) - Real.cos ((k + 1) * θ))| := le_abs_self _
          _ = |a i k| * |Real.cos ((k + 1) * g i * t) - Real.cos ((k + 1) * θ)| := abs_mul _ _
          _ ≤ |a i k| * (M * ε) := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
      linarith
    have hsum : ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * g i * t) ≤
        ∑ i, ∑ k ∈ range M, (a i k * Real.cos ((k + 1) * θ) + |a i k| * (M * ε)) :=
      sum_le_sum fun i _ => sum_le_sum fun k hk => hterm i k hk
    have hsplit : ∑ i, ∑ k ∈ range M, (a i k * Real.cos ((k + 1) * θ) + |a i k| * (M * ε)) =
        ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ) + M * ε * S := by
      simp only [sum_add_distrib, ← sum_mul, S]
      ring
    have := hP t
    linarith
  by_contra hneg
  rw [not_le] at hneg
  set Q := a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ)
  have hS : 0 ≤ S := sum_nonneg fun i _ => sum_nonneg fun k _ => abs_nonneg _
  have hpos : 0 < (M : ℝ) * S + 1 := by positivity
  have h := hε (-Q / (2 * ((M : ℝ) * S + 1))) (div_pos (by linarith) (by positivity))
  have h2 : (M : ℝ) * (-Q / (2 * ((M : ℝ) * S + 1))) * S ≤ -Q / 2 := by
    rw [show (M : ℝ) * (-Q / (2 * ((M : ℝ) * S + 1))) * S =
      (-Q / 2) * ((M * S) / (M * S + 1)) by field_simp]
    have : (M : ℝ) * S / (M * S + 1) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    nlinarith
  linarith

/-- **The height law.** A nonnegative packet on harmonic progressions `g_i, 2g_i, …, M g_i` along
`ℚ`-independent generators `g_i` buys in total at most `M` times its pole share, however many
generators the cloud has. At `M = 1` this is Kronecker dilution; on a single generator the Fejér
packet attains it (`harmonic_purchase_eq`). -/
theorem sum_le_height_mul_of_packet_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ι → ℝ}
    (hind : LinearIndependent ℚ g) (M : ℕ) (a₀ : ℝ) (a : ι → ℕ → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * g i * t)) :
    ∑ i, ∑ k ∈ range M, a i k ≤ M * a₀ := by
  set θ : ℕ → ℝ := fun j => 2 * j * (Real.pi / (M + 1 : ℕ))
  have hQ := fun j => diagonal_nonneg_of_packet_nonneg hind M a₀ a hP (θ j)
  -- The quadrature over the `M + 1` nodes kills every harmonic of order `1, …, M`.
  have hquad : ∀ k ∈ range M, ∑ j ∈ range (M + 1), Real.cos ((k + 1) * θ j) = 0 := by
    intro k hk
    have h := MultiplicativePositivityGeometry.sum_cos_progression_eq_zero 0
      (N := M + 1) (k := k + 1) (by omega) (by have := mem_range.mp hk; omega)
    refine Eq.trans (sum_congr rfl fun j _ => ?_) h
    simp only [θ, zero_add]
    congr 1
    push_cast
    ring
  have htotal : ∑ j ∈ range (M + 1), (a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ j)) =
      (M + 1) * a₀ := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm]
    have : ∑ i, ∑ j ∈ range (M + 1), ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ j) = 0 := by
      refine sum_eq_zero fun i _ => ?_
      rw [sum_comm]
      refine sum_eq_zero fun k hk => ?_
      rw [← mul_sum, hquad k hk, mul_zero]
    rw [this]
    push_cast
    ring
  -- The node `θ = 0` is one of the nonnegative terms.
  have h0 : a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ 0) ≤
      ∑ j ∈ range (M + 1), (a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ j)) :=
    single_le_sum (f := fun j => a₀ + ∑ i, ∑ k ∈ range M, a i k * Real.cos ((k + 1) * θ j))
      (fun j _ => hQ j) (mem_range.mpr (Nat.succ_pos M))
  simp only [θ, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one] at h0
  rw [htotal] at h0
  linarith

/-! ### Clouds generated by independent ordinates -/

/-- Products of powers of points of the closed unit disc:
`‖Π u_i^{n_i} − Π v_i^{n_i}‖ ≤ Σ n_i ‖u_i − v_i‖`. -/
theorem norm_prod_pow_sub_prod_pow_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {u v : ι → ℂ}
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (n : ι → ℕ) :
    ‖∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i‖ ≤ ∑ i ∈ s, (n i : ℝ) * ‖u i - v i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    have h : u a ^ n a * ∏ i ∈ s, u i ^ n i - v a ^ n a * ∏ i ∈ s, v i ^ n i =
        u a ^ n a * (∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i) +
          (u a ^ n a - v a ^ n a) * ∏ i ∈ s, v i ^ n i := by ring
    have hua : ‖u a ^ n a‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu a)
    have hvs : ‖∏ i ∈ s, v i ^ n i‖ ≤ 1 := by
      rw [norm_prod]
      exact prod_le_one (fun i _ => norm_nonneg _) fun i _ => by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hv i)
    rw [h]
    calc ‖u a ^ n a * (∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i) +
          (u a ^ n a - v a ^ n a) * ∏ i ∈ s, v i ^ n i‖
        ≤ ‖u a ^ n a‖ * ‖∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i‖ +
            ‖u a ^ n a - v a ^ n a‖ * ‖∏ i ∈ s, v i ^ n i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ∑ i ∈ s, (n i : ℝ) * ‖u i - v i‖ + (n a * ‖u a - v a‖) * 1 := by
          gcongr
          exact norm_pow_sub_pow_le (hu a) (hv a) (n a)
      _ = (n a : ℝ) * ‖u a - v a‖ + ∑ i ∈ s, (n i : ℝ) * ‖u i - v i‖ := by ring

/-- `e^{i (Σ n_i x_i)} = Π (e^{i x_i})^{n_i}`. -/
theorem exp_sum_eq_prod_pow {ι : Type*} [Fintype ι] (n : ι → ℕ) (x : ι → ℝ) :
    Complex.exp (((∑ i, (n i : ℝ) * x i : ℝ)) * Complex.I) =
      ∏ i, Complex.exp (((x i : ℝ)) * Complex.I) ^ n i := by
  rw [show (((∑ i, (n i : ℝ) * x i : ℝ)) * Complex.I) =
      ∑ i, (n i : ℂ) * ((x i : ℂ) * Complex.I) by push_cast; rw [sum_mul]; congr 1; ext i; ring,
    Complex.exp_sum]
  exact prod_congr rfl fun i _ => by rw [Complex.exp_nat_mul]

/-- **The height law for generated clouds.** Let the ordinates be nonnegative integer combinations
`ω_j = Σ_i n_{ji} g_i` of `ℚ`-independent generators, with heights `1 ≤ Σ_i n_{ji} ≤ M`. A
nonnegative packet on them buys in total at most `M` times its pole share. -/
theorem sum_le_height_mul_of_generated_packet {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {g : ι → ℝ} (hind : LinearIndependent ℚ g) (n : κ → ι → ℕ) (M : ℕ)
    (hh : ∀ j, 1 ≤ ∑ i, n j i ∧ ∑ i, n j i ≤ M) (a₀ : ℝ) (a : κ → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t)) :
    ∑ j, a j ≤ M * a₀ := by
  set h : κ → ℕ := fun j => ∑ i, n j i
  -- Diagonal positivity: `a₀ + Σ_j a_j cos(h_j θ) ≥ 0` for every `θ`.
  have hdiag : ∀ θ : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ) := by
    intro θ
    set S : ℝ := ∑ j, |a j|
    have hε : ∀ ε : ℝ, 0 < ε → -(M * ε * S) ≤ a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ) := by
      intro ε hεpos
      obtain ⟨t, ht⟩ := kronecker_approx hind (fun _ => θ) hεpos
      have hterm : ∀ j, a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t) ≤
          a j * Real.cos ((h j : ℝ) * θ) + |a j| * (M * ε) := by
        intro j
        have hcos : |Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ)| ≤
            M * ε := by
          refine (abs_cos_sub_cos_le _ _).trans ?_
          have e1 : Complex.exp ((((∑ i, (n j i : ℝ) * g i) * t : ℝ)) * Complex.I) =
              ∏ i, (expChar (g i) t) ^ n j i := by
            rw [show ((∑ i, (n j i : ℝ) * g i) * t : ℝ) = ∑ i, (n j i : ℝ) * (g i * t) by
              rw [sum_mul]; exact sum_congr rfl fun i _ => by ring, exp_sum_eq_prod_pow]
            rfl
          have e2 : Complex.exp ((((h j : ℝ) * θ : ℝ)) * Complex.I) =
              ∏ i, (Complex.exp ((θ : ℝ) * Complex.I)) ^ n j i := by
            rw [show ((h j : ℝ) * θ : ℝ) = ∑ i, (n j i : ℝ) * θ by
              simp only [h]; push_cast; rw [sum_mul], exp_sum_eq_prod_pow]
          rw [e1, e2]
          refine (norm_prod_pow_sub_prod_pow_le univ (fun i => by rw [norm_expChar])
            (fun i => by rw [Complex.norm_exp_ofReal_mul_I]) (n j)).trans ?_
          calc ∑ i, (n j i : ℝ) * ‖expChar (g i) t - Complex.exp ((θ : ℝ) * Complex.I)‖
              ≤ ∑ i, (n j i : ℝ) * ε :=
                sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ht i).le (Nat.cast_nonneg _)
            _ = (h j : ℝ) * ε := by simp only [h]; push_cast; rw [sum_mul]
            _ ≤ M * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast (hh j).2) hεpos.le
        have h1 : a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t) -
            a j * Real.cos ((h j : ℝ) * θ) ≤ |a j| * (M * ε) := by
          rw [← mul_sub]
          calc a j * (Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ))
              ≤ |a j * (Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ))| :=
                le_abs_self _
            _ = |a j| * |Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ)| :=
                abs_mul _ _
            _ ≤ |a j| * (M * ε) := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
        linarith
      have hsum := sum_le_sum fun j (_ : j ∈ univ) => hterm j
      rw [sum_add_distrib, ← sum_mul] at hsum
      have := hP t
      have hS : (∑ j, |a j|) * (M * ε) = M * ε * S := by simp only [S]; ring
      linarith
    by_contra hneg
    rw [not_le] at hneg
    set Q := a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ)
    have hS : 0 ≤ S := sum_nonneg fun j _ => abs_nonneg _
    have hpos : 0 < (M : ℝ) * S + 1 := by positivity
    have h' := hε (-Q / (2 * ((M : ℝ) * S + 1))) (div_pos (by linarith) (by positivity))
    have h2 : (M : ℝ) * (-Q / (2 * ((M : ℝ) * S + 1))) * S ≤ -Q / 2 := by
      rw [show (M : ℝ) * (-Q / (2 * ((M : ℝ) * S + 1))) * S =
        (-Q / 2) * ((M * S) / (M * S + 1)) by field_simp]
      have : (M : ℝ) * S / (M * S + 1) ≤ 1 := by rw [div_le_one hpos]; linarith
      nlinarith
    linarith
  -- Quadrature over the `M + 1` diagonal nodes.
  set θ : ℕ → ℝ := fun l => 2 * l * (Real.pi / (M + 1 : ℕ))
  have hquad : ∀ j, ∑ l ∈ range (M + 1), Real.cos ((h j : ℝ) * θ l) = 0 := by
    intro j
    have hq := MultiplicativePositivityGeometry.sum_cos_progression_eq_zero 0
      (N := M + 1) (k := h j) (hh j).1 (Nat.lt_succ_of_le (hh j).2)
    refine Eq.trans (sum_congr rfl fun l _ => ?_) hq
    simp only [θ, zero_add]
    congr 1
    push_cast
    ring
  have htotal : ∑ l ∈ range (M + 1), (a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ l)) =
      (M + 1) * a₀ := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm]
    have : ∑ j, ∑ l ∈ range (M + 1), a j * Real.cos ((h j : ℝ) * θ l) = 0 :=
      sum_eq_zero fun j _ => by rw [← mul_sum, hquad j, mul_zero]
    rw [this]
    push_cast
    ring
  have h0 : a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ 0) ≤
      ∑ l ∈ range (M + 1), (a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ l)) :=
    single_le_sum (f := fun l => a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ l))
      (fun l _ => hdiag (θ l)) (mem_range.mpr (Nat.succ_pos M))
  simp only [θ, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one] at h0
  rw [htotal] at h0
  linarith

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
