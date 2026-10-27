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

So collective amortization exists only through arithmetic relations among the ordinates, and its
size is the length of the longest harmonic progression in the cloud. A cloud
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
        refine (norm_pow_sub_pow_le (by simp [expChar]) (by
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

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
