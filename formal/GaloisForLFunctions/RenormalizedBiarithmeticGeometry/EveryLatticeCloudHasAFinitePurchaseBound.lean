import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.CollectivePacketsDiluteOverIndependentOrdinates
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheHeckeMomentProblem

/-!
# Every lattice cloud has a finite purchase bound

A cloud of ordinates in the lattice of `ℚ`-independent generators `g_1, …, g_d`,
`ω_j = Σ_i n_{ji} g_i` with `n_{ji} ∈ ℤ`, may contain relations of mixed sign such as
`g_1 − g_2`. Weight the generators by integers `m_i`: the ordinate `ω_j` gets the height
`h_j = Σ_i n_{ji} m_i`.

* **Weighted height law** (`sum_le_height_mul_of_weighted_packet`). If every height satisfies
  `1 ≤ |h_j| ≤ M`, a nonnegative packet on the cloud buys at most `M` times its pole share. Proof:
  Kronecker puts `(g_i t)` near `(m_i θ)` on the torus, so the packet is nonnegative along the
  weighted diagonal `θ ↦ a₀ + Σ_j a_j cos(h_j θ)`, and quadrature over `M + 1` nodes kills every
  height `1 ≤ |h| ≤ M`.
* **Admissible weights exist** (`exists_weight_heights_ne_zero`). For nonzero coefficient vectors
  the heights along `m_i = t^i` are nonzero polynomials in `t`, so all but finitely many `t ∈ ℕ`
  give nonzero heights.
* **Finite purchase** (`exists_purchase_bound`). Every finite cloud of nonzero lattice ordinates has
  a constant `M` with `Σ_j a_j ≤ M a₀` for every nonnegative packet on it.

Positive packets therefore never amortize without bound; the bound is the minimal maximal height
over admissible weightings.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

/-- Integer powers of unit complex numbers: `‖u^n − v^n‖ ≤ |n| ‖u − v‖`. -/
theorem norm_zpow_sub_zpow_le {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (n : ℤ) :
    ‖u ^ n - v ^ n‖ ≤ |(n : ℝ)| * ‖u - v‖ := by
  rcases n with k | k
  · have h := norm_pow_sub_pow_le hu.le hv.le k
    simpa using h
  · have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have hv0 : v ≠ 0 := by rintro rfl; simp at hv
    have hinv : ∀ w : ℂ, ‖w‖ = 1 → w⁻¹ = (starRingEnd ℂ) w := fun w hw => by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]; simp
    rw [zpow_negSucc, zpow_negSucc, ← inv_pow, ← inv_pow, hinv u hu, hinv v hv]
    have h := norm_pow_sub_pow_le (u := (starRingEnd ℂ) u) (v := (starRingEnd ℂ) v)
      (by rw [Complex.norm_conj, hu]) (by rw [Complex.norm_conj, hv]) (k + 1)
    rw [← map_sub, Complex.norm_conj] at h
    refine h.trans (le_of_eq ?_)
    simp only [Int.cast_negSucc]
    rw [abs_neg]
    push_cast
    rw [abs_of_nonneg (by positivity)]

/-- Products of integer powers of unit complex numbers. -/
theorem norm_prod_zpow_sub_prod_zpow_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {u v : ι → ℂ}
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (n : ι → ℤ) :
    ‖∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i‖ ≤ ∑ i ∈ s, |(n i : ℝ)| * ‖u i - v i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    have h : u a ^ n a * ∏ i ∈ s, u i ^ n i - v a ^ n a * ∏ i ∈ s, v i ^ n i =
        u a ^ n a * (∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i) +
          (u a ^ n a - v a ^ n a) * ∏ i ∈ s, v i ^ n i := by ring
    have hua : ‖u a ^ n a‖ = 1 := by rw [norm_zpow, hu a, one_zpow]
    have hvs : ‖∏ i ∈ s, v i ^ n i‖ = 1 := by
      rw [norm_prod]; exact prod_eq_one fun i _ => by rw [norm_zpow, hv i, one_zpow]
    rw [h]
    calc ‖u a ^ n a * (∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i) +
          (u a ^ n a - v a ^ n a) * ∏ i ∈ s, v i ^ n i‖
        ≤ ‖u a ^ n a‖ * ‖∏ i ∈ s, u i ^ n i - ∏ i ∈ s, v i ^ n i‖ +
            ‖u a ^ n a - v a ^ n a‖ * ‖∏ i ∈ s, v i ^ n i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ 1 * ∑ i ∈ s, |(n i : ℝ)| * ‖u i - v i‖ + (|(n a : ℝ)| * ‖u a - v a‖) * 1 := by
          rw [hua, hvs]
          gcongr
          exact norm_zpow_sub_zpow_le (hu a) (hv a) (n a)
      _ = |(n a : ℝ)| * ‖u a - v a‖ + ∑ i ∈ s, |(n i : ℝ)| * ‖u i - v i‖ := by ring

/-- `e^{i (Σ n_i x_i)} = Π (e^{i x_i})^{n_i}` for integer coefficients. -/
theorem exp_sum_eq_prod_zpow {ι : Type*} [Fintype ι] (n : ι → ℤ) (x : ι → ℝ) :
    Complex.exp (((∑ i, (n i : ℝ) * x i : ℝ)) * Complex.I) =
      ∏ i, Complex.exp (((x i : ℝ)) * Complex.I) ^ n i := by
  rw [show (((∑ i, (n i : ℝ) * x i : ℝ)) * Complex.I) =
      ∑ i, (n i : ℂ) * ((x i : ℂ) * Complex.I) by push_cast; rw [sum_mul]; congr 1; ext i; ring,
    Complex.exp_sum]
  exact prod_congr rfl fun i _ => by rw [Complex.exp_int_mul]

/-- **The weighted height law.** -/
theorem sum_le_height_mul_of_weighted_packet {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {g : ι → ℝ} (hind : LinearIndependent ℚ g) (n : κ → ι → ℤ) (m : ι → ℤ) (M : ℕ)
    (hh : ∀ j, 1 ≤ |∑ i, n j i * m i| ∧ |∑ i, n j i * m i| ≤ M) (a₀ : ℝ) (a : κ → ℝ)
    (hP : ∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t)) :
    ∑ j, a j ≤ M * a₀ := by
  set h : κ → ℤ := fun j => ∑ i, n j i * m i
  set B : ℝ := ∑ j, ∑ i, |(n j i : ℝ)|
  -- Positivity along the weighted diagonal `θ_i = m_i θ`.
  have hdiag : ∀ θ : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ) := by
    intro θ
    set S : ℝ := ∑ j, |a j|
    have hε : ∀ ε : ℝ, 0 < ε → -(B * ε * S) ≤ a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ) := by
      intro ε hεpos
      obtain ⟨t, ht⟩ := kronecker_approx hind (fun i => (m i : ℝ) * θ) hεpos
      have hBj : ∀ j, ∑ i, |(n j i : ℝ)| ≤ B := fun j =>
        single_le_sum (f := fun j => ∑ i, |(n j i : ℝ)|)
          (fun j _ => sum_nonneg fun i _ => abs_nonneg _) (mem_univ j)
      have hterm : ∀ j, a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t) ≤
          a j * Real.cos ((h j : ℝ) * θ) + |a j| * (B * ε) := by
        intro j
        have hcos : |Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ)| ≤
            B * ε := by
          refine (abs_cos_sub_cos_le _ _).trans ?_
          have e1 : Complex.exp ((((∑ i, (n j i : ℝ) * g i) * t : ℝ)) * Complex.I) =
              ∏ i, (expChar (g i) t) ^ n j i := by
            rw [show ((∑ i, (n j i : ℝ) * g i) * t : ℝ) = ∑ i, (n j i : ℝ) * (g i * t) by
              rw [sum_mul]; exact sum_congr rfl fun i _ => by ring, exp_sum_eq_prod_zpow]
            rfl
          have e2 : Complex.exp ((((h j : ℝ) * θ : ℝ)) * Complex.I) =
              ∏ i, (Complex.exp ((((m i : ℝ) * θ : ℝ)) * Complex.I)) ^ n j i := by
            rw [show ((h j : ℝ) * θ : ℝ) = ∑ i, (n j i : ℝ) * ((m i : ℝ) * θ) by
              simp only [h]; push_cast; rw [sum_mul]; exact sum_congr rfl fun i _ => by ring,
              exp_sum_eq_prod_zpow]
          rw [e1, e2]
          refine (norm_prod_zpow_sub_prod_zpow_le univ (fun i => norm_expChar _ _)
            (fun i => by rw [Complex.norm_exp_ofReal_mul_I]) (n j)).trans ?_
          calc ∑ i, |(n j i : ℝ)| *
                ‖expChar (g i) t - Complex.exp ((((m i : ℝ) * θ : ℝ)) * Complex.I)‖
              ≤ ∑ i, |(n j i : ℝ)| * ε :=
                sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ht i).le (abs_nonneg _)
            _ = (∑ i, |(n j i : ℝ)|) * ε := by rw [sum_mul]
            _ ≤ B * ε := mul_le_mul_of_nonneg_right (hBj j) hεpos.le
        have h1 : a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t) -
            a j * Real.cos ((h j : ℝ) * θ) ≤ |a j| * (B * ε) := by
          rw [← mul_sub]
          calc a j * (Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ))
              ≤ |a j * (Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ))| :=
                le_abs_self _
            _ = |a j| * |Real.cos ((∑ i, (n j i : ℝ) * g i) * t) - Real.cos ((h j : ℝ) * θ)| :=
                abs_mul _ _
            _ ≤ |a j| * (B * ε) := mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
        linarith
      have hsum := sum_le_sum fun j (_ : j ∈ univ) => hterm j
      rw [sum_add_distrib, ← sum_mul] at hsum
      have := hP t
      have hS : (∑ j, |a j|) * (B * ε) = B * ε * S := by simp only [S]; ring
      linarith
    by_contra hneg
    rw [not_le] at hneg
    set Q := a₀ + ∑ j, a j * Real.cos ((h j : ℝ) * θ)
    have hS : 0 ≤ S := sum_nonneg fun j _ => abs_nonneg _
    have hB : 0 ≤ B := sum_nonneg fun j _ => sum_nonneg fun i _ => abs_nonneg _
    have hpos : 0 < B * S + 1 := by positivity
    have h' := hε (-Q / (2 * (B * S + 1))) (div_pos (by linarith) (by positivity))
    have h2 : B * (-Q / (2 * (B * S + 1))) * S ≤ -Q / 2 := by
      rw [show B * (-Q / (2 * (B * S + 1))) * S = (-Q / 2) * ((B * S) / (B * S + 1)) by
        field_simp]
      have : B * S / (B * S + 1) ≤ 1 := by rw [div_le_one hpos]; linarith
      nlinarith
    linarith
  -- Quadrature over `M + 1` diagonal nodes; heights enter through `|h_j|`.
  set θ : ℕ → ℝ := fun l => 2 * l * (Real.pi / (M + 1 : ℕ))
  have hquad : ∀ j, ∑ l ∈ range (M + 1), Real.cos ((h j : ℝ) * θ l) = 0 := by
    intro j
    have habs : ∀ l, Real.cos ((h j : ℝ) * θ l) = Real.cos (((h j).natAbs : ℝ) * θ l) := by
      intro l
      rw [Nat.cast_natAbs, Int.cast_abs]
      rcases abs_choice ((h j : ℤ) : ℝ) with e | e <;> rw [e]
      rw [neg_mul, Real.cos_neg]
    have h1 : 1 ≤ (h j).natAbs := by
      have h' : (1 : ℤ) ≤ ((h j).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact (hh j).1
      exact_mod_cast h'
    have h2 : (h j).natAbs < M + 1 := by
      have h' : ((h j).natAbs : ℤ) ≤ M := by rw [Int.natCast_natAbs]; exact (hh j).2
      have : (h j).natAbs ≤ M := by exact_mod_cast h'
      omega
    have hq := MultiplicativePositivityGeometry.sum_cos_progression_eq_zero 0
      (N := M + 1) (k := (h j).natAbs) h1 h2
    rw [sum_congr rfl fun l _ => habs l]
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

/-- **Admissible weights exist.** For nonzero coefficient vectors on `Fin d`, some weighting
`m_i = t^i` with `t ∈ ℕ` makes every height nonzero. -/
theorem exists_weight_heights_ne_zero {d : ℕ} {κ : Type*} [Fintype κ] (n : κ → Fin d → ℤ)
    (hn : ∀ j, n j ≠ 0) : ∃ t : ℕ, ∀ j, ∑ i, n j i * (t : ℤ) ^ (i : ℕ) ≠ 0 := by
  classical
  -- Bad values of `t` are roots of the nonzero polynomials `Σ_i n_{ji} X^i`.
  set P : κ → Polynomial ℝ := fun j => coeffPoly fun i => (n j i : ℝ)
  have hP : ∀ j, P j ≠ 0 := fun j => coeffPoly_ne_zero (by
    intro h; apply hn j; funext i; have := congrFun h i; simpa using this)
  set bad : Finset ℝ := univ.biUnion fun j => (P j).roots.toFinset
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℝ) ∉ bad := by
    by_contra hall
    push Not at hall
    have hinj : Set.InjOn (fun t : ℕ => (t : ℝ)) (Set.univ : Set ℕ) :=
      fun a _ b _ h => Nat.cast_injective h
    exact Set.infinite_univ (α := ℕ) ((bad.finite_toSet).subset
      (fun x hx => by obtain ⟨t, -, rfl⟩ := hx; exact hall t) |>.of_finite_image hinj)
  refine ⟨t, fun j hj => ht ?_⟩
  simp only [bad, mem_biUnion, mem_univ, true_and, Multiset.mem_toFinset]
  refine ⟨j, (Polynomial.mem_roots (hP j)).mpr ?_⟩
  simp only [P, Polynomial.IsRoot, eval_coeffPoly, coeffEval]
  have := congrArg (fun z : ℤ => (z : ℝ)) hj
  push_cast at this
  exact this

/-- **Every lattice cloud has a finite purchase bound.** -/
theorem exists_purchase_bound {d : ℕ} {κ : Type*} [Fintype κ] {g : Fin d → ℝ}
    (hind : LinearIndependent ℚ g) (n : κ → Fin d → ℤ) (hn : ∀ j, n j ≠ 0) :
    ∃ M : ℕ, ∀ (a₀ : ℝ) (a : κ → ℝ),
      (∀ t : ℝ, 0 ≤ a₀ + ∑ j, a j * Real.cos ((∑ i, (n j i : ℝ) * g i) * t)) →
        ∑ j, a j ≤ M * a₀ := by
  classical
  obtain ⟨t, ht⟩ := exists_weight_heights_ne_zero n hn
  set m : Fin d → ℤ := fun i => (t : ℤ) ^ (i : ℕ)
  set M : ℕ := univ.sup fun j => (∑ i, n j i * m i).natAbs
  refine ⟨M, fun a₀ a hP => sum_le_height_mul_of_weighted_packet hind n m M (fun j => ?_) a₀ a hP⟩
  have hne : ∑ i, n j i * m i ≠ 0 := ht j
  have hle : (∑ i, n j i * m i).natAbs ≤ M := le_sup (f := fun j => (∑ i, n j i * m i).natAbs)
    (mem_univ j)
  rw [Int.abs_eq_natAbs]
  constructor
  · have : 0 < (∑ i, n j i * m i).natAbs := Int.natAbs_pos.mpr hne
    omega
  · exact_mod_cast hle

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
