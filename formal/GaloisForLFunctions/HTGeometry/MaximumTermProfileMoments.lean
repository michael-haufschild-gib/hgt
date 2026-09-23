import GaloisForLFunctions.HTGeometry.MaximumTermGaussianTail
import GaloisForLFunctions.HTGeometry.MeanIndexSharpAssembly

/-!
# The zeroth and second moments of the coefficient profile

The deviation series was the first moment.  The Wiman--Valiron estimate in profile form needs the
other two: the total mass, which controls the alignment defect, and the second moment, which enters
the Cauchy--Schwarz bound on the weighted misalignment.

Both split the same way as the first moment — a window of half-width `N` around the central index,
where the squared weight is at most `N^(2 : ℕ)`, and two tails on which the terms decay at rate `N/(4L)`
per unit of deviation.  The tail series are the shifted geometric series of orders `0` and `2`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-! ## Shifted geometric series -/

/-- The exponential decay rate written as a power. -/
private theorem exp_rate_pow' {L : ℝ} (hL : 0 < L) (N k : ℕ) :
    Real.exp (-((k : ℝ) * (N : ℝ) / (4 * L)))
      = Real.exp (-((N : ℝ) / (4 * L))) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp

/-- The shifted geometric series. -/
private theorem summable_shifted_geom {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    Summable fun j : ℕ => q ^ (N + 1 + j) := by
  refine ((summable_geometric_of_lt_one hq0.le hq1).mul_left (q ^ (N + 1))).congr fun j => ?_
  rw [← pow_add]

/-- The shifted geometric series with a squared weight. -/
private theorem summable_shifted_sq_weight {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    Summable fun j : ℕ => ((N : ℝ) + 1 + j) ^ (2 : ℕ) * q ^ (N + 1 + j) := by
  have h0 : Summable fun j : ℕ => q ^ j := summable_geometric_of_lt_one hq0.le hq1
  have h1 : Summable fun j : ℕ => (j : ℝ) * q ^ j := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have h2 : Summable fun j : ℕ => (j : ℝ) ^ (2 : ℕ) * q ^ j := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have hpoly : Summable fun j : ℕ => ((N : ℝ) + 1 + j) ^ (2 : ℕ) * q ^ j := by
    refine (((h0.mul_left (((N : ℝ) + 1) ^ (2 : ℕ))).add (h1.mul_left (2 * ((N : ℝ) + 1)))).add
      h2).congr fun j => ?_
    ring
  refine (hpoly.mul_left (q ^ (N + 1))).congr fun j => ?_
  rw [pow_add]
  ring

/-! ## The moments -/

set_option maxHeartbeats 400000 in
/-- **The total mass under Gaussian concentration.**  Outside a window of half-width `N` the terms
decay geometrically at rate `N/(4L)`, so the majorant is the window sum plus a geometric tail. -/
theorem coeffSum_le_gaussian
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    {N : ℕ} (hN0 : 0 < N) (hNK : (N : ℝ) ≤ 2 * L * H) (hNv : 2 * L * v₀ ≤ (N : ℝ))
    (hlipA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    (hlipB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {W : ℝ}
    (hW : ∑ n ∈ Finset.Ico (centralIndex a (Real.exp x) - N)
              (centralIndex a (Real.exp x) + N + 1), ‖a n‖ * Real.exp x ^ n ≤ W) :
    coeffSum a (Real.exp x)
      ≤ W + 2 * maxTerm a (Real.exp x)
            * ∑' j : ℕ, Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j) := by
  classical
  set r : ℝ := Real.exp x with hr
  have hrpos : 0 < r := Real.exp_pos x
  set v : ℕ := centralIndex a r with hv
  set μ : ℝ := maxTerm a r with hμdef
  have hμ : (0 : ℝ) ≤ μ := le_trans (term_nonneg a hrpos 0) (term_le_maxTerm ha hrpos 0)
  set q : ℝ := Real.exp (-((N : ℝ) / (4 * L))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
    linarith
  set T : ℕ → ℝ := fun n => ‖a n‖ * r ^ n with hT
  have hTnn : ∀ n, 0 ≤ T n := fun n => term_nonneg a hrpos n
  have hTsum : Summable T := summable_term ha hrpos
  set f : ℕ → ℝ := fun j => q ^ (N + 1 + j) with hf
  have hfsum : Summable f := summable_shifted_geom hq0 hq1 N
  have hfnn : ∀ j, 0 ≤ f j := fun j => pow_nonneg hq0.le _
  have hexp : ∀ j : ℕ, Real.exp (-(((N : ℝ) + 1 + j) * (N : ℝ) / (4 * L))) = q ^ (N + 1 + j) := by
    intro j
    have hcast : ((N + 1 + j : ℕ) : ℝ) = (N : ℝ) + 1 + j := by push_cast; ring
    rw [hq, ← exp_rate_pow' hL N (N + 1 + j), hcast]
  have hdecay_up : ∀ j : ℕ, T (j + (v + N + 1)) ≤ μ * f j := by
    intro j
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = j + (v + N + 1) := ⟨_, rfl⟩
    rw [← hn]
    have hk : ((N : ℝ) + 1 + j) = (n : ℝ) - (v : ℝ) := by rw [hn]; push_cast; ring
    have hkK : (N : ℝ) ≤ (n : ℝ) - (v : ℝ) := by
      rw [← hk]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hterm := term_le_maxTerm_exp_uniform_above (x := x) ha hn₀ hH hL hNpos hNK hNv hlipA
      (n := n) (k := (n : ℝ) - (v : ℝ)) rfl hkK
    rw [← hk] at hterm
    calc T n ≤ μ * Real.exp (-(((N : ℝ) + 1 + j) * (N : ℝ) / (4 * L))) := hterm
      _ = μ * f j := by rw [hexp j, hf]
  have hdecay_down : ∀ j : ℕ, j < v - N → T (v - N - 1 - j) ≤ μ * f j := by
    intro j hj
    have hvN : N < v := by omega
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = v - N - 1 - j := ⟨_, rfl⟩
    rw [← hn]
    have hle : N + 1 + j ≤ v := by omega
    have hnv : (n : ℝ) = (v : ℝ) - ((N : ℝ) + 1 + j) := by
      have hne : n = v - (N + 1 + j) := by omega
      rw [hne, Nat.cast_sub hle]
      push_cast
      ring
    have hk : ((N : ℝ) + 1 + j) = (v : ℝ) - (n : ℝ) := by rw [hnv]; ring
    have hkK : (N : ℝ) ≤ (v : ℝ) - (n : ℝ) := by
      rw [← hk]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hterm := term_le_maxTerm_exp_uniform_below (x := x) ha hn₀ hH hL hNpos hNK hNv hlipB
      (n := n) (k := (v : ℝ) - (n : ℝ)) rfl hkK
    rw [← hk] at hterm
    calc T n ≤ μ * Real.exp (-(((N : ℝ) + 1 + j) * (N : ℝ) / (4 * L))) := hterm
      _ = μ * f j := by rw [hexp j, hf]
  have hlow : ∑ n ∈ Finset.Ico 0 (v - N), T n ≤ μ * ∑' j : ℕ, f j := by
    rw [← Finset.range_eq_Ico]
    have hrefl : ∑ n ∈ Finset.range (v - N), T n
        = ∑ j ∈ Finset.range (v - N), T (v - N - 1 - j) :=
      (Finset.sum_range_reflect (fun n => T n) (v - N)).symm
    rw [hrefl]
    refine le_trans (Finset.sum_le_sum fun j hj => hdecay_down j (Finset.mem_range.mp hj)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Summable.sum_le_tsum _ (fun j _ => hfnn j) hfsum) hμ
  have hup : ∑' j : ℕ, T (j + (v + N + 1)) ≤ μ * ∑' j : ℕ, f j := by
    have hsumL : Summable fun j : ℕ => T (j + (v + N + 1)) :=
      (summable_nat_add_iff (v + N + 1)).mpr hTsum
    have hle := Summable.tsum_le_tsum hdecay_up hsumL (hfsum.mul_left μ)
    rwa [tsum_mul_left] at hle
  have hsplit := Summable.sum_add_tsum_nat_add (f := T) (v + N + 1) hTsum
  have hcons : (∑ n ∈ Finset.Ico 0 (v - N), T n) + ∑ n ∈ Finset.Ico (v - N) (v + N + 1), T n
      = ∑ n ∈ Finset.Ico 0 (v + N + 1), T n :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  calc coeffSum a r
      = ∑' n : ℕ, T n := rfl
    _ = (∑ n ∈ Finset.Ico 0 (v + N + 1), T n) + ∑' j : ℕ, T (j + (v + N + 1)) := by
        rw [← hsplit, Finset.range_eq_Ico]
    _ = (∑ n ∈ Finset.Ico 0 (v - N), T n) + (∑ n ∈ Finset.Ico (v - N) (v + N + 1), T n)
        + ∑' j : ℕ, T (j + (v + N + 1)) := by rw [hcons]
    _ ≤ μ * (∑' j : ℕ, f j) + W + μ * ∑' j : ℕ, f j := by gcongr
    _ = W + 2 * μ * ∑' j : ℕ, f j := by ring

set_option maxHeartbeats 400000 in
/-- **The second moment under Gaussian concentration.**  Inside the window the squared deviation is
at most `N^(2 : ℕ)`; outside it the geometric decay dominates the quadratic weight. -/
theorem tsum_index_sq_le_gaussian
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    {N : ℕ} (hN0 : 0 < N) (hNK : (N : ℝ) ≤ 2 * L * H) (hNv : 2 * L * v₀ ≤ (N : ℝ))
    (hlipA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    (hlipB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {W : ℝ}
    (hW : ∑ n ∈ Finset.Ico (centralIndex a (Real.exp x) - N)
              (centralIndex a (Real.exp x) + N + 1), ‖a n‖ * Real.exp x ^ n ≤ W) :
    ∑' n : ℕ, ((n : ℝ) - (centralIndex a (Real.exp x) : ℝ)) ^ (2 : ℕ)
        * (‖a n‖ * Real.exp x ^ n)
      ≤ (N : ℝ) ^ (2 : ℕ) * W
        + 2 * maxTerm a (Real.exp x)
            * ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ (2 : ℕ)
                * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j) := by
  classical
  set r : ℝ := Real.exp x with hr
  have hrpos : 0 < r := Real.exp_pos x
  set v : ℕ := centralIndex a r with hv
  set μ : ℝ := maxTerm a r with hμdef
  have hμ : (0 : ℝ) ≤ μ := le_trans (term_nonneg a hrpos 0) (term_le_maxTerm ha hrpos 0)
  set q : ℝ := Real.exp (-((N : ℝ) / (4 * L))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
    linarith
  set D : ℕ → ℝ := fun n => ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n) with hD
  have hDsum : Summable D := summable_index_deviation_sq ha hrpos v
  set f : ℕ → ℝ := fun j => ((N : ℝ) + 1 + j) ^ (2 : ℕ) * q ^ (N + 1 + j) with hf
  have hfsum : Summable f := summable_shifted_sq_weight hq0 hq1 N
  have hfnn : ∀ j, 0 ≤ f j := fun j => by
    have : (0 : ℝ) ≤ ((N : ℝ) + 1 + j) ^ (2 : ℕ) := sq_nonneg _
    exact mul_nonneg this (pow_nonneg hq0.le _)
  have hexp : ∀ j : ℕ, Real.exp (-(((N : ℝ) + 1 + j) * (N : ℝ) / (4 * L))) = q ^ (N + 1 + j) := by
    intro j
    have hcast : ((N + 1 + j : ℕ) : ℝ) = (N : ℝ) + 1 + j := by push_cast; ring
    rw [hq, ← exp_rate_pow' hL N (N + 1 + j), hcast]
  have hdecay_up : ∀ j : ℕ, D (j + (v + N + 1)) ≤ μ * f j := by
    intro j
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = j + (v + N + 1) := ⟨_, rfl⟩
    rw [← hn]
    have hk : ((N : ℝ) + 1 + j) = (n : ℝ) - (v : ℝ) := by rw [hn]; push_cast; ring
    have hkK : (N : ℝ) ≤ (n : ℝ) - (v : ℝ) := by
      rw [← hk]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hterm := term_le_maxTerm_exp_uniform_above (x := x) ha hn₀ hH hL hNpos hNK hNv hlipA
      (n := n) (k := (n : ℝ) - (v : ℝ)) rfl hkK
    rw [← hk] at hterm
    calc D n = ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n) := rfl
      _ = ((N : ℝ) + 1 + j) ^ (2 : ℕ) * (‖a n‖ * r ^ n) := by rw [hk]
      _ ≤ ((N : ℝ) + 1 + j) ^ (2 : ℕ)
          * (μ * Real.exp (-(((N : ℝ) + 1 + j) * (N : ℝ) / (4 * L)))) :=
          mul_le_mul_of_nonneg_left hterm (sq_nonneg _)
      _ = μ * f j := by rw [hexp j, hf]; ring
  have hdecay_down : ∀ j : ℕ, j < v - N → D (v - N - 1 - j) ≤ μ * f j := by
    intro j hj
    have hvN : N < v := by omega
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = v - N - 1 - j := ⟨_, rfl⟩
    rw [← hn]
    have hle : N + 1 + j ≤ v := by omega
    have hnv : (n : ℝ) = (v : ℝ) - ((N : ℝ) + 1 + j) := by
      have hne : n = v - (N + 1 + j) := by omega
      rw [hne, Nat.cast_sub hle]
      push_cast
      ring
    have hk : ((N : ℝ) + 1 + j) = (v : ℝ) - (n : ℝ) := by rw [hnv]; ring
    have hkK : (N : ℝ) ≤ (v : ℝ) - (n : ℝ) := by
      rw [← hk]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hterm := term_le_maxTerm_exp_uniform_below (x := x) ha hn₀ hH hL hNpos hNK hNv hlipB
      (n := n) (k := (v : ℝ) - (n : ℝ)) rfl hkK
    rw [← hk] at hterm
    have hsq : ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) = ((N : ℝ) + 1 + j) ^ (2 : ℕ) := by
      rw [hnv]; ring
    calc D n = ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n) := rfl
      _ = ((N : ℝ) + 1 + j) ^ (2 : ℕ) * (‖a n‖ * r ^ n) := by rw [hsq]
      _ ≤ ((N : ℝ) + 1 + j) ^ (2 : ℕ)
          * (μ * Real.exp (-(((N : ℝ) + 1 + j) * (N : ℝ) / (4 * L)))) :=
          mul_le_mul_of_nonneg_left hterm (sq_nonneg _)
      _ = μ * f j := by rw [hexp j, hf]; ring
  have hwin : ∑ n ∈ Finset.Ico (v - N) (v + N + 1), D n ≤ (N : ℝ) ^ (2 : ℕ) * W := by
    have hpt : ∀ n ∈ Finset.Ico (v - N) (v + N + 1),
        D n ≤ (N : ℝ) ^ (2 : ℕ) * (‖a n‖ * r ^ n) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
      have habs : |(n : ℝ) - (v : ℝ)| ≤ (N : ℝ) := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · rcases le_or_gt N v with hNv | hNv
          · have hcast : ((v - N : ℕ) : ℝ) = (v : ℝ) - (N : ℝ) := by
              push_cast [Nat.cast_sub hNv]; ring
            have hn1' : ((v - N : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
            rw [hcast] at hn1'
            linarith
          · have hvN : (v : ℝ) < (N : ℝ) := by exact_mod_cast hNv
            have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith
        · have hle : (n : ℝ) ≤ (v : ℝ) + (N : ℝ) := by
            have : n ≤ v + N := by omega
            exact_mod_cast this
          linarith
      have hsq : ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) ≤ (N : ℝ) ^ (2 : ℕ) := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      exact mul_le_mul_of_nonneg_right hsq (term_nonneg a hrpos n)
    have hstep := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum] at hstep
    exact le_trans hstep (mul_le_mul_of_nonneg_left hW (sq_nonneg _))
  have hlow : ∑ n ∈ Finset.Ico 0 (v - N), D n ≤ μ * ∑' j : ℕ, f j := by
    rw [← Finset.range_eq_Ico]
    have hrefl : ∑ n ∈ Finset.range (v - N), D n
        = ∑ j ∈ Finset.range (v - N), D (v - N - 1 - j) :=
      (Finset.sum_range_reflect (fun n => D n) (v - N)).symm
    rw [hrefl]
    refine le_trans (Finset.sum_le_sum fun j hj => hdecay_down j (Finset.mem_range.mp hj)) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Summable.sum_le_tsum _ (fun j _ => hfnn j) hfsum) hμ
  have hup : ∑' j : ℕ, D (j + (v + N + 1)) ≤ μ * ∑' j : ℕ, f j := by
    have hsumL : Summable fun j : ℕ => D (j + (v + N + 1)) :=
      (summable_nat_add_iff (v + N + 1)).mpr hDsum
    have hle := Summable.tsum_le_tsum hdecay_up hsumL (hfsum.mul_left μ)
    rwa [tsum_mul_left] at hle
  have hsplit := Summable.sum_add_tsum_nat_add (f := D) (v + N + 1) hDsum
  have hcons : (∑ n ∈ Finset.Ico 0 (v - N), D n) + ∑ n ∈ Finset.Ico (v - N) (v + N + 1), D n
      = ∑ n ∈ Finset.Ico 0 (v + N + 1), D n :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  calc ∑' n : ℕ, D n
      = (∑ n ∈ Finset.Ico 0 (v + N + 1), D n) + ∑' j : ℕ, D (j + (v + N + 1)) := by
        rw [← hsplit, Finset.range_eq_Ico]
    _ = (∑ n ∈ Finset.Ico 0 (v - N), D n) + (∑ n ∈ Finset.Ico (v - N) (v + N + 1), D n)
        + ∑' j : ℕ, D (j + (v + N + 1)) := by rw [hcons]
    _ ≤ μ * (∑' j : ℕ, f j) + (N : ℝ) ^ (2 : ℕ) * W + μ * ∑' j : ℕ, f j := by gcongr
    _ = (N : ℝ) ^ (2 : ℕ) * W + 2 * μ * ∑' j : ℕ, f j := by ring

end GaloisForLFunctions.HTGeometry
