import GaloisForLFunctions.MultiplicativePositivityGeometry.ExactFejerBarrier

/-!
# Multi-frequency certificates purchase at most two

A positive certificate couples finitely many real frequencies `u ∈ S ⊂ [0, ∞)`: several heights,
several primes, several harmonics, with no commensurability assumed. Its almost-periodic polynomial
is `P(t) = Σ_{u ∈ S} a(u) cos(ut) ≥ 0`. For every frequency `γ > 0` of `S` the zero share is at most
twice the pole share: `a(γ) ≤ 2 a(0)` (`multiFrequency_purchase_le_two`).

*Proof.* Sample `(1 − cos γt) P(t) ≥ 0` at `t = 0, h, …, (N−1)h`, with the step `h` below the first
resonance of every mode. The cosine sums `Σ_j cos(v j h)` stay bounded for `v ≠ 0`
(`abs_cosSum_le`), so the sampled sum is `N (a(0) − a(γ)/2) + O(1)`.

So coupling several frequencies never beats the single-frequency purchase ratio. With growth weight
`L·S`, the cap `(3 − 2√2)/(2L)` binds every finite certificate (`multiFrequency_width_cap`). Any
interior gain must therefore come from the growth input, not from the choice of positive
certificate.
-/

open Finset Real

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- The cosine sum `Σ_{j<N} cos(v · jh)` along a progression of step `h`. -/
noncomputable def cosSum (v h : ℝ) (N : ℕ) : ℝ := ∑ j ∈ range N, Real.cos (v * (j * h))

theorem cosSum_zero (h : ℝ) (N : ℕ) : cosSum 0 h N = N := by simp [cosSum]

/-- Off resonance the cosine sums are bounded: `|Σ_{j<N} cos(v jh)| ≤ 1/|sin(vh/2)|`. -/
theorem abs_cosSum_le {v h : ℝ} (hs : Real.sin (v * h / 2) ≠ 0) (N : ℕ) :
    |cosSum v h N| ≤ 1 / |Real.sin (v * h / 2)| := by
  have h1 := two_sin_mul_sum_cos 0 (v * h / 2) N
  have hterm : ∀ j ∈ range N,
      Real.cos (0 + 2 * (j : ℝ) * (v * h / 2)) = Real.cos (v * (j * h)) :=
    fun j _ => by congr 1; ring
  rw [Finset.sum_congr rfl hterm] at h1
  have hpos : 0 < |Real.sin (v * h / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos]
  have hb : |2 * Real.sin (v * h / 2) * cosSum v h N| ≤ 2 := by
    rw [cosSum, h1]
    calc |Real.sin (0 + (2 * N - 1) * (v * h / 2)) - Real.sin (0 - v * h / 2)|
        ≤ |Real.sin (0 + (2 * N - 1) * (v * h / 2))| + |Real.sin (0 - v * h / 2)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  rw [abs_mul, abs_mul, abs_two] at hb
  linarith

/-- A step `h = π/M` keeps every frequency `0 < |v| < M` off resonance. -/
theorem sin_half_ne_zero {v M : ℝ} (hv : v ≠ 0) (hvM : |v| < M) (hM : 0 < M) :
    Real.sin (v * (Real.pi / M) / 2) ≠ 0 := by
  have hx : 0 < |v * (Real.pi / M) / 2| ∧ |v * (Real.pi / M) / 2| < Real.pi := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos (div_pos Real.pi_pos hM)]
    have hv0 := abs_pos.mpr hv
    constructor
    · positivity
    · have : |v| * (Real.pi / M) < Real.pi := by
        rw [mul_div_assoc', div_lt_iff₀ hM]
        nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
  intro h0
  have := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  rcases abs_choice (v * (Real.pi / M) / 2) with he | he
  · rw [he, h0] at this
    exact lt_irrefl 0 this
  · rw [he, Real.sin_neg, h0, neg_zero] at this
    exact lt_irrefl 0 this

/-- The resonance-free part of a cosine sum: `cosSum v h N − N·[v = 0]`. -/
theorem abs_cosSum_sub_le {v M : ℝ} (hvM : |v| < M) (hM : 0 < M) (N : ℕ) :
    |cosSum v (Real.pi / M) N - (if v = 0 then (N : ℝ) else 0)| ≤
      (if v = 0 then 0 else 1 / |Real.sin (v * (Real.pi / M) / 2)|) := by
  split_ifs with hv
  · rw [hv, cosSum_zero, sub_self, abs_zero]
  · rw [sub_zero]
    exact abs_cosSum_le (sin_half_ne_zero hv hvM hM) N

/-- **Multi-frequency purchase cap.** A nonnegative almost-periodic cosine polynomial with
frequencies in `[0, ∞)` has `a(γ) ≤ 2 a(0)` for every frequency `γ > 0`. -/
theorem multiFrequency_purchase_le_two {S : Finset ℝ} {a : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hS : ∀ u ∈ S, 0 ≤ u) (h0 : 0 ∈ S) (hγS : γ ∈ S)
    (hP : ∀ t, 0 ≤ ∑ u ∈ S, a u * Real.cos (u * t)) : a γ ≤ 2 * a 0 := by
  set M : ℝ := ∑ u ∈ S, (|u| + |u - γ| + |u + γ|) + 1 with hMdef
  have hsum0 : 0 ≤ ∑ u ∈ S, (|u| + |u - γ| + |u + γ|) := Finset.sum_nonneg fun u _ => by positivity
  have hM : 0 < M := by linarith
  have hlt : ∀ u ∈ S, |u| < M ∧ |u - γ| < M ∧ |u + γ| < M := by
    intro u hu
    have hle : |u| + |u - γ| + |u + γ| ≤ ∑ u ∈ S, (|u| + |u - γ| + |u + γ|) :=
      Finset.single_le_sum (f := fun u => |u| + |u - γ| + |u + γ|) (fun u _ => by positivity) hu
    refine ⟨?_, ?_, ?_⟩ <;> linarith [abs_nonneg u, abs_nonneg (u - γ), abs_nonneg (u + γ)]
  set h := Real.pi / M with hhdef
  -- Resonance-free bounds.
  set B : ℝ → ℝ := fun v => if v = 0 then 0 else 1 / |Real.sin (v * h / 2)| with hBdef
  set K : ℝ := ∑ u ∈ S, |a u| * (B u + B (u - γ) / 2 + B (u + γ) / 2) with hKdef
  have hmode : ∀ u t, (1 - Real.cos (γ * t)) * Real.cos (u * t) =
      Real.cos (u * t) - Real.cos ((u - γ) * t) / 2 - Real.cos ((u + γ) * t) / 2 := by
    intro u t
    have e1 : (u - γ) * t = u * t - γ * t := by ring
    have e2 : (u + γ) * t = u * t + γ * t := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  -- Sampling the nonnegative function `(1 − cos γt) P(t)` along the progression.
  have hgram : ∀ N : ℕ, 0 ≤ ∑ u ∈ S, a u *
      (cosSum u h N - cosSum (u - γ) h N / 2 - cosSum (u + γ) h N / 2) := by
    intro N
    have hnn : 0 ≤ ∑ j ∈ range N, (1 - Real.cos (γ * (j * h))) *
        ∑ u ∈ S, a u * Real.cos (u * (j * h)) :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (by linarith [Real.cos_le_one (γ * (j * h))]) (hP _)
    have heq : ∑ j ∈ range N, (1 - Real.cos (γ * (j * h))) *
        ∑ u ∈ S, a u * Real.cos (u * (j * h)) = ∑ u ∈ S, a u *
          (cosSum u h N - cosSum (u - γ) h N / 2 - cosSum (u + γ) h N / 2) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      unfold cosSum
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, hmode]
    rw [← heq]
    exact hnn
  -- Each mode is `N·[resonance] + O(1)`.
  have hmode_le : ∀ N : ℕ, ∀ u ∈ S, a u *
      (cosSum u h N - cosSum (u - γ) h N / 2 - cosSum (u + γ) h N / 2) ≤
      a u * ((if u = 0 then (N : ℝ) else 0) - (if u - γ = 0 then (N : ℝ) else 0) / 2 -
        (if u + γ = 0 then (N : ℝ) else 0) / 2) +
        |a u| * (B u + B (u - γ) / 2 + B (u + γ) / 2) := by
    intro N u hu
    obtain ⟨h1, h2, h3⟩ := hlt u hu
    have b1 := abs_cosSum_sub_le h1 hM N
    have b2 := abs_cosSum_sub_le h2 hM N
    have b3 := abs_cosSum_sub_le h3 hM N
    set e1 := cosSum u h N - (if u = 0 then (N : ℝ) else 0)
    set e2 := cosSum (u - γ) h N - (if u - γ = 0 then (N : ℝ) else 0)
    set e3 := cosSum (u + γ) h N - (if u + γ = 0 then (N : ℝ) else 0)
    have hdiff : a u * (cosSum u h N - cosSum (u - γ) h N / 2 - cosSum (u + γ) h N / 2) -
        a u * ((if u = 0 then (N : ℝ) else 0) - (if u - γ = 0 then (N : ℝ) else 0) / 2 -
          (if u + γ = 0 then (N : ℝ) else 0) / 2) = a u * (e1 - e2 / 2 - e3 / 2) := by
      simp only [e1, e2, e3]; ring
    have hbound : a u * (e1 - e2 / 2 - e3 / 2) ≤ |a u| * (B u + B (u - γ) / 2 + B (u + γ) / 2) := by
      have habs : |e1 - e2 / 2 - e3 / 2| ≤ B u + B (u - γ) / 2 + B (u + γ) / 2 := by
        have := abs_sub (e1 - e2 / 2) (e3 / 2)
        have := abs_sub e1 (e2 / 2)
        rw [abs_div, abs_two] at *
        simp only [hBdef]
        linarith
      calc a u * (e1 - e2 / 2 - e3 / 2) ≤ |a u * (e1 - e2 / 2 - e3 / 2)| := le_abs_self _
        _ = |a u| * |e1 - e2 / 2 - e3 / 2| := abs_mul _ _
        _ ≤ |a u| * (B u + B (u - γ) / 2 + B (u + γ) / 2) :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    linarith
  -- The resonant parts add up to `N (a(0) − a(γ)/2)`.
  have hres : ∀ N : ℕ, ∑ u ∈ S, a u * ((if u = 0 then (N : ℝ) else 0) -
      (if u - γ = 0 then (N : ℝ) else 0) / 2 - (if u + γ = 0 then (N : ℝ) else 0) / 2) =
      N * (a 0 - a γ / 2) := by
    intro N
    have hz : ∀ u ∈ S, (if u + γ = 0 then (N : ℝ) else 0) = 0 := fun u hu => by
      rw [if_neg]; linarith [hS u hu]
    have e : ∀ u ∈ S, a u * ((if u = 0 then (N : ℝ) else 0) -
        (if u - γ = 0 then (N : ℝ) else 0) / 2 - (if u + γ = 0 then (N : ℝ) else 0) / 2) =
        (if u = 0 then a u * N else 0) - (if u = γ then a u * N / 2 else 0) := by
      intro u hu
      rw [hz u hu, zero_div, sub_zero]
      by_cases h1 : u = 0
      · have h2 : ¬ u - γ = 0 := fun h => by rw [h1] at h; linarith
        have h3 : ¬ u = γ := by rw [h1]; exact hγ.ne
        rw [if_pos h1, if_neg h2, if_pos h1, if_neg h3]
        ring
      · by_cases h2 : u = γ
        · rw [if_neg h1, if_pos (sub_eq_zero.mpr h2), if_neg h1, if_pos h2]
          ring
        · rw [if_neg h1, if_neg (fun h => h2 (sub_eq_zero.mp h)), if_neg h1, if_neg h2]
          ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq' S 0,
      Finset.sum_ite_eq' S γ, if_pos h0, if_pos hγS]
    ring
  have hfinal : ∀ N : ℕ, 0 ≤ N * (a 0 - a γ / 2) + K := by
    intro N
    have := (hgram N).trans (Finset.sum_le_sum (hmode_le N))
    rw [Finset.sum_add_distrib, hres N] at this
    exact this
  by_contra hneg
  push Not at hneg
  have hpos : 0 < a γ / 2 - a 0 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (K / (a γ / 2 - a 0))
  have h1 := hfinal N
  rw [div_lt_iff₀ hpos] at hN
  nlinarith

/-- **Universal width cap for multi-frequency certificates.** With pole weight `a(0) > 0`, growth
weight `L·W`, `W ≥ a(γ)`, no finite multi-frequency certificate excludes a zero at distance
`η ≥ (3 − 2√2)/(2L)`: the purchase inequality holds for every `δ > 0`. -/
theorem multiFrequency_width_cap {S : Finset ℝ} {a : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hS : ∀ u ∈ S, 0 ≤ u) (h0 : 0 ∈ S) (hγS : γ ∈ S)
    (hP : ∀ t, 0 ≤ ∑ u ∈ S, a u * Real.cos (u * t)) {L W η δ : ℝ} (hL : 0 < L)
    (ha0 : 0 < a 0) (hW0 : 0 ≤ W) (hW : a γ ≤ W)
    (hη : (3 - 2 * Real.sqrt 2) / (2 * L) ≤ η) (hδ : 0 < δ) :
    a γ / (δ + η) ≤ a 0 / δ + L * W :=
  HTGeometry.purchase_width_cap hL ha0 (multiFrequency_purchase_le_two hγ hS h0 hγS hP) hW0 hW
    hη hδ

end GaloisForLFunctions.MultiplicativePositivityGeometry
