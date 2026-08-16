import GaloisForLFunctions.RHTower.FloorTransformHarmonicInverse

/-!
# The harmonic triangular projection of a floor transport

For a source sequence `a` with partial sums `R`, the triangular transport

`T_N(D) = ∑_{m ≤ ⌊N/(D+1)⌋} a_m (⌊N/m⌋ − D)`

is exactly the tail `∑_{d > D} R(⌊N/d⌋)` of the harmonic floor transform.  Projecting it against
the harmonic increment weights `w_D = 1/D − 1/(D+1)` collapses it back onto the same two invariants
it came from:

`∑_{D < N} w_D T_N(D) = ∑_{m ≤ N} a_m ⌊N/m⌋ − ∑_{d ≤ N} R(⌊N/d⌋)/d`.

So the signed harmonic projection is a change of coordinates, not a cancellation mechanism.  The
quadratic path kernel is computed in closed form as well; it is positive semidefinite, and its
diagonal is of the same size as the whole transport.
-/

namespace RHTower

noncomputable section

/-! ## Harmonic sums and increment weights -/

/-- The harmonic number `H_n = ∑_{k ≤ n} 1/k`. -/
def harmonicSum (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k

theorem harmonicSum_succ (n : ℕ) :
    harmonicSum (n + 1) = harmonicSum n + 1 / ((n : ℝ) + 1) := by
  rw [harmonicSum, harmonicSum, Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

/-- The harmonic increment weight `w_D = 1/D − 1/(D+1)`. -/
def harmonicGap (D : ℕ) : ℝ := 1 / (D : ℝ) - 1 / ((D : ℝ) + 1)

theorem harmonicGap_mul (D : ℕ) (hD : 1 ≤ D) :
    (D : ℝ) * harmonicGap D = 1 / ((D : ℝ) + 1) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [harmonicGap]
  field_simp
  ring

theorem harmonicGap_sq_mul (D : ℕ) (hD : 1 ≤ D) :
    (D : ℝ) ^ 2 * harmonicGap D = 1 - 1 / ((D : ℝ) + 1) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [harmonicGap]
  field_simp
  ring

/-! ## The three telescoping moments -/

theorem sum_harmonicGap (n : ℕ) :
    ∑ D ∈ Finset.Icc 1 n, harmonicGap D = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonicGap]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    push_cast
    field_simp
    ring

theorem sum_mul_harmonicGap (n : ℕ) :
    ∑ D ∈ Finset.Icc 1 n, (D : ℝ) * harmonicGap D = harmonicSum (n + 1) - 1 := by
  induction n with
  | zero => simp [harmonicSum]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonicGap_mul _ (by omega),
      harmonicSum_succ (n + 1)]
    push_cast
    ring

theorem sum_sq_mul_harmonicGap (n : ℕ) :
    ∑ D ∈ Finset.Icc 1 n, (D : ℝ) ^ 2 * harmonicGap D = (n : ℝ) - (harmonicSum (n + 1) - 1) := by
  induction n with
  | zero => simp [harmonicSum]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonicGap_sq_mul _ (by omega),
      harmonicSum_succ (n + 1)]
    push_cast
    ring

/-! ## The linear and quadratic projections -/

/-- **(24.38) The harmonic projection of a linear ramp.** -/
theorem sum_ramp_harmonicGap {q : ℕ} (hq : 1 ≤ q) :
    ∑ D ∈ Finset.Icc 1 (q - 1), ((q : ℝ) - (D : ℝ)) * harmonicGap D
      = (q : ℝ) - harmonicSum q := by
  have hsucc : q - 1 + 1 = q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsplit : ∑ D ∈ Finset.Icc 1 (q - 1), ((q : ℝ) - (D : ℝ)) * harmonicGap D
      = (q : ℝ) * ∑ D ∈ Finset.Icc 1 (q - 1), harmonicGap D
        - ∑ D ∈ Finset.Icc 1 (q - 1), (D : ℝ) * harmonicGap D := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  rw [hsplit, sum_harmonicGap, sum_mul_harmonicGap, hsucc]
  have hcast : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
    rw [Nat.cast_sub hq]
    push_cast
    ring
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hstep : (q : ℝ) * (1 - 1 / (q : ℝ)) = (q : ℝ) - 1 := by field_simp
  rw [hcast, hstep]
  ring

/-- **(24.42) The harmonic projection of a product of two ramps.** -/
theorem sum_biramp_harmonicGap {l v : ℕ} (hl : 1 ≤ l) :
    ∑ D ∈ Finset.Icc 1 (l - 1), ((l : ℝ) - (D : ℝ)) * ((v : ℝ) - (D : ℝ)) * harmonicGap D
      = (l : ℝ) * (v : ℝ) + 2 * (l : ℝ) - ((l : ℝ) + (v : ℝ) + 1) * harmonicSum l := by
  have hsucc : l - 1 + 1 = l := by omega
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hsplit : ∑ D ∈ Finset.Icc 1 (l - 1),
        ((l : ℝ) - (D : ℝ)) * ((v : ℝ) - (D : ℝ)) * harmonicGap D
      = (l : ℝ) * (v : ℝ) * ∑ D ∈ Finset.Icc 1 (l - 1), harmonicGap D
        - ((l : ℝ) + (v : ℝ)) * ∑ D ∈ Finset.Icc 1 (l - 1), (D : ℝ) * harmonicGap D
        + ∑ D ∈ Finset.Icc 1 (l - 1), (D : ℝ) ^ 2 * harmonicGap D := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun D _ => by ring
  rw [hsplit, sum_harmonicGap, sum_mul_harmonicGap, sum_sq_mul_harmonicGap, hsucc]
  have hcastAdd : ((l - 1 : ℕ) : ℝ) + 1 = (l : ℝ) := by
    rw [Nat.cast_sub hl]
    push_cast
    ring
  have hcastSub : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub hl]
    push_cast
    ring
  have hlne : (l : ℝ) ≠ 0 := ne_of_gt hlpos
  have hstep : (l : ℝ) * (v : ℝ) * (1 - 1 / (l : ℝ)) = (l : ℝ) * (v : ℝ) - (v : ℝ) := by
    field_simp
  rw [hcastAdd, hcastSub, hstep]
  ring

/-! ## Two hyperbola regroupings -/

theorem hyperbolaSwap (N : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / m), G m d
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), G m d := by
  rw [Finset.sum_sigma' (Finset.Icc 1 N) (fun m => Finset.Icc 1 (N / m)) (fun m d => G m d),
    Finset.sum_sigma' (Finset.Icc 1 N) (fun d => Finset.Icc 1 (N / d)) (fun d m => G m d)]
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hm1, hmN⟩, hd1, hdq⟩ := hx
    have hmd : d * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hdq
    refine ⟨⟨hd1, by nlinarith⟩, hm1, (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)⟩
  · rintro ⟨d, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hd1, hdN⟩, hm1, hmq⟩ := hx
    have hmd : m * d ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmq
    refine ⟨⟨hm1, by nlinarith⟩, hd1, (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)⟩
  · rintro ⟨m, d⟩ _
    rfl
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨m, d⟩ _
    rfl

theorem shiftedSwap (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ D ∈ Finset.Icc 1 (N - 1), ∑ m ∈ Finset.Icc 1 (N / (D + 1)), F D m
      = ∑ m ∈ Finset.Icc 1 N, ∑ D ∈ Finset.Icc 1 (N / m - 1), F D m := by
  rw [Finset.sum_sigma' (Finset.Icc 1 (N - 1)) (fun D => Finset.Icc 1 (N / (D + 1)))
      (fun D m => F D m),
    Finset.sum_sigma' (Finset.Icc 1 N) (fun m => Finset.Icc 1 (N / m - 1)) (fun m D => F D m)]
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨D, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hD1, hDN⟩, hm1, hmq⟩ := hx
    have hmd : m * (D + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmq
    have hdiv : D + 1 ≤ N / m := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
    exact ⟨⟨hm1, by nlinarith⟩, hD1, by omega⟩
  · rintro ⟨m, D⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hm1, hmN⟩, hD1, hDq⟩ := hx
    have hdiv : D + 1 ≤ N / m := by omega
    have hmd : (D + 1) * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hdiv
    have hDN : D + 1 ≤ N := by nlinarith
    exact ⟨⟨hD1, by omega⟩, hm1, (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)⟩
  · rintro ⟨D, m⟩ _
    rfl
  · rintro ⟨m, D⟩ _
    rfl
  · rintro ⟨D, m⟩ _
    rfl

/-! ## The transport and its harmonic projection -/

/-- The partial sums of the source. -/
def sourcePartialSum (a : ℕ → ℝ) (k : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 k, a m

/-- The floor moment `∑_{m ≤ N} a_m ⌊N/m⌋`. -/
def floorMoment (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, a m * ((N / m : ℕ) : ℝ)

/-- **(24.32) The triangular transport** `T_N(D) = ∑_{m ≤ ⌊N/(D+1)⌋} a_m (⌊N/m⌋ − D)`. -/
def triangularTransport (a : ℕ → ℝ) (N D : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (N / (D + 1)), a m * (((N / m : ℕ) : ℝ) - (D : ℝ))

/-- **(24.39) The harmonic floor moment is the harmonic floor transform of the partial sums.** -/
theorem sum_harmonicSum_floor_eq (a : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, a m * harmonicSum (N / m)
      = floorTransform harmonicWeight (sourcePartialSum a) N := by
  have hleft : ∑ m ∈ Finset.Icc 1 N, a m * harmonicSum (N / m)
      = ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / m), a m * (1 / (d : ℝ)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [harmonicSum, Finset.mul_sum]
  have hright : floorTransform harmonicWeight (sourcePartialSum a) N
      = ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), a m * (1 / (d : ℝ)) := by
    rw [floorTransform]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [harmonicWeight, sourcePartialSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hleft, hright]
  exact hyperbolaSwap N fun m d => a m * (1 / (d : ℝ))

/-- **(24.41) The harmonic projection of the triangular transport is a change of coordinates.** -/
theorem harmonic_projection_triangularTransport (a : ℕ → ℝ) (N : ℕ) :
    ∑ D ∈ Finset.Icc 1 (N - 1), harmonicGap D * triangularTransport a N D
      = floorMoment a N - floorTransform harmonicWeight (sourcePartialSum a) N := by
  have hexpand : ∑ D ∈ Finset.Icc 1 (N - 1), harmonicGap D * triangularTransport a N D
      = ∑ D ∈ Finset.Icc 1 (N - 1), ∑ m ∈ Finset.Icc 1 (N / (D + 1)),
          a m * (((N / m : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D := by
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [triangularTransport, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hexpand, shiftedSwap N fun D m => a m * (((N / m : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D]
  have hinner : ∀ m ∈ Finset.Icc 1 N,
      ∑ D ∈ Finset.Icc 1 (N / m - 1), a m * (((N / m : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D
        = a m * ((N / m : ℕ) : ℝ) - a m * harmonicSum (N / m) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hq : 1 ≤ N / m := (Nat.one_le_div_iff (by omega)).2 hm.2
    have hstep : ∑ D ∈ Finset.Icc 1 (N / m - 1),
        a m * (((N / m : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D
          = a m * ∑ D ∈ Finset.Icc 1 (N / m - 1), (((N / m : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun D _ => by ring
    rw [hstep, sum_ramp_harmonicGap hq]
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib, sum_harmonicSum_floor_eq, floorMoment]

/-! ## The quadratic path kernel -/

theorem harmonicGap_nonneg {D : ℕ} (hD : 1 ≤ D) : 0 ≤ harmonicGap D := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [harmonicGap, sub_nonneg]
  apply one_div_le_one_div_of_le hDpos
  linarith

theorem shiftedSwap₂ (N : ℕ) (F : ℕ → ℕ × ℕ → ℝ) :
    ∑ D ∈ Finset.Icc 1 (N - 1),
        ∑ p ∈ Finset.Icc 1 (N / (D + 1)) ×ˢ Finset.Icc 1 (N / (D + 1)), F D p
      = ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
          ∑ D ∈ Finset.Icc 1 (min (N / p.1) (N / p.2) - 1), F D p := by
  rw [Finset.sum_sigma' (Finset.Icc 1 (N - 1))
      (fun D => Finset.Icc 1 (N / (D + 1)) ×ˢ Finset.Icc 1 (N / (D + 1))) (fun D p => F D p),
    Finset.sum_sigma' (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)
      (fun p => Finset.Icc 1 (min (N / p.1) (N / p.2) - 1)) (fun p D => F D p)]
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨D, m, n⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hD1, hDN⟩, ⟨hm1, hmq⟩, hn1, hnq⟩ := hx
    have hmd : m * (D + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmq
    have hnd : n * (D + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hnq
    have hmdiv : D + 1 ≤ N / m := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
    have hndiv : D + 1 ≤ N / n := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
    exact ⟨⟨⟨hm1, by nlinarith⟩, hn1, by nlinarith⟩, hD1, by omega⟩
  · rintro ⟨⟨m, n⟩, D⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨⟨hm1, hmN⟩, hn1, hnN⟩, hD1, hDq⟩ := hx
    have hmdiv : D + 1 ≤ N / m := by omega
    have hndiv : D + 1 ≤ N / n := by omega
    have hmd : (D + 1) * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmdiv
    have hnd : (D + 1) * n ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hndiv
    have hDN : D + 1 ≤ N := by nlinarith
    exact ⟨⟨hD1, by omega⟩, ⟨hm1, (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)⟩,
      hn1, (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)⟩
  · rintro ⟨D, m, n⟩ _
    rfl
  · rintro ⟨⟨m, n⟩, D⟩ _
    rfl
  · rintro ⟨D, m, n⟩ _
    rfl

/-- The exact positive path kernel `K(q_m, q_n)`. -/
def pathKernel (N m n : ℕ) : ℝ :=
  ∑ D ∈ Finset.Icc 1 (min (N / m) (N / n) - 1),
    (((N / m : ℕ) : ℝ) - (D : ℝ)) * (((N / n : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D

/-- **(24.42) The closed form of the path kernel.** -/
theorem pathKernel_eq {N m n : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    pathKernel N m n
      = ((min (N / m) (N / n) : ℕ) : ℝ) * ((max (N / m) (N / n) : ℕ) : ℝ)
          + 2 * ((min (N / m) (N / n) : ℕ) : ℝ)
          - (((min (N / m) (N / n) : ℕ) : ℝ) + ((max (N / m) (N / n) : ℕ) : ℝ) + 1)
              * harmonicSum (min (N / m) (N / n)) := by
  have hqm : 1 ≤ N / m := (Nat.one_le_div_iff (by omega)).2 hmN
  have hqn : 1 ≤ N / n := (Nat.one_le_div_iff (by omega)).2 hnN
  have hmin : 1 ≤ min (N / m) (N / n) := le_min hqm hqn
  rcases le_total (N / m) (N / n) with h | h
  · have hminEq : min (N / m) (N / n) = N / m := min_eq_left h
    have hmaxEq : max (N / m) (N / n) = N / n := max_eq_right h
    rw [pathKernel, hminEq, hmaxEq]
    exact sum_biramp_harmonicGap (l := N / m) (v := N / n) hqm
  · have hminEq : min (N / m) (N / n) = N / n := min_eq_right h
    have hmaxEq : max (N / m) (N / n) = N / m := max_eq_left h
    rw [pathKernel, hminEq, hmaxEq]
    have hswap : ∑ D ∈ Finset.Icc 1 (N / n - 1),
        (((N / m : ℕ) : ℝ) - (D : ℝ)) * (((N / n : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D
          = ∑ D ∈ Finset.Icc 1 (N / n - 1),
            (((N / n : ℕ) : ℝ) - (D : ℝ)) * (((N / m : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D :=
      Finset.sum_congr rfl fun D _ => by ring
    rw [hswap]
    exact sum_biramp_harmonicGap (l := N / n) (v := N / m) hqn

/-- **(24.43) The exact centered path energy.** -/
theorem harmonic_pathEnergy_triangularTransport (a : ℕ → ℝ) (N : ℕ) :
    ∑ D ∈ Finset.Icc 1 (N - 1), harmonicGap D * triangularTransport a N D ^ 2
      = ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, a p.1 * a p.2 * pathKernel N p.1 p.2 := by
  have hexpand : ∀ D : ℕ, harmonicGap D * triangularTransport a N D ^ 2
      = ∑ p ∈ Finset.Icc 1 (N / (D + 1)) ×ˢ Finset.Icc 1 (N / (D + 1)),
          a p.1 * a p.2 * ((((N / p.1 : ℕ) : ℝ) - (D : ℝ))
            * (((N / p.2 : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D) := by
    intro D
    rw [triangularTransport, sq, Finset.sum_mul_sum, Finset.mul_sum,
      Finset.sum_product' (f := fun m n => a m * a n * ((((N / m : ℕ) : ℝ) - (D : ℝ))
        * (((N / n : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl fun D _ => hexpand D,
    shiftedSwap₂ N fun D p => a p.1 * a p.2 * ((((N / p.1 : ℕ) : ℝ) - (D : ℝ))
      * (((N / p.2 : ℕ) : ℝ) - (D : ℝ)) * harmonicGap D)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pathKernel, Finset.mul_sum]

/-- The path energy is nonnegative: the kernel is positive semidefinite. -/
theorem harmonic_pathEnergy_nonneg (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, a p.1 * a p.2 * pathKernel N p.1 p.2 := by
  rw [← harmonic_pathEnergy_triangularTransport]
  refine Finset.sum_nonneg fun D hD => ?_
  rw [Finset.mem_Icc] at hD
  exact mul_nonneg (harmonicGap_nonneg hD.1) (sq_nonneg _)

/-! ## The transport is the tail of the harmonic floor sum -/

theorem tailSwap (N D : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ d ∈ Finset.Icc (D + 1) N, ∑ m ∈ Finset.Icc 1 (N / d), G d m
      = ∑ m ∈ Finset.Icc 1 (N / (D + 1)), ∑ d ∈ Finset.Icc (D + 1) (N / m), G d m := by
  rw [Finset.sum_sigma' (Finset.Icc (D + 1) N) (fun d => Finset.Icc 1 (N / d)) (fun d m => G d m),
    Finset.sum_sigma' (Finset.Icc 1 (N / (D + 1))) (fun m => Finset.Icc (D + 1) (N / m))
      (fun m d => G d m)]
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, m⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hd1, hdN⟩, hm1, hmq⟩ := hx
    have hmd : m * d ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmq
    have hmD : m * (D + 1) ≤ N := le_trans (Nat.mul_le_mul_left m hd1) hmd
    exact ⟨⟨hm1, (Nat.le_div_iff_mul_le (by omega)).2 hmD⟩, hd1,
      (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)⟩
  · rintro ⟨m, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hm1, hmq⟩, hd1, hdq⟩ := hx
    have hdm : d * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hdq
    exact ⟨⟨hd1, by nlinarith⟩, hm1, (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)⟩
  · rintro ⟨d, m⟩ _
    rfl
  · rintro ⟨m, d⟩ _
    rfl
  · rintro ⟨d, m⟩ _
    rfl

/-- **(24.32) The triangular transport is exactly the tail of the harmonic floor sum.** -/
theorem tail_sourcePartialSum_eq_triangularTransport (a : ℕ → ℝ) (N D : ℕ) :
    ∑ d ∈ Finset.Icc (D + 1) N, sourcePartialSum a (N / d) = triangularTransport a N D := by
  have hleft : ∑ d ∈ Finset.Icc (D + 1) N, sourcePartialSum a (N / d)
      = ∑ d ∈ Finset.Icc (D + 1) N, ∑ m ∈ Finset.Icc 1 (N / d), a m :=
    Finset.sum_congr rfl fun d _ => rfl
  rw [hleft, tailSwap N D fun _ m => a m, triangularTransport]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have hmD : m * (D + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hm.2
  have hq : D + 1 ≤ N / m := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hcast : ((N / m + 1 - (D + 1) : ℕ) : ℝ) = ((N / m : ℕ) : ℝ) - (D : ℝ) := by
    have hle : D + 1 ≤ N / m + 1 := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hcast]
  ring

end

end RHTower
