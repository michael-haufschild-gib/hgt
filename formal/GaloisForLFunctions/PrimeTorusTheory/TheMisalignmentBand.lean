import GaloisForLFunctions.PrimeTorusTheory.SquaredWordsForbidAlignment

/-!
# The misalignment band

The squared phase of a word is defined at real `u`, so the crossing of `½` is a whole interval: there is `u₁` such that the phase lies
in `[1/(2R), ½]` on `[u₁, u₁ + 1]` (`exists_band`).

Since the word has mass zero, `Σ c_a c_b log(u + a + b) = Σ c_a c_b log(x + h(a + b))` for `u = x/h`. So every arithmetic progression
`x + h(a + b)` with `x/h` in the band carries misalignment (`one_div_le_sum_dist`). Counting these progressions gives a positive density
of misaligned integers: the average of the distance over `n < N` is `≫ 1/(R H² M²)` for every `N ≫ M`. The word has mass zero, so the same
holds against every rotation `φ + ℤ` (`le_sum_rotDist`).

For `H = 1` some integer of size `≪ (log |t|)² log log |t|` has its phase at distance `≫ (log |t|)^{-4} (log log |t|)^{-2}` from the
integers (`exists_not_aligned_of_large_of_word`).
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The distance to the integers. -/
def dist01 (θ : ℝ) : ℝ := |θ - round θ|

theorem dist01_nonneg (θ : ℝ) : 0 ≤ dist01 θ := abs_nonneg _

theorem dist01_le_abs_sub_int (θ : ℝ) (j : ℤ) : dist01 θ ≤ |θ - j| := round_le θ j

theorem continuousOn_wordForm (M : ℕ) (c : ℕ → ℤ) :
    ContinuousOn (wordForm M c) (Set.Ioi 0) := fun _ hx =>
  (hasDerivAt_logForm _ _ (fun a _ => Nat.cast_nonneg a) hx).continuousAt.continuousWithinAt

theorem wordForm_mono (M : ℕ) (c : ℕ → ℤ) : MonotoneOn (wordForm M c) (Set.Ioi 0) :=
  logForm_mono _ _ fun a _ => Nat.cast_nonneg a

/-- The data of a word at height `t`: its height `H`, the step ratio `R`, its order `k + 1`, and the point `N₁` up to which the phase is at
least `½`. -/
structure WordSetup (H R : ℝ) (M k N₁ : ℕ) (c : ℕ → ℤ) (t : ℝ) : Prop where
  one_le_H : 1 ≤ H
  one_le_R : 1 ≤ R
  bound : ∀ a, |(c a : ℝ)| ≤ H
  moments : ∀ j ≤ k, binomMoment M c j = 0
  zero_ne : c 0 ≠ 0
  one_le_N : 1 ≤ N₁
  low : 4 * ((N₁ : ℝ) + 2) * (3 * H) ^ (N₁ + 2) * π ≤ |t|
  step : |t| * (2 * H ^ 2 * ((M : ℝ) + 1) ^ 3) ≤ π * R ^ N₁
  up : |t| * (H ^ 2 * ((M : ℝ) + 1) ^ 2) < π * 4 ^ k

namespace WordSetup

variable {H R : ℝ} {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ}

theorem abs_pos (S : WordSetup H R M k N₁ c t) : 0 < |t| := by
  have h3 : 0 < H := by linarith [S.one_le_H]
  have : 0 < 4 * ((N₁ : ℝ) + 2) * (3 * H) ^ (N₁ + 2) * π := by
    have := Real.pi_pos
    positivity
  linarith [S.low]

theorem phase_pos (S : WordSetup H R M k N₁ c t) {u : ℝ} (hu : 1 ≤ u) :
    0 < -wordForm M c u := by
  have h1 := three_pow_le_neg_wordForm S.one_le_H S.bound S.zero_ne (S.moments 0 (Nat.zero_le k)) hu
  have hH : 0 < H := by linarith [S.one_le_H]
  have h2 : 0 < (1 / (3 * H)) ^ (u + 1) / (4 * (u + 1)) := by
    have : 0 < u + 1 := by linarith
    positivity
  linarith

/-- Log-convexity of the phase along a lattice `u₀ + ℕ`. -/
theorem logConvex_shift (S : WordSetup H R M k N₁ c t) {u₀ : ℝ} (hu : 1 ≤ u₀) (n : ℕ) :
    (-wordForm M c (u₀ + ((n + 1 : ℕ) : ℝ))) ^ 2 ≤
      (-wordForm M c (u₀ + (n : ℝ))) * (-wordForm M c (u₀ + ((n + 2 : ℕ) : ℝ))) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hx : (0 : ℝ) < u₀ + n := by linarith
  have hpos := S.phase_pos (u := u₀ + n) (by linarith)
  have h := logForm_logConvex (range (M + 1)) (v := fun a => (c a : ℝ)) (s := fun a => (a : ℝ))
    (fun a _ => Nat.cast_nonneg a) (wordMass_eq_zero (S.moments 0 (Nat.zero_le k))) hx (by
      have : wordForm M c (u₀ + n) < 0 := by linarith
      simpa [wordForm] using this)
  have e1 : u₀ + ((n + 1 : ℕ) : ℝ) = u₀ + n + 1 := by push_cast; ring
  have e2 : u₀ + ((n + 2 : ℕ) : ℝ) = u₀ + n + 2 := by push_cast; ring
  rw [e1, e2, neg_sq, neg_mul_neg]
  exact h

/-- **The band.** A real `u₁ ∈ [N₁ + 1, 4(M + 1)]` with the phase in `[A/R, A]` on `[u₁, u₁ + 1]`, where `A = π/|t|`. -/
theorem exists_band (S : WordSetup H R M k N₁ c t) :
    ∃ u₁ : ℝ, (N₁ : ℝ) + 1 ≤ u₁ ∧ u₁ ≤ 4 * ((M : ℝ) + 1) ∧
      ∀ u ∈ Set.Icc u₁ (u₁ + 1), π / |t| / R ≤ -wordForm M c u ∧ -wordForm M c u ≤ π / |t| := by
  have hm0 := S.moments 0 (Nat.zero_le k)
  have hπ : 0 < π := Real.pi_pos
  have htpos := S.abs_pos
  have hH1 := S.one_le_H
  have hR1 := S.one_le_R
  have hH0 : 0 < H := by linarith
  have hR0 : 0 < R := by linarith
  set A : ℝ := π / |t| with hA
  have hApos : 0 < A := by positivity
  have hN0 : (1 : ℝ) ≤ N₁ := by exact_mod_cast S.one_le_N
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- above `A` at `N₁ + 1`
  have hA1 : A ≤ -wordForm M c ((N₁ : ℝ) + 1) := by
    have h1 := three_pow_le_neg_wordForm hH1 S.bound S.zero_ne hm0 (x := (N₁ : ℝ) + 1) (by linarith)
    refine le_trans ?_ h1
    have e1 : (N₁ : ℝ) + 1 + 1 = ((N₁ + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, Real.rpow_natCast]
    have h3p : (0 : ℝ) < (3 * H) ^ (N₁ + 2) := by positivity
    have e : (1 / (3 * H)) ^ (N₁ + 2) = 1 / (3 * H) ^ (N₁ + 2) := by rw [div_pow, one_pow]
    have e2 : 4 * (((N₁ + 2 : ℕ) : ℝ)) = 4 * ((N₁ : ℝ) + 2) := by push_cast; ring
    rw [hA, e, e2, div_le_div_iff₀ htpos (by positivity), div_mul_eq_mul_div, one_mul,
      le_div_iff₀ h3p]
    linarith [S.low]
  -- below `A` at `4(M + 1)`
  have hA2 : -wordForm M c (4 * ((M : ℝ) + 1)) < A := by
    have h1 := abs_wordForm_le hH0.le S.bound S.moments (x := 4 * ((M : ℝ) + 1)) le_rfl
    have h2 := neg_le_abs (wordForm M c (4 * ((M : ℝ) + 1)))
    refine lt_of_le_of_lt (h2.trans h1) ?_
    rw [hA, lt_div_iff₀ htpos]
    have h4k : (0 : ℝ) < 4 ^ k := by positivity
    have e3 : (1 / 4 : ℝ) ^ k = 1 / 4 ^ k := by rw [div_pow, one_pow]
    rw [e3]
    have h3 : H ^ 2 * ((M : ℝ) + 1) ^ 2 * (1 / 4 ^ k) * |t| =
        |t| * (H ^ 2 * ((M : ℝ) + 1) ^ 2) / 4 ^ k := by ring
    rw [h3, div_lt_iff₀ h4k]
    exact S.up
  have hlt : (N₁ : ℝ) + 1 < 4 * ((M : ℝ) + 1) := by
    by_contra hge
    push Not at hge
    have := wordForm_mono M c (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < (N₁ : ℝ) + 1)) hge
    linarith
  obtain ⟨u₁, hu₁, hval⟩ : ∃ u₁ ∈ Set.Icc ((N₁ : ℝ) + 1) (4 * ((M : ℝ) + 1)),
      -wordForm M c u₁ = A := by
    have hcont : ContinuousOn (fun u => -wordForm M c u)
        (Set.Icc ((N₁ : ℝ) + 1) (4 * ((M : ℝ) + 1))) :=
      ((continuousOn_wordForm M c).mono fun u hu =>
        Set.mem_Ioi.mpr (by linarith [hu.1])).neg
    have := intermediate_value_Icc' hlt.le hcont
    exact this ⟨hA2.le, hA1⟩
  refine ⟨u₁, hu₁.1, hu₁.2, ?_⟩
  have hu1 : (N₁ : ℝ) + 1 ≤ u₁ := hu₁.1
  -- lattice through `u₁`
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℕ, N₁ ≤ m ∧ ((m : ℝ) + 1 ≤ u₁ ∧ u₁ < (m : ℝ) + 2) := by
    have hu0 : 0 ≤ u₁ := by linarith
    refine ⟨⌊u₁⌋₊ - 1, ?_, ?_⟩
    · have : N₁ + 1 ≤ ⌊u₁⌋₊ := by
        refine Nat.le_floor ?_
        push_cast
        exact hu1
      omega
    · have h1 : 1 ≤ ⌊u₁⌋₊ := by
        refine Nat.le_floor ?_
        push_cast
        linarith
      have e : (((⌊u₁⌋₊ - 1 : ℕ) : ℝ)) = (⌊u₁⌋₊ : ℝ) - 1 := by
        rw [Nat.cast_sub h1]
        push_cast
        ring
      rw [e]
      have h2 := Nat.floor_le hu0
      have h3 := Nat.lt_floor_add_one u₁
      constructor <;> linarith
  set u₀ : ℝ := u₁ - m with hu₀
  have hu₀1 : 1 ≤ u₀ := by rw [hu₀]; linarith [hm2.1]
  set g : ℕ → ℝ := fun n => -wordForm M c (u₀ + n) with hg
  have hgpos : ∀ n, 0 < g n := fun n => S.phase_pos (by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hconv : ∀ n, g (n + 1) ^ 2 ≤ g n * g (n + 2) := fun n => S.logConvex_shift hu₀1 n
  have hgm : g m = A := by
    simp only [hg, hu₀]
    rw [sub_add_cancel]
    exact hval
  have hstepg : (1 / R) * g m ≤ g (m + 1) := by
    refine logConvex_step hgpos hconv (by positivity) (by have := S.one_le_N; omega) ?_
    rw [hgm]
    have hg0 : g 0 ≤ 2 * H ^ 2 * ((M : ℝ) + 1) ^ 3 := by
      have h1 := neg_wordForm_one_le (M := M) S.bound
      have h2 := wordForm_mono M c (Set.mem_Ioi.mpr one_pos)
        (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < u₀)) hu₀1
      simp only [hg, Nat.cast_zero, add_zero]
      linarith
    have hRinv : 1 / R ≤ 1 := by
      rw [div_le_one hR0]
      exact hR1
    have h16 : (1 / R) ^ m ≤ (1 / R) ^ N₁ :=
      pow_le_pow_of_le_one (by positivity) hRinv hm1
    have h16p : (0 : ℝ) < R ^ N₁ := by positivity
    have e : (1 / R) ^ N₁ = 1 / R ^ N₁ := by rw [div_pow, one_pow]
    calc g 0 * (1 / R) ^ m ≤ 2 * H ^ 2 * ((M : ℝ) + 1) ^ 3 * (1 / R) ^ N₁ :=
          mul_le_mul hg0 h16 (by positivity) (by positivity)
      _ ≤ A := by
          rw [hA, e, le_div_iff₀ htpos]
          have e2 : 2 * H ^ 2 * ((M : ℝ) + 1) ^ 3 * (1 / R ^ N₁) * |t| =
              |t| * (2 * H ^ 2 * ((M : ℝ) + 1) ^ 3) / R ^ N₁ := by ring
          rw [e2, div_le_iff₀ h16p]
          exact S.step
  have hgm1 : g (m + 1) = -wordForm M c (u₁ + 1) := by
    simp only [hg, hu₀]
    congr 2
    push_cast
    ring
  intro u hu
  have hu0 : 0 < u₁ := by linarith
  have h1 := wordForm_mono M c (Set.mem_Ioi.mpr hu0)
    (Set.mem_Ioi.mpr (by linarith [hu.1] : 0 < u)) hu.1
  have h2 := wordForm_mono M c (Set.mem_Ioi.mpr (by linarith [hu.1] : 0 < u))
    (Set.mem_Ioi.mpr (by linarith : 0 < u₁ + 1)) hu.2
  rw [hgm, hgm1] at hstepg
  have e : A / R = 1 / R * A := by ring
  constructor
  · rw [e]
    linarith
  · linarith

end WordSetup

/-- The phase at `x/h` is the word on the progression `x + h(a + b)`. -/
theorem wordForm_div {M : ℕ} {c : ℕ → ℤ} (hm : binomMoment M c 0 = 0) {x h : ℝ} (hx : 0 < x)
    (hh : 0 < h) :
    wordForm M c (x / h) = ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
      (c a : ℝ) * (c b : ℝ) * Real.log (x + h * ((a : ℝ) + b)) := by
  have hmass := wordMass_eq_zero hm
  have hzero : ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) * Real.log h = 0 := by
    have e : ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) * Real.log h =
        (∑ a ∈ range (M + 1), (c a : ℝ)) * (∑ b ∈ range (M + 1), (c b : ℝ)) * Real.log h := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    rw [e, hmass]
    ring
  unfold wordForm logForm
  rw [← add_zero (∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
    (c a : ℝ) * (c b : ℝ) * Real.log (x / h + a + b)), ← hzero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hp : 0 < x / h + a + b := by positivity
  have e : x + h * ((a : ℝ) + b) = h * (x / h + a + b) := by
    field_simp
    ring
  rw [e, Real.log_mul hh.ne' hp.ne']
  ring

/-- A real in `[1/(2R), ½]` is at distance at least `1/(2R)` from every integer. -/
theorem le_abs_sub_int' {F R : ℝ} (hR : 1 ≤ R) (h1 : 1 / (2 * R) ≤ F) (h2 : F ≤ 1 / 2) (J : ℤ) :
    1 / (2 * R) ≤ |F - J| := by
  have hR0 : 0 < R := by linarith
  have hRpos : 0 < 1 / (2 * R) := by positivity
  have hR2 : 1 / (2 * R) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rcases le_or_gt J 0 with hJ | hJ
  · have : (J : ℝ) ≤ 0 := by exact_mod_cast hJ
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- **Every progression in the band is misaligned.** -/
theorem one_div_le_sum_dist {M : ℕ} {c : ℕ → ℤ} {H R : ℝ} (hR : 1 ≤ R)
    (hc : ∀ a, |(c a : ℝ)| ≤ H) (hm : binomMoment M c 0 = 0) {t x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    (htpos : 0 < |t|) (h1 : π / |t| / R ≤ -wordForm M c (x / h))
    (h2 : -wordForm M c (x / h) ≤ π / |t|) (φ : ℝ) :
    1 / (2 * R) ≤ H ^ 2 * ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
      dist01 (t * Real.log (x + h * ((a : ℝ) + b)) / (2 * π) - φ) := by
  have hπ : 0 < π := Real.pi_pos
  have hR0 : 0 < R := by linarith
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hc 0)
  set θ : ℕ → ℕ → ℝ := fun a b => t * Real.log (x + h * ((a : ℝ) + b)) / (2 * π) - φ with hθ
  set JJ : ℤ := ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), c a * c b * round (θ a b) with hJJ
  have hc2 : 0 < |t| / (2 * π) := by positivity
  have hmass := wordMass_eq_zero hm
  have hzero : ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) * φ = 0 := by
    have e : ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) * φ =
        (∑ a ∈ range (M + 1), (c a : ℝ)) * (∑ b ∈ range (M + 1), (c b : ℝ)) * φ := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    rw [e, hmass]
    ring
  set F : ℝ := |t| / (2 * π) * -wordForm M c (x / h) with hF
  have hF1 : 1 / (2 * R) ≤ F := by
    have e : |t| / (2 * π) * (π / |t| / R) = 1 / (2 * R) := by
      field_simp
    calc 1 / (2 * R) = |t| / (2 * π) * (π / |t| / R) := e.symm
      _ ≤ F := mul_le_mul_of_nonneg_left h1 hc2.le
  have hF2 : F ≤ 1 / 2 := by
    have e : |t| / (2 * π) * (π / |t|) = 1 / 2 := by
      field_simp
    calc F ≤ |t| / (2 * π) * (π / |t|) := mul_le_mul_of_nonneg_left h2 hc2.le
      _ = 1 / 2 := e
  have hsum : t / (2 * π) * wordForm M c (x / h) - JJ =
      ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) * (θ a b - round (θ a b)) := by
    rw [wordForm_div hm hx hh, hJJ]
    push_cast
    rw [← sub_zero (t / (2 * π) * _ - _), ← hzero, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hθ]
    ring
  have hdist : 1 / (2 * R) ≤ |t / (2 * π) * wordForm M c (x / h) - JJ| := by
    rcases le_total 0 t with ht | ht
    · have e : t / (2 * π) * wordForm M c (x / h) - JJ = -(F - ((-JJ : ℤ) : ℝ)) := by
        rw [hF, abs_of_nonneg ht]
        push_cast
        ring
      rw [e, abs_neg]
      exact le_abs_sub_int' hR hF1 hF2 _
    · have e : t / (2 * π) * wordForm M c (x / h) - JJ = F - JJ := by
        rw [hF, abs_of_nonpos ht]
        ring
      rw [e]
      exact le_abs_sub_int' hR hF1 hF2 _
  refine hdist.trans ?_
  rw [hsum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, abs_mul]
  have h4 : |(c a : ℝ)| * |(c b : ℝ)| ≤ H ^ 2 := by
    rw [sq]
    exact mul_le_mul (hc a) (hc b) (abs_nonneg _) hH0
  exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)

/-- Blocks of length `h`. -/
theorem sum_range_mul_eq (g : ℕ → ℝ) (h n : ℕ) :
    ∑ r ∈ range (h * n), g r = ∑ b ∈ range n, ∑ i ∈ range h, g (h * b + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.mul_succ, Finset.sum_range_add]

/-- A shifted window of a nonnegative sequence is at most the full sum. -/
theorem sum_shift_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {C R N : ℕ} (hN : C + R ≤ N) :
    ∑ r ∈ range R, g (C + r) ≤ ∑ n ∈ range N, g n := by
  have h1 : ∑ n ∈ range (C + R), g n ≤ ∑ n ∈ range N, g n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hN) fun n _ _ => hg n
  rw [Finset.sum_range_add] at h1
  have h2 : 0 ≤ ∑ n ∈ range C, g n := Finset.sum_nonneg fun n _ => hg n
  linarith

/-- For fixed `h`, each `n` meets the progressions with a given `a` at most once. -/
theorem sum_progressions_le {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {M h B N : ℕ}
    (hN : B + h * (2 * M + 1) ≤ N) :
    ∑ i ∈ range h, ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), g (B + i + h * (a + b)) ≤
      ((M : ℝ) + 1) * ∑ n ∈ range N, g n := by
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _a ∈ range (M + 1), ∑ n ∈ range N, g n := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [Finset.sum_comm]
        have ha' := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hshift := sum_shift_le hg (C := B + h * a) (R := h * (M + 1)) (N := N) (by
          have : h * a ≤ h * M := Nat.mul_le_mul_left _ ha'
          nlinarith)
        rw [sum_range_mul_eq (fun r => g (B + h * a + r))] at hshift
        refine le_trans (le_of_eq ?_) hshift
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
        congr 1
        ring
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The distance of the phase of `n` to the integers. -/
def phaseDist (t : ℝ) (n : ℕ) : ℝ := dist01 (t * Real.log n / (2 * π))

theorem phaseDist_nonneg (t : ℝ) (n : ℕ) : 0 ≤ phaseDist t n := dist01_nonneg _

/-- The distance of the phase of `n ≥ 1` to the rotated integers `φ + ℤ`. -/
def rotDist (t φ : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else dist01 (t * Real.log n / (2 * π) - φ)

theorem rotDist_nonneg (t φ : ℝ) (n : ℕ) : 0 ≤ rotDist t φ n := by
  unfold rotDist
  split_ifs
  · exact le_rfl
  · exact dist01_nonneg _

theorem rotDist_zero (t : ℝ) (n : ℕ) : rotDist t 0 n = phaseDist t n := by
  unfold rotDist phaseDist
  split_ifs with h
  · subst h
    simp [dist01]
  · rw [sub_zero]

namespace WordSetup

variable {H R : ℝ} {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ}

/-- **Non-alignment.** Some integer in `[N₁ + 1, 6M + 5]` has its phase at distance more than `ε` from the integers. -/
theorem exists_not_aligned (S : WordSetup H R M k N₁ c t) {ε : ℝ}
    (hε : H ^ 2 * (((M : ℝ) + 1) ^ 2 * ε) < 1 / (2 * R)) :
    ∃ n : ℕ, N₁ + 1 ≤ n ∧ n ≤ 6 * M + 5 ∧ ∀ j : ℤ, ε < |t * Real.log n / (2 * π) - j| := by
  obtain ⟨u₁, hu1, hu2, hband⟩ := S.exists_band
  have hN0 : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg N₁
  have hu0 : 0 < u₁ := by linarith
  set X := ⌈u₁⌉₊ with hX
  have hX1 : u₁ ≤ X := Nat.le_ceil _
  have hX2 : (X : ℝ) < u₁ + 1 := Nat.ceil_lt_add_one hu0.le
  have hXpos : (0 : ℝ) < X := by linarith
  have hmem : (X : ℝ) / (1 : ℝ) ∈ Set.Icc u₁ (u₁ + 1) := by
    rw [div_one]
    exact ⟨hX1, hX2.le⟩
  have hb := hband _ hmem
  have hsum := one_div_le_sum_dist S.one_le_R S.bound (S.moments 0 (Nat.zero_le k)) hXpos one_pos
    S.abs_pos hb.1 hb.2 0
  simp only [sub_zero] at hsum
  have hXN : N₁ + 1 ≤ X := by
    have : ((N₁ + 1 : ℕ) : ℝ) ≤ X := by
      push_cast
      linarith
    exact_mod_cast this
  have hXM : X ≤ 4 * M + 5 := by
    have : (X : ℝ) < ((4 * M + 5 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h3 : X < 4 * M + 5 + 1 := by exact_mod_cast this
    omega
  by_contra hcon
  push Not at hcon
  have hle : ∀ a ∈ range (M + 1), ∀ b ∈ range (M + 1),
      dist01 (t * Real.log ((X : ℝ) + 1 * ((a : ℝ) + b)) / (2 * π)) ≤ ε := by
    intro a ha b hb
    have ha' := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hn := hcon (X + a + b) (by omega) (by omega)
    set J := hn.choose
    have hJ : |t * Real.log ((X + a + b : ℕ) : ℝ) / (2 * π) - J| ≤ ε := hn.choose_spec
    have e : (X : ℝ) + 1 * ((a : ℝ) + b) = ((X + a + b : ℕ) : ℝ) := by
      push_cast
      ring
    rw [e]
    exact (dist01_le_abs_sub_int _ J).trans hJ
  have hupper : ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
      dist01 (t * Real.log ((X : ℝ) + 1 * ((a : ℝ) + b)) / (2 * π)) ≤ ((M : ℝ) + 1) ^ 2 * ε := by
    calc _ ≤ ∑ _a ∈ range (M + 1), ((M : ℝ) + 1) * ε := by
          refine Finset.sum_le_sum fun a ha => ?_
          calc _ ≤ ∑ _b ∈ range (M + 1), ε := Finset.sum_le_sum fun b hb => hle a ha b hb
            _ = _ := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                push_cast
                ring
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ H ^ 2)
  linarith

/-- The mean of the distance over a multiple of `6M + 6` terms of the progression `r + qm`. -/
theorem le_sum_rotDist_ap_mul (S : WordSetup H R M k N₁ c t) (φ : ℝ) {q r B : ℕ} (hq : 1 ≤ q)
    (hr : r ≤ q) (hB : 1 ≤ B) :
    (B : ℝ) / (4 * R * H ^ 2 * ((M : ℝ) + 1)) ≤
      ∑ m ∈ range (B * (6 * M + 6)), rotDist t φ (r + q * m) := by
  have hm0 := S.moments 0 (Nat.zero_le k)
  obtain ⟨u₁, hu1, hu2, hband⟩ := S.exists_band
  have htpos := S.abs_pos
  have hN0 : (1 : ℝ) ≤ N₁ := by exact_mod_cast S.one_le_N
  have hu0 : 2 ≤ u₁ := by linarith
  have hH0 : 0 < H := by linarith [S.one_le_H]
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrq : (r : ℝ) / q ≤ 1 := by
    rw [div_le_one hq0]
    exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / q := by positivity
  set g : ℕ → ℝ := fun m => rotDist t φ (r + q * m) with hg
  have hgnn : ∀ m, 0 ≤ g m := fun m => rotDist_nonneg t φ _
  set Sm : ℝ := ∑ m ∈ range (B * (6 * M + 6)), g m with hSm
  have hSnn : 0 ≤ Sm := Finset.sum_nonneg fun n _ => hgnn n
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  -- one step `h`
  have hone : ∀ j ∈ range B, (((j + 1 : ℕ) : ℝ)) * (1 / (2 * R)) ≤ H ^ 2 * (((M : ℝ) + 1) * Sm) := by
    intro j hj
    have hjB := Finset.mem_range.mp hj
    set h := j + 1 with hh
    have hh0 : (0 : ℝ) < (h : ℝ) := by positivity
    have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (by omega : 1 ≤ h)
    have hhu : 2 ≤ (h : ℝ) * u₁ := by nlinarith
    set A := ⌈(h : ℝ) * u₁ - (r : ℝ) / q⌉₊ with hA
    have hAlow : (h : ℝ) * u₁ - (r : ℝ) / q ≤ A := Nat.le_ceil _
    have hAup : (A : ℝ) < (h : ℝ) * u₁ - (r : ℝ) / q + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have hApos : 1 ≤ A := by
      have : (1 : ℝ) ≤ A := by linarith
      exact_mod_cast this
    have hAnat : A ≤ h * (4 * (M + 1)) := by
      have h1 : (h : ℝ) * u₁ ≤ (h : ℝ) * (4 * ((M : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hu2 hh0.le
      have h2 : (A : ℝ) < ((h * (4 * (M + 1)) : ℕ) : ℝ) + 1 := by
        push_cast
        linarith
      exact Nat.lt_succ_iff.mp (by exact_mod_cast h2)
    have hupper := sum_progressions_le hgnn (M := M) (h := h) (B := A)
      (N := B * (6 * M + 6)) (by
        have h3 : h * (6 * M + 5) ≤ B * (6 * M + 6) :=
          Nat.mul_le_mul hjB (by omega)
        nlinarith)
    have hlower : ∀ i ∈ range h, 1 / (2 * R) ≤ H ^ 2 * ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1),
        g (A + i + h * (a + b)) := by
      intro i hi
      have hih : (i : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hApos
      have hx : (0 : ℝ) < ((r + q * (A + i) : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        have h3 : 0 < (q : ℝ) * ((A : ℝ) + i) := by positivity
        linarith
      have hh'0 : (0 : ℝ) < ((q * h : ℕ) : ℝ) := by
        push_cast
        positivity
      have ee : ((r + q * (A + i) : ℕ) : ℝ) / ((q * h : ℕ) : ℝ) =
          ((r : ℝ) / q + A + i) / h := by
        push_cast
        field_simp
        ring
      have hmem : ((r + q * (A + i) : ℕ) : ℝ) / ((q * h : ℕ) : ℝ) ∈ Set.Icc u₁ (u₁ + 1) := by
        rw [ee]
        constructor
        · rw [le_div_iff₀ hh0]
          linarith
        · rw [div_le_iff₀ hh0]
          nlinarith
      have hb := hband _ hmem
      have h5 := one_div_le_sum_dist S.one_le_R S.bound hm0 hx hh'0 htpos hb.1 hb.2 φ
      refine h5.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have hne : r + q * (A + i + h * (a + b)) ≠ 0 := by
        have : 0 < q * (A + i + h * (a + b)) := Nat.mul_pos (by omega) (by omega)
        omega
      simp only [hg]
      unfold rotDist
      rw [if_neg hne]
      congr 3
      push_cast
      ring_nf
    have hsumlow : ((h : ℝ)) * (1 / (2 * R)) ≤ H ^ 2 * ∑ i ∈ range h, ∑ a ∈ range (M + 1),
        ∑ b ∈ range (M + 1), g (A + i + h * (a + b)) := by
      rw [Finset.mul_sum]
      calc (h : ℝ) * (1 / (2 * R)) = ∑ _i ∈ range h, 1 / (2 * R) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hlower
    exact hsumlow.trans (mul_le_mul_of_nonneg_left hupper (by positivity))
  have hsum : ∑ j ∈ range B, (((j + 1 : ℕ) : ℝ)) * (1 / (2 * R)) ≤
      (B : ℝ) * (H ^ 2 * (((M : ℝ) + 1) * Sm)) := by
    calc _ ≤ ∑ _j ∈ range B, H ^ 2 * (((M : ℝ) + 1) * Sm) := Finset.sum_le_sum hone
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgauss : ∑ j ∈ range B, (((j + 1 : ℕ) : ℝ)) * (1 / (2 * R)) =
      (B : ℝ) * ((B : ℝ) + 1) / 2 * (1 / (2 * R)) := by
    obtain ⟨K, rfl⟩ : ∃ K, B = K + 1 := ⟨B - 1, by omega⟩
    have h1 := two_mul_sum_range_succ K
    have h2 : (2 : ℝ) * ∑ j ∈ range (K + 1), ((j + 1 : ℕ) : ℝ) = ((K : ℝ) + 1) * ((K : ℝ) + 2) := by
      exact_mod_cast h1
    rw [← Finset.sum_mul]
    push_cast at h2 ⊢
    congr 1
    linarith
  rw [hgauss] at hsum
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have h6 : ((B : ℝ) + 1) / 2 * (1 / (2 * R)) ≤ H ^ 2 * (((M : ℝ) + 1) * Sm) := by
    have e : (B : ℝ) * ((B : ℝ) + 1) / 2 * (1 / (2 * R)) =
        (B : ℝ) * (((B : ℝ) + 1) / 2 * (1 / (2 * R))) := by ring
    rw [e] at hsum
    exact le_of_mul_le_mul_left hsum hB0
  rw [div_le_iff₀ (by positivity)]
  have e7 : ((B : ℝ) + 1) / 2 * (1 / (2 * R)) = ((B : ℝ) + 1) / (4 * R) := by
    field_simp
    ring
  rw [e7, div_le_iff₀ (by positivity)] at h6
  nlinarith

/-- **The mean of the distance on progressions.** For every `K ≥ 6(M + 1)`, uniformly in `q ≥ r`, the phases of `r + qm`, `m < K`, have
mean distance `≥ 1/(48 R H² (M + 1)²)` to every rotation `φ + ℤ`. -/
theorem le_sum_rotDist_ap (S : WordSetup H R M k N₁ c t) (φ : ℝ) {q r K : ℕ} (hq : 1 ≤ q)
    (hr : r ≤ q) (hK : 6 * M + 6 ≤ K) :
    (K : ℝ) / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) ≤ ∑ m ∈ range K, rotDist t φ (r + q * m) := by
  set Q := 6 * M + 6 with hQ
  have hQ0 : 0 < Q := by omega
  set B := K / Q with hB
  have hB1 : 1 ≤ B := (Nat.one_le_div_iff hQ0).mpr hK
  have hBle : B * Q ≤ K := Nat.div_mul_le_self K Q
  have hNlt : K < (B + 1) * Q := by
    have := Nat.lt_succ_iff.mpr (le_refl (K / Q))
    exact Nat.lt_mul_of_div_lt this hQ0
  have hmain := S.le_sum_rotDist_ap_mul φ hq hr hB1
  have hsub : ∑ m ∈ range (B * Q), rotDist t φ (r + q * m) ≤ ∑ m ∈ range K, rotDist t φ (r + q * m) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hBle) fun n _ _ =>
      rotDist_nonneg t φ _
  refine le_trans ?_ (hmain.trans hsub)
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hH0 : 0 < H := by linarith [S.one_le_H]
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hNr : (K : ℝ) ≤ ((B : ℝ) + 1) * (6 * ((M : ℝ) + 1)) := by
    have : (K : ℝ) ≤ (((B + 1) * Q : ℕ) : ℝ) := by exact_mod_cast hNlt.le
    rw [hQ] at this
    push_cast at this
    linarith
  have hNr2 : (K : ℝ) ≤ 2 * (B : ℝ) * (6 * ((M : ℝ) + 1)) := by nlinarith
  have e : (K : ℝ) / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) =
      ((K : ℝ) / (12 * ((M : ℝ) + 1))) / (4 * R * H ^ 2 * ((M : ℝ) + 1)) := by
    field_simp
    ring
  rw [e]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The mean of the distance.** For every `N ≥ 6(M + 1)` the phases of `n < N` have mean distance `≥ 1/(48 R H² (M + 1)²)` to every
rotation. -/
theorem le_sum_rotDist (S : WordSetup H R M k N₁ c t) (φ : ℝ) {N : ℕ} (hN : 6 * M + 6 ≤ N) :
    (N : ℝ) / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) ≤ ∑ n ∈ range N, rotDist t φ n := by
  have h := S.le_sum_rotDist_ap φ (q := 1) (r := 0) le_rfl (Nat.zero_le 1) hN
  simpa using h

/-- The unrotated mean. -/
theorem le_sum_phaseDist (S : WordSetup H R M k N₁ c t) {N : ℕ} (hN : 6 * M + 6 ≤ N) :
    (N : ℝ) / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) ≤ ∑ n ∈ range N, phaseDist t n := by
  refine (S.le_sum_rotDist 0 hN).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun n _ => rotDist_zero t n

end WordSetup

/-- Hypotheses on the size of the height `exp L`, with `ℓ = log L`. -/
structure HeightSize (L ℓ : ℝ) : Prop where
  log_eq : ℓ = Real.log L
  one_le : 1 ≤ ℓ
  log_le : 100 * ℓ ≤ L
  hundred_le : 100 ≤ L

theorem HeightSize.exp_eq {L ℓ : ℝ} (h : HeightSize L ℓ) : Real.exp ℓ = L := by
  rw [h.log_eq, Real.exp_log (by linarith [h.hundred_le])]

theorem HeightSize.M_add_two_le {L ℓ : ℝ} (h : HeightSize L ℓ) {M : ℕ}
    (hM : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) : (M : ℝ) + 2 ≤ L ^ 3 := by
  have hL := h.hundred_le
  have h1 := h.log_le
  have hsq : 0 < L ^ 2 := by positivity
  have h2 : 6 * L ^ 2 * ℓ ≤ L ^ 2 * (6 / 100 * L) := by nlinarith
  have h3 : L ^ 3 = L ^ 2 * L := by ring
  nlinarith

theorem HeightSize.word {L ℓ : ℝ} (h : HeightSize L ℓ) {M k : ℕ} (hM1 : 6 * L ^ 2 * ℓ ≤ M)
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hk : (k : ℝ) ≤ L + 1) :
    ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ (M + 1) := by
  refine prod_choose_lt_of_log ?_
  have hL := h.hundred_le
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : Real.log ((M : ℝ) + 2) ≤ 3 * ℓ := by
    have h1 := Real.log_le_log (by positivity) (h.M_add_two_le hM2)
    rw [Real.log_pow] at h1
    rw [h.log_eq]
    exact_mod_cast h1
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith)
  have hsq : ((k : ℝ) + 2) ^ 2 ≤ 2 * L ^ 2 := by nlinarith
  calc ((k : ℝ) + 2) ^ 2 * Real.log ((M : ℝ) + 2) ≤ 2 * L ^ 2 * (3 * ℓ) :=
        mul_le_mul hsq hlog hlog0 (by positivity)
    _ = 6 * L ^ 2 * ℓ := by ring
    _ ≤ M := hM1

theorem four_pow_eq (n : ℕ) : (4 : ℝ) ^ n = Real.exp ((n : ℝ) * (2 * Real.log 2)) := by
  rw [Real.exp_nat_mul, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
  norm_num

theorem sixteen_pow_eq (n : ℕ) : (16 : ℝ) ^ n = Real.exp ((n : ℝ) * (4 * Real.log 2)) := by
  rw [Real.exp_nat_mul, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
  norm_num

theorem HeightSize.low {L ℓ : ℝ} (h : HeightSize L ℓ) {N : ℕ} (hN : (N : ℝ) ≤ L / 2) :
    4 * ((N : ℝ) + 2) * 3 ^ (N + 2) * π ≤ Real.exp L := by
  have hL := h.hundred_le
  have h100 := h.log_le
  have ha1 := Real.log_two_gt_d9
  have ha2 := Real.log_two_lt_d9
  set a := Real.log 2 with ha
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h3 : (3 : ℝ) ^ (N + 2) ≤ Real.exp ((L / 2 + 2) * (2 * a)) := by
    calc (3 : ℝ) ^ (N + 2) ≤ 4 ^ (N + 2) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = Real.exp (((N + 2 : ℕ) : ℝ) * (2 * a)) := four_pow_eq _
      _ ≤ _ := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (by linarith))
        push_cast
        linarith
  have h4 : 4 * ((N : ℝ) + 2) * π ≤ Real.exp (4 * a + ℓ) := by
    have e16 : Real.exp (4 * a) = 16 := by
      have := sixteen_pow_eq 1
      simpa using this.symm
    rw [Real.exp_add, e16, h.exp_eq]
    have hπ := Real.pi_lt_four
    have hπ0 := Real.pi_pos
    have h5 : (N : ℝ) + 2 ≤ L := by linarith
    calc 4 * ((N : ℝ) + 2) * π ≤ 4 * L * 4 := by
          refine mul_le_mul (by linarith) hπ.le hπ0.le (by linarith)
      _ = 16 * L := by ring
  calc 4 * ((N : ℝ) + 2) * 3 ^ (N + 2) * π = (4 * ((N : ℝ) + 2) * π) * 3 ^ (N + 2) := by ring
    _ ≤ Real.exp (4 * a + ℓ) * Real.exp ((L / 2 + 2) * (2 * a)) :=
        mul_le_mul h4 h3 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (4 * a + ℓ + (L / 2 + 2) * (2 * a)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp L := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith

theorem HeightSize.step {L ℓ : ℝ} (h : HeightSize L ℓ) {M N : ℕ}
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hN : L / 2 - 1 ≤ (N : ℝ)) :
    Real.exp L * (2 * ((M : ℝ) + 1) ^ 3) ≤ π * 16 ^ N := by
  have hL := h.hundred_le
  have h100 := h.log_le
  have ha1 := Real.log_two_gt_d9
  have ha2 := Real.log_two_lt_d9
  set a := Real.log 2 with ha
  have hMle : (M : ℝ) + 1 ≤ Real.exp (3 * ℓ) := by
    have e : Real.exp (3 * ℓ) = L ^ 3 := by
      have := Real.exp_nat_mul ℓ 3
      push_cast at this
      rw [this, h.exp_eq]
    rw [e]
    linarith [h.M_add_two_le hM2]
  have hcube : ((M : ℝ) + 1) ^ 3 ≤ Real.exp (9 * ℓ) := by
    have h1 := pow_le_pow_left₀ (by positivity) hMle 3
    have e : Real.exp (3 * ℓ) ^ 3 = Real.exp (9 * ℓ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [e] at h1
  have e2 : (2 : ℝ) = Real.exp a := (Real.exp_log (by norm_num)).symm
  have hπ : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  calc Real.exp L * (2 * ((M : ℝ) + 1) ^ 3) ≤ Real.exp L * (Real.exp a * Real.exp (9 * ℓ)) := by
        rw [← e2]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube (by norm_num))
          (Real.exp_pos _).le
    _ = Real.exp (L + (a + 9 * ℓ)) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp ((N : ℝ) * (4 * a)) := by
        refine Real.exp_le_exp.mpr ?_
        have h3 : (L / 2 - 1) * (4 * a) ≤ (N : ℝ) * (4 * a) :=
          mul_le_mul_of_nonneg_right hN (by linarith)
        nlinarith
    _ = 16 ^ N := (sixteen_pow_eq N).symm
    _ ≤ π * 16 ^ N := le_mul_of_one_le_left (by positivity) hπ

theorem HeightSize.up {L ℓ : ℝ} (h : HeightSize L ℓ) {M k : ℕ}
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hk : L ≤ (k : ℝ)) :
    Real.exp L * ((M : ℝ) + 1) ^ 2 < π * 4 ^ k := by
  have hL := h.hundred_le
  have h100 := h.log_le
  have ha1 := Real.log_two_gt_d9
  set a := Real.log 2 with ha
  have hMle : (M : ℝ) + 1 ≤ Real.exp (3 * ℓ) := by
    have e : Real.exp (3 * ℓ) = L ^ 3 := by
      have := Real.exp_nat_mul ℓ 3
      push_cast at this
      rw [this, h.exp_eq]
    rw [e]
    linarith [h.M_add_two_le hM2]
  have hsq : ((M : ℝ) + 1) ^ 2 ≤ Real.exp (6 * ℓ) := by
    have h1 := pow_le_pow_left₀ (by positivity) hMle 2
    have e : Real.exp (3 * ℓ) ^ 2 = Real.exp (6 * ℓ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [e] at h1
  have hπ : (1 : ℝ) < π := by linarith [Real.pi_gt_three]
  calc Real.exp L * ((M : ℝ) + 1) ^ 2 ≤ Real.exp L * Real.exp (6 * ℓ) :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = Real.exp (L + 6 * ℓ) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((k : ℝ) * (2 * a)) := by
        refine Real.exp_le_exp.mpr ?_
        have h3 : L * (2 * a) ≤ (k : ℝ) * (2 * a) := mul_le_mul_of_nonneg_right hk (by linarith)
        nlinarith
    _ = 4 ^ k := (four_pow_eq k).symm
    _ < π * 4 ^ k := lt_mul_of_one_lt_left (by positivity) hπ

theorem HeightSize.precision {L ℓ : ℝ} (h : HeightSize L ℓ) {M : ℕ}
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) :
    ((M : ℝ) + 1) ^ 2 * (1 / (4096 * L ^ 4 * ℓ ^ 2)) < 1 / 32 := by
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hpos : 0 < L ^ 2 * ℓ := by positivity
  have h1 : (M : ℝ) + 1 ≤ 8 * (L ^ 2 * ℓ) := by
    have : (1 : ℝ) ≤ L ^ 2 * ℓ := by nlinarith
    nlinarith
  have h2 : ((M : ℝ) + 1) ^ 2 ≤ (8 * (L ^ 2 * ℓ)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have e : (8 * (L ^ 2 * ℓ)) ^ 2 * (1 / (4096 * L ^ 4 * ℓ ^ 2)) = 1 / 64 := by
    field_simp
    norm_num
  have h3 : ((M : ℝ) + 1) ^ 2 * (1 / (4096 * L ^ 4 * ℓ ^ 2)) ≤
      (8 * (L ^ 2 * ℓ)) ^ 2 * (1 / (4096 * L ^ 4 * ℓ ^ 2)) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

/-- The heights to which the size hypotheses apply. -/
theorem eventually_heightSize : ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
    HeightSize (Real.log |t|) (Real.log (Real.log |t|)) := by
  have hev1 : ∀ᶠ L : ℝ in atTop, 1 ≤ Real.log L := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hev2 : ∀ᶠ L : ℝ in atTop, 100 * Real.log L ≤ L := by
    have h1 := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 100 by norm_num)
    filter_upwards [h1, hev1, eventually_gt_atTop (0 : ℝ)] with L hL h12 hLpos
    simp only [id, Real.norm_eq_abs] at hL
    rw [abs_of_pos (by linarith), abs_of_pos hLpos] at hL
    linarith
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hev1.and (hev2.and (eventually_ge_atTop (100 : ℝ))))
  refine ⟨Real.exp L₀, Real.exp_pos _, fun t ht => ?_⟩
  have htpos : 0 < |t| := lt_of_lt_of_le (Real.exp_pos _) ht
  have hLge : L₀ ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le htpos]
    exact ht
  obtain ⟨h1, h2, h3⟩ := hL₀ _ hLge
  exact ⟨rfl, h1, h2, h3⟩

/-- The word of height `1` at height `exp L`. -/
theorem HeightSize.exists_setup {L ℓ t : ℝ} (h : HeightSize L ℓ) (hexp : Real.exp L = |t|) {M k N : ℕ}
    (hM1 : 6 * L ^ 2 * ℓ ≤ M) (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hk1 : L ≤ k) (hk2 : (k : ℝ) ≤ L + 1)
    (hN1 : (N : ℝ) ≤ L / 2) (hN2 : L / 2 - 1 ≤ (N : ℝ)) (hN3 : 1 ≤ N) :
    ∃ c, WordSetup 1 16 M k N c t := by
  obtain ⟨c, hc, hm, h0⟩ := exists_normalized_word (h.word hM1 hM2 hk2)
  refine ⟨c, ⟨le_rfl, by norm_num, fun a => ?_, hm, h0, hN3, ?_, ?_, ?_⟩⟩
  · exact_mod_cast hc.bound a
  · rw [← hexp]
    have := h.low hN1
    simpa using this
  · rw [← hexp]
    have := h.step hM2 hN2
    simpa using this
  · rw [← hexp]
    have := h.up hM2 hk1
    simpa using this

/-- The word of height `1` at height `exp L`, for any length `K ≥ 48 L² ℓ`. -/
theorem HeightSize.exists_data {L ℓ t : ℝ} (h : HeightSize L ℓ) (hexp : Real.exp L = |t|) {K : ℕ}
    (hK : 48 * L ^ 2 * ℓ ≤ K) :
    ∃ (M k N : ℕ) (c : ℕ → ℤ), WordSetup 1 16 M k N c t ∧ 6 * M + 6 ≤ K ∧
      ((M : ℝ) + 1) ^ 2 ≤ 64 * (L ^ 4 * ℓ ^ 2) := by
  have hL := h.hundred_le
  have hℓ := h.one_le
  set M := ⌈6 * L ^ 2 * ℓ⌉₊ with hM
  set k := ⌈L⌉₊ with hk
  set N := ⌊L / 2⌋₊ with hN
  have hM1 : 6 * L ^ 2 * ℓ ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : L ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hN1 : (N : ℝ) ≤ L / 2 := Nat.floor_le (by linarith)
  have hN2 : L / 2 - 1 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one (L / 2)
    linarith
  have hN3 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hone : (1 : ℝ) ≤ L ^ 2 * ℓ := by nlinarith
  obtain ⟨c, hS⟩ := h.exists_setup hexp hM1 hM2 hk1 hk2 hN1 hN2 hN3
  refine ⟨M, k, N, c, hS, ?_, ?_⟩
  · have : ((6 * M + 6 : ℕ) : ℝ) ≤ K := by
      push_cast
      nlinarith
    exact_mod_cast this
  · have hM8 : (M : ℝ) + 1 ≤ 8 * (L ^ 2 * ℓ) := by nlinarith
    calc ((M : ℝ) + 1) ^ 2 ≤ (8 * (L ^ 2 * ℓ)) ^ 2 := pow_le_pow_left₀ (by positivity) hM8 2
      _ = _ := by ring

/-- **Non-alignment at length `(log |t|)² log log |t|`.** At every large height, with `L = log |t|` and `ℓ = log L`, some `n ≤ 50 L² ℓ`
has `t log n/2π` at distance more than `1/(4096 L⁴ ℓ²)` from the integers. -/
theorem exists_not_aligned_of_large_of_word :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ 50 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ∧
        ∀ j : ℤ, 1 / (4096 * Real.log |t| ^ 4 * Real.log (Real.log |t|) ^ 2) <
          |t * Real.log n / (2 * π) - j| := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp ⊢
  generalize Real.log L = ℓ at h ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  set M := ⌈6 * L ^ 2 * ℓ⌉₊ with hM
  set k := ⌈L⌉₊ with hk
  set N := ⌊L / 2⌋₊ with hN
  have hM1 : 6 * L ^ 2 * ℓ ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : L ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hN1 : (N : ℝ) ≤ L / 2 := Nat.floor_le (by linarith)
  have hN2 : L / 2 - 1 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one (L / 2)
    linarith
  have hN3 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  obtain ⟨c, hS⟩ := h.exists_setup hexp hM1 hM2 hk1 hk2 hN1 hN2 hN3
  obtain ⟨n, hn1, hn2, hn3⟩ := hS.exists_not_aligned (ε := 1 / (4096 * L ^ 4 * ℓ ^ 2)) (by
    have := h.precision hM2
    have e1 : (1 : ℝ) ^ 2 = 1 := by norm_num
    rw [e1, one_mul]
    norm_num
    norm_num at this
    linarith)
  refine ⟨n, by omega, ?_, hn3⟩
  have hn2' : (n : ℝ) ≤ 6 * (M : ℝ) + 5 := by exact_mod_cast hn2
  have : (1 : ℝ) ≤ L ^ 2 * ℓ := by nlinarith
  nlinarith

end

end GaloisForLFunctions.PrimeTorusTheory
