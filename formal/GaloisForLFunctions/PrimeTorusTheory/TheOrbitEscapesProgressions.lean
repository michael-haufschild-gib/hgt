import GaloisForLFunctions.PrimeTorusTheory.TheMassOfMisalignedPrimes

/-!
# The orbit escapes generalized progressions

Non-alignment at the corners `±1` says that the phases `θ_p = t log p/2π` are not all near `0` or `½`. Moments see only `|P(t)|`, so they need more: the phases must not all be near one rotation `φ`. More generally they must not lie near any low-rank progression. This is incommensurability made effective.

Let `c` be a word of height one, of length `M`. Its squared phase `y(u) = (|t|/2π) Σ_{a,b} (−c_a c_b) log(u + a + b)` is a continuous function of `u`: it decreases from above `½` to below `¼`, and along any lattice `(β + n)/h` it is log-convex, so it moves slowly (`exists_grid_point`). If `θ_p` lies within `ε` of a model `ψ_p` for all relevant primes, then `y(x/h)` lies within `(M + 1)² Λ ε` of the values of the model `Σ_{a,b} c_a c_b ψ(x + h(a + b))`, where `ψ` is extended additively over the prime factors and `Λ` bounds the number of prime factors.

The values of the model form a set `B`. If it is small, a cell of `[¼, ½]` is free of `±B` (`exists_free_cell`), and the slowly moving `y` lands in that cell. So:

**Theorem** (`exists_prime_escape`). Some prime `p ≤ N = 1 + Q h (6M + 5)`, `p ∤ Q`, has `θ_p` at distance more than `ε` from the model, as soon as `(M + 1)² Λ ε < 1/(4K)`, `K > 6|B|`, and `h ≳ K`.

The progression is `1 + Q(x + h(a + b))`, so every prime factor avoids `Q`: the escape happens away from any prescribed set of primes.

* **Rank `d`** (`exists_prime_escape_rank`). If `ψ_p = Σ_{i ≤ d} e(p, i) φ_i` with `|e| ≤ E`, then `|B| ≤ (2WE + 1)^d`, `W = (M + 1)² Λ`.
* **Rotations** (`exists_prime_not_near_rotation`). At height `t`, with `L = log |t|`, `ℓ = log L`, for every `φ` some prime `p ≪ L⁶ ℓ²Λ` not dividing `Q` has `θ_p` at distance `≫ 1/(L⁸ ℓ² Λ²)` from `φ + ℤ`, where `Λ ≍ ℓ + log Q`.
* **Many misaligned primes** (`exists_prime_not_mem_of_large`). Generators cost their number, not their size. So for every set `Ex` of `d ≤ L` primes, some prime `p ∉ Ex`, `p ≤ L^{9d + 6}`, has `θ_p` at distance `> L^{−(9d + 10)}` from the integers.
* **The modulus** (`norm_sum_primes_le`). So `|Σ_{p<N} p^{−½ + it}| ≤ Σ_{p<N} p^{−½} − 1/(10²⁵ L¹⁹ ℓ¹⁴)` for `N` past `10⁹ L⁶ ℓ⁴`, against every rotation. This is what moments can see.
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-! ### The free cell -/

/-- **A cell of `[¼, ½]` free of a finite set modulo `1`.** -/
theorem exists_free_cell (B : Finset ℝ) {K : ℕ} (hK : 3 * B.card < K) :
    ∃ i : ℕ, K ≤ i ∧ i < 2 * K ∧ ∀ b ∈ B, ∀ y : ℝ, (i : ℝ) / (4 * K) ≤ y → y ≤ ((i : ℝ) + 1) / (4 * K) →
      ∀ m : ℤ, 1 / (4 * (K : ℝ)) ≤ |y - b - m| := by
  classical
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK0
  set cell : ℝ → ℕ := fun b => ⌊4 * (K : ℝ) * Int.fract b⌋₊ with hcell
  set Ex : Finset ℕ := B.image cell ∪ B.image (fun b => cell b + 1) ∪ B.image (fun b => cell b - 1)
    with hEx
  have hExcard : Ex.card ≤ 3 * B.card := by
    rw [hEx]
    have h1 := Finset.card_union_le (B.image cell ∪ B.image (fun b => cell b + 1))
      (B.image (fun b => cell b - 1))
    have h2 := Finset.card_union_le (B.image cell) (B.image (fun b => cell b + 1))
    have h3 : (B.image cell).card ≤ B.card := Finset.card_image_le
    have h4 : (B.image (fun b => cell b + 1)).card ≤ B.card := Finset.card_image_le
    have h5 : (B.image (fun b => cell b - 1)).card ≤ B.card := Finset.card_image_le
    omega
  have hIco : (Finset.Ico K (2 * K)).card = K := by
    rw [Nat.card_Ico]
    omega
  obtain ⟨i, hi, hiEx⟩ : ∃ i ∈ Finset.Ico K (2 * K), i ∉ Ex :=
    Finset.exists_mem_notMem_of_card_lt_card (by omega)
  obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
  refine ⟨i, hi1, hi2, fun b hb y hy1 hy2 m => ?_⟩
  set f := Int.fract b with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg b
  have hf1 : f < 1 := Int.fract_lt_one b
  set j := cell b with hj
  have hjlow : (j : ℝ) ≤ 4 * (K : ℝ) * f := Nat.floor_le (by positivity)
  have hjup : 4 * (K : ℝ) * f < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hij : i ≠ j ∧ i ≠ j + 1 ∧ i ≠ j - 1 := by
    refine ⟨fun h => hiEx ?_, fun h => hiEx ?_, fun h => hiEx ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, h.symm⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, h.symm⟩))
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, h.symm⟩)
  have h4K : (0 : ℝ) < 4 * K := by positivity
  rw [div_le_iff₀ h4K] at hy1
  rw [le_div_iff₀ h4K] at hy2
  have hb' : b = (⌊b⌋ : ℝ) + f := (Int.floor_add_fract b).symm
  set m' : ℤ := m + ⌊b⌋ with hm'
  have e : y - b - m = y - f - m' := by
    rw [hm']
    push_cast
    linarith
  rw [e, div_le_iff₀ h4K]
  have hir : (K : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
  have hir2 : (i : ℝ) + 1 ≤ 2 * (K : ℝ) := by exact_mod_cast hi2
  have hyl : (K : ℝ) ≤ y * (4 * K) := by linarith
  have hyu : y * (4 * K) ≤ 2 * (K : ℝ) := by linarith
  -- The target is `1 ≤ |y − f − m'| · 4K`.
  rcases eq_or_ne m' 0 with hm0 | hm0
  · rw [hm0]
    simp only [Int.cast_zero, sub_zero]
    rcases lt_or_gt_of_ne hij.1 with hlt | hgt
    · -- `i < j`, so `i + 2 ≤ j`
      have h2 : i + 2 ≤ j := by
        have := hij.2.2
        omega
      have h2r : (i : ℝ) + 2 ≤ j := by exact_mod_cast h2
      have h3 : 1 ≤ (f - y) * (4 * K) := by nlinarith
      have hle := neg_le_abs (y - f)
      have := mul_le_mul_of_nonneg_right hle h4K.le
      linarith
    · have h2 : j + 2 ≤ i := by
        have := hij.2.1
        omega
      have h2r : (j : ℝ) + 2 ≤ i := by exact_mod_cast h2
      have h3 : 1 ≤ (y - f) * (4 * K) := by nlinarith
      have hle := le_abs_self (y - f)
      have := mul_le_mul_of_nonneg_right hle h4K.le
      linarith
  · -- `|m'| ≥ 1`
    have hquarter : (1 : ℝ) / 4 ≤ |y - f - m'| := by
      have hyl' : 1 / 4 ≤ y := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith
      have hyu' : y ≤ 1 / 2 := by
        rw [le_div_iff₀ (by norm_num)]
        nlinarith
      rcases lt_or_gt_of_ne hm0 with hneg | hpos
      · have : (m' : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
        have h5 : 1 / 4 ≤ y - f - m' := by linarith
        exact h5.trans (le_abs_self _)
      · have : (1 : ℝ) ≤ m' := by exact_mod_cast hpos
        have h5 : 1 / 4 ≤ -(y - f - m') := by linarith
        exact h5.trans (neg_le_abs _)
    have := mul_le_mul_of_nonneg_right hquarter h4K.le
    nlinarith

/-! ### The word, and the slow descent of its phase -/

/-- A word of height one at height `t`, with room at both ends. -/
structure FineWord (M k N₁ : ℕ) (c : ℕ → ℤ) (t : ℝ) : Prop where
  bound : ∀ a, |(c a : ℝ)| ≤ 1
  moments : ∀ j ≤ k, binomMoment M c j = 0
  zero_ne : c 0 ≠ 0
  one_le_N : 1 ≤ N₁
  low : 4 * ((N₁ : ℝ) + 3) * 3 ^ (N₁ + 3) * π ≤ |t|
  top : |t| * (2 * ((M : ℝ) + 1) ^ 2) ≤ π * 4 ^ k

/-- The squared phase of a word. -/
def wordHeight (M : ℕ) (c : ℕ → ℤ) (t u : ℝ) : ℝ := |t| / (2 * π) * -wordForm M c u

theorem wordHeight_anti {M : ℕ} {c : ℕ → ℤ} {t u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    wordHeight M c t v ≤ wordHeight M c t u := by
  have h := wordForm_mono M c (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr (lt_of_lt_of_le hu huv)) huv
  unfold wordHeight
  have hc : 0 ≤ |t| / (2 * π) := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hc

namespace FineWord

variable {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ}

theorem abs_pos (S : FineWord M k N₁ c t) : 0 < |t| := by
  have : 0 < 4 * ((N₁ : ℝ) + 3) * 3 ^ (N₁ + 3) * π := by
    have := Real.pi_pos
    positivity
  linarith [S.low]

theorem mass (S : FineWord M k N₁ c t) : binomMoment M c 0 = 0 := S.moments 0 (Nat.zero_le k)

theorem pos (S : FineWord M k N₁ c t) {u : ℝ} (hu : 1 ≤ u) : 0 < -wordForm M c u := by
  have h1 := three_pow_le_neg_wordForm (H := 1) le_rfl S.bound S.zero_ne S.mass hu
  have h2 : 0 < (1 / (3 * (1 : ℝ))) ^ (u + 1) / (4 * (u + 1)) := by
    have : 0 < u + 1 := by linarith
    positivity
  linarith

/-- The phase is at least `½` up to `N₁ + 2`. -/
theorem half_le (S : FineWord M k N₁ c t) {u : ℝ} (hu : 0 < u) (hu2 : u ≤ (N₁ : ℝ) + 2) :
    1 / 2 ≤ wordHeight M c t u := by
  refine le_trans ?_ (wordHeight_anti hu hu2)
  have hN : (1 : ℝ) ≤ (N₁ : ℝ) + 2 := by
    have : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg N₁
    linarith
  have h1 := three_pow_le_neg_wordForm (H := 1) le_rfl S.bound S.zero_ne S.mass hN
  have htpos := S.abs_pos
  have hπ := Real.pi_pos
  have e1 : (N₁ : ℝ) + 2 + 1 = ((N₁ + 3 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [e1, Real.rpow_natCast] at h1
  have e2 : (1 / (3 * (1 : ℝ))) ^ (N₁ + 3) = 1 / 3 ^ (N₁ + 3) := by
    rw [mul_one, div_pow, one_pow]
  rw [e2] at h1
  have h3p : (0 : ℝ) < 3 ^ (N₁ + 3) := by positivity
  have h3 : π / |t| ≤ 1 / 3 ^ (N₁ + 3) / (4 * ((N₁ + 3 : ℕ) : ℝ)) := by
    rw [div_div, div_le_div_iff₀ htpos (by positivity)]
    push_cast
    have := S.low
    nlinarith
  have h4 : π / |t| ≤ -wordForm M c ((N₁ : ℝ) + 2) := h3.trans h1
  unfold wordHeight
  have e : |t| / (2 * π) * (π / |t|) = 1 / 2 := by
    field_simp
  calc 1 / 2 = |t| / (2 * π) * (π / |t|) := e.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- The phase is at most `¼` past `4(M + 1)`. -/
theorem le_quarter (S : FineWord M k N₁ c t) {u : ℝ} (hu : 4 * ((M : ℝ) + 1) ≤ u) :
    wordHeight M c t u ≤ 1 / 4 := by
  have h1 := abs_wordForm_le (H := 1) zero_le_one S.bound S.moments hu
  have h2 := neg_le_abs (wordForm M c u)
  have hπ := Real.pi_pos
  have htpos := S.abs_pos
  unfold wordHeight
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  have h3 : -wordForm M c u ≤ ((M : ℝ) + 1) ^ 2 / 4 ^ k := by
    have e : (1 : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2 * (1 / 4) ^ k = ((M : ℝ) + 1) ^ 2 / 4 ^ k := by
      rw [div_pow, one_pow]
      ring
    linarith
  calc |t| / (2 * π) * -wordForm M c u ≤ |t| / (2 * π) * (((M : ℝ) + 1) ^ 2 / 4 ^ k) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 1 / 4 := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
        have := S.top
        nlinarith

/-- The word on the lattice `(x₀ + n)/h` is the logarithmic form with shifts `h a`. -/
theorem wordForm_lattice (S : FineWord M k N₁ c t) {h : ℕ} (hh : 1 ≤ h) {x : ℝ} (hx : 0 < x) :
    wordForm M c (x / h) =
      logForm (range (M + 1)) (fun a => (c a : ℝ)) (fun a => (h : ℝ) * (a : ℝ)) x := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  rw [wordForm_div S.mass hx hh0]
  unfold logForm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 2
  ring

/-- **Log-convexity along every lattice.** -/
theorem logConvex_lattice (S : FineWord M k N₁ c t) {h : ℕ} (hh : 1 ≤ h) {x₀ : ℝ} (hx₀ : (h : ℝ) ≤ x₀)
    (n : ℕ) :
    (-wordForm M c ((x₀ + ((n + 1 : ℕ) : ℝ)) / h)) ^ 2 ≤
      (-wordForm M c ((x₀ + (n : ℝ)) / h)) * (-wordForm M c ((x₀ + ((n + 2 : ℕ) : ℝ)) / h)) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxp : 0 < x₀ + n := by linarith
  have hu : 1 ≤ (x₀ + n) / h := by
    rw [le_div_iff₀ hh0]
    linarith
  have hneg := S.pos hu
  have hs : ∀ a ∈ range (M + 1), (0 : ℝ) ≤ (h : ℝ) * (a : ℝ) := fun a _ => by positivity
  have hv := wordMass_eq_zero S.mass
  have hconv := logForm_logConvex (range (M + 1)) hs hv hxp (by
    rw [← S.wordForm_lattice hh hxp]
    linarith)
  have e1 : x₀ + ((n + 1 : ℕ) : ℝ) = x₀ + n + 1 := by
    push_cast
    ring
  have e2 : x₀ + ((n + 2 : ℕ) : ℝ) = x₀ + n + 2 := by
    push_cast
    ring
  have e3 := S.wordForm_lattice hh (x := x₀ + n + 1) (by linarith)
  have e4 := S.wordForm_lattice hh (x := x₀ + n + 2) (by linarith)
  have e5 := S.wordForm_lattice hh hxp
  rw [e1, e2, e3, e4, e5, neg_sq, neg_mul_neg]
  exact hconv

/-- **The phase hits every cell.** Along the lattice `(β + x)/h` the squared phase moves by a factor `≥ 1 − η` at each step, so it lands in every
interval `[α, α + γ] ⊆ [¼, ½]` with `η (α + γ) ≤ γ`. -/
theorem exists_grid_point (S : FineWord M k N₁ c t) {h : ℕ} (hh : 1 ≤ h) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) {η α γ : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hα : 1 / 4 ≤ α) (hγ0 : 0 ≤ γ)
    (hαγ : α + γ ≤ 1 / 2) (hηγ : η * (α + γ) ≤ γ)
    (hstep : |t| / (2 * π) * (2 * ((M : ℝ) + 1) ^ 3) * (1 - η) ^ (h * N₁) ≤ 1 / 4) :
    ∃ x : ℕ, x ≤ h + 4 * (M + 1) * h ∧ α ≤ wordHeight M c t ((β + x) / h) ∧
      wordHeight M c t ((β + x) / h) ≤ α + γ := by
  classical
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have htpos := S.abs_pos
  have hπ := Real.pi_pos
  set x₀ : ℝ := β + h with hx₀
  have hx₀h : (h : ℝ) ≤ x₀ := by rw [hx₀]; linarith
  set g : ℕ → ℝ := fun n => -wordForm M c ((x₀ + n) / h) with hg
  have hu1 : ∀ n : ℕ, 1 ≤ (x₀ + n) / h := fun n => by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [le_div_iff₀ hh0]
    linarith
  have hgpos : ∀ n, 0 < g n := fun n => S.pos (hu1 n)
  have hconv : ∀ n, g (n + 1) ^ 2 ≤ g n * g (n + 2) := fun n => S.logConvex_lattice hh hx₀h n
  have hval : ∀ n : ℕ, wordHeight M c t ((x₀ + (n : ℝ)) / h) = |t| / (2 * π) * g n := fun n => rfl
  have hc : 0 < |t| / (2 * π) := by positivity
  -- Past the top the phase is small.
  set n₁ : ℕ := 4 * (M + 1) * h with hn₁
  have hP1 : wordHeight M c t ((x₀ + (n₁ : ℝ)) / h) ≤ α + γ := by
    refine (S.le_quarter ?_).trans (by linarith)
    rw [le_div_iff₀ hh0, hn₁]
    push_cast
    have : 0 ≤ x₀ := by linarith
    linarith
  have hex : ∃ n : ℕ, wordHeight M c t ((x₀ + (n : ℝ)) / h) ≤ α + γ := ⟨n₁, hP1⟩
  set n := Nat.find hex with hn
  have hn_spec : wordHeight M c t ((x₀ + n) / h) ≤ α + γ := Nat.find_spec hex
  have hn_le : n ≤ n₁ := Nat.find_min' hex hP1
  have hxpos : ∀ m : ℕ, 0 < (x₀ + m) / h := fun m => by linarith [hu1 m]
  refine ⟨h + n, ?_, ?_, ?_⟩
  · omega
  · have e : (β + ((h + n : ℕ) : ℝ)) / h = (x₀ + n) / h := by
      rw [hx₀]
      push_cast
      ring_nf
    rw [e]
    -- The lower bound.
    by_cases hbase : n ≤ h * N₁
    · have hu2 : (x₀ + n) / h ≤ (N₁ : ℝ) + 2 := by
        rw [div_le_iff₀ hh0, hx₀]
        have : (n : ℝ) ≤ (h : ℝ) * N₁ := by exact_mod_cast hbase
        nlinarith
      have := S.half_le (hxpos n) hu2
      linarith
    · have hn1 : 1 ≤ n := by
        have := Nat.zero_le (h * N₁)
        omega
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hnot : ¬ wordHeight M c t ((x₀ + n') / h) ≤ α + γ := Nat.find_min hex (by omega)
      push Not at hnot
      have hn'big : h * N₁ ≤ n' := by omega
      have hN₁h : 1 ≤ h * N₁ := Nat.mul_pos hh S.one_le_N
      have hr0 : 0 < 1 - η := by linarith
      have hg0 : g 0 ≤ 2 * ((M : ℝ) + 1) ^ 3 := by
        have h1 := neg_wordForm_one_le (M := M) (H := 1) S.bound
        have h2 := wordForm_mono M c (Set.mem_Ioi.mpr one_pos)
          (Set.mem_Ioi.mpr (by linarith [hu1 0])) (hu1 0)
        simp only [hg]
        rw [one_pow, mul_one] at h1
        linarith
      have hstepn : g 0 * (1 - η) ^ n' ≤ g n' := by
        have hpow : (1 - η) ^ n' ≤ (1 - η) ^ (h * N₁) :=
          pow_le_pow_of_le_one hr0.le (by linarith) hn'big
        have h3 : |t| / (2 * π) * (g 0 * (1 - η) ^ n') ≤
            |t| / (2 * π) * (2 * ((M : ℝ) + 1) ^ 3) * (1 - η) ^ (h * N₁) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hc.le
          exact mul_le_mul hg0 hpow (pow_nonneg hr0.le _) (by positivity)
        have h4 : |t| / (2 * π) * g n' > 1 / 4 := by
          rw [hval] at hnot
          linarith
        have h5 : |t| / (2 * π) * (g 0 * (1 - η) ^ n') ≤ |t| / (2 * π) * g n' := by linarith
        exact le_of_mul_le_mul_left h5 hc
      have hstep' := logConvex_step hgpos hconv hr0 (by omega : 1 ≤ n') hstepn
      have hnext : (1 - η) * wordHeight M c t ((x₀ + n') / h) ≤ wordHeight M c t ((x₀ + n) / h) := by
        rw [hval, hval, hn']
        have := mul_le_mul_of_nonneg_left hstep' hc.le
        nlinarith
      have h6 : (1 - η) * (α + γ) ≤ (1 - η) * wordHeight M c t ((x₀ + n') / h) :=
        mul_le_mul_of_nonneg_left hnot.le hr0.le
      nlinarith
  · have e : (β + ((h + n : ℕ) : ℝ)) / h = (x₀ + n) / h := by
      rw [hx₀]
      push_cast
      ring_nf
    rw [e]
    exact hn_spec

end FineWord

/-! ### The model -/

/-- The additive extension of a prime phase model over the factorization. -/
def modelPhase (ψ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * ψ p

/-- The number of prime factors is at most `log₂`. -/
theorem sum_factorization_lt {n Λ : ℕ} (hn : n ≠ 0) (hΛ : n < 2 ^ (Λ + 1)) :
    ∑ p ∈ n.primeFactors, n.factorization p ≤ Λ := by
  have h2 : 2 ^ (∑ p ∈ n.primeFactors, n.factorization p) ≤ n := by
    have hself := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at hself
    calc 2 ^ (∑ p ∈ n.primeFactors, n.factorization p)
        = ∏ p ∈ n.primeFactors, 2 ^ n.factorization p := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
          Finset.prod_le_prod' fun p hp =>
            Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _
      _ = n := hself
  have h3 : 2 ^ (∑ p ∈ n.primeFactors, n.factorization p) < 2 ^ (Λ + 1) := lt_of_le_of_lt h2 hΛ
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

/-- The distance to a model is subadditive over the prime factors. -/
theorem dist01_sub_modelPhase_le (t : ℝ) (ψ : ℕ → ℝ) (n : ℕ) :
    dist01 (t * Real.log n / (2 * π) - modelPhase ψ n) ≤
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * dist01 (t * Real.log p / (2 * π) - ψ p) := by
  have hlog : t * Real.log n / (2 * π) - modelPhase ψ n =
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * (t * Real.log p / (2 * π) - ψ p) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Finset.mul_sum,
      Finset.sum_div]
    unfold modelPhase
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  set J : ℤ := ∑ p ∈ n.primeFactors, (n.factorization p : ℤ) *
    round (t * Real.log p / (2 * π) - ψ p) with hJ
  refine (dist01_le_abs_sub_int _ J).trans ?_
  have e : t * Real.log n / (2 * π) - modelPhase ψ n - J =
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
        (t * Real.log p / (2 * π) - ψ p - round (t * Real.log p / (2 * π) - ψ p)) := by
    rw [hlog, hJ]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  rfl

/-- The progression `1 + Q(x + h(a + b))`. -/
def apTerm (Q x h a b : ℕ) : ℕ := 1 + Q * (x + h * (a + b))

/-- The size of the progression on the grid. -/
theorem apTerm_le {Q x h a b M : ℕ} (hx : x ≤ h + 4 * (M + 1) * h) (ha : a ≤ M) (hb : b ≤ M) :
    apTerm Q x h a b ≤ 1 + Q * (h * (6 * M + 5)) := by
  unfold apTerm
  have h1 : x + h * (a + b) ≤ h * (6 * M + 5) := by
    have h2 : h * (a + b) ≤ h * (2 * M) := Nat.mul_le_mul_left _ (by omega)
    calc x + h * (a + b) ≤ h + 4 * (M + 1) * h + h * (2 * M) := by omega
      _ = h * (6 * M + 5) := by ring
  have := Nat.mul_le_mul_left Q h1
  omega

/-- The word phase on the progression is the squared phase at `(1/Q + x)/h`. -/
theorem word_sum_apTerm {M : ℕ} {c : ℕ → ℤ} (hm : binomMoment M c 0 = 0) (t : ℝ) {Q x h : ℕ}
    (hQ : 1 ≤ Q) (hh : 1 ≤ h) :
    ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) *
        (t * Real.log (apTerm Q x h a b) / (2 * π)) =
      t / (2 * π) * wordForm M c ((1 / (Q : ℝ) + x) / h) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have e : (1 / (Q : ℝ) + x) / h = (1 + (Q : ℝ) * x) / ((Q : ℝ) * h) := by
    field_simp
  rw [e, wordForm_div hm (by positivity) (by positivity), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e2 : ((apTerm Q x h a b : ℕ) : ℝ) = 1 + (Q : ℝ) * x + (Q : ℝ) * h * ((a : ℝ) + b) := by
    unfold apTerm
    push_cast
    ring
  rw [e2]
  ring

/-- **The escape from a model.** If the values of the model on the progressions lie in a small set `B` modulo `1`, some prime up to `N = 1 + Q h (6M + 5)`,
not dividing `Q`, has its phase at distance more than `ε` from its model. -/
theorem exists_prime_escape {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ} (S : FineWord M k N₁ c t) {Q h : ℕ}
    (hQ : 1 ≤ Q) (hh : 1 ≤ h) (ψ : ℕ → ℝ) (B : Finset ℝ)
    (hB : ∀ x : ℕ, x ≤ h + 4 * (M + 1) * h → ∃ b ∈ B, ∃ m : ℤ, ∑ a ∈ range (M + 1), ∑ b' ∈ range (M + 1),
      (c a : ℝ) * (c b' : ℝ) * modelPhase ψ (apTerm Q x h a b') = b + m)
    {K Λ : ℕ} (hK : 3 * (2 * B.card) < K)
    (hstep : |t| / (2 * π) * (2 * ((M : ℝ) + 1) ^ 3) * (1 - 1 / (2 * (K : ℝ))) ^ (h * N₁) ≤ 1 / 4)
    (hΛ : 1 + Q * (h * (6 * M + 5)) < 2 ^ (Λ + 1)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ((M : ℝ) + 1) ^ 2 * ((Λ : ℝ) * ε) < 1 / (4 * (K : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ Q ∧ p ≤ 1 + Q * (h * (6 * M + 5)) ∧
      ε < dist01 (t * Real.log p / (2 * π) - ψ p) := by
  classical
  by_contra hcon
  push Not at hcon
  have hK0 : 0 < K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK0
  set B' : Finset ℝ := B ∪ B.image (fun b => -b) with hB'
  have hB'card : 3 * B'.card < K := by
    rw [hB']
    have h1 := Finset.card_union_le B (B.image fun b => -b)
    have h2 : (B.image fun b => -b).card ≤ B.card := Finset.card_image_le
    omega
  obtain ⟨i, hi1, hi2, hfree⟩ := exists_free_cell B' hB'card
  have hir : (K : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
  have hir2 : (i : ℝ) + 1 ≤ 2 * (K : ℝ) := by exact_mod_cast hi2
  have h4K : (0 : ℝ) < 4 * K := by positivity
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hβ1 : 1 / (Q : ℝ) ≤ 1 := by
    rw [div_le_one hQ0]
    exact hQ1
  -- A grid point in the free cell.
  obtain ⟨x, hxle, hx1, hx2⟩ := S.exists_grid_point hh (β := 1 / (Q : ℝ)) (by positivity) hβ1
    (η := 1 / (2 * (K : ℝ))) (α := (i : ℝ) / (4 * K)) (γ := 1 / (4 * (K : ℝ))) (by positivity)
    (by
      rw [div_lt_one (by positivity)]
      linarith)
    (by
      rw [div_le_div_iff₀ (by norm_num) h4K]
      linarith)
    (by positivity)
    (by
      rw [← add_div, div_le_div_iff₀ h4K (by norm_num)]
      linarith)
    (by
      rw [← add_div, div_mul_div_comm, div_le_div_iff₀ (by positivity) h4K]
      have : (0 : ℝ) < K := hKr
      nlinarith)
    hstep
  set u : ℝ := (1 / (Q : ℝ) + x) / h with hu
  set y : ℝ := wordHeight M c t u with hy
  -- The model value.
  obtain ⟨b₀, hb₀, m₀, hm₀⟩ := hB x hxle
  set A := range (M + 1) with hA
  -- Each term is near its model.
  have hterm : ∀ a ∈ A, ∀ b ∈ A,
      dist01 (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)) ≤ (Λ : ℝ) * ε := by
    intro a ha b hb
    have ha' := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    set n := apTerm Q x h a b with hn
    have hnle : n ≤ 1 + Q * (h * (6 * M + 5)) := apTerm_le hxle ha' hb'
    have hn0 : n ≠ 0 := by
      rw [hn]
      unfold apTerm
      omega
    have hsum := sum_factorization_lt hn0 (lt_of_le_of_lt hnle hΛ)
    refine (dist01_sub_modelPhase_le t ψ n).trans ?_
    have hpt : ∀ p ∈ n.primeFactors, (n.factorization p : ℝ) * dist01 (t * Real.log p / (2 * π) - ψ p) ≤
        (n.factorization p : ℝ) * ε := by
      intro p hp
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      refine hcon p hpp ?_ ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans hnle)
      intro hpQ
      have h1 : p ∣ Q * (x + h * (a + b)) := hpQ.trans (Dvd.intro _ rfl)
      have h2 : p ∣ 1 := by
        have h3 : p ∣ 1 + Q * (x + h * (a + b)) := hpn
        exact (Nat.dvd_add_left h1).mp h3
      exact hpp.one_lt.ne' (Nat.dvd_one.mp h2)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hε0
    exact_mod_cast hsum
  -- Assemble over the word.
  set W : ℝ := ∑ a ∈ A, ∑ b ∈ A, (c a : ℝ) * (c b : ℝ) * (t * Real.log (apTerm Q x h a b) / (2 * π)) with hW
  have hWeq : W = t / (2 * π) * wordForm M c u := word_sum_apTerm S.mass t hQ hh
  set JJ : ℤ := ∑ a ∈ A, ∑ b ∈ A, c a * c b *
    round (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)) with hJJ
  have hclose : |W - (b₀ + (m₀ + JJ : ℤ))| ≤ ((M : ℝ) + 1) ^ 2 * ((Λ : ℝ) * ε) := by
    have e : W - (b₀ + (m₀ + JJ : ℤ)) = ∑ a ∈ A, ∑ b ∈ A, (c a : ℝ) * (c b : ℝ) *
        ((t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)) -
          round (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b))) := by
      have hsplit : ∑ a ∈ A, ∑ b ∈ A, (c a : ℝ) * (c b : ℝ) *
          ((t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)) -
            round (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b))) =
          W - (∑ a ∈ A, ∑ b ∈ A, (c a : ℝ) * (c b : ℝ) * modelPhase ψ (apTerm Q x h a b)) - (JJ : ℝ) := by
        rw [hW, hJJ]
        push_cast
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [hsplit, hm₀]
      push_cast
      ring
    rw [e]
    have hcab : ∀ a ∈ A, ∀ b ∈ A, |(c a : ℝ) * (c b : ℝ) *
        ((t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)) -
          round (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)))| ≤
        (Λ : ℝ) * ε := by
      intro a ha b hb
      rw [abs_mul, abs_mul]
      have h1 := S.bound a
      have h2 := S.bound b
      have h3 : |(c a : ℝ)| * |(c b : ℝ)| ≤ 1 := by
        have := abs_nonneg (c a : ℝ)
        have := abs_nonneg (c b : ℝ)
        nlinarith
      have h4 := hterm a ha b hb
      have h5 : 0 ≤ dist01 (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)) :=
        dist01_nonneg _
      calc |(c a : ℝ)| * |(c b : ℝ)| *
            |t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b) -
              round (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b))|
          ≤ 1 * ((Λ : ℝ) * ε) := mul_le_mul h3 h4 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hcardA : ((A.card : ℕ) : ℝ) = (M : ℝ) + 1 := by
      rw [hA, Finset.card_range]
      push_cast
      ring
    calc _ ≤ ∑ a ∈ A, |∑ b ∈ A, (c a : ℝ) * (c b : ℝ) *
          ((t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)) -
            round (t * Real.log (apTerm Q x h a b) / (2 * π) - modelPhase ψ (apTerm Q x h a b)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ A, ((M : ℝ) + 1) * ((Λ : ℝ) * ε) := by
          refine Finset.sum_le_sum fun a ha => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc _ ≤ ∑ _b ∈ A, (Λ : ℝ) * ε := Finset.sum_le_sum fun b hb => hcab a ha b hb
            _ = _ := by
                rw [Finset.sum_const, nsmul_eq_mul, hcardA]
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardA]
          ring
  have hy1 : (i : ℝ) / (4 * K) ≤ y := hx1
  have hy2 : y ≤ ((i : ℝ) + 1) / (4 * K) := by
    have : y ≤ (i : ℝ) / (4 * K) + 1 / (4 * (K : ℝ)) := hx2
    rwa [← add_div] at this
  have hlt := hclose.trans_lt hε
  rcases le_total 0 t with ht | ht
  · -- `W = −y`, so `y` is near `−b₀`.
    have hyW : W = -y := by
      rw [hWeq, hy]
      unfold wordHeight
      rw [abs_of_nonneg ht]
      ring
    have hmem : -b₀ ∈ B' := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b₀, hb₀, rfl⟩)
    have hf := hfree (-b₀) hmem y hy1 hy2 (-(m₀ + JJ))
    have e : y - -b₀ - ((-(m₀ + JJ) : ℤ) : ℝ) = -(W - (b₀ + ((m₀ + JJ : ℤ) : ℝ))) := by
      rw [hyW]
      push_cast
      ring
    rw [e, abs_neg] at hf
    exact absurd hlt (not_lt.mpr hf)
  · have hyW : W = y := by
      rw [hWeq, hy]
      unfold wordHeight
      rw [abs_of_nonpos ht]
      ring
    have hmem : b₀ ∈ B' := Finset.mem_union_left _ hb₀
    have hf := hfree b₀ hmem y hy1 hy2 (m₀ + JJ)
    have e : y - b₀ - ((m₀ + JJ : ℤ) : ℝ) = W - (b₀ + ((m₀ + JJ : ℤ) : ℝ)) := by
      rw [hyW]
      ring
    rw [e] at hf
    exact absurd hlt (not_lt.mpr hf)

/-! ### Rank -/

/-- The integer coefficient of a generator in the model of a progression. -/
def rankCoeff {ι : Type*} (M : ℕ) (c : ℕ → ℤ) (e : ℕ → ι → ℤ) (Q x h : ℕ) (i : ι) : ℤ :=
  ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), c a * c b *
    ∑ p ∈ (apTerm Q x h a b).primeFactors, ((apTerm Q x h a b).factorization p : ℤ) * e p i

/-- The model of a progression is a lattice point of the generators. -/
theorem word_sum_model_rank {ι : Type*} [Fintype ι] (M : ℕ) (c : ℕ → ℤ) (φ : ι → ℝ) (e : ℕ → ι → ℤ)
    (Q x h : ℕ) :
    ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) *
        modelPhase (fun p => ∑ i, (e p i : ℝ) * φ i) (apTerm Q x h a b) =
      ∑ i, (rankCoeff M c e Q x h i : ℝ) * φ i := by
  have hab : ∀ a b, (c a : ℝ) * (c b : ℝ) *
      modelPhase (fun p => ∑ i, (e p i : ℝ) * φ i) (apTerm Q x h a b) =
      ∑ i, (c a : ℝ) * (c b : ℝ) * ((∑ p ∈ (apTerm Q x h a b).primeFactors,
        ((apTerm Q x h a b).factorization p : ℝ) * (e p i : ℝ)) * φ i) := by
    intro a b
    unfold modelPhase
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  have hR : ∀ i, (rankCoeff M c e Q x h i : ℝ) * φ i =
      ∑ a ∈ range (M + 1), ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) *
        ((∑ p ∈ (apTerm Q x h a b).primeFactors,
          ((apTerm Q x h a b).factorization p : ℝ) * (e p i : ℝ)) * φ i) := by
    intro i
    unfold rankCoeff
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hab a b,
    Finset.sum_congr rfl fun i _ => hR i]
  calc _ = ∑ a ∈ range (M + 1), ∑ i, ∑ b ∈ range (M + 1), (c a : ℝ) * (c b : ℝ) *
        ((∑ p ∈ (apTerm Q x h a b).primeFactors,
          ((apTerm Q x h a b).factorization p : ℝ) * (e p i : ℝ)) * φ i) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The bound on the coefficient of a generator. -/
theorem abs_rankCoeff_le {ι : Type*} {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ} (S : FineWord M k N₁ c t)
    {e : ℕ → ι → ℤ} {E Λ Q x h : ℕ} (hE : ∀ p i, |e p i| ≤ (E : ℤ)) (hx : x ≤ h + 4 * (M + 1) * h)
    (hΛ : 1 + Q * (h * (6 * M + 5)) < 2 ^ (Λ + 1)) (i : ι) :
    |rankCoeff M c e Q x h i| ≤ (((M + 1) ^ 2 * (Λ * E) : ℕ) : ℤ) := by
  have hc : ∀ a, |c a| ≤ 1 := fun a => by
    have := S.bound a
    exact_mod_cast this
  have hterm : ∀ a ∈ range (M + 1), ∀ b ∈ range (M + 1),
      |c a * c b * ∑ p ∈ (apTerm Q x h a b).primeFactors,
        ((apTerm Q x h a b).factorization p : ℤ) * e p i| ≤ ((Λ * E : ℕ) : ℤ) := by
    intro a ha b hb
    have ha' := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hb' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    set n := apTerm Q x h a b with hn
    have hn0 : n ≠ 0 := by
      rw [hn]
      unfold apTerm
      omega
    have hsum := sum_factorization_lt hn0 (lt_of_le_of_lt (apTerm_le hx ha' hb') hΛ)
    have h1 : |∑ p ∈ n.primeFactors, (n.factorization p : ℤ) * e p i| ≤ ((Λ * E : ℕ) : ℤ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h2 : ∀ p ∈ n.primeFactors, |(n.factorization p : ℤ) * e p i| ≤
          (n.factorization p : ℤ) * (E : ℤ) := by
        intro p _
        rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hE p i) (Int.natCast_nonneg _)
      refine (Finset.sum_le_sum h2).trans ?_
      rw [← Finset.sum_mul]
      push_cast
      refine mul_le_mul_of_nonneg_right ?_ (Int.natCast_nonneg _)
      exact_mod_cast hsum
    rw [abs_mul, abs_mul]
    have h3 : |c a| * |c b| ≤ 1 := by
      have := hc a
      have := hc b
      have := abs_nonneg (c a)
      have := abs_nonneg (c b)
      nlinarith
    calc |c a| * |c b| * |∑ p ∈ n.primeFactors, (n.factorization p : ℤ) * e p i|
        ≤ 1 * ((Λ * E : ℕ) : ℤ) := mul_le_mul h3 h1 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  unfold rankCoeff
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hin : ∀ a ∈ range (M + 1), |∑ b ∈ range (M + 1), c a * c b *
      ∑ p ∈ (apTerm Q x h a b).primeFactors, ((apTerm Q x h a b).factorization p : ℤ) * e p i| ≤
      ((M : ℤ) + 1) * ((Λ * E : ℕ) : ℤ) := by
    intro a ha
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (hterm a ha)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  refine (Finset.sum_le_sum hin).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **The rank theorem.** The prime phases do not lie near a progression of rank `d = |ι|` and width `E`: some prime escapes it, as soon as `K > 6 (2W + 1)^d`,
`W = (M + 1)² Λ E`. -/
theorem exists_prime_escape_rank {ι : Type*} [Fintype ι] [DecidableEq ι] {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ}
    (S : FineWord M k N₁ c t) {Q h : ℕ} (hQ : 1 ≤ Q) (hh : 1 ≤ h) (φ : ι → ℝ) (e : ℕ → ι → ℤ) {E K Λ : ℕ}
    (hE : ∀ p i, |e p i| ≤ (E : ℤ))
    (hK : 6 * (2 * ((M + 1) ^ 2 * (Λ * E)) + 1) ^ Fintype.card ι < K)
    (hstep : |t| / (2 * π) * (2 * ((M : ℝ) + 1) ^ 3) * (1 - 1 / (2 * (K : ℝ))) ^ (h * N₁) ≤ 1 / 4)
    (hΛ : 1 + Q * (h * (6 * M + 5)) < 2 ^ (Λ + 1)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ((M : ℝ) + 1) ^ 2 * ((Λ : ℝ) * ε) < 1 / (4 * (K : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ Q ∧ p ≤ 1 + Q * (h * (6 * M + 5)) ∧
      ε < dist01 (t * Real.log p / (2 * π) - ∑ i, (e p i : ℝ) * φ i) := by
  classical
  set W : ℕ := (M + 1) ^ 2 * (Λ * E) with hW
  set B : Finset ℝ := (Fintype.piFinset fun _ : ι => Finset.Icc (-(W : ℤ)) (W : ℤ)).image
    (fun j => ∑ i, (j i : ℝ) * φ i) with hB
  have hcard : B.card ≤ (2 * W + 1) ^ Fintype.card ι := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    congr 1
    omega
  refine exists_prime_escape S hQ hh (fun p => ∑ i, (e p i : ℝ) * φ i) B ?_ (by omega) hstep hΛ hε0 hε
  intro x hx
  refine ⟨∑ i, (rankCoeff M c e Q x h i : ℝ) * φ i, ?_, 0, ?_⟩
  · refine Finset.mem_image.mpr ⟨fun i => rankCoeff M c e Q x h i, ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro i
    have := abs_rankCoeff_le S hE hx hΛ i
    exact Finset.mem_Icc.mpr (abs_le.mp this)
  · rw [word_sum_model_rank]
    simp

/-! ### The word at height `t` -/

/-- The top condition, with its margin. -/
theorem HeightSize.top {L ℓ : ℝ} (h : HeightSize L ℓ) {M k : ℕ}
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hk : L ≤ (k : ℝ)) :
    Real.exp L * (2 * ((M : ℝ) + 1) ^ 2) ≤ π * 4 ^ k := by
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
  have hsq : ((M : ℝ) + 1) ^ 2 ≤ Real.exp (6 * ℓ) := by
    have h1 := pow_le_pow_left₀ (by positivity) hMle 2
    have e : Real.exp (3 * ℓ) ^ 2 = Real.exp (6 * ℓ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [e] at h1
  have hπ : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have e2 : (2 : ℝ) = Real.exp a := (Real.exp_log (by norm_num)).symm
  calc Real.exp L * (2 * ((M : ℝ) + 1) ^ 2) ≤ Real.exp L * (Real.exp a * Real.exp (6 * ℓ)) := by
        rw [← e2]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by norm_num)) (Real.exp_pos _).le
    _ = Real.exp (L + (a + 6 * ℓ)) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp ((k : ℝ) * (2 * a)) := by
        refine Real.exp_le_exp.mpr ?_
        have h3 : L * (2 * a) ≤ (k : ℝ) * (2 * a) := mul_le_mul_of_nonneg_right hk (by linarith)
        nlinarith
    _ = 4 ^ k := (four_pow_eq k).symm
    _ ≤ π * 4 ^ k := le_mul_of_one_le_left (by positivity) hπ

/-- The word of height one at height `exp L`, with room at both ends. -/
theorem HeightSize.exists_fineWord {L ℓ t : ℝ} (h : HeightSize L ℓ) (hexp : Real.exp L = |t|) {M k N₁ : ℕ}
    (hM1 : 6 * L ^ 2 * ℓ ≤ M) (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hk1 : L ≤ k) (hk2 : (k : ℝ) ≤ L + 1)
    (hN1 : (N₁ : ℝ) + 1 ≤ L / 2) (hN3 : 1 ≤ N₁) :
    ∃ c, FineWord M k N₁ c t := by
  obtain ⟨c, hc, hm, h0⟩ := exists_normalized_word (h.word hM1 hM2 hk2)
  refine ⟨c, ⟨fun a => ?_, hm, h0, hN3, ?_, ?_⟩⟩
  · exact_mod_cast hc.bound a
  · rw [← hexp]
    have := h.low (N := N₁ + 1) (by push_cast; linarith)
    have e : 4 * ((N₁ : ℝ) + 3) = 4 * (((N₁ + 1 : ℕ) : ℝ) + 2) := by
      push_cast
      ring
    rw [e]
    exact this
  · rw [← hexp]
    exact h.top hM2 hk1

/-- The step condition at `h = 8K`. -/
theorem HeightSize.step_fine {L ℓ t : ℝ} (h : HeightSize L ℓ) (hexp : Real.exp L = |t|) {M N₁ K : ℕ}
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hN : L / 2 - 2 ≤ (N₁ : ℝ)) (hK : 1 ≤ K) :
    |t| / (2 * π) * (2 * ((M : ℝ) + 1) ^ 3) * (1 - 1 / (2 * (K : ℝ))) ^ (8 * K * N₁) ≤ 1 / 4 := by
  have hL := h.hundred_le
  have h100 := h.log_le
  have hℓ := h.one_le
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hπ : (3 : ℝ) ≤ π := Real.pi_gt_three.le
  set x : ℝ := 1 / (2 * (K : ℝ)) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hpow : (1 - x) ^ (8 * K * N₁) ≤ Real.exp (-(4 * (N₁ : ℝ))) := by
    have h2 := pow_le_pow_left₀ (by linarith) h1 (8 * K * N₁)
    refine h2.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hx]
    push_cast
    field_simp
    ring
  have hMle : (M : ℝ) + 1 ≤ Real.exp (3 * ℓ) := by
    have e : Real.exp (3 * ℓ) = L ^ 3 := by
      have := Real.exp_nat_mul ℓ 3
      push_cast at this
      rw [this, h.exp_eq]
    rw [e]
    linarith [h.M_add_two_le hM2]
  have hcube : ((M : ℝ) + 1) ^ 3 ≤ Real.exp (9 * ℓ) := by
    have h3 := pow_le_pow_left₀ (by positivity) hMle 3
    have e : Real.exp (3 * ℓ) ^ 3 = Real.exp (9 * ℓ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [e] at h3
  rw [← hexp]
  have hπ0 : 0 < π := Real.pi_pos
  have e1 : Real.exp L / (2 * π) * (2 * ((M : ℝ) + 1) ^ 3) = Real.exp L * ((M : ℝ) + 1) ^ 3 / π := by
    field_simp
  rw [e1]
  have hexpo : Real.exp L * ((M : ℝ) + 1) ^ 3 * Real.exp (-(4 * (N₁ : ℝ))) ≤ Real.exp (-1) := by
    calc _ ≤ Real.exp L * Real.exp (9 * ℓ) * Real.exp (-(4 * (N₁ : ℝ))) := by
          gcongr
      _ = Real.exp (L + 9 * ℓ + -(4 * (N₁ : ℝ))) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-1) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
  have hbig : Real.exp (-1) ≤ 3 / 4 := by
    have h4 := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hnn : 0 ≤ Real.exp L * ((M : ℝ) + 1) ^ 3 / π := by positivity
  calc _ ≤ Real.exp L * ((M : ℝ) + 1) ^ 3 / π * Real.exp (-(4 * (N₁ : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow hnn
    _ = (Real.exp L * ((M : ℝ) + 1) ^ 3 * Real.exp (-(4 * (N₁ : ℝ)))) / π := by ring
    _ ≤ (3 / 4) / π := div_le_div_of_nonneg_right (hexpo.trans hbig) hπ0.le
    _ ≤ (3 / 4) / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ
    _ = 1 / 4 := by norm_num

/-- `1826 A L⁹ ≤ 2^A` when `A ≥ 100 log L`. -/
theorem le_two_pow_of_large {A : ℕ} {L ℓ : ℝ} (hexp : Real.exp ℓ = L) (hℓ : 1 ≤ ℓ) (hA : 100 * ℓ ≤ A) :
    1826 * (A : ℝ) * L ^ 9 ≤ 2 ^ A := by
  have ha1 := Real.log_two_gt_d9
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have h2 : (2 : ℝ) ^ A = Real.exp ((A : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h2]
  have h3 : (A : ℝ) ≤ 3 * Real.exp (0.345 * (A : ℝ)) := by
    have := Real.add_one_le_exp (0.345 * (A : ℝ))
    nlinarith
  have hL9 : L ^ 9 = Real.exp (9 * ℓ) := by
    rw [← hexp, ← Real.exp_nat_mul]
    norm_num
  have h9 : (5478 : ℝ) ≤ Real.exp 9 := by
    have h1 := Real.exp_one_gt_d9
    have h4 : (2.7 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) (by linarith) 9
    rw [← Real.exp_nat_mul] at h4
    norm_num at h4 ⊢
    linarith
  rw [hL9]
  calc 1826 * (A : ℝ) * Real.exp (9 * ℓ) ≤ 1826 * (3 * Real.exp (0.345 * (A : ℝ))) * Real.exp (9 * ℓ) := by
        gcongr
    _ = 5478 * Real.exp (0.345 * (A : ℝ)) * Real.exp (9 * ℓ) := by ring
    _ ≤ Real.exp 9 * Real.exp (0.345 * (A : ℝ)) * Real.exp (9 * ℓ) := by gcongr
    _ = Real.exp (9 + 0.345 * (A : ℝ) + 9 * ℓ) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp ((A : ℝ) * Real.log 2) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith

/-- The real bookkeeping behind `lt_two_pow`. -/
theorem size_algebra {x Q Z Λ A M2 : ℝ} {two : ℝ} (hx : 1 ≤ x) (hQ1 : 1 ≤ Q) (hQ : Q < 2 * Z) (hΛ1 : 1 ≤ Λ)
    (hΛZ : Λ ≤ 2 * A * Z) (hZ1 : 1 ≤ Z) (hM : M2 ≤ x) (hM1 : 1 ≤ M2)
    (hb : 1826 * A * x ^ 3 ≤ two) :
    1 + Q * (8 * (12 * (M2 ^ 2 * Λ) + 7) * (6 * (M2 - 1) + 5)) < 2 * two * Z ^ 2 := by
  have hx2 : 1 ≤ x ^ 2 * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) hΛ1
  have hW : M2 ^ 2 * Λ ≤ x ^ 2 * Λ := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    exact pow_le_pow_left₀ (by linarith) hM 2
  have hK : 12 * (M2 ^ 2 * Λ) + 7 ≤ 19 * (x ^ 2 * Λ) := by linarith
  have h6 : 6 * (M2 - 1) + 5 ≤ 6 * x := by linarith
  have h60 : 0 ≤ 6 * (M2 - 1) + 5 := by linarith
  have hprod : 8 * (12 * (M2 ^ 2 * Λ) + 7) * (6 * (M2 - 1) + 5) ≤ 912 * (x ^ 3 * Λ) := by
    have hnn : 0 ≤ 12 * (M2 ^ 2 * Λ) + 7 := by positivity
    calc _ ≤ 8 * (19 * (x ^ 2 * Λ)) * (6 * x) := by
          gcongr
      _ = _ := by ring
  have hx3 : 1 ≤ x ^ 3 * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx) hΛ1
  have h1 : 1 + Q * (8 * (12 * (M2 ^ 2 * Λ) + 7) * (6 * (M2 - 1) + 5)) ≤ Q * (913 * (x ^ 3 * Λ)) := by
    have := mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ Q)
    nlinarith
  have hpos : 0 < 913 * (x ^ 3 * Λ) := by positivity
  have h2 : Q * (913 * (x ^ 3 * Λ)) < 2 * Z * (913 * (x ^ 3 * Λ)) := mul_lt_mul_of_pos_right hQ hpos
  have h3 : 2 * Z * (913 * (x ^ 3 * Λ)) ≤ 2 * Z * (913 * (x ^ 3 * (2 * A * Z))) := by
    gcongr
  have h4 : 2 * Z * (913 * (x ^ 3 * (2 * A * Z))) = 2 * (1826 * A * x ^ 3) * Z ^ 2 := by ring
  have h5 : 2 * (1826 * A * x ^ 3) * Z ^ 2 ≤ 2 * two * Z ^ 2 := by
    gcongr
  linarith

/-- The size of the progression, against the number of prime factors allowed. -/
theorem HeightSize.lt_two_pow {L ℓ : ℝ} (h : HeightSize L ℓ) {M Q A : ℕ}
    (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hQ : 1 ≤ Q) (hA : 100 * ℓ ≤ A) :
    1 + Q * (8 * (12 * ((M + 1) ^ 2 * (A + 2 * Nat.log 2 Q)) + 7) * (6 * M + 5)) <
      2 ^ (A + 2 * Nat.log 2 Q + 1) := by
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hexp := h.exp_eq
  obtain ⟨z, hz⟩ : ∃ z, z = Nat.log 2 Q := ⟨_, rfl⟩
  rw [← hz]
  have hA1 : (100 : ℝ) ≤ A := by nlinarith
  have hQlt : (Q : ℝ) < 2 * (2 : ℝ) ^ z := by
    have h1 : Q < 2 ^ (z + 1) := by
      rw [hz]
      exact Nat.lt_pow_succ_log_self (by norm_num) Q
    have h2 : (Q : ℝ) < (2 : ℝ) ^ (z + 1) := by exact_mod_cast h1
    rw [pow_succ] at h2
    linarith
  have hZ1 : (1 : ℝ) ≤ (2 : ℝ) ^ z := one_le_pow₀ (by norm_num)
  have hzle : (z : ℝ) + 1 ≤ (2 : ℝ) ^ z := by
    have h2 : z + 1 ≤ 2 ^ z := Nat.lt_two_pow_self
    exact_mod_cast h2
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hΛ1 : (1 : ℝ) ≤ (A : ℝ) + 2 * z := by linarith
  have hΛZ : (A : ℝ) + 2 * z ≤ 2 * (A : ℝ) * (2 : ℝ) ^ z := by nlinarith
  have hML : (M : ℝ) + 1 ≤ L ^ 3 := by linarith [h.M_add_two_le hM2]
  have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hb := le_two_pow_of_large hexp hℓ hA
  have hb' : 1826 * (A : ℝ) * (L ^ 3) ^ 3 ≤ (2 : ℝ) ^ A := by
    have e : (L ^ 3) ^ 3 = L ^ 9 := by ring
    rw [e]
    exact hb
  have hreal := size_algebra (one_le_pow₀ (by linarith : (1 : ℝ) ≤ L)) (by exact_mod_cast hQ) hQlt hΛ1 hΛZ
    hZ1 hML hM1 hb'
  have htwo : (2 : ℝ) ^ (A + 2 * z + 1) = 2 * (2 : ℝ) ^ A * ((2 : ℝ) ^ z) ^ 2 := by
    rw [pow_succ, pow_add, pow_mul' (2 : ℝ)]
    ring
  rw [← htwo] at hreal
  have hcast : ((1 + Q * (8 * (12 * ((M + 1) ^ 2 * (A + 2 * z)) + 7) * (6 * M + 5)) : ℕ) : ℝ) <
      ((2 ^ (A + 2 * z + 1) : ℕ) : ℝ) := by
    push_cast
    have e : (M : ℝ) + 1 - 1 = M := by ring
    rw [e] at hreal
    exact hreal
  exact_mod_cast hcast

/-- The escape at fixed parameters, from a rotation. -/
theorem HeightSize.escape {L ℓ t : ℝ} (h : HeightSize L ℓ) (hexp : Real.exp L = |t|) {M k N₁ Q A : ℕ}
    (hM1 : 6 * L ^ 2 * ℓ ≤ M) (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1) (hk1 : L ≤ k) (hk2 : (k : ℝ) ≤ L + 1)
    (hN1 : (N₁ : ℝ) + 1 ≤ L / 2) (hN2 : L / 2 - 2 ≤ (N₁ : ℝ)) (hN3 : 1 ≤ N₁) (hQ : 1 ≤ Q)
    (hA : 100 * ℓ ≤ A) (hΛ1 : 1 ≤ A + 2 * Nat.log 2 Q) (φ : ℝ) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ Q ∧
      p ≤ 1 + Q * (8 * (12 * ((M + 1) ^ 2 * (A + 2 * Nat.log 2 Q)) + 7) * (6 * M + 5)) ∧
      1 / (8 * ((12 * (((M : ℝ) + 1) ^ 2 * ((A + 2 * Nat.log 2 Q : ℕ) : ℝ)) + 7) *
          (((M : ℝ) + 1) ^ 2 * ((A + 2 * Nat.log 2 Q : ℕ) : ℝ)))) <
        dist01 (t * Real.log p / (2 * π) - φ) := by
  obtain ⟨c, S⟩ := h.exists_fineWord hexp hM1 hM2 hk1 hk2 hN1 hN3
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = A + 2 * Nat.log 2 Q := ⟨_, rfl⟩
  have hsizeN := h.lt_two_pow hM2 hQ hA
  rw [← hΛ] at hsizeN hΛ1 ⊢
  obtain ⟨K, hK⟩ : ∃ K, K = 12 * ((M + 1) ^ 2 * Λ) + 7 := ⟨_, rfl⟩
  have hsize' : 1 + Q * ((8 * K) * (6 * M + 5)) < 2 ^ (Λ + 1) := by
    rw [hK]
    exact hsizeN
  have hstep := h.step_fine hexp hM2 hN2 (K := K) (by omega)
  have hKr : ((K : ℕ) : ℝ) = 12 * (((M : ℝ) + 1) ^ 2 * (Λ : ℝ)) + 7 := by
    rw [hK]
    push_cast
    ring
  have hK0 : (0 : ℝ) < K := by
    rw [hKr]
    positivity
  have hΛr : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ1
  have hMr : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hprodpos : 0 < ((M : ℝ) + 1) ^ 2 * (Λ : ℝ) := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (8 * ((K : ℝ) * (((M : ℝ) + 1) ^ 2 * (Λ : ℝ)))) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]
    positivity
  have hεeq : ((M : ℝ) + 1) ^ 2 * ((Λ : ℝ) * ε) = 1 / (8 * (K : ℝ)) := by
    rw [hε]
    field_simp
  obtain ⟨p, hp, hpQ, hple, hpε⟩ := exists_prime_escape_rank (ι := Unit) S hQ (h := 8 * K) (by omega)
    (fun _ => φ) (fun _ _ => 1) (E := 1) (K := K) (Λ := Λ) (fun _ _ => by simp) (by
      rw [Fintype.card_unit, hK, pow_one, mul_one]
      omega) hstep hsize' hεpos.le (by
      rw [hεeq]
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith))
  refine ⟨p, hp, hpQ, ?_, ?_⟩
  · rw [← hK]
    exact hple
  · have hsimp : (∑ i : Unit, (((fun _ _ => (1 : ℤ)) : ℕ → Unit → ℤ) p i : ℝ) * (fun _ : Unit => φ) i) = φ := by
      simp
    rw [hsimp, hε, hKr] at hpε
    exact hpε

/-- The real bound on the size of the escaping prime. -/
theorem prime_size_algebra {p Q M2 Λ L ℓ : ℝ} (hQ : 1 ≤ Q) (hM2 : 1 ≤ M2) (hΛ : 1 ≤ Λ)
    (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) (hMl : M2 ≤ 8 * (L ^ 2 * ℓ))
    (hp : p ≤ 1 + Q * (8 * (12 * (M2 ^ 2 * Λ) + 7) * (6 * (M2 - 1) + 5))) :
    p ≤ Q * (10 ^ 6 * L ^ 6 * ℓ ^ 3 * Λ) := by
  have hW : 1 ≤ M2 ^ 2 * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM2) hΛ
  have hK : 12 * (M2 ^ 2 * Λ) + 7 ≤ 19 * (M2 ^ 2 * Λ) := by linarith
  have h6 : 6 * (M2 - 1) + 5 ≤ 6 * M2 := by linarith
  have h60 : 0 ≤ 6 * (M2 - 1) + 5 := by linarith
  have h1 : 8 * (12 * (M2 ^ 2 * Λ) + 7) * (6 * (M2 - 1) + 5) ≤ 912 * (M2 ^ 3 * Λ) := by
    have hnn : 0 ≤ 12 * (M2 ^ 2 * Λ) + 7 := by positivity
    calc _ ≤ 8 * (19 * (M2 ^ 2 * Λ)) * (6 * M2) := by
          gcongr
      _ = _ := by ring
  have h2 : M2 ^ 3 ≤ 512 * (L ^ 6 * ℓ ^ 3) := by
    calc M2 ^ 3 ≤ (8 * (L ^ 2 * ℓ)) ^ 3 := pow_le_pow_left₀ (by linarith) hMl 3
      _ = _ := by ring
  have h3 : 912 * (M2 ^ 3 * Λ) ≤ 466944 * (L ^ 6 * ℓ ^ 3 * Λ) := by
    have := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ Λ)
    linarith
  have hbig : 1 ≤ L ^ 6 * ℓ ^ 3 * Λ :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) (one_le_pow₀ hℓ)) hΛ
  have h7 : Q * (8 * (12 * (M2 ^ 2 * Λ) + 7) * (6 * (M2 - 1) + 5)) ≤ Q * (466944 * (L ^ 6 * ℓ ^ 3 * Λ)) :=
    mul_le_mul_of_nonneg_left (h1.trans h3) (by linarith)
  have h8 : 1 ≤ Q * (L ^ 6 * ℓ ^ 3 * Λ) := one_le_mul_of_one_le_of_one_le hQ hbig
  have e : Q * (10 ^ 6 * L ^ 6 * ℓ ^ 3 * Λ) = 10 ^ 6 * (Q * (L ^ 6 * ℓ ^ 3 * Λ)) := by ring
  have e2 : Q * (466944 * (L ^ 6 * ℓ ^ 3 * Λ)) = 466944 * (Q * (L ^ 6 * ℓ ^ 3 * Λ)) := by ring
  rw [e]
  rw [e2] at h7
  linarith

/-- The real bound on the precision of the escape. -/
theorem precision_algebra {M2 Λ L ℓ : ℝ} (hM2 : 1 ≤ M2) (hΛ : 1 ≤ Λ) (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ)
    (hMl : M2 ≤ 8 * (L ^ 2 * ℓ)) :
    8 * ((12 * (M2 ^ 2 * Λ) + 7) * (M2 ^ 2 * Λ)) ≤ 10 ^ 6 * L ^ 8 * ℓ ^ 4 * Λ ^ 2 := by
  have hW : 1 ≤ M2 ^ 2 * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM2) hΛ
  have hK : 12 * (M2 ^ 2 * Λ) + 7 ≤ 19 * (M2 ^ 2 * Λ) := by linarith
  have h4 : M2 ^ 4 ≤ 4096 * (L ^ 8 * ℓ ^ 4) := by
    calc M2 ^ 4 ≤ (8 * (L ^ 2 * ℓ)) ^ 4 := pow_le_pow_left₀ (by linarith) hMl 4
      _ = _ := by ring
  have hΛ2 : 0 ≤ Λ ^ 2 := sq_nonneg _
  have h1 : 8 * ((12 * (M2 ^ 2 * Λ) + 7) * (M2 ^ 2 * Λ)) ≤ 152 * (M2 ^ 4 * Λ ^ 2) := by
    calc _ ≤ 8 * (19 * (M2 ^ 2 * Λ) * (M2 ^ 2 * Λ)) := by
          gcongr
      _ = _ := by ring
  have h2 := mul_le_mul_of_nonneg_right h4 hΛ2
  have hnn : 0 ≤ L ^ 8 * ℓ ^ 4 * Λ ^ 2 := by positivity
  have e : (10 : ℝ) ^ 6 * L ^ 8 * ℓ ^ 4 * Λ ^ 2 = 10 ^ 6 * (L ^ 8 * ℓ ^ 4 * Λ ^ 2) := by ring
  have e2 : 4096 * (L ^ 8 * ℓ ^ 4) * Λ ^ 2 = 4096 * (L ^ 8 * ℓ ^ 4 * Λ ^ 2) := by ring
  rw [e]
  rw [e2] at h2
  linarith

/-- **The orbit escapes every rotation, away from any modulus.** With `L = log |t|`, `ℓ = log L` and `Λ = ⌈100 ℓ⌉ + 2 log₂ Q`: for every `Q ≥ 1` and every `φ`, some
prime `p ∤ Q`, `p ≤ 10⁶ Q L⁶ ℓ³ Λ`, has `t log p/2π` at distance more than `1/(10⁶ L⁸ ℓ⁴ Λ²)` from `φ + ℤ`. -/
theorem exists_prime_not_near_rotation :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ Q : ℕ, 1 ≤ Q → ∀ φ : ℝ,
      ∃ p : ℕ, p.Prime ∧ ¬ p ∣ Q ∧
        (p : ℝ) ≤ Q * (10 ^ 6 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 3 *
          ((⌈100 * Real.log (Real.log |t|)⌉₊ + 2 * Nat.log 2 Q : ℕ) : ℝ)) ∧
        1 / (10 ^ 6 * Real.log |t| ^ 8 * Real.log (Real.log |t|) ^ 4 *
          ((⌈100 * Real.log (Real.log |t|)⌉₊ + 2 * Nat.log 2 Q : ℕ) : ℝ) ^ 2) <
          dist01 (t * Real.log p / (2 * π) - φ) := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht Q hQ φ => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp ⊢
  generalize Real.log L = ℓ at h ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hM1 : 6 * L ^ 2 * ℓ ≤ (⌈6 * L ^ 2 * ℓ⌉₊ : ℝ) := Nat.le_ceil _
  have hM2 : ((⌈6 * L ^ 2 * ℓ⌉₊ : ℕ) : ℝ) ≤ 6 * L ^ 2 * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil _
  have hk2 : ((⌈L⌉₊ : ℕ) : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hfl1 : ((⌊L / 2⌋₊ : ℕ) : ℝ) ≤ L / 2 := Nat.floor_le (by linarith)
  have hfl2 := Nat.lt_floor_add_one (L / 2)
  have hfl3 : 2 ≤ ⌊L / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hN₁r : ((⌊L / 2⌋₊ - 1 : ℕ) : ℝ) = ((⌊L / 2⌋₊ : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hA : 100 * ℓ ≤ (⌈100 * ℓ⌉₊ : ℝ) := Nat.le_ceil _
  have hA1 : 1 ≤ ⌈100 * ℓ⌉₊ := by
    have : (1 : ℝ) ≤ (⌈100 * ℓ⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨p, hp, hpQ, hple, hpε⟩ := h.escape hexp hM1 hM2 hk1 hk2 (N₁ := ⌊L / 2⌋₊ - 1) (by linarith)
    (by linarith) (by omega) hQ hA (by omega) φ
  generalize ⌈6 * L ^ 2 * ℓ⌉₊ = M at hM1 hM2 hple hpε
  generalize hΛ : ⌈100 * ℓ⌉₊ + 2 * Nat.log 2 Q = Λ at hple hpε ⊢
  have hΛr : (1 : ℝ) ≤ Λ := by
    have : 1 ≤ Λ := by omega
    exact_mod_cast this
  have hMr : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have h100 := h.log_le
  have hMl : (M : ℝ) + 1 ≤ 8 * (L ^ 2 * ℓ) := by
    have : (1 : ℝ) ≤ L ^ 2 * ℓ := by nlinarith
    nlinarith
  have hLr : (1 : ℝ) ≤ L := by linarith
  refine ⟨p, hp, hpQ, ?_, ?_⟩
  · refine prime_size_algebra (M2 := (M : ℝ) + 1) (by exact_mod_cast hQ) hMr hΛr hLr hℓ hMl ?_
    have h1 : ((p : ℕ) : ℝ) ≤ ((1 + Q * (8 * (12 * ((M + 1) ^ 2 * Λ) + 7) * (6 * M + 5)) : ℕ) : ℝ) := by
      exact_mod_cast hple
    push_cast at h1
    have e : (M : ℝ) + 1 - 1 = M := by ring
    rw [e]
    exact h1
  · refine lt_of_le_of_lt ?_ hpε
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact precision_algebra hMr hΛr hLr hℓ hMl

/-- The window bound `Σ (1/√p)(1 − cos(t log p − 2πφ)) ≥ 8ε²/√p₀` at an escaping prime. -/
theorem le_sum_one_sub_cos {G : Finset ℕ} {t φ ε : ℝ} {p₀ : ℕ} (hp₀ : p₀ ∈ G)
    (hε0 : 0 ≤ ε) (hp : ε < dist01 (t * Real.log p₀ / (2 * π) - φ)) :
    8 * ε ^ 2 / √(p₀ : ℝ) ≤
      ∑ p ∈ G, (1 - Real.cos (t * Real.log p - 2 * π * φ)) / √(p : ℝ) := by
  have hπ := Real.pi_pos
  have hterm : ∀ p ∈ G, 0 ≤ (1 - Real.cos (t * Real.log p - 2 * π * φ)) / √(p : ℝ) := fun p _ =>
    div_nonneg (by linarith [Real.cos_le_one (t * Real.log p - 2 * π * φ)]) (Real.sqrt_nonneg _)
  refine le_trans ?_ (Finset.single_le_sum hterm hp₀)
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  have h1 := eight_mul_sq_le_one_sub_cos (t * Real.log p₀ / (2 * π) - φ)
  have e : 2 * π * (t * Real.log p₀ / (2 * π) - φ) = t * Real.log p₀ - 2 * π * φ := by
    field_simp
  rw [e] at h1
  have h2 : ε ^ 2 ≤ dist01 (t * Real.log p₀ / (2 * π) - φ) ^ 2 := pow_le_pow_left₀ hε0 hp.le 2
  linarith

/-- The norm of a positive combination of phases, read at its argument. -/
theorem sum_sub_norm_eq (G : Finset ℕ) (t : ℝ) :
    ∃ φ : ℝ, (∑ p ∈ G, 1 / √(p : ℝ)) - ‖∑ p ∈ G, ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p))‖ =
      ∑ p ∈ G, (1 - Real.cos (t * Real.log p - 2 * π * φ)) / √(p : ℝ) := by
  set P : ℂ := ∑ p ∈ G, ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p)) with hP
  refine ⟨Complex.arg P / (2 * π), ?_⟩
  have hπ := Real.pi_pos
  have e0 : ∀ p : ℕ, 2 * π * (Complex.arg P / (2 * π)) = Complex.arg P := fun _ => by
    field_simp
  rw [e0 0]
  -- `‖P‖ = Re(e^{−i arg P} P)`.
  have hnorm : (‖P‖ : ℝ) = (Complex.exp (-(Complex.arg P : ℂ) * Complex.I) * P).re := by
    have h1 := Complex.norm_mul_exp_arg_mul_I P
    have h2 : Complex.exp (-(Complex.arg P : ℂ) * Complex.I) * P = (‖P‖ : ℂ) := by
      nth_rewrite 2 [← h1]
      rw [mul_comm (‖P‖ : ℂ), ← mul_assoc, ← Complex.exp_add]
      simp
    rw [h2, Complex.ofReal_re]
  have hsum : (Complex.exp (-(Complex.arg P : ℂ) * Complex.I) * P).re =
      ∑ p ∈ G, (1 / √(p : ℝ)) * Real.cos (t * Real.log p - Complex.arg P) := by
    rw [hP, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : Complex.exp (-(Complex.arg (∑ p ∈ G, ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p))) : ℂ) * Complex.I) *
        (((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p))) =
        ((1 / √(p : ℝ) : ℝ) : ℂ) *
          Complex.exp (((t * Real.log p - Complex.arg (∑ p ∈ G, ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p))) : ℝ) : ℂ) * Complex.I) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hnorm, hsum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- The real bookkeeping of the modulus saving. -/
theorem modulus_algebra {L ℓ Λ s : ℝ} (hL : 1 ≤ L) (hℓ : 1 ≤ ℓ) (hΛ1 : 1 ≤ Λ) (hΛ : Λ ≤ 101 * ℓ) (hs0 : 0 < s)
    (hs : s ≤ 10 ^ 4 * 2 * (L ^ 3 * ℓ ^ 2)) :
    1 / (10 ^ 25 * L ^ 19 * ℓ ^ 14) ≤ 8 * (1 / (10 ^ 6 * L ^ 8 * ℓ ^ 4 * Λ ^ 2)) ^ 2 / s := by
  have hLp : 0 < L := by linarith
  have hℓp : 0 < ℓ := by linarith
  have hΛp : 0 < Λ := by linarith
  have e : 8 * (1 / (10 ^ 6 * L ^ 8 * ℓ ^ 4 * Λ ^ 2)) ^ 2 / s =
      8 / (10 ^ 12 * L ^ 16 * ℓ ^ 8 * Λ ^ 4 * s) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have hΛ4 : Λ ^ 4 ≤ (101 * ℓ) ^ 4 := pow_le_pow_left₀ hΛp.le hΛ 4
  have e4 : (101 * ℓ) ^ 4 = 104060401 * ℓ ^ 4 := by ring
  rw [e4] at hΛ4
  have hprod : 10 ^ 12 * L ^ 16 * ℓ ^ 8 * Λ ^ 4 * s ≤
      10 ^ 12 * L ^ 16 * ℓ ^ 8 * (104060401 * ℓ ^ 4) * (10 ^ 4 * 2 * (L ^ 3 * ℓ ^ 2)) := by
    gcongr
  have e5 : (10 : ℝ) ^ 12 * L ^ 16 * ℓ ^ 8 * (104060401 * ℓ ^ 4) * (10 ^ 4 * 2 * (L ^ 3 * ℓ ^ 2)) =
      (10 ^ 12 * 104060401 * (10 ^ 4 * 2)) * (L ^ 19 * ℓ ^ 14) := by ring
  rw [e5] at hprod
  have hnn : 0 < L ^ 19 * ℓ ^ 14 := by positivity
  have e6 : 8 * (10 ^ 25 * L ^ 19 * ℓ ^ 14) = (8 * 10 ^ 25) * (L ^ 19 * ℓ ^ 14) := by ring
  rw [e6, one_mul]
  have hconst : ((10 : ℝ) ^ 12 * 104060401 * (10 ^ 4 * 2)) * (L ^ 19 * ℓ ^ 14) ≤ (8 * 10 ^ 25) * (L ^ 19 * ℓ ^ 14) :=
    mul_le_mul_of_nonneg_right (by norm_num) hnn.le
  linarith

/-- **The modulus stays below its size.** With `L = log |t|`, `ℓ = log L`, for every `N` past `10⁹ L⁶ ℓ⁴`, against every rotation,
`|Σ_{p<N} p^{−½ + it}| ≤ Σ_{p<N} p^{−½} − 1/(10²⁵ L¹⁹ ℓ¹⁴)`. -/
theorem norm_sum_primes_le :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
      10 ^ 9 * Real.log |t| ^ 6 * Real.log (Real.log |t|) ^ 4 < N →
      ‖∑ p ∈ N.primesBelow, ((1 / √(p : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (t * Real.log p))‖ ≤
        (∑ p ∈ N.primesBelow, 1 / √(p : ℝ)) -
          1 / (10 ^ 25 * Real.log |t| ^ 19 * Real.log (Real.log |t|) ^ 14) := by
  obtain ⟨T₀, hT₀, hrot⟩ := exists_prime_not_near_rotation
  obtain ⟨T₁, hT₁, hsize⟩ := eventually_heightSize
  refine ⟨max T₀ T₁, lt_of_lt_of_le hT₀ (le_max_left _ _), fun t ht N hN => ?_⟩
  have h := hsize t ((le_max_right _ _).trans ht)
  obtain ⟨φ, hφ⟩ := sum_sub_norm_eq N.primesBelow t
  obtain ⟨p, hp, -, hple, hpε⟩ := hrot t ((le_max_left _ _).trans ht) 1 le_rfl φ
  have hlog1 : Nat.log 2 1 = 0 := by simp
  rw [hlog1] at hple hpε
  simp only [mul_zero, add_zero, Nat.cast_one, one_mul] at hple hpε
  generalize Real.log |t| = L at h hN hple hpε ⊢
  generalize Real.log L = ℓ at h hN hple hpε ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hA1 : 100 * ℓ ≤ (⌈100 * ℓ⌉₊ : ℝ) := Nat.le_ceil _
  have hA2 : ((⌈100 * ℓ⌉₊ : ℕ) : ℝ) ≤ 101 * ℓ := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 100 * ℓ)
    linarith
  generalize ((⌈100 * ℓ⌉₊ : ℕ) : ℝ) = Λ at hA1 hA2 hple hpε
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hLr : (1 : ℝ) ≤ L := by linarith
  have hpR : (p : ℝ) ≤ 10 ^ 6 * L ^ 6 * ℓ ^ 3 * (101 * ℓ) := by
    refine hple.trans ?_
    gcongr
  have hpN : (p : ℝ) < N := by
    refine lt_of_le_of_lt hpR (lt_of_le_of_lt ?_ hN)
    have e : (10 : ℝ) ^ 6 * L ^ 6 * ℓ ^ 3 * (101 * ℓ) = 101 * 10 ^ 6 * (L ^ 6 * ℓ ^ 4) := by ring
    have e2 : (10 : ℝ) ^ 9 * L ^ 6 * ℓ ^ 4 = 10 ^ 9 * (L ^ 6 * ℓ ^ 4) := by ring
    rw [e, e2]
    have hnn : 0 ≤ L ^ 6 * ℓ ^ 4 := by positivity
    nlinarith
  have hmem : p ∈ N.primesBelow := Nat.mem_primesBelow.mpr ⟨by exact_mod_cast hpN, hp⟩
  set ε : ℝ := 1 / (10 ^ 6 * L ^ 8 * ℓ ^ 4 * Λ ^ 2) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hsum := le_sum_one_sub_cos hmem hε0 hpε
  have hspos : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hsle : √(p : ℝ) ≤ 10 ^ 4 * 2 * (L ^ 3 * ℓ ^ 2) := by
    rw [Real.sqrt_le_left (by positivity)]
    refine hpR.trans ?_
    have e : (10 : ℝ) ^ 6 * L ^ 6 * ℓ ^ 3 * (101 * ℓ) = 101 * 10 ^ 6 * (L ^ 6 * ℓ ^ 4) := by ring
    have e2 : ((10 : ℝ) ^ 4 * 2 * (L ^ 3 * ℓ ^ 2)) ^ 2 = 4 * 10 ^ 8 * (L ^ 6 * ℓ ^ 4) := by ring
    rw [e, e2]
    have hnn : 0 ≤ L ^ 6 * ℓ ^ 4 := by positivity
    nlinarith
  have hfin := modulus_algebra hLr hℓ hΛ1 hA2 hspos hsle
  rw [← hε] at hfin
  linarith

/-! ### The number of misaligned primes -/

/-- **Escape from a finite set.** The primes of `Ex` may be misaligned in any way: as generators they cost only their number, not their size. Some prime outside `Ex` is
still misaligned. -/
theorem exists_prime_not_mem {M k N₁ : ℕ} {c : ℕ → ℤ} {t : ℝ} (S : FineWord M k N₁ c t) {h : ℕ}
    (hh : 1 ≤ h) (Ex : Finset ℕ) {K Λ : ℕ}
    (hK : 6 * (2 * ((M + 1) ^ 2 * (Λ * 1)) + 1) ^ Ex.card < K)
    (hstep : |t| / (2 * π) * (2 * ((M : ℝ) + 1) ^ 3) * (1 - 1 / (2 * (K : ℝ))) ^ (h * N₁) ≤ 1 / 4)
    (hΛ : 1 + 1 * (h * (6 * M + 5)) < 2 ^ (Λ + 1)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ((M : ℝ) + 1) ^ 2 * ((Λ : ℝ) * ε) < 1 / (4 * (K : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ p ∉ Ex ∧ p ≤ 1 + 1 * (h * (6 * M + 5)) ∧ ε < phaseDist t p := by
  classical
  have hcard : Fintype.card Ex = Ex.card := Fintype.card_coe Ex
  obtain ⟨p, hp, -, hple, hpε⟩ := exists_prime_escape_rank (ι := Ex) S (Q := 1) le_rfl hh
    (fun i => t * Real.log ((i : ℕ) : ℝ) / (2 * π)) (fun p i => if p = (i : ℕ) then 1 else 0) (E := 1)
    (K := K) (Λ := Λ) (fun p i => by
      split_ifs <;> simp) (by rw [hcard]; exact hK) hstep hΛ hε0 hε
  have hmodel : ∀ q : ℕ, (∑ i : Ex, (((if q = (i : ℕ) then 1 else 0 : ℤ)) : ℝ) *
      (t * Real.log ((i : ℕ) : ℝ) / (2 * π))) =
      if q ∈ Ex then t * Real.log (q : ℝ) / (2 * π) else 0 := by
    intro q
    split_ifs with hq
    · rw [Finset.sum_eq_single (⟨q, hq⟩ : Ex)]
      · simp
      · intro b _ hb
        have : q ≠ (b : ℕ) := fun h => hb (Subtype.ext h.symm)
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : q ≠ (i : ℕ) := fun h => hq (h ▸ i.2)
      simp [this]
  rw [hmodel p] at hpε
  by_cases hmem : p ∈ Ex
  · rw [if_pos hmem, sub_self] at hpε
    have : dist01 0 = 0 := by simp [dist01]
    rw [this] at hpε
    exact absurd hpε (not_lt.mpr hε0)
  · rw [if_neg hmem, sub_zero] at hpε
    exact ⟨p, hp, hmem, hple, hpε⟩

/-- The size of the progression for the count of misaligned primes. -/
theorem misaligned_size {L X K M1 : ℝ} (hL : 100 ≤ L) (hX : 1 ≤ X) (hK : K ≤ 7 * X)
    (hM : M1 ≤ L ^ 3) (hM1 : 1 ≤ M1) : 1 + 8 * K * (6 * (M1 - 1) + 5) ≤ X * L ^ 6 := by
  have hL3 : (10 : ℝ) ^ 6 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at this ⊢
    linarith
  have h1 : 8 * K * (6 * (M1 - 1) + 5) ≤ 8 * (7 * X) * (6 * L ^ 3) := by
    have h2 : 6 * (M1 - 1) + 5 ≤ 6 * L ^ 3 := by linarith
    have h3 : 0 ≤ 6 * (M1 - 1) + 5 := by linarith
    gcongr
  have h4 : X * L ^ 3 * L ^ 3 = X * L ^ 6 := by ring
  have h5 : 0 < X * L ^ 3 := by positivity
  have h6 : 1 ≤ X * L ^ 3 := by nlinarith
  have h7 : 337 * (X * L ^ 3) ≤ (X * L ^ 3) * L ^ 3 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) h5.le
  nlinarith

/-- The precision for the count of misaligned primes. -/
theorem misaligned_prec {L X K M1 Λ : ℝ} (hL : 100 ≤ L) (hX : 1 ≤ X) (hK : K ≤ 7 * X) (hK1 : 1 ≤ K)
    (hM : M1 ≤ L ^ 3) (hM1 : 1 ≤ M1) (hΛ1 : 1 ≤ Λ) (hΛ : Λ ≤ 2 * L ^ 2) :
    M1 ^ 2 * (Λ * (1 / (X * L ^ 10))) < 1 / (4 * K) := by
  have hLp : 0 < L := by linarith
  have e : M1 ^ 2 * (Λ * (1 / (X * L ^ 10))) = M1 ^ 2 * Λ / (X * L ^ 10) := by ring
  rw [e, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  have hM2 : M1 ^ 2 ≤ (L ^ 3) ^ 2 := pow_le_pow_left₀ (by linarith) hM 2
  have h1 : M1 ^ 2 * Λ ≤ (L ^ 3) ^ 2 * (2 * L ^ 2) :=
    mul_le_mul hM2 hΛ (by linarith) (by positivity)
  have h2 : M1 ^ 2 * Λ * (4 * K) ≤ (L ^ 3) ^ 2 * (2 * L ^ 2) * (4 * (7 * X)) :=
    mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  have e2 : (L ^ 3) ^ 2 * (2 * L ^ 2) * (4 * (7 * X)) = 56 * (X * L ^ 8) := by ring
  have e3 : X * L ^ 10 = (X * L ^ 8) * L ^ 2 := by ring
  rw [e2] at h2
  rw [e3]
  have h3 : 0 < X * L ^ 8 := by positivity
  have h4 : (57 : ℝ) ≤ L ^ 2 := by nlinarith
  nlinarith

/-- `N < 2^{Λ+1}` once `Λ ≥ 100 ℓ (d + 1)`. -/
theorem lt_two_pow_of_exp {L ℓ N : ℝ} {d Λ : ℕ} (hexp : Real.exp ℓ = L) (hℓ : 1 ≤ ℓ)
    (hN : N ≤ L ^ (9 * d) * L ^ 6) (hΛ : 100 * ℓ * ((d : ℝ) + 1) ≤ Λ) : N < 2 ^ (Λ + 1) := by
  have ha := Real.log_two_gt_d9
  have h2 : (2 : ℝ) ^ Λ = Real.exp ((Λ : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hL : L ^ (9 * d) * L ^ 6 = Real.exp (((9 * d + 6 : ℕ) : ℝ) * ℓ) := by
    rw [← pow_add, ← hexp, ← Real.exp_nat_mul]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hle : L ^ (9 * d) * L ^ 6 ≤ (2 : ℝ) ^ Λ := by
    rw [hL, h2]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    have h3 : (9 * (d : ℝ) + 6) * ℓ ≤ 100 * ℓ * ((d : ℝ) + 1) * 0.69 := by nlinarith
    have h4 : 100 * ℓ * ((d : ℝ) + 1) * 0.69 ≤ (Λ : ℝ) * 0.69 := by
      exact mul_le_mul_of_nonneg_right hΛ (by norm_num)
    have h5 : (Λ : ℝ) * 0.69 ≤ (Λ : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  have h6 : (2 : ℝ) ^ Λ < 2 ^ (Λ + 1) := by
    rw [pow_succ]
    have : (0 : ℝ) < 2 ^ Λ := by positivity
    linarith
  linarith

/-- **The misaligned primes are many.** With `L = log |t|`: for every set `Ex` of `d ≤ L` primes, some prime `p ∉ Ex`, `p ≤ L^{9d + 6}`, has `t log p/2π` at distance more
than `L^{−(9d + 10)}` from the integers. So at least `d + 1` primes up to `L^{9d + 6}` are misaligned at that precision. -/
theorem exists_prime_not_mem_of_large :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ Ex : Finset ℕ, (Ex.card : ℝ) ≤ Real.log |t| →
      ∃ p : ℕ, p.Prime ∧ p ∉ Ex ∧ (p : ℝ) ≤ Real.log |t| ^ (9 * Ex.card) * Real.log |t| ^ 6 ∧
        1 / (Real.log |t| ^ (9 * Ex.card) * Real.log |t| ^ 10) < phaseDist t p := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht Ex hd => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hd ⊢
  have hℓexp := h.exp_eq
  generalize Real.log L = ℓ at h hℓexp
  have hL := h.hundred_le
  have hℓ := h.one_le
  have h100 := h.log_le
  have hM1 : 6 * L ^ 2 * ℓ ≤ (⌈6 * L ^ 2 * ℓ⌉₊ : ℝ) := Nat.le_ceil _
  have hM2 : ((⌈6 * L ^ 2 * ℓ⌉₊ : ℕ) : ℝ) ≤ 6 * L ^ 2 * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil _
  have hk2 : ((⌈L⌉₊ : ℕ) : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hfl1 : ((⌊L / 2⌋₊ : ℕ) : ℝ) ≤ L / 2 := Nat.floor_le (by linarith)
  have hfl2 := Nat.lt_floor_add_one (L / 2)
  have hfl3 : 2 ≤ ⌊L / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hN₁r : ((⌊L / 2⌋₊ - 1 : ℕ) : ℝ) = ((⌊L / 2⌋₊ : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  obtain ⟨c, S⟩ := h.exists_fineWord hexp hM1 hM2 hk1 hk2 (N₁ := ⌊L / 2⌋₊ - 1) (by linarith) (by omega)
  have hML : ((⌈6 * L ^ 2 * ℓ⌉₊ : ℕ) : ℝ) + 1 ≤ L ^ 3 := by linarith [h.M_add_two_le hM2]
  have hstep0 := fun K (hK : 1 ≤ K) => h.step_fine hexp hM2 (N₁ := ⌊L / 2⌋₊ - 1) (K := K) (by linarith) hK
  obtain ⟨N₁, hN₁⟩ : ∃ N₁, N₁ = ⌊L / 2⌋₊ - 1 := ⟨_, rfl⟩
  rw [← hN₁] at S hstep0
  obtain ⟨M, hM⟩ : ∃ M, M = ⌈6 * L ^ 2 * ℓ⌉₊ := ⟨_, rfl⟩
  rw [← hM] at S hML hstep0
  have hA : 100 * ℓ ≤ (⌈100 * ℓ⌉₊ : ℝ) := Nat.le_ceil _
  have hA2 : ((⌈100 * ℓ⌉₊ : ℕ) : ℝ) ≤ 101 * ℓ := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 100 * ℓ)
    linarith
  obtain ⟨A, hAdef⟩ : ∃ A, A = ⌈100 * ℓ⌉₊ := ⟨_, rfl⟩
  rw [← hAdef] at hA hA2
  obtain ⟨d, hdd⟩ : ∃ d, d = Ex.card := ⟨_, rfl⟩
  rw [← hdd] at hd ⊢
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hA1 : (1 : ℝ) ≤ A := by linarith
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = A * (d + 1) := ⟨_, rfl⟩
  have hΛr : (Λ : ℝ) = (A : ℝ) * ((d : ℝ) + 1) := by
    rw [hΛdef]
    push_cast
    ring
  have hΛ1 : (1 : ℝ) ≤ Λ := by
    rw [hΛr]
    nlinarith
  have hΛL : (Λ : ℝ) ≤ 2 * L ^ 2 := by
    rw [hΛr]
    have h1 : (A : ℝ) ≤ 1.01 * L := by linarith
    have h2 : (d : ℝ) + 1 ≤ 1.01 * L := by linarith
    nlinarith
  have hΛbig : 100 * ℓ * ((d : ℝ) + 1) ≤ Λ := by
    rw [hΛr]
    exact mul_le_mul_of_nonneg_right hA (by linarith)
  have hMr : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  -- The modulus of the rank.
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hW : 2 * (((M : ℝ) + 1) ^ 2 * (Λ : ℝ)) + 1 ≤ L ^ 9 := by
    have h1 : ((M : ℝ) + 1) ^ 2 ≤ (L ^ 3) ^ 2 := pow_le_pow_left₀ (by linarith) hML 2
    have h2 : ((M : ℝ) + 1) ^ 2 * (Λ : ℝ) ≤ (L ^ 3) ^ 2 * (2 * L ^ 2) :=
      mul_le_mul h1 hΛL (by linarith) (by positivity)
    have e : (L ^ 3) ^ 2 * (2 * L ^ 2) = 2 * L ^ 8 := by ring
    rw [e] at h2
    have h8 : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ hL1
    have e9 : L ^ 9 = L ^ 8 * L := by ring
    rw [e9]
    nlinarith
  obtain ⟨V, hV⟩ : ∃ V, V = (2 * ((M + 1) ^ 2 * (Λ * 1)) + 1) ^ d := ⟨_, rfl⟩
  have hVr : (V : ℝ) ≤ L ^ (9 * d) := by
    rw [hV, pow_mul]
    push_cast
    rw [mul_one]
    exact pow_le_pow_left₀ (by positivity) hW d
  obtain ⟨K, hK⟩ : ∃ K, K = 6 * V + 1 := ⟨_, rfl⟩
  have hX : (1 : ℝ) ≤ L ^ (9 * d) := one_le_pow₀ hL1
  have hKr : (K : ℝ) ≤ 7 * L ^ (9 * d) := by
    rw [hK]
    push_cast
    linarith
  have hK1 : 1 ≤ K := by omega
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hsizeN := misaligned_size hL hX hKr hML hMr
  have hreal : ((1 + 1 * (8 * K * (6 * M + 5)) : ℕ) : ℝ) ≤ L ^ (9 * d) * L ^ 6 := by
    push_cast
    have e : (M : ℝ) + 1 - 1 = M := by ring
    rw [e] at hsizeN
    linarith
  have hΛlt : 1 + 1 * (8 * K * (6 * M + 5)) < 2 ^ (Λ + 1) := by
    have := lt_two_pow_of_exp hℓexp hℓ hreal hΛbig
    exact_mod_cast this
  have hprec := misaligned_prec hL hX hKr hK1r hML hMr hΛ1 hΛL
  obtain ⟨p, hp, hpEx, hple, hpε⟩ := exists_prime_not_mem S (h := 8 * K) (by omega) Ex (K := K) (Λ := Λ)
    (by
      rw [← hdd, ← hV, hK]
      omega) (hstep0 K hK1) hΛlt (ε := 1 / (L ^ (9 * d) * L ^ 10)) (by positivity) hprec
  refine ⟨p, hp, hpEx, ?_, hpε⟩
  have : (p : ℝ) ≤ ((1 + 1 * (8 * K * (6 * M + 5)) : ℕ) : ℝ) := by exact_mod_cast hple
  exact this.trans hreal

end

end GaloisForLFunctions.PrimeTorusTheory
