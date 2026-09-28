import GaloisForLFunctions.RHTower.Sieve.PrimeCountRelativeWindow
import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardQuadTuples

/-!
# Prime counts in the windows of a prime tuple

For a window `(y, y(1+θ)]` and a modulus `d` (a product of primes), the cofactor window is
`(⌊y⌋/d, ⌊y(1+θ)⌋/d] = (⌊y/d⌋, ⌊(y/d)(1+θ)⌋]`.  A prime count above `r` in it vanishes unless
`d r ≤ y(1+θ)`, and otherwise the relative-window prime number theorem bounds it by
`(1+η) θ (y/d)/log(y/d)`, uniformly over all such `d, r` with `r ≥ y^{1/6}`.  Also: sums
dominated by indicators of nested index sets, and logarithmic coordinates `log q/log y` of
integers in `(y^l, y^r]`.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

/-- A sum dominated termwise by the indicator of a second index set. -/
theorem sum_le_sum_of_le_ite {ι : Type*} [DecidableEq ι] {S R : Finset ι} {f g : ι → ℝ}
    (hg : ∀ t ∈ R, 0 ≤ g t) (h : ∀ t ∈ S, f t ≤ if t ∈ R then g t else 0) :
    ∑ t ∈ S, f t ≤ ∑ t ∈ R, g t := by
  calc ∑ t ∈ S, f t ≤ ∑ t ∈ S, (if t ∈ R then g t else 0) := Finset.sum_le_sum h
    _ = ∑ t ∈ S.filter (· ∈ R), g t := (Finset.sum_filter _ _).symm
    _ ≤ ∑ t ∈ R, g t := Finset.sum_le_sum_of_subset_of_nonneg
        (fun t ht => (Finset.mem_filter.1 ht).2) (fun t ht _ => hg t ht)

/-- A sum over pairs dominated by the indicator of a nested region `q₂ ∈ S₂, q₁ ∈ S₁ q₂`. -/
theorem sum_pairs_le_nested {S : Finset (ℕ × ℕ)} {S₂ : Finset ℕ} {S₁ : ℕ → Finset ℕ}
    {F G : ℕ × ℕ → ℝ} (hG : ∀ q₂ ∈ S₂, ∀ q₁ ∈ S₁ q₂, 0 ≤ G (q₁, q₂))
    (h : ∀ t ∈ S, F t ≤ if t.2 ∈ S₂ ∧ t.1 ∈ S₁ t.2 then G t else 0) :
    ∑ t ∈ S, F t ≤ ∑ q₂ ∈ S₂, ∑ q₁ ∈ S₁ q₂, G (q₁, q₂) := by
  set R : Finset (ℕ × ℕ) := (S₂.sigma S₁).image (fun x => (x.2, x.1)) with hRdef
  have hR : ∀ p : ℕ × ℕ, p ∈ R ↔ p.2 ∈ S₂ ∧ p.1 ∈ S₁ p.2 := by
    intro p
    simp only [hRdef, Finset.mem_image, Finset.mem_sigma]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨ha, hb⟩
    · intro h; exact ⟨⟨p.2, p.1⟩, h, rfl⟩
  rw [← Finset.sum_finset_product_right R S₂ S₁ hR]
  refine sum_le_sum_of_le_ite (fun t ht => ?_) (fun t ht => ?_)
  · obtain ⟨h1, h2⟩ := (hR t).1 ht
    exact hG _ h1 _ h2
  · have e : (t ∈ R) = (t.2 ∈ S₂ ∧ t.1 ∈ S₁ t.2) := propext (hR t)
    simp only [e]
    exact h t ht

/-- `y^(log q/log y) = q`. -/
theorem rpow_logScale {y : ℝ} {q : ℕ} (hy : 1 < y) (hq : 0 < q) :
    y ^ (log q / log y) = q := by
  have hly : log y ≠ 0 := (Real.log_pos hy).ne'
  rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hly,
    Real.exp_log (by exact_mod_cast hq)]

/-- An integer lies in `(y^l, y^r]` iff its logarithmic scale lies in `(l, r]`. -/
theorem mem_Ioc_floor_rpow_iff {y l r : ℝ} {q : ℕ} (hy : 1 < y) (hq : 0 < q) :
    q ∈ Finset.Ioc ⌊y ^ l⌋₊ ⌊y ^ r⌋₊ ↔ l < log q / log y ∧ log q / log y ≤ r := by
  have hly : 0 < log y := Real.log_pos hy
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Finset.mem_Ioc, Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity),
    lt_div_iff₀ hly, div_le_iff₀ hly]
  have e1 : y ^ l < q ↔ l * log y < log q := by
    rw [← Real.log_lt_log_iff (by positivity) hq', Real.log_rpow (by linarith)]
  have e2 : (q : ℝ) ≤ y ^ r ↔ log q ≤ r * log y := by
    rw [← Real.log_le_log_iff hq' (by positivity), Real.log_rpow (by linarith)]
  rw [e1, e2]

/-- The cofactor window of a modulus `d`. -/
theorem primeCountAbove_le_card_primesIn {y θ : ℝ} {d r : ℕ} :
    primeCountAbove (⌊y⌋₊ / d) (⌊y * (1 + θ)⌋₊ / d) r
      ≤ (primesIn (y / d) (y / d * (1 + θ))).card := by
  rw [← Nat.floor_div_natCast, ← Nat.floor_div_natCast,
    show y * (1 + θ) / d = y / d * (1 + θ) by ring]
  unfold primeCountAbove primesIn
  exact Finset.card_le_card (Finset.monotone_filter_right _ (fun p _ hp => hp.1))

/-- A nonzero prime count above `r` in the cofactor window forces `d r ≤ b`. -/
theorem mul_le_of_primeCountAbove_ne_zero {a b r d : ℕ} (hd : 0 < d)
    (h : primeCountAbove (a / d) (b / d) r ≠ 0) : d * r ≤ b := by
  unfold primeCountAbove at h
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  have h1 : p * d ≤ b := (Nat.le_div_iff_mul_le hd).1 hp.1.2
  calc d * r ≤ d * p := Nat.mul_le_mul_left _ hp.2.2
    _ = p * d := Nat.mul_comm _ _
    _ ≤ b := h1

/-- **Prime counts in the cofactor windows**, uniformly over moduli `d` and thresholds
`r ≥ y^{1/6}` with `d r ≤ y(1+θ)`. -/
theorem eventually_primeCountAbove_window_le {c η : ℝ} (hc : 0 < c)
    (hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z)) :
    ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ d r : ℕ, 0 < d → y ^ (1 / 6 : ℝ) ≤ r → (d : ℝ) * r ≤ y * (1 + θ) →
      (primeCountAbove (⌊y⌋₊ / d) (⌊y * (1 + θ)⌋₊ / d) r : ℝ)
        ≤ (1 + η) * (θ * (y / d) / log (y / d)) := by
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.1 hB2
  have hgrow : ∀ᶠ y : ℝ in atTop, 2 * max Z₁ 1 ≤ y ^ (5 / 48 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  filter_upwards [hgrow, eventually_gt_atTop (1 : ℝ)] with y hy hy1
  intro θ hθ hθ1 d r hd hr hdr
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hy0 : 0 < y := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set Z := y / d with hZ
  have hsplit : y ^ (1 / 6 : ℝ) = y ^ (5 / 48 : ℝ) * y ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_add hy0]; norm_num
  have h16 : 1 ≤ y ^ (1 / 16 : ℝ) := Real.one_le_rpow hy1.le (by norm_num)
  -- `Z ≥ y^{1/6}/2`
  have hZlow : y ^ (1 / 6 : ℝ) ≤ 2 * Z := by
    have h1 : (d : ℝ) * r ≤ y * 2 := hdr.trans (by nlinarith)
    have h2 : (r : ℝ) ≤ 2 * Z := by
      rw [hZ, mul_div_assoc', le_div_iff₀ hd0]; linarith
    linarith
  have hZ1 : Z₁ ≤ Z := by
    have : 2 * max Z₁ 1 ≤ 2 * Z := by
      calc 2 * max Z₁ 1 ≤ y ^ (5 / 48 : ℝ) := hy
        _ ≤ y ^ (5 / 48 : ℝ) * y ^ (1 / 16 : ℝ) := le_mul_of_one_le_right (by positivity) h16
        _ ≤ 2 * Z := by rw [← hsplit]; exact hZlow
    linarith [le_max_left Z₁ 1]
  have hZ16 : y ^ (1 / 16 : ℝ) ≤ Z := by
    have hm : 2 ≤ y ^ (5 / 48 : ℝ) := by linarith [le_max_right Z₁ 1]
    have : 2 * y ^ (1 / 16 : ℝ) ≤ 2 * Z := by
      calc 2 * y ^ (1 / 16 : ℝ) ≤ y ^ (5 / 48 : ℝ) * y ^ (1 / 16 : ℝ) :=
            mul_le_mul_of_nonneg_right hm (by positivity)
        _ ≤ 2 * Z := by rw [← hsplit]; exact hZlow
    linarith
  have hlogZ : log y / 16 ≤ log Z := by
    have := Real.log_le_log (by positivity) hZ16
    rw [Real.log_rpow hy0] at this
    linarith
  have hθZ : exp (-c * sqrt (log Z)) ≤ θ := by
    refine le_trans (Real.exp_le_exp.2 ?_) hθ
    have hs : sqrt (log y) / 4 ≤ sqrt (log Z) := by
      have : sqrt (log y / 16) ≤ sqrt (log Z) := Real.sqrt_le_sqrt hlogZ
      rwa [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16),
        show sqrt (16 : ℝ) = 4 by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    nlinarith
  have hcard := hZ₁ Z hZ1 θ hθZ hθ1
  calc (primeCountAbove (⌊y⌋₊ / d) (⌊y * (1 + θ)⌋₊ / d) r : ℝ)
      ≤ ((primesIn Z (Z * (1 + θ))).card : ℝ) := by exact_mod_cast primeCountAbove_le_card_primesIn
    _ ≤ (1 + η) * (θ * Z / log Z) := hcard

/-- `1/log(y/d)` in logarithmic coordinates. -/
theorem div_log_div_eq {y θ : ℝ} {d : ℕ} (hy : 1 < y) (hd : 0 < d) (hyd : (d : ℝ) < y) :
    θ * (y / d) / log (y / d) = θ * y / log y * (1 / d * (1 / (1 - log d / log y))) := by
  have hly : 0 < log y := Real.log_pos hy
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : log (y / d) = log y - log d := Real.log_div (by linarith) hd0.ne'
  have hlt : log d < log y := Real.log_lt_log hd0 hyd
  have h2 : log y - log d ≠ 0 := by linarith
  have h1 : 1 - log d / log y = (log y - log d) / log y := by field_simp
  rw [hl, h1]
  field_simp

/-- `y^a < m` in logarithmic coordinates. -/
theorem lt_logScale_of_rpow_lt {y a m : ℝ} (hy : 1 < y) (h : y ^ a < m) : a < log m / log y := by
  have hly : 0 < log y := Real.log_pos hy
  have hm : 0 < m := lt_of_le_of_lt (by positivity) h
  rw [lt_div_iff₀ hly]
  have := Real.log_lt_log (by positivity) h
  rwa [Real.log_rpow (by linarith)] at this

/-- `m ≤ y^b` in logarithmic coordinates. -/
theorem logScale_le_of_le_rpow {y b m : ℝ} (hy : 1 < y) (hm : 0 < m) (h : m ≤ y ^ b) :
    log m / log y ≤ b := by
  have hly : 0 < log y := Real.log_pos hy
  rw [div_le_iff₀ hly]
  have := Real.log_le_log hm h
  rwa [Real.log_rpow (by linarith)] at this

/-- The Harman parameters `z, Q, D, E` measured against the window scale `y`. -/
structure HarmanWindowScale (κ y : ℝ) (z Q D E : ℕ) : Prop where
  z_gt : y ^ (2 / 11 : ℝ) < z
  Q_le : (Q : ℝ) ≤ y ^ (1 / 2 + κ)
  D_gt : y ^ (1 / 4 - κ) < D
  D_le : (D : ℝ) ≤ y ^ (1 / 4 + κ)
  E_gt : y ^ (1 - κ) < E
  E_le : (E : ℝ) ≤ y ^ (1 + κ)

end RHTower.Sieve
