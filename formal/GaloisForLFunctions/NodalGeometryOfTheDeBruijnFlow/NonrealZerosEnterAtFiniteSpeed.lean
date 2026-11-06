import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.NonrealTimeOnWindows

/-!
# Nonreal zeros enter at finite speed

The vertical energy `E₁` of a unit window evolves by `E₁(b) − E₁(a) + 2∫N ≤ K log X ∫E₁^{out}`, with `N` the nonreal count. Iterating it over nested blocks is a discrete parabolic estimate: the energy and the nonreal time of a block at time `b` are bounded by a Poisson average of the energies of the enlarged blocks at time `a`,

`E₁(A, B; b) + 2 Σ_j ∫_a^b N_j ≤ Σ_{k ≤ J} E₁(A − 4k, B + 4k; a) · w^k/k! + C (size) log X · w^{J+1}/(J + 1)!`,   `w = Λ log X (b − a)`

(`exists_energy_propagates_at_finite_speed`). Since `b ≤ 1/log X` gives `w ≤ Λ`, the domain of dependence of the times `t ≲ 1/log X` has bounded width, up to a super-exponentially small tail.

This is the lateral control of nonreal zeros. A window that is real at time `a` on a neighbourhood of width `4J` stays real on its core in the following sense: its energy and its total nonreal time up to `b` are at most `C (size) log X · w^{J+1}/(J + 1)!`, and any nonreal zero that arrives there has height at most the square root of this (`exists_nonreal_entry_le`). The energy does not exclude a pair of tiny height: exact reality on the core is not claimed.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn
open scoped Nat

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The Poisson weights -/

/-- The integral of a Poisson weight is the next weight. -/
theorem mul_integral_poisson_weight (Λ a b : ℝ) (k : ℕ) :
    Λ * ∫ s in a..b, (Λ * (s - a)) ^ k / (k ! : ℝ) = (Λ * (b - a)) ^ (k + 1) / ((k + 1)! : ℝ) := by
  have h (s : ℝ) : (Λ * (s - a)) ^ k / (k ! : ℝ) = Λ ^ k / (k ! : ℝ) * (s - a) ^ k := by
    rw [mul_pow]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x => x ^ k) a,
    integral_pow, sub_self, zero_pow (Nat.succ_ne_zero k), sub_zero, mul_pow, Nat.factorial_succ]
  push_cast
  have h1 : (k ! : ℝ) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- One integration of the Poisson bound. -/
theorem nest_step {f : ℕ → ℝ → ℝ} {Λ S a b : ℝ} {J : ℕ} (hΛ : 0 ≤ Λ) (hab : a ≤ b) (hc : Continuous (f 1))
    (hbound : ∀ s ∈ Icc a b, f 1 s ≤ ∑ k ∈ Finset.range J, f (k + 1) a * ((Λ * (s - a)) ^ k / (k ! : ℝ)) +
      S * ((Λ * (s - a)) ^ J / (J ! : ℝ))) :
    f 0 a + Λ * ∫ s in a..b, f 1 s ≤
      ∑ k ∈ Finset.range (J + 1), f k a * ((Λ * (b - a)) ^ k / (k ! : ℝ)) +
        S * ((Λ * (b - a)) ^ (J + 1) / ((J + 1)! : ℝ)) := by
  have hweight (k : ℕ) : Continuous fun s : ℝ => (Λ * (s - a)) ^ k / (k ! : ℝ) := by fun_prop
  have hI (k : ℕ) : IntervalIntegrable (fun s : ℝ => (Λ * (s - a)) ^ k / (k ! : ℝ)) volume a b :=
    (hweight k).intervalIntegrable a b
  have hsumc : Continuous fun s : ℝ => ∑ k ∈ Finset.range J, f (k + 1) a * ((Λ * (s - a)) ^ k / (k ! : ℝ)) :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (hweight k)
  have hlastc : Continuous fun s : ℝ => S * ((Λ * (s - a)) ^ J / (J ! : ℝ)) := continuous_const.mul (hweight J)
  have hmono : (∫ s in a..b, f 1 s) ≤ ∫ s in a..b,
      (∑ k ∈ Finset.range J, f (k + 1) a * ((Λ * (s - a)) ^ k / (k ! : ℝ)) +
        S * ((Λ * (s - a)) ^ J / (J ! : ℝ))) :=
    intervalIntegral.integral_mono_on hab (hc.intervalIntegrable a b)
      ((hsumc.add hlastc).intervalIntegrable a b) hbound
  rw [intervalIntegral.integral_add (hsumc.intervalIntegrable a b) (hlastc.intervalIntegrable a b),
    intervalIntegral.integral_finsetSum fun k _ => (hI k).const_mul _,
    intervalIntegral.integral_const_mul] at hmono
  have hsum : Λ * ∑ k ∈ Finset.range J, ∫ s in a..b, f (k + 1) a * ((Λ * (s - a)) ^ k / (k ! : ℝ)) =
      ∑ k ∈ Finset.range J, f (k + 1) a * ((Λ * (b - a)) ^ (k + 1) / ((k + 1)! : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, ← mul_integral_poisson_weight]
    ring
  have hlast : Λ * (S * ∫ s in a..b, (Λ * (s - a)) ^ J / (J ! : ℝ)) =
      S * ((Λ * (b - a)) ^ (J + 1) / ((J + 1)! : ℝ)) := by
    rw [← mul_integral_poisson_weight]
    ring
  have h2 := mul_le_mul_of_nonneg_left hmono hΛ
  rw [mul_add, hsum, hlast] at h2
  rw [Finset.sum_range_succ']
  have h0 : f 0 a * ((Λ * (b - a)) ^ 0 / ((0 : ℕ)! : ℝ)) = f 0 a := by simp
  rw [h0]
  linarith only [h2]

/-- **The Poisson bound for a nested family.** If `f_k(b) ≤ f_k(a) + Λ ∫_a^b f_{k+1}` for `k < J`, and `f_J ≤ S`, then `f_0` is bounded by the Poisson average of the initial values, with last term `S · w^J/J!`. -/
theorem nest_poisson_le {Λ S a T : ℝ} (hΛ : 0 ≤ Λ) : ∀ (J : ℕ) (f : ℕ → ℝ → ℝ), (∀ k, Continuous (f k)) →
    (∀ s ∈ Icc a T, f J s ≤ S) →
    (∀ k < J, ∀ b ∈ Icc a T, f k b ≤ f k a + Λ * ∫ s in a..b, f (k + 1) s) →
    ∀ b ∈ Icc a T, f 0 b ≤ ∑ k ∈ Finset.range J, f k a * ((Λ * (b - a)) ^ k / (k ! : ℝ)) +
      S * ((Λ * (b - a)) ^ J / (J ! : ℝ)) := by
  intro J
  induction J with
  | zero =>
    intro f _ hS _ b hb
    simpa using hS b hb
  | succ J ih =>
    intro f hc hS hlaw b hb
    have h1 := ih (fun k => f (k + 1)) (fun k => hc _) hS (fun k hk c hc' => hlaw (k + 1) (by omega) c hc')
    refine (hlaw 0 (by omega) b hb).trans ?_
    exact nest_step hΛ hb.1 (hc 1) fun s hs => h1 s ⟨hs.1, hs.2.trans hb.2⟩

/-! ## The block law and the crude bound -/

/-- The law of the vertical energy on a block. -/
theorem block_square_law {K X₀ Y : ℝ} (hlaws : WindowLaws K X₀) (hK : 0 < K) (hX₀ : 1 ≤ X₀) (hY : 1 ≤ Y)
    {A B : ℤ} (hA : X₀ ≤ A) (hB : (B : ℝ) ≤ Y) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 8)
    (hbY : b * Real.log Y ≤ 1) :
    blockObs uSquare A B b - blockObs uSquare A B a + 2 * ∑ j ∈ Finset.Icc A B, ∫ s in a..b, windowObs uNonreal j s ≤
      9 * K * Real.log Y * ∫ s in a..b, blockObs uSquare (A - 4) (B + 4) s := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hL : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hone (j : ℤ) (hj : j ∈ Finset.Icc A B) :
      windowObs uSquare j b - windowObs uSquare j a + 2 * (∫ s in a..b, windowObs uNonreal j s) ≤
        K * Real.log Y * ∫ s in a..b, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uSquare s := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    have hjA : (A : ℝ) ≤ j := by exact_mod_cast h1
    have hjB : (j : ℝ) ≤ B := by exact_mod_cast h2
    have hjpos : (0 : ℝ) < j := by linarith only [hX₀, hA, hjA]
    have hlog : Real.log j ≤ Real.log Y := Real.log_le_log hjpos (hjB.trans hB)
    have hbj : b * Real.log j ≤ 1 := (mul_le_mul_of_nonneg_left hlog hb0).trans hbY
    obtain ⟨-, h3, -⟩ := hlaws j (hA.trans hjA) a b ha hab hb hbj
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ (integral_outerObs_nonneg uSquare_nonneg j hab))
    exact mul_le_mul_of_nonneg_left hlog hK.le
  have hsum := Finset.sum_le_sum hone
  have hint := sum_integral_outerObs_le continuous_uSquare uSquare_nonneg A B ha hab
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  change blockObs uSquare A B b - blockObs uSquare A B a + 2 * _ ≤ _ at hsum
  refine hsum.trans ?_
  have hKL : 0 ≤ K * Real.log Y := mul_nonneg hK.le hL
  have := mul_le_mul_of_nonneg_left hint hKL
  linarith only [this]

/-- The vertical energy of a unit window is at most its zero count. -/
theorem exists_windowObs_square_le :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ j : ℤ, X₀ ≤ j → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 8 → s * Real.log j ≤ 1 →
      windowObs uSquare j s ≤ C * Real.log j := by
  obtain ⟨C, hC, X₀, hX₀, hforce⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨C, hC, X₀, hX₀, fun j hj s hs hs8 hsj => ?_⟩
  obtain ⟨S, Q, hS, hcount, -, -⟩ := hforce j hj s hs hs8 hsj
  have heq := heatLocalizedZeroObservable_eq_sum (X := (j : ℝ)) hs w₀ uSquare
    (fun x hx => w₀_eq_zero hx) S (fun z hz hr => (hS z).mpr ⟨hz, by linarith only [hr]⟩)
  change windowObs uSquare j s = _ at heq
  rw [heq]
  refine le_trans ?_ hcount
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hs ((hS z).mp hz).1
  have hy : uSquare z.im ≤ 1 := by
    unfold uSquare
    have := abs_le.mp him
    nlinarith only [this.1, this.2]
  have hw : w₀ (z.re - j) * uSquare z.im ≤ 1 :=
    (mul_le_mul (w₀_le_one _) hy (uSquare_nonneg _) zero_le_one).trans (by norm_num)
  have hm : (0 : ℝ) ≤ zeroMult (riemannHeat s) z := Nat.cast_nonneg _
  simpa using mul_le_mul_of_nonneg_left hw hm

/-! ## Finite speed -/

/-- **The energy propagates at finite speed.** On a block of unit windows at heights `≤ Y`, for `0 ≤ a ≤ b ≤ 1/log Y` and any `J`, the energy at time `b` and the nonreal time on `[a, b]` are bounded by the Poisson average with parameter `w = Λ log Y (b − a)` of the energies of the enlarged blocks at time `a`, with last term `C (size) log Y · w^{J+1}/(J + 1)!`. -/
theorem exists_energy_propagates_at_finite_speed :
    ∃ Λ₀ > 0, ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ (Y : ℝ) (A B : ℤ) (J : ℕ), 8 ≤ Real.log Y → A ≤ B →
      X₀ ≤ ((A - 4 * ((J : ℤ) + 1) : ℤ) : ℝ) → ((B + 4 * ((J : ℤ) + 1) : ℤ) : ℝ) ≤ Y →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b * Real.log Y ≤ 1 →
        blockObs uSquare A B b + 2 * ∑ j ∈ Finset.Icc A B, ∫ s in a..b, windowObs uNonreal j s ≤
          ∑ k ∈ Finset.range (J + 1), blockObs uSquare (A - 4 * (k : ℤ)) (B + 4 * (k : ℤ)) a *
              ((Λ₀ * Real.log Y * (b - a)) ^ k / (k ! : ℝ)) +
            C * (((B - A + 8 * ((J : ℤ) + 1) + 1 : ℤ) : ℝ) * Real.log Y) *
              ((Λ₀ * Real.log Y * (b - a)) ^ (J + 1) / ((J + 1)! : ℝ)) := by
  obtain ⟨K₀, hK₀, X₁, hX₁, hlaws⟩ := exists_window_laws
  obtain ⟨C₀, hC₀, X₂, hX₂, hcrude⟩ := exists_windowObs_square_le
  refine ⟨9 * K₀, by positivity, C₀, hC₀, max X₁ X₂, hX₁.trans (le_max_left _ _), ?_⟩
  intro Y A B J hlogY hAB hA hB a b ha hab hbY
  set X₀ := max X₁ X₂ with hX₀def
  have hX₀1 : 1 ≤ X₀ := by linarith only [hX₁, le_max_left X₁ X₂]
  have hW : WindowLaws K₀ X₀ := fun j hj => hlaws j ((le_max_left _ _).trans hj)
  set L := Real.log Y with hLdef
  have hL : 0 < L := by linarith only [hlogY]
  have hJn : (0 : ℤ) ≤ J := Int.natCast_nonneg J
  have hAdown (n : ℤ) (hn : n ≤ J + 1) : X₀ ≤ ((A - 4 * n : ℤ) : ℝ) := by
    refine hA.trans ?_
    have : A - 4 * ((J : ℤ) + 1) ≤ A - 4 * n := by omega
    exact_mod_cast this
  have hBup (n : ℤ) (hn : n ≤ J + 1) : ((B + 4 * n : ℤ) : ℝ) ≤ Y := by
    refine le_trans ?_ hB
    have : B + 4 * n ≤ B + 4 * ((J : ℤ) + 1) := by omega
    exact_mod_cast this
  have hY : 1 ≤ Y := by
    have h1 := hAdown (J + 1) le_rfl
    have h2 := hBup (J + 1) le_rfl
    have h3 : ((A - 4 * ((J : ℤ) + 1) : ℤ) : ℝ) ≤ ((B + 4 * ((J : ℤ) + 1) : ℤ) : ℝ) := by
      have : A - 4 * ((J : ℤ) + 1) ≤ B + 4 * ((J : ℤ) + 1) := by omega
      exact_mod_cast this
    linarith only [h1, h2, h3, hX₀1]
  have hb0 : 0 ≤ b := ha.trans hab
  have hτ (s : ℝ) (hs : s ∈ Icc a b) : 0 ≤ s ∧ s ≤ 1 / 8 ∧ s * L ≤ 1 := by
    have h0 : 0 ≤ s := ha.trans hs.1
    have h1 : s * L ≤ 1 := (mul_le_mul_of_nonneg_right hs.2 hL.le).trans hbY
    refine ⟨h0, ?_, h1⟩
    have h2 : s * 8 ≤ s * L := mul_le_mul_of_nonneg_left hlogY h0
    linarith only [h1, h2]
  -- the nested family
  set f : ℕ → ℝ → ℝ := fun k s => blockObs uSquare (A - 4 * (k : ℤ)) (B + 4 * (k : ℤ)) (max s 0) with hf
  have hfc (k : ℕ) : Continuous (f k) := continuous_blockObs_clamped continuous_uSquare _ _
  have hfeq (k : ℕ) {s : ℝ} (hs : 0 ≤ s) : f k s = blockObs uSquare (A - 4 * (k : ℤ)) (B + 4 * (k : ℤ)) s := by
    simp only [hf, max_eq_left hs]
  set Λ := 9 * K₀ * L with hΛdef
  have hΛ : 0 ≤ Λ := by positivity
  -- the integral of the next member
  have hcong (k : ℕ) (c : ℝ) (hc : a ≤ c) : (∫ s in a..c, f (k + 1) s) =
      ∫ s in a..c, blockObs uSquare (A - 4 * (k : ℤ) - 4) (B + 4 * (k : ℤ) + 4) s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hc] at hs
    rw [hfeq _ (ha.trans hs.1)]
    congr 1 <;> (push_cast; ring)
  -- the nesting
  have hlaw (k : ℕ) (hk : k ≤ J) (c : ℝ) (hc : c ∈ Icc a b) :
      blockObs uSquare (A - 4 * (k : ℤ)) (B + 4 * (k : ℤ)) c +
          2 * ∑ j ∈ Finset.Icc (A - 4 * (k : ℤ)) (B + 4 * (k : ℤ)), ∫ s in a..c, windowObs uNonreal j s ≤
        f k a + Λ * ∫ s in a..c, f (k + 1) s := by
    obtain ⟨h0, h8, hcL⟩ := hτ c hc
    have hkz : (k : ℤ) ≤ J + 1 := by omega
    have h := block_square_law hW hK₀ hX₀1 hY (A := A - 4 * (k : ℤ)) (B := B + 4 * (k : ℤ)) (hAdown k hkz)
      (hBup k hkz) ha hc.1 h8 hcL
    rw [hcong k c hc.1, hfeq k ha]
    linarith only [h]
  have hnest : ∀ k < J, ∀ c ∈ Icc a b, f (k + 1) c ≤ f (k + 1) a + Λ * ∫ s in a..c, f (k + 1 + 1) s := by
    intro k hk c hc
    have h0 := (hτ c hc).1
    have h := hlaw (k + 1) (by omega) c hc
    rw [hfeq (k + 1) h0]
    have hN : 0 ≤ ∑ j ∈ Finset.Icc (A - 4 * ((k + 1 : ℕ) : ℤ)) (B + 4 * ((k + 1 : ℕ) : ℤ)),
        ∫ s in a..c, windowObs uNonreal j s :=
      Finset.sum_nonneg fun j _ => intervalIntegral.integral_nonneg hc.1 fun s _ =>
        windowObs_nonneg uNonreal_nonneg j s
    linarith only [h, hN]
  -- the crude bound on the outermost block
  set size : ℝ := ((B - A + 8 * ((J : ℤ) + 1) + 1 : ℤ) : ℝ) with hsize
  have hsize0 : 0 ≤ size := by
    have : (0 : ℤ) ≤ B - A + 8 * ((J : ℤ) + 1) + 1 := by omega
    rw [hsize]
    exact_mod_cast this
  have hlast : ∀ s ∈ Icc a b, f (J + 1) s ≤ C₀ * (size * L) := by
    intro s hs
    obtain ⟨h0, h8, hsL⟩ := hτ s hs
    rw [hfeq _ h0]
    unfold blockObs
    have hA' : A - 4 * ((J + 1 : ℕ) : ℤ) = A - 4 * ((J : ℤ) + 1) := by push_cast; ring
    have hB' : B + 4 * ((J + 1 : ℕ) : ℤ) = B + 4 * ((J : ℤ) + 1) := by push_cast; ring
    rw [hA', hB']
    have hcard : ((Finset.Icc (A - 4 * ((J : ℤ) + 1)) (B + 4 * ((J : ℤ) + 1))).card : ℝ) = size := by
      rw [Int.card_Icc]
      have h1 : (0 : ℤ) ≤ B + 4 * ((J : ℤ) + 1) + 1 - (A - 4 * ((J : ℤ) + 1)) := by omega
      have h2 : (((B + 4 * ((J : ℤ) + 1) + 1 - (A - 4 * ((J : ℤ) + 1))).toNat : ℕ) : ℤ) =
          B - A + 8 * ((J : ℤ) + 1) + 1 := by
        rw [Int.toNat_of_nonneg h1]
        ring
      rw [hsize, ← h2]
      push_cast
      rfl
    have hsum : ∑ j ∈ Finset.Icc (A - 4 * ((J : ℤ) + 1)) (B + 4 * ((J : ℤ) + 1)), windowObs uSquare j s ≤
        ∑ _j ∈ Finset.Icc (A - 4 * ((J : ℤ) + 1)) (B + 4 * ((J : ℤ) + 1)), C₀ * L := by
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
      have hj1 : ((A - 4 * ((J : ℤ) + 1) : ℤ) : ℝ) ≤ j := by exact_mod_cast h1
      have hj2 : (j : ℝ) ≤ ((B + 4 * ((J : ℤ) + 1) : ℤ) : ℝ) := by exact_mod_cast h2
      have hjX : X₀ ≤ j := (hAdown (J + 1) le_rfl).trans hj1
      have hjY : (j : ℝ) ≤ Y := hj2.trans (hBup (J + 1) le_rfl)
      have hjpos : (0 : ℝ) < j := by linarith only [hjX, hX₀1]
      have hlog : Real.log j ≤ L := Real.log_le_log hjpos hjY
      have hsj : s * Real.log j ≤ 1 := (mul_le_mul_of_nonneg_left hlog h0).trans hsL
      refine (hcrude j ((le_max_right _ _).trans hjX) s h0 h8 hsj).trans ?_
      exact mul_le_mul_of_nonneg_left hlog hC₀.le
    refine hsum.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  -- the Poisson bound on the shifted family
  have hb' : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hPoisson := nest_poisson_le (a := a) (T := b) (S := C₀ * (size * L)) hΛ J (fun k => f (k + 1))
    (fun k => hfc _) hlast hnest
  have hstep := nest_step (f := f) (J := J) (S := C₀ * (size * L)) hΛ hab (hfc 1)
    (fun s hs => hPoisson s hs)
  have h0law := hlaw 0 (by omega) b hb'
  have hA0 : A - 4 * ((0 : ℕ) : ℤ) = A := by simp
  have hB0 : B + 4 * ((0 : ℕ) : ℤ) = B := by simp
  rw [hA0, hB0] at h0law
  refine h0law.trans (hstep.trans (le_of_eq ?_))
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hfeq k ha, hΛdef]

/-! ## Entry of a nonreal zero -/

/-- The depth of a zero over the core is at most the energy of the window. -/
theorem sq_im_le_windowObs {j : ℤ} {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : riemannHeat s z = 0)
    (hre : |z.re - j| ≤ 1 / 2) : z.im ^ 2 ≤ windowObs uSquare j s := by
  have hsum := summable_heatLocalizedZeroObservable (t := s) hasCompactSupport_w₀ uSquare j hs
  have hle := hsum.le_tsum z (fun w _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (w₀_nonneg _) (uSquare_nonneg _)))
  have hm : (1 : ℝ) ≤ zeroMult (riemannHeat s) z := by
    exact_mod_cast one_le_zeroMult_riemannHeat hs hz
  rw [w₀_eq_one hre, one_mul] at hle
  have hdef : windowObs uSquare j s = ∑' w : ℂ, (zeroMult (riemannHeat s) w : ℝ) *
      (w₀ (w.re - j) * uSquare w.im) := rfl
  rw [hdef]
  refine le_trans ?_ hle
  have h2 := mul_le_mul_of_nonneg_right hm (uSquare_nonneg z.im)
  rw [one_mul] at h2
  exact h2

/-- A window whose zeros are real at time `s` has no vertical energy. -/
theorem windowObs_square_eq_zero {j : ℤ} {s : ℝ} (hs : 0 ≤ s) (hreal : ∀ z : ℂ, riemannHeat s z = 0 → |z.re - j| < 1 → z.im = 0) :
    windowObs uSquare j s = 0 := by
  have hdef : windowObs uSquare j s = ∑' w : ℂ, (zeroMult (riemannHeat s) w : ℝ) *
      (w₀ (w.re - j) * uSquare w.im) := rfl
  rw [hdef]
  refine (tsum_congr fun w => ?_).trans tsum_zero
  by_cases hw : riemannHeat s w = 0
  · rcases lt_or_ge |w.re - j| 1 with h | h
    · simp [uSquare, hreal w hw h]
    · simp [w₀_eq_zero h]
  · simp [zeroMult_riemannHeat_eq_zero hs hw]

/-- **Lateral control of nonreal zeros.** If all zeros over the enlarged block of width `4J` are real at time `a`, then at time `b ≤ 1/log Y` the energy of the block and its nonreal time on `[a, b]` are at most `C (size) log Y · w^{J+1}/(J + 1)!`, `w = Λ log Y (b − a)`. A nonreal zero that arrives over the core has squared height below this. -/
theorem exists_nonreal_entry_le :
    ∃ Λ₀ > 0, ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ (Y : ℝ) (A B : ℤ) (J : ℕ), 8 ≤ Real.log Y → A ≤ B →
      X₀ ≤ ((A - 4 * ((J : ℤ) + 1) : ℤ) : ℝ) → ((B + 4 * ((J : ℤ) + 1) : ℤ) : ℝ) ≤ Y →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b * Real.log Y ≤ 1 →
        (∀ z : ℂ, riemannHeat a z = 0 → ((A - 4 * (J : ℤ) : ℤ) : ℝ) - 1 < z.re → z.re < ((B + 4 * (J : ℤ) : ℤ) : ℝ) + 1 →
          z.im = 0) →
        (blockObs uSquare A B b + 2 * ∑ j ∈ Finset.Icc A B, ∫ s in a..b, windowObs uNonreal j s ≤
          C * (((B - A + 8 * ((J : ℤ) + 1) + 1 : ℤ) : ℝ) * Real.log Y) *
            ((Λ₀ * Real.log Y * (b - a)) ^ (J + 1) / ((J + 1)! : ℝ))) ∧
        ∀ z : ℂ, riemannHeat b z = 0 → (A : ℝ) - 1 / 2 ≤ z.re → z.re ≤ (B : ℝ) + 1 / 2 →
          z.im ^ 2 ≤ C * (((B - A + 8 * ((J : ℤ) + 1) + 1 : ℤ) : ℝ) * Real.log Y) *
            ((Λ₀ * Real.log Y * (b - a)) ^ (J + 1) / ((J + 1)! : ℝ)) := by
  obtain ⟨Λ₀, hΛ₀, C, hC, X₀, hX₀, h⟩ := exists_energy_propagates_at_finite_speed
  refine ⟨Λ₀, hΛ₀, C, hC, X₀, hX₀, ?_⟩
  intro Y A B J hlogY hAB hA hB a b ha hab hbY hreal
  have hmain := h Y A B J hlogY hAB hA hB a b ha hab hbY
  have hzero : ∑ k ∈ Finset.range (J + 1), blockObs uSquare (A - 4 * (k : ℤ)) (B + 4 * (k : ℤ)) a *
      ((Λ₀ * Real.log Y * (b - a)) ^ k / (k ! : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkz : (k : ℤ) ≤ J := by exact_mod_cast hk'
    have hblock : blockObs uSquare (A - 4 * (k : ℤ)) (B + 4 * (k : ℤ)) a = 0 := by
      refine Finset.sum_eq_zero fun j hj => windowObs_square_eq_zero ha fun z hz hre => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
      have h3 := abs_lt.mp hre
      have h4 : ((A - 4 * (J : ℤ) : ℤ) : ℝ) ≤ j := by
        have : A - 4 * (J : ℤ) ≤ j := by omega
        exact_mod_cast this
      have h5 : (j : ℝ) ≤ ((B + 4 * (J : ℤ) : ℤ) : ℝ) := by
        have : j ≤ B + 4 * (J : ℤ) := by omega
        exact_mod_cast this
      exact hreal z hz (by linarith only [h3.1, h4]) (by linarith only [h3.2, h5])
    rw [hblock, zero_mul]
  rw [hzero, zero_add] at hmain
  have hN : 0 ≤ ∑ j ∈ Finset.Icc A B, ∫ s in a..b, windowObs uNonreal j s :=
    Finset.sum_nonneg fun j _ => intervalIntegral.integral_nonneg hab fun s _ =>
      windowObs_nonneg uNonreal_nonneg j s
  refine ⟨hmain, fun z hz hz1 hz2 => ?_⟩
  -- the nearest integer window
  obtain ⟨j, hj1, hj2⟩ : ∃ j : ℤ, j ∈ Finset.Icc A B ∧ |z.re - j| ≤ 1 / 2 := by
    set j₀ := max A (min B (round z.re)) with hj₀
    refine ⟨j₀, Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le hAB (min_le_left _ _)⟩, ?_⟩
    have hround := abs_sub_round z.re
    rcases le_total (round z.re) A with h1 | h1
    · have h2 : j₀ = A := by
        rw [hj₀]
        exact max_eq_left ((min_le_right _ _).trans h1)
      rw [h2, abs_le]
      have h3 : ((round z.re : ℤ) : ℝ) ≤ A := by exact_mod_cast h1
      have h4 := abs_le.mp hround
      constructor <;> linarith only [hz1, h3, h4.2]
    · rcases le_total (round z.re) B with h5 | h5
      · have h2 : j₀ = round z.re := by
          rw [hj₀, min_eq_right h5, max_eq_right h1]
        rw [h2]
        exact hround
      · have h2 : j₀ = B := by
          rw [hj₀, min_eq_left h5, max_eq_right hAB]
        rw [h2, abs_le]
        have h3 : (B : ℝ) ≤ ((round z.re : ℤ) : ℝ) := by exact_mod_cast h5
        have h4 := abs_le.mp hround
        constructor <;> linarith only [hz2, h3, h4.1]
  have hb0 : 0 ≤ b := ha.trans hab
  have h1 := sq_im_le_windowObs hb0 hz hj2
  have h2 : windowObs uSquare j b ≤ blockObs uSquare A B b :=
    Finset.single_le_sum (f := fun i => windowObs uSquare i b) (fun i _ => windowObs_nonneg uSquare_nonneg i b) hj1
  linarith only [h1, h2, hmain, hN]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
