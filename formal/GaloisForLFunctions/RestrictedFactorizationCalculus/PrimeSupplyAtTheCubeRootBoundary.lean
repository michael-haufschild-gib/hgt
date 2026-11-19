import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount
import GaloisForLFunctions.RHTower.Sieve.GhsOuterBlock

/-!
# Prime supply beyond comparable factors

At product scale `s⁶` the smaller factor of a geometrically deficient pair
can be as small as `s²`. Mertens' first theorem prices the entire growing
band `(s²/2,2s³]`. Its log-weight is asymptotic to `log s`. The two factors'
logarithms have product at least `(15/2)(log s)²`, enough to fit the demand
into one prime interval of the original width.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells RHTower.Sieve

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Products admitting a prime factor between half the cube root and twice
the square root of the reference scale. -/
def cubeProducts (s u v : ℝ) : Finset ℕ :=
  (windowPrimes (s^2/2) (2*s^3)).biUnion fun q =>
    (windowPrimes (u/q) (v/q)).image (q*·)

/-- The prime window is the difference of the two exact integer prefix sets. -/
theorem windowPrimes_eq_primesLE_sdiff (u v : ℝ) : RHTower.windowPrimes u v =
    Nat.primesLE ⌊v⌋₊ \ Nat.primesLE ⌊u⌋₊ := by
  apply Finset.ext
  intro q
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  change q ∈ (Ioc _ _).filter Nat.Prime ↔ _
  simp only [mem_filter,mem_Ioc]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hp⟩
    exact ⟨⟨hhi,hp⟩,fun h => hlo.not_ge h.1⟩
  · rintro ⟨⟨hhi,hp⟩,hn⟩
    exact ⟨⟨lt_of_not_ge (fun h => hn ⟨h,hp⟩),hhi⟩,hp⟩

private theorem cube_band_mass {s : ℝ} (hs : 2 ≤ s)
    (hL : 20*(Real.log 2 + Real.log 4 + mertensBlockGapConst) ≤ Real.log s) :
    ∑ q ∈ windowPrimes (s^2/2) (2*s^3), Real.log q / q ≤ 21/20 * Real.log s := by
  have hs0 : 0 < s := by linarith only [hs]
  have ha : 2 ≤ s^2/2 := by nlinarith only [hs, sq_nonneg (s-2)]
  have hab : s^2/2 ≤ 2*s^3 := by nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg s),sq_nonneg s]
  have haN : 1 ≤ ⌊s^2/2⌋₊ := (Nat.one_le_floor_iff _).2 (by linarith only [ha])
  have hA : s^2/4 ≤ (⌊s^2/2⌋₊ : ℝ) := by
    linarith only [Nat.lt_floor_add_one (s^2/2),ha]
  have hB := Nat.floor_le (show 0 ≤ 2*s^3 by positivity)
  have hBn : 0 < (⌊2*s^3⌋₊ : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_of_lt haN) (Nat.floor_le_floor hab)
  have hu := Real.log_le_log hBn hB
  have hl := Real.log_le_log (show 0 < s^2/4 by positivity) hA
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hu
  rw [Real.log_div (by positivity) (by norm_num),Real.log_pow] at hl
  norm_num1 at hu hl
  rw [windowPrimes_eq_primesLE_sdiff]
  linarith only [mertensFirst_general_block haN (Nat.floor_le_floor hab), hL, hu, hl]

private theorem cube_logs {s : ℝ} (hs : 2 ≤ s) (hL : 10*Real.log 2 ≤ Real.log s)
    {q : ℕ} (hq : q ∈ windowPrimes (s^2/2) (2*s^3)) :
    Real.log s ≤ Real.log (s^6/q) ∧
    15/2 * Real.log s ^ 2 ≤ Real.log q * Real.log (s^6/q) := by
  have hs0 : 0 < s := by linarith only [hs]
  obtain ⟨hp, hl, hu⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
  have hq0 : (0:ℝ) < q := by exact_mod_cast hp.pos
  have hlo := Real.log_le_log (show 0 < s^2/2 by positivity) hl.le
  have hup := Real.log_le_log hq0 hu
  rw [Real.log_div (by positivity) (by norm_num),Real.log_pow] at hlo
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hup
  rw [Real.log_div (by positivity) hq0.ne', Real.log_pow]
  norm_num1 at hlo hup ⊢
  have hlog := Real.log_nonneg (show 1 ≤ s by linarith only [hs])
  have h1 : 0 ≤ Real.log q - 19/10 * Real.log s := by linarith only [hlo,hL]
  have h2 : 0 ≤ 41/10 * Real.log s - Real.log q := by linarith only [hup,hL,hlog]
  constructor
  · linarith only [hup,hL,hlog]
  · nlinarith only [mul_nonneg h1 h2,sq_nonneg (Real.log s)]

/-- The whole cube-root band uses at most nine tenths of the prime supply,
uniformly in every sharp quotient cell of fixed logarithmic relative width. -/
theorem eventually_cubeProducts_nine_tenths (B : ℕ) :
    ∀ᶠ s : ℝ in atTop, ∀ u v : ℝ, s^6 ≤ u → u ≤ v → v ≤ 2*s^6 →
      s^6 / Real.log s ^ B ≤ v-u → 10*(cubeProducts s u v).card ≤ 9*(windowPrimes u v).card := by
  obtain ⟨A,_,hupper⟩ := exists_card_windowPrimes_le B (by norm_num : (0:ℝ)<1/100)
  obtain ⟨H,_,hlower⟩ := exists_card_windowPrimes_div_ge B (by norm_num : (0:ℝ)<1/100)
  filter_upwards [eventually_ge_atTop (max 2 (max A H)),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (max (10*Real.log 2) (20*(Real.log 2 + Real.log 4 + mertensBlockGapConst)))] with s hs hL
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := by linarith only [hs2]
  have hs1 : 1 ≤ s := by linarith only [hs2]
  have hlog := Real.log_pos (show 1<s by linarith only [hs2])
  have hA : A ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hH : H ≤ s := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hm := cube_band_mass hs2 ((le_max_right _ _).trans hL)
  have h10 := (le_max_left _ _).trans hL
  intro u v hu huv hv hgap
  have hlen := sub_nonneg.mpr huv
  have hrow (q : ℕ) (hq : q ∈ windowPrimes (s^2/2) (2*s^3)) :
      ((windowPrimes (u/q) (v/q)).card:ℝ) ≤
        ((101/100)*(v-u)/(15/2 * Real.log s ^ 2)) * (Real.log q / q) := by
    obtain ⟨hp,_,hqhi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
    have hq0 : (0:ℝ)<q := by exact_mod_cast hp.pos
    obtain ⟨hl,hprod⟩ := cube_logs hs2 h10 hq
    have hlogq := hlog.trans_le hl
    have hsR : s ≤ s^6/q := (Real.log_le_log_iff hs0 (by positivity)).1 hl
    have hg : s^6/q / Real.log (s^6/q) ^ (B:ℝ) ≤ v/q-u/q := by
      rw [Real.rpow_natCast, ← sub_div, div_right_comm]
      exact div_le_div_of_nonneg_right
        ((div_le_div_of_nonneg_left (by positivity) (pow_pos hlog B)
          (pow_le_pow_left₀ hlog.le hl B)).trans hgap) hq0.le
    have h := hupper (s^6/q) (hA.trans hsR) (u/q) (v/q) (by gcongr) (by gcongr)
      (by rw [← mul_div_assoc]; gcongr) hg
    refine h.trans ?_
    rw [← sub_div, mul_div_assoc', div_div, div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hprod (mul_nonneg hlen hq0.le)]
  have hcnt : ((cubeProducts s u v).card:ℝ) ≤
      ((101/100)*(v-u)/(15/2 * Real.log s ^ 2)) *
        ∑ q ∈ windowPrimes (s^2/2) (2*s^3), Real.log q / q := by
    calc _ ≤ ∑ q ∈ windowPrimes (s^2/2) (2*s^3), ((windowPrimes (u/q) (v/q)).card:ℝ) := by
                have hn : (cubeProducts s u v).card ≤
                    ∑ q ∈ windowPrimes (s^2/2) (2*s^3), (windowPrimes (u/q) (v/q)).card :=
                  card_biUnion_le.trans (sum_le_sum (fun (q : ℕ) _ =>
                    card_image_le (s := windowPrimes (u/q) (v/q)) (f := (q*·))))
                exact_mod_cast hn
         _ ≤ _ := (sum_le_sum hrow).trans_eq (mul_sum _ _ _).symm
  have hprice : ((cubeProducts s u v).card:ℝ) ≤ (v-u)/(7 * Real.log s) := by
    refine hcnt.trans ((mul_le_mul_of_nonneg_left hm (by positivity)).trans ?_)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg hlen (sq_nonneg (Real.log s))]
  have h6 : s ≤ s^6 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hs1 (show 1 ≤ 6 by decide))
  have hbig : Real.log (2*s^6) = Real.log 2 + 6 * Real.log s := by
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]; norm_num
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hbigpos : 0 < Real.log (2*s^6) := by rw [hbig]; linarith only [hlog2,hlog]
  have hlow := hlower (2*s^6) (by linarith only [hH,h6,hs0]) 2 (by norm_num) (by norm_num)
    (2*u) (2*v) (by linarith only [hu]) (by linarith only [huv]) (by linarith only [hv]) (by
      rw [Real.rpow_natCast, mul_div_assoc]
      have hle : Real.log s ≤ Real.log (2*s^6) := by rw [hbig]; linarith only [hlog,hlog2]
      have h := (div_le_div_of_nonneg_left (show 0 ≤ s^6 by positivity)
        (pow_pos hlog B) (pow_le_pow_left₀ hlog.le hle B)).trans hgap
      linarith only [h])
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] at hlow
  have hratio : 10*((v-u)/(7*Real.log s)) ≤
      9*((1-1/100)*(2*v-2*u)/(2*Real.log (2*s^6))) := by
    rw [← mul_div_assoc,← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity),hbig]
    nlinarith only [mul_le_mul_of_nonneg_right h10 hlen, mul_nonneg hlen hlog.le]
  exact_mod_cast (mul_le_mul_of_nonneg_left hprice (by norm_num : (0:ℝ) ≤ 10)).trans
    (hratio.trans (mul_le_mul_of_nonneg_left hlow (by norm_num : (0:ℝ) ≤ 9)))

/-- Every semiprime in the cube-root band can be assigned a distinct prime. -/
theorem eventually_cubeProducts_capacity (B : ℕ) :
    ∀ᶠ s : ℝ in atTop, ∀ u v : ℝ, s^6 ≤ u → u ≤ v → v ≤ 2*s^6 →
      s^6 / Real.log s ^ B ≤ v-u → (cubeProducts s u v).card ≤ (windowPrimes u v).card := by
  filter_upwards [eventually_cubeProducts_nine_tenths B] with s hs u v hu huv hv hw
  have := hs u v hu huv hv hw
  omega

/-- Ordinary prime supply in a full sharp octave. -/
theorem eventually_dyadic_prime_lower :
    ∀ᶠ v : ℝ in atTop, (99/100)*v/Real.log (2*v) ≤ ((windowPrimes v (2*v)).card:ℝ) := by
  obtain ⟨H,_,hc⟩ := exists_card_windowPrimes_div_ge 0 (by norm_num : (0:ℝ)<1/100)
  filter_upwards [eventually_ge_atTop (max 2 H)] with v hv
  have hv0 : 0<v := by linarith only [((le_max_left _ _).trans hv : 2≤v)]
  have h := hc (2*v) (by linarith only [((le_max_right _ _).trans hv : H≤v),hv0])
    2 (by norm_num) (by norm_num) (2*v) (2*(2*v)) le_rfl (by linarith only [hv0]) le_rfl
    (by rw [Real.rpow_zero,div_one]; linarith)
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] at h
  convert h using 1
  ring

end GaloisForLFunctions.RestrictedFactorizationCalculus
